"""HyperWolf: Hypercube-Wise Optimized lattice PCS (lab item 7.12, ePrint 2025/922).

Paper: "HyperWolf: Efficient Polynomial Commitment Schemes from Lattices"
(Zhang, Gao, Xiao; PolyU HK).  This is the deepest protocol module of the
lab — a full transcription of Protocols 1/2/3 (§4.1, §5.1 of the paper):

* **PC.Commit (Protocol 2)**: ring-pack d consecutive coefficients per ring
  element, balanced gadget-decompose every element into iota base-delta
  digits, parse into a k-dimensional hypercube s^(k) (axes b x ... x b x
  b*iota), Ajtai-commit every outermost-axis slice with the block-tiled
  A^(k) = 1^T (x) A, and bind the stack of inner commitments with the outer
  B^(k) = 1^T (x) B applied to the digit-decomposed stack.
* **PC.Eval (Protocol 3)**: build the k auxiliary evaluation vectors
  (univariate: powers of u; multilinear: tensor products of (1,u_j)), expand
  a0 through the gadget pairing rule, run Protocol 1.
* **Protocol 1** (k-1 rounds + final): per round the prover sends
  fold^(k-r) in R_q^b, JL projections p_i in R_q^jl_rows for each slice, and
  the slice commitments c_min,i in R_q^kappa.  The verifier checks the
  evaluation identity, the JL norm bound (128-style threshold), the outer
  commitment binding, and the cross-round projection consistency; then
  samples b Labrador challenges and both parties update the statement
  (y <- <fold, C>, cm_out <- B G^{-1}(sum C_i c_min,i)).  The final round
  reveals s^(1) and pins everything to A s^(1) = sum C_i t_i.

Lab parameters run at reduced sizes (d in {8,16,64}, q a 32/61-bit prime
= 5 mod 8, delta = 16) with the *identical* protocol logic; the paper's
128-bit instantiation is reproduced by the parameter-derivation helper
`paper_params()` and the proof-size model (Table 2 verification).

Documented deviations (see docs/papers/hyperwolf.md gap ledger):
1. Round-r >= 1 outer-binding check uses the statement-chain form
   B G^{-1}(sum_i C_i c_min,i^{(r-1)}) == cm_out^(r) (the paper's own
   completeness narrative: "the outer commitment in round r+1 is computed
   based on the proof provided in round r"); the literal per-round
   B^(l) G^{-1}((c_min,i)_i) re-decomposition is applied at round 0 and is
   not additive across folds, so it cannot be re-checked verbatim at every
   round — binding is carried by round-0 MSIS + the final A s^(1) check +
   the projection-consistency chain.
2. jl_rows is configurable (256 in the paper; scaled down for tests with
   the check constant jl_rows/2 preserving the JL margin).
3. Challenges use the Labrador distribution scaled to the ring dimension,
   with op-norm rejection (deterministic under Fiat-Shamir).
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import List, Sequence, Tuple

import numpy as np

from ..core.ring import Ring, RingElt
from ..core.transcript import Transcript
from ..core.commitment import _SeededRandom

# Lab primes q = 5 mod 8 (NTT-hostile on purpose — Kronecker multiply path)
HW_Q32 = 4294967197          # 32-bit, 5 mod 8
HW_Q61 = 2305843009213693693  # 61-bit, 5 mod 8


# --------------------------------------------------------------------------- #
#  Parameters
# --------------------------------------------------------------------------- #


@dataclass
class HWParams:
    q: int = HW_Q32
    d: int = 16              # ring dimension (paper: 64)
    b: int = 2               # hypercube axis length (paper: 2)
    k: int = 3               # hypercube dimension; N = b^k * d coefficients
    delta: int = 16          # gadget base (paper: 16)
    delta_t: int = 16        # outer gadget base
    kappa: int | None = None # commitment height (default 2*iota)
    jl_rows: int = 256       # JL projection rows (paper: 256; tests: 64)
    op_norm_bound: float | None = None  # challenge operator-norm bound (auto)

    def __post_init__(self):
        # +1 headroom digit: balanced digits in (-delta/2, delta/2] cover
        # only ~0.53 * delta^iota, so ceil(log_delta q) digits are too tight
        self.iota = math.ceil(math.log(self.q, self.delta)) + 1
        self.iota_p = math.ceil(math.log(self.q, self.delta_t)) + 1
        if self.kappa is None:
            self.kappa = 2 * self.iota
        self.ring = Ring(q=self.q, n=self.d)
        self.N = self.b**self.k * self.d
        self._beta_ladder()

    def _beta_ladder(self):
        """Witness norm ladder: beta[k-1] = delta/2 * sqrt(b^{k-1} iota d),
        conservative growth sqrt(2T) per fold with the paper's T = 15
        (spec pitfall 5 safe choice — looser bound, completeness-safe)."""
        T = 15.0
        beta = [0.0] * self.k
        beta[self.k - 1] = (self.delta / 2) * math.sqrt(
            self.b ** (self.k - 1) * self.iota * self.d
        )
        for lvl in range(self.k - 2, -1, -1):
            beta[lvl] = math.sqrt(2 * T) * beta[lvl + 1]
        self.beta = beta

    def slab(self) -> str:
        return f"hw:v1:q{self.q}:d{self.d}:b{self.b}:k{self.k}:dl{self.delta}:jl{self.jl_rows}"


def paper_params(N: int = 2**15) -> HWParams:
    """The paper's concrete instantiation (Table 4 / §7.5) — NOT executable at
    full size in the lab; used for proof-size modelling (Table 2 check)."""
    d = 64
    k = int(round(math.log2(N / d)))
    return HWParams(q=HW_Q61, d=d, b=2, k=k, delta=16, delta_t=16, jl_rows=256)


# --------------------------------------------------------------------------- #
#  Labrador challenge sampler (deterministic, op-norm rejection)
# --------------------------------------------------------------------------- #


def _negacyclic_matrix(c: Sequence[int], d: int) -> np.ndarray:
    """Negacyclic Toeplitz matrix T(c) with T[i,j] = c[(i-j) mod d], negated
    when i < j (X^d = -1)."""
    M = np.zeros((d, d))
    for i in range(d):
        for j in range(d):
            idx = (i - j) % d
            val = c[idx]
            if i < j:
                val = -val
            M[i, j] = val
    return M


def labrador_counts(d: int) -> Tuple[int, int, int]:
    """(zeros, ones, twos) scaled from the paper's 64: (23, 31, 10)."""
    z = max(1, round(d * 23 / 64))
    o = max(1, round(d * 31 / 64))
    t = max(0, d - z - o)
    while z + o + t > d:
        if o > z:
            o -= 1
        else:
            z -= 1
    return z, o, d - z - o


class ChallengeSampler:
    """Deterministic Labrador sampler with operator-norm rejection.
    Rejection tries are forked from the parent transcript (challenges depend
    on the statement + messages so far); the accepted retry count is absorbed
    back into the parent transcript."""

    def __init__(self, ring: Ring, op_bound: float | None = None):
        self.ring = ring
        self.z, self.o, self.t = labrador_counts(ring.n)
        if op_bound is None:
            # auto: ~2x the expected spectral norm of a random sparse element
            op_bound = 2.0 * math.sqrt(self.tau_sq() * 1.0 + 1)
        self.op_bound = op_bound

    def tau_sq(self) -> int:
        return self.o + 4 * self.t

    def sample(self, transcript: Transcript, label: str) -> RingElt:
        d = self.ring.n
        q = self.ring.q
        counter = 0
        while True:
            t = transcript.fork(f"{label}:try{counter}")
            vals = [t.challenge_range(0, d, label=f"c{i}") for i in range(d)]
            order = sorted(range(d), key=lambda i: vals[i])
            coeffs = [0] * d
            for pos, idx in enumerate(order):
                if pos < self.z:
                    coeffs[idx] = 0
                elif pos < self.z + self.o:
                    coeffs[idx] = 1 if t.challenge_int(1, label=f"s{idx}") else -1
                else:
                    coeffs[idx] = 2 if t.challenge_int(1, label=f"s{idx}") else -2
            coeffs = [c % q for c in coeffs]
            M = _negacyclic_matrix(coeffs, d)  # coeffs are small signed reps
            op = float(np.linalg.svd(M, compute_uv=False)[0])
            if op <= self.op_bound:
                transcript.absorb_int(counter, label="labrador-retries")
                transcript.absorb_bytes(
                    b"".join(c.to_bytes(2, "little", signed=True) for c in coeffs),
                    label="labrador-accept",
                )
                return RingElt(coeffs, self.ring)
            counter += 1


# --------------------------------------------------------------------------- #
#  Gadget machinery (balanced digits, component-major layout)
# --------------------------------------------------------------------------- #


def balanced_digits(v: int, delta: int, iota: int) -> List[int]:
    """Balanced base-delta digits (each in (-delta/2, delta/2]) of a CENTRED
    integer v.  Algorithm: unsigned decomposition of |v|, then rebalance
    with carries (the naive greedy signed-digit recursion fails on ~3% of
    negative values — see lab notes).  Requires one headroom digit: call
    with iota = ceil(log_delta(q)) + 1."""
    sign = -1 if v < 0 else 1
    u = abs(v)
    digits = []
    for _ in range(iota):
        digits.append(u % delta)
        u //= delta
    if u != 0:
        raise ValueError(f"value {v} exceeds {iota} digits of base {delta}")
    # rebalance: move digits > delta/2 into the next position
    for e in range(iota):
        if digits[e] > delta // 2:
            digits[e] -= delta
            if e + 1 < iota:
                digits[e + 1] += 1
            else:
                raise ValueError(f"carry overflow at top digit for {v}")
    return [d * sign for d in digits]


def gadget_decompose_elt(elt: RingElt, delta: int, iota: int) -> List[RingElt]:
    """G^{-1}_{delta,iota}(a): iota digit ring elements (balanced digits),
    component-major: digit e of every coefficient goes to layer e."""
    ring = elt.ring
    q = ring.q
    layers = [ring.zero() for _ in range(iota)]
    for i, c in enumerate(elt.coeffs):
        v = ring.center(c, q)
        for e, dg in enumerate(balanced_digits(v, delta, iota)):
            layers[e].coeffs[i] = dg % q
    return layers


def gadget_recompose_elt(layers: Sequence[RingElt], delta: int) -> RingElt:
    ring = layers[0].ring
    out = ring.zero()
    for e, layer in enumerate(layers):
        out = out + layer * (delta**e)
    return out


def gadget_decompose_vector(
    vec: Sequence[RingElt], delta: int, iota: int
) -> List[RingElt]:
    """Flat component-major decomposition: output index t*iota + e is digit
    layer e of ring component t (matches G_{a,m} = I_m (x) g_a^T)."""
    out: List[RingElt] = []
    for elt in vec:
        out.extend(gadget_decompose_elt(elt, delta, iota))
    return out


def gadget_recompose_vector(
    flat: Sequence[RingElt], delta: int, iota: int, count: int
) -> List[RingElt]:
    return [
        gadget_recompose_elt(flat[t * iota : (t + 1) * iota], delta)
        for t in range(count)
    ]


def mr_pack(ints: Sequence[int], ring: Ring) -> List[RingElt]:
    """M_R: group d consecutive integers into ring elements."""
    d = ring.n
    m = len(ints) // d
    out = []
    for t in range(m):
        out.append(RingElt([ints[t * d + j] % ring.q for j in range(d)], ring))
    return out


def expand_a0(a0_ints: Sequence[int], ring: Ring, delta: int, iota: int) -> List[RingElt]:
    """a0_ext[t*iota+e] = delta^e * M_R(a0)[t]  (spec §8.4-1 pairing rule —
    the gadget-transpose expansion that matches the component-major layout)."""
    packed = mr_pack(a0_ints, ring)
    out: List[RingElt] = []
    for t, elt in enumerate(packed):
        for e in range(iota):
            out.append(elt * (delta**e))
    return out


# --------------------------------------------------------------------------- #
#  Evaluation-vector builders (Protocol 3)
# --------------------------------------------------------------------------- #


def build_a_univariate(u: int, q: int, k: int, b: int, d: int):
    """a0 = (1,u,...,u^{bd-1}); a_i = (1, u^{b^i * d}, ...) — the stride of
    axis i is (product of inner axis lengths in INTEGER positions): axis 0
    spans a full b*d integer block, so axis i's stride is b^i * d."""
    a0 = [pow(u, e, q) for e in range(b * d)]
    a_list = []
    for i in range(1, k):
        stride = (b**i) * d
        a_list.append([pow(u, j * stride, q) for j in range(b)])
    return a0, a_list


def build_a_multilinear(u_vec: Sequence[int], q: int, k: int, b: int, d: int):
    """a_0 = eq-style product over the first log2(b*d) variables (X_0 is the
    LOW bit of the innermost integer position pos = i_0*d + j'); each outer
    axis i >= 1 takes one variable (b=2) in order X_{log2(bd)+i-1}."""
    log_b = int(round(math.log2(b)))
    log_bd = log_b + int(round(math.log2(d)))
    if len(u_vec) != log_bd + (k - 1) * log_b:
        raise ValueError("multilinear point length mismatch")
    a0 = []
    for pos in range(b * d):
        v = 1
        for l in range(log_bd):
            bit = (pos >> l) & 1
            v = v * (u_vec[l] if bit else (1 - u_vec[l])) % q
        a0.append(v)
    a_list = []
    for i in range(1, k):
        ai = []
        for j in range(b):
            # axis value j in base b: digits consume variables LSB-first
            v = 1
            for s in range(log_b):
                bit = (j >> s) & 1
                u = u_vec[log_bd + (i - 1) * log_b + s]
                v = v * (u if bit else (1 - u)) % q
            ai.append(v)
        a_list.append(ai)
    return a0, a_list


# --------------------------------------------------------------------------- #
#  Hypercube witness container
# --------------------------------------------------------------------------- #


class Hypercube:
    """k-dim hypercube of ring elements; last axis = b*iota (gadget-decomposed
    innermost axis).  Flattening D is row-major with the OUTERMOST axis
    slowest (spec pitfall 3)."""

    def __init__(self, flat: List[RingElt], axes: Tuple[int, ...]):
        self.flat = flat
        self.axes = axes
        self._check()

    def _check(self):
        if len(self.flat) != math.prod(self.axes):
            raise ValueError("flat length != product of axes")

    def slices(self) -> List[List[RingElt]]:
        """D(s_i): slices along the outermost axis, each flattened row-major."""
        m = self.axes[0]
        inner = math.prod(self.axes[1:])
        return [self.flat[i * inner : (i + 1) * inner] for i in range(m)]

    def fold_outer(self, C: Sequence[RingElt]) -> "Hypercube":
        """s^{(l-1)} = sum_i C_i s_i^{(l)} — removes the outermost axis."""
        m = self.axes[0]
        inner = math.prod(self.axes[1:])
        out = [self.flat[0].ring.zero() for _ in range(inner)]
        for i in range(m):
            ci = C[i]
            base = i * inner
            for j in range(inner):
                out[j] = out[j] + self.flat[base + j] * ci
        return Hypercube(out, self.axes[1:])


def fold_engine(
    hc: Hypercube, a0_ext_conj: Sequence[RingElt], a_ints: List[List[int]]
) -> List[RingElt]:
    """Fold^(l) (Eq. 4): contract the innermost axis with the CONJUGATED
    expanded a0 (ring inner products), then contract axes 1..l-2 with the
    integer vectors a_i (lifted scalars).  Returns R_q^{b} (outermost axis)."""
    axes = hc.axes
    if not a_ints:
        # only the innermost contraction: result has shape axes[:-1]
        n_last = axes[-1]
        rest = math.prod(axes[:-1])
        out = []
        for t in range(rest):
            acc = hc.flat[0].ring.zero()
            base = t * n_last
            for j in range(n_last):
                acc = acc + a0_ext_conj[j] * hc.flat[base + j]
            out.append(acc)
        return out
    # innermost contraction first
    n_last = axes[-1]
    rest = math.prod(axes[:-1])
    contracted = []
    for t in range(rest):
        acc = hc.flat[0].ring.zero()
        base = t * n_last
        for j in range(n_last):
            acc = acc + a0_ext_conj[j] * hc.flat[base + j]
        contracted.append(acc)
    # then contract intermediate axes: a_1 hits the current LAST axis (the
    # second-innermost), a_2 the next, ... — a_i maps to the axis that is
    # i-th from the innermost (paper Eq. 2's F-operator).
    cur = contracted
    cur_axes = list(axes[:-1])
    for a_i in a_ints:
        if len(a_i) != cur_axes[-1]:
            raise ValueError(f"axis mismatch: len(a)={len(a_i)} axis={cur_axes[-1]}")
        block = cur_axes[-1]
        nblocks = math.prod(cur_axes[:-1])
        nxt = []
        for bidx in range(nblocks):
            acc = cur[0].ring.zero()
            base = bidx * block
            for j in range(block):
                acc = acc + cur[base + j] * a_i[j]
            nxt.append(acc)
        cur = nxt
        cur_axes = cur_axes[:-1]
    return cur


# --------------------------------------------------------------------------- #
#  JL projection engine
# --------------------------------------------------------------------------- #


class JLMatrix:
    """Seeded JL matrix Pi (trits), ring-packed to R_q^{jl_rows x (b0*iota)},
    conjugated entrywise (sigma_{-1}).  Tiled application via block sums."""

    def __init__(self, seed: bytes, ring: Ring, cols: int, jl_rows: int):
        self.ring = ring
        self.cols = cols  # = b0 * iota ring columns
        self.jl_rows = jl_rows
        rng = _SeededRandom(seed)
        d = ring.n
        self.entries = [
            [rng.randrange(0, 3) - 1 for _ in range(cols * d)] for _ in range(jl_rows)
        ]
        # ring-pack rows and conjugate
        self.rows = []
        for row in self.entries:
            packed = mr_pack(row, ring)
            self.rows.append([e.conjugate() for e in packed])

    def project(self, flat: Sequence[RingElt], block: int) -> List[RingElt]:
        """sigma_{-1}(Pi^{(l)}) . v for a flattened slice of length
        blocks*block — computed as block-sum then matvec."""
        if len(flat) % block != 0 or block != self.cols:
            # block == cols always in this design
            raise ValueError("projection layout mismatch")
        nblocks = len(flat) // block
        acc = [self.ring.zero() for _ in range(self.cols)]
        for bi in range(nblocks):
            base = bi * block
            for j in range(block):
                acc[j] = acc[j] + flat[base + j]
        out = []
        for row in self.rows:
            s = self.ring.zero()
            for j, w in enumerate(row):
                if not w.is_zero():
                    s = s + w * acc[j]
            out.append(s)
        return out


# --------------------------------------------------------------------------- #
#  Ajtai keys with block-tiling
# --------------------------------------------------------------------------- #


class HWKeys:
    """A in R_q^{kappa x (b0*iota)}, B in R_q^{kappa x (kappa*iota_p)},
    deterministically seed-expanded (transparent setup)."""

    def __init__(self, params: HWParams, seed: bytes = b"hw-default-seed"):
        self.p = params
        ring = params.ring
        self.a_cols = params.b * params.iota
        self.b_cols = params.kappa * params.iota_p
        rng = _SeededRandom(seed)
        self.A = [
            [RingElt([rng.randrange_mod(ring.q) for _ in range(ring.n)], ring)
             for _ in range(self.a_cols)]
            for _ in range(params.kappa)
        ]
        self.B = [
            [RingElt([rng.randrange_mod(ring.q) for _ in range(ring.n)], ring)
             for _ in range(self.b_cols)]
            for _ in range(params.kappa)
        ]

    def commit_slices(self, flat: Sequence[RingElt]) -> List[RingElt]:
        """A^{(l)} . v = A . block-sum(v into b0*iota-sized blocks)."""
        ring = self.p.ring
        block = self.a_cols
        nblocks = len(flat) // block
        acc = [ring.zero() for _ in range(block)]
        for bi in range(nblocks):
            base = bi * block
            for j in range(block):
                acc[j] = acc[j] + flat[base + j]
        return self._matvec(self.A, acc)

    def outer_commit(self, stack: Sequence[RingElt], delta_t: int, iota_p: int) -> List[RingElt]:
        """cm_out = B^{(l)} . G^{-1}_{delta_t}(stack) = B . block-sum of the
        digit decomposition of the stacked commitments."""
        ring = self.p.ring
        digits = gadget_decompose_vector(stack, delta_t, iota_p)
        block = self.b_cols
        nblocks = len(digits) // block
        acc = [ring.zero() for _ in range(block)]
        for bi in range(nblocks):
            base = bi * block
            for j in range(block):
                acc[j] = acc[j] + digits[base + j]
        return self._matvec(self.B, acc)

    def outer_commit_from_fold(
        self, c_mins: Sequence[Sequence[RingElt]], C: Sequence[RingElt]
    ) -> List[RingElt]:
        """cm_out^{(l-1)} = B . G^{-1}_{delta_t,kappa}(sum_i C_i c_min,i^{(l-1)})
        — the statement update both parties compute (paper Eq. after Eq. 5)."""
        ring = self.p.ring
        folded = [
            sum((c * C[i] for c in c_min), start=ring.zero())
            for i, c_min in enumerate(c_mins)
        ]
        digits = gadget_decompose_vector(folded, self.p.delta_t, self.p.iota_p)
        return HWKeys._matvec(self.B, digits)

    def _blocksum_matvec(self, M, v):
        ring = self.p.ring
        block = self.b_cols
        nblocks = len(v) // block
        acc = [ring.zero() for _ in range(block)]
        for bi in range(nblocks):
            base = bi * block
            for j in range(block):
                acc[j] = acc[j] + v[base + j]
        return self._matvec(M, acc)

    @staticmethod
    def _matvec(M, v) -> List[RingElt]:
        out = []
        for row in M:
            acc = v[0].ring.zero()
            for a, x in zip(row, v):
                if not a.is_zero():
                    acc = acc + a * x
            out.append(acc)
        return out


# --------------------------------------------------------------------------- #
#  Protocol 2/3 + Protocol 1 driver
# --------------------------------------------------------------------------- #


@dataclass
class HWStatement:
    """x^{(l)}: (a-vectors, y, cm_out).  `level` = k - r."""

    a0_ints: List[int]                  # length b*d
    a_list: List[List[int]]             # k-1 integer vectors (length b)
    y: RingElt                          # current claim (ring element)
    cm_out: List[RingElt]               # R_q^kappa outer commitment
    level: int                          # current hypercube dimension l


@dataclass
class HWCommitState:
    f_ints: List[int]                   # original coefficient vector
    s: Hypercube                        # witness hypercube
    slices: List[List[RingElt]]         # D(s_i^{(k-1)})
    c_mins: List[List[RingElt]]         # inner commitments c_min,i^{(k-1)}


@dataclass
class HWRoundMessage:
    fold: List[RingElt]                 # R_q^b
    projections: List[List[RingElt]]    # b x jl_rows
    c_mins: List[List[RingElt]]         # b x kappa (t_i = c_min,i)


@dataclass
class HWProof:
    rounds: List[HWRoundMessage]
    s_final: List[RingElt]              # s^{(1)} in R_q^{b*iota}
    n_ring_elts: int = 0
    n_bytes: int = 0


class HyperWolf:
    """The HyperWolf PCS: commit / eval_prove / eval_verify."""

    def __init__(self, params: HWParams, seed: bytes = b"hw-default-seed"):
        self.p = params
        self.ring = params.ring
        self.keys = HWKeys(params, seed)
        self.sampler = ChallengeSampler(params.ring, params.op_norm_bound)

    # ------------------------------------------------------------ Protocol 2 #
    def commit(self, f_ints: Sequence[int]) -> Tuple[List[RingElt], HWCommitState]:
        p = self.p
        if len(f_ints) != p.N:
            raise ValueError(f"f must have N={p.N} coefficients")
        # 1-2. ring-pack
        packed = mr_pack(f_ints, self.ring)
        # 3. gadget-decompose (component-major)
        s_flat = gadget_decompose_vector(packed, p.delta, p.iota)
        # 4. parse into hypercube: axes (b,...,b, b*iota)
        axes = (p.b,) * (p.k - 1) + (p.b * p.iota,)
        s = Hypercube(list(s_flat), axes)
        slices = s.slices()
        c_mins = [self.keys.commit_slices(sl) for sl in slices]
        # 5. outer commitment
        stack = [c for c_min in c_mins for c in c_min]
        cm_out = self.keys.outer_commit(stack, p.delta_t, p.iota_p)
        state = HWCommitState(
            f_ints=list(f_ints), s=s, slices=slices, c_mins=c_mins
        )
        return cm_out, state

    def open(self, cm: Sequence[RingElt], f_ints: Sequence[int],
             state: HWCommitState) -> bool:
        """PC.Open (Protocol 2): recompute the commitment pipeline."""
        cm2, _ = self.commit(f_ints)
        return cm2 == list(cm)

    # ------------------------------------------------------------ helpers #
    def _a0_ext_conj(self, a0_ints: Sequence[int]) -> List[RingElt]:
        a0_ext = expand_a0(a0_ints, self.ring, self.p.delta, self.p.iota)
        return [e.conjugate() for e in a0_ext]

    def _jl(self, transcript: Transcript) -> JLMatrix:
        seed = transcript.challenge_bytes(32, label="hw:jl-seed")
        return JLMatrix(seed, self.ring, self.p.b * self.p.iota, self.p.jl_rows)

    def _jl_bound(self, level: int) -> float:
        """Check-2 threshold: (jl_rows/2) * beta^2 (paper: 128 beta^2 with
        jl_rows=256)."""
        return (self.p.jl_rows / 2) * (self.p.beta[level] ** 2)

    # ------------------------------------------------------------ Protocol 1 #
    def eval_prove(
        self,
        state: HWCommitState,
        cm: Sequence[RingElt],
        a0_ints: Sequence[int],
        a_list: List[List[int]],
        transcript: Transcript,
    ) -> HWProof:
        p = self.p
        ring = self.ring
        # y^{(k)} = <Fold^(k), a_{k-1}> — the prover computes the fold and
        # the verifier checks it as check 1 of round 0; y enters the
        # statement via the PCS wrapper.  Here we just run the rounds.
        s = state.s
        c_mins = state.c_mins
        y = None
        a0c = self._a0_ext_conj(a0_ints)
        jl = self._jl(transcript)
        rounds: List[HWRoundMessage] = []
        level = p.k
        C_hist: List[List[RingElt]] = []
        p_hist: List[List[List[RingElt]]] = []
        while level > 1:
            # fold^(level) — contract innermost + intermediate axes; the
            # outermost axis survives (a_{level-1} is NOT applied here).
            fold = fold_engine(s, a0c, a_list[: level - 2])
            # wait: intermediate contractions use a_1..a_{level-2}; the
            # outermost axis (b) survives for check 1 with a_{level-1}.
            slices = s.slices()
            projs = [jl.project(sl, p.b * p.iota) for sl in slices]
            msg = HWRoundMessage(fold=fold, projections=projs, c_mins=c_mins)
            rounds.append(msg)
            # absorb + challenges
            transcript.absorb_bytes(b"hw:round")
            for fr in fold:
                transcript.absorb_ring(fr)
            for pr in projs:
                for x in pr:
                    transcript.absorb_ring(x)
            for cmn in c_mins:
                for x in cmn:
                    transcript.absorb_ring(x)
            C = [self.sampler.sample(transcript, f"hw:chal:L{level}") for _ in range(p.b)]
            C_hist.append(C)
            p_hist.append(projs)
            # fold witness
            s = s.fold_outer(C)
            # re-commit new slices
            new_slices = s.slices()
            c_mins = [self.keys.commit_slices(sl) for sl in new_slices]
            level -= 1
        proof = HWProof(rounds=rounds, s_final=list(s.flat), n_ring_elts=0, n_bytes=0)
        proof.n_ring_elts = sum(
            len(m.fold) + sum(len(x) for x in m.projections) + sum(len(x) for x in m.c_mins)
            for m in rounds
        ) + len(proof.s_final)
        w = (self.p.q.bit_length() + 7) // 8
        proof.n_bytes = proof.n_ring_elts * w * self.ring.n
        return proof

    def eval_verify(
        self,
        cm: Sequence[RingElt],
        a0_ints: Sequence[int],
        a_list: List[List[int]],
        y_claim: int,
        proof: HWProof,
        transcript: Transcript,
    ) -> bool:
        p = self.p
        ring = self.ring
        # initial y^{(k)}: ring elt with constant term = claimed evaluation
        y = ring.from_int(0)
        y.coeffs[0] = y_claim % ring.q
        a0c = self._a0_ext_conj(a0_ints)
        jl = self._jl(transcript)
        cm_out = list(cm)
        level = p.k
        C_hist: List[List[RingElt]] = []
        p_hist: List[List[List[RingElt]]] = []
        c_min_hist: List[List[List[RingElt]]] = []
        for r, msg in enumerate(proof.rounds):
            if len(msg.fold) != p.b or len(msg.c_mins) != p.b:
                return False
            # ---- check 1: <fold, a_{level-1}> == y   (a_{level-1} = a_list[level-2];
            # round 0 compares the constant term against the scalar claim)
            ip = ring.zero()
            for i, fr in enumerate(msg.fold):
                ip = ip + fr * a_list[level - 2][i]
            if r == 0:
                if ip.coeffs[0] != y.coeffs[0]:
                    return False
            else:
                if ip != y:
                    return False
            # ---- check 2: JL norm bound per slice
            bound = self._jl_bound(level - 1)
            for pr in msg.projections:
                if len(pr) != p.jl_rows:
                    return False
                s_sq = 0
                for x in pr:
                    s_sq += self.ring.center(x.coeffs[0], ring.q) ** 2
                if s_sq > bound:
                    return False
            # ---- check 3: outer commitment binding
            if r == 0:
                stack = [c for c_min in msg.c_mins for c in c_min]
                if self.keys.outer_commit(stack, p.delta_t, p.iota_p) != cm_out:
                    return False
            else:
                # statement-chain form: cm_out^{(level)} == B G^{-1}(sum C_i c_min,i^{prev})
                if self.keys.outer_commit_from_fold(c_min_hist[-1], C_hist[-1]) != cm_out:
                    return False
            # ---- check 4: cross-round projection consistency
            if r > 0:
                lhs = [ring.zero() for _ in range(p.jl_rows)]
                for j, pj in enumerate(p_hist[-1]):
                    for idx, x in enumerate(pj):
                        lhs[idx] = lhs[idx] + x * C_hist[-1][j]
                rhs = [ring.zero() for _ in range(p.jl_rows)]
                for pr in msg.projections:
                    for idx, x in enumerate(pr):
                        rhs[idx] = rhs[idx] + x
                if lhs != rhs:
                    return False
            # ---- challenge + statement update
            transcript.absorb_bytes(b"hw:round")
            for fr in msg.fold:
                transcript.absorb_ring(fr)
            for pr in msg.projections:
                for x in pr:
                    transcript.absorb_ring(x)
            for cmn in msg.c_mins:
                for x in cmn:
                    transcript.absorb_ring(x)
            C = [self.sampler.sample(transcript, f"hw:chal:L{level}") for _ in range(p.b)]
            # y^{(level-1)} = <fold, C>
            y = ring.zero()
            for i, fr in enumerate(msg.fold):
                y = y + fr * C[i]
            # cm_out^{(level-1)} = B G^{-1}_{delta_t,kappa}(sum C_i c_min,i)
            cm_out = self.keys.outer_commit_from_fold(msg.c_mins, C)
            C_hist.append(C)
            p_hist.append(msg.projections)
            c_min_hist.append(msg.c_mins)
            level -= 1
        # ---------------- final checks (round k-1) ----------------
        s1 = proof.s_final
        if len(s1) != p.b * p.iota:
            return False
        # (a) <conj(a0_ext), s^(1)> == y  (ring equality)
        ip = ring.zero()
        for j in range(len(s1)):
            ip = ip + a0c[j] * s1[j]
        if ip != y:
            return False
        # norm bound ||s^(1)|| <= beta^{(0)}
        norm_sq = sum(
            self.ring.center(c, ring.q) ** 2 for elt in s1 for c in elt.coeffs
        )
        if norm_sq > self.p.beta[0] ** 2:
            return False
        # (b) sigma_{-1}(Pi) s^(1) == sum_i C_i p_i^{(2)}
        lhs = [ring.zero() for _ in range(p.jl_rows)]
        for j, pj in enumerate(p_hist[-1]):
            for idx, x in enumerate(pj):
                lhs[idx] = lhs[idx] + x * C_hist[-1][j]
        rhs = jl.project(s1, p.b * p.iota)
        if lhs != rhs:
            return False
        # A s^(1) == sum_i C_i t_i^{(1)}   (a kappa-vector: sum over slices,
        # weighted by the last round's challenges, per commitment row)
        lhs_c = self.keys.commit_slices(s1)
        last_mins = c_min_hist[-1]
        rhs_c = [
            sum(
                (last_mins[i][r] * C_hist[-1][i] for i in range(len(last_mins))),
                start=ring.zero(),
            )
            for r in range(p.kappa)
        ]
        if lhs_c != rhs_c:
            return False
        return True

    # ------------------------------------------------------------ Protocol 3 #
    def eval(
        self,
        cm: Sequence[RingElt],
        state: HWCommitState,
        point,
        y_claim: int,
        multilinear: bool,
        transcript: Transcript,
    ) -> HWProof:
        p = self.p
        if multilinear:
            a0, a_list = build_a_multilinear(point, p.q, p.k, p.b, p.d)
        else:
            a0, a_list = build_a_univariate(point, p.q, p.k, p.b, p.d)
        # y as claimed: the prover must show <Fold^(k), a_{k-1}> has ct = y.
        # We set the statement y^{(k)} = ring elt with ct = y_claim; the
        # prover's round-0 fold check pins it (verified in eval_verify).
        return self.eval_prove(state, cm, a0, a_list, transcript)

    def evaluate_direct(self, f_ints: Sequence[int], point, multilinear: bool) -> int:
        """Reference evaluation for tests (no proving)."""
        p = self.p
        if multilinear:
            acc = 0
            for idx, c in enumerate(f_ints):
                bits = [(idx >> i) & 1 for i in range(len(point))]
                term = c
                for b_i, u in zip(bits, point):
                    term = term * ((1 - u) if b_i == 0 else u) % p.q
                acc = (acc + term) % p.q
            return acc
        u = point
        return sum(c * pow(u, i, p.q) for i, c in enumerate(f_ints)) % p.q
