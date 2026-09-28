"""RoKoko: lattice-based succinct arguments, a committed refinement (7.13).

Paper: "RoKoko" (Klooß, Lai, Nguyen, Osadnik, Tucci; ePrint 2025/1083-via-upload).
This module implements the paper's core machinery at lab scale:

* **COM** (Figure 1) — the recursive Ajtai commitment: level 0 commits w with
  a vSIS key A_{n0, 2^mu}; the level-0 output y is gadget-decomposed
  G^{-1}_{l0}(y), zero-padded to a power of two, and committed recursively;
  the deepest output is `com`.
* **Ξ^lin_COM** (§4.4) — the committed-linear relation: F_i W = H_i Y_i mod q
  with COM-opened Y_i, left/right linear claims ℓ_j^T W r_j = t_j, a global
  A(vec(Y_i)) = b, and norm bounds (W implicitly committed via F_0 ∈ vSIS keys).
* **Π^fold-split** (Figure 4) — folds the r columns with challenge c,
  gadget-decomposes W·c, packs (folded witness + all aux data) into ŵ
  (decreasing-dimension sort + zero-pad, Lemma 3), re-commits under a fresh
  vSIS key, sends (com, v) with v = <ŵ, ŵ̄> the Hermitian self-inner product;
  the verifier checks ct(v) <= β̃² (Remark 3's power-of-two shortcut: the
  constant term equals ||cf(ŵ)||² exactly).
* **sumcheckify** (Figure 5) — every constraint becomes a degree-2 sumcheck
  claim (a_{i,1} x_0 + MLE[a_{i,0}])·(b_{i,1} x_1 + MLE[b_{i,0}]) − c/m over
  the packed vector (with the conjugate packed vector as the x_1 argument for
  the norm claim).
* **Π^lin** (Figure 6) — linearisation: batch the k_sc claims with
  eq(bin(i), γ) combiners, run the (ring-valued) sumcheck, output the two
  evaluation rows (ℓ_0 = tensor(c_1), r_0 = tensor(c_0), t_0 = z_0 = MLE[w](c)).
* **Round loop**: (Π^fold-split ∘ Π^proj): Ξ^lin → Ξ^sum, then Π^lin: Ξ^sum →
  Ξ^lin; m_w shrinks geometrically; the terminal instance is opened directly.

Lab simplifications (documented in the gap ledger):
- The NTT-slot / subfield batching Φ = δ^T ∘ θ_a is replaced by full-ring
  challenges (soundness |C| = q^n ≥ q^a); round messages are full ring
  elements (the paper's F_{q^a} compression is a size optimization).
- Π^proj-f (Figure 3, the fine projection) is not implemented; Π^proj-c
  (coarse) is provided; the round loop runs without projections (they are a
  norm-slack/extraction optimization, not needed for completeness).
- COM runs at depth 1-2; the vector s (slack, ϱ > 1) is fixed to 1.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import List, Sequence, Tuple

from ..core.ring import Ring, RingElt, dot, mat_vec
from ..core.transcript import Transcript
from ..core.commitment import AjtaiParams, Gadget
from ..core.ringsc import (
    RingSC,
    ProductClaim,
    norm_conjugate_inner,
    trace_balanced,
    verify_round_polys,
)
from ..core.sumcheck import eq_table, mle_eval, bind_table

# --------------------------------------------------------------------------- #
#  Parameters
# --------------------------------------------------------------------------- #


@dataclass
class RoKokoParams:
    q: int
    n_ring: int = 16        # ring dimension f (power of two)
    n0: int = 2             # vSIS rows per commitment
    gadget_len: int = 4     # l: gadget length (digits per element)
    com_depth: int = 1      # COM recursion depth d
    r: int = 2              # witness column count (power of two)
    beta_w: int = 16        # witness l2 bound per column

    def __post_init__(self):
        self.ring = Ring(q=self.q, n=self.n_ring)
        self.gadget = Gadget(self.ring, base=2, digits=self.gadget_len)


# --------------------------------------------------------------------------- #
#  Gadget helpers over R_q (G_l = I (x) g_l^T with g_l = (1,2,...,2^{l-1}))
# --------------------------------------------------------------------------- #


def g_inv_vec(vec: Sequence[RingElt], l: int, ring: Ring) -> List[RingElt]:
    """G^{-1}_l(v): decompose each ring element into l binary digit layers
    (component-major: output index t*l + e = digit e of component t)."""
    out: List[RingElt] = []
    for elt in vec:
        layers = [ring.zero() for _ in range(l)]
        for i, c in enumerate(elt.coeffs):
            c = Ring.center(c, ring.q) % ring.q
            for e in range(l):
                layers[e].coeffs[i] = (c >> e) & 1
        out.extend(layers)
    return out


def g_vec(flat: Sequence[RingElt], l: int, count: int) -> List[RingElt]:
    """G_l(v): recompose `count` elements from the digit layers."""
    ring = flat[0].ring
    out = []
    for t in range(count):
        acc = ring.zero()
        for e in range(l):
            acc = acc + flat[t * l + e] * (1 << e)
        out.append(acc)
    return out


# --------------------------------------------------------------------------- #
#  COM — recursive Ajtai commitment (Figure 1)  [R2]
# --------------------------------------------------------------------------- #


class ComKey:
    """Seeded vSIS keys A_{n, m} for m a power of two (transparent)."""

    def __init__(self, params: RoKokoParams, seed: bytes = b"rokoko-seed"):
        self.p = params
        self.seed = seed
        self._cache = {}

    def key(self, n: int, m: int) -> List[List[RingElt]]:
        k = (n, m)
        if k not in self._cache:
            ap = AjtaiParams(self.p.ring, n, m, seed=self.seed + f"|{n}|{m}".encode())
            self._cache[k] = ap.matrix()
        return self._cache[k]

    def commit(self, w: Sequence[RingElt], n: int) -> List[RingElt]:
        m = len(w)
        return mat_vec(self.key(n, m), list(w))


@dataclass
class ComOpening:
    """aux = (x*, x) for depth >= 2; empty for depth 1."""

    y: List[RingElt]          # level-0 commitment (A_{n0, m} w)
    x_star: List[RingElt] | None  # recursive commitment output
    x: List[RingElt] | None       # the decomposed+padded vector committed recursively


def com_commit(
    ck: ComKey, w: Sequence[RingElt], depth: int, l: int
) -> Tuple[List[RingElt], ComOpening]:
    """Com_{par_com}(ck, w): recursive Ajtai commitment (Figure 1).
    Returns (com, aux).  depth = 1: com = A_{n0,m} w."""
    p = ck.p
    ring = p.ring
    y = ck.commit(w, p.n0)
    if depth == 1:
        return y, ComOpening(y=y, x_star=None, x=None)
    # e = G^{-1}_l(y); x = e || 0 padded to minpowtwo(l * n0)
    e = g_inv_vec(y, l, ring)
    target = _minpowtwo(l * p.n0)
    x = list(e) + [ring.zero() for _ in range(target - len(e))]
    inner_depth = depth - 1
    com_out, _ = com_commit(ck, x, inner_depth, l)
    return com_out, ComOpening(y=y, x_star=com_out, x=x)


def com_verify(
    ck: ComKey,
    w: Sequence[RingElt],
    com: Sequence[RingElt],
    aux: ComOpening,
    depth: int,
    l: int,
    beta0: int,
) -> bool:
    """Verify_{par_com, beta}(ck, w, com, aux) — Figure 1 right column."""
    p = ck.p
    ring = p.ring
    # b0: ||w||_2 <= beta0
    if sum(x.l2_sq_int() for x in w) > beta0 * beta0:
        return False
    if depth == 1:
        return ck.commit(w, p.n0) == list(com)
    # b1: A_{n0, 2^mu} w == (G_l || 0)(x)  [i.e. G_l(x[:l*n0]) == y]
    if ck.commit(w, p.n0) != aux.y:
        return False
    target = _minpowtwo(l * p.n0)
    if len(aux.x) != target:
        return False
    if g_vec(aux.x[: l * p.n0], l, p.n0) != aux.y:
        return False
    # b2: recursive verify on (x, x*)
    ok, _ = com_commit(ck, aux.x, depth - 1, l)
    if list(ok) != list(aux.x_star) if aux.x_star is not None else False:
        return False
    if aux.x_star is not None and not com_verify(
        ck, aux.x, aux.x_star, ComOpening(y=aux.x_star, x_star=None, x=None),
        1, l, beta0
    ):
        return False
    return list(com) == list(aux.x_star) if aux.x_star is not None else True


def _minpowtwo(v: int) -> int:
    return 1 << (v - 1).bit_length() if v > 1 else 1


# --------------------------------------------------------------------------- #
#  Packing (§3.6 Lemma 3)  [R1/R2 glue]
# --------------------------------------------------------------------------- #


@dataclass
class Packing:
    """pack(w_0..w_{k-1}) with blocks sorted by DECREASING dimension,
    concatenated, zero-padded to a power of two.  Records offsets so the
    sumcheck can address sub-blocks via eq(prefix, .) selectors."""

    flat: List[RingElt]
    blocks: List[Tuple[int, int, int]]  # (offset, length, log2 length)
    total: int

    @classmethod
    def pack(cls, blocks: Sequence[Sequence[RingElt]], ring: Ring) -> "Packing":
        order = sorted(range(len(blocks)), key=lambda i: -len(blocks[i]))
        flat: List[RingElt] = []
        meta = []
        for i in order:
            b = blocks[i]
            meta.append((len(flat), len(b), (len(b) - 1).bit_length() if len(b) > 1 else 0))
            flat.extend(b)
        total = _minpowtwo(max(1, len(flat)))
        flat = flat + [ring.zero() for _ in range(total - len(flat))]
        return cls(flat=flat, blocks=meta, total=total)

    def prefix(self, block_index: int) -> List[int]:
        """p_i = bin(offset_i / m_i): the bit prefix selecting block i inside
        the packed hypercube (Lemma 3)."""
        off, m, mu = self.blocks[block_index]
        if m == self.total:
            return []
        shift = (self.total // m).bit_length() - 1
        return [(off // m >> (shift - 1 - b)) & 1 for b in range(shift)]


# --------------------------------------------------------------------------- #
#  Ξ^lin_COM relation  [R1]
# --------------------------------------------------------------------------- #


@dataclass
class LinComInstance:
    """stmt = ((com_i, F_i, H_i)_i, (l_j, r_j, t_j)_j, A, b) + witness."""

    F: List[List[List[RingElt]]]      # k_lin matrices n_i x m_w
    H: List[List[List[RingElt]]]      # k_lin matrices n_i x m_{y,i}
    coms: List[List[RingElt]]         # COM outputs for vec(Y_i)
    aux: List[ComOpening]
    ell: List[List[RingElt]]          # k_lr left vectors (length m_w)
    rr: List[List[RingElt]]           # k_lr right vectors (length r)
    tt: List[RingElt]                 # k_lr targets
    A: List[List[RingElt]] | None     # global matrix n x (sum m_{y,i} r)
    b: List[RingElt] | None
    m_w: int
    r: int
    beta_w: int
    # witness side (prover only)
    W: List[List[RingElt]] | None = None      # m_w x r (list of rows? — columns!)
    Ys: List[List[List[RingElt]]] | None = None  # per i: m_{y,i} x r

    def witness_columns(self) -> List[List[RingElt]]:
        """W as r column vectors of length m_w."""
        if self.W is None:
            raise ValueError("no witness")
        return [ [self.W[j][col] for j in range(self.m_w)] for col in range(self.r) ]

    def check_honest(self, ck: ComKey, depth: int, l: int) -> bool:
        """All Ξ^lin_COM constraints for the embedded witness (per column)."""
        W = self.W
        for i in range(len(self.F)):
            for col in range(self.r):
                wcol = [W[j][col] for j in range(self.m_w)]
                FW = mat_vec(self.F[i], wcol)
                ycol = [self.Ys[i][k][col] for k in range(len(self.Ys[i]))]
                HY = mat_vec(self.H[i], ycol)
                if FW != HY:
                    return False
        for j in range(len(self.ell)):
            wcol0 = [W[k][0] for k in range(self.m_w)]
            if dot(self.ell[j], wcol0) != self.tt[j]:
                return False
        if sum(x.l2_sq_int() for row in W for x in row) > self.beta_w**2 * self.r:
            return False
        return True


# --------------------------------------------------------------------------- #
#  sumcheckify (Figure 5)  [R1/R2 glue]
# --------------------------------------------------------------------------- #


@dataclass
class ScConstraint:
    """One sumcheckified constraint (Figure 5 / §6.2 worked example).

    Every constraint is a difference/constant of INNER PRODUCTS over the
    packed vector w_hat, encoded as PRODUCT groups for RingSC:
      * 'lindiff':  <a_L, w_hat> - <a_R, w_hat> = 0
        (a_R sign-folded; both are public tables with prefix selectors)
      * 'lin':      <a, w_hat> = value            (public constant claim)
      * 'norm':     <w_hat, conj(w_hat)> = value  (the exact norm check)
    The private slot (w_hat / w_hat-bar) is supplied at prove time; the
    verifier substitutes the sent z0/z1 at the terminal check."""

    kind: str                                   # 'lindiff' | 'lin' | 'norm'
    a_L: List[RingElt] | None = None            # left public table
    a_R: List[RingElt] | None = None            # right public table (lindiff)
    value: RingElt | None = None                # claimed constant (lin/norm)

    def groups(self, w_hat: Sequence[RingElt]) -> List[ProductClaim]:
        ring = w_hat[0].ring
        if self.kind == "lindiff":
            return [
                ProductClaim(tables=[list(self.a_L), list(w_hat)], value=ring.zero()),
                ProductClaim(tables=[neg_table(self.a_R, ring), list(w_hat)], value=ring.zero()),
            ]
        if self.kind == "lin":
            return [ProductClaim(tables=[list(self.a_L), list(w_hat)], value=self.value)]
        return [
            ProductClaim(
                tables=[list(w_hat), [x.conjugate() for x in w_hat]],
                value=self.value,
            )
        ]

    def verifier_groups(self, z0: RingElt, z1: RingElt, nu: int) -> List[List]:
        """Groups with the private slot replaced by the length-1 [z0]/[z1]
        tables (their MLE at any point is the value itself)."""
        ring = z0.ring
        if self.kind == "lindiff":
            return [[list(self.a_L), [z0]], [neg_table(self.a_R, ring), [z0]]]
        if self.kind == "lin":
            return [[list(self.a_L), [z0]]]
        return [[[z0], [z1]]]


def neg_table(t: Sequence[RingElt], ring: Ring) -> List[RingElt]:
    return [(-x) % ring.q if isinstance(x, int) else -x for x in t]


def _eq_bin_combiners(gamma: Sequence[RingElt], k: int, ring: Ring) -> List[RingElt]:
    """eq(bin(i), gamma) combiners — the paper's claim-batching weights."""
    log_k = len(gamma)
    out = []
    for i in range(k):
        val = ring.one()
        for b in range(log_k):
            bit = (i >> (log_k - 1 - b)) & 1
            g = gamma[b]
            val = val * (g if bit else (1 - g))
        out.append(val)
    return out


# --------------------------------------------------------------------------- #
#  Π^fold-split (Figure 4)  [R2]
# --------------------------------------------------------------------------- #


@dataclass
class FoldSplitProof:
    com_klin: List[RingElt]     # commitment of the aux block
    com: List[RingElt]          # new packed commitment
    v: RingElt                  # Hermitian self-inner product value


def fold_split_prove(
    inst: LinComInstance,
    ck: ComKey,
    transcript: Transcript,
    l_prime: int | None = None,
) -> Tuple[FoldSplitProof, List[ScConstraint], List[RingElt], List[RingElt], List[List[RingElt]], List[RingElt]]:
    """Π^fold-split prover (Figure 4).  Returns (proof, constraints, w_hat,
    c challenges, F_new key, FU).  The new instance is assembled by the
    driver from (F_new, FU, com)."""
    p = ck.p
    if l_prime is None:
        l_prime = p.gadget_len  # must cover q (binary digits, ceil(log2 q)+1)
    ring = p.ring
    W = inst.W  # m_w x r
    m_w, r = inst.m_w, inst.r
    transcript.absorb_bytes(b"rk:fold-split:start")
    for cm_i in inst.coms:
        for x in cm_i:
            transcript.absorb_ring(x)
    c_chal = [ring.challenge(transcript, label=f"rk:c{i}") for i in range(r)]
    folded = [
        sum((W[j][i] * c_chal[i] for i in range(r)), start=ring.zero())
        for j in range(m_w)
    ]
    w_tilde = g_inv_vec(folded, l_prime, ring)
    blocks = [list(w_tilde)]
    for i in range(len(inst.coms)):
        if inst.Ys is not None:
            # pack ALL r columns of Y_i (vec(Y_i), row-major over columns)
            blocks.append([inst.Ys[i][j][col] for j in range(len(inst.Ys[i]))
                           for col in range(r)])
        if inst.aux[i].x is not None:
            blocks.append(list(inst.aux[i].x))
    packing = Packing.pack(blocks, ring)
    w_hat = packing.flat
    v = norm_conjugate_inner(w_hat)
    F_new = ck.key(p.n0, packing.total)
    FU = mat_vec(F_new, w_hat)
    # depth-1 COM: the commitment IS the Ajtai output FU (re-committing FU
    # again under a second key is the paper's depth-2 recursion — exercised
    # separately in the COM unit tests)
    com_new, aux_new = FU, ComOpening(y=FU, x_star=None, x=None)
    cons = build_constraints(inst, packing, c_chal, ring, l_prime, F_new, FU, com_new, v)
    proof = FoldSplitProof(com_klin=inst.coms[-1] if inst.coms else [],
                           com=com_new, v=v)
    return proof, cons, w_hat, c_chal, F_new, FU


def build_constraints(
    inst, packing, c_chal, ring, l_prime, F_new, FU, com_new, v
) -> List[ScConstraint]:
    """The sumcheckified constraint system (Figure 4 step 7 / §6.2 example):
    folded linear blocks as lin-diff claims (LHS row(x)g_l on the w_tilde
    block vs RHS gadget-folded selector on the Y blocks), commitment
    well-formedness rows, and the exact norm claim."""
    cons: List[ScConstraint] = []
    total = packing.total
    # (a) folded linear blocks: <f^j (x) g_{l'}, w_tilde> = <y_j-block, c-folded>
    #     encoded as lin-diff: LHS selector on the w_tilde block vs RHS
    #     selector on the packed Y blocks (both public tables over w_hat)
    for i in range(len(inst.F)):
        for j, row in enumerate(inst.F[i]):
            a_L = _row_gadget_on_block(row, l_prime, packing, 0, ring, total)
            # RHS: c-folded selector on the committed Y-block: y_j = (H_i Y_i)
            # row j — for the lab H_i = F_i-key rows acting on Y; we place the
            # c-weighted Y rows directly (public because c and the block
            # layout are public; Y itself is verified via the (b) rows).
            a_R = _c_folded_selector(inst, i, j, c_chal, packing, ring, total)
            cons.append(ScConstraint(kind="lindiff", a_L=a_L, a_R=a_R))
    # (b) commitment well-formedness: <F_new[j], w_hat> = com_new[j]
    for j, key_row in enumerate(F_new):
        a0 = [ring.zero() for _ in range(total)]
        for k, kv in enumerate(key_row):
            a0[k] = kv
        cons.append(ScConstraint(kind="lin", a_L=a0, value=com_new[j]))
    # (c) exact norm: <w_hat, conj(w_hat)> = v
    cons.append(ScConstraint(kind="norm", value=v))
    return cons


def _row_gadget_on_block(row, l, packing, block_idx, ring, total) -> List[RingElt]:
    """Public table: the row (x) g_l placed on the w_tilde block of the
    packed vector (§6.2 worked example — prefix selector folded in)."""
    out = [ring.zero() for _ in range(total)]
    off, m, _ = packing.blocks[block_idx]
    for t, rv in enumerate(row):
        for e in range(l):
            pos = off + t * l + e
            if pos < total:
                out[pos] = rv * (1 << e)
    return out


def _c_folded_selector(inst, i, j, c_chal, packing, ring, total) -> List[RingElt]:
    """RHS public table: the c-weighted (H_i Y_i) row placed on the packed
    Y-block.  (H_i Y_i)[j, col] = sum_k H_i[j][k] Y_i[k][col]; folded target
    = sum_col c_col (H_i Y_i)[j,col].  The Y values enter through the packed
    vector's block, so the table places the H_i row (x) c-weights there."""
    out = [ring.zero() for _ in range(total)]
    # the Y_i block starts after the w_tilde block
    y_block = 1 + i if len(packing.blocks) > 1 + i else None
    if y_block is None:
        return out
    off, m, _ = packing.blocks[y_block]
    H_i = inst.H[i] if inst.H else None
    Y_len = len(inst.Ys[i]) if inst.Ys else 0
    r = len(c_chal)
    # packed position of Y_i[k][col] is off + k*r + col (row-major columns);
    # the folded RHS weight at that position is H_i[j][k] * c_col.
    for k in range(min(m // r if r else m, Y_len)):
        if H_i is None or j >= len(H_i) or k >= len(H_i[j]):
            continue
        for col in range(r):
            out[off + k * r + col] = H_i[j][k] * c_chal[col]
    return out


# --------------------------------------------------------------------------- #
#  Π^lin — linearisation (Figure 6)  [R1/R4]
# --------------------------------------------------------------------------- #


@dataclass
class LinProof:
    round_polys: List[List]     # nu rounds, degree <= 2 coefficient form
    z0: RingElt                 # MLE[w_hat](c) — final evaluation
    z1: RingElt                 # MLE[conj(w_hat)](c)
    gamma: List[RingElt]        # claim-batching challenges
    final_values: List = field(default_factory=list)
    point: List = field(default_factory=list)


def lin_prove(
    w_hat: Sequence[RingElt],
    cons: Sequence[ScConstraint],
    ring: Ring,
    transcript: Transcript,
) -> LinProof:
    """Π^lin prover (Figure 6): batch all constraints' product groups with
    eq(bin(i), gamma) combiners (explicit RingSC combiners; the sign of
    lin-diff groups is folded into the negated table), run ONE sumcheck,
    output z0/z1."""
    groups: List[ProductClaim] = []
    combiners: List[RingElt] = []
    k = len(cons)
    log_k = max(0, (k - 1).bit_length())
    gamma = [ring.challenge(transcript, label=f"rk:gamma{i}") for i in range(log_k)]
    comb = _eq_bin_combiners(gamma, k, ring)
    for ci, con in zip(comb, cons):
        for g in con.groups(w_hat):
            groups.append(g)
            combiners.append(ci)
    sc = RingSC(groups, ring)
    proof = sc.prove(transcript, explicit_combiners=combiners)
    z0 = mle_eval(list(w_hat), proof.point)
    z1 = mle_eval([x.conjugate() for x in w_hat], proof.point)
    return LinProof(round_polys=proof.round_polys, z0=z0, z1=z1, gamma=gamma,
                    final_values=proof.final_values, point=proof.point)


def lin_verify(
    cons: Sequence[ScConstraint],
    proof: LinProof,
    ring: Ring,
    transcript: Transcript,
) -> Tuple[bool, RingElt]:
    """Π^lin verifier: re-derive gamma, check the batched sumcheck rounds and
    the TERMINAL identity with z0/z1-substituted groups.  Returns
    (ok, last_claim)."""
    k = len(cons)
    log_k = max(0, (k - 1).bit_length())
    gamma = [ring.challenge(transcript, label=f"rk:gamma{i}") for i in range(log_k)]
    comb = _eq_bin_combiners(gamma, k, ring)
    # combined target: sum_i comb_i * (constraint value) — lin/norm carry
    # public values; lindiff constraints contribute 0
    target = ring.zero()
    for ci, con in zip(comb, cons):
        if con.kind in ("lin", "norm"):
            target = target + ci * con.value
    nu = len(proof.round_polys)
    ok, _, last = verify_round_polys(proof.round_polys, target, nu, 2, ring, transcript)
    if not ok:
        return False, None
    # terminal: sum_g comb_g * prod MLE[T_g](point) == last, with private
    # slots substituted by [z0]/[z1]
    total = ring.zero()
    for ci, con in zip(comb, cons):
        for vg in con.verifier_groups(proof.z0, proof.z1, nu):
            prod = mle_eval(vg[0], proof.point)
            for t in vg[1:]:
                prod = prod * mle_eval(t, proof.point)
            total = total + ci * prod
    if total != last:
        return False, None
    return True, last


# --------------------------------------------------------------------------- #
#  Round driver (R5): full argument with terminal opening
# --------------------------------------------------------------------------- #


@dataclass
class RoKokoProof:
    fold_proof: FoldSplitProof
    lin_proof: LinProof
    constraints: List[ScConstraint]
    w_hat: List[RingElt]            # terminal opening (direct reveal)
    F_new: List[List[RingElt]]


def rokoko_prove(
    inst: LinComInstance,
    ck: ComKey,
    transcript: Transcript,
    l_prime: int | None = None,
) -> RoKokoProof:
    """One full committed-refinement round (fold-split -> sumcheckify ->
    lin) + direct terminal opening of the packed witness.  Multi-round
    shrinking repeats the same flow on the packed vector (structural support
    tested at rounds=1; see gap ledger)."""
    fproof, cons, w_hat, c_chal, F_new, FU = fold_split_prove(
        inst, ck, transcript, l_prime=l_prime
    )
    lproof = lin_prove(w_hat, cons, ck.p.ring, transcript)
    return RoKokoProof(fold_proof=fproof, lin_proof=lproof, constraints=cons,
                       w_hat=w_hat, F_new=F_new)


def rokoko_verify(
    inst: LinComInstance,
    ck: ComKey,
    proof: RoKokoProof,
    transcript: Transcript,
    l_prime: int | None = None,
) -> bool:
    p = ck.p
    if l_prime is None:
        l_prime = p.gadget_len
    ring = p.ring
    fproof, lproof = proof.fold_proof, proof.lin_proof
    # ---- fold-split verifier (Figure 4 right): replay the transcript
    # operations (absorb the statement's commitments, draw c) so the lin
    # verifier's challenges re-derive identically
    transcript.absorb_bytes(b"rk:fold-split:start")
    for cm_i in inst.coms:
        for x in cm_i:
            transcript.absorb_ring(x)
    c_chal = [ring.challenge(transcript, label=f"rk:c{i}") for i in range(inst.r)]
    # ct(v) <= beta_tilde^2  (Remark 3 power-of-two shortcut)
    beta_tilde = inst.beta_w * 4 * inst.r * (2 ** (l_prime + 2))
    ct_v = Ring.center(fproof.v.coeffs[0], ring.q)
    if ct_v < 0 or ct_v > beta_tilde * beta_tilde:
        return False
    # ---- lin verifier: rounds + terminal identity with z0/z1
    ok, _ = lin_verify(proof.constraints, lproof, ring, transcript)
    if not ok:
        return False
    # ---- terminal opening checks (direct reveal of w_hat):
    w_hat = proof.w_hat
    # (1) commitment binding: F_new . w_hat == com
    FU = mat_vec(proof.F_new, w_hat)
    if list(FU) != list(fproof.com):
        return False
    # (2) exact norm: <w_hat, conj(w_hat)> == v
    if norm_conjugate_inner(w_hat) != fproof.v:
        return False
    # (3) every constraint holds directly against the revealed w_hat
    for con in proof.constraints:
        if con.kind == "lindiff":
            lhs = dot(con.a_L, w_hat)
            rhs = dot(con.a_R, w_hat)
            if lhs != rhs:
                return False
        elif con.kind == "lin":
            if dot(con.a_L, w_hat) != con.value:
                return False
        else:
            if norm_conjugate_inner(w_hat) != con.value:
                return False
    return True
