"""RingSC — the shared ring sumcheck engine (lab item 7.8).

This module implements the *generalized sumcheck over rings* (LatticeFold+
Lemma 2.7 / SALSAA Π_sum Fig. 2) plus the two claim shapers every protocol
composes:

* **Π_norm** (SALSAA Fig. 4 / LatticeFold+ norm-check layer): the prover
  computes the conjugate inner product ``t = sum_j conj(w_j) w_j`` directly —
  O(m) ring multiply-adds, no convolution, no auxiliary commitment (the
  SALSAA prover-efficiency trick) — the verifier checks the *balanced integer
  trace* ``Tr(t) <= n beta^2`` (wraparound-free by 4 beta'^2 < q), and the
  pair ``(t, W)`` is proven by a degree-2 sumcheck
  ``sum_z MLE[W](z) * MLE[Wbar](z) = t``.

* **Π_batch** (SALSAA Fig. 3): bottom-row claims of a committed linear
  relation are batched with a challenge power ladder ``c^j`` into a single
  degree-2 sumcheck claim ``sum_z MLE[h](z) * MLE[W](z) = s``.

* **Power-ladder / alpha-combiner batching** (LF+ Remarks 2.5-2.6): several
  product claims over the same cube compress into one sumcheck with random
  combiners.

Round messages are in COEFFICIENT form (LF+ §5.0 convention):
``g_i(X) = sum_{b} f(rho_<i, X, b)`` sent as its ``ell+1`` coefficients;
verifier checks ``g_i(0) + g_i(1) = previous`` (g(1) = sum of coefficients),
samples ``rho_i`` from the ring (the sampling set C), computes the running
claim by Horner.  After the last round the protocol reduces to point-opening
claims which the caller supplies its own opening step for (LF+ §5.0: "this is
where each sub-protocol supplies its own opening step").
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, List, Sequence, Tuple

from .ring import Ring, RingElt
from .sumcheck import (
    SumcheckProduct,
    bind_table,
    eq_eval,
    eq_table,
    mle_eval,
)

# --------------------------------------------------------------------------- #
#  Claim specification
# --------------------------------------------------------------------------- #


@dataclass
class ProductClaim:
    """sum_{x in {0,1}^mu}  prod_j MLE[T_j](x)  =  value."""

    tables: List[List]  # each table: 2^mu values (RingElt / int)
    value: object  # ring element / int


@dataclass
class RingSCProof:
    """Round messages (coefficient form) + the final opening claims."""

    round_polys: List[List]  # mu rounds; each ell+1 coefficients
    degree: int
    # final per-table bound values, flat across all groups (in group order)
    final_values: List = field(default_factory=list)
    # the verifier's challenge point (rho_0..rho_{mu-1}) — carried so callers
    # can evaluate their public tables at it without replaying the transcript
    point: List = field(default_factory=list)


class RingSC:
    """Engine for one *combined* sumcheck over several product claims.

    groups: list of (tables, value) ProductClaims — the claim proven is
        sum over groups of  alpha^g * (product claim g)
    for random combiners alpha drawn from the transcript (LF+ batching mode).
    """

    def __init__(self, groups: Sequence[ProductClaim], ring: Ring):
        lens = {len(t[0]) for g in groups for t in [g.tables]}
        if len(lens) != 1:
            raise ValueError("all tables must share the hypercube size")
        self.groups = list(groups)
        self.ring = ring
        self.mu = (lens.pop() - 1).bit_length()
        self.degree = max(len(g.tables) for g in groups)

    # ------------------------------------------------------------------ setup #
    def combiners(self, transcript, explicit: Sequence[RingElt] | None = None) -> List[RingElt]:
        """Combiners: drawn from the transcript by default, or EXPLICIT
        (protocol-supplied batching weights, e.g. RoKoko's eq(bin(i), gamma)
        claim combiners — must be identical on both sides)."""
        if explicit is not None:
            if len(explicit) != len(self.groups):
                raise ValueError("explicit combiner count mismatch")
            return list(explicit)
        return [
            self.ring.challenge(transcript, label=f"ringsc:alpha{g}")
            for g in range(len(self.groups))
        ]

    def combined_claim(self, alphas: Sequence[RingElt]) -> RingElt:
        acc = self.ring.zero()
        for a, g in zip(alphas, self.groups):
            acc = acc + a * g.value
        return acc

    # ------------------------------------------------------------------ prover #
    def prove(self, transcript, explicit_combiners: Sequence[RingElt] | None = None) -> RingSCProof:
        """Run the full sumcheck; challenges drawn from ``transcript``.
        Returns the proof (round messages + final openings)."""
        alphas = self.combiners(transcript, explicit_combiners)
        # per-group bound table state
        bound = [ [list(t) for t in g.tables] for g in self.groups ]
        round_polys: List[List] = []
        point: List[RingElt] = []
        mus = self.mu
        for i in range(mus):
            # round polynomial = sum_g alpha^g * g_i^group(X)
            acc: List = [self.ring.zero() for _ in range(self.degree + 1)]
            for a, tables in zip(alphas, bound):
                # compute this group's round polynomial (degree = len(tables))
                half = len(tables[0]) // 2
                d_g = len(tables)
                poly_acc = [self.ring.zero() for _ in range(d_g + 1)]
                for idx in range(half):
                    low = [T[idx] for T in tables]
                    high = [T[idx + half] for T in tables]
                    poly = [self.ring.one()]
                    for lo, hi in zip(low, high):
                        delta = hi - lo
                        new = [self.ring.zero() for _ in range(len(poly) + 1)]
                        for d, c in enumerate(poly):
                            new[d] = new[d] + c * lo
                            new[d + 1] = new[d + 1] + c * delta
                        poly = new
                    for d, c in enumerate(poly):
                        poly_acc[d] = poly_acc[d] + c
                for d in range(self.degree + 1):
                    term = poly_acc[d] if d < len(poly_acc) else self.ring.zero()
                    acc[d] = acc[d] + a * term
            round_polys.append(acc)
            # absorb round message, draw challenge, bind all groups
            transcript.absorb_bytes(b"ringsc-round")
            for c in acc:
                transcript.absorb_ring(c)
            rho = self.ring.challenge(transcript, label=f"ringsc:rho{i}")
            point.append(rho)
            bound = [[bind_table(T, rho) for T in tables] for tables in bound]
        final_values = [T[0] for tables in bound for T in tables]
        return RingSCProof(round_polys=round_polys, degree=self.degree,
                           final_values=final_values, point=point)

    # ---------------------------------------------------------------- verifier #
    def verify(self, proof: RingSCProof, transcript, explicit_combiners: Sequence[RingElt] | None = None) -> Tuple[bool, List, RingElt]:
        """Verify round messages against the combined claim; returns
        (ok, final_values, last_claim).  The caller must check the final
        values against its own opening logic (terminal check).  Verification
        only needs the combined claim, mu and degree — not the witness
        tables."""
        alphas = self.combiners(transcript, explicit_combiners)
        claim = self.combined_claim(alphas)
        return verify_round_polys(
            proof.round_polys, claim, self.mu, self.degree, self.ring, transcript
        )


def _horner(poly: Sequence, r: RingElt, ring: Ring) -> RingElt:
    acc = ring.zero()
    for c in reversed(list(poly)):
        acc = acc * r + c
    return acc


def verify_round_polys(
    round_polys: List[List],
    claim: RingElt,
    mu: int,
    degree: int,
    ring: Ring,
    transcript,
) -> Tuple[bool, List, RingElt]:
    """Standalone verification of RingSC round messages (coefficient form):
    g_i(0) + g_i(1) == previous claim, degree bound, challenges re-derived
    from the transcript.  Returns (ok, final_values, last_claim) — the
    caller checks the terminal identity on final_values itself."""
    if len(round_polys) != mu:
        return False, None, None
    prev = claim
    for i in range(mu):
        poly = round_polys[i]
        if len(poly) - 1 > degree:
            return False, None, None
        g0 = poly[0]
        g1 = ring.zero()
        for c in poly:
            g1 = g1 + c
        if g0 + g1 != prev:
            return False, None, None
        transcript.absorb_bytes(b"ringsc-round")
        for c in poly:
            transcript.absorb_ring(c)
        rho = ring.challenge(transcript, label=f"ringsc:rho{i}")
        prev = _horner(poly, rho, ring)
    return True, None, prev


# --------------------------------------------------------------------------- #
#  Π_norm — the conjugate inner-product norm check (SALSAA Fig. 4) [A2]
# --------------------------------------------------------------------------- #


@dataclass
class NormProof:
    t: RingElt                      # claimed conjugate inner product
    sc_proof: RingSCProof           # sumcheck of sum_z MLE[W](z) MLE[Wbar](z) = t
    final_w: RingElt                # MLE[W](r)
    final_wbar: RingElt             # MLE[Wbar](r)


def norm_conjugate_inner(w: Sequence[RingElt]) -> RingElt:
    """t = sum_j conj(w_j) * w_j  — the O(m) direct computation."""
    ring = w[0].ring
    acc = ring.zero()
    for x in w:
        acc = acc + x.conjugate() * x
    return acc


def trace_balanced(t: RingElt) -> int:
    """Balanced integer trace for power-of-two cyclotomics:
    Tr(a) = n * a_0 with a_0 the centred constant coefficient."""
    ring = t.ring
    return ring.n * Ring.center(t.coeffs[0], ring.q)


def norm_check_prove(
    w: Sequence[RingElt], transcript, beta: int
) -> NormProof:
    """SALSAA Π_norm + Π_sum: prove ||W||^2 (coefficient l2 norm) with the
    conjugate inner product and a degree-2 sumcheck.  The trace check uses
    the lab convention trace_balanced(t) = n * ||W||^2 <= n * beta^2."""
    ring = w[0].ring
    t = norm_conjugate_inner(w)
    # sumcheck: sum_z MLE[W](z) * MLE[Wbar](z) = t
    wbar = [x.conjugate() for x in w]
    sc = RingSC([ProductClaim(tables=[list(w), list(wbar)], value=t)], ring)
    proof = sc.prove(transcript)
    return NormProof(t=t, sc_proof=proof, final_w=proof.final_values[0],
                     final_wbar=proof.final_values[1])


def norm_check_verify(
    proof: NormProof, transcript, beta: int, ring: Ring, mu: int
) -> Tuple[bool, RingElt, RingElt]:
    """Returns (ok, MLE[W](r), MLE[Wbar](r)) — the opening claims the caller
    must bind to the commitment (e.g. via the tensor RoK / folding).
    ``mu`` = log2(len(w)) is the hypercube dimension of the witness."""
    # integer trace check (wraparound-free regime)
    tr = trace_balanced(proof.t)
    if tr < 0 or tr > ring.n * beta * beta:
        return False, None, None
    # mirror the prover's combiner draw (single group => alpha0)
    alpha0 = ring.challenge(transcript, label="ringsc:alpha0")
    claim = alpha0 * proof.t
    ok, _, last = verify_round_polys(
        proof.sc_proof.round_polys, claim, mu, 2, ring, transcript
    )
    if not ok:
        return False, None, None
    # terminal check: alpha * (final_w * final_wbar) == last claim
    if alpha0 * (proof.final_w * proof.final_wbar) != last:
        return False, None, None
    # conjugation consistency: MLE[Wbar](r) must equal conj(MLE[W])(r̄)... the
    # lab checks the algebraic identity conj(final_w) == final_wbar when the
    # challenge point is fixed-point-free; protocols enforce this at their
    # opening layer.
    return True, proof.final_w, proof.final_wbar


# --------------------------------------------------------------------------- #
#  Π_batch — bottom-row batching of committed linear relations (Fig. 3) [A1]
# --------------------------------------------------------------------------- #


def batch_linear_rows(
    rows: Sequence[Sequence[RingElt]],  # n_b bottom rows, each length m
    targets: Sequence[RingElt],         # Y_bottom, length n_b
    w: Sequence[RingElt],               # witness (prover side; None on verifier)
    transcript,
    ring: Ring,
):
    """Π_batch: batch bottom rows of a committed linear relation into ONE
    degree-2 sumcheck claim.

    Verifier:  c <-$ R_q;  s = sum_j c^j Y_j;  h = sum_j c^j rows_j (an MLE).
    Claim:     sum_z MLE[h](z) * MLE[W](z) = s.

    Returns (c, s, h_table) — the caller feeds the ProductClaim into RingSC
    together with its other claims.
    """
    n_b = len(rows)
    c = ring.challenge(transcript, label="batch:c")
    # h = sum_j c^j row_j  (table of length m)
    m = len(rows[0])
    h = [ring.zero() for _ in range(m)]
    s = ring.zero()
    for j, (row, y) in enumerate(zip(rows, targets)):
        cp = pow_ring(c, j, ring)
        for idx in range(m):
            h[idx] = h[idx] + row[idx] * cp
        s = s + y * cp
    return c, s, h


def pow_ring(c: RingElt, e: int, ring: Ring) -> RingElt:
    """Fast exponentiation of a ring element."""
    if e == 0:
        return ring.one()
    if e == 1:
        return c
    half = pow_ring(c, e // 2, ring)
    return half * half if e % 2 == 0 else half * half * c


# --------------------------------------------------------------------------- #
#  MLE opening helpers shared by all protocols (LF+ §5.0 API)
# --------------------------------------------------------------------------- #


def open_mle(table: Sequence, r: Sequence) -> object:
    """Evaluate the MLE of ``table`` at point ``r`` (the final opening)."""
    return mle_eval(table, r)


def eval_tensor(c: Sequence[int], r: Sequence) -> int:
    """LF+ tensor(r) = eq indicator: prod_i ((1-r_i)(1-c_i) + r_i c_i)."""
    return eq_eval(list(c), list(r))


def tensor_table(r: Sequence, mu: int) -> List[int]:
    """The eq(r, .) table — LF+ calls this tensor(r)."""
    return eq_table(list(r), mu)
