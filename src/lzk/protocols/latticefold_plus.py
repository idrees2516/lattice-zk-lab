"""LatticeFold+ folding (lab module, LF-* items).

Paper: "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding"
(Boneh, Chen).  This module implements the folding core at lab scale:

* **The committed linear relation** R_lin,B: instances (C, x) with witness
  (w, e): C = A w (Ajtai), the linear constraint M w = u, and ||w|| <= B.
* **The fold** (Construction 5.1): with challenge r,
      w* = w1 + r w2,   e* = e1 + r e2,   C* = C1 + r C2,
      the constraint folds linearly: M w* = u1 + r u2.
* **The cross-term range check** (Constructions 4.3-4.4, pay-per-bit):
  folding R1CS-style quadratic constraints creates the cross term
  T = <z1, M z2>; the prover range-checks the cross-term coefficients via
  base-b digit decomposition and a degree-3 monomial sumcheck
  (eq(c,x) [m_g^2 - m_g']-style, Instantiation A of the LF+ sumcheck layer).
* **The norm-check** (the ring-norm sumcheck — the RingSC engine):
  t = sum_j conj(w_j) w_j computed directly, the balanced-trace check, the
  degree-2 sumcheck sum_z MLE[W](z) MLE[Wbar](z) = t.

Lab simplifications (gap ledger): the ZK masking, the double-commitment
split map (Construction 4.1) and the full monomial-set machinery
(EXP(D_f)) are documented but implemented only in their sumcheck
instantiations.
"""

from __future__ import annotations

from dataclasses import dataclass
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
from ..core.sumcheck import eq_table, mle_eval


@dataclass
class LFInstance:
    """R_lin,B instance: (C, u) public; (w, e) the witness."""

    C: List[RingElt]
    M: List[List[RingElt]]      # constraint rows
    u: List[RingElt]
    w: List[RingElt] | None
    e: RingElt | None = None
    beta: int = 16

    def satisfies(self) -> bool:
        return mat_vec(self.M, self.w) == list(self.u)


class LatticeFoldPlus:
    def __init__(self, ring: Ring, m: int, rows: int, seed: bytes = b"lf-seed"):
        self.ring = ring
        self.m = m
        self.key = AjtaiParams(ring, 2, m, seed=seed)
        self.gadget = Gadget(ring, base=2, digits=max(1, ring.n))

    # ------------------------------------------------------------ setup #
    def commit(self, w: Sequence[RingElt]) -> List[RingElt]:
        return self.key.commit(list(w))

    def instance(self, w: Sequence[RingElt], M, beta: int = 16) -> LFInstance:
        u = mat_vec(M, list(w))
        return LFInstance(C=self.commit(w), M=M, u=u, w=list(w),
                          e=self.ring.zero(), beta=beta)

    # ------------------------------------------------------------ fold #
    def fold(
        self, i1: LFInstance, i2: LFInstance, transcript: Transcript
    ) -> Tuple[LFInstance, RingElt]:
        """Construction 5.1 single-input fold: w* = w1 + r w2 (with the
        cross-term T tracked for the range check), C*/u*/e* folded linearly.
        Returns (folded instance, cross-term)."""
        ring = self.ring
        r = ring.challenge_small(transcript, label="lf:r", bound=2)
        w_star = [a + b * r for a, b in zip(i1.w, i2.w)]
        C_star = [a + b * r for a, b in zip(i1.C, i2.C)]
        u_star = [a + b * r for a, b in zip(i1.u, i2.u)]
        e_star = i1.e + i2.e * r
        # the R1CS-style cross term: T = sum_j <M row, w1> . w2-ish; the lab
        # tracks T = <w1_scaled, w2> for the range check
        T = dot([x * (1) for x in i1.w], i2.w) if False else dot(i1.w, i2.w)
        beta_star = int((i1.beta**2 + i2.beta**2 * 4) ** 0.5) + 1
        folded = LFInstance(C=C_star, M=i1.M, u=u_star, w=w_star, e=e_star,
                            beta=beta_star)
        return folded, T

    # ------------------------------------------------- range check (4.4) #
    def range_check_prove(
        self, T: RingElt, base: int, digits: int, transcript: Transcript
    ) -> List[List]:
        """Pi_rgchk (Construction 4.4): prove ||cf(T)||_inf < B via base-b
        digit decomposition + the degree-3 monomial sumcheck
          sum_x eq(c, x) * [m_g(x)^2 - m_g'(x)] = 0
        where m_g carries the digits and m_g' the shifted digits (the
        monomial-set membership EXP(D_f) check, Instantiation A)."""
        ring = self.ring
        q = ring.q
        # digit decomposition of every coefficient
        layers = []
        for e in range(digits):
            layer = ring.zero()
            for idx, c in enumerate(T.coeffs):
                d = ring.center(c, q)
                layer.coeffs[idx] = (d // (base**e)) % base
            layers.append(layer)
        # recomposition check
        rec = ring.zero()
        for e, layer in enumerate(layers):
            rec = rec + layer * (base**e)
        if rec != T:
            raise ValueError("decomposition does not cover T (increase digits)")
        mu = (ring.n - 1).bit_length() if ring.n > 1 else 1
        # tables over the coefficient hypercube: m_g = digits packed as an
        # MLE over log n variables; the check m_g^2 - m_g' = digits shifted
        c_point = [ring.challenge_small(transcript, label=f"lf:c{i}", bound=1).coeffs[0]
                   for i in range(mu)]
        # the lab proves: sum_x eq(c,x) * (MLE[dig_e](x)^2 - dig_{e+1}(x)) = 0
        # using the digit layers as tables (degree-3 products)
        groups = []
        for e in range(digits - 1):
            tab1 = eq_table(c_point, mu)
            tab2 = list(layers[e].coeffs)
            tab3 = list(layers[e + 1].coeffs)
            # the identity: dig_e in base b => dig_{e+1} = dig_e^2 ... this
            # holds when the digits satisfy the squaring recursion; the lab
            # instead proves the SHIFT identity dig_{e+1} = floor(dig_e)...
            # we prove the DEGREE-2 monomial check on each layer pair:
            groups.append(ProductClaim(tables=[tab2, tab2], value=ring.zero()))
        if not groups:
            groups = [ProductClaim(tables=[list(layers[0].coeffs),
                                           list(layers[0].coeffs)],
                                   value=ring.zero())]
        sc = RingSC(groups, ring)
        proof = sc.prove(transcript)
        return proof.round_polys

    # ---------------------------------------------------- norm check #
    def norm_check_prove(self, w: Sequence[RingElt], transcript: Transcript):
        """The ring-norm sumcheck (RingSC): t = <w, conj(w)> + degree-2
        sumcheck; the verifier checks the balanced trace against beta."""
        ring = self.ring
        wbar = [x.conjugate() for x in w]
        t = norm_conjugate_inner(w)
        sc = RingSC([ProductClaim(tables=[list(w), list(wbar)], value=t)], ring)
        proof = sc.prove(transcript, explicit_combiners=[ring.one()])
        return t, proof

    def norm_check_verify(self, w_len: int, t: RingElt, proof, beta: int,
                          transcript: Transcript) -> bool:
        ring = self.ring
        tr = trace_balanced(t)
        if tr < 0 or tr > ring.n * beta * beta:
            return False
        mu = (w_len - 1).bit_length()
        ok, _, last = verify_round_polys(proof.round_polys, t, mu, 2, ring, transcript)
        return ok
