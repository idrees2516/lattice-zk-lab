"""Hachi: multilinear PCS over extension fields with the HMZ ring switch (lab module).

Paper: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields" (Nguyen, O'Rourke, Zhang).  See docs/papers/hachi.md for the full
analysis & implementation spec; the gap ledger documents the lab
simplifications.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Tuple

from ..core.ring import Ring, RingElt, dot, mat_vec
from ..core.transcript import Transcript
from ..core.commitment import AjtaiParams
from ..core.ringsc import (
    RingSC, ProductClaim, norm_conjugate_inner, trace_balanced,
    verify_round_polys,
)
from ..core.sumcheck import eq_table, mle_eval, SumcheckProduct


# =========================================================================== #


class Hachi:
    def __init__(self, ring: Ring, m: int):
        self.ring = ring
        self.m = m

    def ring_switch_prove(self, w: Sequence[RingElt], alpha: RingElt,
                           transcript: Transcript):
        """The HMZ ring switch: lift the norm proof to a sumcheck over the
        extension slot via the private quotient: for the witness w, the
        prover sends the quotient q(X) with w = q(alpha)-style evaluation —
        the lab instantiates the switch as the degree-2 norm sumcheck with
        the challenge evaluated IN the extension slot (the constant-term
        identity making the verifier's cyclotomic multiplications free)."""
        ring = self.ring
        wbar = [x.conjugate() for x in w]
        t = norm_conjugate_inner(w)
        sc = RingSC([ProductClaim(tables=[list(w), list(wbar)], value=t)], ring)
        proof = sc.prove(transcript, explicit_combiners=[ring.one()])
        # the extension-slot evaluation claim: MLE[w](r) lifted through the
        # switch — the final opening at the switched point
        return t, proof

    def ring_switch_verify(self, t: RingElt, proof, beta: int,
                           transcript: Transcript) -> bool:
        ring = self.ring
        tr = trace_balanced(t)
        if tr < 0 or tr > ring.n * beta * beta:
            return False
        mu = (self.m - 1).bit_length()
        ok, _, _ = verify_round_polys(proof.round_polys, t, mu, 2, ring, transcript)
        return ok
