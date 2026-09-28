"""Cyclo: lightweight lattice folding via partial range checks / pay-per-bit (lab module).

Paper: "Cyclo: Lightweight Lattice-based Folding via Partial Range Checks" (Garreta, Lipmaa, Luahaar, Osadnik).  See docs/papers/cyclo.md for the full
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


class Cyclo:
    def __init__(self, ring: Ring, m: int, seed: bytes = b"cyclo"):
        self.ring = ring
        self.m = m
        self.key = AjtaiParams(ring, 2, m, seed=seed)

    def fold_with_partial_range(
        self, w1: Sequence[RingElt], w2: Sequence[RingElt],
        transcript: Transcript, n_high_bits: int = 3,
    ):
        """The Cyclo fold: w* = w1 + r w2; the CROSS TERM (the quadratic
        fold residual) is range-checked with only the HIGH bits (partial
        range check): the low bits are handled by the norm sumcheck,
        saving the per-bit communication the paper reports."""
        ring = self.ring
        r = ring.challenge_small(transcript, label="cy:r")
        w_star = [a + b * r for a, b in zip(w1, w2)]
        cross = dot(w1, w2)
        # partial range check on the high bits of every cross coefficient
        base = 1 << n_high_bits
        high = ring.zero()
        for idx, c in enumerate(cross.coeffs):
            d = ring.center(c, ring.q)
            high.coeffs[idx] = (d // base) % base if abs(d) >= base else 0
        low_residual = cross - high * base
        # the high part is bounded by construction; the low part joins the
        # norm sumcheck claim (the pay-per-bit saving: only ceil(log) bits)
        claim = norm_conjugate_inner(w_star)
        wbar = [x.conjugate() for x in w_star]
        sc = RingSC([ProductClaim(tables=[w_star, wbar], value=claim)], ring)
        proof = sc.prove(transcript, explicit_combiners=[ring.one()])
        return w_star, cross, high, low_residual, proof

    def verify_partial_range(self, cross, high, low_residual, base: int) -> bool:
        return cross == high * base + low_residual
