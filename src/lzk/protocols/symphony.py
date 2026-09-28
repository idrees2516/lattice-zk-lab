"""Symphony: scalable SNARKs in the ROM from lattice-based high-arity folding (lab module).

Paper: "Symphony: Scalable SNARKs in the Random Oracle Model from Lattice-Based High-Arity Folding" (B. Chen).  See docs/papers/symphony.md for the full
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


class Symphony:
    def __init__(self, ring: Ring, m: int, arity: int = 4):
        self.ring = ring
        self.m = m
        self.arity = arity

    def high_arity_fold(self, ws: Sequence[Sequence[RingElt]],
                        transcript: Transcript):
        """One arity-4 accumulation: the witnesses are folded with a
        challenge VECTOR (not a scalar) — the high-arity fold compresses 4
        instances per round; the composition uses folding as a black box
        (no hash function embedded in the circuit: the ROM argument)."""
        ring = self.ring
        k = len(ws)
        chal = [ring.challenge_small(transcript, label=f"sy:c{i}") for i in range(k)]
        # the fold: w* = sum_i L_i(c) w_i with the arity-4 power basis
        w_star = [
            sum((ws[i][j] * chal[i] for i in range(k)), start=ring.zero())
            for j in range(self.m)
        ]
        norm_val = norm_conjugate_inner(w_star)
        return w_star, chal, norm_val

    def compose_rounds(self, batches: Sequence[Sequence[Sequence[RingElt]]],
                       transcript: Transcript):
        """Multi-round high-arity accumulation (the scalable SNARK shape):
        each batch folds arity instances; accumulators chain."""
        acc = None
        for b_idx, batch in enumerate(batches):
            if acc is not None:
                batch = [acc] + list(batch[: self.arity - 1])
            acc, _, norm_val = self.high_arity_fold(batch, transcript)
        return acc, norm_val
