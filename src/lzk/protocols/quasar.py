"""Quasar: sublinear multi-cast commitment mixing in recursive accumulation (lab module).

Paper: "Quasar: Sublinear Multi-Cast Commitment Mixing in Recursive Accumulation" (Zheng et al.).  See docs/papers/quasar.md for the full
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


class Quasar:
    def __init__(self, ring: Ring, m: int, arity: int = 2):
        self.ring = ring
        self.m = m
        self.arity = arity

    def union_commit(self, ws: Sequence[Sequence[RingElt]]) -> List[RingElt]:
        """The union polynomial's coefficient vector: the multi-cast commit
        mixes arity witnesses on the arity hypercube (union poly)."""
        ring = self.ring
        total = self.m * len(ws)
        union = [ring.zero() for _ in range(total)]
        for i, w in enumerate(ws):
            for j in range(self.m):
                union[i * self.m + j] = union[i * self.m + j] + w[j]
        return union

    def accumulate_fold(self, acc: Sequence[RingElt],
                        ws: Sequence[Sequence[RingElt]],
                        transcript: Transcript):
        """One accumulation step: the 2-to-1 fold with the gamma-ladder —
        the union poly is folded into the accumulator keeping the interface
        (shape) constant across steps (the paper's IOR accumulator)."""
        ring = self.ring
        k = len(ws)
        gammas = [ring.challenge_small(transcript, label=f"qs:g{i}") for i in range(k)]
        union = self.union_commit(ws)
        # fold: acc* = acc + sum_i gamma_i * (union blocks)
        acc_star = [
            acc[j] + sum((union[i * self.m + j] * gammas[i] for i in range(k)),
                         start=ring.zero())
            for j in range(self.m)
        ]
        return acc_star, gammas, union
