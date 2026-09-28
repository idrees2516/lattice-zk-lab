"""Serval: slack-free l2-sound polynomial commitments — split-and-fold IPA (lab module).

Paper: "Serval: Slack-Free l2-Sound Polynomial Commitments from Lattices" (Zhang et al.).  See docs/papers/serval.md for the full
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


class Serval:
    def __init__(self, ring: Ring, m: int):
        self.ring = ring
        self.m = m

    def split_fold_round(self, v: Sequence[RingElt], transcript: Transcript):
        """One split-and-fold round: v -> (v_L, v_R); the cross-term quartet
        (L, M1, M2, R) with the challenge pair; the exact-norm bookkeeping
        (slack-free): t is maintained as the true conjugate inner product."""
        ring = self.ring
        half = len(v) // 2
        v_L, v_R = list(v[:half]), list(v[half:])
        # quartet
        L = dot(v_L, v_L)
        M1 = dot(v_L, v_R)
        M2 = dot(v_R, v_L)
        R = dot(v_R, v_R)
        # challenge pair (c, c') with the quadratic fold
        c = ring.challenge_small(transcript, label="sv:c")
        cp = ring.challenge_small(transcript, label="sv:cp")
        v_next = [a * c + b * cp for a, b in zip(v_L, v_R)]
        # the exact norm bookkeeping: t' = c^2 L + c cp M1 + cp c M2 + cp^2 R
        t_next = (L * c * c + M1 * c * cp + M2 * cp * c + R * cp * cp)
        return v_next, (L, M1, M2, R), t_next

    def run_ipa(self, v: Sequence[RingElt], transcript: Transcript):
        """The full log-round IPA: the claim <a, v> = b for a public a,
        maintaining the exact l2 norm (slack-free extraction)."""
        ring = self.ring
        t_final = norm_conjugate_inner(v)
        history = []
        cur = list(v)
        while len(cur) > 1:
            v_next, quartet, t_next = self.split_fold_round(cur, transcript)
            history.append((quartet, t_next))
            cur = v_next
        return cur[0], history, t_final
