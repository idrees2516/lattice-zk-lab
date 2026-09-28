"""PikkuFold: efficient folding in a few KB via layered random projections (lab module).

Paper: "PikkuFold: Efficient Folding in a Few Kilobytes" (Osadnik).  See docs/papers/pikkufold.md for the full
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


class PikkuFold:
    def __init__(self, ring: Ring, m: int, layers: int = 2, factor: int = 2):
        self.ring = ring
        self.m = m
        self.layers = layers
        self.factor = factor

    def _sparse_proj(self, v: Sequence[RingElt], seed_label: str,
                     transcript: Transcript) -> List[RingElt]:
        """One sparse random projection layer: each output coordinate mixes
        `factor` inputs with small challenges (the layered structure whose
        final image is short)."""
        ring = self.ring
        out_len = max(1, len(v) // self.factor)
        out = [ring.zero() for _ in range(out_len)]
        for o in range(out_len):
            for f in range(self.factor):
                idx = (o * self.factor + f) % len(v)
                c = ring.challenge_small(transcript, label=f"{seed_label}:{o}:{f}")
                out[o] = out[o] + v[idx] * c
        return out

    def fold_lrp(self, w1: Sequence[RingElt], w2: Sequence[RingElt],
                 transcript: Transcript):
        """Fold + layered random projections: the folded witness is
        compressed through the projection stack; the SHORT final image is
        what gets communicated (the paper's few-KB step)."""
        ring = self.ring
        r = ring.challenge_small(transcript, label="pf:r")
        w = [a + b * r for a, b in zip(w1, w2)]
        images = [list(w)]
        cur = w
        for L in range(self.layers):
            cur = self._sparse_proj(cur, f"pf:L{L}", transcript)
            images.append(list(cur))
        norm_val = norm_conjugate_inner(cur)
        return w, images, cur, norm_val

    def verify_lrp(self, images, final_image, norm_val, beta: int) -> bool:
        tr = trace_balanced(norm_val)
        if tr < 0 or tr > self.ring.n * beta * beta:
            return False
        return images[-1] == list(final_image)
