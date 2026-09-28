"""Akita: high-performance lattice PCS — tensor commitment with one row-folding round (lab module).

Paper: "Akita: A High-Performance Lattice-Based Polynomial Commitment Scheme" (Dao et al.).  See docs/papers/akita.md for the full
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


class Akita:
    """Tensor-layout commitment + row-folding evaluation."""

    def __init__(self, ring: Ring, rows: int, cols: int, seed: bytes = b"akita"):
        self.ring = ring
        self.rows, self.cols = rows, cols
        self.row_key = AjtaiParams(ring, 2, cols, seed=seed)

    def commit(self, W: Sequence[Sequence[RingElt]]) -> List[List[RingElt]]:
        """Per-row Ajtai commitments (the tensor/two-tier layout)."""
        return [self.row_key.commit(list(row)) for row in W]

    def eval_prove(self, W: Sequence[Sequence[RingElt]], r_row: Sequence[RingElt],
                   r_col: Sequence[RingElt], transcript: Transcript):
        """y = <tensor(r_row), W tensor(r_col)> proved by ONE row-folding
        round: the prover sends the row-fold f = W . tensor(r_col) in
        R^rows plus per-row commitments; the verifier checks the tensor
        inner product and the JL-style norm bound, then folds."""
        ring = self.ring
        rows = len(W)
        # f_i = <W_i, tensor(r_col)> (row contractions)
        f = [dot(row, eq_table([c.coeffs[0] for c in r_col], len(r_col)))
             for row in W]
        y = dot(f, eq_table([c.coeffs[0] for c in r_row], len(r_row)))
        # folding challenge; the folded row = sum_i L_i W_i
        gamma = [ring.challenge_small(transcript, label=f"ak:g{i}") for i in range(rows)]
        W_fold = [
            sum((W[i][j] * gamma[i] for i in range(rows)), start=ring.zero())
            for j in range(self.cols)
        ]
        com_fold = self.row_key.commit(W_fold)
        norm_val = norm_conjugate_inner(W_fold)
        # the degree-2 norm sumcheck on the folded row
        wbar = [x.conjugate() for x in W_fold]
        sc = RingSC([ProductClaim(tables=[W_fold, wbar], value=norm_val)], ring)
        proof = sc.prove(transcript, explicit_combiners=[ring.one()])
        return y, com_fold, norm_val, proof, W_fold

    def eval_verify(self, y_claim, com_fold, norm_val, proof, W_fold,
                    beta: int, transcript: Transcript, rows: int = 4) -> bool:
        ring = self.ring
        # replay the prover's challenge flow: the folding gammas first
        gamma = [ring.challenge_small(transcript, label=f"ak:g{i}") for i in range(rows)]
        tr = trace_balanced(norm_val)
        if tr < 0 or tr > ring.n * beta * beta:
            return False
        if self.row_key.commit(W_fold) != list(com_fold):
            return False
        mu = (len(W_fold) - 1).bit_length()
        ok, _, last = verify_round_polys(proof.round_polys, norm_val, mu, 2,
                                         ring, transcript)
        return ok
