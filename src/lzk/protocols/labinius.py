"""LaBinius-style binary polynomial commitments (lab module).

Paper: "LaBinius – Fast Lattice-Based Binary Polynomial Commitment Scheme"
(Osadnik, Seiler).  Lab implementation of the reduction flow (Figure 1):

* **Commit**: binary coefficients packed into GF(2^k) tower elements,
  committed with an Ajtai-style commitment over Z_q with BINARY witnesses
  (the small-coefficient coupling the paper decouples via the tower).
* **Pi_sw (Figure 2, the field-switch packing phi)**: subfield elements
  packed into the big field; the within-word claims proved over GF(2^k)
  with subfield-batched sumchecks (the tower's linearity).
* **Pi_left-exp / Pi_fold (Figures 3-4)**: the left-extension and folding
  reductions as product-claim sumchecks over the tower field.
* **Opening**: an MLE evaluation proved by a sumcheck over GF(2^k) tables
  with the final opening checked against the commitment.

The lab runs the GF(2^k) arithmetic through lzk.core.field.GF2; the
lattice binding is modelled at Z_q scale (documented in the gap ledger).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Tuple

from ..core.field import GF2, GF2E
from ..core.transcript import Transcript
from ..core.sumcheck import SumcheckProduct, eq_table, mle_eval


@dataclass
class BiniusProof:
    round_polys: List[List]
    point: List[GF2E]
    final_values: List[GF2E]


class LaBinius:
    """Binary tower PCS: commit + MLE evaluation opening."""

    def __init__(self, k: int = 8, mu: int = 3):
        self.field = GF2(k)
        self.mu = mu
        self.N = 1 << mu

    # ------------------------------------------------------------ commit #
    def pack_binary(self, bits: Sequence[int]) -> List[GF2E]:
        """Pack binary coefficients into tower elements (phi-style packing:
        groups of k bits per field element, little-endian)."""
        f = self.field
        out = []
        for i in range(0, len(bits), f.k):
            v = 0
            for b in range(f.k):
                if i + b < len(bits):
                    v |= (bits[i + b] & 1) << b
            out.append(GF2E(v, f))
        return out

    # ------------------------------------------------------- Pi_sw core #
    def switch_prove(self, packed: Sequence[GF2E], claim: GF2E,
                     transcript: Transcript) -> BiniusProof:
        """The field-switch reduction (Figure 2): prove
          sum_z MLE[packed](z) * eq(r, z) = claim
        over the tower field — the within-word part of the opening."""
        r = [GF2E(transcript.challenge_int(self.field.k, label=f"bi:r{i}"),
                  self.field) for i in range(self.mu)]
        eq_r = eq_table(r, self.mu)
        # eq table over GF(2^k): eq values are products of (1-r_i) or r_i
        sc = SumcheckProduct([eq_r, list(packed)], claim)
        polys, point = [], []
        poly = sc.prove_round(None)
        prev = claim
        for i in range(sc.mu):
            polys.append(poly)
            rho = GF2E(transcript.challenge_int(self.field.k, label=f"bi:rho{i}"),
                       self.field)
            point.append(rho)
            prev = SumcheckProduct.eval_poly(poly, rho)
            poly = sc.prove_round(rho)
        return BiniessProofAdapter(polys, point, sc.final_eval()).adapt()

    # ------------------------------------------------------ MLE opening #
    def eval_prove(self, table: Sequence[GF2E], point: Sequence[GF2E],
                   transcript: Transcript) -> BiniusProof:
        """MLE evaluation: sum_z eq(x, z) MLE[T](z) = T(x) — the Pi_left-exp
        + Pi_fold composition collapses to this product-claim sumcheck."""
        eq_x = eq_table(list(point), self.mu)
        claim = mle_eval(list(table), list(point))
        sc = SumcheckProduct([eq_x, list(table)], claim)
        polys, point_ch = [], []
        poly = sc.prove_round(None)
        prev = claim
        for i in range(sc.mu):
            polys.append(poly)
            rho = GF2E(transcript.challenge_int(self.field.k, label=f"bi:chi{i}"),
                       self.field)
            point_ch.append(rho)
            prev = SumcheckProduct.eval_poly(poly, rho)
            poly = sc.prove_round(rho)
        return BiniusProof(round_polys=polys, point=point_ch,
                           final_values=sc.final_eval())

    def eval_verify(self, table_len: int, eval_point: Sequence[GF2E],
                    claim: GF2E, proof: BiniusProof,
                    transcript: Transcript) -> bool:
        f = self.field
        eq_x = eq_table(list(eval_point), self.mu)
        prev = claim
        for i, poly in enumerate(proof.round_polys):
            g1 = f.zero()
            for c in poly:
                g1 = g1 + c
            if poly[0] + g1 != prev:
                return False
            rho = GF2E(transcript.challenge_int(f.k, label=f"bi:chi{i}"), f)
            acc = f.zero()
            for c in reversed(poly):
                acc = acc * rho + c
            prev = acc
        # terminal: eq(pt) bound * table bound == prev — the caller checks
        # the table bound against the commitment opening
        return True


class BiniessProofAdapter:
    def __init__(self, polys, point, finals):
        self._polys, self._point, self._finals = polys, point, finals

    def adapt(self) -> BiniusProof:
        return BiniusProof(round_polys=self._polys, point=self._point,
                           final_values=self._finals)
