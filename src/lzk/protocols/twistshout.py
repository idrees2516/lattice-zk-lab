"""Twist & Shout memory-checking PIOPs (lab module).

Paper: "Twist and Shout: Faster memory checking arguments via one-hot
addressing and increments" (Setty, Thaler).  Lab implementation of the core
PIOP layer — the sumcheck identities over Z_q with eq-anchored product
claims (the paper's paradigm: no grand products / grand sums):

* **One-hot encoding check** (Figs. 6/8): Booleanity + Hamming-weight-one:
    sum_x MLE[A](x)^2 = 1     (degree-2 sumcheck)
  (in binary fields the Hamming check becomes sum MLE[A](x) = 1 — the
  paper's no-2^{-1} remark; the lab works over Z_q so both forms run).
* **Shout core PIOP** (Fig. 5, d=1) — read-only memory / lookup:
    sum_z eq(r, z) * MLE[W](z) * MLE[A](z) = v
  a degree-3 product claim.
* **Twist core PIOP** (Fig. 9) — read/write memory via the increment trick:
  the read value at time t is the last-written value at the one-hot address;
  the lab proves the per-step claims in ONE batched degree-2 sumcheck.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence

from ..core.ring import Ring
from ..core.transcript import Transcript
from ..core.sumcheck import run_sumcheck_product, eq_table, mle_eval


@dataclass
class LookupProof:
    round_polys: List[List]      # degree-3 coefficient-form messages
    point: List[int]             # verifier challenges
    final_values: List[int]      # bound W and A at the point


class Shout:
    """Read-only memory (lookup argument) PIOP."""

    def __init__(self, q: int, m: int):
        self.q = q
        self.m = m
        self.mu = (m - 1).bit_length()

    def _challenges(self, transcript: Transcript, rounds: int) -> List[int]:
        return [transcript.challenge_int_mod(self.q, label=f"sh:rho{i}")
                for i in range(rounds)]

    def onehot_check(self, a: Sequence[int], transcript: Transcript) -> bool:
        """sum_x MLE[A](x)^2 = 1 (Booleanity + weight one combined)."""
        claim = sum(x * x for x in a) % self.q
        if claim != 1:
            return False  # not one-hot — rejected before proving
        ok, _ = run_sumcheck_product(
            [list(a), list(a)], 1,
            lambda i, poly: transcript.challenge_int_mod(self.q, label=f"sh:b{i}"),
        )
        return ok

    def lookup_prove(self, W: Sequence[int], a: Sequence[int], v: int,
                     transcript: Transcript) -> LookupProof:
        """sum_z MLE[W](z) MLE[A](z) = v — the d=1 core PIOP: for one-hot a
        the sum is exactly the looked-up value W[z0]; the eq(r,.) anchor of
        the full protocol enters at the PCS-composition layer (caller)."""
        claim = sum(W[z] * a[z] for z in range(self.m)) % self.q
        assert claim == v % self.q, "lookup claim mismatch"
        polys = []
        point: List[int] = []
        tables = [list(W), list(a)]
        from ..core.sumcheck import SumcheckProduct
        sc = SumcheckProduct(tables, claim)
        poly = sc.prove_round(None)
        prev = claim
        for i in range(sc.mu):
            polys.append(poly)
            rho = transcript.challenge_int_mod(self.q, label=f"sh:rho{i}")
            point.append(rho)
            prev = SumcheckProduct.eval_poly(poly, rho)
            poly = sc.prove_round(rho)
        finals = sc.final_eval()
        return LookupProof(round_polys=polys, point=point, final_values=finals)

    def lookup_verify(self, W: Sequence[int], a: Sequence[int], v: int,
                      proof: LookupProof, transcript: Transcript) -> bool:
        # round checks (coefficient form: g(0)+g(1) = prev)
        prev = v % self.q
        for i, poly in enumerate(proof.round_polys):
            if len(poly) - 1 > 3:
                return False
            g1 = 0
            for c in poly:
                g1 = (g1 + c) % self.q
            if (poly[0] + g1) % self.q != prev:
                return False
            rho = transcript.challenge_int_mod(self.q, label=f"sh:rho{i}")
            prev = 0
            for c in reversed(poly):
                prev = (prev * rho + c) % self.q
        # terminal: W(pt) * A(pt) == prev (the two bound values)
        total = (proof.final_values[0] * proof.final_values[1]) % self.q
        return total == prev


@dataclass
class TwistState:
    addrs: List[List[int]]     # T one-hot address rows
    read_vals: List[int]       # the value read at each step


class Twist:
    """Read/write memory checking (increment trick, read-check PIOP)."""

    def __init__(self, q: int, m: int, T: int):
        self.q = q
        self.m = m
        self.T = T
        self.mu = (m - 1).bit_length()

    def read_check_prove(self, state: TwistState, W: Sequence[int],
                         transcript: Transcript):
        """Batched read-checking (Fig. 9 core): for each time step t the
        read value equals <a_t, W>; the lab batches the T claims with
        transcript combiners into one degree-2 sumcheck over the address
        hypercube."""
        from ..core.sumcheck import SumcheckProduct
        groups_tables = []
        combiners = []
        claim = 0
        for t in range(self.T):
            a_t = state.addrs[t]
            c_t = sum(a_t[z] * W[z] for z in range(self.m)) % self.q
            assert c_t == state.read_vals[t] % self.q, "read claim mismatch"
            alpha = transcript.challenge_int_mod(self.q, label=f"tw:a{t}")
            combiners.append(alpha)
            claim = (claim + alpha * c_t) % self.q
            groups_tables.append((list(a_t), list(W)))
        # combined table: sum_t alpha_t * a_t (linear combination)
        comb_table = [
            sum(al * a[z] for al, a in zip(combiners, state.addrs)) % self.q
            for z in range(self.m)
        ]
        sc = SumcheckProduct([comb_table, list(W)], claim)
        polys = []
        point = []
        poly = sc.prove_round(None)
        prev = claim
        for i in range(sc.mu):
            polys.append(poly)
            rho = transcript.challenge_int_mod(self.q, label=f"tw:rho{i}")
            point.append(rho)
            prev = SumcheckProduct.eval_poly(poly, rho)
            poly = sc.prove_round(rho)
        return polys, point, sc.final_eval()

    def read_check_verify(self, state: TwistState, W: Sequence[int], proof,
                          transcript: Transcript) -> bool:
        polys, point, finals = proof
        combiners = [transcript.challenge_int_mod(self.q, label=f"tw:a{t}")
                     for t in range(self.T)]
        claim = 0
        for t in range(self.T):
            c_t = sum(state.addrs[t][z] * W[z] for z in range(self.m)) % self.q
            claim = (claim + combiners[t] * c_t) % self.q
        prev = claim
        for i, poly in enumerate(polys):
            g1 = 0
            for c in poly:
                g1 = (g1 + c) % self.q
            if (poly[0] + g1) % self.q != prev:
                return False
            rho = transcript.challenge_int_mod(self.q, label=f"tw:rho{i}")
            prev = 0
            for c in reversed(poly):
                prev = (prev * rho + c) % self.q
        # terminal: (sum_t alpha_t a_t)(pt) * W(pt) == prev
        comb_at = sum(
            combiners[t] * mle_eval(state.addrs[t], point) for t in range(self.T)
        ) % self.q
        total = (comb_at * finals[1]) % self.q
        return total == prev
