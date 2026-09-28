"""Multilinear extensions and the generic sumcheck engine.

The sumcheck engine is the single most reused component of the lab: SALSAA's
Π_sum/Π_batch/Π_norm/Π_bin, LatticeFold+'s norm-check sumcheck (RingSC),
Akita's fused sum-check, Twist&Shout's one-hot PIOPs and HyperWolf's per-round
dimension reduction are all instances of "prove a sum over the boolean
hypercube of a product of multilinear extensions".

Engine design
-------------
* A *table* ``T`` of length 2^mu (values in any ring supporting +, *, scalars)
  defines the multilinear extension ``f(x_1..x_mu) = sum_b eq(x, b) T[b]``.
* ``SumcheckProduct`` proves ``sum_{b in {0,1}^mu} prod_j f_j(b) = v`` for a
  list of tables ``[T_1, ..., T_J]`` with round polynomials of degree ``J``
  per variable.  ``SumcheckLinear`` is the J=1 fast path.
* The prover uses the classic linear-time *bind* recursion: after each round,
  every table is bound to the verifier's challenge, halving its length; the
  round polynomial is computed from a single pass over the current tables.
  Prover cost: O(2^mu * J) ring operations (+ one eq-table of size 2^mu).
* Rings: works over Z_q[X]/(X^n+1) (RingElt), GF(p), GF(2^k) — anything with
  ``+``, ``*``, additive inverses and int scalar multiplication.  Values must
  also support ``==``.
"""

from __future__ import annotations

from typing import Callable, List, Sequence


# --------------------------------------------------------------------------- #
#  Multilinear extension utilities
# --------------------------------------------------------------------------- #


def eq_table(point: Sequence[int], mu: int) -> List[int]:
    """eq(r, x) as a table over x in {0,1}^mu, MSB-first variable order:
    table index bit (mu-1-i) corresponds to point[i].  Process the point in
    REVERSE so the first variable occupies the most significant bit."""
    if len(point) != mu:
        raise ValueError("point length must equal mu")
    t = [1]
    for r_i in reversed(list(point)):
        t = [v * (1 - r_i) for v in t] + [v * r_i for v in t]
    return t


def eq_eval(a: Sequence[int], b: Sequence[int]) -> int:
    """eq(a, b) = prod_i (a_i b_i + (1-a_i)(1-b_i)) for bits b."""
    out = 1
    for x, y in zip(a, b):
        out *= (1 - x) * (1 - y) + x * y
    return out


def mle_eval(table: Sequence, point: Sequence[int]):
    """Evaluate the multilinear extension of ``table`` (length 2^mu,
    MSB-first variable order) at ``point`` (mu coordinates)."""
    cur = list(table)
    for r in point:
        half = len(cur) // 2
        nxt = []
        for i in range(half):
            nxt.append(cur[i] * (1 - r) + cur[half + i] * r)
        cur = nxt
    return cur[0]


def bind_table(table: Sequence, r):
    """Bind variable 1 (MSB) to challenge r; returns the halved table."""
    half = len(table) // 2
    return [table[i] * (1 - r) + table[half + i] * r for i in range(half)]


def tensor2_tables(tables: Sequence[Sequence]):
    """Cross two lists of tables via the tensor product (used by sumcheck
    composition / SALSAA's u-folded f~). Not a hot path."""
    out = []
    for A in tables[0]:
        for B in tables[1]:
            out.append(A * B)
    return out


def bits_of(index: int, mu: int) -> List[int]:
    """Index -> bit list, MSB first (variable x_1 is the high bit)."""
    return [(index >> (mu - 1 - i)) & 1 for i in range(mu)]


def index_of(bits: Sequence[int]) -> int:
    out = 0
    for b in bits:
        out = (out << 1) | (b & 1)
    return out


# --------------------------------------------------------------------------- #
#  Sumcheck over products of multilinear extensions
# --------------------------------------------------------------------------- #


class SumcheckProduct:
    """Prove  sum_{b in {0,1}^mu}  prod_j f_j(b)  =  v  where f_j = MLE(T_j).

    Round i's polynomial:  g_i(X) = sum_{b' in {0,1}^{mu-i}}
        prod_j  f_j(r_1..r_{i-1}, X, b').

    The prover maintains the tables bound to (r_1..r_{i-1}); each round
    message is computed in one pass with degree-J Horner over the running
    product.  Verifier checks g_i(0) + g_i(1) = g_{i-1}(r_{i-1}) (round 0:
    = v), the degree bound, and finally evaluates the bound tables at r_mu.
    """

    def __init__(self, tables: Sequence[Sequence], claim):
        self.tables = [list(t) for t in tables]
        self.mu = (len(self.tables[0]) - 1).bit_length() if self.tables[0] else 0
        if len(self.tables[0]) != 1 << self.mu:
            raise ValueError("tables must have power-of-two length")
        self.claim = claim
        self.degree = len(self.tables)

    # ------------------------------------------------------------------ prover
    def prove_round(self, challenge=None):
        """Compute the next round polynomial. If ``challenge`` is not None it
        is the verifier's challenge for the *previous* round: bind all tables
        to it FIRST, then compute this round's polynomial over the bound
        tables.  Round polynomials have degree J in the bound variable."""
        if challenge is not None:
            self.bind(challenge)
        tables = self.tables
        J = self.degree
        half = len(tables[0]) // 2
        acc = [0] * (J + 1)
        for idx in range(half):
            low = [T[idx] for T in tables]
            high = [T[idx + half] for T in tables]
            # p(X) = prod_j (low_j + (high_j - low_j) X)
            poly = [1]
            for lo, hi in zip(low, high):
                delta = hi - lo
                new = [0] * (len(poly) + 1)
                for d, c in enumerate(poly):
                    new[d] = new[d] + c * lo
                    new[d + 1] = new[d + 1] + c * delta
                poly = new
            for d, c in enumerate(poly):
                acc[d] = acc[d] + c
        self._last_round_poly = acc
        return acc

    def bind(self, r):
        self.tables = [bind_table(T, r) for T in self.tables]

    def final_eval(self):
        """After all rounds: each table has length 1 — the bound value."""
        return [T[0] for T in self.tables]

    # --------------------------------------------------------------- verifier
    @staticmethod
    def check_round(prev_eval, round_poly, degree):
        """Round polynomials are in COEFFICIENT form: g(X) = sum_d c_d X^d.
        Check deg(g) <= degree and g(0) + g(1) == prev_eval, where
        g(0) = c_0 and g(1) = sum_d c_d."""
        if len(round_poly) - 1 > degree:
            return False, None
        g0 = round_poly[0]
        g1 = 0
        for c in round_poly:
            g1 = g1 + c
        if g0 + g1 != prev_eval:
            return False, None
        return True, None

    @staticmethod
    def eval_poly(poly, r):
        acc = 0
        for c in reversed(poly):
            acc = acc * r + c
        return acc


def run_sumcheck_product(tables, claim, challenge_fn, degree=None) -> tuple[bool, list]:
    """Drive SumcheckProduct with challenges from ``challenge_fn``.

    challenge_fn(round_index, round_poly) -> r  (must be derived from a
    Fiat-Shamir transcript in non-interactive usage).

    Returns (accept, final_values) where final_values are the bound tables'
    terminal values (the final opening claims the caller must check).
    """
    sc = SumcheckProduct(tables, claim)
    degree = degree if degree is not None else sc.degree
    prev = claim
    poly = sc.prove_round(None)
    for i in range(sc.mu):
        ok, _ = SumcheckProduct.check_round(prev, poly, degree)
        if not ok:
            return False, None
        r = challenge_fn(i, poly)
        prev = SumcheckProduct.eval_poly(poly, r)
        if i < sc.mu - 1:
            poly = sc.prove_round(r)
        else:
            sc.bind(r)
    # final check: prod of terminal values == prev
    final = sc.final_eval()
    prod = final[0]
    for f in final[1:]:
        prod = prod * f
    return prod == prev, final


class SumcheckLinear:
    """J=1 specialization: prove sum_b f(b) = v for a single table.

    Round polynomial is affine: g_i(X) = f0 + (f1 - f0) X with
    f0 = sum over bound-then-0 assignments etc.  Kept for clarity and for
    protocols that need per-round access (Twist&Shout binds in custom order).
    """

    def __init__(self, table, claim):
        self.table = list(table)
        self.mu = (len(self.table) - 1).bit_length()
        self.claim = claim

    def prove_round(self, challenge):
        if challenge is not None:
            self.bind(challenge)
        half = len(self.table) // 2
        f0 = sum(self.table[:half])
        f1 = sum(self.table[half:])
        return [f0, f1 - f0]

    def bind(self, r):
        self.table = bind_table(self.table, r)


# --------------------------------------------------------------------------- #
#  Ring-valued sumcheck helper (u-folded claims as in SALSAA / LF+)
# --------------------------------------------------------------------------- #


class RingSumcheck:
    """Sumcheck where the *claimed value* is a ring element and tables hold
    ring elements.  This wraps SumcheckProduct with ring bookkeeping and is
    the type used by RingSC (core/ringsc.py)."""

    def __init__(self, tables: List[List], claim):
        self.engine = SumcheckProduct(tables, claim)

    def prove(self, challenge_fn):
        return run_sumcheck_product(
            [t for t in self.engine.tables], self.engine.claim, challenge_fn,
            degree=self.engine.degree,
        )
