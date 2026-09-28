"""Ring Gröbner reduction over the staircase ideal I (lab item 7.4 / P0-4).

ProtogaLattice's verifier-side check compression relies on Proposition 1:
the ideal

    I = <Z_{i,j}(Y) = Y_i Y_j − Y_i : 0 <= j <= i <= k−1>  in M = R_q[Y]

has the REDUCED GRÖBNER BASIS G = {Z_{i,j}} whose reduction rules are:

    Y_i^a        -> Y_i          (idempotence, via Z_{i,i})
    Y_i Y_j      -> Y_max(i,j)   (absorption,  via Z_{i,j}, j <= i)

so every monomial collapses to the single variable of highest index in its
support (or 1), and the normal form of any P is AFFINE LINEAR:
c_0 + sum_i c_i Y_i.  The division algorithm extracts the unique quotients
(K_{rs}) with

    P = sum_{r <= s} K_{rs} . Z_{rs} + R,   deg(K_{rs}) <= deg(P) − 2,

which PGL-Fold/PGL-Boot send to the verifier (degree-checked, evaluated at
the folding challenges to update the error accumulator e*).

This module implements polynomials over Z_q (coefficients as Python ints)
in k+1 variables with:
* monomial-dict representation and arithmetic;
* the explicit Gröbner basis G;
* `divide()` — the deterministic division computing (K_{rs}) and R with the
  degree bound (Pauer's Gröbner bases over rings, D.1);
* verification helpers (evaluate at a point, degree checks).
"""

from __future__ import annotations

from typing import Dict, List, Sequence, Tuple

Mono = Tuple[int, ...]  # exponent vector (k+1 entries: Y_0 .. Y_k)


def mono_mul(a: Mono, b: Mono) -> Mono:
    return tuple(x + y for x, y in zip(a, b))


def mono_deg(a: Mono) -> int:
    return sum(a)


def mono_ldiv(a: Mono, b: Mono) -> Mono | None:
    """a / b if b divides a (exact exponent-wise)."""
    out = []
    for x, y in zip(a, b):
        if x < y:
            return None
        out.append(x - y)
    return tuple(out)


class MPoly:
    """Multivariate polynomial over Z_q in variables Y_0..Y_{k}."""

    __slots__ = ("terms", "q", "nvars")

    def __init__(self, terms: Dict[Mono, int], q: int, nvars: int):
        self.terms = {m: c % q for m, c in terms.items() if c % q != 0}
        self.q = q
        self.nvars = nvars

    # ---- constructors ------------------------------------------------------ #
    @classmethod
    def const(cls, c: int, q: int, nvars: int) -> "MPoly":
        return cls({(0,) * nvars: c % q}, q, nvars)

    @classmethod
    def var(cls, i: int, q: int, nvars: int) -> "MPoly":
        m = [0] * nvars
        m[i] = 1
        return cls({tuple(m): 1}, q, nvars)

    @classmethod
    def linear_comb(cls, coeffs: Sequence, q: int, nvars: int) -> "MPoly":
        """c_0 + c_1 Y_0 + ... + c_{nvars-1} Y_{nvars-1} from a coefficient
        list (the normal-form shape)."""
        terms = {}
        if coeffs[0] % q:
            terms[(0,) * nvars] = coeffs[0] % q
        for i in range(1, nvars):
            if coeffs[i] % q:
                m = [0] * nvars
                m[i - 1] = 1
                terms[tuple(m)] = coeffs[i] % q
        return cls(terms, q, nvars)

    # ---- arithmetic -------------------------------------------------------- #
    def __add__(self, other: "MPoly") -> "MPoly":
        out = dict(self.terms)
        for m, c in other.terms.items():
            out[m] = (out.get(m, 0) + c) % self.q
        return MPoly(out, self.q, self.nvars)

    def __sub__(self, other: "MPoly") -> "MPoly":
        out = dict(self.terms)
        for m, c in other.terms.items():
            out[m] = (out.get(m, 0) - c) % self.q
        return MPoly(out, self.q, self.nvars)

    def __mul__(self, other: "MPoly" | int) -> "MPoly":
        if isinstance(other, int):
            return MPoly({m: c * other for m, c in self.terms.items()}, self.q, self.nvars)
        out: Dict[Mono, int] = {}
        for ma, ca in self.terms.items():
            for mb, cb in other.terms.items():
                m = mono_mul(ma, mb)
                out[m] = (out.get(m, 0) + ca * cb) % self.q
        return MPoly(out, self.q, self.nvars)

    def __neg__(self) -> "MPoly":
        return MPoly({m: -c for m, c in self.terms.items()}, self.q, self.nvars)

    def __eq__(self, other) -> bool:
        return isinstance(other, MPoly) and self.terms == other.terms and self.q == other.q

    # ---- queries ----------------------------------------------------------- #
    def degree(self) -> int:
        return max((mono_deg(m) for m in self.terms), default=0)

    def is_zero(self) -> bool:
        return not self.terms

    def eval(self, point: Sequence[int]) -> int:
        """Evaluate at a point in Z_q^{nvars}."""
        total = 0
        for m, c in self.terms.items():
            term = c
            for i, e in enumerate(m):
                if e:
                    term = term * pow(point[i] % self.q, e, self.q)
            total = (total + term) % self.q
        return total

    def coeffs_linear(self) -> List[int]:
        """Extract (c_0, c_{Y_0}, ..., c_{Y_{nvars-1}}) — valid when self is
        affine linear (the normal form shape)."""
        out = [0] * (self.nvars + 1)
        for m, c in self.terms.items():
            if sum(m) == 0:
                out[0] = c
            elif sum(m) == 1:
                out[1 + m.index(1)] = c
            else:
                raise ValueError(f"not affine linear: monomial {m}")
        return out


# --------------------------------------------------------------------------- #
#  The staircase Gröbner basis (Proposition 1)
# --------------------------------------------------------------------------- #


def z_poly(i: int, j: int, q: int, nvars: int) -> MPoly:
    """Z_{i,j}(Y) = Y_i Y_j − Y_i  (reduced over 0 <= j <= i <= nvars−2)."""
    mi = [0] * nvars
    mi[i] = 1
    mj = [0] * nvars
    mj[j] = 1
    prod = tuple(a + b for a, b in zip(mi, mj))
    terms = {prod: 1}
    mi_t = tuple(mi)
    terms[mi_t] = terms.get(mi_t, 0) - 1
    return MPoly({m: c for m, c in terms.items() if c % q}, q, nvars)


def groebner_basis(nvars: int, q: int) -> List[Tuple[int, int, MPoly]]:
    """G = {Z_{i,j} : 0 <= j <= i <= nvars−2} (the Y_k slot is the constant-1
    variable in the L-basis; the basis covers Y_0..Y_{k−1})."""
    out = []
    for i in range(nvars - 1):
        for j in range(i + 1):
            out.append((i, j, z_poly(i, j, q, nvars)))
    return out


# --------------------------------------------------------------------------- #
#  Division modulo G with quotient extraction (P0-4 core)
# --------------------------------------------------------------------------- #


def divide(P: MPoly) -> Tuple[Dict[Tuple[int, int], MPoly], MPoly]:
    """Deterministic division of P by the Gröbner basis G:
    returns (K, R) with P = sum_{i>=j} K_{ij} Z_{ij} + R, R affine linear,
    deg(K_{ij}) <= max(2, deg(P) − 2).

    Reduction rules applied greedily on each monomial:
      * idempotence: Y_i^a -> Y_i  with quotient Y_i^{a-2} Z_{i,i}  (a >= 2)
      * absorption:  Y_i Y_j -> Y_max(i,j) with quotient (rest) Z_{i,j}
    """
    q, nvars = P.q, P.nvars
    work: Dict[Mono, int] = dict(P.terms)
    quotients: Dict[Tuple[int, int], Dict[Mono, int]] = {}

    def add_quotient(i: int, j: int, mono: Mono, coeff: int):
        key = (i, j)
        d = quotients.setdefault(key, {})
        d[mono] = (d.get(mono, 0) + coeff) % q
        if d[mono] == 0:
            del d[mono]

    # process monomials of degree >= 2 until none remain
    changed = True
    while changed:
        changed = False
        for m in list(work.keys()):
            if mono_deg(m) < 2:
                continue
            c = work.pop(m)
            if c == 0:
                changed = True
                continue
            # find the two largest indices with positive exponents
            order = sorted(
                [i for i in range(nvars) if m[i] > 0], reverse=True
            )
            if len(order) >= 2 and m[order[0]] >= 1 and m[order[1]] >= 1:
                i, j = order[0], order[1]  # i > j
                # Y_i Y_j -> Y_i ; quotient: (m / (Y_i Y_j)) * Z_{i,j}
                rest = list(m)
                rest[i] -= 1
                rest[j] -= 1
                add_quotient(i, j, tuple(rest), c)
                # new term: same monomial with Y_j exponent reduced by 1
                new_m = list(m)
                new_m[j] -= 1
                nm = tuple(new_m)
                work[nm] = (work.get(nm, 0) + c) % q
                changed = True
            elif len(order) == 1:
                i = order[0]
                a = m[i]
                # Y_i^a -> Y_i^{a-1}; quotient: Y_i^{a-2} (rest) Z_{i,i}
                rest = list(m)
                rest[i] -= 2
                add_quotient(i, i, tuple(rest), c)
                new_m = list(m)
                new_m[i] -= 1
                nm = tuple(new_m)
                work[nm] = (work.get(nm, 0) + c) % q
                changed = True
            # loop continues until every monomial has degree <= 1
    K = {ij: MPoly(terms, q, nvars) for ij, terms in quotients.items() if terms}
    R = MPoly(work, q, nvars)
    return K, R


def verify_division(P: MPoly, K: Dict[Tuple[int, int], MPoly], R: MPoly) -> bool:
    """Check P == sum K_{ij} Z_{ij} + R (used in tests + verifier audits)."""
    q, nvars = P.q, P.nvars
    acc = R
    for (i, j), Kij in K.items():
        acc = acc + Kij * z_poly(i, j, q, nvars)
    return acc == P


def quotient_degree_bound_ok(
    K: Dict[Tuple[int, int], MPoly], bound: int
) -> bool:
    """The verifier's degree check: deg(K_{rs}) <= d − 2."""
    return all(Kij.degree() <= bound for Kij in K.values())


# --------------------------------------------------------------------------- #
#  The L-basis (Lemma 4 closed form) and Z-evaluation helpers
# --------------------------------------------------------------------------- #


def l_basis(j: int, k: int, q: int) -> MPoly:
    """The L-basis over variables Y_0..Y_{k-1} (Y_k := 1 fixed by Lemma 4):
      L_0 = Y_0;   L_j = Y_j − Y_{j−1} (1 <= j <= k−1);   L_k = 1 − Y_{k−1}.
    Telescoping identity: sum_{j=0}^{k} L_j = 1."""
    nvars = k
    if j == 0:
        return MPoly.var(0, q, nvars)
    if j == k:
        return MPoly.const(1, q, nvars) - MPoly.var(k - 1, q, nvars)
    return MPoly.var(j, q, nvars) - MPoly.var(j - 1, q, nvars)


def l_eval(j: int, k: int, y: Sequence[int], q: int) -> int:
    """L_j evaluated at the challenge tuple y (y has k entries; y_k := 1)."""
    if j == 0:
        return y[0] % q
    if j == k:
        return (1 - y[k - 1]) % q
    return (y[j] - y[j - 1]) % q


def z_eval(i: int, j: int, y: Sequence[int], q: int) -> int:
    """Z_{i,j}(y) = y_i y_j − y_i."""
    return (y[i] * y[j] - y[i]) % q
