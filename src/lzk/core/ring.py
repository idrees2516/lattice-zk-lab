"""Cyclotomic rings R_q = Z_q[X] / (X^n + 1) — the algebraic backbone of the lab.

Every lattice protocol in this repository (LatticeFold+, SALSAA, RoKoko, Cyclo,
PikkuFold, ProtogaLattice, Akita, Hachi, HyperWolf, Serval, ...) works over a
power-of-two cyclotomic ring R_q = Z_q[X]/(X^n + 1), typically with an NTT-friendly
prime modulus q.

Design notes
------------
* Coefficients are stored as Python ints in ``[0, q)`` — canonical representatives.
* Multiplication uses a *negacyclic NTT* when ``2n | q-1`` (Goldilocks default),
  otherwise an exact Kronecker-substitution bigint multiplication.  The negacyclic
  NTT is realised as: twist ``a_j -> a_j * psi^j`` followed by a cyclic NTT with
  the primitive n-th root ``omega = psi^2``; this evaluates ``a`` at the n points
  ``psi^{1}, psi^{3}, ..., psi^{2n-1}`` (odd powers of the primitive 2n-th root
  ``psi``), at which ``X^n = -1`` — hence a ring homomorphism R_q -> Z_q^n.
* The conjugation / coefficient-reversal involution ``X -> X^{-1}`` is used
  pervasively by the papers (Hermitian traces, squared norms).  We expose it as
  ``conjugate()`` / ``conj``.
* Norms: the papers always bound *integer* norms of short representatives, never
  mod-q norms.  ``l2_sq_int`` returns the exact integer sum of squared centred
  coefficients (each coefficient mapped to ``(-q/2, q/2]``).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Union

# --------------------------------------------------------------------------- #
#  Moduli
# --------------------------------------------------------------------------- #

#: Goldilocks prime 2^64 - 2^32 + 1: 2^32 | q-1 so the NTT works for any n <= 2^31;
#: 7 is a multiplicative generator.  Default modulus of the lab.
GOLDILOCKS = (1 << 64) - (1 << 32) + 1
GOLDILOCKS_GENERATOR = 7

#: Small NTT-friendly prime for tests: 12289 = 3 * 2^12 + 1, generator 31.
SMALL_Q = 12289
SMALL_Q_GENERATOR = 31


@dataclass
class RingParams:
    """Parameters of a cyclotomic ring R_q = Z_q[X]/(X^n+1)."""

    q: int
    n: int  # power of two

    def __post_init__(self):
        if self.n & (self.n - 1):
            raise ValueError("n must be a power of two")
        if self.q < 3:
            raise ValueError("q must be an odd prime >= 3")

    def ntt_order(self) -> int:
        """Largest power-of-two NTT size dividing q-1 (1 if none)."""
        order = 0
        m = self.q - 1
        while m % 2 == 0:
            order += 1
            m //= 2
        return 1 << order if order else 1

    def supports_ntt(self) -> bool:
        return self.ntt_order() >= 2 * self.n


class Ring:
    """R_q = Z_q[X]/(X^n+1) with negacyclic NTT / Kronecker multiplication."""

    def __init__(self, q: int = GOLDILOCKS, n: int = 64, generator: int | None = None):
        self.params = RingParams(q=q, n=n)
        self.q = q
        self.n = n
        if generator is None:
            generator = GOLDILOCKS_GENERATOR if q == GOLDILOCKS else SMALL_Q_GENERATOR
        self._generator = generator
        self._slot_bits = 2 * q.bit_length() + n.bit_length() + 8
        self._build_ntt_tables()

    # ------------------------------------------------------------------ NTT #
    def _build_ntt_tables(self):
        self._use_ntt = self.params.supports_ntt()
        if not self._use_ntt:
            self._w = self._inv_w = self._psi = self._inv_psi = None
            self._n_inv = None
            return
        order = self.params.ntt_order()
        g = pow(self._generator, (self.q - 1) // order, self.q)
        psi = pow(g, order // (2 * self.n), self.q)          # primitive 2n-th root
        omega = psi * psi % self.q                            # primitive n-th root
        self._psi = [pow(psi, i, self.q) for i in range(self.n)]
        self._inv_psi = [pow(x, self.q - 2, self.q) for x in self._psi]
        self._w = [pow(omega, i, self.q) for i in range(self.n)]
        self._inv_w = [pow(x, self.q - 2, self.q) for x in self._w]
        self._n_inv = pow(self.n, self.q - 2, self.q)

    @staticmethod
    def _bit_reverse(res: List[int]) -> None:
        n = len(res)
        j = 0
        for i in range(1, n):
            bit = n >> 1
            while j & bit:
                j ^= bit
                bit >>= 1
            j |= bit
            if i < j:
                res[i], res[j] = res[j], res[i]

    def _cyclic_ntt(self, a: Sequence[int], inv: bool = False) -> List[int]:
        """Iterative Cooley-Tukey: input natural order (bit-reversal applied
        internally), output natural order.  ``inv`` scales by n^{-1}."""
        q = self.q
        res = list(a)
        self._bit_reverse(res)
        roots = self._inv_w if inv else self._w
        length = 2
        while length <= self.n:
            half = length // 2
            tablestep = self.n // length
            for start in range(0, self.n, length):
                for i in range(half):
                    w = roots[i * tablestep]
                    j = start + i
                    k = j + half
                    u = res[j]
                    v = res[k] * w % q
                    res[j] = (u + v) % q
                    res[k] = (u - v) % q
            length <<= 1
        if inv:
            ninv = self._n_inv
            res = [x * ninv % q for x in res]
        return res

    def _negacyclic_ntt(self, a: Sequence[int]) -> List[int]:
        """a(X) |-> (a(psi^{2i+1}))_i  via twist + cyclic NTT."""
        q = self.q
        twisted = [x * w % q for x, w in zip(a, self._psi)]
        return self._cyclic_ntt(twisted)

    def _negacyclic_intt(self, v: Sequence[int]) -> List[int]:
        q = self.q
        t = self._cyclic_ntt(v, inv=True)
        return [x * w % q for x, w in zip(t, self._inv_psi)]

    # ----------------------------------------------------------- arithmetic #
    def reduce(self, a: Sequence[int]) -> List[int]:
        n = self.n
        out = [x % self.q for x in a]
        if len(out) < n:
            out = out + [0] * (n - len(out))
        elif len(out) > n:
            carry = out[:n]
            for i, c in enumerate(out[n:]):
                carry[i] = (carry[i] - c) % self.q
            out = carry
        return out

    def zero(self) -> "RingElt":
        return RingElt([0] * self.n, self)

    def one(self) -> "RingElt":
        e = [0] * self.n
        e[0] = 1
        return RingElt(e, self)

    def generator_elt(self) -> "RingElt":
        """The class of X (useful for tests and challenge ladders)."""
        e = [0] * self.n
        if self.n > 1:
            e[1] = 1
        else:
            e[0] = 1
        return RingElt(e, self)

    def random(self, rng, coeffs_range: int | None = None) -> "RingElt":
        """Uniform ring element (or bounded-coefficient random element)."""
        if coeffs_range is None:
            return RingElt([rng.randrange(self.q) for _ in range(self.n)], self)
        return RingElt(
            [rng.randrange(-coeffs_range, coeffs_range) % self.q for _ in range(self.n)],
            self,
        )

    def from_int(self, v: int) -> "RingElt":
        e = [0] * self.n
        e[0] = v % self.q
        return RingElt(e, self)

    def element(self, coeffs: Sequence[int]) -> "RingElt":
        return RingElt(self.reduce(coeffs), self)

    def challenge(self, transcript, label: str = "") -> "RingElt":
        """Sample a uniform ring element from a Fiat-Shamir transcript."""
        return RingElt(
            [transcript.challenge_int_mod(self.q, label=f"{label}:c{i}") for i in range(self.n)],
            self,
        )

    def challenge_small(self, transcript, label: str = "", bound: int = 2) -> "RingElt":
        """Sample a SHORT ring element (each centred coefficient in
        (-bound, bound]) from the transcript — the papers' small challenge
        set C (Labrador-style), controlling norm growth across folds."""
        coeffs = []
        for i in range(self.n):
            v = transcript.challenge_range(-bound, bound + 1, label=f"{label}:s{i}")
            coeffs.append(v % self.q)
        return RingElt(coeffs, self)

    # ------------------------------------------------------------- norms etc #
    @staticmethod
    def center(v: int, q: int) -> int:
        """Canonical representative in (-q/2, q/2]."""
        v %= q
        return v - q if v > q // 2 else v

    def l2_sq_int(self, a: Sequence[int]) -> int:
        """Exact integer squared l2 norm of the centred coefficient vector."""
        return sum((self.center(c, self.q)) ** 2 for c in a)

    def linf_int(self, a: Sequence[int]) -> int:
        return max(abs(self.center(c, self.q)) for c in a)

    # ------------------------------------------------------------ multiply #
    def mul_raw(self, a: Sequence[int], b: Sequence[int]) -> List[int]:
        if self._use_ntt:
            fa = self._negacyclic_ntt(list(a))
            fb = self._negacyclic_ntt(list(b))
            fc = [(x * y) % self.q for x, y in zip(fa, fb)]
            return self._negacyclic_intt(fc)
        return self._mul_kronecker(a, b)

    def _mul_kronecker(self, a: Sequence[int], b: Sequence[int]) -> List[int]:
        """Exact negacyclic convolution via one bigint multiplication."""
        n, q = self.n, self.q
        mask = (1 << self._slot_bits) - 1
        A = 0
        for i in reversed(range(n)):
            A = (A << self._slot_bits) | (a[i] % q)
        Bv = 0
        for i in reversed(range(n)):
            Bv = (Bv << self._slot_bits) | (b[i] % q)
        P = A * Bv
        p = [(P >> (self._slot_bits * k)) & mask for k in range(2 * n - 1)]
        p.append(0)
        out = [0] * n
        for k in range(n):
            out[k] = (p[k] - p[k + n]) % q
        return out

    def schoolbook_negacyclic(self, a: Sequence[int], b: Sequence[int]) -> List[int]:
        """O(n^2) reference convolution (used to validate the fast paths)."""
        n, q = self.n, self.q
        full = [0] * (2 * n)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    full[i + j] = (full[i + j] + x * y) % q
        out = [0] * n
        for k in range(n):
            out[k] = (full[k] - full[k + n]) % q
        return out


class RingElt:
    """Element of R_q = Z_q[X]/(X^n+1)."""

    __slots__ = ("coeffs", "ring")

    def __init__(self, coeffs: List[int], ring: Ring):
        self.coeffs: List[int] = coeffs
        self.ring: Ring = ring

    # ---- basic ops -------------------------------------------------------- #
    def _coerce(self, other) -> "RingElt":
        if isinstance(other, RingElt):
            return other
        if isinstance(other, int):
            return self.ring.from_int(other)
        return NotImplemented

    def __add__(self, other: "RingElt") -> "RingElt":
        other = self._coerce(other)
        if other is NotImplemented:
            return NotImplemented
        q = self.ring.q
        return RingElt([(x + y) % q for x, y in zip(self.coeffs, other.coeffs)], self.ring)

    def __sub__(self, other: "RingElt") -> "RingElt":
        other = self._coerce(other)
        if other is NotImplemented:
            return NotImplemented
        q = self.ring.q
        return RingElt([(x - y) % q for x, y in zip(self.coeffs, other.coeffs)], self.ring)

    def __neg__(self) -> "RingElt":
        q = self.ring.q
        return RingElt([(-x) % q for x in self.coeffs], self.ring)

    def __mul__(self, other: Union["RingElt", int]) -> "RingElt":
        if isinstance(other, int):
            return RingElt([(x * other) % self.ring.q for x in self.coeffs], self.ring)
        return RingElt(self.ring.mul_raw(self.coeffs, other.coeffs), self.ring)

    def __radd__(self, other):
        return self + other

    def __rsub__(self, other):
        coerced = self._coerce(other)
        if coerced is NotImplemented:
            return NotImplemented
        q = self.ring.q
        return RingElt([(x - y) % q for x, y in zip(coerced.coeffs, self.coeffs)], self.ring)

    def __rmul__(self, other: int) -> "RingElt":
        return self * other

    def __eq__(self, other) -> bool:
        return (
            isinstance(other, RingElt)
            and self.coeffs == other.coeffs
            and self.ring.q == other.ring.q
            and self.ring.n == other.ring.n
        )

    def __hash__(self):
        return hash((tuple(self.coeffs), self.ring.q, self.ring.n))

    # ---- ring structure ---------------------------------------------------- #
    def conjugate(self) -> "RingElt":
        """Ring involution X -> X^{-1} (the lattice-crypto 'adjoint' a†).
        Since X * X^{n-1} = X^n = -1, we have X^{-1} = -X^{n-1}, so
        conj(a) = a_0 - sum_{i>=1} a_{n-i} X^i.  This is the involution that
        makes the Hermitian trace identity Tr(conj(a) * b) = n * <a, b>_coeff
        hold (verified in tests) — used by every norm-check in the papers."""
        n = self.ring.n
        q = self.ring.q
        c = self.coeffs
        out = [c[0]] + [(-c[n - i]) % q for i in range(1, n)]
        return RingElt(out, self.ring)

    conj = conjugate

    def trace(self) -> int:
        """Cyclotomic trace mod q.  For power-of-two cyclotomics the power basis
        is orthogonal under the Hermitian trace form, so Tr(a) = n * a_0 mod q."""
        return (self.ring.n * self.coeffs[0]) % self.ring.q

    def trace_int(self) -> int:
        """Balanced integer trace Tr(a) = n * a_0 with a_0 centred in
        (-q/2, q/2].  This is the wraparound-free integer the papers' norm
        checks compare against bounds (SALSAA's balanced-trace check)."""
        return self.ring.n * Ring.center(self.coeffs[0], self.ring.q)

    def l2_sq_int(self) -> int:
        return self.ring.l2_sq_int(self.coeffs)

    def linf_int(self) -> int:
        return self.ring.linf_int(self.coeffs)

    def scale(self, s: int) -> "RingElt":
        return self * s

    def is_zero(self) -> bool:
        return all(c == 0 for c in self.coeffs)

    def to_bytes(self) -> bytes:
        """Canonical serialization: ceil(q/8)-byte little-endian per coefficient."""
        w = (self.ring.q.bit_length() + 7) // 8
        return b"".join(c.to_bytes(w, "little") for c in self.coeffs)

    def n_bytes(self) -> int:
        w = (self.ring.q.bit_length() + 7) // 8
        return w * self.ring.n

    def __repr__(self):
        if self.ring.n <= 8:
            return f"RingElt({self.coeffs})"
        return f"RingElt(n={self.ring.n}, q~2^{self.ring.q.bit_length()}, first={self.coeffs[:4]})"


# --------------------------------------------------------------------------- #
#  Vector / matrix helpers over R_q  (module operations)
# --------------------------------------------------------------------------- #


def dot(av: Sequence[RingElt], bv: Sequence[RingElt]) -> RingElt:
    ring = av[0].ring
    acc = ring.zero()
    for a, b in zip(av, bv):
        acc = acc + a * b
    return acc


def lin_comb(coeffs: Sequence[int], vecs: Sequence[Sequence[RingElt]]) -> List[RingElt]:
    """Sum_i coeffs[i] * vecs[i] (each vec a list of ring elements)."""
    k = len(vecs[0])
    ring = vecs[0][0].ring
    out = [ring.zero() for _ in range(k)]
    for c, vec in zip(coeffs, vecs):
        if c:
            for j in range(k):
                out[j] = out[j] + vec[j] * c
    return out


def mat_vec(A: Sequence[Sequence[RingElt]], v: Sequence[RingElt]) -> List[RingElt]:
    """A: m x k matrix of ring elements (list of rows), v in R_q^k -> A v in R_q^m."""
    return [dot(row, v) for row in A]
