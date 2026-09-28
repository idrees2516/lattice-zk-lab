"""Ajtai / Module-SIS commitments and gadget decompositions.

The commitment used across LatticeFold+, SALSAA, RoKoko, Cyclo, PikkuFold,
ProtogaLattice, Akita, Hachi, HyperWolf, Serval is the Ajtai hash:

    Com_A(w) = A . w  mod q,      A in R_q^{m x k},  w in R_q^k

* **Binding** holds under Module-SIS when w is short ( l_infty <= beta );
  finding w != w' with A w = A w' and ||w - w'|| small breaks M-SIS.
* The lab uses *deterministic* commitments (no randomness): hiding is out of
  scope for the reference implementations (the papers add masks for ZK; we
  note this in each protocol's gap ledger).
* Structured A: each row is sampled seeded from a transcript/seed so the
  verifier can re-derive A in O(1) space (transparent setup, Wave 8 item).
* Gadget decomposition G^{-1}: decompose ring coefficients into base-b digits
  for range proofs (LatticeFold+/Cyclo/Neo pay-per-bit, SALSAA's b-decomp).
  G . G^{-1}(w) = w  with G = [1, b, b^2, ..., b^{d-1}] (per coefficient).
"""

from __future__ import annotations

import hashlib
import struct
from typing import List, Sequence

from .ring import Ring, RingElt

# --------------------------------------------------------------------------- #
#  Seeded structured matrix sampling (transparent setup)
# --------------------------------------------------------------------------- #


class AjtaiParams:
    """Parameters of an Ajtai commitment key A in R_q^{m x k}."""

    def __init__(self, ring: Ring, m: int, k: int, seed: bytes = b"lzk-default-seed"):
        self.ring = ring
        self.m = m
        self.k = k
        self.seed = seed
        self._A: List[List[RingElt]] | None = None

    def matrix(self) -> List[List[RingElt]]:
        """Deterministically expand A from the seed (each row derived from
        SHA3(seed, row_index, slot_index)).  Cached after first expansion."""
        if self._A is None:
            rng = _SeededRandom(self.seed)
            ring = self.ring
            q = ring.q
            self._A = [
                [RingElt([rng.randrange_mod(q) for _ in range(ring.n)], ring) for _ in range(self.k)]
                for _ in range(self.m)
            ]
        return self._A

    def commit(self, w: Sequence[RingElt]) -> List[RingElt]:
        """C = A . w mod q in R_q^m."""
        A = self.matrix()
        out = []
        for row in A:
            acc = self.ring.zero()
            for a_ij, w_j in zip(row, w):
                acc = acc + a_ij * w_j
            out.append(acc)
        return out

    def check(self, C: Sequence[RingElt], w: Sequence[RingElt]) -> bool:
        return self.commit(w) == list(C)

    def bytes_size(self) -> int:
        """Serialized commitment size in bytes."""
        return self.m * self.ring.n * ((self.ring.q.bit_length() + 7) // 8)


class _SeededRandom:
    """Deterministic PRNG from a seed (SHA3 CTR mode)."""

    def __init__(self, seed: bytes):
        self.seed = seed
        self._counter = 0
        self._buf = b""
        self._pos = 0

    def _refill(self):
        h = hashlib.sha3_256()
        h.update(self.seed)
        h.update(struct.pack(">Q", self._counter))
        self._counter += 1
        self._buf = h.digest()
        self._pos = 0

    def next_bytes(self, n: int) -> bytes:
        out = b""
        while len(out) < n:
            if self._pos >= len(self._buf):
                self._refill()
            take = min(n - len(out), len(self._buf) - self._pos)
            out += self._buf[self._pos : self._pos + take]
            self._pos += take
        return out

    def randrange_mod(self, q: int) -> int:
        nbytes = (q.bit_length() + 7) // 8
        while True:
            data = self.next_bytes(nbytes)
            val = int.from_bytes(data, "little")
            if val < q:
                return val

    def randrange(self, lo: int, hi: int) -> int:
        return lo + self.randrange_mod(hi - lo)


# --------------------------------------------------------------------------- #
#  Gadget decomposition
# --------------------------------------------------------------------------- #


class Gadget:
    """Base-b gadget decomposition over R_q.

    G^{-1}(a) for a ring element with coefficients in [0, q) (or centred)
    returns the digit vector: each coefficient c is written in base b with
    ``digits`` digits (c = sum_d digit_d b^d), so that
    ``G . G^{-1}(a) = a`` with G = [1, b, ..., b^{d-1}] per coefficient.
    If every digit lies in [0, b) this certifies |c| < b^d — the range-proof
    primitive used by LatticeFold+/Cyclo/Neo (pay-per-bit) and SALSAA.
    """

    def __init__(self, ring: Ring, base: int, digits: int):
        self.ring = ring
        self.base = base
        self.digits = digits
        if base ** digits < ring.q:
            # still allowed; decomposition only covers values < base^digits
            pass

    def decompose_elt(self, a: RingElt) -> List[RingElt]:
        """G^{-1}(a): d ring elements, digit layer j holds the j-th base-b
        digits of all n coefficients (a *column* layout matching the papers'
        digit-decomposition of the witness)."""
        ring = self.ring
        b, d = self.base, self.digits
        layers = [ring.zero() for _ in range(d)]
        for i, c in enumerate(a.coeffs):
            c = c % ring.q
            for j in range(d):
                layers[j].coeffs[i] = (c % b)
                c //= b
        return layers

    def recompose_elt(self, layers: Sequence[RingElt]) -> RingElt:
        ring = self.ring
        b, d = self.base, self.digits
        out = ring.zero()
        for j, layer in enumerate(layers[:d]):
            out = out + layer * (b**j)
        return out

    def decompose_vector(self, w: Sequence[RingElt]) -> List[List[RingElt]]:
        """G^{-1} applied to each entry: returns a (k*d) flat vector."""
        out: List[List[RingElt]] = []
        for a in w:
            out.append(self.decompose_elt(a))
        return out

    def decompose_vector_flat(self, w: Sequence[RingElt]) -> List[RingElt]:
        flat: List[RingElt] = []
        for a in w:
            flat.extend(self.decompose_elt(a))
        return flat

    def recompose_vector(self, flat: Sequence[RingElt], k: int) -> List[RingElt]:
        out = []
        d = self.digits
        for i in range(k):
            out.append(self.recompose_elt(flat[i * d : (i + 1) * d]))
        return out

    def digit_bound_linf(self) -> int:
        return self.base - 1

    def covers(self) -> int:
        """Largest absolute value certifiable by the decomposition."""
        return self.base**self.digits


def decompose_int(v: int, base: int, digits: int) -> List[int]:
    """Little-endian base-b digits of a non-negative integer."""
    out = []
    v = abs(v)
    for _ in range(digits):
        out.append(v % base)
        v //= base
    return out
