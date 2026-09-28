"""Fiat-Shamir transcripts with domain separation (Wave 8 production item).

Every protocol in the lab derives its challenges from a ``Transcript`` — a
SHA3-256 (keccak) based duplex sponge with:

* explicit **domain separation**: each protocol instance initializes the
  sponge with a unique ASCII label (e.g. ``b"lzk/hyperwolf/v1/commit"``),
  so challenges from different sub-protocols never collide;
* canonical absorption of every public input (bytes, ints, ring elements,
  field elements, commitments);
* deterministic challenge derivation: ``challenge_int(bits)``,
  ``challenge_int_mod(q)``, ``challenge_field(p)``, ``challenge_bytes(n)``;
* a ``challenge_counter`` for reproducibility audits and proof replay.

The transcript makes the lab's interactive protocols non-interactive
(Schnorr-style Fiat-Shamir) without changing their soundness structure: the
verifier re-derives every challenge from the same absorb/squeeze sequence.
"""

from __future__ import annotations

import hashlib
import struct
from typing import Sequence


class Transcript:
    """Keccak-based duplex sponge with domain separation."""

    def __init__(self, domain_label: bytes | str):
        if isinstance(domain_label, str):
            domain_label = domain_label.encode("ascii")
        self._label = domain_label
        self._state = hashlib.sha3_256()
        self._state.update(b"lzk-transcript/v1")
        self._state.update(struct.pack(">H", len(domain_label)))
        self._state.update(domain_label)
        self.challenge_counter = 0
        self._squeeze_buffer = b""

    # ---------------------------------------------------------------- absorb #
    def absorb_bytes(self, data: bytes, label: bytes | str = b"") -> "Transcript":
        if isinstance(label, str):
            label = label.encode("ascii")
        h = hashlib.sha3_256()
        h.update(self._state.digest())
        h.update(b"absorb")
        h.update(struct.pack(">H", len(label)))
        h.update(label)
        h.update(struct.pack(">Q", len(data)))
        h.update(data)
        self._state = h
        return self

    def absorb_int(self, v: int, label: bytes | str = b"") -> "Transcript":
        if v < 0:
            v = -v - 1
            sign = 1
        else:
            sign = 0
        payload = struct.pack(">BQ", sign, v)
        return self.absorb_bytes(payload, label or b"int")

    def absorb_ring(self, elt, label: bytes | str = b"") -> "Transcript":
        return self.absorb_bytes(elt.to_bytes(), label or b"ring")

    def absorb_ring_vector(self, vec: Sequence, label: bytes | str = b"") -> "Transcript":
        for i, elt in enumerate(vec):
            self.absorb_ring(elt, label=f"{label}:rv{i}" if label else f"rv{i}")
        return self

    def absorb_point(self, point: Sequence, label: bytes | str = b"") -> "Transcript":
        """Absorb a challenge point (list of ints or ring elements)."""
        for i, c in enumerate(point):
            if isinstance(c, int):
                self.absorb_int(c, label=f"{label}:pt{i}" if label else f"pt{i}")
            else:
                self.absorb_ring(c, label=f"{label}:pt{i}" if label else f"pt{i}")
        return self

    # --------------------------------------------------------------- squeeze #
    def _refill(self, n: int) -> bytes:
        h = hashlib.sha3_256()
        h.update(self._state.digest())
        h.update(b"squeeze")
        h.update(struct.pack(">Q", self.challenge_counter))
        self.challenge_counter += 1
        block = h.digest()
        while len(block) < n:
            h2 = hashlib.sha3_256()
            h2.update(block)
            h2.update(struct.pack(">Q", self.challenge_counter))
            self.challenge_counter += 1
            block += h2.digest()
        return block[:n]

    def challenge_bytes(self, n: int, label: bytes | str = b"") -> bytes:
        data = self._refill(n)
        # absorb what was squeezed to make future challenges depend on it
        self.absorb_bytes(data, label or b"chal")
        return data

    def challenge_int(self, bits: int, label: bytes | str = b"") -> int:
        nbytes = (bits + 7) // 8
        data = self.challenge_bytes(nbytes, label or b"int")
        val = int.from_bytes(data, "little")
        return val & ((1 << bits) - 1)

    def challenge_int_mod(self, q: int, label: bytes | str = b"") -> int:
        """Challenge in [0, q) via rejection sampling: sample ceil(log2 q)
        bits, retry while >= q (expected <= 2 draws).  Residual bias is
        (2^bits - q)/2^bits < 1/2 — documented, negligible for the lab."""
        bits = q.bit_length()
        while True:
            val = self.challenge_int(bits, label or b"modq")
            if val < q:
                return val

    def challenge_field(self, p: int, label: bytes | str = b"") -> int:
        return self.challenge_int_mod(p, label or b"field")

    def challenge_range(self, lo: int, hi: int, label: bytes | str = b"") -> int:
        return lo + self.challenge_int_mod(hi - lo, label or b"range")

    def digest(self) -> bytes:
        """Current transcript digest (use as protocol message hash / proof id)."""
        return self._state.digest()

    # ----------------------------------------------------------------- misc #
    def fork(self, label: bytes | str) -> "Transcript":
        """A child transcript bound to the current digest — used to derive
        independent sub-protocol challenge streams."""
        child = Transcript(label)
        child.absorb_bytes(self._state.digest(), b"parent")
        return child
