"""Canonical proof serialization & size accounting (Wave 8).

Every protocol's proof object carries a ``n_ring_elts``/``n_bytes`` size
model; this module provides the canonical byte encoders used by the
benchmark harness:

* ring elements: ceil(q/8)-byte little-endian per coefficient;
* small-digit ring elements (Labrador/LF+ gadget digits): fixed signed
  byte or short encodings — the papers' compression;
* proof objects: length-prefixed canonical concatenation.
"""

from __future__ import annotations

from typing import Sequence

from .ring import Ring, RingElt


def ring_elt_bytes(elt: RingElt) -> bytes:
    return elt.to_bytes()


def ring_elt_small_bytes(elt: RingElt, digit_bits: int = 8) -> bytes:
    """Signed small-digit encoding (assumes centred coefficients fit)."""
    ring = elt.ring
    signed = digit_bits // 8 or 1
    out = bytearray()
    for c in elt.coeffs:
        v = ring.center(c, ring.q)
        out += v.to_bytes(signed, "little", signed=True)
    return bytes(out)


def ring_vector_bytes(vec: Sequence[RingElt], small: bool = False,
                      digit_bits: int = 8) -> bytes:
    out = b""
    for elt in vec:
        out += ring_elt_small_bytes(elt, digit_bits) if small else ring_elt_bytes(elt)
    return out


def proof_size_bytes(n_ring_elts: int, ring: Ring, small: bool = False,
                     digit_bits: int = 8) -> int:
    """Size model: ring elements x ring dimension x coefficient width."""
    if small:
        return n_ring_elts * ring.n * (digit_bits // 8 or 1)
    w = (ring.q.bit_length() + 7) // 8
    return n_ring_elts * ring.n * w


def length_prefixed(data: bytes) -> bytes:
    return len(data).to_bytes(8, "little") + data
