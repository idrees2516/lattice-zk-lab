"""GF(2^k) extension fields (tower construction) for binary-field protocols.

LaBinius and Twist&Shout work over binary tower fields GF(2) ⊂ GF(2^2) ⊂ ...
⊂ GF(2^{2^t}).  We implement generic GF(2^k) arithmetic with carry-less
multiplication over Python big ints and reduction modulo an irreducible
polynomial.  The default irreducibles form a *tower*: each GF(2^{2m}) is built
as GF((2^m))[X]/(X^2 + X + beta_m) with beta_m the class of X in the level
below that is not a square... To stay simple and correct we use the classic
irreducible polynomials for each width and provide explicit ``embed`` maps for
the subfield structure the papers need (LaBinius's field-switch packing phi).

Irreducibles (low-bit = coefficient of X^0):
  k=1   : 1
  k=2   : x^2 + x + 1                -> 0b111
  k=4   : x^4 + x + 1                -> 0b10011
  k=8   : x^8 + x^4 + x^3 + x + 1    -> AES polynomial
  k=16  : x^16 + x^5 + x^3 + x + 1   -> 0x1002B (GHASH-related, irreducible)
  k=32  : x^32 + x^7 + x^3 + x^2 + 1
  k=64  : x^64 + x^4 + x^3 + x + 1
  k=128 : x^128 + x^7 + x^2 + x + 1  -> GCM polynomial

Subfield embedding: for the 2^t tower we embed GF(2^m) into GF(2^{2m}) by
``x |-> x^2 + x`` style maps... we instead simply *interleave* coordinates:
an element of GF(2^{2m}) is a + b*T with a, b in GF(2^m) where T satisfies
T^2 = T + beta.  Our ``subfield_embed``/``subfield_decompose`` implement the
paper-style packing used by LaBinius's phi switch (packing 2^s small-field
elements into one big-field element) as explicit bit-block copies, which is
the linear "change of basis" the papers actually rely on (the switch is an
F_2-linear map, not a subfield homomorphism).
"""

from __future__ import annotations

IRREDUCIBLES: dict[int, int] = {
    1: 0b1,
    2: 0b111,
    4: 0b10011,            # x^4 + x + 1
    8: 0b100011101,        # x^8 + x^4 + x^3 + x + 1  (AES)
    16: 0x1002B,           # x^16 + x^5 + x^3 + x + 1
    32: 0x100000087,       # x^32 + x^7 + x^3 + x^2 + 1
    64: (1 << 64) | 0x1B,  # x^64 + x^4 + x^3 + x + 1
    128: (1 << 128) | 0x87,  # x^128 + x^7 + x^2 + x + 1 (GCM)
}


def _clmul(a: int, b: int) -> int:
    """Carry-less multiplication of two polynomials over GF(2)."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def _reduce_mod(poly: int, mod: int, k: int) -> int:
    """Reduce ``poly`` modulo the irreducible ``mod`` of degree k."""
    mod_len = mod.bit_length() - 1  # == k
    while poly.bit_length() - 1 >= mod_len and poly:
        shift = poly.bit_length() - 1 - mod_len
        poly ^= mod << shift
    return poly


class GF2:
    """GF(2^k) field; elements are Python ints (bit i = coefficient of X^i)."""

    def __init__(self, k: int):
        if k not in IRREDUCIBLES:
            raise ValueError(f"unsupported GF(2^{k}); pick from {sorted(IRREDUCIBLES)}")
        self.k = k
        self.mod = IRREDUCIBLES[k]
        self.order = 1 << k
        self.mod_len = k

    # ---- element constructors -------------------------------------------- #
    def zero(self) -> "GF2E":
        return GF2E(0, self)

    def one(self) -> "GF2E":
        return GF2E(1, self)

    def generator(self) -> "GF2E":
        """The class of X — has multiplicative order dividing 2^k - 1."""
        return GF2E(0b10 if self.k > 1 else 1, self)

    def element(self, v: int) -> "GF2E":
        return GF2E(v % self.order if v >= 0 else v & (self.order - 1), self)

    def random(self, rng) -> "GF2E":
        return GF2E(rng.randrange(self.order), self)

    def all_elements(self):
        for v in range(self.order):
            yield GF2E(v, self)

    # ---- arithmetic -------------------------------------------------------- #
    def add(self, a: int, b: int) -> int:
        return a ^ b

    def mul(self, a: int, b: int) -> int:
        if a == 0 or b == 0:
            return 0
        return _reduce_mod(_clmul(a, b), self.mod, self.k)

    def inv(self, a: int) -> int:
        if a == 0:
            raise ZeroDivisionError
        # exponentiation: a^(2^k - 2)
        return pow_gf2(a, self.order - 2, self)

    def pow(self, a: int, e: int) -> int:
        result = 1
        base = a
        while e:
            if e & 1:
                result = self.mul(result, base)
            base = self.mul(base, base)
            e >>= 1
        return result

    def trace(self, a: int) -> int:
        """Absolute trace Tr: GF(2^k) -> GF(2)."""
        t = 0
        x = a
        for _ in range(self.k):
            t ^= x & 1
            x = self.mul(x, x)
        return t

    # ---- F_2-linear packing (LaBinius phi-style) --------------------------- #
    def pack(self, parts: list["GF2E"], part_field: "GF2") -> "GF2E":
        """Pack len(parts) elements of a smaller GF(2^s) into this GF(2^k)
        (k = s * len(parts)) by bit-block concatenation — the F_2-linear
        'field switch' packing used by LaBinius (phi: T -> V)."""
        s = part_field.k
        m = len(parts)
        if s * m != self.k:
            raise ValueError("sizes do not match packing layout")
        v = 0
        for i, p in enumerate(parts):
            v |= (p.value & ((1 << s) - 1)) << (i * s)
        return GF2E(v, self)

    def unpack(self, v: "GF2E", part_field: "GF2", m: int) -> list["GF2E"]:
        s = part_field.k
        if s * m != self.k:
            raise ValueError("sizes do not match packing layout")
        mask = (1 << s) - 1
        return [
            GF2E((v.value >> (i * s)) & mask, part_field) for i in range(m)
        ]

    def to_bytes(self, a: int) -> bytes:
        return a.to_bytes((self.k + 7) // 8, "little")

    def challenge(self, transcript, label: str = "") -> "GF2E":
        return GF2E(transcript.challenge_int(self.k, label=label), self)


def pow_gf2(a: int, e: int, field: GF2) -> int:
    result = 1
    base = a
    while e:
        if e & 1:
            result = field.mul(result, base)
        base = field.mul(base, base)
        e >>= 1
    return result


class GF2E:
    """Element of GF(2^k)."""

    __slots__ = ("value", "field")

    def __init__(self, value: int, field: GF2):
        self.value = value
        self.field = field

    def __add__(self, other):
        return GF2E(self.value ^ other.value, self.field)

    __sub__ = __add__

    def __mul__(self, other):
        if isinstance(other, int):
            return GF2E(self.value if other & 1 else 0, self.field)
        return GF2E(self.field.mul(self.value, other.value), self.field)

    def __pow__(self, e: int):
        return GF2E(self.field.pow(self.value, e), self.field)

    def inverse(self):
        return GF2E(self.field.inv(self.value), self.field)

    def __eq__(self, other):
        return isinstance(other, GF2E) and self.value == other.value

    def __hash__(self):
        return hash((self.value, self.field.k))

    def trace(self) -> int:
        return self.field.trace(self.value)

    def __repr__(self):
        return f"GF2E({self.value:#x}, k={self.field.k})"
