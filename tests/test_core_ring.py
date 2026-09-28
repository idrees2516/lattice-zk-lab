"""Migrated from the bring-up script scripts/test_ring_quick.py."""

import random, sys
from lzk.core.ring import Ring, RingElt, GOLDILOCKS, SMALL_Q


def test_core_ring():
    sys.path.insert(0, 'src')
    rng = random.Random(7)
    for q, n, gen in [(GOLDILOCKS, 64, None), (GOLDILOCKS, 256, None), (SMALL_Q, 64, None), (101, 32, None)]:
        R = Ring(q=q, n=n, generator=gen)
        print(f'q={q} n={n} ntt={R._use_ntt}')
        for t in range(5):
            a = [rng.randrange(q) for _ in range(n)]
            b = [rng.randrange(q) for _ in range(n)]
            fast = R.mul_raw(a, b)
            ref = R.schoolbook_negacyclic(a, b)
            assert fast == ref, f'mul mismatch q={q} n={n} t={t}'
        e = R.element([rng.randrange(q) for _ in range(n)])
        assert e.conjugate().conjugate() == e
        g = R.generator_elt()
        gp = R.zero()
        gp.coeffs[n - 1] = 1
        assert (g * gp).coeffs == R.from_int(-1).coeffs
        assert e.l2_sq_int() == sum((R.center(c, q) ** 2 for c in e.coeffs))
