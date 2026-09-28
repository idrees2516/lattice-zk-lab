"""Migrated from the bring-up script scripts/test_sc_quick.py."""

import random, sys
from lzk.core.ring import Ring, GOLDILOCKS
from lzk.core.sumcheck import run_sumcheck_product, SumcheckProduct, mle_eval, eq_table, eq_eval, bind_table


def test_core_sumcheck():
    sys.path.insert(0, 'src')
    rng = random.Random(11)
    for mu in range(1, 7):
        for J in range(1, 4):
            tables = [[rng.randrange(0, 50) for _ in range(1 << mu)] for _ in range(J)]
            claim = 0
            for b in range(1 << mu):
                p = 1
                for T in tables:
                    p *= T[b]
                claim += p
            challenges = []
            ok, final = run_sumcheck_product(tables, claim, lambda i, poly: rng.randrange(0, 100))
            assert ok, f'fail mu={mu} J={J}'
    R = Ring(q=GOLDILOCKS, n=8)
    for mu in range(1, 6):
        for J in range(1, 4):
            tables = [[R.random(rng) for _ in range(1 << mu)] for _ in range(J)]
            claim = R.zero()
            for b in range(1 << mu):
                p = R.one()
                for T in tables:
                    p = p * T[b]
                claim = claim + p
            ok, final = run_sumcheck_product(tables, claim, lambda i, poly: R.random(rng))
            assert ok, f'ring fail mu={mu} J={J}'
    tables = [[rng.randrange(0, 50) for _ in range(8)] for _ in range(2)]
    claim = 999999
    ok, _ = run_sumcheck_product(tables, claim, lambda i, poly: rng.randrange(0, 100))
    assert not ok
    class Cheat:

        def __init__(self, tables, claim):
            self.sc = SumcheckProduct(tables, claim)
    for mu in range(1, 7):
        T = [rng.randrange(0, 100) for _ in range(1 << mu)]
        for _ in range(3):
            pt = [rng.random() for _ in range(mu)]
            ref = sum((eq_eval(pt, [b >> mu - 1 - i & 1 for i in range(mu)]) * T[b] for b in range(1 << mu)))
            got = mle_eval(T, pt)
            assert abs(got - ref) < 1e-09 * max(1, abs(ref)), (mu, got, ref)
    pt = [rng.random() for _ in range(4)]
    T = eq_table(pt, 4)
    ref = sum((eq_eval(pt, [b >> 4 - 1 - i & 1 for i in range(4)]) ** 2 for b in range(16)))
    assert abs(mle_eval(T, pt) - ref) < 1e-09
    bp = [rng.randrange(2) for _ in range(4)]
    Tb = eq_table(bp, 4)
    assert abs(mle_eval(Tb, bp) - 1.0) < 1e-12
