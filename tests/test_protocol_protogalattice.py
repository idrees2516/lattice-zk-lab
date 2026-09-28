"""Migrated from the bring-up script scripts/test_pgl_quick.py."""

import random, sys
from lzk.protocols.protogalattice import PGL, PolyMap, Accumulator, FoldInstance
from lzk.core.transcript import Transcript
from lzk.core.ring import Ring, SMALL_Q


def test_protocol_protogalattice():
    sys.path.insert(0, 'src')
    rng = random.Random(9)
    R = Ring(q=SMALL_Q, n=8)
    m, n = (4, 3)
    f = PolyMap.random_quadratic(R, m, n, rng, scalar=True)
    for i in range(n):
        for c in range(2, m):
            for r in range(m):
                f.N[i][r][c] = R.zero()
                f.M[i][c] = R.zero() if False else f.M[i][c]
            f.M[i][c] = R.zero()
            for r in range(m):
                f.N[i][c][r] = R.zero()
                f.N[i][r][c] = R.zero()
    pgl = PGL(R, f, k=2)
    beta = [rng.randrange(1, SMALL_Q) for _ in range(n)]
    w0 = [R.from_int(rng.randrange(0, 4)) for _ in range(m)]
    acc0 = pgl.fresh_accumulator(w0, beta, rng)
    ws = []
    for _ in range(pgl.k):
        wj = list(w0)
        for c in range(2, m):
            wj[c] = R.from_int(rng.randrange(0, 4))
        assert pgl.f.eval(wj) == pgl.f.eval(w0)
        ws.append(wj)
    insts = [FoldInstance(t=pgl.commit(w), x=[R.random(rng) for _ in range(2)], w=w) for w in ws]
    acc1, proof = pgl.fold_prove(acc0, insts, Transcript('pgl/fold'))
    ok, acc1v = pgl.fold_verify(acc0, insts, proof, Transcript('pgl/fold'))
    assert ok, 'PGL-Fold verify FAILED'
    lhs = pgl.power_constraint(acc1.w, acc1.beta)
    assert lhs == acc1.e, 'folded accumulator relation fails'
    _, pr2 = pgl.fold_prove(acc0, insts, Transcript('pgl/fold'))
    pr2.F_const = pr2.F_const + R.one()
    ok2, _ = pgl.fold_verify(acc0, insts, pr2, Transcript('pgl/fold'))
    assert not ok2, 'tampered F accepted'
    base, k1 = (4, 3)
    acc2, bproof = pgl.boot_prove(acc1, base, k1, Transcript('pgl/boot'))
    ok3, acc2v = pgl.boot_verify(acc1, bproof, Transcript('pgl/boot'))
    assert ok3, 'PGL-Boot verify FAILED'
    lhs2 = pgl.power_constraint(acc2.w, acc2.beta)
    assert lhs2 == acc2.e, 'bootstrapped accumulator relation fails'
    insts2 = []
    for _ in range(pgl.k):
        wj = list(acc2.w)
        for c in range(2, m):
            wj[c] = R.from_int(rng.randrange(0, 4))
        assert pgl.f.eval(wj) == pgl.f.eval(acc2.w)
        insts2.append(FoldInstance(t=pgl.commit(wj), x=[R.random(rng) for _ in range(2)], w=wj))
    acc3, _ = pgl.fold_prove(acc2, insts2, Transcript('pgl/fold2'))
    lhs3 = pgl.power_constraint(acc3.w, acc3.beta)
    assert lhs3 == acc3.e
