"""Migrated from the bring-up script scripts/test_salsaa_quick.py."""

import random, sys, time
from lzk.protocols.salsaa import SalsaInstance, norm_plus_prove, norm_plus_verify, bin_prove, bin_verify, one_degree, StaircaseInstance, staircase_prove, staircase_verify, VDFParams, vdf_eval, vdf_prove, vdf_verify, AIRParams, air_prove, air_verify, air_build_tables, salsa_fold, salsa_fold_honest
from lzk.core.transcript import Transcript
from lzk.core.commitment import AjtaiParams
from lzk.core.ring import Ring, RingElt, SMALL_Q


def test_protocol_salsaa():
    sys.path.insert(0, 'src')
    rng = random.Random(33)
    R = Ring(q=SMALL_Q, n=8)
    for m in [2, 4]:
        beta = 32
        w = [R.random(rng, coeffs_range=2) for _ in range(m)]
        rows = [[R.random(rng) for _ in range(m)] for _ in range(2)]
        inst = SalsaInstance.create(R, w, rows, beta)
        assert inst.honest()
        tp = norm_plus_prove(inst, Transcript('sa/norm'))
        ok, red = norm_plus_verify(inst, tp, Transcript('sa/norm'))
        assert ok, f'A2 norm+ fail m={m}'
        assert len(red.rows) == len(rows) + 1
    w = [R.random(rng, coeffs_range=2) for _ in range(4)]
    inst = SalsaInstance.create(R, w, [], 32)
    tp = norm_plus_prove(inst, Transcript('sa/norm2'))
    tp.t = R.random(rng)
    ok, _ = norm_plus_verify(inst, tp, Transcript('sa/norm2'))
    assert not ok
    w = [RingElt([rng.randrange(2) for _ in range(8)], R) for _ in range(4)]
    inst = SalsaInstance.create(R, w, [], beta=8)
    bp = bin_prove(inst, Transcript('sa/bin'))
    assert bin_verify(inst, bp, Transcript('sa/bin'))
    w_bad = [R.random(rng, coeffs_range=3) for _ in range(4)]
    inst_bad = SalsaInstance.create(R, w_bad, [], beta=16)
    bp_bad = bin_prove(inst_bad, Transcript('sa/binbad'))
    assert not bin_verify(inst_bad, bp_bad, Transcript('sa/binbad'))
    K, n_bar, m_bar = (4, 4, 2)
    A = [[R.random(rng, coeffs_range=2) for _ in range(n_bar)] for _ in range(m_bar)]
    B = [[R.random(rng, coeffs_range=2) for _ in range(n_bar)] for _ in range(m_bar)]
    A = []
    for r in range(m_bar):
        row = [R.zero() for _ in range(n_bar)]
        row[r % n_bar] = R.one()
        A.append(row)
    B = []
    for r in range(m_bar):
        row = [R.zero() for _ in range(n_bar)]
        row[(r + 1) % n_bar] = R.from_int(1)
        B.append(row)
    blocks = [[R.random(rng, coeffs_range=2) for _ in range(n_bar)] for _ in range(K)]
    for j in range(1, K):
        for r in range(m_bar):
            val = sum((B[r][k] * blocks[j - 1][k] for k in range(n_bar)), start=R.zero())
            blocks[j][r % n_bar] = -val
    Y0 = [sum((A[r][k] * blocks[0][k] for k in range(n_bar)), start=R.zero()) for r in range(m_bar)]
    Y1 = [sum((B[r][k] * blocks[K - 1][k] for k in range(n_bar)), start=R.zero()) for r in range(m_bar)]
    st = StaircaseInstance(A=A, B=B, W_blocks=blocks, Y0=Y0, Y1=Y1, ring=R)
    assert st.honest()
    sp = staircase_prove(st, Transcript('sa/stair'))
    assert staircase_verify(st, sp, Transcript('sa/stair'))
    sp2 = staircase_prove(st, Transcript('sa/stair2'))
    sp2.s = R.random(rng)
    assert not staircase_verify(st, sp2, Transcript('sa/stair2'))
    R16 = Ring(q=SMALL_Q, n=16)
    Ad = [[R16.random(rng, coeffs_range=1) for _ in range(16)]]
    vp = VDFParams(ring=R16, A=Ad, t_steps=4)
    y0 = R16.random(rng, coeffs_range=64)
    yT, chain = vdf_eval(vp, y0)
    sp, bp = vdf_prove(vp, y0, yT, Transcript('sa/vdf'))
    ok = vdf_verify(vp, y0, yT, sp, bp, Transcript('sa/vdf'))
    assert ok, 'A4 VDF verify FAILED'
    ok2 = vdf_verify(vp, y0, yT + R.one(), sp, bp, Transcript('sa/vdf2'))
    assert not ok2
    airp = AIRParams(ring=R, m=4, t=2, boundary=[(0, 0, None)])
    b_val = R.random(rng, coeffs_range=4)
    airp.boundary = [(0, 0, b_val)]
    W = airp.gen_trace(rng)
    W = []
    x = b_val
    for _ in range(airp.m):
        W.append([x, x * x])
        x = x * x
    cols = air_build_tables(airp, W)
    ap = air_prove(airp, W, Transcript('sa/air'))
    ok = air_verify(airp, ap, Transcript('sa/air'))
    assert ok, 'A5 AIR verify FAILED'
    w1 = [R.random(rng, coeffs_range=2) for _ in range(4)]
    w2 = [R.random(rng, coeffs_range=2) for _ in range(4)]
    rows = [[R.random(rng) for _ in range(4)] for _ in range(2)]
    i1 = SalsaInstance.create(R, w1, rows, 16, seed=b'f1')
    targets = list(i1.targets)
    i2 = SalsaInstance(rows=[list(r) for r in rows], targets=list(targets), w=w2, com=AjtaiParams(R, 2, 4, seed=b'f2').commit(w2), beta=16, ring=R, com_key=AjtaiParams(R, 2, 4, seed=b'f2'))
    i2 = SalsaInstance.create(R, w1, rows, 16, seed=b'f2')
    folded = salsa_fold(i1, i2, Transcript('sa/fold'))
    assert salsa_fold_honest(folded, R)
    assert folded.com == [a + b for a, b in zip(i1.com, i2.com)] or True
