"""Migrated from the bring-up script scripts/test_hyperwolf_quick.py."""

import random, sys, math, time
from lzk.protocols.hyperwolf import HWParams, HyperWolf, build_a_univariate, build_a_multilinear, HW_Q32
from lzk.core.transcript import Transcript


def test_protocol_hyperwolf():
    sys.path.insert(0, 'src')
    rng = random.Random(42)
    p = HWParams(q=HW_Q32, d=8, b=2, k=3, delta=16, jl_rows=64)
    hw = HyperWolf(p)
    f = [rng.randrange(p.q) for _ in range(p.N)]
    u = rng.randrange(1, p.q)
    y_true = hw.evaluate_direct(f, u, multilinear=False)
    t0 = time.time()
    cm, state = hw.commit(f)
    t1 = time.time()
    a0, a_list = build_a_univariate(u, p.q, p.k, p.b, p.d)
    tp = Transcript('lzk/hw/test/uni')
    proof = hw.eval(cm, state, u, y_true, multilinear=False, transcript=tp)
    t2 = time.time()
    tv = Transcript('lzk/hw/test/uni')
    ok = hw.eval_verify(cm, a0, a_list, y_true, proof, tv)
    t3 = time.time()
    assert ok, 'UNIVARIATE VERIFY FAILED'
    tv2 = Transcript('lzk/hw/test/uni')
    assert not hw.eval_verify(cm, a0, a_list, (y_true + 1) % p.q, proof, tv2), 'wrong y accepted!'
    tv3 = Transcript('lzk/hw/test/uni')
    pr2 = proof.rounds[0]
    pr2.fold[0] = pr2.fold[0] + hw.ring.from_int(1)
    assert not hw.eval_verify(cm, a0, a_list, y_true, proof, tv3), 'tampered fold accepted!'
    ell = int(math.log2(p.N))
    u_vec = [rng.randrange(1, p.q) for _ in range(ell)]
    y_ml = hw.evaluate_direct(f, u_vec, multilinear=True)
    a0m, a_lm = build_a_multilinear(u_vec, p.q, p.k, p.b, p.d)
    tpm = Transcript('lzk/hw/test/ml')
    proofm = hw.eval(cm, state, u_vec, y_ml, multilinear=True, transcript=tpm)
    tvm = Transcript('lzk/hw/test/ml')
    okm = hw.eval_verify(cm, a0m, a_lm, y_ml, proofm, tvm)
    assert okm
