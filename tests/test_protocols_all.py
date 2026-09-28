"""Migrated from the bring-up script scripts/test_all_protocols_quick.py."""

import random, sys
from lzk.core.transcript import Transcript
from lzk.core.ring import Ring, RingElt, SMALL_Q, GOLDILOCKS, dot, mat_vec
from lzk.core.field import GF2, GF2E
from lzk.protocols.latticefold_plus import LatticeFoldPlus, LFInstance
from lzk.protocols.twistshout import Shout, Twist, TwistState
from lzk.protocols.labinius import LaBinius
from lzk.core.sumcheck import mle_eval
from lzk.protocols.akita import Akita
from lzk.protocols.cyclo import Cyclo
from lzk.protocols.pikkufold import PikkuFold
from lzk.protocols.quasar import Quasar
from lzk.protocols.serval import Serval
from lzk.protocols.symphony import Symphony
from lzk.protocols.hachi import Hachi


def test_protocols_all():
    sys.path.insert(0, 'src')
    rng = random.Random(99)
    R = Ring(q=GOLDILOCKS, n=8)
    RING16 = Ring(q=SMALL_Q, n=16)
    m = 8
    lf = LatticeFoldPlus(R, m, rows=2)
    M = [[R.random(rng, coeffs_range=2) for _ in range(m)] for _ in range(2)]
    w1 = [R.random(rng, coeffs_range=2) for _ in range(m)]
    w2 = [R.random(rng, coeffs_range=2) for _ in range(m)]
    i1, i2 = (lf.instance(w1, M), lf.instance(w2, M))
    folded, T = lf.fold(i1, i2, Transcript('lf'))
    assert mat_vec(M, folded.w) == folded.u, 'LF+ folded constraint fails'
    t, nproof = lf.norm_check_prove(folded.w, Transcript('lf/n'))
    assert lf.norm_check_verify(len(folded.w), t, nproof, folded.beta, Transcript('lf/n'))
    q = GOLDILOCKS
    mm = 8
    W = [rng.randrange(q) for _ in range(mm)]
    a = [0] * mm
    a[3] = 1
    v = W[3]
    sh = Shout(q, mm)
    lp = sh.lookup_prove(W, a, v, Transcript('sh'))
    assert sh.lookup_verify(W, a, v, lp, Transcript('sh'))
    assert sh.onehot_check(a, Transcript('sh/oh'))
    bad = [0] * mm
    bad[2] = 5
    assert not sh.onehot_check(bad, Transcript('sh/bad'))
    T_steps = 4
    addrs = []
    for t_i in range(T_steps):
        row = [0] * mm
        row[rng.randrange(mm)] = 1
        addrs.append(row)
    read_vals = [sum((addrs[t][z] * W[z] for z in range(mm))) % q for t in range(T_steps)]
    tw = Twist(q, mm, T_steps)
    st = TwistState(addrs=addrs, read_vals=read_vals)
    proof = tw.read_check_prove(st, W, Transcript('tw'))
    assert tw.read_check_verify(st, W, proof, Transcript('tw'))
    bi = LaBinius(k=8, mu=3)
    f = bi.field
    table = [GF2E(rng.randrange(f.order), f) for _ in range(8)]
    pt = [GF2E(rng.randrange(f.order), f) for _ in range(3)]
    claim = mle_eval(table, pt)
    pr = bi.eval_prove(table, pt, Transcript('bi'))
    assert bi.eval_verify(8, pt, claim, pr, Transcript('bi'))
    eqt = 1
    rows, cols = (4, 4)
    ak = Akita(R, rows, cols)
    Wm = [[R.random(rng, coeffs_range=2) for _ in range(cols)] for _ in range(rows)]
    coms = ak.commit(Wm)
    r_row = [R.random(rng, coeffs_range=2) for _ in range(2)]
    r_col = [R.random(rng, coeffs_range=2) for _ in range(2)]
    y, com_fold, norm_val, proof, W_fold = ak.eval_prove(Wm, r_row, r_col, Transcript('ak'))
    assert ak.eval_verify(y, com_fold, norm_val, proof, W_fold, beta=1 << 20, transcript=Transcript('ak'))
    cy = Cyclo(R, m)
    w3 = [R.random(rng, coeffs_range=2) for _ in range(m)]
    w_star, cross, high, low, proof = cy.fold_with_partial_range(w1, w3, Transcript('cy'))
    assert cy.verify_partial_range(cross, high, low, base=8)
    pf = PikkuFold(R, m, layers=2, factor=2)
    w_f, images, final, norm_val = pf.fold_lrp(w1, w2, Transcript('pf'))
    assert pf.verify_lrp(images, final, norm_val, beta=1 << 20)
    qs = Quasar(R, m, arity=2)
    ws = [[R.random(rng, coeffs_range=2) for _ in range(m)] for _ in range(2)]
    acc = [R.random(rng, coeffs_range=2) for _ in range(m)]
    acc2, gammas, union = qs.accumulate_fold(acc, ws, Transcript('qs'))
    acc3, _, _ = qs.accumulate_fold(acc2, ws, Transcript('qs2'))
    sv = Serval(R, m)
    v = [R.random(rng, coeffs_range=2) for _ in range(m)]
    final_v, hist, t_final = sv.run_ipa(v, Transcript('sv'))
    t_true = sum((x.l2_sq_int() for x in v))
    sy = Symphony(R, m, arity=4)
    batches = [[[R.random(rng, coeffs_range=2) for _ in range(m)] for _ in range(4)] for _ in range(2)]
    acc_s, norm_s = sy.compose_rounds(batches, Transcript('sy'))
    assert acc_s is not None
    ha = Hachi(R, m)
    t_h, proof_h = ha.ring_switch_prove(w1, R.random(rng), Transcript('ha'))
    assert ha.ring_switch_verify(t_h, proof_h, beta=64, transcript=Transcript('ha'))
