"""Migrated from the bring-up script scripts/test_ringsc_quick.py."""

import random, sys
from lzk.core.ring import Ring, RingElt, GOLDILOCKS
from lzk.core.transcript import Transcript
from lzk.core.ringsc import RingSC, ProductClaim, norm_check_prove, norm_check_verify, norm_conjugate_inner, trace_balanced, batch_linear_rows, pow_ring


def test_core_ringsc():
    sys.path.insert(0, 'src')
    rng = random.Random(5)
    R = Ring(q=GOLDILOCKS, n=16)
    for m in [2, 4, 8]:
        beta_coeff = 4
        w = [R.random(rng, coeffs_range=beta_coeff) for _ in range(m)]
        beta = int(sum((x.l2_sq_int() for x in w)) ** 0.5) + 1
        t = norm_conjugate_inner(w)
        tr = trace_balanced(t)
        assert tr == R.n * sum((x.l2_sq_int() for x in w)), 'trace identity'
        tr_prove = norm_check_prove(w, Transcript('lzk/test/norm'), beta)
        ok, fw, fwb = norm_check_verify(tr_prove, Transcript('lzk/test/norm'), beta, R, mu=m.bit_length() - 1)
        assert ok, f'norm verify fail m={m}'
    w = [R.random(rng, coeffs_range=4) for _ in range(4)]
    p = norm_check_prove(w, Transcript('lzk/test/norm2'), 4)
    p.t = R.random(rng)
    ok, _, _ = norm_check_verify(p, Transcript('lzk/test/norm2'), 4, R, mu=2)
    assert not ok
    m = 8
    w = [R.random(rng, coeffs_range=4) for _ in range(m)]
    rows = [[R.random(rng) for _ in range(m)] for _ in range(3)]
    targets = []
    for row in rows:
        acc = R.zero()
        for a, x in zip(row, w):
            acc = acc + a * x
        targets.append(acc)
    tr = Transcript('lzk/test/batch')
    c, s, h = batch_linear_rows(rows, targets, w, tr, R)
    claim = R.zero()
    for z in range(m):
        claim = claim + h[z] * w[z]
    assert claim == s, 'batch claim identity'
    groups = [ProductClaim(tables=[list(w), [x.conjugate() for x in w]], value=norm_conjugate_inner(w)), ProductClaim(tables=[h, list(w)], value=s)]
    sc = RingSC(groups, R)
    t1 = Transcript('lzk/test/combined')
    proof = sc.prove(t1)
    ok, finals, last = sc.verify(proof, Transcript('lzk/test/combined'))
    assert ok
    t2 = Transcript('lzk/test/combined')
    alphas = sc.combiners(t2)
    fw, fwb, fh = (proof.final_values[0], proof.final_values[1], proof.final_values[2])
    manual = alphas[0] * (fw * fwb) + alphas[1] * (fh * fw)
    assert manual == last, 'combined terminal check'
