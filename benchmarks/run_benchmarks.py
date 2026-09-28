#!/usr/bin/env python3
"""Benchmark harness (Wave 8): per-protocol prover/verifier wall-clock and
proof-size models at lab scale, plus the HyperWolf paper-parameter size
model (Table 2 reproduction).  Run with --quick for CI smoke tests."""

import argparse
import random
import sys
import time
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))


def bench(label):
    def deco(fn):
        RESULTS.append((label, fn))
        return fn
    return deco


RESULTS = []


def run(scale: str):
    rng = random.Random(1234)
    from lzk.core.ring import Ring, RingElt, SMALL_Q, GOLDILOCKS
    from lzk.core.transcript import Transcript

    R = Ring(q=GOLDILOCKS, n=8)
    RS = Ring(q=SMALL_Q, n=8)

    print(f"{'protocol':28s} {'op':8s} {'time':>10s}   detail")
    print("-" * 72)

    # ---------------- core engine ----------------
    from lzk.core.ringsc import RingSC, ProductClaim, norm_conjugate_inner
    m = 32
    w = [R.random(rng, coeffs_range=2) for _ in range(m)]
    wbar = [x.conjugate() for x in w]
    t = norm_conjugate_inner(w)
    sc = RingSC([ProductClaim([list(w), wbar], t)], R)
    t0 = time.time(); pr = sc.prove(Transcript("b1")); t1 = time.time()
    ok, _, _ = sc.verify(pr, Transcript("b1")); t2 = time.time()
    print(f"{'RingSC (7.8) norm sumcheck':28s} {'prove':8s} {t1-t0:10.3f}s   m={m}, n={R.n}")
    print(f"{'':28s} {'verify':8s} {t2-t1:10.3f}s   accept={ok}")

    # ---------------- HyperWolf ----------------
    from lzk.protocols.hyperwolf import HWParams, HyperWolf, build_a_univariate, HW_Q32, paper_params
    p = HWParams(q=HW_Q32, d=8, b=2, k=3, delta=16, jl_rows=64)
    hw = HyperWolf(p)
    f = [rng.randrange(p.q) for _ in range(p.N)]
    u = rng.randrange(1, p.q)
    y = hw.evaluate_direct(f, u, multilinear=False)
    t0 = time.time(); cm, st = hw.commit(f); t1 = time.time()
    a0, al = build_a_univariate(u, p.q, p.k, p.b, p.d)
    pr = hw.eval(cm, st, u, y, False, Transcript("b2")); t2 = time.time()
    ok = hw.eval_verify(cm, a0, al, y, pr, Transcript("b2")); t3 = time.time()
    print(f"{'HyperWolf (7.12) k=3':28s} {'commit':8s} {t1-t0:10.3f}s   N={p.N} coeffs")
    print(f"{'':28s} {'prove':8s} {t2-t1:10.3f}s   proof={pr.n_bytes} B")
    print(f"{'':28s} {'verify':8s} {t3-t2:10.3f}s   accept={ok}")
    # paper size model (Table 2)
    for N in [2**15, 2**25]:
        pp = paper_params(N)
        per_round = pp.b * (1 + pp.jl_rows + 64)  # paper's iota=32, kappa=64
        model = (pp.k - 1) * per_round * 16 + pp.b * 32 * 16
        print(f"{'  paper model':28s} {'size':8s} {'':>10s}   N=2^{N.bit_length()-1}: {model/1024:.1f} KB")

    if scale == "quick":
        print("\n(quick mode — see docs/BENCHMARKS.md for the full suite)")
        return

    # ---------------- RoKoko / SALSAA / PGL ----------------
    from lzk.protocols.rokoko import RoKokoParams, ComKey, LinComInstance, rokoko_prove, rokoko_verify, com_commit
    p = RoKokoParams(q=SMALL_Q, n_ring=8, n0=2, gadget_len=14, com_depth=1, r=2, beta_w=24)
    ck = ComKey(p)
    F0 = ck.key(p.n0, 8)
    W = [[RS.random(rng, coeffs_range=2) for _ in range(2)] for _ in range(8)]
    Y0 = [[W[j][c] for c in range(2)] for j in range(8)]
    yv = [Y0[k][0] for k in range(8)]
    com_y, aux_y = com_commit(ck, yv, 1, p.gadget_len)
    inst = LinComInstance(F=[F0], H=[F0], coms=[com_y], aux=[aux_y], ell=[], rr=[],
                          tt=[], A=None, b=None, m_w=8, r=2, beta_w=24, W=W, Ys=[Y0])
    t0 = time.time(); rk_pr = rokoko_prove(inst, ck, Transcript("b3")); t1 = time.time()
    ok = rokoko_verify(inst, ck, rk_pr, Transcript("b3")); t2 = time.time()
    print(f"{'RoKoko (7.13) fold-split':28s} {'prove':8s} {t1-t0:10.3f}s   m_w=8, r=2")
    print(f"{'':28s} {'verify':8s} {t2-t1:10.3f}s   accept={ok}")

    from lzk.protocols.salsaa import (SalsaInstance, norm_plus_prove, norm_plus_verify,
        bin_prove, bin_verify, StaircaseInstance, staircase_prove, staircase_verify,
        VDFParams, vdf_eval, vdf_prove, vdf_verify, AIRParams, air_prove, air_verify)
    w = [RS.random(rng, coeffs_range=2) for _ in range(8)]
    rows = [[RS.random(rng) for _ in range(8)] for _ in range(2)]
    si = SalsaInstance.create(RS, w, rows, 32)
    t0 = time.time(); np_ = norm_plus_prove(si, Transcript("b4")); t1 = time.time()
    ok, _ = norm_plus_verify(si, np_, Transcript("b4")); t2 = time.time()
    print(f"{'SALSAA (7.11) A2 Pi_norm+':28s} {'prove':8s} {t1-t0:10.3f}s")
    print(f"{'':28s} {'verify':8s} {t2-t1:10.3f}s   accept={ok}")
    # A4 VDF
    R16 = Ring(q=SMALL_Q, n=16)
    Ad = [[R16.random(rng, coeffs_range=1) for _ in range(16)]]
    vp = VDFParams(ring=R16, A=Ad, t_steps=4)
    y0 = R16.random(rng, coeffs_range=64)
    yT, _ = vdf_eval(vp, y0)
    t0 = time.time(); sp, bp = vdf_prove(vp, y0, yT, Transcript("b5")); t1 = time.time()
    ok = vdf_verify(vp, y0, yT, sp, bp, Transcript("b5")); t2 = time.time()
    print(f"{'SALSAA A4 VDF (T=4)':28s} {'prove':8s} {t1-t0:10.3f}s")
    print(f"{'':28s} {'verify':8s} {t2-t1:10.3f}s   accept={ok}")

    from lzk.protocols.protogalattice import PGL, PolyMap, FoldInstance
    f_map = PolyMap.random_quadratic(RS, 4, 3, rng, scalar=True)
    # kernel structure (f depends on the first 2 coords only) so fresh
    # witnesses share the accumulator's f-image (same-statement folding)
    for i in range(3):
        for c in range(2, 4):
            f_map.M[i][c] = RS.zero()
            for r in range(4):
                f_map.N[i][r][c] = RS.zero()
                f_map.N[i][c][r] = RS.zero()
    pgl = PGL(RS, f_map, k=2)
    beta = [rng.randrange(1, SMALL_Q) for _ in range(3)]
    w0 = [RS.from_int(rng.randrange(0, 4)) for _ in range(4)]
    acc0 = pgl.fresh_accumulator(w0, beta, rng)
    ws = []
    for _ in range(2):
        wj = list(w0)
        for c in range(2, 4):
            wj[c] = RS.from_int(rng.randrange(0, 4))
        ws.append(wj)
    insts = [FoldInstance(t=pgl.commit(wj), x=[RS.random(rng) for _ in range(2)], w=wj) for wj in ws]
    t0 = time.time(); acc1, fpr = pgl.fold_prove(acc0, insts, Transcript("b6")); t1 = time.time()
    ok, _ = pgl.fold_verify(acc0, insts, fpr, Transcript("b6")); t2 = time.time()
    print(f"{'ProtogaLattice (7.4) fold':28s} {'prove':8s} {t1-t0:10.3f}s")
    print(f"{'':28s} {'verify':8s} {t2-t1:10.3f}s   accept={ok}")

    # ---------------- the other ten ----------------
    from lzk.protocols.latticefold_plus import LatticeFoldPlus
    lf = LatticeFoldPlus(R, 8, rows=2)
    M = [[R.random(rng, coeffs_range=2) for _ in range(8)] for _ in range(2)]
    w1 = [R.random(rng, coeffs_range=2) for _ in range(8)]
    w2 = [R.random(rng, coeffs_range=2) for _ in range(8)]
    i1 = lf.instance(w1, M)
    i2 = lf.instance(w2, M)
    t0 = time.time(); folded, T = lf.fold(i1, i2, Transcript("b7")); t1 = time.time()
    print(f"{'LatticeFold+ fold':28s} {'prove':8s} {t1-t0:10.3f}s")

    from lzk.protocols.akita import Akita
    ak = Akita(R, 4, 4)
    Wm = [[R.random(rng, coeffs_range=2) for _ in range(4)] for _ in range(4)]
    rr = [R.random(rng, coeffs_range=2) for _ in range(2)]
    rc = [R.random(rng, coeffs_range=2) for _ in range(2)]
    t0 = time.time(); ak.eval_prove(Wm, rr, rc, Transcript("b8")); t1 = time.time()
    print(f"{'Akita tensor round':28s} {'prove':8s} {t1-t0:10.3f}s")

    from lzk.protocols.serval import Serval
    sv = Serval(R, 32)
    v = [R.random(rng, coeffs_range=2) for _ in range(32)]
    t0 = time.time(); sv.run_ipa(v, Transcript("b9")); t1 = time.time()
    print(f"{'Serval split-fold IPA':28s} {'prove':8s} {t1-t0:10.3f}s   m=32 (5 rounds)")

    from lzk.protocols.symphony import Symphony
    sy = Symphony(R, 8, arity=4)
    batches = [[[R.random(rng, coeffs_range=2) for _ in range(8)] for _ in range(4)] for _ in range(3)]
    t0 = time.time(); sy.compose_rounds(batches, Transcript("b10")); t1 = time.time()
    print(f"{'Symphony arity-4 folding':28s} {'prove':8s} {t1-t0:10.3f}s")

    print("-" * 72)
    print("All benchmarks complete. Lab scale: q=2^64/2^13, rings n=8..16, m<=64.")
    print("Paper-scale numbers: see docs/papers/<name>.md section 7.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    run("quick" if args.quick else "full")
