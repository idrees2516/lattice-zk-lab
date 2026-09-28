import random, sys, math, time
sys.path.insert(0, 'src')
from lzk.protocols.hyperwolf import (HWParams, HyperWolf, build_a_univariate,
    build_a_multilinear, HW_Q32)
from lzk.core.transcript import Transcript

rng = random.Random(42)
p = HWParams(q=HW_Q32, d=8, b=2, k=3, delta=16, jl_rows=64)
print(f"params: iota={p.iota} kappa={p.kappa} N={p.N} beta={[round(b,1) for b in p.beta]}")
hw = HyperWolf(p)
f = [rng.randrange(p.q) for _ in range(p.N)]
u = rng.randrange(1, p.q)
y_true = hw.evaluate_direct(f, u, multilinear=False)
print("y_true =", y_true)

t0 = time.time()
cm, state = hw.commit(f)
t1 = time.time()
print(f"commit: {t1-t0:.2f}s, cm = {len(cm)} ring elts")

a0, a_list = build_a_univariate(u, p.q, p.k, p.b, p.d)
tp = Transcript("lzk/hw/test/uni")
proof = hw.eval(cm, state, u, y_true, multilinear=False, transcript=tp)
t2 = time.time()
print(f"prove: {t2-t1:.2f}s, rounds={len(proof.rounds)}, proof={proof.n_bytes} bytes")

tv = Transcript("lzk/hw/test/uni")
ok = hw.eval_verify(cm, a0, a_list, y_true, proof, tv)
t3 = time.time()
print(f"verify: {t3-t2:.2f}s -> {ok}")
assert ok, "UNIVARIATE VERIFY FAILED"

# wrong y rejected
tv2 = Transcript("lzk/hw/test/uni")
assert not hw.eval_verify(cm, a0, a_list, (y_true + 1) % p.q, proof, tv2), "wrong y accepted!"
print("wrong-y rejected PASS")

# tampered proof rejected
tv3 = Transcript("lzk/hw/test/uni")
pr2 = proof.rounds[0]
pr2.fold[0] = pr2.fold[0] + hw.ring.from_int(1)
assert not hw.eval_verify(cm, a0, a_list, y_true, proof, tv3), "tampered fold accepted!"
print("tampered-fold rejected PASS")

# multilinear
ell = int(math.log2(p.N))
u_vec = [rng.randrange(1, p.q) for _ in range(ell)]
y_ml = hw.evaluate_direct(f, u_vec, multilinear=True)
a0m, a_lm = build_a_multilinear(u_vec, p.q, p.k, p.b, p.d)
tpm = Transcript("lzk/hw/test/ml")
proofm = hw.eval(cm, state, u_vec, y_ml, multilinear=True, transcript=tpm)
tvm = Transcript("lzk/hw/test/ml")
okm = hw.eval_verify(cm, a0m, a_lm, y_ml, proofm, tvm)
print("multilinear verify:", okm)
assert okm
print("ALL HYPERWOLF TESTS PASS")
