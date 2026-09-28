import random, sys, time
sys.path.insert(0, 'src')
from lzk.protocols.rokoko import (RoKokoParams, ComKey, com_commit, com_verify,
    LinComInstance, rokoko_prove, rokoko_verify, g_inv_vec, g_vec)
from lzk.core.transcript import Transcript
from lzk.core.ring import Ring, SMALL_Q, mat_vec

rng = random.Random(21)
# lab params: small prime q=12289 (14 bits) -> gadget_len 14 covers q
p = RoKokoParams(q=SMALL_Q, n_ring=8, n0=2, gadget_len=14, com_depth=1, r=2, beta_w=24)
ring = p.ring
ck = ComKey(p)

# --- COM depth 1 and 2 roundtrip ---
m = 8
w = [ring.random(rng, coeffs_range=2) for _ in range(m)]
com, aux = com_commit(ck, w, 1, p.gadget_len)
assert com_verify(ck, w, com, aux, 1, p.gadget_len, beta0=100)
print("COM depth-1 PASS")
com2, aux2 = com_commit(ck, w, 2, p.gadget_len)
# manual depth-2 verify: A w == y; G(x[:l*n0]) == y; com == recursive commit of x
assert ck.commit(w, p.n0) == aux2.y
target = 1 << ((p.gadget_len * p.n0 - 1).bit_length())
assert len(aux2.x) == target
assert g_vec(aux2.x[: p.gadget_len * p.n0], p.gadget_len, p.n0) == aux2.y
inner_com, _ = com_commit(ck, aux2.x, 1, p.gadget_len)
assert list(inner_com) == list(com2)
print("COM depth-2 PASS")

# --- end-to-end: committed-linear instance + rokoko round ---
m_w, r = 8, 2
F0 = ck.key(p.n0, m_w)          # vSIS key committing W
W = [[ring.random(rng, coeffs_range=2) for _ in range(r)] for _ in range(m_w)]
# Y_0 such that F0 W = H0 Y0: take H0 = F0 and Y0 = W (r columns)
Y0 = [[W[j][col] for col in range(r)] for j in range(m_w)]
# commit Y0's flattened vec (per column, depth 1)
yvec = [Y0[k][0] for k in range(m_w)]
com_y, aux_y = com_commit(ck, yvec, 1, p.gadget_len)
inst = LinComInstance(
    F=[F0], H=[F0], coms=[com_y], aux=[aux_y],
    ell=[], rr=[], tt=[], A=None, b=None,
    m_w=m_w, r=r, beta_w=24, W=W, Ys=[Y0],
)
assert inst.check_honest(ck, 1, p.gadget_len)
print("Xi^lin honest instance PASS")

t0 = time.time()
proof = rokoko_prove(inst, ck, Transcript("lzk/rk/test"))
t1 = time.time()
ok = rokoko_verify(inst, ck, proof, Transcript("lzk/rk/test"))
t2 = time.time()
print(f"rokoko round: prove {t1-t0:.2f}s verify {t2-t1:.2f}s -> {ok}")
assert ok, "ROKOKO VERIFY FAILED"

# --- tamper tests ---
pr2 = rokoko_prove(inst, ck, Transcript("lzk/rk/test"))
pr2.w_hat[0] = pr2.w_hat[0] + ring.from_int(1)
assert not rokoko_verify(inst, ck, pr2, Transcript("lzk/rk/test")), "tampered w_hat accepted"
pr3 = rokoko_prove(inst, ck, Transcript("lzk/rk/test"))
pr3.fold_proof.v = ring.random(rng)
assert not rokoko_verify(inst, ck, pr3, Transcript("lzk/rk/test")), "tampered v accepted"
pr4 = rokoko_prove(inst, ck, Transcript("lzk/rk/test"))
pr4.lin_proof.z0 = ring.random(rng)
assert not rokoko_verify(inst, ck, pr4, Transcript("lzk/rk/test")), "tampered z0 accepted"
print("tamper rejections PASS")
print("ALL ROKOKO TESTS PASS")
