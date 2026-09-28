import random, sys
sys.path.insert(0, 'src')
from lzk.core.ring import Ring, RingElt, GOLDILOCKS
from lzk.core.transcript import Transcript
from lzk.core.ringsc import (RingSC, ProductClaim, norm_check_prove, norm_check_verify,
                              norm_conjugate_inner, trace_balanced, batch_linear_rows, pow_ring)

rng = random.Random(5)
R = Ring(q=GOLDILOCKS, n=16)

# --- norm check end-to-end ---
for m in [2, 4, 8]:
    # beta bounds the l2 norm of the flattened witness (lab convention):
    # trace_balanced(t) = n * ||W||^2 must be <= n * beta^2
    beta_coeff = 4
    w = [R.random(rng, coeffs_range=beta_coeff) for _ in range(m)]
    beta = int(sum(x.l2_sq_int() for x in w) ** 0.5) + 1
    t = norm_conjugate_inner(w)
    tr = trace_balanced(t)
    assert tr == R.n * sum(x.l2_sq_int() for x in w), "trace identity"
    tr_prove = norm_check_prove(w, Transcript("lzk/test/norm"), beta)
    ok, fw, fwb = norm_check_verify(tr_prove, Transcript("lzk/test/norm"), beta, R, mu=(m).bit_length()-1)
    assert ok, f"norm verify fail m={m}"
print("norm check PASS")

# --- cheating trace rejected ---
w = [R.random(rng, coeffs_range=4) for _ in range(4)]
p = norm_check_prove(w, Transcript("lzk/test/norm2"), 4)
p.t = R.random(rng)   # tamper
ok, _, _ = norm_check_verify(p, Transcript("lzk/test/norm2"), 4, R, mu=2)
assert not ok
print("norm cheat detection PASS")

# --- batch: linear rows ---
m = 8
w = [R.random(rng, coeffs_range=4) for _ in range(m)]
rows = [[R.random(rng) for _ in range(m)] for _ in range(3)]
targets = []
for row in rows:
    acc = R.zero()
    for a, x in zip(row, w):
        acc = acc + a * x
    targets.append(acc)
tr = Transcript("lzk/test/batch")
c, s, h = batch_linear_rows(rows, targets, w, tr, R)
# check the claim: sum_z MLE[h](z)*MLE[w](z) == s
claim = R.zero()
for z in range(m):
    claim = claim + h[z] * w[z]
assert claim == s, "batch claim identity"
print("batch linear rows PASS")

# --- combined RingSC with two groups ---
groups = [
    ProductClaim(tables=[list(w), [x.conjugate() for x in w]], value=norm_conjugate_inner(w)),
    ProductClaim(tables=[h, list(w)], value=s),
]
sc = RingSC(groups, R)
t1 = Transcript("lzk/test/combined")
proof = sc.prove(t1)
ok, finals, last = sc.verify(proof, Transcript("lzk/test/combined"))
assert ok
# terminal: group0 final_w * final_wbar == last contribution? combined final = alpha0*(w_r*wbar_r) + alpha1*(h_r*w_r)
# recompute manually
t2 = Transcript("lzk/test/combined")
alphas = sc.combiners(t2)
fw, fwb, fh = proof.final_values[0], proof.final_values[1], proof.final_values[2]
manual = alphas[0] * (fw * fwb) + alphas[1] * (fh * fw)
assert manual == last, "combined terminal check"
print("combined RingSC PASS")
