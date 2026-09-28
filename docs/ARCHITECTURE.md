# lzk — Architecture (In Depth)

This document is the authoritative map of the lab: every engine component,
every protocol's internal mechanics as implemented, the exact mapping from
each paper's figures to code, the invariants that make the proofs hold, and
the deliberate deviations.  Read it together with `docs/papers/<name>.md`
(the 15 per-paper deep analyses, ~11,900 lines total) and
`docs/GAP_LEDGER.md` (the consolidated status).

```
                     ┌────────────────────────────────────────────┐
                     │                protocols/                  │
   hyperwolf  rokoko  salsaa  protogalattice  latticefold_plus    │
   labinius   akita   twistshout  cyclo  pikkufold  quasar        │
   serval     symphony  hachi                                   │
                     └───────────────┬────────────────────────────┘
                                     │ uses
                     ┌───────────────┴────────────────────────────┐
                     │                 core/                      │
   ring  field  sumcheck  ringsc  groebner  transcript            │
   commitment  serialization                                      │
                     └───────────────┬────────────────────────────┘
                                     │ tested/benched by
                     ┌───────────────┴────────────┐
                     │ tests/ (pytest)  benchmarks/│
                     └────────────────────────────┘
```

---

## Part I — The Core Engine

### 1. `core/ring.py` — R_q = Z_q[X]/(X^n + 1)

The algebraic ground of every protocol in the lab.

**Representation.**  A `RingElt` is a list of `n` Python ints in `[0, q)`
(canonical representatives).  `n` is a power of two; the negacyclic modulus
`X^n + 1` makes `X^{2n} = 1`, `X^n = -1`.

**Multiplication — two exact paths.**
- *Negacyclic NTT* when `2n | q-1` (the Goldilocks prime
  `2^64 - 2^32 + 1`, generator 7): the map
  `a ↦ (a(psi^{2i+1}))_i` (twist by `psi^j` + cyclic Cooley–Tukey with the
  primitive n-th root `omega = psi^2`) is a ring homomorphism `R_q → Z_q^n`
  because `X^n = -1` at every point `psi^{odd}`.  Multiply pointwise,
  untwist.  Verified against a schoolbook reference on every supported
  modulus.
- *Kronecker substitution* otherwise (e.g. HyperWolf's `q ≡ 5 mod 8`
  primes, which are NTT-hostile): pack the coefficient vectors into one
  big integer with `slot_bits = 2·log2(q) + log2(n) + 8` padding, one
  bigint multiply (Karatsuba), unpack slots, fold `p[k] - p[k+n]` for the
  negacyclic reduction.

**The conjugation involution (the single most-used identity).**
`conj(a) = a(X^{-1}) = a_0 - Σ_{i≥1} a_{n-i} X^i` (the signs are forced by
`X^{-1} = -X^{n-1}` — getting this wrong silently breaks every trace/norm
identity; the lab caught this on day one).  It makes the Hermitian trace
pairing exact:
```
Tr(conj(a)·b) = n·⟨a, b⟩_coeff     Tr(conj(a)·a) = n·‖a‖²
```
and the constant term of `conj(a)·a` is `‖a‖²` — the wraparound-free
integer the norm checks compare against bounds (`trace_balanced`).

**Norms.**  Always over centred representatives `(−q/2, q/2]`:
`l2_sq_int`, `linf_int` — the papers' bounded-norm witnesses live on the
integer side of the mod-q arithmetic; the *wraparound-free regime*
(`4β² < q`) is what lets mod-q statements certify integer properties.

**Module helpers.**  `dot`, `mat_vec`, `lin_comb` over `R_q` vectors — the
Ajtai commitment's grammar.

### 2. `core/field.py` — GF(2^k) tower fields

Carry-less multiplication of Python ints + reduction by the fixed
irreducibles (k ∈ {1,2,4,8,16,32,64,128}); characteristic-two arithmetic
(`a - b = a + b`) with reflected operators for mixed int/GF2E expressions;
`pack`/`unpack` implement the F_2-linear bit-block packing that LaBinius's
field switch relies on.

### 3. `core/sumcheck.py` — the multilinear sumcheck engine

The engine proves `Σ_{x∈{0,1}^μ} Π_j MLE[T_j](x) = v` for **products of
multilinear tables** over any commutative ring (ints, `R_q`, `GF(2^k)`).

- Round messages are **coefficient-form** univariates `g_i(X) = Σ_d c_d X^d`
  of degree `J` (#tables): the verifier checks `g(0) + g(1) = previous`
  where `g(1) = Σ c_d`, samples `ρ_i`, keeps the Horner running claim.
- The prover uses the classic linear-time **bind recursion**: each round
  halves every table (`bind_table`), one pass computes the round polynomial
  via degree-J products of `(low, high)` pairs.
- `eq_table` / `mle_eval` / `bits_of` implement the MSB-first hypercube
  convention uniformly across the lab (an endianness bug here — first
  variable in the low bit — was caught and fixed early; see
  `scripts/test_sc_quick.py`).

This engine is the shared substrate of: SALSAA's Π_sum, LF+'s §5.0 layer,
Twist&Shout's one-hot PIOPs, RoKoko's `sumcheckify`, HyperWolf's PCS, and
the AIR claims.

### 4. `core/ringsc.py` — RingSC (lab item 7.8)

The **ring-norm sumcheck** engine the prior plan identified as the reuse
hub.  On top of `sumcheck.py`:

- `RingSC` batches several product claims into ONE sumcheck with
  **combiners** — drawn from the transcript, or **explicit**
  (`explicit_combiners=...`) when the protocol supplies its own batching
  weights (RoKoko's `eq(bin(i), γ)` ladder, SALSAA's α, LF+'s Remark-2.5
  power bases).  The proof carries the round messages, final bound values
  and the challenge point.
- **Π_norm (SALSAA Fig. 4 / LF+ norm-check)**: `t = Σ_j conj(w_j)·w_j`
  computed directly in O(m) — the paper's prover-efficiency trick that
  replaces RPS/RnR's O(m log m) convolution commitment — plus the
  balanced-trace check `0 ≤ Tr(t) ≤ n·β²` and the degree-2 sumcheck
  `Σ_z MLE[W](z)·MLE[W̄](z) = t`.
- **Π_batch (SALSAA Fig. 3)**: bottom-row folding with the `c^i` power
  ladder (`fold_rows`).
- The terminal checks are deliberately left to callers (each protocol pins
  its own final openings — LF+ §5.0: "each sub-protocol supplies its own
  opening step").

### 5. `core/groebner.py` — the staircase Gröbner reduction (P0-4)

ProtogaLattice Proposition 1: `I = ⟨Z_{i,j} = Y_iY_j − Y_i : j ≤ i⟩ ⊂
Z_q[Y_0..Y_{k-1}]` has the **reduced Gröbner basis** `G = {Z_{i,j}}` whose
division realizes two rewrite rules:

```
Y_i^a  →  Y_i            (idempotence, Z_{i,i})
Y_i·Y_j →  Y_max(i,j)    (absorption,  Z_{i,j})
```

so every polynomial's normal form is **affine linear** (`c_0 + Σ c_iY_i`),
the quotient module is free of rank k+1, and division produces *unique*
quotients `K_{rs}` with `deg(K_{rs}) ≤ deg(P) − 2` (Pauer's Gröbner-bases-
over-rings, the paper's D.1).  `divide()` implements the deterministic
greedy division (pair-collapse on the two largest indices, idempotence on
singles) with quotient extraction; `verify_division` re-checks
`P = Σ KZ + R` exactly; `l_basis` builds Lemma 4's telescoping functions
(`L_0 = Y_0, L_j = Y_j − Y_{j-1}, L_k = 1 − Y_{k-1}`, `Σ L_j = 1`).

Why this matters: Theorem 1 (`f(ΣL_jw_j) − ΣL_jf(w_j) ∈ I`) is exactly the
statement that folding deviations collapse into the ideal — it is why
PGL-Fold's verifier needs only the K-quotients and a degree check instead
of re-evaluating the degree-d map.  The security lesson from the PROV
attack (`docs/papers/salsa_probe.md`): Gröbner *division* here is a sound
verifier-side tool; Gröbner *elimination* is what breaks under-designed
systems.

### 6. `core/transcript.py` — Fiat-Shamir

A SHA3-256 duplex with domain separation labels per sub-protocol,
length-prefixed canonical absorption (bytes/ints/ring elements/vectors),
counter-based challenge derivation with rejection sampling
(`challenge_int_mod`, expected ≤ 2 draws), and `fork()` for deterministic
rejection loops (HyperWolf's Labrador sampler).  Every protocol's
prover/verifier pair replays the identical absorb/squeeze sequence — the
class of desync bugs caught during bring-up (alpha-draw mismatches) is
structurally prevented by replaying challenge *derivations* on both sides.

### 7. `core/commitment.py` — Ajtai / Module-SIS

Seeded (transparent) key expansion `A ∈ R_q^{m×k}` via a SHA3 PRG;
`commit(w) = A·w mod q` binding under Module-SIS for short `w`; the
`Gadget` class provides base-b digit decompositions (`G·G^{-1} = id`) for
range proofs; HyperWolf carries its own balanced-digit variant (the
carry-rebalance algorithm — the greedy signed-digit recursion fails on ~3%
of negative integers, an implementation note worth keeping).

### 8. `core/serialization.py`

Canonical per-coefficient encodings (full-width and small signed-digit),
`length_prefixed` framing, and the size models used by the benchmark
harness (`n_ring_elts × ring dim × coefficient width`).

---

## Part II — The Protocol Modules

### HyperWolf (7.12) — `protocols/hyperwolf.py` — the deepest module

The paper's three protocols, transcribed figure-by-figure:

**Protocol 2 (commit).**  `f ∈ Z_q^N` → ring-pack `d` consecutive
coefficients per ring element → balanced gadget-decompose each element into
`ι` digit layers (component-major: index `t·ι+e` = digit `e` of component
`t`) → parse into the k-dim hypercube `s^(k)` (axes `b × ... × b × bι`) →
per-slice Ajtai commitments with the block-tiled `A^(k) = 1^T ⊗ A`
(computed by block-sums, never materialized) → the outer commitment
`cm_out = B^(k)·G^{-1}_{δt}(stack)`.

**Protocol 1 (the k-round recursive core).**  Each round: the prover sends
`fold^(k-r) ∈ R_q^b` (the Eq.-4 fold: innermost axis contracted with the
conjugated gadget-expanded `a₀_ext` — the §8.4-1 pairing rule, then
intermediate axes with the integer `a_i`, each hitting the current-last
axis), the JL projections `p_i = σ_{-1}(Π^(k-r))·D(s_i) ∈ R_q^{jl_rows}`,
and the slice commitments `c_min,i`.  The verifier checks: (1)
`⟨fold, a_{k-r-1}⟩ = y` (ct at round 0, ring-exact after — the
multilinearity identity is exact); (2) the JL norm bound
`Σ_j ct(p_{ij})² ≤ (jl_rows/2)·β²`; (3) the outer binding
(`B^(k)·G^{-1}(stack)` at round 0, the statement-chain form after);
(4) cross-round projection consistency `Σ_j C_jp_j^{prev} = Σ_i p_i`.
Challenges: Labrador-distribution ring elements (23 zeros / 31 ±1 / 10 ±2
scaled to the ring dimension) with operator-norm rejection via SVD of the
negacyclic Toeplitz matrix — deterministic under Fiat-Shamir with retry
counters absorbed.  The final round reveals `s^(1)` and pins everything:
`⟨conj(a₀_ext), s^(1)⟩ = y`, `‖s^(1)‖ ≤ β^{(0)}`,
`σ_{-1}(Π)s^(1) = Σ C_ip_i`, `A·s^(1) = Σ C_it_i`.

**Protocol 3 (eval).**  The a-vector builders: univariate
`a_i = (1, u^{b^i·d}, ...)` (the stride includes the ring-packing factor d
— an easy silent bug the bring-up caught), multilinear
`a₀ = eq-product over the first log2(bd) variables with X₀ in the LOW
bits`, one variable per outer axis.  `paper_params()` reproduces the
concrete instantiation; the size model reproduces Table 2 within 1%
(81.2 vs 80.28 KB at N=2^15).

### RoKoko (7.13) — `protocols/rokoko.py`

The committed-refinement pipeline.  **COM (Fig. 1)**: the recursive Ajtai
commitment — level-0 commits `w`, the output is gadget-decomposed,
zero-padded to `minpowtwo`, and re-committed recursively; binding breaks
unroll to SIS (Lemma 4).  **Ξ^lin_COM**: `F_iW = H_iY_i` with COM-opened
`Y_i` — `W` implicitly committed through the vSIS key `F_0`.
**Π^fold-split (Fig. 4)**: challenge-fold the r columns, gadget-decompose,
pack everything into `ŵ` with the decreasing-dimension sort + zero-pad
(Lemma 3's prefix-restricted MLEs), re-commit, send `(com, v)` with `v =
⟨ŵ, ŵ̄⟩`; the verifier checks `ct(v) ≤ β̃²` (Remark 3's power-of-two
shortcut — the constant term IS the squared norm).  **sumcheckify
(Fig. 5/§6.2)**: every constraint becomes a difference of inner products
over the packed vector — public tables carry the prefix selectors —
encoded as product claims.  **Π^lin (Fig. 6)**: batch all claims with
`eq(bin(i), γ)` combiners (explicit RingSC alphas), one degree-2 sumcheck,
terminal identity with z₀/z₁ substitution for the private slots.  The
driver closes with a direct terminal opening (commitment binding, exact
norm, every constraint against the revealed packed vector).

### SALSAA (7.11 A1–A5) — `protocols/salsaa.py`

A1: Π_sum/Π_batch on RingSC.  A2: Π_norm+ (the O(m) conjugate inner
product + trace check + degree-2 sumcheck + Π_mle row appends).
A3: Π_bin (`t = ⟨w, 1°−w⟩`, `Tr(t)=0` ⟺ binary by Lemma 4.11's
orthogonality) and the staircase RoK (Fig. 6): the block-bidiagonal system
`AW₀=Y₀; BW_{j-1}+AW_j=0; BW_{K-1}=Y₁` batched into ONE degree-3 claim
`Σ_z MLE[p](z_step)·MLE[d](z_inner)·MLE[W](z) = s` with the geometric
powers `p_j = (c^{m̄})^j` and the batched row
`d = Σ_ρ c^ρA_ρ + c^{m̄+ρ}B_ρ`.  A4: the VDF as a binary staircase
(`w_i = G^{-1}(−y_i)`, `y_{i+1} = Aw_i` — the [G;A] stacked system with
binary witnesses).  A5: Π_air (Fig. 7) — `V = [W, shift(W)]`, the
transition claim with the `(1−eq(z,1))` wrap-drop, the shift claim with
the `(θ^m−1)eq(z,1)` correction (Eq. 6: `θ·θ̃ − (θ^m−1)eq(z,1) =
MLE[(θ,...,θ^{m-1},1)]`), boundary selectors — plus the folding step.

### ProtogaLattice (7.4 P0-1..P0-5) — `protocols/protogalattice.py`

The algebraic folding core on top of `core/groebner.py`.  **PGL-Fold
(Fig. 2)**: `δ ← C` with the δ-vector `(δ, δ², ..., δ^n)`; `F(X) =
Σ_i (β_i + Xδ^i)f_i(w₀)` affine in X; `α ← C`, `β*_i = β_i + αδ^i`;
`H(Y) = Σ_i β*_i f_i(Σ_jL_j(Y)w_j)`; the Gröbner division
`H − F(α) = Σ K_{rs}Z_{rs}` (Theorem 1 guarantees membership in I; the
remainder must vanish — asserted, and it does for same-statement inputs);
degree-checked K's; the L-basis fold at fresh challenges; the error
accumulator `e* = ΣK(y)Z(y) + F(α)`.  **PGL-Boot (Fig. 3)**: base-b
decomposition with recomposition, per-digit errors, the same Gröbner
reduction against `Σ L_je_j`, the D-tuple checks (`Σb^jt_j = t`,
`Σb^je_j = e + ΣZ(D)K(D)` with `L_j(D) = b^j`), norm re-anchoring —
unbounded fold-after-boot composition demonstrated in the tests.

### The ten core-mechanism modules

- **LatticeFold+** — Construction 5.1 fold + cross-term tracking + the
  norm-check and range-check (pay-per-bit digit) instantiations of the
  §5.0 sumcheck layer.
- **LaBinius** — GF(2^k) tower arithmetic, φ-packing, the MLE-opening
  sumcheck (Π_left-exp/Π_fold collapse).
- **Akita** — two-tier tensor commitment, one row-folding round, JL-style
  norm bounds (the paper's full compression pipeline is in the gap ledger).
- **Twist & Shout** — the one-hot encoding check (Booleanity + Hamming),
  the d=1 Shout lookup sumcheck, the batched Twist read-check.
- **Cyclo** — the fold with the PARTIAL range check (high bits by digits,
  low residual into the norm sumcheck).
- **PikkuFold** — the layered random projection stack with the short final
  image.
- **Quasar** — the multi-cast union polynomial + the γ-ladder accumulation
  fold.
- **Serval** — the split-and-fold IPA with the quadratic cross-term quartet
  `(L, M1, M2, R)` and exact-norm bookkeeping
  `t' = c²L + cc'M1 + c'cM2 + c'²R`.
- **Symphony** — arity-4 folding accumulation, black-box composition.
- **Hachi** — the HMZ ring-switch structure as the norm sumcheck with
  extension-slot evaluation claims.

---

## Part III — Cross-Cutting Invariants

1. **Wraparound-freeness.**  Every integer claim certified mod q (trace
   checks, norm bounds) lives in the regime `value < q/2`; the labs pick q
   accordingly (the q=12289 suite for small norms, Goldilocks elsewhere —
   the negative-trace bug in the bring-up was exactly this regime
   violated).
2. **Transcript determinism.**  Prover and verifier replay identical
   absorb/squeeze sequences; all rejection loops (Labrador, mod-q) carry
   retry counters into the transcript.
3. **Commutator bookkeeping.**  `conj` appears in exactly the places the
   papers put it (norm claims, RoKoko's Hermitian self-inner product);
   linear claims use plain bilinear pairings.
4. **Beta conventions.**  `β` bounds the *flattened coefficient ℓ2 norm*;
   the trace checks compare `n·‖·‖²` against `n·β²`; ladders grow by
   `√(2T)` per fold (conservative).
5. **Terminal responsibility.**  Engines verify rounds; protocols own their
   final openings — the LF+ §5.0 contract.

## Part IV — Data Flow of a Proof (worked example: HyperWolf)

```
f ∈ Z_q^N
  │ ring-pack (d per element)
  ▼
f ∈ R_q^{b^k}  ──gadget──▶  s ∈ R_q^{b^k·ι}  ──reshape──▶  s^(k) hypercube
  │                                                              │
  │                              slice + block-sum matvec (A^(k))│
  ▼                                                              ▼
c_min,i^{(k-1)} per slice ◀────────────────────────── A^(k)·D(s_i)
  │ stack + G^{-1}_{δt} + B^(k) matvec
  ▼
cm_out ── statement ──▶ round loop r = 0..k-2:
     P: fold^(k-r) (Eq. 4 engine), p_i = σ_{-1}(Π^(k-r))D(s_i), c_min,i
     V: eval identity, JL bound, outer binding, projection consistency
     both: y ← ⟨fold,C⟩, cm_out ← B G^{-1}(ΣC_i c_min,i); s ← ΣC_i s_i
  ▼
final: reveal s^(1); four closing checks (eval, norm, Π-consistency, A·s^(1))
```

## Part V — Test & Benchmark Architecture

- `tests/` — 8 pytest modules migrated from the bring-up scripts:
  core (ring/sumcheck/RingSC) + one per priority protocol + the combined
  suite for the ten core modules.  Every protocol module has an
  honest-completeness test AND at least one tamper/attack rejection test.
- `benchmarks/run_benchmarks.py` — wall-clock per protocol + the HyperWolf
  paper-parameter size model; `--quick` for CI.
- `scripts/` — the original bring-up scripts (kept as reproducible
  artifacts; the tests are their AST-normalized migrations).

## Part VI — What This Is Not

Not audited, not constant-time, not full-security-parameterized.  It is a
protocol-mechanics lab: every figure transcribed, every invariant
exercised, every simplification written down in the per-paper gap ledger.
