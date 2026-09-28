# SALSAA — Deep Analysis & Implementation Spec

> Spec for the lab's SALSAA implementation items **A1–A5** (see `/home/z/my-project/worklog.md`).
> A1 = Π_sum + Π_batch core; A2 = Π_norm+ (norm RoK, O(m) prover); A3 = Π_bin+ + staircase RoK;
> A4 = VDF application (Papercraft blueprint, G^{-1}/A chain, staircase + binary relations);
> A5 = committed-AIR folding (§7 incl. §7.4) + parameters (§8).
> Written from a full read of the paper text (`/tmp/sq/salsaa.txt`, squeezed from ePrint 2025/2124, 3543 orig. lines).

---

## 1 Metadata

| Field | Value |
|---|---|
| Title | SALSAA: Sumcheck-Aided Lattice-based Succinct Arguments and Applications |
| Authors | Shuto Kuriyama, Russell W. F. Lai, Michał Osadnik, Lorenzo Tucci |
| Affiliation | Aalto University, Espoo, Finland |
| Publication | IACR ePrint 2025/2124 |
| Domain | Lattice-based fully-succinct arguments (post-quantum SNARKs, PCS, folding, VDF) |
| Builds on | RPS = "RoK, paper, SISsors" [KLNO24, ASIACRYPT'24]; RnR = "RoK and Roll" [KLNO25, ASIACRYPT'25]; CLM23; sumcheck [LFKN90]; Papercraft VDF [OKC+25] |
| Subsequent work | RoKoko [KLN+26] — alternates generalised Ξ^{lin-⊗}/Ξ^sum per round; trades slightly slower verification for smaller proofs & faster prover; SALSAA's application-interfacing layer is transferable to it |
| Core idea | Integrate the sumcheck protocol **as a first-class relation (Ξ^sum)** into the RPS/RnR RoK toolkit, run **over cyclotomic ring elements** (not coefficients), transcript batched across CRT/NTT slots |
| Headline results | (i) norm-check RoK with O_λ(m)-time prover (drop-in for RPS's O_λ(m log m)); improved batching RoK that also cuts prover time; SNARK for Ξ^{lin-⊗} + PCS with ½ proof size of RPS, verification < 7 ms for witnesses up to 2^30 Zq elements (5.64 ms @ 2^28); (ii) binariness + staircase RoKs → lattice VDF verifying in ~10 ms (2–3 orders of magnitude below the delay), prover = constant multiple of delay; (iii) folding scheme for bounded-ℓ2-norm semi-structured Ξ^{lin-}: < 0.5 ms verify / ~60 KB per step, independent of witness size; (iv) AIR RoK → SNARK & folding for AIR |
| Implementation | Modular implementation of (i)–(iii) in one codebase, AVX-512-accelerated cyclotomic ring arithmetic (paper §8); the AIR compositions (SNARK/folding for AIR) are constructed but not implemented in the paper |
| Security assumption | vSIS (row-tensor/structured SIS) for Ξ^{lin-⊗}; SIS for the semi-structured Ξ^{lin-} variant (unstructured commitment key) |
| Paper structure | §1 Intro, §2 Technical Overview, §3 Preliminaries, §4 Sumcheck-aided RoKs (Π_mle 4.1, Π_sum 4.2, Π_batch 4.3, Π_norm+ 4.4, Π_bin+ 4.5, Π_+ staircase 4.6, Π_air+ 4.7), §5 SNARK/PCS, §6 VDF, §7 Folding (incl. 7.4 AIR folding), §8 Implementation & benchmarks, appendices |

**Reduction pipeline (the whole paper in one line):**

```
{ Ξ^lin-⊗, Ξ^bin, Ξ^staircase, Ξ^com-air }  --Π_*-->  Ξ^sum  --Π_sum-->  Ξ^mle  --Π_mle-->  Ξ^lin-⊗
```

Each application-level RoK (norm, binariness, staircase, AIR) is just a different way of *encoding its
constraint as sumcheck claims attached to the same committed bounded-norm witness*; the last two steps
(Π_sum → Ξ^mle → Ξ^lin-⊗) are shared by all of them. This is the key architectural fact for the
implementation: build Π_sum/Π_mle once (A1), then layer A2/A3/A4/A5 as thin wrappers producing sumcheck claims.

**Why sumcheck over ring elements (not coefficients):** a coefficient-wise sumcheck [BC25a, NS25, GLLO26]
needs a large modulus or extension field; running each sumcheck round directly over Rq and batching the
transcript across the φ/e CRT (NTT) slots gives comparable communication with concrete efficiency
(observed in [BC25b]).

---

## 2 Notation Table

*(every symbol of the paper, in rough order of appearance — §3.x gives context)*

| Symbol | Meaning |
|---|---|
| λ | security parameter (assumed included in unary in every pp) |
| N | natural numbers {1, 2, …} |
| [n] | {0, …, n−1} (counting from **0**) |
| [m:n] | [n] \ [m] = {m, …, n−1} |
| (i,j,k) ∈ [n,m,ℓ] | multidimensional range: i∈[n], j∈[m], k∈[ℓ] |
| Zq (balanced) | {−⌈q/2⌉+1, …, ⌊q/2⌋}; comparisons like Trace(x) ≤ β² are over Z in this rep |
| **v**, **M** | bold lower-case = vector, bold upper-case = matrix |
| (M_i)_{i∈[k]} | horizontal concatenation of matrices/vectors M_0,…,M_{k−1} |
| K = Q(ζ) | cyclotomic field, ζ a root of unity of order f (the conductor) |
| f | conductor of the cyclotomic field |
| φ = φ(f) | degree of K = Euler totient; number of coefficients of a ring element |
| R = O_K = Z[ζ] | ring of integers of K |
| q | modulus, always **prime**, q ∤ f |
| Rq := R/qR | quotient ring; arithmetic happens here |
| R×, R×_q | unit groups of R and Rq |
| cf / cf_b : K → Q^φ | coefficient embedding w.r.t. Z-basis b = (b_i)_{i∈[φ]}; cf_b(x) = (x_i) if x = Σ x_i b_i; extended to vectors by concatenation |
| σ : K → C^φ | canonical embedding; σ(x) = (σ_j(x))_{j∈[φ]}, σ_j ∈ Gal(K/Q) |
| ‖x‖_{σ,p} | ℓp norm of x under σ, i.e. ‖σ(x)‖_p (vectors: concatenation) |
| ‖M‖_{σ,p} | for M ∈ R^{m×n}: max over **columns** m_i of ‖m_i‖_{σ,p} |
| ⟨·,·⟩ | inner product; ‖x‖²_{σ,2} = Trace(⟨x, x⟩); bar = complex conjugation |
| Trace_{M/L} | field trace of Galois extension M/L; Trace = Trace_{M/Q} |
| Trace : Rq → Zq | trace descends mod q (Trace(R) ⊆ Z, Trace(qR) ⊆ qZ); "Trace(x)" means its **balanced** representative in Z |
| e | multiplicative order of q mod f = residue degree of q in R |
| φ/e | number of CRT components |
| CRT : Rq → (F_{q^e})^{φ/e} | ring splitting isomorphism (and inverse CRT^{-1}); generalised to vectors (concatenation) and to polynomials Rq^r[x^µ] → F_{q^e}^r[x^µ] coefficient-wise |
| (Rq^r, +, ⊙) | coordinate ring of vectors in Rq^r (⊙ = coordinate-wise multiplication) |
| Rq[x^µ], Rq[z]_{≤δ} | polynomial ring over Rq^r / multivariate polynomials over Rq with individual degree ≤ δ |
| staircase matrix | for A, B ∈ Rq^{n̄×m̄}: the (T+1)-block-bidiagonal matrix in Rq^{(T+1)n̄ × Tm̄} with A on the diagonal blocks and B on the subdiagonal blocks (§4.6) |
| b | gadget base (b > 1) |
| k := ⌈log_b β⌉ + 2 | gadget digit count |
| g = [1, b, …, b^{k−1}]^T ∈ Z^k | gadget vector |
| G_{b,m,k} := I_m ⊗ g^T ∈ Z^{m×mk} | gadget matrix; G_b, G_b^{-1} when dims clear |
| G^{-1}_{b,m,k} : R^{m×r} → Rq^{mk×r} | deterministic digit-decomposition s.t. G_{b,m,k} G^{-1}_{b,m,k}(W) = W |
| m = 2^µ | witness height = number of MLE hypercube points (τ = 2 columns per tensor factor) |
| µ | number of multilinear variables = tensor depth |
| MLE[w](z) := w · e_z ∈ Rq[z] | multilinear extension of w ∈ Rq^{2^µ}; unique multilinear poly agreeing with w on the hypercube |
| e_z := ⊗_{j∈[µ]} (1−z_j, z_j)^T | tensor indicator vector; {0,1}^µ identified with [2^µ] **MSB first** |
| eq(x, z) := Π_{i∈[µ]} (x_i·z_i + (1−x_i)(1−z_i)) | equality polynomial; 1 iff x = z ∈ {0,1}^µ |
| r̄, w̄, MLE[w̄] | conjugates (used by the norm claim) |
| 1° ∈ R | ring element with all-ones coefficients (used by binariness claim) |
| t | number of MLE evaluation claims (cols of trace register matrix in AIR: W ∈ R^{m×t}) |
| r | witness column count (W ∈ R^{m×r}) |
| n̂ | number of rows of H (output/instance rows) |
| n, n̄, n_ | rows of F; n = n̄ + n_; top part F̄ (commitment-key rows, n̄ rows) and bottom part F_ (constraint rows) |
| n_com | rows of the commitment key F_com ∈ Rq^{n_com×m} (top rows of F̄) |
| β | norm bound of the (honest) witness |
| β′ | relaxed norm bound, 0 < β ≤ β′ |
| β_sis | SIS norm bound for the assumption/extractor |
| δ_h | total degree bound of sumcheck claim polynomial f (h = "high" degree; 2 for norm/bin) |
| δ(pp, stmt) | correctness error of a RoK (0 if omitted) |
| κ(pp, stmt) | knowledge error of a RoK |
| Ξ^{lin-⊗}_{n̂,n,µ,r,β} | principal structured linear relation (Def 3.2): H ∈ Rq^{n̂×n}, F ∈ Rq^{n×m}, Y ∈ Rq^{n̂×r}, W ∈ Rq^{m×r}, ‖W‖_{σ,2} ≤ β, HFW = Y mod q; H = [I_n; H̄]; F row-tensor F = F_0 • … • F_{µ−1} |
| Ξ^{lin-} | same but top rows F̄ of F **unstructured** (semi-structured; unstructured commitment keys); F_ still row-tensor |
| Ξ^{sis}_{n_com,m,β_sis} | SIS-break relation (Def 3.3): F_com x = 0 mod q ∧ 0 < ‖x‖_{σ,2} ≤ β_sis |
| Ξ^{mle-⊗}_{n̂,n,µ,r,β,t} | MLE relation (Def 4.1): Ξ^{lin-⊗} ∧ (r_i, s_i)_{i∈[t]} ∈ (Rq^µ × Rq)^t ∧ ∀i: s_i = MLE[W](r_i) mod q (column-wise MLE for r > 1) |
| Ξ^{sum} | sumcheck relation (§4.2): Ξ^{lin} + list of claims Σ_{z∈{0,1}^µ} f(MLE[W], MLE[W̄])(z) = s mod q (captures Ξ^{sum-⊗} and Ξ^{sum-}) |
| Ξ^{bin} | binariness relation: cf(w) ∈ {0,1}^{φm} (§4.5) |
| Ξ^{com-air} | committed-AIR relation (§4.7) |
| • | row-wise Kronecker (row-tensor) product: F = F_0 • … • F_{µ−1}, F_j ∈ Rq^{n×τ} |
| Rq^{n×τ^µ} | shorthand for row-tensor structured matrices with µ factors |
| ⊗ | ordinary Kronecker product (e.g. G_{b,m,k} = I_m ⊗ g^T); also tensor of vectors e_z |
| Π_mle, Π_sum, Π_batch, Π_norm+, Π_bin+, Π_+, Π_air+ | the paper's RoKs (§4.1–4.7); "+" marks improved versions vs RPS/Papercraft |
| Π_fold, Π_fs, Π_as | folding RoK (inherited), folding scheme, argument system (§5, §7) |
| RoK | reduction of knowledge (Def 3.8): P/V interactively map instance (stmt0, wit0) → (stmt1, wit1) |
| Ξ_a → Ξ_b | completeness direction (L→R); Ξ_a ← Ξ_b = extraction direction (R→L), e.g. Ξ^{sis} ∪ Ξ^{lin} ← Ξ^{lin} |
| SIS^{sis}_{R,q,m,n,β} / SIS^{inf} / vSIS | SIS variants (Defs 3.5–3.7): inf-SIS bounds ‖cf(w)‖_∞; vSIS uses row-tensor A = A_0 • … • A_{µ−1}, A_j ∈ Rq^{n×2}, 2^µ = m |
| O_λ(·) | hides poly(λ) factors |
| shift(W) | row shift: moves every row of W up by one, wraps first row to bottom (AIR, Fig. 1) |
| V = [W, shift(W)] | committed AIR witness ∈ R^{m×2t} |
| p, d, c | staircase batching: geometric powers vector p, batched row d := Σ_ρ c^ρ A_{ρ,:} + c^{m̄+ρ} B_{ρ,:}, challenge c |
| A, B | staircase blocks ∈ Rq^{m̄×n̄} (m̄ rows each; K = m/n̄ blocks of witness) |
| r_out | output dimension of the sumcheck function h (number of claims bundled in one Ξ^sum instance) |
| h ∈ ((Rq[x^µ])[y^{2r}])^{r_out} | sumcheck function: vector of r_out polys in 2r "y" variables, coefficients in Rq[x^µ]; h(ν_0,…,ν_{2r−1}) = coordinate-wise evaluation |
| f0 := MLE[W], f1 := MLE[W̄] | the two multilinear inputs of h (W̄ = entrywise complex conjugate) |
| f̃ := u^T · CRT(h(f0, f1)) | CRT-slot-batched sumcheck polynomial ∈ F_{q^e}[x^µ] (the polynomial the sumcheck actually runs on) |
| u ←$ F_{q^e}, u^T = (u_i)_{i∈[r_out·φ/e]} | verifier's random batching vector over CRT slots |
| g_i(x) ∈ F_{q^e}[x] | round-i univariate message of the sumcheck, degree ≤ δ̂_h |
| a_i | running claimed partial sum after round i; a_0 := u^T·CRT(s) |
| r_{<i} := (r_0,…,r_{i−1}) | prefix of sumcheck challenges |
| r ∈ Rq^µ | final lifted challenge: r = (CRT^{-1}(1_{φ/e}·r_i))_{i∈[µ]}; r̄ its conjugate; claims (r, v0), (r̄, v1) |
| v0, v1 ∈ Rq^r | final evaluations: v0 = MLE[W](r), v1 = MLE[W̄](r) = MLE[W](r̄) |
| δ̂_h | bound on **individual** degrees of (h_i)_{i∈[r_out]} (round messages have degree ≤ δ̂_h; e.g. 2 for norm/bin/batch) |
| c ←$ Rq | batching challenge; c := (1, c, …, c^{n̂−n})^T powers vector for Π_batch / staircase |
| s | sumcheck target value(s); also staircase batched RHS |
| p | staircase geometric-powers vector (powers of c per block) |
| d | staircase batched row d := Σ_{ρ} c^ρ A_{ρ,:} + c^{m̄+ρ} B_{ρ,:} ∈ Rq^{n̄} |
| K | staircase block count: K := m/n̄ (n = K·n̄; K and n powers of 2) |
| t (vector) | per-column claimed value of a sumcheck: t = (⟨w_i, w_i⟩)_{i∈[r]} (norm) or (⟨w_i, 1°−w_i⟩)_{i∈[r]} (binariness) |
| Π^{klno24}_{norm}, Π^{klno24}_{batch} | the old RPS/RnR norm-check / lazy-batching RoKs that SALSAA improves on |
| T (VDF context) | delay-function time parameter; VDF witness = T staircase blocks (m·T = 2^µ); do not confuse with the staircase block count K |
| σ, σ′, p(λ) | sequentiality bound; SIS-Seq sequentiality parameter; depth-preserving polynomial slack (Lemma 6.7) |
| ϵ | VDF correctness error (gadget-decomposition failure union bound) |
| SIS-Seq_{R,q,m,n,σ} | timed SIS assumption (Def 6.5): no low-depth adversary solves the stacked binary staircase |
| str, Ξ\|s, Ξ_acc, Ξ_break | folding: structure map (returns commitment key F), structure-restricted sub-relation, accumulator relation, break relation (Def 7.1/7.2/7.4) |
| r_acc = 2^ℓ, γ, m_rp, β̂ | folding accumulator column count; Π_fold challenge-set expansion factor; random-projection dimension O(λ); projection norm bound β̂ = √(m_rp)·β |
| #Zq | benchmark witness-size unit = number of Zq coefficients (m·φ) |
| incomplete-rexl | authors' Rust library for almost-splitting cyclotomic ring arithmetic (Intel HEXL subset, AVX-512) |

---

## 3 Algebraic Setting

### 3.1 Rings, embeddings, norms

- **Cyclotomic field and ring.** K = Q(ζ), ζ a root of unity of order f (the *conductor*), degree φ = φ(f)
  (Euler totient). Ring of integers R = O_K = Z[ζ]. Modulus q ∈ N is **always prime** and q ∤ f.
  All protocol arithmetic happens in Rq := R/qR. For power-of-two cyclotomics (the binariness case,
  §5.5): f = 2^k, φ = f/2, minimal polynomial of ζ is X^φ + 1, i.e. R = Z[x]/(x^φ + 1) — exactly the
  `lzk` ring Z_q[x]/(x^n + 1).
- **Embeddings.** For a Z-basis b = (b_i)_{i∈[φ]} of R and x = Σ x_i b_i:
  - coefficient embedding `cf_b(x) := (x_i)_{i∈[φ]}` (K → Q^φ; extended to vectors/matrices by concatenation);
  - canonical embedding `σ(x) := (σ_j(x))_{j∈[φ]}`, σ_j ∈ Gal(K/Q) (K → C^φ).
- **Norms.** For x ∈ R^m: ‖x‖_{σ,p} := ‖σ(x)‖_p. For M ∈ R^{m×n}: ‖M‖_{σ,p} := max over **columns**.
  Key identity: ‖x‖²_{σ,2} = Trace(⟨x, x⟩) where ⟨·,·⟩ is the *conjugate* inner product
  (⟨w, v⟩ = Σ_j w̄_j v_j — note w̄ = entrywise complex conjugate = coefficient-negation map for
  power-of-two cyclotomics: x ↦ x(x^{... }) i.e. ζ^i ↦ ζ^{−i}).
- **Trace.** Trace_{M/L}(x) := Σ_{σ_j ∈ Gal(K/L)} σ_j(x); Trace := Trace_{M/Q}. Since Trace(R) ⊆ Z and
  Trace(qR) ⊆ qZ, the trace descends to Trace : Rq → Zq; in the protocols "Trace(x)" always means the
  **balanced representative** in {−⌈q/2⌉+1, …, ⌊q/2⌋}, so integer comparisons (Trace(t) ≤ β²,
  Trace(t) = 0) are meaningful.
- **Coefficient–trace link (power-of-two only), Lemma 4.11.** For R = Z[ζ_f], f = 2^k, φ = f/2 and
  w, v ∈ R: ⟨cf(w), cf(v)⟩ = Trace(w·v)/φ. (Proof: Trace(ζ^0) = φ, Trace(ζ^ℓ) = 0 for 0 < |ℓ| < φ.)
  Consequence: ‖cf(w)‖² = ‖w‖²_{σ,2}/φ, and generally ‖cf(·)‖₂ ≤ sqrt(rad(f)/f)·‖·‖_{σ,2}
  (Lemma 2 of [KLNO25]).

### 3.2 CRT splitting / NTT slots (the batching substrate)

- e := multiplicative order of q mod f = residue degree of q in R. Rq ≅ (F_{q^e})^{φ/e}
  ("e splits into φ/e slots").
- CRT : Rq → (F_{q^e})^{φ/e} and CRT^{-1} backwards; extended to vectors (entrywise concatenation) and
  to polynomials Rq^r[x^µ] → F_{q^e}^r[x^µ] (coefficient-wise).
- This is the **NTT** of the `lzk` engine: φ/e independent F_{q^e} slots when e > 1 (for e = 1: φ slots
  of F_q, the fully-split case). SALSAA's sumcheck messages g_i(x) live in F_{q^e}[x]; the "lift"
  CRT^{-1}(1_{φ/e}·r_i) (all slots set to r_i) maps a field challenge back into Rq.
- Coordinate ring (Rq^r, +, ⊙): vectors with coordinate-wise multiplication ⊙ — this is how a sumcheck
  function h acts on r-column witnesses (h is r_out-dimensional, applied coordinate-wise to its 2r
  arguments).

### 3.3 Tensor structure (row-tensor matrices)

- A matrix F ∈ Rq^{n×m} is **row-tensor structured** if F = F_0 • F_1 • … • F_{µ−1} where each
  F_j ∈ Rq^{n×τ} and • is the *row-wise Kronecker product*: row i of F is the ⊗ of rows of the factors.
  Shorthand: F ∈ Rq^{n×τ^µ}. SALSAA assumes **τ = 2**, so m = 2^µ = witness height = MLE hypercube size.
- Split of F (vertical): F = [F̄ ; F_] with top part F̄ ∈ Rq^{n̄×m} (the vSIS **commitment key**
  F_com ∈ Rq^{n_com×m} sits at the top of F̄) and bottom part F_ ∈ Rq^{n_×m} (application constraints).
  n = n̄ + n_.
- The MLE evaluation trick that bridges tensor structure ↔ sumcheck: for a row-tensor row
  f_j^T = ⊗_k f_{j,k}^T, evaluating at e_r := ⊗_{k∈[µ]} (1−r_k, r_k)^T costs O(µ) by the
  mixed-product property — this is why the verifier stays polylog even though it evaluates
  MLE[(c^T H̄F)^T](r).
- A vSIS commitment is Com(W) = F̄·W with row-tensor F̄; binding of that top block is the vSIS
  assumption. `lzk` Ajtai commitments over Z_q[x]/(x^n+1) with tensor keys implement this directly.

### 3.4 Standing parameters (Setting 3.4)

- m := 2^µ = poly(λ) (witness height);
- 0 < β ≤ β′ (honest vs relaxed norm bound) and **4β′² < q** — this inequality is what makes every
  "read the integer off the residue mod q" argument (norm Trace(t) ≤ β², binariness Trace(t) = 0)
  wrap-around-free;
- q^e = ω(poly(λ)) (superpolynomial residue field ⇒ Schwartz–Zippel over F_{q^e} is meaningful).

### 3.5 Gadgets and the staircase matrix

- **Gadget decomposition.** b > 1, k := ⌈log_b β⌉ + 2, g = [1, b, …, b^{k−1}]^T ∈ Z^k,
  G_{b,m,k} := I_m ⊗ g^T ∈ Z^{m×mk}, and G^{-1}_{b,m,k} : R^{m×r} → Rq^{mk×r} the deterministic
  base-b digit expansion with G·G^{-1}(W) = W. Used by the VDF chain (§6 of this doc) and for
  norm management in folding.
- **Staircase matrix** (§3.1 of paper): for A, B ∈ Rq^{n̄×m̄}, the block-bidiagonal matrix
  `[A; B]_K`-style object in Rq^{(K+1)n̄ × Km̄}: A on the diagonal blocks, B on the subdiagonal
  blocks, everything else 0. Constraints `[A;B]·W = [Y₀; 0; …; 0; Y₁]` express "each block of W is
  tied to the next block through B, and anchored by A at both ends" — i.e. a repeated-computation
  trace.

### 3.6 SIS assumptions (Defs 3.5–3.7)

| Name | Adversary sees | Must find | Bound |
|---|---|---|---|
| SIS^{sis}_{R,q,m,n,β} | A ←$ Rq^{n×m} | x: Ax = 0 mod q, 0 < ‖cf_b(x)‖ ≤ β_sis | coefficient norm (ℓ2 over cf_b) |
| inf-SIS | A ←$ Rq^{n×m} | x: Ax = 0 mod q, ‖cf(w)‖_∞ ≤ β_sis | coefficient ∞-norm |
| vSIS | A = A_0 • … • A_{µ−1}, A_j ∈ Rq^{n×2}, 2^µ = m | x: Ax = 0 mod q | row-tensor (structured) key |

vSIS hardness ~ SIS on the much smaller seed (n×2µ structured ⇒ m·φ coefficients of entropy in n·2·φ);
this is what makes the tensor commitment key compressible and the verifier polylog. The extraction
statements of every RoK in §5 route a cheating prover either to a witness of the target relation or to
a vSIS solution with norm ≤ 2β′ over 2µ coordinates (two accepting transcripts with witnesses
W ≠ W′ give a non-zero column of W − W′ with F·(W−W′) = 0).

### 3.7 Reductions of knowledge (Def 3.8)

A RoK Π = (P, V):
- P(pp, stmt₀, wit₀) → (stmt₁, wit₁) or ⊥ — interactive instance mapping;
- V(pp, stmt₀) → stmt₁ — interactive statement mapping.

Π is **correct** for Ξ₀ → Ξ₁ with error δ if honest P maps Ξ₀ instances into Ξ₁ instances (δ = 0 when
omitted). Π is **knowledge sound** for Ξ₀′ ← Ξ₁′ with error κ if a black-box expected-PPT extractor E
produces a Ξ₀′ witness whenever P* produces an accepting Ξ₁′ instance, losing only κ.
**Depth-preserving** knowledge soundness: Depth(E) ≤ Depth(P*) + poly(λ) (needed for FS/IVC chaining).

Arrow convention (Remark on §3.3 of paper): `Ξ_in → Ξ_out` = completeness direction (left-to-right);
`Ξ_ext ← Ξ_out` = extraction direction (right-to-left). A statement like
`Ξ^{sis} ∪ Ξ^{lin} ← Ξ^{lin}` means: from an accepting output instance the extractor yields either a
vSIS break or a witness of the stronger input relation.

---

## 4 Relations (exact definitions)

All relations share the shape "public matrices + bounded-norm witness + equations mod q". Subscripts
dropped when irrelevant. `{lin-⊗}` vs `{lin-}` variants differ *only* in whether the top rows F̄ of F
carry the row-tensor structure.

### 4.1 Ξ^{lin} — structured / semi-structured linear relations (Def 3.2)

$$
Ξ^{\text{lin-}⊗}_{\hat n, n, µ, r, β} = \Big\{ ((H, F, Y), W) :\;
H ∈ R_q^{\hat n × n},\; F ∈ R_q^{n×m},\; Y ∈ R_q^{\hat n × r},\; W ∈ R_q^{m×r},\; ‖W‖_{σ,2} ≤ β,\; HFW = Y \bmod q \Big\}
$$

with:
- H restricted to the form H = [I_n ; H̄] (top n rows = identity — the "output" rows the final
  verifier checks directly);
- F = [F̄ ; F_] (n = n̄ + n_), F̄ = commitment-key rows (top n_com rows are F_com), F_ = constraints;
- F row-tensor: F = F_0 • … • F_{µ−1}, F_j ∈ Rq^{n×2}, τ = 2, m = 2^µ.

**Ξ^{lin-}** (semi-structured): identical except F̄ is **not** required to be row-tensor (unstructured
Ajtai commitment keys — this is the folding variant, §7); F_ keeps the row-tensor structure.

### 4.2 Ξ^{sis} — SIS-break relation (Def 3.3)

$$
Ξ^{\text{sis}}_{n_\text{com}, m, β_\text{sis}} = \Big\{ (F_\text{com}, x) :\;
F_\text{com} ∈ R_q^{n_\text{com}×m},\; x ∈ R^m,\; 0 < ‖x‖_{σ,2} ≤ β_\text{sis},\; F_\text{com}\,x = 0 \bmod q \Big\}
$$

### 4.3 Ξ^{mle} — MLE evaluation relation (Def 4.1)

$$
Ξ^{\text{mle-}⊗}_{\hat n,n,µ,r,β,t} = \Big\{ ((H, F, Y, (r_i, s_i)_{i∈[t]}), W) :\;
((H,F,Y),W) ∈ Ξ^{\text{lin-}⊗},\; (r_i, s_i)_{i∈[t]} ∈ (R_q^µ × R_q)^t,\; ∀i:\; s_i = \mathrm{MLE}[W](r_i) \bmod q \Big\}
$$

(Ξ^{mle-} = same with Ξ^{lin-} underneath. For r > 1 the MLE is column-wise: MLE[W] ∈ Rq^{r}[x^µ].)
The two claims produced by Π_sum are t = 2: (r, v0) for MLE[W] and (r̄, v1), exploiting
MLE[W̄](r) = MLE[W](r̄) (conjugation is a ring automorphism commuting with evaluation).

### 4.4 Ξ^{sum} — the sumcheck relation (Def 4.3) — *the SALSAA interface*

$$
Ξ^{\text{sum-}⊗}_{\hat n,n,µ,r,r_\text{out},β} = \Big\{ ((h, s, H, F, Y), W) :
\begin{array}{l}
((H,F,Y),W) ∈ Ξ^{\text{lin-}⊗} \\
s ∈ R_q^{r_\text{out}},\; h ∈ ((R_q[\mathbf{x}^µ]))^{r_\text{out}}[\mathbf{y}^{2r}] \\
\sum_{z∈\{0,1\}^µ} h(\mathrm{MLE}[W], \mathrm{MLE}[\bar W])(z) = s \bmod q
\end{array} \Big\}
$$

- h = vector of r_out polynomials in 2r variables y (r variables for MLE[W], r for MLE[W̄]),
  **coefficients themselves polynomials in the µ hypercube variables**;
- evaluation h(ν_0, …, ν_{2r−1}) is coordinate-wise, so h(f0, f1) ∈ Rq^{r_out}[x^µ];
- W̄ = complex conjugate of W (entrywise);
- total degree ≤ δ_h, individual degree ≤ δ̂_h of the h_i.

Instances used by the RoKs: norm → h = y0 ⊙ y1 (δ̂_h = 2); binariness → h = y1 ⊙ (1° − y0);
batching → h = MLE[(c^T H̄F)^T] ⊙ y0 (no y1 dependence!); staircase → h = (p ⊗ d)^T-related
weight ⊙ y0; AIR → transition + shift + boundary claims (see §5).

### 4.5 Ξ^{bin} — binariness relation (Def 4.10)

$$
Ξ^{\text{bin}}_{\hat n,n,µ,r,β} = \Big\{ ((H,F,Y), W) ∈ Ξ^{\text{lin}} :\;
∀j∈[m], i∈[r]:\; \mathrm{cf}(w_{j,i}) ∈ \{0,1\}^{φ} \Big\}
$$

Equivalent scalar test (power-of-two cyclotomics only, via Lemma 4.11):
cf(w) ∈ {0,1}^{φm} ⟺ ⟨cf(w), 1 − cf(w)⟩ = 0 ⟺ Trace(⟨w, 1°·1 − w⟩) = 0, where
1° := Σ_{k∈[φ]} ζ^k ∈ R is the all-ones-coefficient ring element.

### 4.6 Ξ^{staircase} — block-bidiagonal relation (Def 4.14)

$$
Ξ^{\text{stair}}_{\bar m, \bar n, \hat n, n, µ, r, β} = \Big\{ ((H, F, Y, A, B, Y_0, Y_1), W) :
\begin{array}{l}
((H,F,Y),W) ∈ Ξ^{\text{lin}}_{\hat n,n,µ,r,β} \\
A, B ∈ R_q^{\bar m × \bar n},\; Y_0, Y_1 ∈ R_q^{\bar m × r} \\
\left[\begin{smallmatrix} A & & & \\ B & A & & \\ & B & A & \\ & & \ddots & \ddots \\ & & & B & A \\ & & & & B \end{smallmatrix}\right]\cdot W
= \left[\begin{smallmatrix} Y_0 \\ 0 \\ \vdots \\ 0 \\ Y_1 \end{smallmatrix}\right] \bmod q
\end{array} \Big\}
$$

i.e. with K := m/n̄ (block count; K and n powers of 2) and W parsed into K row-blocks
W_j ∈ Rq^{n̄×r}:

- A·W_0 = Y_0,
- B·W_{j−1} + A·W_j = 0 for j ∈ [1:K] (= {1,…,K−1}),
- B·W_{K−1} = Y_1.

Decoupling note (vs Papercraft's analogue): the block width n̄ of A, B is **decoupled** from the
tensor structure of the underlying Ξ^{lin} instance — the staircase is expressed as one sumcheck
claim regardless of n̄.

### 4.7 Ξ^{com-air} — committed-AIR relation (§4.7; formal shape from Fig. 7 context)

Witness W ∈ R^{m×t} is the execution **trace** (rows = time steps, columns = registers). The committed
object is V = [W, shift(W)] ∈ R^{m×2t} where shift(W) moves every row up by one and wraps row 0 to the
bottom (Fig. 1). The relation asserts, for a given transition polynomial f of degree d and boundary
conditions:
- ∀i ∈ [m−1]: f(W_{i,:}, W_{i+1,:}) = 0 mod q — imposed row-locally as f(V_{i,:}) = 0 on all rows but
  the last (the cyclic wrap pairs the final trace row with the first one, leaving the last row
  unconstrained by the transition);
- **shift claim**: the second half of V is the shifted copy of the first half;
- **boundary conditions**: fix initial/final states (and is handled by linear constraints on the
  first/last rows of V).

---

## 5 Protocols — full step-by-step transcriptions

> **Reading guide.** Every "+"-protocol has the same anatomy:
> `Π_X+ = Π_batch+ ∘ Π_mle ∘ Π_sum ∘ Π_X` where Π_X is a *local* reduction that only turns a
> constraint into sumcheck claims (communication ≈ 0, work O(1) or O(mr)), Π_sum is the shared
> sumcheck engine (Fig. 2), Π_mle is the free rewriter of evaluation claims into linear rows
> (Lemma 4.2), and Π_batch+ compresses the leftover constraint rows (Cor. 4.7). The A1
> implementation builds Π_sum, Π_mle, Π_batch once; A2/A3/A4/A5 only add new "h functions".
> Dotted lines in the paper's figures denote "no message / local computation".

### 5.1 Π_mle : Ξ^{mle} → Ξ^{lin} (Lemma 4.2) — the free step

On input a Ξ^{mle} instance ((H, F, Y, (r_i, s_i)_{i∈[t]}), W), output the Ξ^{lin} instance
((H′, F′, Y′), W) with

$$
H′ = \begin{bmatrix} H \\ I_t \end{bmatrix},\qquad
F′ = \begin{bmatrix} F \\ (\tilde e_{r_i})_{i∈[t]} \end{bmatrix}^{\!T},\qquad
Y′ = \begin{bmatrix} Y \\ (s_i)_{i∈[t]} \end{bmatrix}^{\!T},
$$

where the appended row for claim i is the tensor indicator $\tilde e_{r_i} = ⊗_{j∈[µ]}(1−r_{i,j},\, r_{i,j})^T$
(a tensor product of µ 2-dimensional vectors ⇒ F′ retains row-tensor structure; for Ξ^{mle-} the
unstructured top rows stay unstructured). Since $\langle \tilde e_{r_i}, W\rangle = \mathrm{MLE}[W](r_i)$,
the new rows encode exactly the t evaluation claims.

- Perfectly correct, knowledge sound with **κ = 0** for Ξ^{mle} ↔ Ξ^{lin}_{n̂+t, n+t, µ, r, β}.
- Communication 0; both parties O(1).
- *Implementation note:* this is pure data plumbing — append rows to (H, F, Y); in the `lzk` tensor
  representation append each 2-column factor pair to every factor F_j (a row appended to a row-tensor
  matrix is appended to each factor and Kronecker'd).

### 5.2 Π_sum : Ξ^{sum} → Ξ^{mle} (Fig. 2, Lemma 4.4) — the sumcheck engine [A1 core]

**Instance:** ((h, s, H, F, Y), W) with h : (Rq[x^µ])^{2r} → (Rq[x^µ])^{r_out}, f0 := MLE[W],
f1 := MLE[W̄], claim Σ_{z∈{0,1}^µ} h(f0, f1)(z) = s mod q. Degrees: total ≤ δ_h, individual ≤ δ̂_h.

**Prover P((h, s, H, F, Y), W):**
1. `f0 := MLE[W] ∈ Rq^r[x^µ]` — the multilinear extension of the witness (never materialised as
   a dense polynomial; keep W and evaluate lazily).
2. `f1 := MLE[W̄] ∈ Rq^r[x^µ]` — extension of the conjugate witness.
3. `f̃ := u^T · CRT(h(f0, f1)) mod q ∈ F_{q^e}[x^µ]` — CRT every coefficient of h(f0,f1) into its
   φ/e NTT slots and random-combine with u.

**Verifier V(h, s, H, F, Y):**
1. `u ←$ F_{q^e}` (one field element; conceptually u^T = (u_i)_{i∈[r_out·φ/e]} broadcasts it over
   slots/components).
2. `a0 := u^T · CRT(s) mod q` — the folded target.
3. Rounds i = 0 … µ−1 (r_{<i} := (r_0,…,r_{i−1}) already fixed):
   - P sends the univariate `g_i(x) ∈ F_{q^e}[x]`, deg ≤ δ̂_h:
     $$g_i(x) := \sum_{z_i∈\{0,1\}^{µ−i−1}} \tilde f(r_{<i},\, x,\, z_i) \bmod q$$
   - V checks: `a_i = Σ_{z∈{0,1}} g_i(z) mod q` (consistency of the running claim), then draws
     `r_i ←$ F_{q^e}` and sets `a_{i+1} := g_i(r_i) mod q`.
4. After round µ−1: P sends final evaluations
   - `v0 := f0(r) mod q` (i.e. MLE[W](r) ∈ Rq^r),
   - `v1 := f1(r) mod q` (i.e. MLE[W̄](r) ∈ Rq^r) — sent as (v_j)_{j∈[2]} ∈ Rq^{r×2};
   - V computes `b := h(v0, v1)` (coordinate-wise evaluation of h at the two vectors).
5. V's **final check**: `a_µ = u^T · CRT(b) mod q`.
6. Both lift the challenges: `r^T := (CRT^{-1}(1_{φ/e}·r_i)^T)_{i∈[µ]}`; set `r^0 := r`, `r^1 := r̄`.
7. **Output:** Ξ^{mle} instance `((H, F, Y, (r^j, v^j)_{j∈[2]}), W)` — claims MLE[W](r^0) = v0 and
   MLE[W](r^1) = v1, where v1 = MLE[W̄](r) = MLE[W](r̄) because conjugation is a ring automorphism
   commuting with polynomial evaluation.

**Properties (Lemma 4.4).** Perfectly correct for Ξ^{sum}_{n̂,n,µ,r,r_out,β} → Ξ^{mle}_{n̂,n,µ,r,β,t=2}.
Knowledge sound with

$$κ = \frac{r_\text{out}·φ/e − 1 + µ·\hat δ_h}{q^e}\quad\text{for}\quad
Ξ^{\text{sum}} ∪ Ξ^{\text{sis}}_{n_\text{com},2µ,2β′} ← Ξ^{\text{mle}}_{n̂,n,µ,r,β′,t=2}$$

Communication `(δ̂_h+1)·µ·e·log q + 2r·log|Rq|` bits. **Prover O(δ_h·m·r) ring operations**; verifier
O(µ·δ̂_h) ops over F_{q^e} + the cost of evaluating h(v0, v1).

**Prover algorithmics (from the proof):**
- f0, f1 available in O(mr);
- f̃ assembled in O(δ_h·m·r) by **Horner's method** over the y-variables of h (h has ≤ δ_h
  nonconstant y-monomials, each a coefficient-vector-in-x times multilinear f-arguments);
- the sumcheck itself uses the **standard linear-time dynamic programming** ([Tha13, XZZ+19, CBBZ23]):
  maintain the partially-evaluated table of f̃ over the remaining hypercube; each round halves the
  table at O(current size), total O(m) — *never* recompute from scratch.
- Round message bound: any two distinct degree-δ̂_h univariates over F_{q^e} agree on ≤ δ̂_h points —
  that is the per-round soundness; plus one Schwartz–Zippel in u for the CRT-slot batching
  ((r_out·φ/e − 1)/q^e).

**Remark 4.5 (single-claim optimisation).** If h does not depend on the y1-block (no conjugate —
true for batch/staircase/AIR), the prover omits v1 and the output is a t = 1 Ξ^{mle} instance;
communication drops to `(δ̂_h+1)·µ·e·log q + r·log|Rq|`; knowledge error unchanged.

**Soundness sketch (extractor):** run P* once at (u, r); rewind with fresh (u′, r′) for a second
transcript (E[#invocations] = (1−ϵ) + ϵ·(1+1/ϵ) = 2). If W′ ≠ W, any non-zero column of W′−W hits
F·w = 0 ⇒ Ξ^{sis}_{n_com, 2µ, 2β′}. If W′ = W but the claim is false: the µ round checks + final
check pin f̃ to the honest polynomial except w.p. µδ̂_h/q^e, then u′-Schwartz–Zippel except w.p.
(r_out·φ/e−1)/q^e.

### 5.3 Π_batch : Ξ^{lin} → Ξ^{sum} (Fig. 3, Lemma 4.6) and Π_batch+ (Cor. 4.7) [A1 core]

**Helper RoK Π_batch (Fig. 3).** Input ((H, F, Y), W) ∈ Ξ^{lin}_{n̂,n,µ,r,β}.

1. V: `c ←$ Rq`.
2. Both: `c := (1, c, …, c^{n̂−n})^T` (n̂−n+1 powers).
3. Split `H = [H̄; H_]` and `Y = [Ȳ; Y_]` at row n (H̄ ∈ Rq^{n×n}, H_ the bottom n̂−n rows);
   `s^T := c^T · Ȳ` — the batched bottom-row claim.
4. `h(y0, y1) := MLE[(c^T H_ F)^T] ⊙ y0` — i.e. h(f0, f1)(x) = MLE[(c^T H_ F)^T](x) · f0(x),
   a *linear* sumcheck claim with no y1-dependence.
5. Output Ξ^{sum} instance `((h, s, H̄, F, Ȳ), W)` — the linear part keeps only the top n rows
   (identity block), all bottom constraints are now carried by the sumcheck claim.

**Why correct:** with h^T := c^T H_ F ∈ Rq^{1×m},
s = (c^T H_ F W)^T = (h^T·W)^T = Σ_{z∈{0,1}^µ} MLE[h](z)·MLE[W](z), using
j = Σ_{k∈[µ]} z_k·2^k (MSB-first identification of [2^µ] with {0,1}^µ).

**Lemma 4.6:** perfectly correct Ξ^{lin}_{n̂,n,µ,r,β} → Ξ^{sum}_{n,n,µ,r,r,β}; knowledge sound with
κ = (n̂−n)/q^e for Ξ^{sis}_{n_com,2µ,2β′} ∪ Ξ^{lin}_{n̂,n,µ,r,β′} ← Ξ^{sum}_{n,n,µ,r,r,β′}.
Communication **0**; prover O(n(m+r)); verifier O(nr) ring ops (both compute s; the prover also
materialises h by computing c^T H_ F in O(nm)).

**Corollary 4.7 (Π_batch+ := Π_mle-⊗ ∘ Π_sum ∘ Π_batch).** Perfectly correct for

$$Ξ^{\text{lin}}_{\hat n,n,µ,r,β} → Ξ^{\text{lin}}_{n+1,n+1,µ,r,β}$$

knowledge sound with κ = (n̂−n + r·φ/e − 1 + 2µ)/q^e for
Ξ^{sis}_{n_com,2µ,2β′} ∪ Ξ^{lin}_{n̂,n,µ,r,β′} ← Ξ^{lin}_{n+1,n+1,µ,r,β′}.
Communication 3µe·log q + r·log|Rq| (δ̂_h = 2). Prover O(m(n+r) + nr); verifier O(n(µ+r+n)):
- verifier computes s^T = c^T Ȳ in O(nr);
- verifier evaluates MLE[(c^T H_ F)^T](r) = (c^T H_)·F·e_r with e_r := ⊗_{k∈[µ]}(1−r_k, r_k)^T:
  a^T := c^T H_ costs O(n²); each row f_j^T of F evaluates against e_r in O(µ) (mixed-product
  property of the row-tensor structure) ⇒ F·e_r costs O(nµ); final inner product O(n); times r
  output columns ⇒ O(µn + n(r+n)).
- vs RPS's lazy Π_batch-: same *asymptotics* for proof size, but **constraint rows actually leave the
  instance** (this is what later makes the folding scheme step cost constant — §7.3).

### 5.4 Π_norm : Ξ^{lin} → Ξ^{sum} (Fig. 4, Lemma 4.8) and Π_norm+ (Cor. 4.9) [A2]

**Helper RoK Π_norm (Fig. 4).** Input ((H, F, Y), W).

**Prover:**
1. Parse `W = (w_i)_{i∈[r]}` into columns.
2. Compute the claimed norms `t^T := (⟨w_i, w_i⟩)_{i∈[r]}` where
   ⟨w_i, w_i⟩ = Σ_{j∈[m]} w̄_{j,i}·w_{j,i} ∈ Rq (conjugate inner product) — **O(mr) ring
   multiply-adds, no polynomial multiplication, no FFT/NTT convolution**.
3. Send t.

**Verifier:**
- Receive t; check `for i ∈ [r]: Trace(t_i) ≤ β²` — Trace in the **balanced** integer
  representative; the comparison is over Z.

**Both:**
4. `h := y0 ⊙ y1` (coordinate-wise product; h(f0, f1)(z) = MLE[W](z) ⊙ MLE[W̄](z)).
5. Output Ξ^{sum} instance `((h, t, H, F, Y), W)` — claim:
   Σ_{z∈{0,1}^µ} (MLE[W] ⊙ MLE[W̄])(z) = t mod q.

**Correctness chain:** on the hypercube MLE[W](z) = w_z, so the sum equals
Σ_j w̄_{j,i}w_{j,i} = t_i exactly; and Trace(t_i) = Trace(Σ_j w̄_j w_j) = Σ_j Σ_σ σ(w̄_j w_j) =
‖w_i‖²_{σ,2} ≤ β². Conversely (extraction): the sumcheck claim gives t_i ≡ Σ_j w̄_j w_j mod q, and
since ‖W‖ ≤ β′ with 4β′² < q (Setting 3.4) the integer Σ_j w̄_j w_j = ‖w_i‖²_{σ,2} ≤ β′² < q/2 is the
*unique* balanced lift — no wraparound, so Trace(t_i) ≤ β² ⇒ ‖w_i‖²_{σ,2} ≤ β² ⇒ ‖W‖_{σ,2} ≤ β.

**Lemma 4.8:** perfectly correct, knowledge sound with **κ = 0** for
Ξ^{lin}_{n̂,n,µ,r,β} ← Ξ^{sum}_{n̂,n,µ,r,r,β′} (note: no SIS case needed — extraction is direct).
Communication r·log|Rq|; prover O(r·m); verifier O(r).

**Corollary 4.9 (Π_norm+ := Π_batch+ ∘ Π_mle ∘ Π_sum ∘ Π_norm).** Perfectly correct for

$$Ξ^{\text{lin-}⊗}_{\hat n,n,µ,r,β} → Ξ^{\text{lin-}⊗}_{n+1,n+1,µ,r,β}$$

knowledge sound with κ = (n̂−n + 2(rφ/e + 2µ))/q^e for
Ξ^{lin-⊗} ∪ Ξ^{sis}_{n_com,2µ,2β′} ← Ξ^{lin-⊗}_{n+1,n+1,µ,r,β′}. Works natively for Ξ^{lin-} too.
Communication 6µe·log q + 4r·log|Rq| (t vector r log|Rq| + Π_sum 3µe log q + 2r log|Rq| (two claims)
+ Π_batch+ 3µe log q + r log|Rq|). **Prover O(m(n+r) + nr) ring ops; verifier O(n(µ+r+n)).**

#### The Π_norm+ prover-efficiency trick — O(m) vs O(m log m) [transcribe exactly]

RPS/RnR's Π_norm-: prove ‖w‖² = Trace(⟨w,w⟩) via an **auxiliary commitment to the convolution of the
witness with itself**: compute the two degree-m polynomials
p0 := Σ_{i∈[m]} w_i·x^i and p1 := Σ_{i∈[m]} w̄_i·x^{−i}, multiply p0·p1 (an O_λ(m log m)
ring-NTT convolution — *the* prover bottleneck of the whole framework, inherited by Papercraft),
commit to the product, prove consistency of the commitment, and open it at the constant term, which
aggregates the self-inner product Σ_i w̄_i·w_i.

SALSAA's Π_norm+ replaces that by two linear-time pieces:
1. **Compute t directly** as the conjugate inner product t_i = Σ_j w̄_{j,i}·w_{j,i} — O(m) ring
   multiplications (entrywise conjugate-multiply-accumulate; no convolution, no NTT of length m·φ).
2. **Prove t by a degree-2 sumcheck over the MLEs**: the claim
   Σ_{z∈{0,1}^µ} MLE[W](z)·MLE[W̄](z) = t fits Ξ^sum with h = y0 ⊙ y1, and Π_sum's prover runs in
   O(δ_h·m·r) = O(2·m·r) ring operations via the dynamic-programming sumcheck — linear for constant
   degree. (Key point: the sumcheck runs *over ring elements*, i.e. over Rq-valued MLEs, one
   hypercube point = one ring element, not one coefficient; the CRT-slot batching of the transcript
   is what keeps the messages small without a coefficient-wise large-modulus sumcheck.)

Net effect: the single quasi-linear bottleneck of the RPS/RnR prover disappears; every round of the
SNARK composition is now O(λm) total. Π_norm+ is a **drop-in replacement**: same interface
(Ξ^{lin-⊗} → Ξ^{lin-⊗}), preserves the norm bound without inflation, does not widen the witness r,
and increases n by only 1 (Π_norm- increases it by 3 and widens r by ℓ).

### 5.5 Π_bin : Ξ^{bin} → Ξ^{sum} (Fig. 5, Lemma 4.12) and Π_bin+ (Cor. 4.13) [A3]

**Precondition: power-of-two cyclotomic ring** R = Z[ζ_f], f = 2^k, φ = f/2 (Lemma 4.11's
orthogonality of the power basis under the Hermitian trace form). Let 1° := Σ_{k∈[φ]} ζ^k ∈ R
(all-ones coefficients), 1° ∈ R^m the all-1° vector.

**Helper RoK Π_bin (Fig. 5).** Input ((H, F, Y), W) ∈ Ξ^{bin}.

**Prover:**
1. Parse `W = (w_i)_{i∈[r]}`.
2. `t^T := (⟨w_i, 1° − w_i⟩)_{i∈[r]}` where ⟨w_i, 1°−w_i⟩ = Σ_{j∈[m]} w̄_{j,i}·(1° − w_{j,i}) — O(mr).
3. Send t.

**Verifier:**
- Receive t; check `for i ∈ [r]: Trace(t_i) = 0` (balanced representative, over Z).

**Both:**
4. `h := y1 ⊙ (1° − y0)` — note the argument order: h(f0, f1)(z) = MLE[W̄](z)·(1° − MLE[W](z)).
5. Output Ξ^{sum} instance ((h, t, H, F, Y), W).

**Why Trace(t_i) = 0 ⟺ binary:** by Lemma 4.11,
Trace(w·(1°−w)) = φ·Σ_k cf(w)_k·(1−cf(w)_k), and for integer a, a(1−a) ≤ 0 with equality iff
a ∈ {0,1}. So Trace(t_i) = φ·Σ_{j,k} cf(w_{j,i})_k(1−cf(w_{j,i})_k) = 0 with every summand ≤ 0
forces all coefficients into {0,1}. **No wraparound:** |Trace(t_i)| ≤ 2φ·Σ cf² ≤ 2·rad(f)·φ/f·‖w_i‖²_{σ,2}
= 2‖w_i‖²_{σ,2} ≤ 2β′² < q/2 (uses ‖cf(·)‖² ≤ (rad(f)/f)·‖·‖²_{σ,2}, Lemma 2 of [KLNO25], rad(f) = 2,
φ = f/2, and Setting 3.4).

**Lemma 4.12:** perfectly correct and knowledge sound (κ = 0) for
Ξ^{bin}_{n̂,n,µ,r,β} ↔ Ξ^{sum}_{n̂,n,µ,r,r,β}. Communication r log|Rq|; prover O(r·m); verifier O(r).

**Corollary 4.13 (Π_bin+ := Π_batch+ ∘ Π_mle ∘ Π_sum ∘ Π_bin).** Perfectly correct for
Ξ^{bin}_{n̂,n,µ,r,β} → Ξ^{lin}_{n+1,n+1,µ,r,β}; κ = (n̂−n+2(rφ/e+2µ))/q^e for
Ξ^{bin} ∪ Ξ^{sis}_{n_com,2µ,2β′} ← Ξ^{lin}_{n+1,n+1,µ,r,β′}; communication 6µe log q + 4r log|Rq|;
prover O(m(n+r)+nr); verifier O(n(µ+r+n)). (Identical cost profile to Π_norm+ — as expected, both
are degree-2 sumchecks with a t-vector prelude.)

*Vs RPS/Papercraft binariness:* the old RoK inherited the O_λ(m log m) cost from Π_norm- **and**
required the witness to live in a "tensor subring" (so that coefficient-wise binariness could be
phrased ring-element-wise). SALSAA's Π_bin+ needs only the power-of-two ring, no subring constraint.

### 5.6 Π_ (staircase) : Ξ^{stair} → Ξ^{sum} (Fig. 6, Lemma 4.15) and Π_+ (Cor. 4.16) [A3]

**Setting:** K := m/n̄ block count (K and n̄ powers of 2), W parsed into K row-blocks
W_j ∈ Rq^{n̄×r}. Constraint: A·W_0 = Y₀, B·W_{j−1} + A·W_j = 0 for j = 1,…,K−1, B·W_{K−1} = Y₁.
The µ hypercube variables split as x = (x_step, x_inner): the first log₂K variables index the block,
the last log₂n̄ variables index the position within a block (µ = log₂K + log₂n̄).

**Helper RoK Π_ (Fig. 6).** Input ((H, F, Y, A, B, Y₀, Y₁), W).

1. V: `c ←$ Rq`.
2. *(no interaction)*
3. Both compute (deterministically from c and the instance):
   - `c₀ := (1, c, …, c^{m̄−1})^T` — m̄ successive multiplications (m̄ = row count of A, B);
   - `p := (c^{j·m̄})_{j∈[K]}` — the geometric step-power vector, p_j = (c^{m̄})^j;
   - `d^T := Σ_{ρ∈[m̄]} c^ρ·A_{ρ,:} + c^{m̄+ρ}·B_{ρ,:}` — the single batched row ∈ Rq^{n̄};
   - `s := c₀^T·Y₀ + c^{K·m̄}·c₀^T·Y₁`.
4. (continued)
5. `h(x)(y₀, y₁) := MLE[p](x_step) · MLE[d](x_inner) · y₀` — a *linear* claim (no y1).
6. Output Ξ^{sum} instance ((h, s, H, F, Y), W).

**Correctness derivation (batching identity).** Weight block-row i (i = 0…K) by c^{i·m̄} and its
ρ-th inner row by c^ρ, then sum all (K+1)·m̄ rows and group by column block j:
- W_j is hit by A-rows of block-row j (weight c^{j·m̄}·c^ρ) and B-rows of block-row j+1 (weight
  c^{(j+1)m̄}·c^{m̄+ρ} = c^{j·m̄}·c^{m̄+ρ}); grouping yields coefficient c^{j·m̄}·d^T = p_j·d^T.
- RHS: block-row 0 contributes c₀^T·Y₀; block-row K contributes c^{K·m̄}·c₀^T·Y₁.

$$\sum_{j∈[K]} p_j·d^T W_j = c_0^T Y_0 + c^{K\bar m}·c_0^T Y_1 = s
\quad\Longleftrightarrow\quad
\sum_{z∈\{0,1\}^µ} \mathrm{MLE}[p](z_\text{step})·\mathrm{MLE}[d](z_\text{inner})·\mathrm{MLE}[W](z) = s \bmod q$$

**Lemma 4.15:** perfectly correct for Ξ^{stair}_{m̄,n̄,n̂,n,µ,r,β} → Ξ^{sum}_{n̂,n,µ,r,r,β}; knowledge
sound with κ = (K+1)·m̄/q^e for Ξ^{sis}_{n_com,2µ,2β′} ∪ Ξ^{stair}_{m̄,n̄,n̂,n,µ,r,β′} ←
Ξ^{sum}_{n̂,n,µ,r,r,β′}. Communication **0**; both parties O(m̄·(n̄+r) + log₂K) ring ops.

**Soundness mechanism:** define block-row errors E₀ := AW₀−Y₀, E_j := BW_{j−1}+AW_j (1 ≤ j ≤ K−1),
E_K := BW_{K−1}−Y₁. The batched sum equals Σ_{i∈[K+1]} c^{i·m̄}·c₀^T·E_i; per CRT slot this is a
univariate polynomial in c of degree ≤ (K+1)·m̄ − 1, nonzero in some slot if some E_i ≠ 0 (CRT is an
isomorphism), so a fresh c′ kills it with probability ≤ (K+1)m̄/q^e (Schwartz–Zippel over F_{q^e}).

**Cost details:** c₀ costs O(m̄); c^{m̄} is the next power after c₀ (O(1)); p is *not* materialised
by the prover; d costs O(m̄·n̄); s costs O(m̄·r); c^{K·m̄} = (c^{m̄})^K via O(log₂K) squarings.
Verifier evaluates MLE[p](r_step) in **O(log₂K)** by iterative squaring (p geometric ⇒ its MLE is
the product of per-variable powers), and MLE[d](r_inner) in O(n̄) (d is an arbitrary length-n̄
vector with no structure).

**Corollary 4.16 (Π_+ := Π_batch+ ∘ Π_mle ∘ Π_sum ∘ Π_).** Perfectly correct for
Ξ^{stair}_{m̄,n̄,n̂,n,µ,r,β} → Ξ^{lin}_{n+1,n+1,µ,r,β}; knowledge sound with
κ = ((K+1)m̄ + n̂−n + 2(rφ/e+2µ) − 1)/q^e for Ξ^{stair} ∪ Ξ^{sis} ← Ξ^{lin}_{n+1,n+1,µ,r,β′}.
Communication 6µe log q + 2r log|Rq| (single claim: h has no y1). Prover O(m̄n̄ + m(n+r) + nr);
verifier O(m̄(n̄+r) + n(µ+r+n) + log₂K) ring ops. (δ̂_h = 2: MLE[p] and MLE[d] act on disjoint
variable blocks, so the coefficient of y₀ is multilinear in x; multiplied by MLE[W] ⇒ individual
degree 2.)

*Decoupling vs Papercraft:* the block width n̄ of A, B is decoupled from the tensor structure of
the Ξ^{lin} instance (in Papercraft's analogue the staircase width is tied to the tensor split).

### 5.7 Π_air : Ξ^{com-air} → Ξ^{sum} (Fig. 7, Lemma 4.20) and Π_air+ (Cor. 4.21) [A5 base]

**Objects:** V := [W, shift(W)] ∈ Rq^{m×2t} (m = 2^µ rows), shift(W)_{i,:} = W_{(i+1) mod m,:}
(Def 4.17). Transition f ∈ Rq[y^{2t}]_{≤d}; boundary set C = {(i_k, j_k, u_k)}_{k∈[|C|]} ⊆
[m]×[t]×Rq. e_{i,n} = i-th standard basis vector; bin(i) ∈ {0,1}^µ the binary rep of row i;
eq(·, 1) with 1 = bin(m−1) indicates the last row. Column-selector identity (Eq. 3):

$$⟨\mathrm{MLE}[V],\, e_{b,2} ⊗ α⟩ = \mathrm{MLE}[V_b α] \quad (b ∈ [2])$$

because e_{0,2}⊗α = (α, 0) picks the first t columns (the trace) and e_{1,2}⊗α = (0, α) the last t
(the shifted copy).

**Helper RoK Π_air (Fig. 7).** Input ((f, C, H, F, Y), W); witness for the sumcheck is V.

1. V draws three challenges: `η ←$ Rq^µ`, `α ←$ Rq^t`, `θ ←$ Rq`.
2. *(comment: y₀, y₁ take values in Rq^{2t}[x] — the column-wise MLEs of V; no y1 is ever used)*
3. Both: `θ̃(x) := MLE[(θ^i)_{i∈[m]}](x)` (multilinear; θ̃(x) = Π_{j∈[µ]}(1 − x_j + θ·x_j)),
   targets `s₀ = s₁ = 0`, `s₂₊k = u_k ∀k ∈ [|C|]`.
4. `h₀(y₀, y₁) := eq(η, x)·(1 − eq(x, 1))·f(y₀)` — **transition claim**.
5. `h₁(y₀, y₁) := θ̃(x)·⟨y₀, e_{0,2} ⊗ α⟩ − (θ·θ̃(x) − (θ^m − 1)·eq(x, 1))·⟨y₀, e_{1,2} ⊗ α⟩`
   — **shift claim**.
6. `h₂₊k(y₀, y₁) := eq(x, bin(i_k))·⟨y₀, e_{j_k, 2t}⟩ ∀k ∈ [|C|]` — **boundary claims**.
7. `h := (h_k)_{k∈[2+|C|]}, s := (s_k)_{k∈[2+|C|]}`.
8. Output Ξ^{sum} instance `((h, s, H, F, Y), V)` with r_out = 2 + |C| and r = 2t witness columns.

All messages are verifier challenges ⇒ communication 0; both parties O(µ + t + |C|) ring ops
(θ̃ from µ successive squarings (θ^{2^j})_{j∈[µ]} plus one more for θ^m; α stored; boundary terms
are just (i_k, j_k) indices).

**The three verification equations (what the claims mean on the hypercube):**

(a) *Transition (Eq. 4).* Σ_z eq(η,z)·(1 − eq(z,1))·f(MLE[V])(z) = Σ_{i∈[m−1]} eq(η, bin(i))·f(V_{i,:}) = s₀ = 0.
The factor (1 − eq(z,1)) drops the single wrap-around row m−1 on which f is unconstrained; the
eq(η,·) weight randomises so that the claim pins *every* row (see soundness below).

(b) *Shift (Eqs. 5–6).* Key identities:
- Eq (5): (θ, …, θ^{m−1}, 1)·V₁ = Σ_i θ^{(i+1) mod m}·V_{1,i,:} = Σ_i θ^{(i+1) mod m}·V_{0,(i+1) mod m,:}
  = Σ_{i} θ^{i}·V_{0,i,:} = (1, θ, …, θ^{m−1})·V₀ (uses V₁ = shift(V₀)).
- Eq (6): θ·θ̃(z) − (θ^m−1)·eq(z, 1) = MLE[(θ, …, θ^{m−1}, 1)](z) — θ·θ̃ = MLE[(θ,θ²,…,θ^m)] and the
  correction term replaces the last hypercube value θ^m by 1 (both sides multilinear ⇒ equal).
Then Σ_z h₁(MLE[V])(z) = [(1,θ,…,θ^{m−1})·V₀ − (θ,…,θ^{m−1},1)·V₁]·α = 0 = s₁.

(c) *Boundary (Eq. 7).* Σ_z eq(z, bin(i_k))·⟨MLE[V], e_{j_k,2t}⟩(z) = V_{i_k, j_k} = u_k = s₂₊k
(exact selector identity, no soundness loss; j_k ∈ [t] reads the trace half).

**Lemma 4.20:** perfectly correct for
Ξ^{com-air}_{t,m,d,n̂,n,µ,|C|,β} → Ξ^{sum}_{n̂,n,µ,2t,2+|C|,β}; knowledge sound with κ = (µ+m)/q^e
for Ξ^{com-air} ∪ Ξ^{sis}_{n_com,2µ,2β′} ← Ξ^{sum}_{n̂,n,µ,2t,2+|C|,β′}. Communication 0; both
parties O(µ+t+|C|). **Degrees: δ̂_h ≤ d+2, δ_h ≤ (d+2)µ** (f(MLE[V]) has individual degree d, total
dµ; h₀ adds two multilinear factors; h₁, h₂₊k have individual degree 2).

**Soundness sketch:** two transcripts ⇒ either V′ ≠ V (→ Ξ^{sis} via a non-zero column of V′−V) or
V′ = V fixed before the fresh challenges:
- (i) P₀(x) := Σ_z eq(x,z)(1−eq(z,1))f(MLE[V])(z) is the **MLE of the badness vector**
  (f(V_{i,:})·[i<m−1])_i, multilinear of total degree µ; it vanishes at random η′ only w.p. ≤ µ/q^e
  unless every f(V_{i,:}) = 0.
- (ii) P₁(x₀, x) := (1,x₀,…,x₀^{m−1})V₀ − (x₀,…,x₀^{m−1},1)V₁ · x has total degree m; the
  coefficient of x₀^k is V_{0,k,:} − V_{1,(k−1) mod m,:}, so P₁ ≡ 0 ⟺ V₁ = shift(V₀); random
  (θ′,α′) ⇒ failure ≤ m/q^e.
- (iii) boundary claims are exact.
Then W := V₀ satisfies Ξ^{air} (f(W_{i,:},W_{i+1,:}) = f(V_{i,:}) = 0 for i ∈ [m−1], W_{i_k,j_k} = u_k).

**Corollary 4.21 (Π_air+ := Π_batch+ ∘ Π_mle ∘ Π_sum ∘ Π_air).** Perfectly correct for
Ξ^{com-air}_{t,m,d,n̂,n,µ,|C|,β} → Ξ^{lin}_{n+1,n+1,µ,2t,β}; knowledge sound with
κ = (n̂−n + (|C|+2t+2)φ/e + m + (d+5)µ − 1)/q^e for
Ξ^{com-air} ∪ Ξ^{sis}_{n_com,2µ,2β′} ← Ξ^{lin}_{n+1,n+1,µ,2t,β′}. Communication (d+6)µe log q +
4t log|Rq|. **Prover O((d+2)·µ·m·t) ring operations** (δ_h = (d+2)µ drives Π_sum's O(δ_h·m·r) with
r = 2t). Verifier O((|C|+n+d)·µ + (|C|+n)·t + n² + T_f) ring ops, where T_f = cost of evaluating
f(v₀); θ̃(r) evaluates in O(µ) via mixed-product: θ̃(r) = (1,θ,…,θ^{m−1})·e_r = Π_j⟨(1,θ), (1−r_j, r_j)⟩.

### 5.8 Composition into full argument systems [A1/A4 context]

The RPS/RnR toolkit inherited by SALSAA (Table 1 of the paper; entries marked ✻ are garbled in the
text squeeze — consult [KLNO24/KLNO25] for exact norm bookkeeping):

| RoK | Correctness | Extraction | Communication |
|---|---|---|---|
| Π_split | Ξ^{lin}_{m,r,β} → Ξ^{lin}_{m/τ, r·τ, β} | Ξ^{lin}_{m, √τ·β′} ← Ξ^{lin}_{m/τ, r·τ, β′} | (τ−1)·r·n̂·log|Rq| |
| Π_fold | Ξ^{lin}_{m,r,β} → Ξ^{lin}_{m, γβ} (r→1 col) | Ξ^{lin}_{m,r,β′} ← Ξ^{lin}_{m, γβ′} | 0 |
| Π_b-decomp ✻ | Ξ^{lin}_{r,β} → Ξ^{lin}_{rℓ, √(b−1)·β̃} | Ξ^{lin}_{b^{ℓ−1}…} ← Ξ^{lin}_{rℓ, β′} | (ℓ−1)·r·n̂·log|Rq| |
| Π_batch- (klno24) | Ξ^{lin}_{n̂,β} → Ξ^{lin}_{n+1,β} | Ξ^{lin}_{n̂,β′} ← Ξ^{lin}_{n+1,β′} | 0 |
| Π_norm- (klno24) | Ξ^{lin}_{m,n̂,r,β} → Ξ^{lin}_{m,n̂+3,r+ℓ,β̃} | Ξ^{lin}_{m,n̂,r,√r·β} ← Ξ^{lin}_{m,n̂+3,r+ℓ,β̃′} | (3(ℓ+r)+ℓn̂)·log|Rq| |
| Π_join | Ξ^{lin}_{n̂₀,n₀,r₀} × Ξ^{lin}_{n̂₁,n₁,r₁} → Ξ^{lin}_{n̂₀+n̂₁−n, n₀+n₁−n, r₀+r₁} | (product) ← (output) | ((n̂₀−n)r₁ + (n̂₁−n)r₀)·log|Rq| |
| Π_⊗RP ✻ | Ξ^{lin-⊗(r,m′)}_{m,n̂,r,β} → Ξ^{lin-⊗}_{m,n̂+1,r,β} × Ξ^{lin-⊗}_{m′,n+1,1,β̂} | Ξ^{lin-⊗}_{m,n̂,r,β̃′} ← [output, ϱ × Ξ^{lin-⊗}_{m′,n+1,1,β′′}] | (n+r)·log|Rq| |
| **Π_batch+** | Ξ^{lin}_{n̂,n,β} → Ξ^{lin}_{n+1,n+1,β} | Ξ^{lin}_{n̂,n,β′} ← Ξ^{lin}_{n+1,n+1,β′} | 3µe log q + r log|Rq| |
| **Π_norm+** | Ξ^{lin}_{n̂,n,r,β} → Ξ^{lin}_{n+1,n+1,r,β} | Ξ^{lin}_{n̂,n,r,β} ← Ξ^{lin}_{n+1,n+1,r,β′} | 6µe log q + 4r log|Rq| |

(ℓ = ⌈log_b(2β+1)⌉ for Π_b-decomp; ℓ = log_b(2β̃+1) with β̃ ≥ β for Π_norm-; β̂, β̃′, ϱ, m′ are
Π_⊗RP parameters as in [KLNO25] — β̂ ≈ √(m·r_p)·β, β̃′ ≈ 2·rad(f)·√(m·r_p)·β″.)

**RPS/RnR loop (original):**
`Π_norm- → Π_b-decomp → Π_split → Π_⊗RP → (Π_fold | Π_id) → Π_join → Π_batch-`, and a second-phase
loop replacing Π_⊗RP by unstructured Π_RP and always applying Π_fold.

**SALSAA loop (§5.2):**
```
phase 1 (repeated µ' = O(log_λ m) times, height m → O(λ)):
  Π_norm+ → Π_b-decomp → Π_split → Π_⊗RP → (Π_fold | Π_id) → Π_join → Π_batch+
phase 2 (repeated O(log λ) times, height → O(1)):
  Π_norm+ → Π_b-decomp → Π_split → Π_RP → Π_fold → Π_batch+
final: prover sends the remaining O(1)-height witness in the clear.
```

- Per-round prover: every step O(m) except Π_⊗RP/Π_RP at O(λm) ⇒ per round O(λm); height shrinks
  geometrically ⇒ **total prover O(λm) ring operations** (vs RPS's O_λ(m log m) dominated by
  Π_norm-'s degree-m polynomial product).
- Π_norm+ vs Π_norm- in the loop: no norm inflation, no r-widening, n+1 instead of n+3;
  communication O(log|Rq| + log m·(λ/log λ)·log q) ≈ O(1) Rq elements under the standard parameter
  assumption φ = Θ(λ·log m/log λ) (from [BDGL16]), log q = O(log m).
- Verifier: dominated by Π_⊗RP's O(λ²) per round ⇒ **O(λ²·log m)** ring operations.
- **Theorem 5.1 (Π_as):** overwhelming correctness for Ξ^{lin-⊗}_{n̂,n,µ,r,β} → {0/1} and negligible
  knowledge error for Ξ^{lin-⊗} ∪ {Ξ^{sis}_{param}} ← {0/1}; proof size O(λ·log³m/log λ) bits;
  prover O(λm); verifier O(λ² log m). Under vSIS hardness for all params in the extraction chain.
- **Corollary 5.2 (PCS):** an opening claim MLE[w](x) = t for committed w is a Ξ^{mle-⊗} instance →
  Π_mle → Ξ^{lin-⊗} → Π_as. (A commitment to the witness doubles as a commitment to its MLE.)
- **Corollary 5.3 (SNARK for committed AIR):** Π_as-air := Π_as ∘ Π_air+; same asymptotics with
  n, d, t, |C| = O(1).

### 5.9 Application: the VDF "Papercraft+" construction [A4]

**Delay function (Papercraft blueprint, [LM23, OKC+25]).** Fixed public A ∈ Rq^{n×m} and gadget
matrix G = G_{b,m,k} (b = 2 ⇒ binary digits). Starting from y₀, evaluation runs T inherently
sequential steps:

$$w_i := G^{-1}(−y_i) \bmod q,\qquad y_{i+1} := A·w_i \bmod q \qquad (i = 0,…,T−1),\qquad \text{val} := y_T,\ \text{aux} := w = (w_0,…,w_{T−1})$$

Stacking the chain gives exactly a **staircase system with binary witness** (G on the diagonal, A on
the subdiagonal, m·T = 2^µ total witness height, K = T blocks):

$$
\begin{bmatrix} G & & & \\ A & G & & \\ & A & G & \\ & & \ddots & \ddots \\ & & & A \end{bmatrix}
·\begin{bmatrix} w_0 \\ w_1 \\ \vdots \\ w_{T−1} \end{bmatrix}
= \begin{bmatrix} −y_0 \\ 0 \\ \vdots \\ 0 \\ y_T \end{bmatrix} \bmod q,
\qquad \mathrm{cf}(w) ∈ \{0,1\}^{m·T·φ}
$$

(Row-block check: G·w_i + A·w_{i−1} = −y_i + y_i = 0; endpoints G·w₀ = −y₀, A·w_{T−1} = y_T.)

**Proof system for the VDF (Eq. 9 + Theorem 6.6):**

$$Π^{\text{as-}}:\quad Ξ^{\text{bin-⊗}\text{-stair}} \xrightarrow{Π_+} Ξ^{\text{bin}} \xrightarrow{Π^{\text{bin}+}} Ξ^{\text{lin-⊗}} \xrightarrow{Π^{\text{as}}} \{0/1\}$$

where Ξ^{bin-⊗-stair} is the staircase relation of §4.6 with A := A, B := G swapped roles (G
diagonal, A subdiagonal — note the paper writes the stacked matrix as [G; A]_T) plus the binariness
constraint on w; concretely the proven instance is ((I_n, F, y, G, A, y₀, y_T), w) with commitment
y = F·w and β = φ·√(m·T) (each binary ring element has ‖·‖_{σ,2} ≤ φ; the exact β subscript is
slightly garbled in the squeezed text — recompute as √(Σ‖w_i‖²) ≤ φ·√(m·T) and cross-check
4β² < q). Complexities: proof O(λ log³m/log λ) bits; prover O(mλ); verifier O(log m·λ²) ring ops.

**Full VDF (Theorem 6.8), over power-of-two R = Z[ζ_f], f = 2^k, φ = f/2:**
- `Setup(1^λ)`: A ←$ Rq^{n×m}; F ←$ Rq^{n_com×2^{⊗µ}}` (row-tensor commitment key); pp := (A, F).
- `Gen(pp)`: y₀ ←$ Rq^n; inst := y₀.
- `Eval(pp, inst, 1^T)`: iterate the chain above; output val := y_T, aux := w.
- `⟨P(pp,inst,T,aux), V(pp,inst,T,val)⟩`: P sends the commitment `y = F·w mod q`; both run Π_as-
  on ((I_n, F, y, G, A, y₀, y_T), w); V accepts iff Π_as- accepts.

**VDF properties:** σ-sequential for σ = σ′ − p(λ) (p from Lemma 6.7); ϵ-correct with
ϵ = negl(λ) + T·n·φ·2^{log q − ⌊log q⌋}/q (gadget decomposition of a (pseudo)uniform element fails
with ≤ n·φ·2^{log q−⌊log q⌋}/q per step — union bound over the n·φ integer coefficients and T
steps); sound. Assumptions: q^e = ω(poly(λ)); SIS-Seq_{R,q,m,n,σ′} (Def 6.5: nobody finds u with
A·u = 0 mod q, cf(u) ∈ {0,1}^{m·φ}; and no depth-< σ′ adversary outputs (y_T, u) satisfying the
stacked staircase with binary cf(u)); SIS∞_{R,q,m,n,1} hard; vSIS hard for every extraction param.

**Soundness spine:** binding commitment + argued binary & staircase relations ⇒ extractor yields
either a valid Ξ^{bin-⊗-stair} witness — impossible when val′ ≠ val because **binary gadget
decomposition is injective** (G·w*_i = −y_i uniquely determines w*_i, then y_{i+1} = A·w*_i is
fixed; by induction y_T is uniquely determined by (A, y₀)) — or a vSIS break. Sequentiality: a
depth-< σ prover would give a depth-< σ′ SIS-Seq solver (the composition is depth-preserving,
Lemma 6.7: Π_split/Π_fold/Π_b-decomp by [OKC+25 Lemma 2]; Π_norm+/Π_+/Π_batch+ by splitting Π_sum
into 2-round coordinate-wise special-sound RoKs + negligible challenge collision since
q^e = ω(poly(λ)))).

### 5.10 Application: the folding scheme [A5]

**Definitions (KST22-style, adapted):**
- *Structure map* (Def 7.4): str returns the commitment key F from a statement of Ξ^{lin} / Ξ^{com-air};
  Ξ|s := instances with str(stmt) = s; str on a product is str(stmt₀) if the two agree (else undefined).
- *Folding scheme* (Def 7.2): a RoK Π that is structure-preserving for Ξ × Ξ_acc → Ξ_acc wrt str
  (correctness for every fixed structure s), and knowledge sound for
  (Ξ′ × Ξ′_acc) ∪ Ξ_break ← Ξ′_acc wrt str. Consecutive steps compose because each step outputs an
  Ξ_acc|s instance.

**Theorem 7.3 (Π_fs-core).** Six RoKs in this order (note: **no Π_split** — the relation is not
split into smaller relations for folding):

$$Π^{\text{norm}+} → Π^{\otimes RP} → (Π^{\text{fold}} \mid Π^{\text{id}}) → Π^{\text{join}} → Π^{\text{batch}+} → Π^{\text{b-decomp}}$$

$$Ξ^{\text{lin}-}_{\hat n,n,µ,r_\text{acc}+r,β} \longrightarrow Ξ^{\text{lin}-}_{n+1,n+1,µ,r_\text{acc},β},\qquad r_\text{acc} = 2^\ell$$

with proof O(λ·log²m/log λ) bits, prover O(mλ), verifier O(λ²) ring ops (r, n, ℓ = O(1)). Works for
Ξ^{lin-⊗} too. **Parameter walk-through (§7.3 of paper):**
1. Start: Ξ^{lin}_{n̂,n,µ,r_acc+r,β} (r = # new columns to fold into the r_acc-column accumulator).
2. `Π_norm+`: → Ξ^{lin}_{n+1,n+1,µ,r_acc+r,β} — the *norm checkpoint*: guarantees the extracted
   witness norm ≤ β; from here on the constraint part is a single row whatever the input shape.
3. `Π_⊗RP`: → two instances Ξ^{lin}_{n+2,n+2,µ,r_acc+r,β} × Ξ^{lin}_{n+1,n+1,µ,1,β̂},
   β̂ = √(m_rp)·β with m_rp = O(λ) (random projection; used to argue the *approximate* norm in the
   extraction direction).
4. `Π_fold` (on the first): → Ξ^{lin}_{n+2,n+2,µ,1,(r_acc+r)·γ·β} (γ = challenge-set expansion
   factor; single column).
5. `Π_join`: merge the two branches → Ξ^{lin}_{n+3,n+3,µ,2,max(β̂,(r_acc+r)γβ)}.
6. `Π_batch+` then `Π_b-decomp`: → Ξ^{lin}_{n+1,n+1,µ,2ℓ,β} — ℓ chosen so that b-ary decomposition
   of a max(β̂,(r_acc+r)γβ)-bounded witness lands back under β (r_acc = 2ℓ columns).

**Lemma 7.6 (structure preservation).** None of the six RoKs touches the top rows F̄. If the input
statement's F has the shape `[A; r₀^T M₀; …; r_{t−2}^T M_{t−2}]` (mod q), then so does the output —
A and (M_i, r_i)_{i∈[t−1]} can still be read off the folded statement. This is what lets the folded
accumulator be *re-interpreted* as the application relation after each step.

**Why Π_batch+ is the enabling piece (§7.3):** every folding step *appends* constraint rows (the
evaluation claims produced by Π_norm+ and Π_⊗RP, plus rows merged by Π_join). RPS's lazy batching
Π_batch- aggregates only within H and **leaves the bottom rows of F in place** ⇒ after k steps the
accumulator carries O(k) bottom rows, every subsequent step costs Θ(k), and the output never returns
to the accumulator shape. Π_batch+ compresses the accumulated bottom rows into a single row each
iteration ⇒ every step outputs Ξ^{lin}_{n+1,n+1,µ,r_acc,β}: **fixed-shape accumulator, constant
per-step cost**.

**Corollary 7.5 (Π_fs, folding scheme for Ξ^{lin}):** `Ξ^{lin}_{n̂,n,µ,r,β} --Π_join--> (combined
with the accumulator) --Π_fs-core--> Ξ^{lin}_{n+1,n+1,µ,r_acc,β}`; a folding scheme wrt str with
overwhelming correctness for Ξ^{lin}_{n̂,n,µ,r,β} × Ξ^{lin}_{n+1,n+1,µ,r_acc,β} → Ξ^{lin}_{n+1,n+1,µ,r_acc,β}
and negligible knowledge error for (Ξ^{lin}′ × Ξ^{lin}_acc′) ∪ {Ξ^{sis}_{param}} ← Ξ^{lin}_acc′.
Π_join communicates ((n̂−n)·r_acc + r) ring elements; Π_join's own extractor splits a joined witness
back into the two input witnesses (κ = 0), so total error is Π_fs-core's.

**Corollary 7.7 (Π_fs-air, folding for committed AIR):**
`Ξ^{com-air} --Π_air+--> Ξ^{lin}_{n+1,n+1,µ,2r,β} --Π_fs--> Ξ^{lin}_{n+1,n+1,µ,r_acc,β}` (with the
accumulator entering at Π_fs). Folding scheme wrt str (all folded instances share one commitment
key); with r, n, ℓ, d, |C| = O(1): proof O(λ log²m/log λ) bits, prover O(mλ), verifier O(λ² + T_f).

**Appendix A — R1CS folding (Remark 7.8).** Ξ^{lin-} folding extends to R1CS:
- Ξ^{r1cs}_{m,m̃,ñ,r} (Def A.1): A,B,C ∈ Rq^{m×m̃}, D ∈ Rq^{ñ×m̃}, E ∈ Rq^{ñ×r}, W′ ∈ Rq^{m̃×r}
  with `A W′ ⊙ B W′ = C W′` and `D W′ = E` mod q (⊙ = coordinate-wise).
- Ξ^{com-r1cs} (Def A.2): commit W := G^{-1}_b(W′) under F_com: ((I, F_com, Y), W) ∈
  Ξ^{lin-}_{n_com,n_com,log m,r,β} plus the R1CS constraints on W′.
- Ξ^{gen-lin} (Def A.3, from [BC25b = LatticeFold+, Osa26], generalised to r columns and ℓ2 norm):
  instance (F_com, (M_i)_{i∈[t−1]}, Y, (v^{i,j})_{i∈[t],j∈[r]}, (r_i)_{i∈[t]}, W) with F stacked as
  `[F_com; r₀^T M₀; …; r_{t−2}^T M_{t−2}; r_{t−1}^T]`, RHS stacked as `[Y; (v^{0,j})_j; …;
  (v^{t−1,j})_j]`, v^{i,j} ∈ Rq^{2^µ} the claimed evaluation tables — each row encodes the
  sumcheck-style claim r_i^T M_i w_j = ⟨r_i, v^{i,j}⟩, i.e. Σ_z MLE[r_i](z)·MLE[M_i w_j](z) = … .
- `Π^{r1cs}` (Lemma A.6, from LatticeFold+ [BC25b ePrint App. A]): Ξ^{com-r1cs} →
  Ξ^{gen-lin}_{...,log m,r,β,4}, extraction vs Ξ^{sis}_{n_com,m,2β′}.
- `Π^{hom}` (Lemma A.7): homogenises r single-column Ξ^{gen-lin} instances with different r_{i,j}
  into instances sharing one r* — by batching the t·L sumcheck claims
  Σ_z MLE[r_{i,j}](z)·MLE[M_i w_j](z) = y_j with random c^i·ĉ^j ∈ F_{q^e} (error t·L/q^e; comm
  O(log m); prover O(tmL); verifier O(log m)).
- `Π_fs+` (Lemma A.8): (i) Π_hom → r_acc + r columns; (ii) reinterpret Ξ^{gen-lin} as Ξ^{lin-}
  (read F = [A; r₀^T M₀; …] off the statement); (iii) Π_fs-core; (iv) reinterpret back (legal by
  Lemma 7.6 structure preservation); (v) split the r_acc columns into r_acc single-column
  Ξ^{gen-lin} instances. Same O(λ log²m/log λ) / O(mλ) / O(λ²) complexities.
- Remark A.4: LatticeFold+ used r = 1 and the ∞-norm; SALSAA's ℓ2-canonical version works by
  substituting the norm in the RoK. Remark A.5: F_com may be structured (vSIS) or unstructured (SIS).

---

## 6 Soundness & Security

### 6.1 The universal extraction template

Every SALSAA RoK shares one two-transcript extraction argument (Lemmas 4.4, 4.6, 4.8, 4.12, 4.15,
4.20 and their corollaries):

1. Run the (wlog deterministic) cheating prover P* once on random challenges; rewind with fresh
   challenges for a second accepting transcript. Expected #invocations = (1−ϵ) + ϵ·(1 + 1/ϵ) = 2
   (expected polynomial time).
2. **Witness fork:** if the two witnesses differ (W′ ≠ W), both satisfy the linear relation with the
   same (H, F, Y) ⇒ H·F·(W′−W) = 0; any non-zero column w of W′−W solves F·w = 0 with
   ‖w‖ ≤ 2β′ over 2µ coordinates ⇒ a Ξ^{sis}_{n_com, 2µ, 2β′} (v)SIS break. (This is where the
   commitment binding / vSIS assumption enters.)
3. **Claim fork:** if W′ = W, the deterministic claims must hold except with the Schwartz–Zippel /
   univariate-agreement probability over the *fresh* challenges (the prover is committed to W before
   seeing them).

### 6.2 Error inventory (exact formulas, Setting 3.4 assumed)

| Lemma/Corollary | κ (knowledge error) | extraction target |
|---|---|---|
| Lem 4.2 Π_mle | 0 | Ξ^{mle} ↔ Ξ^{lin} (perfect) |
| Lem 4.4 Π_sum | (r_out·φ/e − 1 + µ·δ̂_h)/q^e | Ξ^{sum} ∪ Ξ^{sis}_{n_com,2µ,2β′} ← Ξ^{mle}_{t=2} |
| Rem 4.5 (no y1) | same | t = 1 variant |
| Lem 4.6 Π_batch | (n̂−n)/q^e | Ξ^{sis} ∪ Ξ^{lin}_{n̂,n,µ,r,β′} ← Ξ^{sum}_{n,n,µ,r,r,β′} |
| Cor 4.7 Π_batch+ | (n̂−n + r·φ/e − 1 + 2µ)/q^e | ← Ξ^{lin}_{n+1,n+1,µ,r,β′} |
| Lem 4.8 Π_norm | **0** | Ξ^{lin}_{n̂,n,µ,r,β} ← Ξ^{sum}_{n̂,n,µ,r,r,β′} (direct, no SIS case!) |
| Cor 4.9 Π_norm+ | (n̂−n + 2(r·φ/e + 2µ))/q^e | Ξ^{lin-⊗} ∪ Ξ^{sis} ← Ξ^{lin-⊗}_{n+1,n+1,µ,r,β′} |
| Lem 4.12 Π_bin | **0** | Ξ^{bin} ↔ Ξ^{sum} (direct) |
| Cor 4.13 Π_bin+ | (n̂−n + 2(r·φ/e + 2µ))/q^e | Ξ^{bin} ∪ Ξ^{sis} ← Ξ^{lin}_{n+1,n+1,µ,r,β′} |
| Lem 4.15 Π_ | (K+1)·m̄/q^e | Ξ^{sis} ∪ Ξ^{stair} ← Ξ^{sum}_{n̂,n,µ,r,r,β′} |
| Cor 4.16 Π_+ | ((K+1)m̄ + n̂−n + 2(r·φ/e + 2µ) − 1)/q^e | Ξ^{stair} ∪ Ξ^{sis} ← Ξ^{lin}_{n+1,n+1,µ,r,β′} |
| Lem 4.20 Π_air | (µ + m)/q^e | Ξ^{com-air} ∪ Ξ^{sis} ← Ξ^{sum}_{n̂,n,µ,2t,2+|C|,β′} |
| Cor 4.21 Π_air+ | (n̂−n + (|C|+2t+2)φ/e + m + (d+5)µ − 1)/q^e | Ξ^{com-air} ∪ Ξ^{sis} ← Ξ^{lin}_{n+1,n+1,µ,2t,β′} |

Error anatomy (useful for the FS/κ budget): each ΣΠ_sum piece contributes µ·δ̂_h (round univariates)
+ r_out·φ/e (the u-SZ over CRT slots); each Π_batch+ piece contributes n̂−n (the c-SZ) + r·φ/e + 2µ;
each application-local reduction contributes its own single-challenge SZ term ((K+1)m̄ for the
staircase, µ+m for AIR — the latter splits into µ for the eq(η,·) transition point and m for the
shift polynomial P₁ of degree m).

### 6.3 Wraparound-freeness (why integer checks mod q are sound)

The Trace-based checks read *integers* off residues mod q; this is only sound because Setting 3.4
imposes 4β′² < q:
- norm: |Σ_j w̄_j w_j| = ‖w_i‖²_{σ,2} ≤ β′² < q/2 — unique balanced lift;
- binariness: |Trace(t_i)| ≤ 2φ·‖cf(w_i)‖² ≤ 2·rad(f)·φ/f·‖w_i‖²_{σ,2} ≤ 2β′² < q/2
  (uses ‖cf(·)‖² ≤ (rad(f)/f)·‖·‖²_{σ,2}, rad(f) = 2, φ = f/2 — [KLNO25] Lemma 2);
- and each summand a(1−a) ≤ 0 with equality iff a ∈ {0,1} then forces binariness exactly.

### 6.4 Global statements

- **Theorem 5.1 (Π_as):** overwhelming correctness Ξ^{lin-⊗} → {0/1}; negligible knowledge error for
  Ξ^{lin-⊗}_{β′} ∪ {Ξ^{sis}_{param}} ← {0/1}. Extractors of all composed RoKs make O(1) expected
  queries each; O(log m) rounds ⇒ 2^{O(log m)} expected queries total — polynomial since
  m = poly(λ). Soundness reduces to vSIS for every parameter set `param = (n_com, m_i, β_i)`
  occurring in the extraction chain.
- **Corollaries 5.2 / 5.3:** PCS and AIR-SNARK inherit Theorem 5.1 exactly.
- **Theorem 6.6 (VDF argument Π_as-):** same shape for Ξ^{bin-⊗-stair}, from Cors. 4.13, 4.16 + Thm 5.1.
- **Lemma 6.7 (depth preservation):** Π_as- is depth-preserving (needed for sequentiality);
  Π_sum-rounds are split into 2-round coordinate-wise special-sound RoKs; challenge collisions are
  negligible because q^e = ω(poly(λ)).
- **Theorem 6.8 (VDF):** σ-sequential (σ = σ′ − p), ϵ-correct
  (ϵ = negl + T·n·φ·2^{log q−⌊log q⌋}/q), sound — under SIS-Seq_{R,q,m,n,σ′}, SIS∞_{R,q,m,n,1},
  and vSIS for all params. Soundness also uses injectivity of binary gadget decomposition.
- **Theorem 7.3 / Corollaries 7.5, 7.7, Lemmas A.6–A.8 (folding):** structure-preserving RoKs wrt
  the commitment-key map; knowledge errors negligible under SIS (unstructured keys) resp. vSIS
  (structured); Π_join's extractor splits witnesses with error 0.
- **Fiat–Shamir:** non-interactive versions obtained via FS with BLAKE3 (implementation); the
  round-by-round / granular-lemma accounting is not spelled out in the paper text beyond the
  standard "coordinate-wise special sound + challenge collision" argument of Lemma 6.7 — budget
  κ ≈ 2^{−100} overall (see §7) and keep the FS domain-separation strict (see §8 pitfalls).

### 6.5 What is *not* proven here (delegate to RPS/RnR docs)

Π_split, Π_fold, Π_b-decomp, Π_join, Π_⊗RP, Π_RP are inherited black boxes with their norm
bookkeeping in [KLNO24, KLNO25] (Table 1 of the paper summarises them; two rows are garbled in the
squeezed text). The lab implements them from the RoKoko/RPS lineage docs, not from this file.

---

## 7 Parameters & Concrete Efficiency

### 7.1 Implementation parameter choices (paper §8.1–8.2)

| Parameter | Value | Why |
|---|---|---|
| ring | power-of-two cyclotomic R = Z[ζ_f], f = 256, φ = 128 | NTT-friendly; binariness needs power-of-two (Lemma 4.11) |
| splitting | "almost split": Rq ≅ (F_{q²})^{φ/2}, i.e. **e = 2** | F_{q^e} = F_{q²} as sumcheck challenge set; batch across φ/2 CRT/NTT slots |
| modulus | q ≈ 2^50 (prime) | fits AVX-512-IFMA 52-bit lanes; 4β′² < q for binary witnesses up to 2^30 Zq elements |
| challenges for Π_fold | cyclotomic ring elements with **binary coefficients** | via [GLLO26 = Cyclo, App. B.2] analysis |
| security | λ = 128 vs Lattice Estimator [APS15] attacks; statistical soundness κ ≈ 2^{−100} (mainly NTT-slot size) | "estimator" mode in their codebase tracks norm growth during extraction |
| witness bitwidth (SNARK) | 10 bits per w entry | Table 3 setting |
| hardware | Dell PowerEdge XE9680, 2×32-core Xeon 8562Y+ 2.8 GHz, 2 TB DDR5-5600; Rust 1.95 nightly | Table 2 |

SNARK sizing convention: F structured n×m, n = Ajtai commitment rank, m = witness size in *ring
elements*; "#Zq" counts coefficients: #Zq = m·φ (e.g. m = 2^19, φ = 128 ⇒ #Zq = 2^26).

### 7.2 SNARK / PCS benchmarks (Table 3; |π| in KB)

| Scheme | 2^26: Comm / P / V / |π| | 2^28 | 2^30 |
|---|---|---|---|
| Brakedown | 36s / 3.21s / 0.703s / 49157 | 150s / 13s / 2.56s / 93767 | 605s / 48.6s / 2.96s / 181948 |
| Ligero | 39.9s / 3.11s / 0.196s / 7256 | 169s / 12.4s / 0.402s / 14383 | 717s / 50s / 0.846s / 28631 |
| FRI | 168s / 185s / 0.041s / 740 | – | – |
| WHIR | 147.1s / 1.8ms / 263 | 659s / 2.0ms / 296 | 3001s / 2.1ms / 324 |
| CMNW24 | – / – / – / 1546 | – | – / – / – / 5296 |
| HSS24 | 188s / 1.07s / 48640 | – | – |
| KLNO25 (RnR) | – / – / – / 2181 | – / 2604 | – / – / – / 3152 |
| Greyhound | 3.8s / 1.64s / 0.45s / 54 | 17.06s / 6s / 0.79s / 56 | 78.66s / 23.35s / 1.6s / 56 |
| **SALSAA** | **1.08s / 27.65s / 4.69ms / 1092** | **4.34s / 112.1s / 5.64ms / 1295** | **17.58s / 445.3s / 6.66ms / 1498** |
| RoKoko (φ=256) | 1.52s / 1.53s / 8.01ms / 164 | 5.85s / 3.40s / 8.11ms / 187 | 23.97s / 10.25s / 14.43ms / 187 |

Reading (paper §8.4): commitment & prover linear in witness size; every 4× witness increase adds
**two rounds** ⇒ fixed proof/verifier increment (logarithmic growth); proof ≈ **half of RnR**
[KLNO25]; RoKoko proof ~constant, verification slower; Greyhound semi-succinct (√ growth);
only WHIR verifies faster but with a several× slower prover and no native bounded-norm statements.
Greyhound's "relaxed extraction" (short denominators) is fine for plain PCS but SALSAA enforces the
exact claimed norm — required by the VDF and folding applications.

### 7.3 VDF benchmarks (Table 4; SALSAA VDF of Thm 6.8)

| | 2^28 | 2^30 | 2^31 |
|---|---|---|---|
| Comm | 4.01s | 15.85s | 31.68s |
| P | 113s | 7m24s | 14m46s |
| V | 6.62ms | 9.32ms | 12.24ms |
| |π| | 1176 KB | 1366 KB | 1554 KB |
| delay (DF) | 1.4s | 5.67s | 11.26s |
| #steps | 8192 | 32768 | 65536 |
| DF step | 0.171ms | 0.173ms | 0.172ms |

Papercraft reference (2^28): Comm+P 26m33s, V 5.10s, |π| 18940 KB, DF 38.54s, 43776 steps @
0.88ms; (2^30): Comm+P 1h56m26s, V 6.00s, |π| 29790 KB, DF 162.40s, 175104 steps @ 0.93ms — but
Papercraft's delay implementation is ~5× slower (no AVX-512/NTT-friendly layout), so normalise
before comparing. VDF parameter decisions: SIS∞ instance over-secure (one delay step is already
meaningful); per-step granularity fixed at ~200 µs so that the inner loop can't be multithreaded
(undesirable for a delay function). Observed: prover ≈ 80× the delay (incl. commitment);
verification < 0.5% of the delay; per-step cost constant across sizes.

### 7.4 Folding benchmarks (Table 5; Π_fs for Ξ^{lin-}, Cor. 7.5)

| | 2^26 | 2^28 | 2^30 |
|---|---|---|---|
| Comm | 1.10s | 4.37s | 18.64s |
| P | 3.92s | 16s | 62.86s |
| V | 0.44ms | 0.45ms | 0.45ms |
| |π| | 62 KB | 62 KB | 66 KB |

Each instance = accumulator (half the witness) + input (the other half). Verifier time and proof
size essentially witness-size-independent (fixed accumulator/message dimensions; only sumcheck
rounds add a log term); folding prover ≈ 1/7 of the SNARK prover at equal size (constant #RoKs per
step vs. the full composition). No direct comparison baseline (the only other efficient
implementation known is LatticeFold [BC24] as reported by Nethermind [Net24], end-to-end R1CS).
**AIR folding left as open direction** (significant undertaking) — this is the lab's A5 stretch goal.

### 7.5 Asymptotic summary

| Construction | proof | prover | verifier |
|---|---|---|---|
| Π_as (SNARK/PCS, Thm 5.1) | O(λ log³m/log λ) bits | O(λm) ring ops | O(λ² log m) ring ops |
| Π_as-air (Cor 5.3) | O(λ log³m/log λ) | O(λm) | O(λ² log m) |
| Π_fs-core / Π_fs / Π_fs-air (Thm 7.3, Cor 7.5/7.7) | O(λ log²m/log λ) | O(mλ) | O(λ²) (+T_f for AIR) |
| Π_fs+ for gen-lin/R1CS (Lem A.8) | O(λ log²m/log λ) | O(mλ) | O(λ²) |

(Reference values used by the paper's asymptotics: φ = Θ(λ·log m/log λ) [BDGL16] and
log q = O(log m).)

---

## 8 Implementation Notes (for the `lzk` Python core engine)

### 8.1 Data structures

- **Ring elements:** `lzk`'s Z_q[x]/(x^n + 1) with n = φ = 128, q ≈ 2^50 prime. The "almost
  split" condition is e = ord_f(q) = 2 for f = 256, i.e. q² ≡ 1 mod 256 with q ≢ 1 mod 256
  (q ≡ 127, 129 or 255 mod 256), giving Rq ≅ (F_{q²})^{64}. NTT is the *incomplete* / negative-wrapped
  one: no 256th root of unity lives in F_q (only gcd(256, q−1) = 2), so coefficients pair into 64
  slots of F_{q²} = F_q[t]/(t² − ζ_pair) where ζ_pair is an order-2-pair generator — exactly the
  setting of the `incomplete-rexl` library the authors use. Store elements as int64 numpy arrays of
  length 128 (balanced reps); slot form = 64 F_{q²} values (each two F_q limbs).
- **Row-tensor matrices F = F_0 • … • F_{µ−1}:** store the µ factors F_j ∈ Rq^{n×2} only (never
  materialise the n×2^µ product — that is the entire point). Row i of F is ⊗_j (F_j)[i,:].
  Mixed-product evaluation: f_row·e_r = Π_j ⟨(F_j)[i,:], (1−r_j, r_j)⟩ in O(µ).
- **Witness W ∈ Rq^{2^µ×r}:** flat array, row index = MSB-first bits (z ∈ {0,1}^µ ↔ j = Σ z_k·2^k).
- **Sumcheck state (Π_sum):** the DP table of f̃ over the shrinking hypercube: at round i an array
  indexed by {0,1}^{µ−i} — represent f̃ in CRT form (per-slot F_{q²} values) as a
  (2^{µ−i}, 64)-shaped array of F_{q²} (or (2^{µ−i}, 128) of F_q with slot pairing). Halving =
  combine pairs (z, z⊕e_i) → evaluate at r_i.
- **Challenges:** u, r_i ∈ F_{q²} (two F_q limbs); c, η_i, θ, α ∈ Rq; lifted r =
  CRT^{-1}(1_{φ/e}·r_i) = the "diagonal" element with all 64 slots equal.
- **h functions:** closures h(f0, f1) evaluated lazily; represent as (coefficient-vector, y-monomial)
  list — e.g. norm: [(1, y0·y1)]; bin: [(1, y1·(1°−y0))] i.e. (−1°, y1·y0)+(1°, y1); batch:
  [(MLE[(c^T H_F)^T] as length-m vector, y0)]; staircase: [(MLE[p]‖MLE[d] outer-style product as
  length-m vector via block structure, y0)]; AIR: eq/θ̃/selector-weighted coefficient vectors times
  f's y-monomials. Everything reduces to "length-m Rq vector ⊙ multilinear evaluation".
- **Trace/balanced Trace:** for power-of-2 cyclotomics Trace(ζ^0) = φ and Trace(ζ^ℓ) = 0 for
  0 < |ℓ| < φ, so Trace(Σ a_k ζ^k) = φ·a₀ — the balanced representative of φ·(constant coefficient)
  mod q. **Do not** compute it as a Galois orbit sum.

### 8.2 Module map A1–A5 onto `lzk`

| SALSAA piece | `lzk` reuse | new code |
|---|---|---|
| Rq arithmetic, NTT/CRT slots, F_{q²} | rings Z_q[x]/(x^n+1), NTT | slot pairing for e = 2; CRT^{-1}(1·r) lift; balanced Trace |
| MLE[w], e_z, eq | multilinear sumcheck / LDE utils | column-wise MLE for r > 1; MSB-first indexing check |
| Π_mle | tensor/LDE utils | append rows to (H, F, Y) incl. tensor factors |
| Π_sum (Fig. 2) | multilinear sumcheck engine (DP prover) | Rq-valued sumcheck with CRT-slot batching (u-fold), δ̂_h-degree messages in F_{q²}, single/dual final claims |
| Π_batch / Π_batch+ (Fig. 3) | Ajtai commitments, tensor eval | helper h = MLE[(c^T H_F)^T]·y0; verifier F·e_r via mixed product |
| Π_norm / Π_norm+ (Fig. 4) | ring-norm sumcheck | t = conjugate inner product; Trace(t) ≤ β² check; h = y0⊙y1 |
| Π_bin / Π_bin+ (Fig. 5) | — | 1° element; t = ⟨w, 1°−w⟩; Trace(t)=0; h = y1⊙(1°−y0) |
| Π_ / Π_+ (Fig. 6) | — | c₀/p/d/s from c; h = MLE[p](x_step)·MLE[d](x_inner)·y0; O(log K) geometric MLE eval |
| Π_air / Π_air+ (Fig. 7) | — | shift operator; θ̃; three h families; Eq. 3 column selectors |
| VDF (A4) | Ajtai commitments, gadget G^{-1} | G^{-1}/A chain eval; staircase+binary instance assembly; Π_as- composition |
| folding (A5) | — (needs Π_fold/Π_join/Π_b-decomp/Π_⊗RP from RPS lineage) | Π_fs-core composition, accumulator shape bookkeeping, structure map |
| Fiat–Shamir | `lzk` FS | BLAKE3-equivalent transcript hashing over Rq-serialised messages |

### 8.3 Complexity targets (to reproduce in Python, ignoring constant-factor gaps)

- Π_sum prover: O(δ_h·m·r) ring mults — for norm/batch/stair δ_h = 2 ⇒ ~2·m·r; the DP table is
  the memory hotspot (2^µ × slots); process in CRT form.
- Π_norm+ total prover O(m(n+r)+nr) — vs the old O_λ(m log m) convolution: **never** compute
  p0·p1 = (Σ w_i x^i)(Σ w̄_i x^{−i}); the whole point of A2.
- Π_air+ prover O((d+2)·µ·m·t): δ_h = (d+2)µ is *total* degree — the sumcheck DP on a degree-(d+2)µ
  polynomial costs µ× the degree-2 cases; budget accordingly for AIR.
- Verifier hot path: Π_⊗RP O(λ²) (not in A1–A5 core), F·e_r O(nµ), staircase d-row O(n̄).

### 8.4 Pitfalls (paper-faithful, in execution order)

1. **MSB-first bit order:** {0,1}^µ ≡ [2^µ] via j = Σ_k z_k·2^k with z_0 the *most* significant —
   the batching identity of Lemma 4.6 and the staircase x = (x_step, x_inner) split depend on it
   (x_step = the *first* log₂K variables).
2. **Conjugation is a ring automorphism:** MLE[W̄](r) = MLE[W](r̄); for power-of-two rings conjugation
   = coefficient index negation mod φ (x ↦ x^{φ−1}·... i.e. ζ^k ↦ ζ^{−k}). The second Ξ^mle claim
   is at r̄, NOT at r — and is *dropped entirely* (Remark 4.5) whenever h has no y1 (batch,
   staircase, AIR). Norm/bin DO need it.
3. **CRT-slot batching of the sumcheck:** messages g_i live in F_{q^e}[x], one univariate per round
   *after* the u-fold — do not run φ/e independent sumchecks; and the final check is
   a_µ = u^T·CRT(h(v0, v1)), evaluated in F_{q^e}.
4. **The lift CRT^{-1}(1_{φ/e}·r_i):** all slots equal — only this "diagonal" lift makes the
   conjugation identity of Fig. 2 step 10 work; arbitrary lifts break MLE[W̄](r) = MLE[W](r̄).
5. **Trace in the balanced representative:** Trace(t_i) ≤ β² / = 0 are *integer* comparisons;
   compute φ·cf₀(t_i) mod q then map to {−⌈q/2⌉+1,…,⌊q/2⌋}. Wraparound-freeness requires 4β′² < q —
   assert it in the parameter module.
6. **[1:K] notation:** [m:n] = {m,…,n−1}; the staircase middle condition is j ∈ [1:K] =
   {1,…,K−1}; the AIR transition applies to rows i ∈ [m−1] and the wrap row m−1 is *skipped* via
   (1 − eq(x, 1)).
7. **Binariness needs power-of-two rings only** (Lemma 4.11 orthogonality); the norm-check does not.
   Don't over-restrict A2.
8. **eq(x, 1) means 1 = (1,…,1) = bin(m−1)**, the *last* hypercube point — off-by-one here silently
   drops the wrong AIR row.
9. **θ̃ and θ^m via squarings:** θ^{2^j} for j ∈ [µ], one more squaring for θ^m (m = 2^µ) — not a
   linear power ladder.
10. **Staircase variable split:** x = (x_step, x_inner) — first log₂K variables step, last log₂n̄
    inner; K = m/n̄ must be a power of 2 and n̄ a power of 2; the verifier's MLE[d] eval is O(n̄)
    (d unstructured) — the only O(n̄) verifier cost in Π_+.
11. **Π_batch's s is over the *bottom* rows only** (Y_ below row n), while the output linear part
    keeps the top n rows; c has length n̂−n+1 starting at c⁰ = 1.
12. **Forking extractor order:** check W′ ≠ W first (vSIS break), then claim-level SZ; the
    knowledge-error sums are exact (§6.2) — keep them as tests.
13. **Folding accumulator shape:** after each Π_fs-core step the instance must be *exactly*
    Ξ^{lin}_{n+1,n+1,µ,r_acc,β} — track (n̂, n, r, β) through all six RoKs in the walk of §5.10;
    a stray extra row breaks the next step's Π_join/Π_norm+ shapes (the paper's §7.3 parameter
    walk is the checklist).
14. **Structure preservation:** none of the folding RoKs may touch F̄ — if your Π_⊗RP or Π_join
    implementation rewrites the commitment rows, the reinterpretation steps (ii)/(iv)/(v) of
    Lemma A.8 become unsound.
15. **Binary gadget digits for the VDF:** w_i = G^{-1}(−y_i) expands each coefficient of −y_i in
    base b = 2 with k = ⌈log_b q⌉ digits (must cover all of Z_q; the residual per-coefficient
    failure (b^k − q)/q = 2^{log q−⌊log q⌋}/q is exactly the ϵ term of Thm 6.8 — the generic
    k = ⌈log_b β⌉+2 of §3.5 is for norm-bounded witnesses, not for uniform mod-q inputs).
    Injectivity (VDF soundness) relies on digits being uniquely determined — don't
    "canonicalise" digits any other way.
16. **Table 1 garbles:** the Π_b-decomp / Π_⊗RP rows of the inherited-RoK table are partially
    illegible in the squeezed text (marked ✻ in §5.8); pull exact norm parameters from
    [KLNO24/25] before implementing the folding core.
17. **Parallelism:** the paper's implementation is single-threaded *by design* (FS synchronisation
    points); in Python keep the transcript-sequential structure and only parallelise within-round
    table halving if at all.
18. **κ budget:** overall statistical soundness target 2^{−100}; with e = 2, q^e = q² ≈ 2^100 —
    the per-challenge errors in §6.2 are then each ≤ (small)/q²; count the *total* number of
    challenges across the composition (O(log m) rounds × per-round challenges) in the estimator.

---

## 9 Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- **A1** (Π_sum + Π_batch core): ✅ — the RingSC engine
  (lzk.core.ringsc) implements the generalized ring sumcheck (LF+ §5.0
  layer / Π_sum's round machinery) with coefficient-form messages,
  transcript challenges and explicit protocol combiners; Π_batch's
  power-ladder row folding (fold_rows with c^i weights).
- **A2** (Π_norm+): ✅ — norm_conjugate_inner (the O(m) direct conjugate
  inner product — the paper's prover-efficiency trick vs RPS/RnR's
  O(m log m) convolution commitment), the balanced-trace check
  (Tr(t) ≤ nβ²), the degree-2 sumcheck, the full Π_norm+ composition with
  Π_mle row appends (norm_plus_prove/norm_plus_verify). Cheat test:
  tampered t rejected.
- **A3** (Π_bin + staircase): ✅ — Π_bin (Figure 5): t = ⟨w, 1°−w⟩ with
  Trace(t)=0 (Lemma 4.11's orthogonality argument — non-binary witnesses
  rejected in tests); the staircase RoK (Figure 6): the block-bidiagonal
  system with the c-ladder batched row d = Σc^ρA_ρ + c^{m̄+ρ}B_ρ, the
  geometric step powers p_j = (c^{m̄})^j, the target
  s = c₀·Y₀ + c^{K·m̄}c₀·Y₁, the degree-3 product sumcheck. Tamper: wrong s
  rejected.
- **A4** (VDF application): ✅ — the Papercraft-style chain
  w_i = G^{-1}(−y_i), y_{i+1} = Aw_i as a BINARY STAIRCASE ([G;A]
  block-bidiagonal, m̄=1) + Π_bin on the flat digit chain
  (vdf_prove/vdf_verify); wrong-output rejection tested.
- **A5** (committed-AIR folding): ✅ — Π_air (Figure 7): V = [W, shift(W)],
  the transition claim Σ eq(η,z)(1−eq(z,1))f(MLE[V])(z) = 0, the shift
  claim with the (θ^m − 1)eq(z,1) wrap correction, boundary claims, all in
  one batched degree-3 sumcheck with column openings; the folding step
  (linear fold + β growth) with folded-constraint verification.
- Simplifications: CRT-slot/subfield u-batching replaced by full-ring
  challenges; the tensor row-matrix F-factor structure flattened to rows;
  the Ξ^lin-⊗ interface carried by the lab instance model.

**(replacing the placeholder)**

- **A1** (Pi_sum + Pi_batch core): DONE — the RingSC engine (lzk.core.ringsc) implements the generalized ring sumcheck with coefficient-form messages, transcript challenges and explicit protocol combiners; Pi_batch's power-ladder row folding (fold_rows with c^i weights).
- **A2** (Pi_norm+): DONE — norm_conjugate_inner (the O(m) direct conjugate inner product — the paper's prover-efficiency trick vs RPS/RnR's O(m log m) convolution commitment), the balanced-trace check (Tr(t) <= n beta^2), the degree-2 sumcheck, the full Pi_norm+ composition with Pi_mle row appends (norm_plus_prove/norm_plus_verify). Cheat test: tampered t rejected.
- **A3** (Pi_bin + staircase): DONE — Pi_bin (Figure 5): t = <w, 1deg - w> with Trace(t)=0 (Lemma 4.11's orthogonality argument — non-binary witnesses rejected in tests); the staircase RoK (Figure 6): the block-bidiagonal system with the c-ladder batched row d = sum c^rho A_rho + c^{mbar+rho} B_rho, the geometric step powers p_j = (c^{mbar})^j, the target s = c0.Y0 + c^{K mbar} c0.Y1, the degree-3 product sumcheck. Tamper: wrong s rejected.
- **A4** (VDF application): DONE — the Papercraft-style chain w_i = G^{-1}(-y_i), y_{i+1} = A w_i as a BINARY STAIRCASE ([G;A] block-bidiagonal, mbar=1) + Pi_bin on the flat digit chain (vdf_prove/vdf_verify); wrong-output rejection tested.
- **A5** (committed-AIR folding): DONE — Pi_air (Figure 7): V = [W, shift(W)], the transition claim sum eq(eta,z)(1-eq(z,1)) f(MLE[V])(z) = 0, the shift claim with the (theta^m - 1) eq(z,1) wrap correction, boundary claims, all in one batched degree-3 sumcheck with column openings; the folding step (linear fold + beta growth) with folded-constraint verification.
- Simplifications: CRT-slot/subfield u-batching replaced by full-ring challenges; the tensor row-matrix F-factor structure flattened to rows; the Xi^lin-otensor interface carried by the lab instance model.
