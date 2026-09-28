# RoKoko: Lattice-based Succinct Arguments, a Committed Refinement — Deep Analysis & Implementation Spec

> Source paper: `papers_txt/rokoko.txt` (3688 lines, ASIACRYPT 2026 / ePrint 2026/575).
> This document is an implementation-grade transcription. Every protocol figure is transcribed
> step-by-step; all relations, lemmas, parameter tables and concrete numbers are captured.
> Gap-ledger IDs from the project plan: **R1** = core tensor RoK + projections, **R2** = committed
> refinement (recursive commitments + committed folding), **R3** = norm/slack management,
> **R4** = PCS composition, **R5** = SNARK end-to-end.

---

## 1. Metadata

| Field | Value |
|---|---|
| Title | RoKoko: Lattice-based Succinct Arguments, a Committed Refinement (a.k.a. "late baRoK") |
| Authors | Michael Klooß (KASTEL, Karlsruhe Institute of Technology); Russell W. F. Lai, Michal Osadnik, Lorenzo Tucci (Aalto University); Ngoc Khanh Nguyen (King's College London) |
| Venue | ePrint 2026/575, to appear in ASIACRYPT 2026 (per SALSAA's citation `[KLN+26]`) |
| Assumption | **vSIS** (vanishing SIS) over cyclotomic rings — structured, row-tensor SIS keys (Def. 1); plus a *conjectured* asymptotic JL scaling (Conjecture 1) for the asymptotic analysis |
| Headline | First lattice SNARK with **linear-time prover + polylog communication + polylog verifier** simultaneously: prover $O(m_w)$ ring ops, proof $O(\lambda\log^3 m_w/\log^2\lambda)$ bits, verifier $O(\lambda^3\log m_w/\log\lambda)$. Improves RoK&Roll (KLNO25) proofs by $\Theta(\log\lambda)$; ~110 KB concrete proofs with ~8–16 ms verification |
| Reference implementation | Rust, https://github.com/lattice-arguments/rokoko ; ring layer open-sourced as `incomplete-rexl` (https://github.com/lattice-arguments/rokoko/tree/main/incomplete-rexl, also on crates.io) |

**Three technical contributions (the "committed refinement"):**
1. **Committed folding** — instead of sending $O(\rho)$ cross-terms in the clear, commit to them and
   prove consistency later. Enables superconstant shrinking factor $\rho$ (up to $\rho=\lambda$) and
   hence $O(\log_\rho m_w)$ recursion rounds. (LaBRADOR did this in the *semi*-succinct setting;
   RoKoko preserves *succinct verification*.)
2. **Recursive commitments** — a $d$-layer Ajtai commitment `COM` (Fig. 1) whose *outermost*
   commitment has rank independent of the witness length; generalizes LaBRADOR's double
   (inner/outer) commitment.
3. **Sumcheck-driven structured recursion** — extends SALSAA's sumcheck framework to prove the
   much more complex constraints arising here (random projections, inner products, recursive
   commitment well-formedness) as *sumcheck* claims that compose with structured folding.

**Concrete headline numbers** (PCS over $2^{26}$ coefficients in $\mathbb{Z}_q$, $\lambda=128$,
$\kappa=2^{-100}$, single-threaded): 112 KB proof, 0.80 s commitment + 1.47 s proving, 8.12 ms
verification (text also cites 3.38 s "commit+prove" for one configuration). vs SALSAA: ~10×
smaller proofs, ~8× faster commit+prove, ~1.8× slower verifier. vs Greyhound: ~52× (laptop) to
~90× (server) faster verification, similar prover time, ~2.4× larger proofs.

---

## 2. Notation Table

Global conventions: $[n] := \{0,1,\dots,n-1\}$ (count from 0). Vectors lowercase bold
($\mathbf{v}$), matrices uppercase bold ($\mathbf{M}$). $\mathrm{vec}(\mathbf{M})$ = column-style
vectorisation; $\mathrm{reshape}_k(\mathbf{v})$ reshapes a vector into a $k$-column matrix with
$\mathrm{vec}(\cdot)$ inverse. Mixed-product property:
$\mathrm{vec}(\mathbf{ABC}) = (\mathbf{C}^{\top}\otimes\mathbf{A})\cdot\mathrm{vec}(\mathbf{B})$.
$\mathbf{A}\Vert\mathbf{B}$ = horizontal concatenation; $(\mathbf{A},\mathbf{B})$ = vertical
concatenation. $\mathbf{e}_i$ = $i$-th unit vector.
`matrix-from-rows`$((\mathbf{v}_j)_{j\in[k]})$ = matrix whose $j$-th row is $\mathbf{v}_j^\top$.
$\mathbf{M}[j,:]$ = $j$-th row. $\minpowtwo(x)$ = smallest power of two $\ge x$.

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter |
| $\kappa$ | knowledge error target (implementation: $\kappa\approx 2^{-100}$) |
| $f$ | conductor of the cyclotomic field $K=\mathbb{Q}(\zeta)$; implementation $f=256$ |
| $\varphi=\varphi(f)$ | degree of $K$; $\varphi=128$ in the implementation ($f=2^8$) |
| $\hat f$ | $f$ if $f$ odd, $f/2$ if $f$ even |
| $\mathrm{rad}(f)$ | radical of $f$ (product of distinct primes dividing $f$); $=2$ for power-of-two $f$ |
| $R=\mathcal{O}_K$ | ring of integers $=\mathbb{Z}[\zeta]$ of the $f$-th cyclotomic field |
| $R_q=R/qR$ | quotient ring, $q$ prime, unramified ($q\nmid f$) |
| $e$ | residue degree: $\Phi_f(X)$ splits mod $q$ into $\varphi/e$ irreducible factors of degree $e$; implementation $e=2$ |
| $\mathrm{trace}$ | field trace $\mathrm{trace}_{K/\mathbb{Q}}$, extended entry-wise to matrices; descends to $\mathrm{trace}:R_q\to\mathbb{Z}_q$ |
| $\mathrm{ct}(\cdot)$ | constant term of a ring element (used in the power-of-two optimisation, Remark 3) |
| $\bar{\cdot}$ | conjugation automorphism $\zeta\mapsto\zeta^{-1}$ (complex conjugation under $\sigma$), entry-wise |
| $\mathrm{cf}_b$ | coefficient embedding w.r.t. $\mathbb{Z}$-basis $b$; $b$ = **powerful basis** $\Rightarrow$ subscript omitted: $\mathrm{cf}$, $\mathrm{cf}^{-1}$ |
| $\mathrm{cf}^\vee$ | coefficient embedding w.r.t. the **trace-dual basis** $b^\vee$ (Lemma 1) |
| $b^\vee$ | trace-dual basis: $\mathrm{trace}(b_i\cdot b_j^\vee)=\delta_{i,j}\bmod q$ (exists for unramified $q$) |
| $\sigma$ | canonical embedding $K\to\mathbb{C}^\varphi$ |
| $\|\cdot\|_p$ | coefficient $\ell_p$ norm (over $\mathrm{cf}$); **default norm** $\|\cdot\|:=\|\mathrm{cf}(\cdot)\|_2$ |
| $\|\cdot\|_{\sigma,p}$ | canonical $\ell_p$ norm (over $\sigma$) |
| $\|\mathbf{B}\|_p$ | matrix norm = max column norm (both coefficient and canonical variants) |
| $\|c\|_{\mathrm{op}}$ | operator norm $= \sup_{t\neq 0}\|t\cdot c\|/\|t\|$ for $c\in R_q$ |
| $\gamma_{\mathcal{C}}$ | $\max_{c\in\mathcal{C}}\|c\|_{\mathrm{op}}$ for a challenge set $\mathcal{C}$ |
| $\mathcal{C}\subseteq R_q$ | challenge set: $c_1\neq c_2\Rightarrow c_1-c_2$ invertible mod $q$ |
| $G_\ell$, $G^{-1}_\ell$ | gadget matrix $G_{\ell}=I_m\otimes \mathbf{g}^\top$ with $\mathbf{g}=[1,b,\dots,b^{\ell-1}]^\top$; $G^{-1}_\ell$ = (balanced) digit decomposition; $b\ge\lceil\beta^{1/\ell}\rceil$ |
| $\mathrm{dcmp}_{m,\ell}(\beta)$ | norm transform for decomposition: input norm $\beta$, output norm $\beta'=\sqrt{m\varphi\ell}\cdot b/2$; inverse $\mathrm{cmp}$ |
| $\mathrm{NTT}$ | CRT isomorphism $R_q\to(\mathbb{F}_{q^e})^{\varphi/e}$, $a\mapsto(a\bmod f_j)_{j\in[\varphi/e]}$ |
| $\mathrm{MLE}[\mathbf{w}]$ | multilinear extension of $\mathbf{w}\in R_q^{2^\mu}$, $\mu=\log m$; $\{0,1\}^\mu\equiv[2^\mu]$ MSB-first |
| $\mathrm{eq}(\mathbf{x},\mathbf{z})$ | equality polynomial $\prod_{i\in[\mu]}(x_iz_i+(1-x_i)(1-z_i))$ |
| $\mathrm{tensor}(\mathbf{x})$ | $((1-x_0),x_0)\otimes\dots\otimes((1-x_{k-1}),x_{k-1})^\top\in R_q^{2^k}$; $\mathrm{MLE}[\mathbf{w}](\mathbf{x})=\mathrm{tensor}(\mathbf{x})^\top\mathbf{w}$ |
| $\otimes$ / $\bullet$ | Kronecker product / **row-wise tensor (row-tensor) product** of matrices with equal row counts; $\mathbf{A}\in R_q^{n\times 2^{\otimes\mu}}$ denotes $\mathbf{A}=\mathbf{A}_0\bullet\dots\bullet\mathbf{A}_{\mu-1}$, $\mathbf{A}_i\in R_q^{n\times2}$ |
| $\mathbf{A}_{n,2^\mu}$ | vSIS key: row-tensor matrix from the family $\mathcal{A}$, $n$ rows, $2^\mu$ columns |
| $k_{\mathrm{lin}},k_{\mathrm{lr}},k_{\mathrm{sc}}$ | number of committed-linear blocks / left-right inner-product constraints / sumcheck polynomials |
| $n$ | rows of the global linear constraint $\mathbf{A}$ |
| $m_w$ | number of rows of the main witness $\mathbf{W}$; $r$ = number of columns |
| $m_y,m_{y,i}$ | dimension of committed vector $\mathbf{Y}$ / $\mathbf{Y}_i$ (vectorised) |
| $m_x[\mathrm{par}_{\mathrm{com}}]$ | $\sum_{i\in[d-1]}n_i\ell_i$ — total auxiliary (decomposition) dimension |
| $\beta_w,\beta_x,\beta_y$ | norm bounds on $\mathbf{W}$, commitment aux $\mathbf{x}$, committed RHS $\mathbf{Y}$ |
| $\beta_x[\mathrm{par}_{\mathrm{com}}]$ | $\sqrt{\sum_{i\in[d-1]}\mathrm{dcmp}_{n_i,\ell_i}(q/2)^2}$ — derived aux norm |
| $\varrho$ | relaxation factor ($\varrho=1$ ⇒ non-relaxed; then $\mathbf{s}=\mathbf{1}$) |
| $\rho$ | per-round shrink factor of the composition (paper also uses $\rho=\log_2 r$ as column-log; disambiguate!) |
| $n_{\mathrm{rp}},m_{\mathrm{rp}}$ | random-projection height / width; JL parameters |
| $\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}},b,\kappa_{\mathrm{rp}}$ | JL norm-interval endpoints, wrap bound, failure probability |
| $n_{\mathrm{bat}}$ | batching width of $\Pi^{\mathrm{proj\text{-}f}}$ |
| $\delta_{\mathrm{sc}}$ | individual degree bound of sumcheck polynomials in $\Xi^{\mathrm{sum}}_{\mathrm{COM}}$ |
| $\mu=\log m_w$, $\rho=\log r$, $\nu=\log(m_wr)$ | variable counts (paper reuses $\rho$; see §5 conventions) |
| $\theta_a$ | $\mathbb{F}_{q^a}$-linear isomorphism $R_q\to(\mathbb{F}_{q^a})^{\varphi/a}$ for $a\mid e$ (NTT-based slot split) |
| $\Phi$ | random $\mathbb{F}_{q^a}$-linear batch map $R_q\to\mathbb{F}_{q^a}$, $\Phi=\boldsymbol\delta^\top\circ\theta_a$, $\boldsymbol\delta\leftarrow\mathbb{F}_{q^a}^{\varphi/a}$ |
| $\chi$ | JL entry distribution over $\{-1,0,1\}$ with $\Pr[0]=\tfrac12$, $\Pr[\pm1]=\tfrac14$ each |
| $\#$constraints$(\mathrm{par}_{\mathrm{com}})$ | $\sum_{i\in[d]}n_i$ — linear constraints to verify `COM` |

---

## 3. Algebraic Setting

### 3.1 Ring

- $K=\mathbb{Q}(\zeta)$ cyclotomic of conductor $f$, degree $\varphi=\varphi(f)$; $R=\mathcal{O}_K=\mathbb{Z}[\zeta]$;
  $q$ prime with $q\nmid f$ (unramified).
- **Powerful basis**: $b=(1,\zeta,\dots,\zeta^{\varphi-1})$ for prime-power $f$; for composite
  $f=\prod_i f_i^{e_i}$, the tensor product of the per-prime-power bases. `cf` (no subscript) uses
  the powerful basis. (For $f=2^k$ this is the usual power basis $\{1,\zeta,\dots,\zeta^{\varphi-1}\}$.)
- **Trace-dual basis** (Lemma 1, [KLNO25, Lem. 1]): for unramified $q$ and any $\mathbb{Z}$-basis
  $b$, there is $b^\vee$ with $\mathrm{trace}(b_i b_j^\vee)=\delta_{i,j}\bmod q$. Write
  $\mathrm{cf}^\vee$ for the dual coefficient embedding (powerful dual basis). **Key identity used
  everywhere**: for $\mathbf{u}\in\mathbb{Z}^\varphi$ and $w\in R$,
  $\mathrm{trace}(\mathrm{cf}^{-1}_\vee(\mathbf{u})\cdot w)=\langle\mathbf{u},\mathrm{cf}(w)\rangle\bmod q$.
- **NTT / CRT**: $\Phi_f(X)\equiv\prod_{j\in[\varphi/e]}f_j(X)\pmod q$ induces
  $\mathrm{NTT}:R_q\xrightarrow{\sim}(\mathbb{F}_{q^e})^{\varphi/e}$.
- **Subfield batching**: for $a\mid e$, view $\mathbb{F}_{q^e}$ as an $\mathbb{F}_{q^a}$-vector
  space of dimension $e/a$; this induces an $\mathbb{F}_{q^a}$-**linear** (not ring) isomorphism
  $\theta_a:R_q\to(\mathbb{F}_{q^a})^{\varphi/a}$. If $a=e$, $\theta_a$ is the NTT itself.
  $\mathbb{F}_{q^a}\subseteq R_q$ is used as challenge space in $\Pi^{\mathrm{lin}}$.

### 3.2 Norms and norm conversions (Lemmas 2, [KLNO24a Lem. 1])

With $\hat f=f$ ($f$ odd) / $f/2$ ($f$ even) and $\mathrm{rad}(f)$ the radical:

- $\|\mathbf{x}\|_2\le\sqrt{\mathrm{rad}(f)/\hat f}\,\|\mathbf{x}\|_{\sigma,2}$ (OCR ambiguity:
  SALSAA cites the tighter $\sqrt{\mathrm{rad}(f)/f}$; both hold).
- $\|\mathbf{x}\|_{\sigma,2}\le\sqrt{\hat f\cdot\mathrm{rad}(f)}\,\|\mathbf{x}\|_2$.
- **Power-of-two exact identity** (implementation-critical, $f=2^k$, $\varphi=f/2$):
  $\|\mathbf{x}\|_{\sigma,2}=\sqrt{\varphi}\cdot\|\mathrm{cf}(\mathbf{x})\|_2$ exactly (the
  canonical-embedding matrix satisfies $M^*M=\varphi I$), and
  $\mathrm{trace}(w\bar v)=\varphi\cdot\langle\mathrm{cf}(w),\mathrm{cf}(v)\rangle$.

**Default norm in RoKoko**: the *coefficient* $\ell_2$ norm $\|\cdot\|=\|\mathrm{cf}(\cdot)\|_2$
(SALSAA defaults to the *canonical* norm — beware when porting code).

### 3.3 Gadget decomposition

For $\mathbf{x}\in R^m$ of norm $\le\beta$: $\mathbf{y}:=G^{-1}_\ell(\mathbf{x})\in R^{m\ell}$ with
$\mathbf{x}=G_\ell(\mathbf{y})$, $G_\ell=I_m\otimes\mathbf{g}^\top$,
$\mathbf{g}=[1,b,\dots,b^{\ell-1}]^\top$, base $b\ge\lceil\beta^{1/\ell}\rceil$ (implementation:
$b=2^{16}$). Norm transform: $\mathrm{dcmp}_{m,\ell}(\beta)=\beta'=\sqrt{m\varphi\ell}\cdot b/2$
(so $\|\mathbf{y}\|\le\beta'$); inverse $\mathrm{cmp}$. Adaptive $\ell$: for target norm
$\le\beta\le q/2$ it suffices
$\ell\ge\big(-2\ln\alpha/W_{-1}(-e^{-u-1})-\varphi m^2\beta_w\ln\frac{2\beta^2}{\alpha}\big)$ …
(the paper's Lambert-$W$ bound; with $\beta\ge\sqrt{2\varphi m\ln q}$ one gets constant
$\ell\ge3$ suffices, hence $\ell=O(1)$ in asymptotics).

### 3.4 Implementation ring (Section 9)

- $f=256$ ($\varphi=128$), power-of-two cyclotomic, $q\approx2^{50}$ **prime with
  $q\equiv \varphi+1 \pmod f$** (⇒ residue degree $e=2$: $q^{2}\equiv1$, $q\not\equiv1$ mod $f$).
- "Almost-splitting": $R_q\simeq(\mathbb{F}_{q^2})^{64}$ — 64 NTT slots, each a degree-1 residue
  $(a_i+b_iX)\in\mathbb{Z}_q[X]/(X^2-\psi_i)$; ring multiplication = 64 independent quadratic
  products (incomplete NTT; no full $\varphi$-point NTT exists since $2\varphi\nmid q-1$ style
  conditions fail for $e>1$).
- Reasons for $e=2$: (i) knowledge error of RoKs is $\ge q^{-e}$ — $e=1$ (full split) is too
  weak; (ii) $\Pi^{\mathrm{fold\text{-}split}}$ needs a large low-norm challenge set — a fully
  splitting ring's largest subfield is $\mathbb{Z}_q$, too small. Rings splitting into large
  factors (LaBRADOR/Greyhound) kill NTT; instead sample **ternary challenges**
  $\{-1,0,1\}^{\varphi}$ with bias $p=1/3$: difference non-invertible with probability
  $\epsilon\approx\varphi/(e\,q^{e})\approx2^{-94}$ (heuristic of [ALS20, BL25 Lemma 32]),
  and reject challenges with large operator norm $\|\cdot\|_{\mathrm{op}}$ to further shrink
  extracted-witness norms.
- Almost-splitting lets $\mathbb{F}_{q^e}$ ($e=2$) serve as the sumcheck challenge set and
  allows batching across the $\varphi/e=64$ CRT slots.

---

## 4. Relations

All relations are parameterised by $(R,q)$ (omitted). $\Xi[\mathrm{par}]$ denotes the relation
with parameter list `par`. Recall $\mathbf{A}\leftarrow\mathrm{vSIS.Setup}(1^\lambda,1^N,1^M)$
samples the family $\mathcal{A}=(\mathbf{B}_{n,i})_{n\le N,i\le\log_2 M}$ defining
$\mathbf{A}_{n,2^\mu}:=\mathbf{B}_{n,0}\bullet\dots\bullet\mathbf{B}_{n,\mu-1}$.

### 4.1 vSIS assumption (Definition 1)

$\mathrm{Adv}^{\mathrm{vsis}}_{\mathrm{par},\mathcal{A}}(\lambda) =
\Pr\big[\mathbf{A}_{n,2^\mu}\mathbf{w}=0 \bmod q,\ 0\ne\|\mathbf{w}\|_2\le\beta,\ m=2^\mu\le M,\ n\le N\big]$
must be negligible (over $\mathcal{A}\leftarrow\mathrm{Setup}$ and the PPT adversary outputting
$(1^\lambda,1^N,1^M,\mathrm{st})$ then $\mathbf{w}$).

**Hardness heuristic (§8.1)**: model vSIS as SIS on the kernel lattice of dimension
$N:=\varphi n$ with volume scale $q^{1/n}$; with $q,\beta=\mathrm{poly}(\lambda)$ one fixes
$n=O(1)$ (module rank) and $\varphi=\Theta(\lambda)$; all recursive-commitment ranks assumed
$O(1)$.

### 4.2 Reduction of Knowledge (Definitions 2–3)

$\Pi=(P,V)$ with $P(\mathrm{ppar},\mathrm{stmt}_0,\mathrm{wit}_0)\to(\mathrm{stmt}_1,\mathrm{wit}_1)$
and $V(\mathrm{ppar},\mathrm{stmt}_0)\to\mathrm{stmt}_1$ interacting.
$\epsilon$-**complete** for $\Xi_0\to\Xi_1$; **knowledge sound** from $\Xi^{\mathrm{ext}}\leftarrow\Xi_1$
with knowledge error $\kappa$ if a black-box expected-poly-time extractor $\mathrm{Ext}$ succeeds
with probability $\epsilon-\kappa$ (strict bound; extractor handles unbounded provers, so
adaptive security is immediate). Arrow convention: completeness left-to-right
($\Xi_{\mathrm{in}}\to\Xi_{\mathrm{out}}$), extraction right-to-left
($\Xi_{\mathrm{ext}}\leftarrow\Xi_{\mathrm{out}}$); a disjunction
$\Xi^{\mathrm{sis}}\vee\Xi^{\mathrm{lin}}_{\mathrm{COM}}\leftarrow\Xi^{\mathrm{lin\text{-}rel}}_{\mathrm{COM}}$
means the extractor outputs a witness for either branch.

### 4.3 Recursive Ajtai commitment `COM` (Figure 1) — [R2 core]

Parameters $\mathrm{par}_{\mathrm{com}}=(d,\mathbf{l},\mathbf{n})$:
depth $d$, gadget lengths $\mathbf{l}=(\ell_0,\dots,\ell_{d-2})$ ($d-1$ of them), output
dimensions $\mathbf{n}=(n_0,\dots,n_{d-1})$, and norm bounds
$\boldsymbol\beta=(\beta_0,\dots,\beta_{d-1})$. Shorthand
$\mathrm{COM}_{\mathrm{par}_{\mathrm{com}},\beta_y,\beta_x}$ sets $\beta_0=\beta_y$,
$\beta_1=\dots=\beta_{d-1}=\beta_x$.

```
Com_parcom(ck, w ∈ R^{2^μ}) → (com, aux):                     Verify_parcom,β(ck, w ∈ R^{2^μ}, com, aux):
  (n_i)_{i∈[d]} := n                                            y* := com
  y := A_{n0,2^μ} · w mod q                                     b0 := ∥w∥₂ ≤ β0
  if d = 1:                                                     if d = 1:
     return (y, ∅)                                                 return b0 ∧ (y* = A_{n0,2^μ}·w mod q)
  (ℓ_i)_{i∈[d−1]} := l                                          else:
  e := G^{-1}_{ℓ0}(y)                                              (ℓ_i)_{i∈[d−1]} := l
  x := e ∥ 0 ∈ R^{minpowtwo(ℓ0 n0)}   // zero-pad                 l' := (ℓ1,…,ℓ_{d−2});  n' := (n1,…,n_{d−1})
  l' := (ℓ1,…,ℓ_{d−2});  n' := (n1,…,n_{d−1})                     (x*, x) := aux
  (y*, x*) := Com_{d−1,l',n'}(ck, x)                               b1 := A_{n0,2^μ}·w = (G_{ℓ0} ∥ 0)(x)   [mod q]
  aux := (x*, x)                                                   b2 := Verify_{d−1,l',n',β'}(ck, x, y*, x*)
  return (y*, aux)                                                                    // β' = (β1,…,β_{d−1})
                                                                   return b0 ∧ b1 ∧ b2
```

Semantics: level 0 commits $\mathbf{w}$ (length $2^\mu$, norm $\le\beta_0$) under vSIS key
$\mathbf{A}_{n_0,2^\mu}$; the level-0 commitment $\mathbf{y}$ is decomposed
$\mathbf{e}=G^{-1}_{\ell_0}(\mathbf{y})$, zero-padded to the next power of two
$\minpowtwo(\ell_0n_0)$, and **recursively committed**; the final (deepest) output is `com`.
Derived quantities:
$m_x[\mathrm{par}_{\mathrm{com}}]=\sum_{i\in[d-1]}n_i\ell_i$;
$\beta_x[\mathrm{par}_{\mathrm{com}}]=\sqrt{\sum_{i\in[d-1]}\mathrm{dcmp}_{n_i,\ell_i}(q/2)^2}$;
$\#$constraints$(\mathrm{par}_{\mathrm{com}})=\sum_{i\in[d]}n_i$.

**Lemma 4 (binding break → SIS break)**: given two openings
$(\mathbf{w}_b,\mathbf{x}_b)_{b\in[2]}$, $\mathbf{w}_0\ne\mathbf{w}_1$, for the same `com`, one
efficiently obtains a $\Xi^{\mathrm{sis}}$ witness for parameters
$\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com}},m_y,\boldsymbol\beta]
=\{(n_0,m_y,2\beta_y)\}\cup\{(n_{i+1},\ell_i n_i,2\beta_{x,i})\}_{i\in[d-1]}$.
(Proof: unroll the recursion; let $i^*$ be the deepest level where the two openings differ;
$\mathbf{z}:=\mathbf{x}^{(i^*)}_0-\mathbf{x}^{(i^*)}_1\ne0$ with $\|\mathbf{z}\|\le2\beta_{i^*}$
lies in the kernel of the level-$i^*$ key.)

### 4.4 Committed-linear relation $\Xi^{\mathrm{lin}}_{\mathrm{COM}}$ — [R1]

- **Parameters**:
  $\mathrm{par}=(\mathrm{ck}=\mathcal{A},\ k_{\mathrm{lin}},\ k_{\mathrm{lr}},\ n,\ m_w,\ r,\ \beta_w,\ (\mathrm{par}_{\mathrm{lin},i})_{i\in[k_{\mathrm{lin}}]},\ \varrho)$
  where $\mathrm{par}_{\mathrm{lin},i}=(n_i,\mathrm{par}_{\mathrm{com},i},m_{y,i},\beta_{x,i},\beta_{y,i})$.
- **Statement**:
  $\mathrm{stmt}=\big((\mathrm{com}_i,\mathbf{F}_i,\mathbf{H}_i)_{i\in[k_{\mathrm{lin}}]},\ (\boldsymbol\ell_j,\mathbf{r}_j,t_j)_{j\in[k_{\mathrm{lr}}]},\ \mathbf{A},\mathbf{b}\big)$
  with $\mathbf{F}_i\in R_q^{n_i\times m_w}$, $\mathbf{H}_i\in R_q^{n_i\times m_{y,i}}$,
  **$\mathbf{F}_0\in\mathcal{A}$ is a vSIS commitment key**;
  $\boldsymbol\ell_j\in R_q^{m_w}$, $\mathbf{r}_j\in R_q^{r}$, $t_j\in R_q$;
  $\mathbf{A}\in R_q^{n\times\sum_i m_{y,i}\cdot r}$, $\mathbf{b}\in R_q^n$.
- **Witness**: $\mathrm{wit}=(\mathbf{W}\in R^{m_w\times r},\ (\mathbf{Y}_i\in R^{m_{y,i}\times r},\ \mathbf{x}_i\in R^{m_x[\mathrm{par}_{\mathrm{com},i}]})_{i\in[k_{\mathrm{lin}}]},\ \mathbf{s}\in R^r)$.
- **Constraints**:
  1. $\forall i\in[k_{\mathrm{lin}}]$: $\mathbf{F}_i\mathbf{W}=\mathbf{H}_i\mathbf{Y}_i \bmod q$;
  2. $\forall i$: $\mathrm{COM.Verify}_{\mathrm{par}_{\mathrm{com},i},\beta_{y,i},\beta_{x,i}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_i),\mathrm{com}_i,\mathbf{x}_i)=1$;
  3. $\forall i$: $\|\mathrm{vec}(\mathbf{Y}_i)\|\le\beta_{y,i}$, $\|\mathbf{x}_i\|\le\beta_{x,i}$;
  4. $\forall j\in[k_{\mathrm{lr}}]$: $\boldsymbol\ell_j^{\top}\mathbf{W}\mathbf{r}_j=t_j\bmod q$;
  5. $\mathbf{A}\cdot(\mathrm{vec}(\mathbf{Y}_i))_{i\in[k_{\mathrm{lin}}]}=\mathbf{b}\bmod q$;
  6. $\|\mathbf{W}\cdot\mathrm{diag}(\mathbf{s})\|_2\le\beta_w$ and $\|\mathrm{diag}(\mathbf{s})\|_{\mathrm{op},2}\le\varrho$.

$\mathbf{W}$ is *implicitly committed*: constraint 1 with $\mathbf{F}_0\in\mathcal{A}$ binds
$\mathbf{H}_0\mathbf{Y}_0$ as an (outer) commitment of $\mathbf{W}$ — the first layer binds the
**columns of $\mathbf{W}$ individually** under the same key, enabling short random combinations
of columns. $\Xi^{\mathrm{lin\text{-}rel}}_{\mathrm{COM}}$ denotes the same relation when
$\varrho>1$ is allowed (slack vector $\mathbf{s}$); if $\varrho=1$ take $\mathbf{s}=\mathbf{1}$.

### 4.5 Functional-sumcheck relation $\Xi^{\mathrm{sum}}_{\mathrm{COM}}$

- **Parameters**: $\mathrm{par}=(\mathrm{ck}=\mathcal{A},\ k_{\mathrm{sc}},\ n,\ m_w,\ r,\ \mathrm{par}_{\mathrm{com}},\ m_y,\ \beta_w,\ \beta_x,\ \beta_y,\ \delta_{\mathrm{sc}})$,
  with $m_w\cdot r=2^\nu$ a power of two.
- **Statement**: $\mathrm{stmt}=(\mathrm{com},\ \mathbf{F}\in R_q^{n\times m_w},\ \mathbf{H}\in R_q^{n\times m_y},\ (f^{(i)}_{\mathrm{sc}})_{i\in[k_{\mathrm{sc}}]})$
  where $\mathbf{F}\in\mathcal{A}$ is a vSIS key, and each
  $f^{(i)}_{\mathrm{sc}}\in(R_q[\mathbf{y}])[x_0,x_1]$ is a polynomial in the two "evaluation"
  variables $x_0,x_1$ over the polynomial ring $R_q[y_0,\dots,y_{\nu-1}]$; for
  $x_0,x_1\in R_q[\mathbf{y}]_{\le1}$ (multilinear), $f^{(i)}_{\mathrm{sc}}(x_0,x_1)\in R_q[\mathbf{y}]_{\le\delta_{\mathrm{sc}}}$.
- **Witness**: $\mathrm{wit}=(\mathbf{W}\in R^{m_w\times r},\ \mathbf{Y}\in R^{m_y\times r},\ \mathbf{x}\in R^{m_x[\mathrm{par}_{\mathrm{com}}]})$.
- **Constraints**:
  1. $\mathbf{FW}=\mathbf{HY}\bmod q$;
  2. $\mathrm{COM.Verify}_{\mathrm{par}_{\mathrm{com}},\beta_y,\beta_x}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}),\mathrm{com},\mathbf{x})=1$;
  3. $\sum_{i\in[k_{\mathrm{sc}}]}\ \sum_{\mathbf{z}\in\{0,1\}^{\nu}} f^{(i)}_{\mathrm{sc}}\big(\mathrm{MLE}[\mathrm{vec}(\mathbf{W})],\ \overline{\mathrm{MLE}[\mathrm{vec}(\mathbf{W})]}\big)(\mathbf{z})=0\bmod q$
     — i.e. each sumcheck claim sums to zero over the Boolean hypercube of $\nu=\log(m_wr)$
     variables, with the two evaluation arguments instantiated at the MLE of the (packed) witness
     and of its conjugate;
  4. $\|\mathbf{W}\|_2\le\beta_w$, $\|\mathrm{vec}(\mathbf{Y})\|_2\le\beta_y$, $\|\mathbf{x}\|_2\le\beta_x$.

### 4.6 SIS-family relation $\Xi^{\mathrm{sis}}$

- Parameters $\mathrm{par}=(\mathrm{ck}=\mathcal{A},\{\mathrm{par}_i\}_{i\in[T]})$,
  $\mathrm{par}_i=(n_i,m_{w,i},\beta_{w,i})$, $m_{w,i}=2^{\mu_i}$.
- Statement: $\varepsilon$ (empty). Witness: $\mathbf{w}\in R^{m_{w,i}}$ for some $i$.
- Constraints: $\exists i$: $\mathbf{A}_{n_i,m_{w,i}}\mathbf{w}=0\bmod q$ and
  $0\ne\|\mathbf{w}\|_2\le\beta_{w,i}$.

### 4.7 Packing (§3.6, Lemma 3) — [R1/R2 glue]

$\mathrm{pack}:(R_q^{m_0},\dots,R_q^{m_{k-1}})\to R_q^{m'}$ with each $m_i$ a power of two,
$m'=\sum_i m_i$, $\hat m=2^{\lceil\log m'\rceil}\ge m'$: **sort inputs by decreasing dimension**,
concatenate, zero-pad to $\hat m$ (padding $<\hat m/2$ of the vector). Offset of block $i$:
$\omega_i=\sum_{j<i}m_j$ (a multiple of $m_i$).
**Lemma 3**: with $p_i=\mathrm{bin}(\omega_i/m_i)\in\{0,1\}^{\mu-\mu_i}$ (the block-prefix),
$\mathrm{MLE}[\mathrm{pack}(\dots)](p_i,\mathbf{z})=\mathrm{MLE}[\mathbf{w}_i](\mathbf{z})$ —
i.e. sub-vector MLEs are *prefix-restricted* MLEs of the packed vector. This is what lets every
sub-witness ($\tilde{\mathbf{w}}$, $\mathbf{Y}_i$, $\mathbf{x}_i$, …) be addressed inside a single
sumcheck over the packed vector via $\mathrm{eq}(p_i,\cdot)$ selectors.

---

## 5. Protocols

Round architecture (each full round):
$\Pi^{\mathrm{fold\text{-}split}}\circ\Pi^{\mathrm{proj}}:\ \Xi^{\mathrm{lin}}_{\mathrm{COM}}\to\Xi^{\mathrm{sum}}_{\mathrm{COM}}$
followed by
$\Pi^{\mathrm{lin}}:\ \Xi^{\mathrm{sum}}_{\mathrm{COM}}\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}$,
with $\Pi^{\mathrm{proj}}\in\{\Pi^{\mathrm{proj\text{-}c}},\Pi^{\mathrm{proj\text{-}f}},\Pi^{\mathrm{proj\text{-}fl}}\}$.
($\Pi'\circ\Pi$ = apply $\Pi$ first.) After each round $m_w\mapsto m_w/\rho$ (effective $\rho$ —
smaller than the folding width $r$ because the witness accumulates projection images, aux data,
decomposition overhead; see footnote 7 of the paper).

### 5.0 Johnson–Lindenstrauss lemmas (Lemmas 5–6) — [R3]

**Lemma 5** ([BS23]): $\chi$ over $\{-1,0,1\}$ with $\Pr[0]=1/2$, $\Pr[\pm1]=1/4$. There are
$n_{\mathrm{rp}},\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}},b$ with, for any $\mathbf{w}\in\mathbb{Z}^{m_{\mathrm{rp}}}\setminus\{0\}$:
$\Pr[\|\mathbf{Jw}\|_2/\|\mathbf{w}\|_2\notin[\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}}]\mid \mathbf{J}\leftarrow\chi^{n_{\mathrm{rp}}\times m_{\mathrm{rp}}}]\le\kappa_{\mathrm{rp}}$,
and for $0<\theta\le q/b$, $\|\mathbf{w}\|_2\ge\theta$, $\mathbf{w}\in[\pm q/2]^{m_{\mathrm{rp}}}$:
$\Pr[\|\mathbf{Jw}\bmod q\|_2\le\alpha_{\mathrm{rp}}\theta]\le\kappa_{\mathrm{rp}}$.
**Concrete ($\kappa_{\mathrm{rp}}=2^{-128}$)**: $n_{\mathrm{rp}}=256$, $\alpha_{\mathrm{rp}}=30$,
$\beta_{\mathrm{rp}}=337$, $b=125$.

**Lemma 6 (structured JL)**: for $\mathbf{W}\in\mathbb{Z}^{m_w\times r}$,
$\mathbf{V}:=(I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{J})\mathbf{W}$:
$\Pr[\|\mathbf{V}\|_2/\|\mathbf{W}\|_2\notin[\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}}]]\le\kappa_{\mathrm{rp}}\cdot r\,m_w/m_{\mathrm{rp}}$
and (wrap-around form) $\Pr[\|\mathbf{V}\bmod q\|_2\le\alpha_{\mathrm{rp}}\theta]\le\kappa_{\mathrm{rp}}\cdot m_w/m_{\mathrm{rp}}$.
Proof = per-column/per-chunk application of Lemma 5 + union bound.

**Conjecture 1** (asymptotic scaling, used only for asymptotics):
$n_{\mathrm{rp}}(\kappa)=\Theta(\log(1/\kappa))$ with
$\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}},b=\Theta(\sqrt{\log(1/\kappa)})$ (second-moment +
Bernstein-type concentration; matches $\chi^2$ behaviour of Gaussian JL).

### 5.1 $\Pi^{\mathrm{proj\text{-}c}}$ — committed coarse random projection (Figure 2) — [R3]

Self-reduction $\Xi^{\mathrm{lin}}_{\mathrm{COM}}\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}$,
$k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+1$; used while $m_w\ge m_{\mathrm{rp}}$
(requires $m_{\mathrm{rp}}\mid m_w$). Eliminates extraction-side norm slack.

**Protocol (Figure 2), subscript $\Pi^{\mathrm{proj\text{-}c}}_{\ell,\mathrm{par}_{\mathrm{com}}}$:**

Prover $P(\mathrm{stmt},\mathrm{wit})$:
1. Parse $\mathrm{stmt}=((\mathrm{com}_i,\mathbf{F}_i,\mathbf{H}_i)_{i\in[k_{\mathrm{lin}}]},(\boldsymbol\ell_j,\mathbf{r}_j,t_j)_{j\in[k_{\mathrm{lr}}]},\mathbf{A},\mathbf{b})$,
   $\mathrm{wit}=(\mathbf{W},(\mathbf{Y}_i,\mathbf{x}_i)_{i\in[k_{\mathrm{lin}}]})$
   (instance of $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\beta_w,(\dots)_{i\in[k_{\mathrm{lin}}]}]$).
2. $\mathbf{V}:=(I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{J})\cdot\mathbf{W}\in R^{(m_w\,n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$.
3. $\mathbf{Y}_{k_{\mathrm{lin}}}:=G^{-1}_{\ell}(\mathbf{V})\in R^{(\ell\,m_w n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$.
4. $(\mathrm{com}_{k_{\mathrm{lin}}},\mathbf{x}_{k_{\mathrm{lin}}}):=\mathrm{Com}_{\mathrm{par}_{\mathrm{com}}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_{k_{\mathrm{lin}}}))$.
5. Set the new linear block: $F_{k_{\mathrm{lin}}}:=I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{J}$,
   $H_{k_{\mathrm{lin}}}:=G_\ell$ (so the new constraint reads
   $(I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{J})\mathbf{W}=G_\ell\mathbf{Y}_{k_{\mathrm{lin}}}\bmod q$);
   $n_{k_{\mathrm{lin}}}:=m_w n_{\mathrm{rp}}/m_{\mathrm{rp}}$,
   $\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}}=\mathrm{par}_{\mathrm{com}}$,
   $m_{y,k_{\mathrm{lin}}}:=\ell\cdot n_{k_{\mathrm{lin}}}$,
   $\beta_{x,k_{\mathrm{lin}}}:=\beta_x$, $\beta_{y,k_{\mathrm{lin}}}:=\mathrm{dcmp}_\ell(\beta_{\mathrm{rp}}\beta_w)$.
6. $\mathrm{wit}':=(\mathbf{W},(\mathbf{Y}_i,\mathbf{x}_i)_{i\in[k_{\mathrm{lin}}+1]})$;
   $\mathrm{stmt}':=((\mathrm{com}_i,\mathbf{F}_i,\mathbf{H}_i)_{i\in[k_{\mathrm{lin}}+1]},(\boldsymbol\ell_j,\mathbf{r}_j,t_j)_{j\in[k_{\mathrm{lr}}]},\mathbf{A},\mathbf{b})$;
   output the $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}+1,\dots]$ instance.

Verifier $V(\mathrm{stmt})$:
1. Sample $\mathbf{J}\leftarrow\chi^{n_{\mathrm{rp}}\times m_{\mathrm{rp}}}$ and send it.
2. Receive $\mathrm{com}_{k_{\mathrm{lin}}}$; output $\mathrm{stmt}'$ (with the new block as above).

**Communication**: $|\mathrm{com}_{k_{\mathrm{lin}}}|$ only.

**Lemma 7.**
- *Completeness* $\epsilon=\kappa_{\mathrm{rp}}\cdot\varphi r m_w/m_{\mathrm{rp}}$ for
  $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}]\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}+1]$
  with $\mathrm{par}_{\mathrm{lin},k_{\mathrm{lin}}}=(m_w\tfrac{n_{\mathrm{rp}}}{m_{\mathrm{rp}}},\ \mathrm{par}_{\mathrm{com}},\ \ell m_w\tfrac{n_{\mathrm{rp}}}{m_{\mathrm{rp}}},\ \beta_x,\ \mathrm{dcmp}_\ell(\beta_{\mathrm{rp}}\beta_w))$.
- *Knowledge soundness*, $\kappa=\kappa_{\mathrm{rp}}\cdot\varphi m_w/m_{\mathrm{rp}}$, for
  $\Xi^{\mathrm{sis}}[\mathrm{par}_{\mathrm{sis}}]\ \vee\ \Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\ \mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}},\ (n_i,\mathrm{par}_{\mathrm{com},i},m_{y,i},\beta'_{x,i},\beta'_{y,i})_{i\in[k_{\mathrm{lin}}]}]\
  \leftarrow\ \Xi^{\mathrm{lin\text{-}rel}}_{\mathrm{COM}}[k_{\mathrm{lin}}+1,\dots,\beta'_w,\dots,\varrho']$,
  where $\mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}}<q/b$ and
  $\mathrm{par}_{\mathrm{sis}}\supseteq\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}},m_{y,k_{\mathrm{lin}}},\beta'_{y,k_{\mathrm{lin}}},\beta'_{x,k_{\mathrm{lin}}}]\cup\{(n_0,m_w,2\beta'_w\varrho')\}$.
- *Efficiency*: prover $O(m_wr n_{\mathrm{rp}})$ $R_q$-ops + the commitment
  $\mathrm{com}_{k_{\mathrm{lin}}}$; verifier $O(n_{\mathrm{rp}}m_{\mathrm{rp}})$ samples from
  $\chi$; communication $|\mathrm{com}_{k_{\mathrm{lin}}}|$.

**Key point (strict norms)**: the new $\mathbf{Y}_{k_{\mathrm{lin}}}$ carries a *slack-free*
norm bound $\beta_{y,k_{\mathrm{lin}}}=\mathrm{dcmp}(\beta_{\mathrm{rp}}\beta_w)$; since the JL
map preserves norms within $[\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}}]$ on every chunk, a short
projection image certifies $\|\mathbf{W}\|\le\mathrm{cmp}(\beta'_{y})/\alpha_{\mathrm{rp}}$
*without* the $\varrho$ slack.

### 5.2 $\Pi^{\mathrm{proj\text{-}f}}$ — committed fine random projection (Figure 3) — [R3]

Self-reduction $\Xi^{\mathrm{lin}}_{\mathrm{COM}}\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}$ with
$k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+2$, $n\mapsto n+n_{\mathrm{bat}}$; used once
$m_w<m_{\mathrm{rp}}$ (dimension condition $m_{\mathrm{rp}}\mid\varphi m_w$; compresses on
coefficients: $\dim_{\mathbb{Z}}(\mathbf{w})=\varphi m_w$, so compression works while
$\varphi m_{\mathrm{rp}}>n_{\mathrm{rp}}$ — up to a factor $\varphi$ more than coarse).

**Core identity** (trace-dual lift): for $\mathbf{u}\in\mathbb{Z}^{\varphi}$, $w\in R$:
$\mathrm{trace}(\mathrm{cf}^{-1}_\vee(\mathbf{u})\cdot w)=\langle\mathbf{u},\mathrm{cf}(w)\rangle\bmod q$.
The projection is applied at the coefficient level:
$\mathrm{trace}(\mathbf{V})=\mathbf{J}\cdot\mathrm{cf}(\mathbf{W})$ (per chunk), equivalently
$\mathbf{V}=(I_{\varphi m_w/m_{\mathrm{rp}}}\otimes\mathrm{cf}^{-1}_\vee(\mathbf{J}^{\top\top}))\mathbf{W}$
where $\mathrm{cf}^{-1}_\vee(\mathbf{J})$ denotes the entry-wise trace-dual lift of $\mathbf{J}$'s
rows (see implementation note §8.6 for a type-safe reformulation).

**Protocol (Figure 3), $\Pi^{\mathrm{proj\text{-}f}}_{n_{\mathrm{bat}},\ell,\ell',\mathrm{par}_{\mathrm{com}},\mathrm{par}'_{\mathrm{com}}}$:**

Prover:
1. Parse $\mathrm{stmt},\mathrm{wit}$ as in $\Pi^{\mathrm{proj\text{-}c}}$.
2. $\mathbf{V}:=(I_{\varphi m_w/m_{\mathrm{rp}}}\otimes\mathrm{cf}^{-1}_\vee(\mathbf{J}^{\top})^{\top})\cdot\mathbf{W}\in R^{(\varphi m_w\,n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$
   (lifted fine projection).
3. $\mathbf{V}_{\mathrm{tr}}:=\mathrm{trace}(\mathbf{V})\in\mathbb{Z}^{(\varphi m_w n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$
   (the integer projection image; trace collapses the $\varphi$-blocks — i.e. the JL projection of
   the coefficient embedding).
4. $\mathbf{V}_{\mathrm{emb}}:=\mathrm{cf}^{-1}(\mathbf{V}_{\mathrm{tr}})\in R^{(m_w\,n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$
   (re-embed projected integers into ring elements, $\varphi$ integers → 1 element).
5. $\mathbf{Y}_{k_{\mathrm{lin}}}:=G^{-1}_{\ell}(\mathbf{V}_{\mathrm{emb}})\in R^{(\ell m_w n_{\mathrm{rp}}/m_{\mathrm{rp}})\times r}$;
   set $F_{k_{\mathrm{lin}}}:=\mathbf{0}$, $H_{k_{\mathrm{lin}}}:=\mathbf{0}$ — **ignored block**
   (its linear constraint is replaced by the trace-consistency constraints below).
6. $(\mathrm{com}_{k_{\mathrm{lin}}},\mathbf{x}_{k_{\mathrm{lin}}}):=\mathrm{Com}_{\mathrm{par}_{\mathrm{com}}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_{k_{\mathrm{lin}}}))$;
   send $\mathrm{com}_{k_{\mathrm{lin}}}$.
7. Receive $\mathbf{Z}^{(0)},\mathbf{Z}^{(1)}$; compute $\mathbf{Z}:=\mathbf{Z}^{(1)}\bullet\mathbf{Z}^{(0)}$
   (row-tensor batch matrix over [block positions × coefficient positions]).
8. $\mathbf{V}_{\mathrm{bat}}:=\mathbf{Z}\mathbf{V}\bmod q\in R_q^{n_{\mathrm{bat}}\times r}$.
9. $\mathbf{Y}_{k_{\mathrm{lin}}+1}:=G^{-1}_{\ell'}(\mathbf{V}_{\mathrm{bat}})\in R^{\ell' n_{\mathrm{bat}}\times r}$;
   $(\mathrm{com}_{k_{\mathrm{lin}}+1},\mathbf{x}_{k_{\mathrm{lin}}+1}):=\mathrm{Com}_{\mathrm{par}'_{\mathrm{com}}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_{k_{\mathrm{lin}}+1}))$.
10. Set the second new block:
    $F_{k_{\mathrm{lin}}+1}=\mathbf{Z}(I_{\varphi m_w/m_{\mathrm{rp}}}\otimes\mathrm{cf}^{-1}_\vee(\mathbf{J}^{\top})^{\top})$,
    $H_{k_{\mathrm{lin}}+1}=G_{\ell'}$ (constraint
    $\mathbf{Z}(I\otimes\mathrm{lift}(\mathbf{J}))\mathbf{W}=G_{\ell'}\mathbf{Y}_{k_{\mathrm{lin}}+1}$).
11. $\hat z^{(0)}_i:=\mathrm{cf}^{-1}_\vee(\mathbf{z}^{(0)}_i)\in R$ for all $i\in[n_{\mathrm{bat}}]$
    (trace-dual lift of the coefficient-position challenges).
12. Compute and send
    $\mathbf{r}:=\big(\mathbf{e}_i^{\top}\mathbf{V}_{\mathrm{bat}}\mathbf{z}^{(2)}_i-\mathbf{z}^{(1)\top}_i\hat z^{(0)}_i\,\mathbf{V}_{\mathrm{emb}}\mathbf{z}^{(2)}_i\big)_{i\in[n_{\mathrm{bat}}]}$
    (batched trace-consistency residuals; $\mathbf{e}_i$ = $i$-th unit vector of length $n_{\mathrm{bat}}$).
13. Extend the global constraint:
    $\mathbf{A}':=\mathrm{diag}\big(\mathbf{A},\ (\mathbf{z}^{(2)\top}_i\otimes\mathbf{z}^{(1)\top}_i\otimes\mathbf{g}^{\top}\ \Vert\ \mathbf{z}^{(0)\top}_i\otimes\mathbf{z}^{(1)\top}_i\otimes\hat z^{(0)\top}_i\otimes\mathbf{g}^{\top})_{i\in[n_{\mathrm{bat}}]}\big)$,
    $\mathbf{b}':=[\mathbf{b}\Vert\mathbf{r}]$ — the new rows are the linear forms selecting
    $\mathbf{e}_i^{\top}G_{\ell'}\mathbf{Y}_{k_{\mathrm{lin}}+1}\mathbf{z}^{(2)}_i$ and
    $\mathbf{z}^{(1)\top}_i\hat z^{(0)}_iG_{\ell}\mathbf{Y}_{k_{\mathrm{lin}}}\mathbf{z}^{(2)}_i$
    from the vectorised $(\mathbf{Y}_i)_i$ (gadget vectors $\mathbf{g}$ select digit positions).
14. Parameter bookkeeping:
    $(n_{k_{\mathrm{lin}}},\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}},m_{y,k_{\mathrm{lin}}},\beta_{x,k_{\mathrm{lin}}},\beta_{y,k_{\mathrm{lin}}}):=(0,\ \mathrm{par}_{\mathrm{com}},\ \ell m_w\tfrac{n_{\mathrm{rp}}}{m_{\mathrm{rp}}},\ \beta_x[\mathrm{par}_{\mathrm{com}}],\ \mathrm{dcmp}_\ell(\beta_{\mathrm{rp}}\beta_w))$;
    $(n_{k_{\mathrm{lin}}+1},\dots):=(n_{\mathrm{bat}},\ \mathrm{par}'_{\mathrm{com}},\ \ell' n_{\mathrm{bat}},\ \beta_x[\mathrm{par}'_{\mathrm{com}}],\ \mathrm{dcmp}_{\ell'}(\sqrt{\varphi n_{\mathrm{bat}}}\,q/2))$.
15. Output $\mathrm{stmt}':=((\mathrm{com}_i,\mathbf{F}_i,\mathbf{H}_i)_{i\in[k_{\mathrm{lin}}+2]},(\boldsymbol\ell_j,\mathbf{r}_j,t_j)_{j\in[k_{\mathrm{lr}}]},\mathbf{A}',\mathbf{b}')$,
    $\mathrm{wit}':=(\mathbf{W},(\mathbf{Y}_i,\mathbf{x}_i)_{i\in[k_{\mathrm{lin}}+2]})$ —
    $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}+2,\ k_{\mathrm{lr}},\ n+n_{\mathrm{bat}},\ m_w,\ r,\ \beta_w,\dots]$.

Verifier:
1. Sample $\mathbf{J}\leftarrow\chi^{n_{\mathrm{rp}}\times m_{\mathrm{rp}}}$; send.
2. Sample $\mathbf{Z}^{(0)}\leftarrow\mathbb{Z}_q^{n_{\mathrm{bat}}\times2^{\otimes\log\varphi}}$,
   $\mathbf{Z}^{(1)}\leftarrow\mathbb{Z}_q^{n_{\mathrm{bat}}\times2^{\otimes\log(m_w n_{\mathrm{rp}}/m_{\mathrm{rp}})}}$
   (row-tensor structured challenges); send $\mathbf{Z}:=\mathbf{Z}^{(1)}\bullet\mathbf{Z}^{(0)}$.
3. Sample $\mathbf{Z}^{(2)}\leftarrow\mathbb{Z}_q^{n_{\mathrm{bat}}\times2^{\otimes\log r}}$; send.
4. Receive $\mathrm{com}_{k_{\mathrm{lin}}+1}$, $\mathbf{r}$; check $\mathrm{trace}(r_i)=0$ for
   all $i\in[n_{\mathrm{bat}}]$; output $\mathrm{stmt}'$.

**Completeness equations** (to test against in code):
$\mathrm{trace}(\mathrm{cf}^{-1}_\vee(\mathbf{J}^{\top})^{\top}\mathbf{w}_{i,j})=\mathbf{J}\,\mathrm{cf}(\mathbf{w}_{i,j})$
per chunk; hence
$\mathrm{trace}(\mathbf{z}^{(1)\top}_i\otimes\mathbf{z}^{(0)\top}_i\mathrm{cf}_\vee(\mathbf{J})^{\top}\mathbf{W}\mathbf{z}^{(2)}_i)
=\mathbf{z}^{(1)\top}_i\otimes\mathbf{z}^{(0)\top}_i\mathbf{V}_{\mathrm{tr}}\mathbf{z}^{(2)}_i$
($\mathbb{Z}_q$-linearity of trace) and
$\mathbf{z}^{(0)\top}_i\mathbf{V}_{\mathrm{tr}}=\mathrm{trace}(\hat z_i\mathbf{V}_{\mathrm{emb}})$,
giving $\mathrm{trace}(r_i)=0$.

**Lemma 8.**
- *Completeness* $\epsilon=(\varphi r m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$ for
  $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}]\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}}+2,n+n_{\mathrm{bat}}]$
  with
  $\mathrm{par}_{\mathrm{lin},k_{\mathrm{lin}}}:=(0,\mathrm{par}_{\mathrm{com}},\ell m_w\tfrac{n_{\mathrm{rp}}}{m_{\mathrm{rp}}},\beta_x,\mathrm{dcmp}_\ell(\beta_{\mathrm{rp}}\beta_w))$
  and
  $\mathrm{par}_{\mathrm{lin},k_{\mathrm{lin}}+1}:=(n_{\mathrm{bat}},\mathrm{par}'_{\mathrm{com}},\ell' n_{\mathrm{bat}},\beta'_x,\mathrm{dcmp}_{\ell'}(\sqrt{\varphi n_{\mathrm{bat}}}q/2))$.
- *Knowledge soundness* with
  $\kappa=\big((\log(\varphi r m_w/m_{\mathrm{rp}}))/q\big)^{n_{\mathrm{bat}}}+(\varphi m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$,
  for
  $\Xi^{\mathrm{sis}}[\mathrm{par}_{\mathrm{sis}}]\vee\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}},\dots,\mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}},\dots]\leftarrow\Xi^{\mathrm{lin\text{-}rel}}_{\mathrm{COM}}[k_{\mathrm{lin}}+2,k_{\mathrm{lr}},n+n_{\mathrm{bat}},m_w,r,\beta'_w,\dots,\varrho']$,
  where $\mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}}<q/b$ and
  $\mathrm{par}_{\mathrm{sis}}\supseteq\{(n_0,m_w,2\beta'_w\varrho')\}\cup\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}},\dots]\cup\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}+1},\dots]$.
- *Efficiency*: prover $O(m_wr n_{\mathrm{rp}}\varphi)$ $\mathbb{Z}$-ops (dominated by
  $\mathbf{V}_{\mathrm{tr}}$; $\mathbf{V}$ itself need not be materialised) +
  $O(n_{\mathrm{bat}}m_wr)$ $R_q$-ops (for $\mathbf{V}_{\mathrm{bat}}$) + two commitments;
  verifier $O(n_{\mathrm{rp}}m_{\mathrm{rp}})$ $\chi$-samples, $O(n_{\mathrm{bat}}\log(\varphi r m_w/m_{\mathrm{rp}}))$
  $\mathbb{Z}_q$-samples and $O(n_{\mathrm{bat}})$ $R_q$-ops; communication
  $|\mathrm{com}_{k_{\mathrm{lin}}}|+|\mathrm{com}_{k_{\mathrm{lin}}+1}|+O(n_{\mathrm{bat}}\log|R_q|)$.

### 5.3 $\Pi^{\mathrm{proj\text{-}fl}}$ — lift-and-batch fine projection (Appendix B) — [R3, optional]

Asymptotic optimisation of $\Pi^{\mathrm{proj\text{-}f}}$ (not used in the concrete
implementation; $\Pi^{\mathrm{proj\text{-}f}}$ = the $c=1$ special case). Assumes a
$d$-smooth tower $R=R_c\supset R_{c-1}\supset\dots\supset R_0=\mathbb{Z}$ with
$[R_{i+1}:R_i]\le d$ (for power-of-two rings, $c=\log\varphi$, $d=2$). Instead of immediately
lifting the trace value from $\mathbb{Z}$ to $R$, gradually lift $r_0\in R^{n_{\mathrm{bat},0}}$
through the tower: at each level $i$, the prover sends $\mathrm{trace}$-relative-to-$R_i$ values
and receives a random challenge
$\mathbf{Z}_i\in R_{i+1,q}^{n_{\mathrm{bat},i+1}\times n_{\mathrm{bat},i}}$ that batches
$n_{\mathrm{bat},i}$ elements into $n_{\mathrm{bat},i+1}$ elements of $R_{i+1}$, ending at
$r_c\in R^{n_{\mathrm{bat},c}}$ sent in the clear. Parameter choice:
$n_{\mathrm{bat},c}=1$, $n_{\mathrm{bat},c-1}=O(1)$,
$n_{\mathrm{bat},i}=n^{c-i}_{\mathrm{bat},c-1}$, $\sum_i n_{\mathrm{bat},i}\in O(\varphi)$,
$n_{\mathrm{bat},0}\in O(\lambda/\log\lambda)$. Soundness needs each intermediate
$Q_i=R_i/qR_i\simeq(\mathbb{F}_{q^{e_i}})^{\varphi_i/e_i}$ to have a "relatively large" subfield;
knowledge error $\sum_{i\in[c]}(n_{\mathrm{bat},i}/q^{e_i})^{n_{\mathrm{bat},i+1}}+(\varphi m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$.

**Lemma 12** (stated for $\Pi^{\mathrm{proj\text{-}fl}}_{n_{\mathrm{bat}},\ell,\ell',\mathrm{par}_{\mathrm{com}},\mathrm{par}'_{\mathrm{com}}}$):
completeness $\epsilon=(\varphi r m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$ for
$\Xi^{\mathrm{lin}}_{\mathrm{COM}}\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}$ with
$k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+2$, $n\mapsto n+n_{\mathrm{bat},c}$, block parameters
identical in form to Lemma 8 (with $n_{\mathrm{bat}}\rightsquigarrow n_{\mathrm{bat},c}$);
knowledge soundness as above; prover $O(m_wr n_{\mathrm{rp}}\varphi)$ $\mathbb{Z}$-ops +
$O(\sum_{i\in[c]}n_{\mathrm{bat},i}m r)$ $R_q$-ops + two commitments; communication
$|\mathrm{com}_{k_{\mathrm{lin}}}|+|\mathrm{com}_{k_{\mathrm{lin}}+1}|+\sum_{i\in[c]}O(n_{\mathrm{bat},i}\log|R_{c,q}|)=O(\log\lambda)$.

### 5.4 $\Pi^{\mathrm{fold\text{-}split}}$ — committed folding and splitting (Figure 4) — [R2]

$\Pi^{\mathrm{fold\text{-}split}}_{r',\ell,\ell',\ell'',\mathrm{par}_{\mathrm{com}},\mathrm{par}'_{\mathrm{com}},\tilde\beta_w}:\ \Xi^{\mathrm{lin}}_{\mathrm{COM}}\to\Xi^{\mathrm{sum}}_{\mathrm{COM}}$.
Folds the $r$ columns with a challenge $\mathbf{c}\in\mathcal{C}^r$, packs everything into a new
witness $\mathbf{U}$ of width $r'$, re-commits, and encodes **all** constraints as sumcheck claims.

**Protocol (Figure 4):**

Prover:
1. Parse the $\Xi^{\mathrm{lin}}_{\mathrm{COM}}$ statement and witness (as before).
2. Build the left-vector matrix:
   $\mathbf{F}_{k_{\mathrm{lin}}}:=\text{matrix-from-rows}((\boldsymbol\ell_j)_{j\in[k_{\mathrm{lr}}]})$,
   $n_{k_{\mathrm{lin}}}:=k_{\mathrm{lr}}$;
   $\mathbf{T}:=\mathbf{F}_{k_{\mathrm{lin}}}\mathbf{W}\bmod q$;
   $\mathbf{Y}_{k_{\mathrm{lin}}}:=G^{-1}_{\ell}(\mathbf{T})\in R^{\ell k_{\mathrm{lr}}\times r}$
   (so $\mathbf{F}_{k_{\mathrm{lin}}}\mathbf{W}=G_\ell\mathbf{Y}_{k_{\mathrm{lin}}}\bmod q$);
   $(\mathrm{com}_{k_{\mathrm{lin}}},\mathbf{x}_{k_{\mathrm{lin}}}):=\mathrm{Com}_{\mathrm{par}_{\mathrm{com}}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_{k_{\mathrm{lin}}}))$;
   send $\mathrm{com}_{k_{\mathrm{lin}}}$.
3. Receive $\mathbf{c}\leftarrow\mathcal{C}^r$. Fold:
   $\tilde{\mathbf{w}}:=G^{-1}_{\ell'}(\mathbf{W}\mathbf{c})\in R^{\ell' m_w}$.
4. Pack the folded witness with all auxiliary data:
   $\hat{\mathbf{w}}:=\mathrm{pack}\big(\tilde{\mathbf{w}},\ (\mathrm{vec}(\mathbf{Y}_i),\mathbf{x}_i):i\in[k_{\mathrm{lin}}+1]\big)$
   (all blocks sorted by decreasing dimension, zero-padded; $|\hat{\mathbf{w}}|=\hat m_w=\minpowtwo(\ell' m_w+\sum_{i\in[k_{\mathrm{lin}}+1]}(m_{y,i}r+m_x[\mathrm{par}_{\mathrm{com},i}]))$).
5. Norm witness: $v\leftarrow\langle\hat{\mathbf{w}},\overline{\hat{\mathbf{w}}}\rangle=\sum_j\hat w_j\overline{\hat w_j}\in R$
   (Hermitian self-inner product; one ring element).
6. Reshape and re-commit:
   $\mathbf{U}:=\mathrm{reshape}_{r'}(\hat{\mathbf{w}})\in R^{\hat m_w/r'\times r'}$;
   $\mathbf{F}:=\mathbf{A}_{n,\hat m_w/r'}$ (vSIS key from ck, $n$ rows);
   $\mathbf{Y}:=G^{-1}_{\ell''}(\mathbf{FU}\bmod q)\in R^{\ell'' n\times r'}$;
   $(\mathrm{com},\mathbf{x})\leftarrow\mathrm{Com}_{\mathrm{par}'_{\mathrm{com}}}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}))$;
   send $(\mathrm{com},v)$.
7. Build the sumcheck claims — `sumcheckify` (Figure 5, §5.5) over
   $f_{\mathrm{sc}}\leftarrow\text{sumcheckify}(\text{the constraint system})$:
   - $\mathbf{F}_i\cdot G_{\ell'}\tilde{\mathbf{w}}=\mathbf{H}_i\mathbf{Y}_i\mathbf{c}\bmod q$
     $\forall i\in[k_{\mathrm{lin}}]$  (folded linear blocks; by linearity
     $\mathbf{F}_i(\mathbf{Wc})=(\mathbf{F}_i\mathbf{W})\mathbf{c}=\mathbf{H}_i\mathbf{Y}_i\mathbf{c}$);
   - $\mathbf{F}_{k_{\mathrm{lin}}}\cdot G_{\ell'}\tilde{\mathbf{w}}=G_\ell\mathbf{Y}_{k_{\mathrm{lin}}}\mathbf{c}\bmod q$;
   - $\mathrm{COM.Verify}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}_i),\mathrm{com}_i,\mathbf{x}_i)=1$
     $\forall i\in[k_{\mathrm{lin}}+1]$ (commitment well-formedness, incl. the two new ones);
   - $(G_\ell\mathbf{Y}_{k_{\mathrm{lin}}})[j,:]\cdot\mathbf{r}_j=t_j\bmod q$ $\forall j\in[k_{\mathrm{lr}}]$
     (right-hand constraints);
   - $\mathbf{A}\cdot(\mathrm{vec}(\mathbf{Y}_i))_{i\in[k_{\mathrm{lin}}]}=\mathbf{b}\bmod q$
     (global constraint);
   - $\langle\hat{\mathbf{w}},\overline{\hat{\mathbf{w}}}\rangle=v\bmod q$ (exact norm check).
   Set $k_i:=\#$constraints$(\mathrm{par}_{\mathrm{com},i})$ and
   $k_{\mathrm{sc}}:=\sum_{i\in[k_{\mathrm{lin}}+1]}k_i+\sum_{i\in[k_{\mathrm{lin}}+1]}n_i+n+k_{\mathrm{lr}}+1$.
8. Output $\mathrm{stmt}':=(\mathrm{com},\mathbf{F},G_{\ell''},\mathbf{f}_{\mathrm{sc}})$,
   $\mathrm{wit}':=(\mathbf{U},\mathbf{Y},\mathbf{x})$ — an instance of
   $\Xi^{\mathrm{sum}}_{\mathrm{COM}}[k_{\mathrm{sc}},\ n,\ \hat m_w/r',\ r',\ \mathrm{par}'_{\mathrm{com}},\ \ell''n,\ \tilde\beta_w,\ \beta'_x,\ \mathrm{dcmp}_{\ell''}(q/2),\ 2]$.

Verifier:
1. Receive $\mathrm{com}_{k_{\mathrm{lin}}}$.
2. Sample $\mathbf{c}\leftarrow\mathcal{C}^r$; send.
3. Receive $(\mathrm{com},v)$; check $\mathrm{trace}(v)\le\hat f\cdot\tilde\beta_w^2$
   (**Remark 3**: for power-of-two rings check instead
   $\mathrm{ct}(v)\le\tilde\beta_w^2$ — the constant term of the Hermitian self-inner product
   equals $\|\mathrm{cf}(\hat{\mathbf{w}})\|_2^2$ exactly, avoiding the $\hat f$ factor and the
   coefficient↔canonical conversions).
4. Output $\mathrm{stmt}'$.

**Lemma 9.** Let $\ell,\ell',\ell''\in\mathbb{N}$, $r,r'$ powers of two,
$\beta_x=\beta_x[\mathrm{par}_{\mathrm{com}}]$, $\beta'_x=\beta_x[\mathrm{par}'_{\mathrm{com}}]$,
and suppose
$\tilde\beta_w\ge\sqrt{\mathrm{dcmp}_{\ell'}(r\gamma_{\mathcal{C}}\beta_w)^2+\beta_x^2+\beta_y^2+\sum_{i\in[k_{\mathrm{lin}}]}\beta_{y,i}^2+\beta_{x,i}^2}$
(norm growth budget: folded column norm $\le r\gamma_{\mathcal{C}}\beta_w$ before
decomposition; packing adds the aux norms; decomposition by $G^{-1}_{\ell'}$ re-scales via
$\mathrm{dcmp}$). Then:
- *Perfect completeness* for
  $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\beta_w,(\dots)]\to\Xi^{\mathrm{sum}}_{\mathrm{COM}}[k_{\mathrm{sc}},n,\hat m_w/r',r',\mathrm{par}'_{\mathrm{com}},\ell''n,\tilde\beta_w,\beta'_x,\mathrm{dcmp}_{\ell''}(q/2),2]$
  with $\mathrm{par}_{\mathrm{com},k_{\mathrm{lin}}}=\mathrm{par}_{\mathrm{com}}$ and
  $m_{y,k_{\mathrm{lin}}}=\ell''n$.
- *Knowledge soundness*, $\kappa=r/|\mathcal{C}|$, for
  $\Xi^{\mathrm{sis}}[\mathrm{par}_{\mathrm{sis}}]\vee\Xi^{\mathrm{lin\text{-}rel}}_{\mathrm{COM}}[k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\ 2\mathrm{cmp}_{\ell'}(\tilde\beta_w),\ (n_i,\mathrm{par}_{\mathrm{com},i},m_{y,i},\tilde\beta_w,\tilde\beta_w)_{i\in[k_{\mathrm{lin}}]},\ 2\gamma_{\mathcal{C}}]\leftarrow\Xi^{\mathrm{sum}}_{\mathrm{COM}}[k_{\mathrm{sc}},n,\hat m_w/r',r',\mathrm{par}'_{\mathrm{com}},\ell''n,\beta'_w,\beta'_x,\mathrm{dcmp}_{\ell''}(q/2),2]$
  where
  $\mathrm{par}_{\mathrm{sis}}\supseteq\bigcup_{i\in[k_{\mathrm{lin}}+1]}\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com},i},m_{y,i},\tilde\beta_w,\tilde\beta_w]$
  and $\tilde\beta'_w=\tilde\beta_w\cdot\sqrt{\hat f\cdot\mathrm{rad}(f)/f}$ provided
  $r'\beta_w'^2\hat f<q/2$ (the no-wraparound side condition).
- *Efficiency*: prover $O(\ell m_wr)$ $R_q$-ops + the $\mathrm{com}$ computation; verifier
  $O(1)$ $R_q$-ops + sampling $r$ challenges; communication
  $|\mathrm{com}_{k_{\mathrm{lin}}}|+|\mathrm{com}|+O(\log|R_q|)$ (the $O(\log|R_q|)$ is $v$).

**Extraction outline (§6 soundness proof)**: coordinate-wise rewinding [FMN24, Lemma 7.1] yields
$r+1$ accepting transcripts whose challenges $\mathbf{c}^{(0)},\dots,\mathbf{c}^{(r)}$ pairwise
differ in exactly one coordinate; witnesses $\mathrm{wit}^{*(j)}=(\mathbf{U}^{*(j)},\mathbf{Y}^{*(j)},\mathbf{x}^{*(j)})$;
unpack $\hat{\mathbf{w}}^{*(j)}=\mathrm{vec}(\mathbf{U}^{*(j)})$ with
$\|\hat{\mathbf{w}}^{*(j)}\|_2\le\sqrt{r'}\beta'_w$. (1) The norm sumcheck + integer lift give
$\|\hat{\mathbf{w}}^{*(j)}\|_2^2\le\tilde\beta_w^2\cdot\hat f\,\mathrm{rad}(f)/f$. (2) If any
$\mathbf{Y}^{*(j)}_i\ne\mathbf{Y}^{*(r)}_i$ → binding break → SIS (Lemma 4). (3) Otherwise
"unfold by coordinate differences": $\mathbf{v}^{*(j)}:=G_{\ell'}\tilde{\mathbf{w}}^{*(j)}$,
$s_j:=c^{(j)}_j-c^{(r)}_j\ne0$,
$\mathbf{u}^{(j)}:=(\mathbf{v}^{*(j)}-\mathbf{v}^{*(r)})/s_j$, and
$\mathbf{U}:=(\mathbf{u}^{(j)})_{j\in[r]}$, $\mathbf{s}:=(s_j)_{j\in[r]}$ satisfy
$\mathbf{F}_i\mathbf{U}=\mathbf{H}_i\mathbf{Y}^*_i$ for all $i$, with
$\|\mathbf{U}\,\mathrm{diag}(\mathbf{s})\|_2\le2\mathrm{cmp}_{\ell'}(\tilde\beta_w)$,
$\|\mathrm{diag}(\mathbf{s})\|_{\mathrm{op},2}\le2\gamma_{\mathcal{C}}$ (the slack!).
(4) Remaining constraints follow from accepted sumcheck claims:
$\mathbf{T}^*[j,:]\mathbf{r}_j=t_j$, $\mathbf{A}(\mathrm{vec}\mathbf{Y}^*_i)_i=\mathbf{b}$,
`COM.Verify` = 1. Success probability $\ge\epsilon-r/|\mathcal{C}|$.

### 5.5 `sumcheckify` — inner-product relations → sumcheck claims (Figure 5) — [R1/R2 glue]

Signature:
$\text{sumcheckify}:R^m\times R^m\times(R_q^{2m+3})^{k_{\mathrm{sc}}}\to\big((R_q[y_0,\dots,y_{\mu-1}]_{\le2})[x_0,x_1]_{\le1}\big)^{k_{\mathrm{sc}}}$
with $m=2^\mu$.

Input: $\big(\mathbf{v},\mathbf{w},(\mathbf{a}_{i,1},\mathbf{b}_{i,1},\mathbf{a}_{i,0},\mathbf{b}_{i,0},c_i)_{i\in[k_{\mathrm{sc}}]}\big)$
where $\mathbf{a}_{i,0},\mathbf{b}_{i,0}\in R_q^{m}$, $\mathbf{a}_{i,1},\mathbf{b}_{i,1},c_i\in R_q$.
The $i$-th constraint means:
$$\big\langle\mathbf{a}_{i,1}\mathbf{v}+\mathbf{a}_{i,0},\ \mathbf{b}_{i,1}\mathbf{w}+\mathbf{b}_{i,0}\big\rangle=c_i\bmod q.\tag{4}$$
Output polynomials:
$$f^{(i)}_{\mathrm{sc}}(x_0,x_1):=\big(a_{i,1}\,x_0+\mathrm{MLE}[\mathbf{a}_{i,0}]\big)\cdot\big(b_{i,1}\,x_1+\mathrm{MLE}[\mathbf{b}_{i,0}]\big)-\frac{c_i}{m}.$$

**Lemma 10**: $\mathbf{v},\mathbf{w}$ satisfy (4) **iff**
$\sum_{\mathbf{z}\in\{0,1\}^\mu}(f^{(i)}_{\mathrm{sc}}(\mathrm{MLE}[\mathbf{v}],\mathrm{MLE}[\mathbf{w}]))(\mathbf{z})=0\bmod q$.
(Uses $\sum_{\mathbf{z}}\mathrm{eq}(\cdot,\mathbf{z})\mathrm{MLE}[\mathbf{a}](\mathbf{z})\mathrm{MLE}[\mathbf{b}](\mathbf{z})=\langle\mathbf{a},\mathbf{b}\rangle$
and $\sum_{\mathbf{z}\in\{0,1\}^\mu}1=m$.)

**Usage in $\Pi^{\mathrm{fold\text{-}split}}$** ($\mathbf{v}:=\hat{\mathbf{w}}$,
$\mathbf{w}:=\overline{\hat{\mathbf{w}}}$… concretely: all constraints are instantiated with the
packed vector as *both* inputs; $a_{i,1}=0$ for every constraint except the final
(inner-product/norm) one):
- **Linear constraints** take the form $\langle\mathbf{a}_{i,0},\hat{\mathbf{w}}\rangle=c_i$
  with $a_{i,1}=0,b_{i,1}=1$: $\mathbf{a}_{i,0}$ is a *padded public vector* (the row
  $\mathbf{f}^j\otimes\mathbf{g}_\ell$ placed on the $\tilde{\mathbf{w}}$-block, the challenge
  products on the $\mathbf{Y}$-blocks, etc.).
- **Norm constraint** takes $a_{i,1}=b_{i,1}=1$, $c_i=v$: claim
  $\sum_{\mathbf{z}}\mathrm{MLE}[\hat{\mathbf{w}}](\mathbf{z})\cdot\mathrm{MLE}[\overline{\hat{\mathbf{w}}}](\mathbf{z})=\langle\hat{\mathbf{w}},\overline{\hat{\mathbf{w}}}\rangle=v$.
- Identity used: $\mathrm{MLE}[\overline{\hat{\mathbf{w}}}]=\overline{\mathrm{MLE}[\hat{\mathbf{w}}]}$.

**Worked example (§6.2)** — the constraint $\mathbf{F}_0G_\ell\tilde{\mathbf{w}}=G_{\ell'}\mathbf{Y}_0\mathbf{c}$,
$j$-th row ($\mathbf{f}^j$ = $j$-th row of $\mathbf{F}_0$; $\mathbf{y}_j$ = the gadget block of
$\mathbf{Y}_0$ recombined into coordinate $j$; $G_\ell=I\otimes\mathbf{g}_\ell^\top$):
$$\langle\mathbf{f}^j\otimes\mathbf{g}_\ell,\ \tilde{\mathbf{w}}\rangle=\langle\mathbf{y}_j,\ \mathbf{c}\otimes\mathbf{g}_{\ell'}\rangle\bmod q,$$
which as a sumcheck over the packed vector $\hat{\mathbf{w}}$ (prefixes $p_w,p_j$ selecting the
$\tilde{\mathbf{w}}$ / $\mathbf{y}_j$ blocks) becomes:
$$\sum_{\mathbf{z}\in\{0,1\}^{\log\hat m_w}}\mathrm{MLE}[\mathbf{g}_\ell](\mathbf{z}_0)\,\mathrm{MLE}[\mathbf{f}^j](\mathbf{z}_1)\,\mathrm{eq}(p_w,\mathbf{z}_2)\,\mathrm{MLE}[\hat{\mathbf{w}}](\mathbf{z})
-\mathrm{eq}(p_j,\mathbf{z}_3)\,\mathrm{MLE}[\hat{\mathbf{w}}](\mathbf{z})\,\mathrm{MLE}[\mathbf{c}](\mathbf{z}_4)\,\mathrm{MLE}[\mathbf{g}_{\ell'}](\mathbf{z}_5)=0\bmod q$$
with $\mathbf{z}_0..\mathbf{z}_5$ (possibly overlapping) substrings of $\mathbf{z}$.
**Verifier efficiency at the final sumcheck point** $\mathbf{r}$:
(i) $\mathbf{g}_\ell,\mathbf{g}_{\ell'},\mathbf{c}$ are short ($\ell,\ell',r$) — direct MLE
evaluation in $O(\ell),O(\ell'),O(r)$;
(ii) $\mathrm{eq}(p_w,\mathbf{r}_2),\mathrm{eq}(p_j,\mathbf{r}_3)$ cost $O(\log\hat m_w)$ by the
product structure;
(iii) vSIS rows factor: $\mathbf{f}^j=\mathbf{f}^j_0\otimes\dots\otimes\mathbf{f}^j_{\mu_1-1}$ (length-2
factors), so $\mathrm{MLE}[\mathbf{f}^j](\mathbf{r}_1)=\prod_k(f^j_{k,0}+(f^j_{k,1}-f^j_{k,0})r_{1,k})$
— $O(\mu_1)$.

### 5.6 Basic sumcheck with linear map (Figure 7, Appendix C) — [R1]

Languages (over an $R$-module setting): a **C-linear** map $\Phi:N\to M$ (i.e.
$\Phi(a\cdot c)=\Phi(a)\cdot c$ for $c\in\mathcal{C}$, $\mathcal{C}\subseteq R$ a strong sampling
set), $g\in N[x_0,\dots,x_{\ell-1}]$, $H=\{0,1\}$:
- Summation claim $\Xi^{\mathrm{sc}}$: $\mathrm{stmt}=(\Phi,g,y)$ with $y=\Phi(\sum_{\mathbf{x}\in H^\ell}g(\mathbf{x}))$.
- Evaluation claim $\Xi^{\mathrm{polyeval}}$: $\mathrm{stmt}=(\Phi,g,\mathbf{c},v)$ with $v=\Phi(g(\mathbf{c}))$.

**Protocol (Figure 7)**: $y_{-1}:=y$. For $i=0..\ell-1$: prover sends
$q_i(x)=\Phi\big(\sum_{z_{i+1},\dots\in H^{\ell-i-1}}g(c_0,..,c_{i-1},x,z_{i+1},..)\big)\in M[x]$;
verifier checks $\sum_{x\in H}q_i(x)=y_{i-1}$; samples $c_i\leftarrow\mathcal{C}$; sets
$y_i:=q_i(c_i)$. Output $(\Phi,g,\mathbf{c},y_{\ell-1})$.

**Lemma 13**: perfectly complete RoK; knowledge error
$\kappa\le\sum_i\deg_{x_i}(g)/|\mathcal{C}|\le\ell\deg(g)/|\mathcal{C}|$ (Schwartz–Zippel with
invertible differences). Communication $\sum_i(\deg_{x_i}(g)+1)$ elements of $M$, $\ell$
challenges in $\mathcal{C}$. Prover with the $H^\ell$ evaluation table:
$O\big(\frac{d}{|H|-1}|H|^\ell\big)$ operations in $N$ + $\sum_i(\deg_{x_i}+1)$ applications of
$\Phi$ (standard bookkeeping: maintain table
$T_i(x_i..x_{\ell-1})=g(c_0,..,c_{i-1},x_i,..)$; per round interpolate the univariate at
$|H|$+extra points). Verifier: evaluate $\ell$ univariates at $|H|$ points.

**Remark 7**: the verifier needs only *one-time evaluation access*
$\mathbf{c}\mapsto\Phi(g(\mathbf{c}))$ — sumcheck is a "delayed-statement" RoK: the honest
verifier never needs $g$ (only degree/variable counts); the extractor knows $g$.
**Remark 8**: $\Phi(g)(\mathbf{c})=\Phi(g(\mathbf{c}))$ so the protocol equals a standard
sumcheck on $\Phi(g)$.

**NTT slot batching (C.2)**: with $M=R_q\simeq(\mathbb{F}_{q^e})^{\varphi/e}$ and
$\mathbb{F}=\mathbb{F}_{q^e}$: choose random $\mathbb{F}$-linear
$\Phi:\mathbb{F}^{\varphi/e}\to\mathbb{F}$:
- $\Phi=\boldsymbol\delta^\top\circ\mathrm{NTT}$, $\boldsymbol\delta\leftarrow\mathbb{F}^{\varphi/e}$:
  knowledge error $1/|\mathbb{F}|=q^{-e}$;
- tensor version $\Phi_i=\mathrm{eq}(\mathrm{bin}(i),\mathbf{r})$: error
$\lceil\log(\varphi/e)\rceil/|\mathbb{F}|$.
The final claim $\Phi(g(\mathbf{c}))=v$ with $\mathbf{c}\in\mathbb{F}^{\nu}\subseteq R_q^{\nu}$
is checked as $\Phi(f_{\mathrm{sc}}(z_0,z_1)(\mathbf{c}))$ given
$z_0=\mathrm{MLE}[\mathbf{w}](\mathbf{c})$, $z_1=\mathrm{MLE}[\overline{\mathbf{w}}](\mathbf{c})$,
using $\ \overline{z_1}=\mathrm{MLE}[\mathbf{w}](\bar{\mathbf{c}})$ (conjugation identity).

### 5.7 $\Pi^{\mathrm{lin}}$ — linearisation with sumcheck (Figure 6) — [R1/R4]

$\Pi^{\mathrm{lin}}_{\theta_a}:\ \Xi^{\mathrm{sum}}_{\mathrm{COM}}\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}$.
Re-encodes the accumulated sumcheck claims as *linear* constraints (2 evaluation rows), enabling
the next iteration. Uses **subfield batching**: $\Phi=\boldsymbol\delta^\top\circ\theta_a$ with
$\boldsymbol\delta\leftarrow\mathbb{F}_{q^a}^{\varphi/a}$, so each sumcheck round communicates a
single $\mathbb{F}_{q^a}$ element.

**Protocol (Figure 6)** — assumptions $m_w=2^\mu$, $r=2^\rho$ (careful: here $\rho=\log r$),
$k_{\mathrm{sc}}$ a power of two:

Prover:
1. Parse $\mathrm{stmt}=(\mathrm{com},\mathbf{F},\mathbf{H},(f^{(i)}_{\mathrm{sc}})_{i\in[k_{\mathrm{sc}}]})$,
   $\mathrm{wit}=(\mathbf{W},\mathbf{Y},\mathbf{x})\in(R^{m_w\times r},R^{n\times r},R^{m_x})$.
2. $\mathbf{w}:=\mathrm{vec}(\mathbf{W})$.
3. Receive $\boldsymbol\gamma$ (challenge batching the $k_{\mathrm{sc}}$ polynomials) and
   $\boldsymbol\delta$ (slot-batching vector).
4. Batch the claims:
   $f_{\mathrm{sc}}(x_0,x_1)(\mathbf{z}):=\sum_{i\in[k_{\mathrm{sc}}]}\mathrm{eq}(\mathrm{bin}(i),\boldsymbol\gamma)\cdot f^{(i)}_{\mathrm{sc}}(x_0,x_1)(\mathbf{z})$.
5. $g_{\mathrm{sc}}(\mathbf{z}):=f_{\mathrm{sc}}\big(\mathrm{MLE}[\mathbf{w}],\ \mathrm{MLE}[\overline{\mathbf{w}}]\big)(\mathbf{z})$
   (degree $\le\delta_{\mathrm{sc}}$ per variable).
6. $\Phi(\cdot):=\boldsymbol\delta^\top\circ\theta_a$ (random $\mathbb{F}_{q^a}$-linear map
   $R_q\to\mathbb{F}_{q^a}$).
7. Run $\Pi^{\mathrm{basic\text{-}sc}}$ for the claim
   $\Phi\big(\sum_{\mathbf{z}\in\{0,1\}^{\nu}}g_{\mathrm{sc}}(\mathbf{z})\big)=0$, reducing to
   $(\Phi,g_{\mathrm{sc}},\mathbf{c},v)$ — $\nu=\mu+\rho$ variables, challenges
   $\mathbf{c}=(\mathbf{c}_0,\mathbf{c}_1)\in\mathbb{F}_{q^a}^{\rho}\times\mathbb{F}_{q^a}^{\mu}$
   (column variables / row variables, each lifted to $R_q$ with all NTT slots equal).
8. $z_0:=\mathrm{MLE}[\mathbf{w}](\mathbf{c}_0,\mathbf{c}_1)=\mathrm{tensor}(\mathbf{c}_1)^\top\mathbf{W}\,\mathrm{tensor}(\mathbf{c}_0)\in R_q$;
   $z_1:=\mathrm{MLE}[\overline{\mathbf{w}}](\mathbf{c}_0,\mathbf{c}_1)
   =\overline{\mathrm{tensor}(\bar{\mathbf{c}}_1)^\top\mathbf{W}\,\mathrm{tensor}(\bar{\mathbf{c}}_0)}$
   (equivalently $\bar z_1=\mathrm{MLE}[\mathbf{w}](\bar{\mathbf{c}}_0,\bar{\mathbf{c}}_1)$).
   Send $(v_j)_{j\in[2]}\in R_q^{r\times2}$ (i.e. $z_0,z_1$).
9. Output $\mathrm{stmt}':=\big((\mathrm{com},\mathbf{F},\mathbf{H}),\ (\boldsymbol\ell_j,\mathbf{r}_j,t_j)_{j\in[2]},\ \mathbf{0},\mathbf{0}\big)$
   with $\boldsymbol\ell_0=\mathrm{tensor}(\mathbf{c}_1)$, $\mathbf{r}_0=\mathrm{tensor}(\mathbf{c}_0)$,
   $t_0=z_0$; $\boldsymbol\ell_1=\mathrm{tensor}(\bar{\mathbf{c}}_1)$,
   $\mathbf{r}_1=\mathrm{tensor}(\bar{\mathbf{c}}_0)$, $t_1=\bar z_1$ — an instance of
   $\Xi^{\mathrm{lin}}_{\mathrm{COM}}[1,2,0,m_w,r,\beta_w,(n,\mathrm{par}_{\mathrm{com}},m_y,\beta_x,\beta_y)]$.

Verifier:
1. Sample $\boldsymbol\delta\leftarrow\mathbb{F}_{q^a}^{\varphi/a}$,
   $\boldsymbol\gamma\leftarrow\mathbb{F}_{q^a}^{\log k_{\mathrm{sc}}}$; send.
2. Run the sumcheck verifier ($\nu=\mu+\rho$ rounds, checks
   $\sum_{x\in\{0,1\}}q_i(x)=y_{i-1}$, challenges $c_i\leftarrow\mathbb{F}_{q^a}$).
3. Receive $(z_0,z_1)$; check $\Phi\big(f_{\mathrm{sc}}(z_0,z_1)(\mathbf{c})\big)=v$.
4. Output $\mathrm{stmt}'$.

**Lemma 11.** With $\theta_a$ the $\mathbb{F}_{q^a}$-linear isomorphism for $a\mid e$ and
$\mathbf{F}_0\in\mathcal{A}$ a vSIS key:
- *Perfect completeness* for
  $\Xi^{\mathrm{sum}}_{\mathrm{COM}}[k_{\mathrm{sc}},n,m_w,r,\mathrm{par}_{\mathrm{com}},m_y,\beta_w,\beta_x,\beta_y,\delta_{\mathrm{sc}}]\to\Xi^{\mathrm{lin}}_{\mathrm{COM}}[1,2,0,m_w,r,\beta_w,(\mathrm{par}_{\mathrm{lin},i})_{i\in[1]}]$
  with $\mathrm{par}_{\mathrm{lin},0}=(n,\mathrm{par}_{\mathrm{com}},m_y,\beta_x,\beta_y)$.
- *Knowledge soundness*,
  $\kappa=\frac{\log(k_{\mathrm{sc}})+(\mu+\rho)\delta_{\mathrm{sc}}+1}{q^{a}}$, for
  $\Xi^{\mathrm{sum}}_{\mathrm{COM}}[k_{\mathrm{sc}},n_0,m_w,r,\mathrm{par}_{\mathrm{com},0},m_{y,0},\beta'_w,\beta'_{x,0},\beta'_{y,0},\delta_{\mathrm{sc}}]\ \cup\ \Xi^{\mathrm{sis}}[\mathrm{par}_{\mathrm{sis}}]\ \leftarrow\ \Xi^{\mathrm{lin}}_{\mathrm{COM}}[1,2,0,m_w,r,\beta'_w,(\dots)]$
  where $\mathrm{par}_{\mathrm{sis}}\supseteq\mathrm{par}_{\mathrm{break}}[\mathrm{par}_{\mathrm{com},0},m_{y,0},\beta'_{y,0},\beta'_{x,0}]\cup\{(n_0,m_w,2\beta'_w)\}$.
- *Efficiency*: prover $O(m)$ $R_q$-ops + $\mathrm{com}$ + two $\mathrm{MLE}[\mathrm{vec}(\mathbf{W})]$
  evaluations + batching of $f_{\mathrm{sc}}$ + the $(\mu+\rho)$-variate sumcheck of individual
  degree $\le\delta_{\mathrm{sc}}$; verifier samples
  $O(\log k_{\mathrm{sc}}+\mu+\rho+\varphi/e)$ elements of $\mathbb{F}_{q^e}$, runs the
  $(\mu+\rho)$-variate sumcheck and one evaluation of $f_{\mathrm{sc}}$; communication
  $O(\log|R_q|)+O(\delta_{\mathrm{sc}}(\mu+\rho)\log(q^a))$.

**Extraction (soundness proof) sketch**: run once; if the witness doesn't satisfy the sumcheck
claims, rewind with fixed prover randomness for fresh challenges. If
$\mathbf{Y}''\ne\mathbf{Y}'$ → binding break → SIS. If $\mathbf{W}''\ne\mathbf{W}'$ → a non-zero
column of $\mathbf{W}''-\mathbf{W}'$ is a vSIS solution with norm $\le2\beta'_w$. Otherwise
Schwartz–Zippel over (a) the $\boldsymbol\gamma$-batching
($\log k_{\mathrm{sc}}/q^a$), (b) the $\Phi$-batching ($1/q^a$), (c) the sumcheck rounds
($(\mu+\rho)\delta_{\mathrm{sc}}/q^a$) forces the honest sum, i.e. the input claims were true.

**Corollary 1 (composition efficiency of $\Pi^{\mathrm{lin}}$, PCS setting)**: prover
$O(m_w+n_{\mathrm{rp}}m_{\mathrm{rp}})$ $R_q$-ops; verifier
$O(r+n_{\mathrm{rp}}m_{\mathrm{rp}}+\log k_{\mathrm{sc}})$ $R_q$-ops + $O(\mu)$ $\mathbb{F}_{q^e}$-ops;
communication $O(\log m_w/\log\lambda)$ $R_q$-elements. The dominant cost is batching the
*projection* constraints: with
$\mathbf{D}:=(I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{J}\otimes\mathbf{g}^\top_{\ell'})$ and
$\mathbf{E}:=(\mathbf{c}\otimes I_{m_w/m_{\mathrm{rp}}}\otimes\mathbf{g}_\ell)$ the batched row
$\mathrm{tensor}(\boldsymbol\gamma_1)^\top\mathbf{D}=\mathrm{tensor}(\boldsymbol\gamma'_1)^\top\otimes(\mathrm{tensor}(\boldsymbol\gamma''_1)^\top\mathbf{J})\otimes\mathbf{g}^\top_{\ell'}$
is never materialised as a $k'_{\mathrm{sc}}\times\hat m_w$ matrix — only the single
unstructured factor $\mathrm{tensor}(\boldsymbol\gamma''_1)^\top\mathbf{J}$ is computed
($O(n_{\mathrm{rp}}m_{\mathrm{rp}})$); the final check value
$v=\mathrm{eq}(\mathbf{0},\boldsymbol\gamma_0)\cdot\big[\mathrm{MLE}[\mathrm{tensor}(\boldsymbol\gamma_1)^\top\mathbf{D}]\,\mathrm{eq}(p_w)\,z_0-\mathrm{MLE}[\mathrm{tensor}(\boldsymbol\gamma_1)^\top\mathbf{E}]\,\mathrm{eq}(p_v)\,z_0\big](\mathbf{s})$
costs $O(r+n_{\mathrm{rp}}m_{\mathrm{rp}}+\log k_{\mathrm{sc}})$; fine projections analogously
$O(r+n_{\mathrm{rp}}m_{\mathrm{rp}}/\varphi+\log k_{\mathrm{sc}})$.

---

## 6. Soundness & Security

### 6.1 Lemma inventory

| Lemma | Statement (one line) |
|---|---|
| 1 | Trace-dual basis exists mod unramified prime $q$ |
| 2 | $\|\cdot\|_2$ vs $\|\cdot\|_{\sigma,2}$ conversions (see §3.2) |
| 3 | Packing preserves sub-MLEs via block prefixes |
| 4 | `COM` binding break ⇒ SIS break with $\mathrm{par}_{\mathrm{break}}$ |
| 5 | (Ring) JL: unstructured $\mathbf{J}$, $\Pr[\|Jw\|/\|w\|\notin[\alpha,\beta]]\le\kappa$ + modular form |
| 6 | Structured JL: $I\otimes\mathbf{J}$ block-diagonal, union bound over chunks/columns |
| 7 | $\Pi^{\mathrm{proj\text{-}c}}$: completeness/soundness/efficiency (see §5.1) |
| 8 | $\Pi^{\mathrm{proj\text{-}f}}$: two-stage extractor, $\kappa=(\log(\varphi rm_w/m_{\mathrm{rp}})/q)^{n_{\mathrm{bat}}}+(\varphi m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$ |
| 9 | $\Pi^{\mathrm{fold\text{-}split}}$: perfect completeness; $\kappa=r/|\mathcal{C}|$; coordinate-wise unfolding |
| 10 | `sumcheckify` correctness (inner product ⟺ hypercube sum) |
| 11 | $\Pi^{\mathrm{lin}}$: $\kappa=(\log k_{\mathrm{sc}}+(\mu+\rho)\delta_{\mathrm{sc}}+1)/q^a$ |
| 12 | $\Pi^{\mathrm{proj\text{-}fl}}$: tower lift-and-batch, $\kappa=\sum_i(n_{\mathrm{bat},i}/q^{e_i})^{n_{\mathrm{bat},i+1}}+(\varphi m_w/m_{\mathrm{rp}})\kappa_{\mathrm{rp}}$ |
| 13 | Basic sumcheck with C-linear $\Phi$: $\kappa\le\ell\deg(g)/|\mathcal{C}|$, linear-time prover |
| Conjecture 1 | Asymptotic JL scaling $\alpha,\beta,b=\Theta(\sqrt{\log(1/\kappa)})$ (Gaussian-tail heuristic; needed only for asymptotics, not concrete params) |

### 6.2 Extractor patterns (what an implementer must mirror in tests)

1. **Simple rewind (Lemmas 7, 8, 11)**: run once; if the extracted witness fails the input
   relation, rewind for a second accepting transcript with fresh challenges. Divergence of
   $(\mathbf{W}',\mathbf{s}')$ vs $(\mathbf{W}'',\mathbf{s}'')$ ⇒ output
   $\mathbf{W}'\mathbf{s}''-\mathbf{W}''\mathbf{s}'$ (a vSIS column witness with norm
   $\le2\beta'_w\varrho'$); divergence of any $\mathbf{Y}_i$ ⇒ commitment binding break ⇒ SIS
   (Lemma 4); else the honest witness satisfies the input relation except with the stated
   Schwartz–Zippel/JL probability.
2. **Two-stage (Lemma 8)**: first extract against the *inner* sub-protocol (challenges
   $\mathbf{Z},\mathbf{Z}^{(2)}$; proves the trace-consistency of $\mathbf{V}_{\mathrm{emb}}$),
   then against the *outer* (challenge $\mathbf{J}$; JL gives
   $\|\mathbf{W}^*\|\le\mathrm{cmp}(\beta'_{y})/\alpha_{\mathrm{rp}}$).
3. **Coordinate-wise rewinding (Lemma 9, [FMN24, Lemma 7.1])**: $r+1$ transcripts differing in
   exactly one challenge coordinate; unfold $\mathbf{u}^{(j)}=(\mathbf{v}^{*(j)}-\mathbf{v}^{*(r)})/s_j$;
   $O(r)$ prover invocations.

### 6.3 Norm/slack ledger — [R3]

- **Folding slack**: extraction from $\Pi^{\mathrm{fold\text{-}split}}$ yields
  $\mathbf{U}$ with $\|\mathbf{U}\,\mathrm{diag}(\mathbf{s})\|_2\le2\mathrm{cmp}_{\ell'}(\tilde\beta_w)$
  and $\|\mathrm{diag}(\mathbf{s})\|_{\mathrm{op},2}\le2\gamma_{\mathcal{C}}$ — i.e. the output
  instance is *relaxed* ($\varrho'=2\gamma_{\mathcal{C}}$).
- **Projection kills slack**: feeding the relaxed instance through
  $\Pi^{\mathrm{proj\text{-}c}}$/$\Pi^{\mathrm{proj\text{-}f}}$ at the *start of the next round*
  certifies $\|\mathbf{W}\|\le\mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}}$
  with **no** $\varrho$ factor (this is why every round begins with a projection).
- **Norm-growth budget per round** (Lemma 9 precondition):
  $\tilde\beta_w\ge\sqrt{\mathrm{dcmp}_{\ell'}(r\gamma_{\mathcal{C}}\beta_w)^2+\beta_x^2+\beta_y^2+\sum_i(\beta_{y,i}^2+\beta_{x,i}^2)}$.
- **No-wraparound side conditions**: $r'\beta_w'^2\hat f<q/2$ (Lemma 9) — with the power-of-two
  optimisation $r'\beta_w'^2<q/2$; and $\mathrm{cmp}(\beta'_{y,k_{\mathrm{lin}}})/\alpha_{\mathrm{rp}}<q/b$
  (Lemmas 7/8) for the modular-JL bound.
- **Norm identities**: $\mathrm{trace}(v)=\|\hat{\mathbf{w}}\|_{\sigma,2}^2\le\hat f\tilde\beta_w^2$
  (general); $\mathrm{ct}(v)=\|\mathrm{cf}(\hat{\mathbf{w}})\|_2^2$ (power-of-two, exact).

---

## 7. Parameters & Concrete Efficiency

### 7.1 Simplifying assumptions for asymptotics (§8.1)

- vSIS: $n=O(1)$ module rank, $\varphi=\Theta(\lambda)$; all commitment ranks $O(1)$;
  $\mathrm{COM}$ depth $d=1$ (so $m_x=0$, $\beta_x[\mathrm{par}_{\mathrm{com}}]=0$,
  $\#$constraints$=n\in O(1)$).
- Random projections: $n_{\mathrm{rp}}=O(\lambda)$, $m_{\mathrm{rp}}=\rho\cdot n_{\mathrm{rp}}$
  (i.e. $n_{\mathrm{rp}}/m_{\mathrm{rp}}=1/\rho$); witnesses $\mathbf{W}\in R^{m_w\times\rho}$
  throughout (asymptotic $\rho$ = shrink factor).
- Norm bound $\beta=\Theta(\sqrt{m_w}\lambda\log q)$; decomposition length $\ell=O(1)$.
- Batching: $\Pi^{\mathrm{proj\text{-}f}}$: $n_{\mathrm{bat}}=O(\lambda/\log\lambda)$;
  $\Pi^{\mathrm{proj\text{-}fl}}$: $n_{\mathrm{bat},0}\in O(\lambda/\log\lambda)$;
  $\Pi^{\mathrm{lin}}$: $a=O(\lambda/\log\lambda)$.
- Simplified relation parameters: $\Xi^{\mathrm{lin}}$ ⇝ $(k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,\beta_w,(n_i)_i)$;
  $\Xi^{\mathrm{sum}}$ ⇝ $(k_{\mathrm{sc}},m_w,\beta_w)$.

### 7.2 RoK summary table (Table 4; $O(\cdot)$ omits $k_{\mathrm{lin}},k_{\mathrm{lr}}$ factors; prover/verifier in $R_q$-ops, comm in $R_q$-elements)

| RoK | Parameter change | Prover | Verifier | Comm |
|---|---|---|---|---|
| $\Pi^{\mathrm{proj\text{-}c}}:\Xi^{\mathrm{lin}}\to\Xi^{\mathrm{lin}}$ | $k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+1$; $n_{k_{\mathrm{lin}}}=m_w/\rho$ | $O(m_w\rho\lambda)$ | $O(\rho\lambda/\log\lambda)$ | $O(1)$ |
| $\Pi^{\mathrm{proj\text{-}f}}:\Xi^{\mathrm{lin}}\to\Xi^{\mathrm{lin}}$ | $k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+2$; $n\mapsto n+n_{\mathrm{bat}}$; $n_{k_{\mathrm{lin}}}=m_w/\rho$; $n_{k_{\mathrm{lin}}+1}=n_{\mathrm{bat}}$ | $O(m_w\rho\lambda)$ | $O((\rho\lambda+\log(m_w\rho))/\log\lambda)$ | $O(\lambda/\log\lambda)$ |
| $\Pi^{\mathrm{proj\text{-}fl}}:\Xi^{\mathrm{lin}}\to\Xi^{\mathrm{lin}}$ | $k_{\mathrm{lin}}\mapsto k_{\mathrm{lin}}+2$; $n\mapsto n+1$; $n_{k_{\mathrm{lin}}}=m_w/\rho$; $n_{k_{\mathrm{lin}}+1}=1$ | $O(m_w\rho\lambda^2\log\lambda)$ | $O((\rho\lambda+\log(m_w\rho))/\log\lambda)$ | $O(\log\lambda)$ |
| $\Pi^{\mathrm{fold\text{-}split}}:\Xi^{\mathrm{lin}}\to\Xi^{\mathrm{sum}}$ | $k_{\mathrm{sc}}=O(n+\sum_i n_i)$; $m_w\mapsto O(m_w/\rho+\sum_i n_i\rho)$; $\beta_w\mapsto O(\beta)$; $n=0$, $n_0=O(1)$, $k_{\mathrm{lin}}=1$ | $O(m_w\rho)$ | $O(\rho/\log\lambda)$ | $O(1)$ |
| $\Pi^{\mathrm{lin}}:\Xi^{\mathrm{sum}}\to\Xi^{\mathrm{lin}}$ | $k_{\mathrm{lr}}=2$ | $O(m_w\rho+\rho\lambda^2)$ | $O(\rho\lambda^2+\log k_{\mathrm{sc}}+\log m_w)$ | $O(\log m_w/\log\lambda)$ |

Both chains ($\Pi^{\mathrm{lin}}\circ\Pi^{\mathrm{fold\text{-}split}}\circ\Pi^{\mathrm{proj\text{-}c}}$
"coarse" and with $\Pi^{\mathrm{proj\text{-}fl}}$ "fine") have net effect
$k_{\mathrm{lin}}\mapsto1$, $k_{\mathrm{lr}}\mapsto2$, $n\mapsto0$,
$m_w\mapsto O(m_w/\rho)$, $\beta_w\mapsto O(\beta)$, $(n_i)_i\mapsto(O(1))$.
Coarse chain totals: prover $O(m_w\rho\lambda)$, verifier $O(\rho\lambda^2+\log m_w)$,
comm $O(\log m_w/\log\lambda)$. Fine chain: prover $O(m_w\rho\lambda^2\log\lambda)$, same
verifier, comm $O(\log\lambda+\log m_w/\log\lambda)$.

### 7.3 Composition (§8.2–8.3) — [R4/R5]

Compose the coarse chain $O(\log_\rho m_w-\log_\rho\lambda)$ times until
$m'_w=O(n_{\mathrm{rp}})=O(\lambda)$, then the fine chain $O(\log_\rho\lambda)$ times down to
$O(1)$; finally the remaining witness is sent in the clear.

**Table 5** (composed succinct argument for $\Xi^{\mathrm{lin}}$, $O(\cdot)$ omitted):

| Shrink factor $\rho$ | Prover | Verifier | Comm |
|---|---|---|---|
| $\rho$ | $\rho m_w\lambda$ | $\rho\lambda^2\log_\rho m_w$ | $\log_\rho(m_w)\cdot\log m_w/\log\lambda$ |
| $2$ | $m_w\lambda$ | $\lambda^2\log m_w$ | $\log^2m_w/\log\lambda$ |
| $\lambda$ | $m_w\lambda^2$ | $\lambda^3\log m_w/\log\lambda$ | $\log^2m_w/\log^2\lambda$ |
| $(m_w\lambda)^{\log m_w/(\log\lambda\log\log m_w)}$ | $o(m_w^2\lambda)$ | $o(m_w\lambda^2)$ | $\log\log m_w$ |

$\rho=\lambda$ reflects the concrete implementation. With
$\rho=\lambda$: total prover $O(\rho m_w\lambda+\rho\lambda^2)=O(\rho m_w\lambda)$, verifier
$O(\rho\lambda^2\log_\rho m_w)$, communication
$O(\log_\rho(m_w)(\log\lambda+\log m_w/\log\lambda))$, dominated by
$O(\log_\rho(m_w)\log m_w/\log\lambda)$ for $m_w\gg\lambda$.

**Remark 5 (slack-tolerant fast path)**: PCS applications that tolerate slack in the *evaluation*
claim (committed polynomial need not have small coefficients) may **skip the very first
$\Pi^{\mathrm{proj\text{-}c}}$**; then with $\rho=\Omega(\lambda)$ the prover improves to
$O(m_w\lambda)$.

**Table 6** (asymptotic comparison vs SALSAA [KLOT25], $m$ = #coefficients of the committed
polynomial $=m_w\rho$; proof sizes in bits; both include the skip-first-projection
optimisation):

| $\rho$ | [KLOT25] Prover / Verifier / Comm | RoKoko Prover / Verifier / Comm |
|---|---|---|
| $2$ | $m\lambda$ / $\lambda^2\log m$ / $\lambda\log^3m/\log\lambda$ | $m\lambda$ / $\lambda^2\log m$ / $\lambda\log^3m/\log\lambda$ |
| $\lambda$ | $m$ / $\lambda^3\log m/\log\lambda$ / $\lambda^2\log^3m/\log^2\lambda$ | $m$ / $\lambda^3\log m/\log\lambda$ / $\lambda\log^3m/\log^2\lambda$ |

I.e. at $\rho=\lambda$: prover time asymptotically faster by $\lambda$, proof size smaller by
$\log\lambda$, verifier asymptotically larger by $\lambda/\log\lambda$ (the latter is an
artifact of not exploiting projection-constraint structure; the implementation is much faster).

### 7.4 PCS instantiation (§8.3) — [R4]

Commitment key = a `COM` key + a random row-tensor matrix
$\mathbf{F}\in R_q^{n\times\otimes_{i\in[\mu]}d_i}$ with $m_w=\prod_i d_i$. To commit to
polynomial $p$ with coefficient matrix $\mathbf{W}\in R^{m_w\times\rho}$ (tensor-structured
basis): compute $\mathbf{V}=\mathbf{FW}\bmod q$, $\mathbf{Y}=G^{-1}_\ell(\mathbf{V})$,
$(\mathrm{com},\mathrm{aux})\leftarrow\mathrm{COM.Commit}(\mathrm{ck},\mathrm{vec}(\mathbf{Y}))$.
Evaluation claim $p(\mathbf{v})=t$: write
$p(\mathbf{v})=(\mathbf{r}^{\top}\otimes\boldsymbol\ell^{\top})\mathrm{vec}(\mathbf{W})$ with
$\boldsymbol\ell\in R^{m_w/\rho}$, $\mathbf{r}\in R^{\rho}$ (evaluations of the basis
polynomials) — a $\Xi^{\mathrm{lin}}_{\mathrm{COM}}$ instance:
$\mathrm{COM.Verify}=1$, $\mathbf{FW}=G_\ell\mathbf{Y}$, $\boldsymbol\ell^\top\mathbf{Wr}=t$,
$\|\mathbf{W}\|\le\beta_w$, $\|\mathbf{Y}\|\le\beta$, with
$(k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\beta_w,(n_i))=(1,1,0,m_w,\rho,\beta_w,(O(1)))$.
Starting from $\Xi^{\mathrm{sum}}_{\mathrm{COM}}$ instead gives a **SNARK for R1CS** (R1CS
constraints are sumcheck-expressible; the verifier additionally evaluates MLEs of the public
R1CS matrices).

### 7.5 Concrete numbers (§9, Tables 1, 7, 8)

**Setup (Table 7)**: 11th-gen Intel i7-11850H @2.50GHz (AVX-512-IFMA), 256KiB L1, 10MiB L2,
24MiB L3, 64GiB RAM, Ubuntu 24.04, Rust 1.95-nightly / g++ 13.3; single-threaded (16 threads for
the parallelised commitment variant, in parentheses). Server: 2×32-core Xeon 8562Y+,
2048GiB DDR5-5600.

**Table 1** (laptop; witness bit-width 32 bits matching Greyhound; SALSAA row uses its original
10-bit witness setting; medians of 3 runs; $\dagger$ = needed >64GiB):

| Scheme | $\#\mathbb{Z}_q=2^{26}$: Comm / P / V / $\|\pi\|$ | $2^{28}$ | $2^{30}$ |
|---|---|---|---|
| Brakedown | 36s / 3.21s / 0.703s / 49157 KB | 150s / 13s / 2.56s / 93767 | 605s / 48.6s / 2.96s / 181948 |
| Ligero | 39.9s / 3.11s / 0.196s / 7256 | 169s / 12.4s / 0.402s / 14383 | 717s / 50s / 0.846s / 28631 |
| FRI | 168s / 185s / 0.041s / 740 | — | — |
| WHIR | 210s / 5.4ms / 689 | 860s / 6.1ms / 770 | 3700s / 6.6ms / 848 |
| CMNW24 | — / — / — / 1546 | — / — / — / — | — / — / — / 5296 |
| HSS24 | 188s / 1.07s / 48640 | — | — |
| Papercraft | — | 1593s / 5.10s / 18940 | 6986s / 6.00s / 29790 |
| KLNO25 | — / — / — / 2181 | — / — / — / 2604 | — / — / — / 3152 |
| Greyhound | 4.80s / 1.41s / 0.42s / 46 | 18.62s / 5.41s / 0.75s / 53 | $\dagger$ |
| SALSAA | 0.80s / 26.46s / 4.56ms / 1092 | 3.29s / 118.69s / 5.58ms / 1295 | $\dagger$ |
| **RoKoko** | **0.80s (0.25s) / 1.47s / 8.12ms / 112** | **3.11s (0.94s) / 3.17s / 7.82ms / 112** | **16.0s (4.79s) / 9.41s / 12.1ms / 112** |

**Table 8** (server): RoKoko $2^{26}$: 1.02s (0.16s) / 1.64s / 9.39ms / 112;
$2^{28}$: 3.96s (0.57s) / 3.60s / 9.14ms / 112; $2^{30}$: 19.50s (2.29s) / 10.95s / 16.05ms / 112
(vs Greyhound $2^{30}$: 88.39s / 26.81s / 1.73s / 53; SALSAA $2^{30}$: 17.58s / 445.3s / 6.66ms / 1498).

Other concrete facts: proofs flat at 112 KB across sizes (strongly-compressing first round);
$\lambda=128$, $\kappa\approx2^{-100}$ (dominated by NTT-slot count); witness $\ell_\infty=2^{31}$;
statistical soundness and security estimated with the Lattice Estimator [APS15] in an
"estimator mode" that accounts for extraction norm growth.

---

## 8. Implementation Notes

### 8.1 Module map (Python package `lzk` reuse)

| RoKoko concept | `lzk` core-engine reuse | New code needed |
|---|---|---|
| $R_q$, incomplete NTT, $\mathbb{F}_{q^2}$ slots | `lzk.ring` ($\mathbb{Z}_q[x]/(x^n+1)$ with NTT) — extend with residue-degree-2 slots | slot arithmetic $(a+bX)(c+dX)$ in $\mathbb{Z}_q[X]/(X^2-\psi_i)$; Karatsuba $(ad+bc)$ trick |
| vSIS keys $\mathbf{A}_{n,2^\mu}$, Ajtai commit | `lzk.commit` (Ajtai/SIS) | row-tensor key family + **recursive** `COM` (Fig. 1) |
| Gadget $G_\ell$ / $G^{-1}_\ell$ | `lzk.gadget` | balanced digits base $2^{16}$, adaptive $\ell$ |
| MLE / eq / tensor / LDE | `lzk.tensor` | prefix-selector bookkeeping for `pack` |
| Multilinear sumcheck | `lzk.sumcheck` | **ring** sumcheck with C-linear $\Phi$ + CRT-slot batching (Fig. 7 + C.2) |
| Fiat–Shamir | `lzk.transcript` (BLAKE3 in the reference; any RO) | domain-separation per RoK/round |
| Norm utils | — | $\mathrm{ct}(\cdot)$, $\mathrm{trace}(\cdot)$, trace-dual basis $b^\vee$, $\mathrm{dcmp}/\mathrm{cmp}$ |

### 8.2 Data structures

- **Row-tensor matrices**: store as a list of $\mu$ factors $\in R_q^{n\times2}$ (never
  materialise the $n\times2^\mu$ matrix). MLE evaluation of a row:
  $\prod_k(f_{k,0}+(f_{k,1}-f_{k,0})s_k)$.
- **Packed witness** $\hat{\mathbf{w}}$: a flat array + a *block table*
  $\{(p_i,\text{offset},\text{len},\text{shape})\}$ recording each sub-vector
  ($\tilde{\mathbf{w}}$, $\mathrm{vec}(\mathbf{Y}_i)$, $\mathbf{x}_i$) sorted by decreasing
  length. This table is what `sumcheckify` selectors and the verifier's $\mathrm{eq}(p_i,\cdot)$
  evaluations consume.
- **Instance state machine** for the round loop:
  $\Xi^{\mathrm{lin}}_{\mathrm{COM}}\xrightarrow{\Pi^{\mathrm{proj}}}\Xi^{\mathrm{lin}}_{\mathrm{COM}}
  \xrightarrow{\Pi^{\mathrm{fold\text{-}split}}}\Xi^{\mathrm{sum}}_{\mathrm{COM}}
  \xrightarrow{\Pi^{\mathrm{lin}}}\Xi^{\mathrm{lin}}_{\mathrm{COM}}$; carry
  $(k_{\mathrm{lin}},k_{\mathrm{lr}},n,m_w,r,\beta_w,(\mathrm{par}_{\mathrm{lin},i})_i,\varrho)$
  explicitly and recompute derived quantities ($m_y$, $\beta_x[\cdot]$, $\hat m_w$) per step.
- **Challenge set** $\mathcal{C}$: ternary coefficients (bias 1/3), rejection-sampled on
  $\|\cdot\|_{\mathrm{op}}\le\gamma$; precompute $\gamma_{\mathcal{C}}$ empirically.

### 8.3 Per-step prover complexity (single round)

| Step | Cost | Dominated by |
|---|---|---|
| $\mathbf{V}=(I\otimes\mathbf{J})\mathbf{W}$ (coarse) | $O(m_wr n_{\mathrm{rp}})$ add/sub only | structured projection |
| Fine projection $\mathbf{V}_{\mathrm{tr}}$ | $O(m_wr n_{\mathrm{rp}}\varphi)$ integer ops | coefficient-level JL |
| $\mathbf{V}_{\mathrm{bat}}=\mathbf{ZV}$ | $O(n_{\mathrm{bat}}m_wr)$ $R_q$-ops | batch matrix |
| `COM` commitments | $O(\text{rank}\times\text{len})$ | matvec with short second operand |
| Fold + decompose $\tilde{\mathbf{w}}=G^{-1}_{\ell'}(\mathbf{Wc})$ | $O(\ell'm_wr)$ | column combination + digits |
| $v=\langle\hat{\mathbf{w}},\bar{\hat{\mathbf{w}}}\rangle$ | $O(\hat m_w)$ ring mults | Hermitian self-product |
| $\mathbf{U}$, $\mathbf{Y}=G^{-1}_{\ell''}(\mathbf{FU})$ | $O(\ell''n\hat m_w/r')$ | vSIS matvec + digits |
| sumcheckify + sumcheck | $O(\delta_{\mathrm{sc}}\hat m_w)$ = $O(\hat m_w)$ | table bookkeeping |
| $\Pi^{\mathrm{lin}}$ | $O(m_w r)$ + $O(\delta_{\mathrm{sc}}(\mu+\rho)\cdot)$ | MLE evals + sumcheck |

**Sumcheck prover bookkeeping (the linear-time trick)**: maintain partially-evaluated factor
tables $T^{(0)}_i,T^{(1)}_i$ (size $\hat m_w/2^i$) for the two MLE arguments; per round compute
the $\delta_{\mathrm{sc}}+1$ univariate coefficients by combining tables (for degree 2:
$c_0=\sum A_0B_0$, $c_1=\sum(A_0B_1+A_1B_0)$, $c_2=\sum A_1B_1$), then update tables with the
challenge (linear combinations). Total $O(\hat m_w)$; *no* NTT/convolution anywhere in the norm
check (this is RoKoko inheriting SALSAA's $O(m)$ norm trick — see the SALSAA doc §5).

### 8.4 Verifier per round

Sample $\mathbf{J}$ ($n_{\mathrm{rp}}m_{\mathrm{rp}}$ ternary entries — derive from the FS
transcript), $\mathbf{c}\in\mathcal{C}^r$, $\boldsymbol\gamma$, $\boldsymbol\delta$, $\mathbf{c}_0,\mathbf{c}_1$
(sumcheck rounds), run $\nu=\mu+\rho$ sumcheck round-checks over $\mathbb{F}_{q^a}$, one final
$f_{\mathrm{sc}}(z_0,z_1)(\mathbf{c})$ evaluation via tensor factorisation
($O(r+n_{\mathrm{rp}}m_{\mathrm{rp}}+\log k_{\mathrm{sc}})$, Corollary 1), and the norm check
$\mathrm{ct}(v)\le\tilde\beta_w^2$ over the integers.

### 8.5 Ring arithmetic (reference implementation details)

- Two variants: (1) FFI to Intel **HEXL** — one degree-$\varphi$ multiplication in incomplete-NTT
  form = 7 HEXL calls (5 element-wise mod-muls + 2 mod-adds over length-$\varphi/2$ vectors,
  schoolbook per-slot); (2) pure-Rust re-implementation with a **single fused AVX-512 kernel**
  (one pass, loads all inputs/writes both outputs per index) + **Karatsuba per slot**
  $(a_ic_i+b_id_i\to$ via $(a_i+b_i)(c_i+d_i)-a_ic_i-b_id_i)$: 4 mod-muls instead of 5 per slot.
  Combined speedup 1.36–1.63× over HEXL/[CCC+25] for $\varphi\in\{2^7..2^{14}\}$; Dekker-based
  floating-point modmul identical to HEXL.
- **Projection arithmetic**: AVX-512 matrix-vector with delayed modular reduction (accumulate
  several adds/muls before reducing).
- **Commitment trick**: never evaluate $\mathbf{FW}$ over $R_q$; the committed witness has
  balanced base-$2^{16}$ digits, so compute $\mathbf{FW}$ exactly over $\mathbb{Z}$ modulo a
  product of NTT-friendly primes $<2^{14}$, reduce to $q$ once at the end.
- **Final-level trick (protocol deviation)**: allow an even more aggressive norm decomposition on
  the final level of the recursive commitment and prove its norm as an *additional constraint in
  $f_{\mathrm{sc}}$*; reduces final-level rank and proof size.
- Non-interactivity: Fiat–Shamir with **BLAKE3**; single-threaded reference; intensive unit
  tests; "estimator mode" reports the estimated $\lambda$ accounting for extraction norm growth.

### 8.6 Pitfalls & edge cases

1. **$\rho$ symbol collision**: the paper uses $\rho$ both for the composition shrink factor and
   for $\log r$ inside $\Pi^{\mathrm{lin}}$ (challenges $\mathbf{c}_0\in\mathbb{F}_{q^a}^{\rho}$).
   Name them `shrink_rho` and `log_r` in code.
2. **Norm convention mismatch with SALSAA**: RoKoko's default norm is *coefficient* $\ell_2$;
   SALSAA's is *canonical*. When porting SALSAA RoKs, convert with
   $\|\cdot\|_{\sigma,2}=\sqrt\varphi\|\cdot\|_2$ (power-of-two, exact) and swap
   $\mathrm{trace}$-checks for $\mathrm{ct}$-checks.
3. **Divisibility conditions**: coarse needs $m_{\mathrm{rp}}\mid m_w$; fine needs
   $m_{\mathrm{rp}}\mid\varphi m_w$ (and $m_w n_{\mathrm{rp}}/m_{\mathrm{rp}}$ blocks for
   $\mathrm{cf}^{-1}$ repacking to be integral). Track these in the parameter scheduler; switch
   coarse→fine exactly when $m_w<m_{\mathrm{rp}}$ (paper: "as late as possible").
4. **Packing order**: `pack` requires *decreasing* dimension order or Lemma 3 breaks — sort
   blocks before concatenation and record prefixes.
5. **Hermitian vs bilinear inner products**: the norm constraint needs the *conjugate* factor;
   linear constraints must use the *non-conjugated* MLE argument. The conjugation identity
   $\overline{\mathrm{MLE}[\mathbf{w}](\mathbf{c})}=\mathrm{MLE}[\overline{\mathbf{w}}](\bar{\mathbf{c}})$
   must hold in the test suite.
6. **Zero padding in `COM`**: level-0 decomposition is padded to $\minpowtwo(\ell_0n_0)$ *before*
   the recursive call; the gadget matrix in the verify equation is $(G_{\ell_0}\Vert 0)$ with the
   matching zero columns.
7. **No-wraparound guards**: assert $r'\beta_w'^2\hat f<q/2$ (or the power-of-two
   $r'\beta_w'^2<q/2$) and $\mathrm{cmp}(\beta'_{y})/\alpha_{\mathrm{rp}}<q/b$ at parameter-selection
   time — these are *correctness* conditions for integer-lift arguments, not just security.
8. **Challenge invertibility**: ternary challenges are not a strong sampling set — the
   non-invertible-difference probability ($\approx\varphi/(eq^e)\approx2^{-94}$) is a *heuristic*
   (bound from [BL25, Lemma 32] with bias $p=1/3$, roots $r_j$ of $\xi^\varphi+1$); also enforce
   the operator-norm rejection filter.
9. **Row bookkeeping across RoKs**: `sumcheckify` row count
   $k_{\mathrm{sc}}=\sum_i k_i+\sum_i n_i+n+k_{\mathrm{lr}}+1$ must include the commitment
   verification constraints of *every* block $i\in[k_{\mathrm{lin}}+1]$ (the two new ones
   included) — forgetting them silently breaks extraction.
10. **$\Pi^{\mathrm{proj\text{-}f}}$ lift typing**: the figure's
    $(I_{\varphi m_w/m_{\mathrm{rp}}}\otimes\mathrm{cf}^{-1}_\vee(\mathbf{J}^\top)^\top)\mathbf{W}$
    mixes ring and coefficient domains; implement the projection as
    $\mathbf{V}_{\mathrm{tr}}:=(I_{\varphi m_w/m_{\mathrm{rp}}}\otimes\mathbf{J})\cdot\mathrm{cf}(\mathbf{W})$
    over $\mathbb{Z}_q$, then $\mathbf{V}_{\mathrm{emb}}:=\mathrm{cf}^{-1}(\mathbf{V}_{\mathrm{tr}})$,
    and certify consistency with the trace identities + $\mathbf{Z}$-batching (validate against
    the completeness equations in §5.2 on random small instances).
11. **Fine-projection block `klin` has $F=H=0$** — its constraint is *not* a linear block; it is
    enforced through the $\mathbf{A}'$ rows and trace checks. Do not emit an $F\mathbf{W}=H\mathbf{Y}$
    row for it.
12. **Memory**: the packed vector $\hat{\mathbf{w}}$ plus all $\mathbf{Y}_i$ live simultaneously;
   at $2^{30}\mathbb{Z}_q$ scale this is tens of GB — plan streaming/parallel commitment (the
   reference gets 3–5× from 16 threads on the commitment only).

### 8.7 Suggested `lzk` test lattice (per RoK)

- `test_com_recursive`: Fig. 1 commit/verify round-trip for depths $d\in\{1,2,3\}$, random
  $\mathrm{par}_{\mathrm{com}}$; binding-break → SIS reduction (Lemma 4) on crafted collisions.
- `test_proj_c`: completeness of Fig. 2 on random $\Xi^{\mathrm{lin}}$ instances; check
  $\beta_{y,k_{\mathrm{lin}}}=\mathrm{dcmp}_\ell(\beta_{\mathrm{rp}}\beta_w)$ holds for honest
  witnesses (JL sanity: $\|\mathbf{V}\|\le\beta_{\mathrm{rp}}\beta_w$).
- `test_proj_f`: the trace identities
  $\mathrm{trace}(\mathrm{cf}^{-1}_\vee(\mathbf{u})\cdot w)=\langle\mathbf{u},\mathrm{cf}(w)\rangle$
  and $\mathrm{trace}(r_i)=0$ for honest provers.
- `test_fold_split`: perfect completeness; norm budget lemma-precondition satisfied; the six
  `sumcheckify` constraint families individually zero-sum.
- `test_sumcheckify` (Lemma 10): random constraints, property "⟺".
- `test_lin`: end-to-end $\Xi^{\mathrm{sum}}\to\Xi^{\mathrm{lin}}$; knowledge-error sanity by
  fixing a cheating prover and measuring acceptance over random $\boldsymbol\gamma$.
- `test_round_trip`: one full round $m_w\mapsto m_w/\rho$; compare prover op-count against
  $O(\hat m_w)$ scaling.

---

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*

R1 — core tensor RoK + projections:
R2 — committed refinement (recursive `COM`, $\Pi^{\mathrm{fold\text{-}split}}$):
R3 — norm/slack management:
R4 — PCS composition:
R5 — SNARK end-to-end:
