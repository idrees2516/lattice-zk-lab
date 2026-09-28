# PikkuFold: Efficient Folding in a Few Kilobytes — Deep Analysis & Implementation Spec

## 1. Metadata

| Field | Value |
|---|---|
| Title | PikkuFold: Efficient Folding in a Few Kilobytes |
| Author | Michał Osadnik (Aalto University, Finland) |
| Venue / status | Manuscript improving on SALSAA (ePrint 2025/2124) and Cyclo (EUROCRYPT 2026); builds on the RoKoko [KLN+26] codebase; companion artifacts on github.com/osdnk/pikku |
| Assumption | Ring-SIS $\mathrm{SIS}_{R,q,m,n,\beta}$ over cyclotomic rings (Ajtai-style commitments $\mathbf{F}\mathbf{w} = \mathbf{y} \bmod q$, $\|\mathbf{w}\|\le\beta$); knowledge soundness reduces either to input-relation witnesses or to a same-key SIS break |
| Headline contribution | A lattice folding scheme where **one folding step communicates 5.7 KB beyond the fresh-input commitments** (vs ≥ 30 KB Cyclo, ≥ 60 KB SALSAA), prover > 10× faster than SALSAA's implementation, verifier in the millisecond range. Enabling ideas: (i) **layered random projections (LRP)** — a product of Kronecker-structured ternary JL layers whose final image is short enough to *send directly*, eliminating all auxiliary in-protocol commitments; (ii) a certified Johnson–Lindenstrauss theorem for biased ternary matrices modulo $q$ with concrete constants (replacing heuristics of [GHL22, BS23]); (iii) a fixed-Hamming-weight, operator-norm-rejection challenge sampler with concrete tradeoffs (drop-in improvement for many lattice protocols). First lattice-based folding scheme with zero in-protocol commitments. |

Additional independent-interest contributions (C2), (C3): the JL theorem (Theorem 2 + Table 1) and the sampler analysis (Lemma 18/19, Heuristic 1, Tables 3–4) are usable outside folding (SNARKs, NIST-threshold-style protocols). The scheme folds *principal relations* (Ajtai commitment + multilinear evaluation claim), and Section 7 shows (a) periodic exact-norm-check + decomposition checkpoints remove the bounded-depth limitation, and (b) an AIR reduction produces exactly the relations $\Pi_{\mathrm{fold}}$ consumes, giving a folding scheme for AIR.

Prior-work landscape (Section 1.1 taxonomy) — norm growth handling in lattice folding:
- Correctness direction (folded witness grows): **decomposition + recommitment** [FKNP24, BC25a, BC25b, NS26, KLOT25, partly BNP26] — costs communication.
- Extraction direction (extracted witness grows): four families:
  - (A1) range proof via polynomial identity (sumcheck, cost linear in $\beta$ — impractical for superconstant $\beta$) [BC25a, NS26, GLLO26];
  - (A2) range proof via monomial decomposition [BC25b] (needs commitment to decomposition + extra sumcheck; expensive per [GLLO26]);
  - (A3) approximate norm certificate via JL projection [Osa26, KLOT25] (image too long → must commit → extra accumulator relation);
  - (A4) subtractive-set extraction [AL21] (sets too small → amplification).
- **Cyclo's observation**: prove norm bounds only on *fresh inputs*, never combine the accumulator commitment with challenges → **additive** norm growth (linear in #folds, both directions) and a single-relation accumulator; but Cyclo then needs (A1) on inputs (small-$\beta$ inputs only) or an expensive "extension commitment" (~10 KB) for large norms.
- **PikkuFold's question**: can we get (i) small additive growth both directions, (ii) no additional Ajtai commitments during folding, (iii) folding cost independent of $\beta$? → **Yes** (Theorem 1).

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $\lambda$ | Security parameter; concrete levels $\{64,96,128,192,256\}$ |
| $f$ | Cyclotomic conductor, $f \bmod 4 \neq 2$; power-of-two case $f = 2\phi$ |
| $\phi := \varphi(f)$ | Degree of $K = \mathbb{Q}(\zeta_f)$ |
| $R := \mathcal{O}_K$, $R_q := R/qR$ | Ring of integers and its modular quotient; $R_q^\times$ units |
| $(b_i)_{i\in[\phi]}$ | Powerful $\mathbb{Z}$-basis of $R$ (power basis for prime-power conductors; tensor of power bases otherwise [LPR13]) |
| $\mathrm{coeff}(x)$ | Coefficient embedding $(x_i)_{i\in[\phi]} \in \mathbb{Q}^\phi$ in the powerful basis; balanced lift for $R_q$ objects |
| $\sigma(x)$, $\sigma_i$ | Canonical embedding into $\mathbb{C}^\phi$; the $\phi$ embeddings |
| $H$ | Canonical real tensor space $\{z: z_{\bar i} = \overline{z_i}\}$ where $i\mapsto\bar i$ is the conjugation permutation |
| $\|\cdot\|$ | **Default: coefficient $\ell_2$ norm** $\|\mathrm{coeff}(x)\|_2$; Euclidean for real/complex vectors |
| $\|\cdot\|_{\mathrm{coeff},\infty}$, $\|\cdot\|_{\sigma,2}$, $\|\cdot\|_{\sigma,\infty}$ | Other coefficient/canonical norms |
| $\bar f$ | $f$ if $f$ odd, $f/2$ if $f$ even |
| $\mathrm{rad}(f)$, $c_{\mathrm{rad}}(f)$ | Product of distinct prime divisors; $c_{\mathrm{rad}}(f)\le(4/\pi)^s$, $s$ = # odd prime divisors |
| $\|c\|_{\mathrm{op}}$ | Coefficient-$\ell_2$ multiplication operator norm $\sup_{x\ne0}\|cx\|/\|x\|$; equals $\|c\|_{\sigma,\infty}$ for power-of-two conductors (Lemma 2) |
| $\mathrm{Tr} := \mathrm{Tr}_{K/\mathbb{Q}}$ | Field trace; $\mathbb{Z}_q$-linear on $R_q$; entry-wise on vectors/matrices |
| $(b_i^\vee)_{i\in[\phi]}$ | Trace-dual basis: $\mathrm{Tr}(b_ib_j^\vee) = \delta_{i,j} \bmod q$ (Lemma 3) |
| $\mathrm{Lift}_{\mathrm{fine}}$, $\mathrm{Lift}_{\mathrm{coarse}}$ | Fine lift (via dual basis, blocks of $\phi$) and coarse lift ($\mathbb{Z}_q\to R_q$ entry-wise) — Definition 8 |
| $\mathrm{NTT}$ | $R_q \to (\mathbb{F}_{q^e})^{\phi/e}$ when $\Phi_f$ factors into $\phi/e$ irreducibles of degree $e$ |
| $\theta_a$ | $\mathbb{F}_{q^a}$-linear expansion of NTT slots: $R_q\to(\mathbb{F}_{q^a})^{\phi/a}$, $a \mid e$ |
| $\Phi_\delta$ | Subfield batching map $R_q\to\mathbb{F}_{q^a}$: $\Phi_\delta(x) = \delta^T\theta_a(x)$, $\delta\leftarrow\$(\mathbb{F}_{q^a})^{\phi/a}$; error $q^{-a}$ (Lemma 5) |
| $C\subseteq R$ | Challenge set; strong sampling ($c-c'$ unit $\forall$ distinct) or $\epsilon_C$-approximate (Definition 11) |
| $\Gamma_C$ | Expansion factor $\max_{c\in C}\|c\|_{\mathrm{op}}$ |
| $[\pm q/2]$ | Balanced representatives $\{-\lceil q/2\rceil+1,\dots,\lfloor q/2\rfloor\}$ |
| $\mathrm{eq}(b,x)$, $\widetilde{\mathrm{eq}}(x)$ | Equality polynomial and expanded tensor vector (Definition 13) |
| $\mathrm{MLE}[w]$, $\mathrm{MLE}[A]$ | Multilinear extensions (Definition 14): $\mathrm{MLE}[w](x) = \widetilde{\mathrm{eq}}(x)^T w$ |
| $\mathrm{LMLE}[M]$ | **Layered** multilinear extension over layer boundaries (Definition 24) |
| $\mathrm{RingSC}$ | Ring sumcheck (Definition 15): subfield-batched standard sumcheck over $\mathbb{F}_{q^a}$ |
| $\kappa_{\mathrm{sc}}(\ell,D)$ | RingSC soundness $(\ell D + 1)/q^a$ |
| $\chi$ | Ternary entry distribution: $\Pr[0]=1/2$, $\Pr[\pm1]=1/4$ |
| $n_{\mathrm{rp}}(\kappa),\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}},b$ | JL projection guarantee parameters (Definition 16): rows, lower/upper norm factors, wrap-around margin |
| $\gamma_1,\alpha,\beta,b$ | Concrete JL constants (Theorem 2, Table 1) |
| $\Xi^{\mathrm{lin}}_{R,q,m,n,\beta}$ | Principal relation (Definition 22) |
| $\Xi^{\mathrm{SIS}}_{R,q,m,n,\beta}$ | SIS-break relation (Definition 26) |
| $\mathrm{str}(\cdot) = \mathbf{F}$ | Commitment-key structure map (Definition 25) |
| $k$ | Folding arity (# fresh inputs per fold); $2t$ for AIR |
| $\mathbf{F}\in R_q^{n\times m}$, $\mathbf{y}$, $\mathbf{w}$ | Commitment key, image, witness ($\mathbf{F}\mathbf{w} = \mathbf{y} \bmod q$) |
| $\mathbf{s}, t$ | Evaluation point $\in R_q^{\log_2 m}$ and claimed value: $\mathrm{MLE}[w](\mathbf{s}) = t$ |
| $d$ | Number of projection layers |
| $(r_j, m_j, n_j)_{j\in[d]}$ | Layer dimensions; compatibility $r_j m_j = r_{j-1} n_{j-1}$; $r_{d-1} = 1$ |
| $N_j$ | Boundary sizes: $N_0 = km$, $N_{j+1} = r_jn_j = r_{j+1}m_{j+1}$, $N_d = n_{d-1}$ (rings for $j<d$, $\mathbb{Z}_q$ coords for $j=d$) |
| $\nu_j := \log_2 N_j$ | Variable counts per boundary; $L_{\mathrm{sc}} := \sum_j \nu_j$ sumcheck rounds |
| $\varsigma$ | Constant layer shrinkage $N_{j+1} = N_j/\varsigma$ (Corollary 1) |
| $J_j$, $M_j$ | Raw ternary layer ($\chi^{n_j\times m_j}$) and its lifted ring form ($\mathrm{Lift}_{\mathrm{coarse}}$, last $\mathrm{Lift}_{\mathrm{fine}}$) |
| $P$, $M$ | Integer layered matrix and ring layered matrix (Lemma 10: $\mathrm{Tr}(Mw) = P\,\mathrm{coeff}(w)$) |
| $w_{\mathrm{all}}$ | Vertical concatenation of the $k$ **fresh** witnesses only (no accumulator!) |
| $\mathbf{v}_{\mathrm{proj}}, \mathbf{v}_{\mathrm{tr}}$ | $M w_{\mathrm{all}} \bmod q$ and its trace $\mathrm{Tr}(\mathbf{v}_{\mathrm{proj}}) \bmod q$ — the sent norm certificate |
| $\mu$ | Number of trace-batching points (concrete: 2) |
| $(\mathbf{c}_i)_{i\in[\mu]}$ | Trace-batching challenges $\leftarrow\$ \mathbb{Z}_q^{\log_2 N_d}$ |
| $\mathbf{b}_{\mathbf{c}_i}$, $\mathbf{v}_{\mathrm{btd}}$ | Tensor vector $\widetilde{\mathrm{eq}}(\mathbf{c}_i)\in\mathbb{Z}_q^{N_d}$ and batched projections $\langle \mathbf{b}_{\mathbf{c}_i}, \mathbf{v}_{\mathrm{proj}}\rangle$ |
| $(d_u)_{u\in[h-1]}$, $h$ | Claim-batching coefficients $d\leftarrow\$ R_q^{h-1}$, $h = \mu + k + 1$ |
| $\mathbf{z}\leftarrow\$ C^k$ | Folding challenges |
| $\beta_{\mathrm{in}}, \beta_{\mathrm{acc}}, \beta_{\mathrm{out}}$ | Input / accumulator / output norm bounds |
| $\beta'_{\mathrm{in}}$ | Extraction-side input bound $\omega/\prod_j \ell_j$ |
| $\omega$ | Norm-certificate threshold: $\sqrt{k}\,\beta_{\mathrm{in}}\prod_j u_j$ |
| $\ell_j, u_j, b_j$ | Per-layer JL constants $\alpha_{\mathrm{rp}}(\kappa_j), \beta_{\mathrm{rp}}(\kappa_j), b(\kappa_j)$ |
| $\kappa_{\mathrm{proj}} := \sum_j \eta_j\kappa_j$ | Layered projection failure probability; $\eta_j = \phi r_j$ (or 1 at the fine boundary) |
| $\beta_{\mathrm{bind}}, \rho_{\mathrm{bind}}$ | $(k+1)\beta'_{\mathrm{out}}(2\Gamma_C)^k$ and $(2\Gamma_C)^k$ — temporary binding bounds |
| $\beta_{\mathrm{sis}}$ | SIS-break bound: $\max\{8\Gamma_C\beta'_{\mathrm{out}}, 2\beta_{\mathrm{bind}}\rho_{\mathrm{bind}}\}$ (Theorem 1); improved to $6\Gamma_C\beta'_{\mathrm{out}}$ (Appendix A / Remark 3) |
| $C^{\mathrm{fw}}_{f,s,B}$ | Bounded fixed-weight challenge set: $s$ non-zero coefficients in $[-B,B]$ |
| $\gamma$, $p_S(\gamma)$ | Operator-norm rejection threshold and acceptance rate (Definition 31) |
| $S_{\mathrm{lay}}, S_{\mathrm{JL}}$ | $\sum_j r_jn_jm_j$ (expanded ring entries) and $\sum_{j<d} n_jm_j + \phi n_{d-1}m_{d-1}$ (ternary entries) |
| $\mathrm{bin}(i)$ | Little-endian binary expansion |
| $q = 2^{50} - 2687$ | Implementation prime (almost-splitting, $e = a = 2$); estimates use $q = 2^{64}-59$ |
| $\beta^*$ | Largest norm at which SIS for $\mathbf{F}$ assumed hard (Section 7.1) |
| $\beta_{\mathrm{reset}}, \beta_{\mathrm{cap}}$ | Post-checkpoint norm; exact-norm-check cap |
| $\beta_{\mathrm{dig}}$ | Decomposition digit bound; $\mathbf{w} = \sum_j b^j\mathbf{w}_j$ |

### 2.5 Notation Table (continued)

Sub-notation used inside the soundness section and appendices:

| Symbol | Meaning |
|---|---|
| $u^{(j)}, \hat u^{(j)}$ | Output witnesses of forked transcripts (Stage 1); hatted = second family (independent coins) |
| $\mathbf z^{(i)}, \mathbf z^{(k)}$ | Forked folding-challenge vectors; $\mathbf z^{(i)}$ differs from $\mathbf z^{(k)}$ only in coordinate $i$ |
| $\Delta_i, \Delta, \Delta_{-i}$ | $z^{(i)}_i - z^{(k)}_i$; product $\prod_i\Delta_i$; product over $j\ne i$ |
| $\mathbf a_i, \mathbf a_{\mathrm{acc}}$ | Numerator differences $u^{(i)} - u^{(k)}$; denominator-cleared accumulator numerator |
| $\mathbf w_i^*, \mathbf w_{\mathrm{acc}}^*$ | Normalised (divided) candidate witnesses — no norm bound individually |
| $\tilde w_{\mathrm{acc}}$ | Additively reconstructed accumulator witness (Stage 4) |
| $\mathbf b_{\mathbf c}, \mathbf b_{\hat{\mathbf c}}$ | Fork values in Appendix A's Lemma 20 ($\zeta_i, \hat\zeta_i$) and their baselines ($u, \hat u$) |
| $\Psi = 0.5508$ | Uniform Laplace-transform bound $\sup_{\|w\| = 1}L_w(s^\times)$ |
| $s^\times \approx 2.31057$ | Envelope crossover point; $\mathrm{env}(s^\times)\approx0.549602$ |
| $\kappa_{\mathrm{BD}}\approx3.178$ | Bentkus–Dzindzalieta optimal Rademacher comparison constant |
| $\mu_0 = 0.45$ | "Large coordinate" threshold (at most 4 large coordinates for unit vectors) |
| $T_\lambda, D_\lambda, r_\lambda$ | Modular-bound auxiliary constants (Table 2) |
| $A_\lambda, C_\lambda, \delta_\lambda, \tau_\lambda$ | Derived modular constants: $r_\lambda D_\lambda$; $D_\lambda/\sqrt{r_\lambda^2-1}$; $0.52\sqrt2/\sqrt{r_\lambda^2-1}$; $\kappa_{\mathrm{BD}}\mathrm{erfc}(D_\lambda/2)$ |
| $\mathrm{env}(s)$ | Lower-tail envelope $\max\{(1+e^{-s})/2, (1+s)^{-1/2}\}$ |
| $L_w(s)$ | Lower-tail Laplace transform $\mathbb E[e^{-s\langle w,u\rangle^2}]$ |
| $\Phi_L(s)$ | Peeled transform (large coordinates exact, small bounded by $e^{-\rho^2\xi^2/4}$) |
| $\ell_\lambda := \sqrt{\alpha(\lambda)}$ | Modular lower-tail factor |
| $\omega$ (avoid clash) | The norm threshold — distinct from the measure $\omega(a,x)$ of Lemma 21 |
| $\kappa_{\mathrm{sc}}(\ell,D)$ | $(\ell D + 1)/q^a$ — RingSC soundness |
| $p, p_0$ | Prover success probability; probability one family-extraction returns a usable family |
| $b_q$ | $\lceil\log_2 q\rceil$ bits per coordinate |

## 3. Algebraic Setting

### 3.1 Rings, embeddings, norms

- $K = \mathbb{Q}(\zeta_f)$, conductor $f \bmod 4 \neq 2$; $R = \mathcal{O}_K$; $q$ prime with $q\nmid f$ (unramified); concrete instantiations use power-of-two conductors $f = 2\phi$.
- Two embeddings: coefficient embedding in the **powerful basis** and canonical embedding $\sigma$; all norms on $R_q$ objects computed from the balanced lift.
- Norm relations (Lemma 1 [KLNO24]):
$$\|x\| \le \sqrt{\tfrac{\mathrm{rad}(f)}{f}}\|x\|_{\sigma,2},\quad \|x\|_{\sigma,2} \le \sqrt{\bar f}\|x\|,\quad \|x\|_{\sigma,\infty}\le\sqrt\phi\,\|x\|_{\mathrm{coeff},\infty},\quad \|x\|_{\mathrm{coeff},\infty}\le c_{\mathrm{rad}}(f)\|x\|_{\sigma,\infty}.$$
- Operator norms (Lemma 2): $\sup_{x\in R\setminus\{0\}}\|cx\|_{\sigma,2}/\|x\|_{\sigma,2} = \|c\|_{\sigma,\infty}$ and
$$\sqrt{\tfrac{f}{\bar f \mathrm{rad}(f)}}\|c\|_{\sigma,\infty} \le \|c\|_{\mathrm{op}} \le \sqrt{\tfrac{\bar f\,\mathrm{rad}(f)}{f}}\|c\|_{\sigma,\infty};\qquad \|c\|_{\mathrm{op}} = \|c\|_{\sigma,\infty}\ \text{for power-of-two } f.$$
  **Implementation consequence**: for $f = 2\phi$, test $\|c\|_{\mathrm{op}}\le\gamma$ by computing the $2\phi$ canonical evaluations of $c$ (FFT of the coefficient vector) and taking the max modulus — exact, no estimation.

### 3.2 Trace, dual basis, fine/coarse lifts

- $\mathrm{Tr}(\cdot)$ descends to a $\mathbb{Z}_q$-linear map $R_q\to\mathbb{Z}_q$; trace-dual basis $(b_i^\vee)$ with $\mathrm{Tr}(b_ib_j^\vee) = \delta_{ij} \bmod q$.
- $\mathrm{Lift}_{\mathrm{fine}}: \mathbb{Z}_q^{a\times\phi b}\to R_q^{a\times b}$ packs each row of $\phi$ consecutive scalars into one ring element via the dual basis: $\mathrm{Lift}_{\mathrm{fine}}(J)_{s,t} := \sum_i J_{s,\phi t + i}\,b_i^\vee$.
- $\mathrm{Lift}_{\mathrm{coarse}}$: entry-wise $\mathbb{Z}_q\to R_q$ embedding.
- **Lift identities (Lemma 4)** — the algebraic engine of the whole scheme:
$$\mathrm{Tr}\big(\mathrm{Lift}_{\mathrm{fine}}(J)\,W\big) = J\,\mathrm{coeff}(W) \bmod q,\qquad \mathrm{Tr}\big(\mathrm{Lift}_{\mathrm{coarse}}(J)\,W\big) = J\,\mathrm{Tr}(W) \bmod q,$$
$$\mathrm{coeff}\big(\mathrm{Lift}_{\mathrm{coarse}}(J)\,w\big) = (J\otimes I_\phi)\,\mathrm{coeff}(w) \bmod q.$$
  Reading: a *fine* lift converts "ring-matrix × ring-vector" into an *integer* matrix–vector product on coefficients under the trace; a *coarse* lift acts as a block-diagonal $(J\otimes I_\phi)$ on coefficients.

### 3.3 NTT, subfield batching

- If $\Phi_f$ factors mod $q$ into $\phi/e$ degree-$e$ irreducibles: $\mathrm{NTT}: R_q\cong(\mathbb{F}_{q^e})^{\phi/e}$.
- For $a \mid e$: expand each slot over an $\mathbb{F}_{q^a}$-basis → $\theta_a: R_q\cong(\mathbb{F}_{q^a})^{\phi/a}$; subfield batching $\Phi_\delta(x) = \delta^T\theta_a(x)$ with $\delta\leftarrow\$(\mathbb{F}_{q^a})^{\phi/a}$ maps $R_q\to\mathbb{F}_{q^a}$ and kills nonzero $x$ with probability exactly $q^{-a}$ (Lemma 5). This is the "random linear combination into a small field" used by RingSC. Concrete: $q = 2^{50}-2687$ with $e = a = 2$ → sumchecks over $\mathbb{F}_{q^2}$.

### 3.4 Challenge sets

- Strong sampling set (Def. 11): all pairwise differences units. **$\epsilon_C$-approximate**: $\max_{c_0\in C}\Pr_{c\leftarrow\$C}[c\ne c_0 \wedge c - c_0\notin R_q^\times]\le\epsilon_C$ — strictly stronger than the [GLLO26] variant (one argument fixed, one uniform — matches coordinate-wise forking, Remark 1).
- $\Gamma_C := \max_{c\in C}\|c\|_{\mathrm{op}}$ controls fold-time witness growth: $\|w_{\mathrm{fold}}\|\le\|w_{\mathrm{acc}}\| + \Gamma_C\|w\|$ per challenge.
- Exact fixed-weight sets $C^{\mathrm{fw}}_{f,s,B}$ (Def. 30): $s$ non-zero coefficients in $[-B,B]$; cardinality $(2B)^s\binom\phi s$; strong sampling if $2B < (q^{1/\varphi(z)}/s_1(z))$ with $z$ the "splitting part" of $f$ and $q = 1 \bmod z$, $\mathrm{ord}_f(q) = f/z$ (Theorem 3 [LS18]). Power-of-two case (Corollary 2): $f = 2\phi$, $q = 2^k+1 \bmod 4k$, $2B < q^{1/k}/\sqrt k$ ⟹ strong sampling with $\Gamma_C \le sB$.
- Operator-norm rejection (Def. 31): resample until $\|c\|_{\mathrm{op}}\le\gamma$; output uniform on $S(\gamma)$; expected trials $1/p_S(\gamma)$; retained entropy $\log_2|S| + \log_2 p_S(\gamma)$; $\Gamma_C\le\gamma$; strong-sampling preserved (subset). 
- Almost-splitting heuristic (Heuristic 1): $f=2\phi$, $x^\phi+1$ splits into degree-$e$ irreducibles, $C = C^{\mathrm{fw}}_{2\phi,s,1}(\gamma)$ with $|C|\ge q^e$ ⟹ conjectured $\epsilon_C\approx\phi/(e q^e)$, $\Gamma_C\le\gamma$. Supported by measurements (Table 4) and [BL25] well-spreadness lemmas; open to prove for fixed-global-weight + rejection.

### 3.5 The JL projection distribution

$\chi$: ternary with $\Pr[0] = 1/2$, $\Pr[\pm1]=1/4$ ("biased ternary"). Definition 16 (Euclidean projection guarantee) for $J\leftarrow\$ \chi^{n_{\mathrm{rp}}\times m}$:
1. $\Pr[\|Jw\|/\|w\| \notin[\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}}]]\le\kappa$ for all non-zero $w\in\mathbb{R}^m$;
2. modular lower tail: for $0<\theta\le q/b$, $\|w\|\ge\theta$, $w\in[\pm q/2]^m$: $\Pr[\|Jw \bmod q\|\le\alpha_{\mathrm{rp}}\theta]\le\kappa$.

Prior constants were heuristic ([BS23, Lemmas 4.1/4.2]: $n_{\mathrm{rp}}=256$, $\alpha_{\mathrm{rp}}=\sqrt{30}$, $\beta_{\mathrm{rp}}=\sqrt{337}$, $b=125$ at 128 bits). Theorem 2 certifies (Table 1): for $2\lambda$ rows, failure $2^{-\lambda}$: e.g. $\lambda=128$: $\gamma_1 = 9.66$, $\alpha = 27.37$, $\beta = 343.2$, $b = 126$ (so $\ell_{\mathrm{rp}} = \sqrt{27.37}\approx 5.23$, $u_{\mathrm{rp}} = \sqrt{343.2}\approx 18.5$). Asymptotics: $\alpha(\lambda) \approx 0.216\lambda - 0.300$ (affine!), $\beta(\lambda)\sim c\sqrt\lambda$ with $c\approx2.68$, $\gamma_1(\lambda)\sim\sqrt{\lambda\ln 2}$, $b(\lambda) = \Theta(\lambda)$, admissible threshold $q/b(\lambda) = \Theta(q/\lambda)$. Row count $2\lambda$ is necessary: the spike $w = e_1$ gives $\Pr[Jw = 0] = 2^{-N}$, consuming the whole budget at $N=\lambda$; positive $\alpha$ requires $N > 1.1623\lambda$ (Remark 4).

### 3.5a Powerful-basis implementation notes

For power-of-two conductors $f = 2\phi$ the powerful basis is the power basis $(1, X, \dots, X^{\phi-1})$ of $R = \mathbb{Z}[X]/\langle X^\phi+1\rangle$ — so a `lzk`-style ring module serves unchanged, with two additions: (i) the canonical embedding $\sigma(c)$ is the length-$\phi$ complex FFT of the coefficient vector (its max modulus equals $\|c\|_{\mathrm{op}}$ exactly — the operator-norm rejection test); (ii) the trace-dual basis is $b_i^\vee = \frac{1}{\phi}X^{-i}$ (check: $\mathrm{Tr}(X^i\cdot\frac1\phi X^{-j}) = \frac1\phi\sum_k\sigma_k(X^{i-j}) = \delta_{ij}$ over $\mathbb{Q}$, and reduces to $\delta_{ij}\bmod q$ when $\phi$ is invertible mod $q$, i.e. $q\nmid\phi$ — true for odd $q$ and power-of-two $\phi$). Consequently:
$$\mathrm{Lift}_{\mathrm{fine}}(J)_{s,t} = \sum_i J_{s,\phi t+i}\tfrac1\phi X^{-i}\ \text{mod } q,\qquad \mathrm{Tr}(a) = \phi\cdot a_0 \bmod q\ (\text{only the constant term survives}),$$
so the fine lift is a scaled negacyclic "reverse-NTT" of each row-block, and the trace of a ring element is $\phi$ times its constant coefficient — both $O(\phi\log\phi)$ per element with precomputed twiddles. For non-power-of-two conductors the powerful basis is a tensor of power bases and the dual-basis must be computed numerically at setup; the implementation target of the paper only needs $f = 256$.


## 4. Relations

### 4.1 Principal relation (Definition 22) — the folded object

$$\Xi^{\mathrm{lin}}_{R,q,m,n,\beta} := \Big\{\big((\mathbf{F},\mathbf{y},\mathbf{s},t),\ \mathbf{w}\big) : \mathbf{F}\in R_q^{n\times m},\ \mathbf{y}\in R_q^n,\ \mathbf{w}\in R_q^m,\ \mathbf{s}\in R_q^{\log_2 m},\ t\in R_q;\ \ \mathrm{MLE}[w](\mathbf{s}) = t \bmod q;\ \|\mathbf{w}\|\le\beta;\ \mathbf{F}\mathbf{w} = \mathbf{y} \bmod q\Big\}.$$

Structure map $\mathrm{str}(\mathbf{F},\mathbf{y},\mathbf{s},t) := \mathbf{F}$ — all statements in a fold share the commitment key. One-column principal linear-relation form (§7.1): $\begin{pmatrix}\mathbf F\\ \widetilde{\mathrm{eq}}(\mathbf s)^T\end{pmatrix}\mathbf w = \begin{pmatrix}\mathbf y\\ t\end{pmatrix}\bmod q$ — this is what makes the [KLNO24/KLOT25] exact-norm-check and decomposition reductions apply.

### 4.2 SIS-break relation (Definition 26)

$$\Xi^{\mathrm{SIS}}_{R,q,m,n,\beta} := \{(\mathbf F, \mathbf x): \mathbf x\in R_q^m,\ \|\mathbf x\|\le\beta,\ \mathbf F\mathbf x = 0,\ \mathbf x\ne0\}.$$

Knowledge soundness of $\Pi_{\mathrm{fold}}$ extracts either valid input witnesses **or** a same-key SIS solution (the "break" alternative of relaxed folding, Definition 21).

### 4.3 Relaxed folding scheme (Definition 21)

A RoK $\Pi$ that is structure-preserving for $\prod_{i\in[k]}\Xi_i \times \Xi_{\mathrm{acc,in}} \to \Xi_{\mathrm{acc,out}}$ (correctness) and knowledge-sound for $(\prod_i \Xi'_i \times \Xi'_{\mathrm{acc,in}}) \cup \Xi_{\mathrm{break}} \leftarrow \Xi'_{\mathrm{acc,out}}$ — input/output accumulator relations may differ ("relaxed"), and extraction may land in the break relation.

### 4.4 AIR relation (Definition 32)

Instance: transition polynomial $f\in R_q[y_0,\dots,y_{2t-1}]_{\le D}$ and boundary values $C\subseteq[N]\times[t]\times R_q$; witness: trace $W\in R_q^{N\times t}$; $(f, W)\in\Xi^{\mathrm{AIR}}_{N,t,D}$ iff $f(W_{i,:}, W_{i+1,:}) = 0 \bmod q$ for all $i\in[N-1]$ and $W_{i,j} = u$ for $(i,j,u)\in C$. The [KLOT25] reduction yields $2t$ fresh $\Xi^{\mathrm{lin}}$ instances at a common evaluation point under a common key → fold with arity $k = 2t$.

## 5. Protocols

### 5.0a Worked micro-example of the layered projection (2 layers, toy)

To build intuition for Definitions 23–24, take $k = 2$ fresh witnesses of $m = 4$ ring elements each, $\phi = 2$, and two layers with $N_0 = km = 8$ ring elements → $N_1 = 4$ ring elements → $N_2 = 4$ $\mathbb{Z}_q$ coordinates:
- Layer 0 (coarse): $r_0 = 2$ blocks of $m_0 = 4$, each projected by $J_0\in\chi^{n_0\times m_0}$ with $n_0 = 2$; requires $r_0m_0 = 8 = N_0$ ✓ and $r_1m_1 = r_0n_0 = 4$.
- Layer 1 (fine, last): $r_1 = 2$ blocks of $m_1 = 2$ ring elements each, projected by $J_1\in\chi^{n_1\times(\phi m_1)} = \chi^{2\times4}$; output $n_1 = 2$ ring elements = $2\phi = 4$ coordinates. $r_2$... with $r_{d-1} = r_1$: the fine layer must have $r_{d-1} = 1$ — so re-index: with $d = 2$ we need $r_1 = 1$, $m_1 = 4$, $J_1\in\chi^{n_1\times(\phi m_1)} = \chi^{n_1\times 8}$, $n_1 = N_2/\phi$ coordinates… the compatibility arithmetic is exactly where implementations slip; always re-derive from $r_jm_j = r_{j-1}n_{j-1}$, $r_{d-1} = 1$, $N_d = n_{d-1}$.
- Data flow: $w_{\mathrm{all}}\in R_q^8$ --($I_2\otimes M_0$, $M_0 = \mathrm{Lift}_{\mathrm{coarse}}(J_0)$)--> $R_q^4$ --($M_1 = \mathrm{Lift}_{\mathrm{fine}}(J_1)$)--> $R_q^{n_1}$ --Tr--> $\mathbb{Z}_q^{\phi n_1}$. The integer matrix realised on coefficients is $P = J_1\big((I_2\otimes J_0)\otimes I_\phi\big)$ — never formed; only the $J_0, J_1$ ternary entries exist.

### 5.0b Communication anatomy at the concrete parameters

At $(k,m,\phi) = (2,2^{20},128)$, 3 layers of 256 rows, $\mu = 2$, $L_{\mathrm{sc}} = 43$, $q$ 50-bit, $a = 2$:
- $\mathbf v_{\mathrm{tr}}$: $N_d = 256$ balanced coords ≈ 30 bits → ≈ 0.96 KB.
- $\mathbf v_{\mathrm{btd}}$: $\mu = 2$ ring elements = $2\cdot128\cdot50/8$ ≈ 1.6 KB.
- Terminal values $(t'_i)_{i\in[2]}, t'_{\mathrm{acc}}$: 3 ring elements ≈ 2.4 KB.
- RingSC rounds: $2L_{\mathrm{sc}} = 86$ elements of $\mathbb{F}_{q^2}$ ≈ 86·100/8 ≈ 1.1 KB.
- Total ≈ 5.7 KB ✓ (matches Table 6's 5.72 KB). The fresh-input commitments (excluded) are 18–20 KB and now dominate the transcript — the paper's Perspective (§1.3) points to recursively-composed commitments as the next bottleneck to attack.

### 5.0 The candidate fold and why extraction fails (Section 3 motivation)

Candidate: sample short $z$, set $w_{\mathrm{fold}} := w_{\mathrm{acc}} + z\,w$, $\mathbf y_{\mathrm{fold}} := \mathbf y_{\mathrm{acc}} + z\,\mathbf y \bmod q$. Correctness: $\mathbf F w_{\mathrm{fold}} = \mathbf y_{\mathrm{fold}}$; norm: $\|w_{\mathrm{fold}}\| \le \|w_{\mathrm{acc}}\| + \|z\|_{\mathrm{op}}\|w\|$ — **additive** because the accumulator is never multiplied by a challenge (Cyclo's trick, retained here).

Extraction problem: two executions with challenges $z_0\ne z_1$ give output witnesses $u_0, u_1$; with $\Delta := z_0 - z_1$, $\mathbf a := u_0 - u_1$:
$$\mathbf F\mathbf a = \Delta\mathbf y \bmod q,\qquad \|\mathbf a\|\le 2\beta'_{\mathrm{out}},\qquad \|\Delta\|_{\mathrm{op}}\le 2\Gamma_C,$$
but recovering $w^* = \Delta^{-1}\mathbf a$ gives only $\|w^*\|\le 2\beta'_{\mathrm{out}}\|\Delta^{-1}\|_{\mathrm{op}}$ — useless. **Resolution**: certify shortness of the *extracted fresh* witness separately (via the layered JL projection); then the accumulator witness is reconstructed additively as $u_0 - z_0 w^*$ with only additive growth. This is why the projection is applied to $w_{\mathrm{all}}$ = concatenation of the **fresh** witnesses only.

### 5.1 Layered random projections (Sections 3.1, Def. 23–24)

**Construction.** Choose layer dimensions $(r_j, m_j, n_j)_{j\in[d]}$ with $r_0m_0 = km$, $r_{d-1} = 1$, $r_jm_j = r_{j-1}n_{j-1}$. Sample raw ternary layers $J_j\leftarrow\$\chi^{n_j\times m_j}$ for $j\in[d-1]$ and $J_{d-1}\leftarrow\$\chi^{n_{d-1}\times(\phi m_{d-1})}$; lift:
$$M_j := \mathrm{Lift}_{\mathrm{coarse}}(J_j)\ (j<d-1),\qquad M_{d-1} := \mathrm{Lift}_{\mathrm{fine}}(J_{d-1}),\qquad M := (I_{r_{d-1}}\otimes M_{d-1})\cdots(I_{r_0}\otimes M_0)\in R_q^{n_{d-1}\times r_0m_0}.$$
Boundary sizes $N_0 = r_0m_0$ (ring elements), $N_{j+1} = r_jn_j$, $N_d = n_{d-1}$ (**$\mathbb{Z}_q$ coordinates** after the fine layer). Figure 1 comparison: dense $J$ (linear verifier work) vs one layer $I_r\otimes J_0$ (image still large → commit) vs **LRP** (each layer succinct, only final image sent).

**Norm preservation (Lemma 9).** With per-layer constants $\ell_j = \alpha_{\mathrm{rp}}(\kappa_j)$, $u_j = \beta_{\mathrm{rp}}(\kappa_j)$, $b_j = b(\kappa_j)$:
$$\Pr\Big[\tfrac{\|Pw\|}{\|w\|}\notin\Big[\textstyle\prod_j\ell_j,\ \prod_ju_j\Big]\Big] \le \sum_j r_j\kappa_j\qquad(w\ne0\in\mathbb{Z}^{r_0m_0}),$$
and modular: for $\theta$ with $\theta\prod_{j'\le j}\ell_{j'} \le q/b_j$ for every $j$, $\|w\|\ge\theta$ ⟹ $\Pr[\|Pw\bmod q\|\le\theta\prod_j\ell_j]\le\sum_j r_j\kappa_j$. Setting $\kappa_j := \kappa/(dr_j)$ gives total failure $\kappa$. In ring form: $\eta_j := \phi r_j$ blocks per coarse layer, $\eta_{d-1} = 1$; $\kappa_{\mathrm{proj}} := \sum_j\eta_j\kappa_j$.

**Trace identity (Lemma 10).** With $C_i := (I_{r_i}\otimes J_i)\otimes I_\phi$ and $P := J_{d-1}C_{d-2}\cdots C_0$: for every $w\in R_q^{r_0m_0}$:
$$\mathrm{Tr}(Mw) = P\,\mathrm{coeff}(w) \bmod q.$$
This is what lets the verifier check a *ring* matrix–vector product via a *short integer* vector sent in the clear: $\mathbf v_{\mathrm{tr}} = \mathrm{Tr}(Mw_{\mathrm{all}})$ has $N_d$ $\mathbb{Z}_q$ coordinates.

**Layered multilinear extension (Def. 24).** Variable sets $x_i\in R_q^{\nu_{d-i}}$ per boundary (indexed opposite to layers: $x_0$ = output, $x_d$ = witness):
$$\mathrm{LMLE}[M](x_0,\dots,x_d) := \prod_{i\in[d]}\mathrm{MLE}[I_{r_{d-1-i}}\otimes M_{d-1-i}](x_i, x_{i+1}),\qquad \mathrm{MLE}[M](x_0,x_d) = \sum_{\mathbf b_1,\dots,\mathbf b_{d-1}}\mathrm{LMLE}[M](x_0,\mathbf b_1,\dots,\mathbf b_{d-1},x_d).$$

### 5.2 Ring sumcheck RingSC (Definition 15) — exact protocol

To verify $\sum_{\mathbf b\in\{0,1\}^\ell}g(\mathbf b) = t$ for $g\in R_q[x_0,\dots,x_{\ell-1}]$, individual degree $\le D$:
1. **V → P**: $\delta\leftarrow\$(\mathbb{F}_{q^a})^{\phi/a}$ (subfield batching vector; $\phi/a$ field elements — sent explicitly if interactive).
2. Both parties form $G := \Phi_\delta(g)$, $T := \Phi_\delta(t)$ — $\mathbb{F}_{q^a}$-valued.
3. **Standard sumcheck over $\mathbb{F}_{q^a}$** on $\sum_{\mathbf b}G(\mathbf b) = T$: $\ell$ rounds; in round $i$ the prover sends the univariate round polynomial of degree $\le D$ **with one coefficient omitted** (the one fixed by the consistency equation $g_i(0)+g_i(1) = $ previous claimed value) — so $D$ elements of $\mathbb{F}_{q^a}$ per round; the verifier supplies one field challenge per round. Terminal point $\mathbf r$ uniform in $(\mathbb{F}_{q^a})^\ell$.
4. **Final opening**: the prover sends $g(\mathbf r)\in R_q$; the verifier checks $\Phi_\delta(g(\mathbf r)) = G(\mathbf r)$ (the terminal value implied by the last round message). The application supplies the final check of $g(\mathbf r)$.

Costs (Lemma 8): prover communication $D\ell$ elements of $\mathbb{F}_{q^a}$ + 1 $R_q$ element; verifier communication $\phi/a + \ell$ elements of $\mathbb{F}_{q^a}$; soundness $\kappa_{\mathrm{sc}}(\ell,D) = (\ell D + 1)/q^a$ (batching error $q^{-a}$ + field sumcheck $\ell D/q^a$); perfect completeness.

### 5.2b The RingSC round-by-round shape (what the prover actually transmits)

Concretising Definition 15 for $\Pi_{\mathrm{fold}}$'s batched claim (degree $D = 2$, $\ell = L_{\mathrm{sc}} = \sum_j\nu_j$ rounds, field $\mathbb F_{q^a}$, ring values $R_q$):

- **Round $i$ message** (prover): the univariate $g_i(X) = \sum_{\mathbf b\in\{0,1\}^{\ell-i}}G(\rho_1..\rho_{i-1},X,\mathbf b)\in\mathbb F_{q^a}[X]_{\le2}$, transmitted as $\{g_i(0), g_i(2)\}$ or any two non-fixed points — the third coefficient is pinned by the consistency equation $g_i(0) + g_i(1) = c_{i-1}$ (the previous round's claimed value at $\rho_{i-1}$). Communication: 2 $\mathbb F_{q^a}$ elements.
- **Verifier round action**: recompute $g_i(1) = c_{i-1} - g_i(0)$; check nothing else; sample $\rho_i\leftarrow\$\mathbb F_{q^a}$; set $c_i := g_i(\rho_i)$ (evaluate the quadratic from the two sent coefficients + consistency).
- **Round 1**: consistency target is $T = \Phi_\delta(S)$ (the batched claim value).
- **Terminal**: $c_\ell$ is the claimed $G(\mathbf r)$; the prover's $g(\mathbf r)\in R_q$ must satisfy $\Phi_\delta(g(\mathbf r)) = c_\ell$. In $\Pi_{\mathrm{fold}}$ the generic terminal ring element is replaced by the structured opening $(t'_i)_{i\in[k]}, t'_{\mathrm{acc}}$ plus the public factors, from which the verifier *reconstructs* $g(\mathbf r)$ and re-derives its batched image.
- **Why degree 2**: every batched claim is a product of exactly two multilinear factors (an MLE of a layer matrix or $\mathrm{eq}$ times an MLE of a table), so the round univariate is quadratic — 2 coefficients suffice.

The subfield-batching vector $\delta$ ($\phi/a$ field elements) is the *only* place the ring-to-field interface appears: all ring-valued tables are folded through $\Phi_\delta$ once, and the terminal check recrosses into $R_q$ through the single opening.

### 5.3 The folding protocol $\Pi_{\mathrm{fold}}$ (Figure 2) — full line-by-line transcription

**Common input**: statements $((\mathbf F,\mathbf y_i,\mathbf s_i,t_i))_{i\in[k]}$ (fresh) and $(\mathbf F,\mathbf y_{\mathrm{acc}},\mathbf s_{\mathrm{acc}},t_{\mathrm{acc}})$ (accumulator), all under key $\mathbf F$. **Prover input**: witnesses $(\mathbf w_i)_{i\in[k]}$, $\mathbf w_{\mathrm{acc}}$. **Public**: layered projection matrix $M\leftarrow\$\chi_{\otimes R; d; (r_j,n_j,m_j)}$ (Definition 23; sampled fresh per fold, described by its $S_{\mathrm{JL}}$ ternary entries), threshold $\omega$, trace-batching count $\mu$.

1. **P (local)**: $w_{\mathrm{all}} := (\mathbf w_i^T)_{i\in[k]}^T\in R_q^{km}$ — fresh witnesses **only**; $\mathbf v_{\mathrm{proj}} := M w_{\mathrm{all}} \bmod q$; $\mathbf v_{\mathrm{tr}} := \mathrm{Tr}(\mathbf v_{\mathrm{proj}}) \bmod q\in\mathbb{Z}_q^{N_d}$. **P → V**: $\mathbf v_{\mathrm{tr}}$.
2. **V**: check $\|\mathbf v_{\mathrm{tr}}\| \le \omega$ (the norm certificate: since $\mathrm{Tr}(Mw_{\mathrm{all}}) = P\,\mathrm{coeff}(w_{\mathrm{all}})$ and $P$ is JL-norm-preserving with modular lower tail, a small trace certifies $\|w_{\mathrm{all}}\|$ small). Abort on failure.
3. **V → P**: trace-batching points $(\mathbf c_i)_{i\in[\mu]}\leftarrow\$\mathbb{Z}_q^{\log_2 N_d}$.
4. **P → V**: $\mathbf v_{\mathrm{btd}} := (\langle \mathbf b_{\mathbf c_i}, \mathbf v_{\mathrm{proj}}\rangle)_{i\in[\mu]}\in R_q^\mu$ where $\mathbf b_{\mathbf c_i} := \widetilde{\mathrm{eq}}(\mathbf c_i)\in\mathbb{Z}_q^{N_d}$ (coarse-lifted scalars acting on ring elements). **V**: check $\mathrm{Tr}((\mathbf v_{\mathrm{btd}})_i) = \langle \mathbf v_{\mathrm{tr}}, \mathbf b_{\mathbf c_i}\rangle \bmod q$ for every $i\in[\mu]$ (consistency of the batched projections with the sent trace).
5. **P and V define the $h := \mu + k + 1$ sumcheck claims** (over $R_q$, later batched):
   - **Projection claims** $\mathrm{SC}^{\mathrm{proj}}_i$ for $i\in[\mu]$:
     $$\sum_{\mathbf b_1\in\{0,1\}^{\nu_{d-1}},\dots,\mathbf b_d\in\{0,1\}^{\nu_0}\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\! \mathrm{LMLE}[M](\mathbf c_i, \mathbf b_1,\dots,\mathbf b_{d-1}, \mathbf b_d)\cdot\mathrm{MLE}[w_{\mathrm{all}}](\mathbf b_d) = (\mathbf v_{\mathrm{btd}})_i \bmod q.$$
     (This is the factorised matrix–vector product $Mw_{\mathrm{all}}$ summed over all intermediate coordinates, evaluated against the batched output weight $\mathbf b_{\mathbf c_i}$.)
   - **Fresh evaluation claims** $\mathrm{SC}^{\mathrm{eval}}_i$ for $i\in[k]$ (homogenisation of $\mathrm{MLE}[w_i](\mathbf s_i) = t_i$ onto $w_{\mathrm{all}}$'s cube):
     $$\sum_{\mathbf b\in\{0,1\}^{\log_2 k},\ \mathbf a\in\{0,1\}^{\log_2 m}} \mathrm{MLE}[w_{\mathrm{all}}](\mathbf b, \mathbf a)\,\mathrm{eq}(\mathbf b, \mathrm{bin}(i))\,\mathrm{eq}(\mathbf a, \mathbf s_i) = t_i \bmod q.$$
   - **Accumulator evaluation claim** $\mathrm{SC}^{\mathrm{eval}}_{\mathrm{acc}}$:
     $$\sum_{\mathbf a\in\{0,1\}^{\log_2 m}}\mathrm{MLE}[w_{\mathrm{acc}}](\mathbf a)\,\mathrm{eq}(\mathbf a,\mathbf s_{\mathrm{acc}}) = t_{\mathrm{acc}} \bmod q.$$
6. **Claim batching** (prover message $d\leftarrow\$R_q^{h-1}$ — sampled by the verifier in the public-coin form): with $g^{\sqcup}$ the $\ell$-variable padding of claim $u$ ($\ell := \max_u\ell_u = \sum_{j\in[d]}\nu_j$; pad by multiplying with $\prod_{j\in[\ell-\ell_u]}(1-x_j)$, which preserves sums since $\sum_{b\in\{0,1\}}(1-b) = 1$):
   $$\mathrm{SC}_{\mathrm{btd}} := \sum_{i\in[\mu]}d_i\,\mathrm{SC}^{\mathrm{proj}}_i + \sum_{i\in[k]}d_{\mu+i}\,\mathrm{SC}^{\mathrm{eval}}_i + \mathrm{SC}^{\mathrm{eval}}_{\mathrm{acc}},\qquad H(\mathbf b) = \sum_{\mathbf b\in\{0,1\}^\ell}H(\mathbf b) = S.$$
7. **P ↔ V: execute RingSC on $\mathrm{SC}_{\mathrm{btd}}$** (Definition 15): subfield batching vector $\delta$; $\ell = L_{\mathrm{sc}}$ rounds of degree-$\le 2$ (the products are of pairs of multilinear factors) over $\mathbb{F}_{q^a}$, 2 coefficients per round polynomial; challenges reduce everything to the terminal point $(\mathbf r_1,\dots,\mathbf r_d)$ with $\mathbf r_j$ living on boundary $j$.
8. **Parse the final boundary**: $(\mathbf r_{d,0}, \mathbf r_{d,1}) := \mathbf r_d\in R_q^{\log_2 k}\times R_q^{\log_2 m}$ (first $\log_2 k$ variables select the fresh-witness block, remaining $\log_2 m$ the coordinate inside it). **P → V**: terminal evaluations
   $$(t'_i)_{i\in[k]} := \big(\widetilde{\mathrm{eq}}(\mathbf r_{d,1})^T\mathbf w_i\big)_{i\in[k}},\qquad t'_{\mathrm{acc}} := \widetilde{\mathrm{eq}}(\mathbf r_{d,1})^T\mathbf w_{\mathrm{acc}}.$$
   **V**: checks the terminal RingSC evaluation, reconstructing the terminal ring element as $\mathrm{MLE}[w_{\mathrm{all}}](\mathbf r_{d,0},\mathbf r_{d,1}) = \sum_{i\in[k]}\mathrm{eq}(\mathbf r_{d,0})_i\,t'_i$ and $\mathrm{MLE}[w_{\mathrm{acc}}](\mathbf r_{d,1}) = t'_{\mathrm{acc}}$ (all other factors of the batched polynomial are public; the generic terminal ring-element message of RingSC is thereby omitted).
   After this step the claims have been **homogenised**: both the fresh and the accumulated evaluation claims now live at the *same* point $\mathbf r_{d,1}$, so they fold by linearity.
9. **V → P: folding challenges** $\mathbf z\leftarrow\$ C^k$.
10. **Fold**:
    - **P**: $w_{\mathrm{fold}} := \mathbf w_{\mathrm{acc}} + \sum_{i\in[k]}z_i\mathbf w_i \in R_q^m$.
    - **V**: $\mathbf y_{\mathrm{fold}} := \mathbf y_{\mathrm{acc}} + \sum_{i\in[k]}z_i\mathbf y_i \bmod q$; $\mathbf s_{\mathrm{fold}} := \mathbf r_{d,1}$; $t_{\mathrm{fold}} := t'_{\mathrm{acc}} + \sum_{i\in[k]}z_i t'_i \bmod q$.
    - Output $((\mathbf F,\mathbf y_{\mathrm{fold}},\mathbf s_{\mathrm{fold}},t_{\mathrm{fold}}),\ w_{\mathrm{fold}})\in\Xi^{\mathrm{lin}}_{R,q,m,n,\beta_{\mathrm{out}}}$ with $\beta_{\mathrm{out}} = \beta_{\mathrm{acc}} + k\Gamma_C\beta_{\mathrm{in}}$.

**Where the "no in-protocol commitments" comes from**: the only prover messages are $\mathbf v_{\mathrm{tr}}$ ($N_d$ short $\mathbb{Z}_q$ coordinates, ~30 bits each with centred encoding), $\mathbf v_{\mathrm{btd}}$ ($\mu$ ring elements), $(t'_i)_{i\in[k]}$ and $t'_{\mathrm{acc}}$ ($k+1$ ring elements), the RingSC round messages ($2L_{\mathrm{sc}}$ elements of $\mathbb{F}_{q^a}$), plus the public layer description. No $\mathbf F$-commitment to any transformed witness is ever sent.

**Pseudocode transcription of Figure 2** (verifier side shown as checks; ⟵ marks verifier-sent challenges):

```
P(pp, stmt0, wit0), V(pp, stmt0):
  # stmt0 = ((F, y_i, s_i, t_i))_{i in [k]} , (F, y_acc, s_acc, t_acc)
  # wit0  = (w_i)_{i in [k]} , w_acc

  # --- public randomness: the layered projection ---
  M ←$ χ_{⊗R; d; (r_j, n_j, m_j)_{j in [d]}}              # Def. 23; described by S_JL ternary entries

  # --- norm certificate ---
  P:  w_all ← concat(w_0, …, w_{k-1})                       # fresh witnesses ONLY
  P:  v_proj ← M · w_all  (mod q)
  P:  v_tr   ← Tr(v_proj)  (mod q)                          # in Z_q^{N_d}
  P → V: v_tr
  V:  assert ‖v_tr‖ ≤ ω

  # --- trace batching ---
  V ⟵ P: (c_i)_{i in [μ]}  ←$ Z_q^{log2 N_d}                # μ points
  P:  v_btd ← ( ⟨b_{c_i}, v_proj⟩ )_{i in [μ]}              # b_{c_i} := eq~(c_i)
  P → V: v_btd
  V:  assert Tr(v_btd_i) = ⟨v_tr, b_{c_i}⟩ (mod q)  ∀i

  # --- μ + k + 1 sumcheck claims (batched) ---
  claims:
    SC^proj_i  : Σ_{b1…bd}  LMLE[M](c_i, b1,…,b_{d-1}, b_d)·MLE[w_all](b_d) = v_btd_i     (i in [μ])
    SC^eval_i  : Σ_{b,a}     MLE[w_all](b, a)·eq(b, bin(i))·eq(a, s_i) = t_i               (i in [k])
    SC^eval_acc: Σ_a         MLE[w_acc](a)·eq(a, s_acc) = t_acc
  V ⟵ P: d ←$ R_q^{h-1}                                     # h = μ + k + 1 claim combiners
  SC_btd ← Σ_i d_i·SC^proj_i + Σ_i d_{μ+i}·SC^eval_i + SC^eval_acc      # eq-padded to ℓ = Σν_j vars

  # --- ring sumcheck ---
  P,V: run RingSC on SC_btd                                  # Def. 15: δ ←$ (F_{q^a})^{φ/a}, then
                                                              # degree-2 sumcheck over F_{q^a}, ℓ rounds
  terminal point: (r_1, …, r_d);  parse r_d = (r_{d,0} ∈ R_q^{log2 k}, r_{d,1} ∈ R_q^{log2 m})

  # --- terminal opening (homogenised claims) ---
  P:  t'_i   ← eq~(r_{d,1})ᵀ w_i      (i in [k])
  P:  t'_acc ← eq~(r_{d,1})ᵀ w_acc
  P → V: (t'_i)_{i in [k]}, t'_acc
  V:  check terminal RingSC evaluation, reconstructing
        MLE[w_all](r_{d,0}, r_{d,1}) = Σ_i eq(r_{d,0})_i · t'_i   and   MLE[w_acc](r_{d,1}) = t'_acc

  # --- fold ---
  V ⟵ P: z ←$ C^k
  P:  w_fold ← w_acc + Σ_i z_i·w_i
  V:  y_fold ← y_acc + Σ_i z_i·y_i (mod q);   s_fold ← r_{d,1};   t_fold ← t'_acc + Σ_i z_i·t'_i (mod q)

  output: ((F, y_fold, s_fold, t_fold), w_fold) ∈ Ξ^lin_{R,q,m,n,β_out}
```

### 5.3b The folding-verifier circuit view (what an IVC step must check)

If $\Pi_{\mathrm{fold}}$ is used inside an IVC, the step circuit verifies the *previous* fold's transcript. The complete list of checks (all $R_q$- or $\mathbb{F}_{q^2}$-sized, none $n$- or $m$-sized):
1. Re-derive all challenges in §8.5 order from the transcript hash.
2. $\|\mathbf v_{\mathrm{tr}}\|\le\omega$ — a $\mathbb{Z}$-norm over $N_d = 256$ small coordinates (the only "range-check-flavoured" cost, and it is *constant-sized*, independent of $m$ and $\beta$).
3. $\mathrm{Tr}((\mathbf v_{\mathrm{btd}})_i) = \langle\mathbf v_{\mathrm{tr}},\mathbf b_{\mathbf c_i}\rangle \bmod q$ for $i\in[\mu]$ — $\mu\cdot N_d$ scalar mults on tiny values.
4. RingSC round consistency: $L_{\mathrm{sc}}$ rounds × degree-2 checks over $\mathbb{F}_{q^2}$ (two coefficients each).
5. Terminal RingSC evaluation: recompute the batched polynomial value at $(\mathbf r_1,\dots,\mathbf r_d)$ from the public layer MLEs (the $S_{\mathrm{JL}}$-entry scans), $\mathrm{eq}$ factors, and the claimed $(t'_i), t'_{\mathrm{acc}}$.
6. The fold: $\mathbf y_{\mathrm{fold}} = \mathbf y_{\mathrm{acc}} + \sum z_i\mathbf y_i$ ($k$ ring-element mults), $t_{\mathrm{fold}} = t'_{\mathrm{acc}} + \sum z_it'_i$ ($k$ ring mults), $\mathbf s_{\mathrm{fold}} := \mathbf r_{d,1}$ (free).
7. Hash the whole transcript (Fiat-Shamir) — in the RoKoko/PikkuFold regime this is now the dominant circuit cost alongside item 5, since the algebra is only kilobytes.

### 5.4 Theorem 1 (PikkuFold folding) — parameter conditions

Let $R_q\cong(\mathbb{F}_{q^e})^{\phi/e}$, fix $a\mid e$ for RingSC. Powers of two: $k,m,\mu,\phi$ and all boundary dims. Layer dims satisfy $r_0m_0 = km$, $r_{d-1}=1$, $r_jm_j = r_{j-1}n_{j-1}$. Constants $\ell_j = \alpha_{\mathrm{rp}}(\kappa_j)$, $u_j = \beta_{\mathrm{rp}}(\kappa_j)$, $b_j = b(\kappa_j)$; $\eta_j := \phi r_j$ ($0\le j\le d-2$), $\eta_{d-1} := 1$; $\kappa_{\mathrm{proj}} := \sum_j\eta_j\kappa_j$;
$$\omega := \sqrt{k}\,\beta_{\mathrm{in}}\prod_{j\in[d]}u_j,\qquad \beta'_{\mathrm{in}} := \frac{\omega}{\prod_{j\in[d]}\ell_j}.$$
Modular conditions: $\beta'_{\mathrm{in}}\prod_{h\in[j]}\ell_h \le q/b_j$ for every $j\in[d]$. Challenge set $C$: $\epsilon_C$-approximate strong sampling with expansion $\Gamma_C$. Bounds:
$$\beta_{\mathrm{out}} = \beta_{\mathrm{acc}} + k\Gamma_C\beta_{\mathrm{in}},\qquad \beta'_{\mathrm{acc}} = \beta'_{\mathrm{out}} + k\Gamma_C\beta'_{\mathrm{in}},$$
$$\beta_{\mathrm{bind}} := (k+1)\beta'_{\mathrm{out}}(2\Gamma_C)^k,\qquad \rho_{\mathrm{bind}} := (2\Gamma_C)^k,\qquad \beta_{\mathrm{sis}} := \max\{8\Gamma_C\beta'_{\mathrm{out}},\ 2\beta_{\mathrm{bind}}\rho_{\mathrm{bind}}\}.$$
Correctness: $\big(\Xi^{\mathrm{lin}}_{\beta_{\mathrm{in}}}\big)^k\times\Xi^{\mathrm{lin}}_{\beta_{\mathrm{acc}}}\to\Xi^{\mathrm{lin}}_{\beta_{\mathrm{out}}}$ with error $\kappa_{\mathrm{proj}}$. Knowledge soundness: $\big(\Xi^{\mathrm{lin}}_{\beta'_{\mathrm{in}}}\big)^k\times\Xi^{\mathrm{lin}}_{\beta'_{\mathrm{acc}}}\ \cup\ \Xi^{\mathrm{SIS}}_{\beta_{\mathrm{sis}}}\ \leftarrow\ \Xi^{\mathrm{lin}}_{\beta'_{\mathrm{out}}}$ with knowledge error
$$\kappa = \frac{k}{|C|} + k\epsilon_C + \kappa_{\mathrm{proj}} + \binom{\log_2 N_d}{\mu}\frac{1}{q^\mu}\ +\ \frac{1}{q^e} + \frac{2\sum_{j\in[d]}\nu_j + 1}{q^a}.$$
(Appendix A improves the SIS-break bound to $\beta_{\mathrm{sis}} = 6\Gamma_C\beta'_{\mathrm{out}}$ at the cost of replacing $k/|C| + k\epsilon_C$ by $2k(1/|C|+\epsilon_C)$ — Proposition 3.)

### 5.5 Efficiency (Lemma 11, Corollary 1)

With $L_{\mathrm{sc}} := \sum_j\nu_j$, $S_{\mathrm{lay}} := \sum_j r_jn_jm_j$ (non-zero ring entries of the expanded block-diagonal layers), $S_{\mathrm{JL}} := \sum_{j\in[d-1]}n_jm_j + \phi n_{d-1}m_{d-1}$ (ternary entries of the unexpanded description):

- **Prover**: $O\big(S_{\mathrm{lay}} + (k+1)m + \mu N_d + km + kn\big)$ $R_q$-ops + $O(S_{\mathrm{JL}} + \phi N_d)$ coefficient ops + $O(L_{\mathrm{sc}}\phi/a)$ $\mathbb{F}_{q^a}$-ops. The prover applies layers successively without materialising zero blocks; the sumcheck is a chain $\prod_j\mathrm{MLE}[I\otimes M_j](x_j,x_{j+1})\cdot\mathrm{MLE}[w_{\mathrm{all}}](x_d)$ processed by standard table folding — one boundary at a time, tables contracted and discarded.
- **Verifier**: $O\big(S_{\mathrm{JL}} + \mu N_d + k\log_2 m + kn\big)$ $R_q$-ops + $O(\mu N_d)$ $\mathbb{Z}_q$-ops + $O(L_{\mathrm{sc}} + \phi/a)$ $\mathbb{F}_{q^a}$-ops. Uses $\mathrm{MLE}[I_{r_j}\otimes M_j]((x_0,x_1),(y_0,y_1)) = \mathrm{eq}(x_0,y_0)\,\mathrm{MLE}[M_j](x_1,y_1)$ — evaluates the layered matrix from the $S_{\mathrm{JL}}$-entry descriptions only, never materialising layers or their product.
- **Communication (P→V)**: $N_d$ elements of $\mathbb{Z}_q$ + $\mu + k + 1$ elements of $R_q$ + $2L_{\mathrm{sc}}$ elements of $\mathbb{F}_{q^a}$; in bits $(N_d + \phi(\mu+k+1) + 2aL_{\mathrm{sc}})\,b_q$ with $b_q := \lceil\log_2 q\rceil$ (short entries of $\mathbf v_{\mathrm{tr}}$ further compress to ~30 bits each with centred encoding).

Constant shrinkage $\varsigma$ (Corollary 1): $N_{j+1} = N_j/\varsigma$, $n_j = n_0$ ⟹ $m_j = \varsigma n_0$, $d = \log_\varsigma(N_0/n_0)$, $L_{\mathrm{sc}} = d\log_2 N_0 - \frac{d(d-1)}{2}\log_2\varsigma$, $S_{\mathrm{lay}} \le n_0N_0\frac{\varsigma}{\varsigma-1}$, $S_{\mathrm{JL}} = \varsigma n_0^2(d-1+\phi)$.

### 5.6 Periodic norm reset (Section 7.1) — unbounded folding

$\Xi^{\mathrm{lin}}$ is a one-column principal relation, so the [KLNO24, KLOT25] reductions apply. After a checkpoint the accumulator has $\beta_{\mathrm{reset}}$; after $T$ folds of $k$ witnesses $\beta_{\mathrm{in}}$:
$$\beta_T = \beta_{\mathrm{reset}} + Tk\Gamma_C\beta_{\mathrm{in}}\quad(\text{correctness}),\qquad \beta'_t = \beta'_{\mathrm{reset}} + tk\Gamma_C\beta'_{\mathrm{in}}\quad(\text{extraction}),$$
$$T \le \min\Big\{\tfrac{\beta_{\mathrm{cap}} - \beta_{\mathrm{reset}}}{k\Gamma_C\beta_{\mathrm{in}}},\ \tfrac{\beta'_{\mathrm{cap}} - \beta'_{\mathrm{reset}}}{k\Gamma_C\beta'_{\mathrm{in}}}\Big\}.\quad(\text{Eq. } 5)$$
With $\beta^*$ the SIS-hardness cap and arity $a$: $\beta^{(a)}_{\mathrm{sis}}(B) := 6\Gamma_CB$ must satisfy $\beta^{(k)}_{\mathrm{sis}}(\beta'_{\mathrm{cap}}) < \beta^*$. **Checkpoint pipeline**: $\Pi^{\mathrm{norm}}$ (exact norm check of [KLOT25]) enforces $\|w\|\le\beta_{\mathrm{cap}}$ and replaces the evaluation claim by a fresh verifier-chosen point $\mathbf r_{\mathrm{check}}$ (value $t_{\mathrm{check}}$); $\Pi^{\mathrm{dec}}$ decomposes $w = \sum_{j\in[L]}b^j\mathbf w_j$ ($\|\mathbf w_j\|\le\beta_{\mathrm{dig}}$; centred base $b$) with public recombination $\mathbf y = \sum_j b^j\mathbf y_j$, $t_{\mathrm{check}} = \sum_j b^jt_j$ where $\mathbf y_j := \mathbf F\mathbf w_j$, $t_j := \mathrm{MLE}[w_j](\mathbf r_{\mathrm{check}})$; then fold the $K\ge L$ digits with a zero accumulator:
$$\Xi^{\mathrm{lin}}_{\beta_{\mathrm{cap}}}\xrightarrow{\Pi^{\mathrm{norm}}}\Xi^{\mathrm{lin}}_{\beta_{\mathrm{cap}}}\xrightarrow{\Pi^{\mathrm{dec}}}\big(\Xi^{\mathrm{lin}}_{\beta_{\mathrm{dig}}}\big)^K\xrightarrow{\Pi^{\mathrm{fold}}}\Xi^{\mathrm{lin}}_{K\Gamma_C\beta_{\mathrm{dig}}}.$$
Repeatable indefinitely if $K\Gamma_C\beta_{\mathrm{dig}} < \beta_{\mathrm{cap}}$ and $\beta^{(k)}_{\mathrm{sis}}(\beta'_{\mathrm{cap}}) < \beta^*$; the checkpoint's cost amortises over the ordinary folds between.

### 5.7 Folding AIR (Section 7.2)

The [KLOT25] AIR reduction emits $2t$ fresh $\Xi^{\mathrm{lin}}$ instances $((\mathbf F,\mathbf y_j,\mathbf r,t_j),\mathbf w_j)_{j\in[2t]}$ at a common evaluation point under a common key; set $k = 2t$ and fold with the current accumulator. Remark 7: the AIR sumcheck can be **batched with the $\Pi_{\mathrm{fold}}$ sumcheck** (same RingSC invocation), since [KLOT25, §8.1] already observes the batching opportunity.

### 5.8 IVC usage pattern (Perspective §1.3)

PikkuFold is presented as a building block; an IVC wraps it by folding, at each step, both the computation's fresh relation(s) and *the verifier's execution of the preceding fold* — covering the algebraic claims and the Fiat-Shamir hash execution. The hash arithmetisation is called out as the nontrivial open task (SHA-256/BLAKE3/SHA-3 arithmetisation over binary or field-agnostic polynomial commitments [DP25, Bin26, BRW26] — porting to the lattice setting is open). Practical composition:
1. Choose the step relation as AIR (§5.7) — the natural fit since the reduction lands exactly on $\Xi^{\mathrm{lin}}$ instances at a common point.
2. Fold with arity $k = 2t$ per step (plus 1 accumulator slot).
3. Every $T\le\min\{\ldots\}$ (Eq. 5) steps, run a checkpoint ($\Pi^{\mathrm{norm}}$+$\Pi^{\mathrm{dec}}$+$\Pi^{\mathrm{fold}}$ with zero accumulator) to reset $\beta_{\mathrm{reset}}$.
4. Terminal statement: prove the final $\Xi^{\mathrm{lin}}$ instance with any principal-relation prover (e.g. the [KLNO24/KLOT25] stack: exact norm check + AmortisedSubvector-style inner-product arguments).

### 5.9 Exact-norm-check and decomposition reductions (checkpoint internals)

The checkpoint reuses two published reductions, applied to the one-column principal form $\begin{pmatrix}\mathbf F\\ \widetilde{\mathrm{eq}}(\mathbf s)^T\end{pmatrix}\mathbf w = \begin{pmatrix}\mathbf y\\ t\end{pmatrix}$:
- **$\Pi^{\mathrm{norm}}$** ([KLOT25]): proves $\|\mathbf w\|\le\beta_{\mathrm{cap}}$ **exactly** (not approximately — no JL here) and refreshes the evaluation claim to a new verifier point $\mathbf r_{\mathrm{check}}$; preserves $\mathbf F, \mathbf y, \mathbf w$. Cost: the expensive operation, amortised over $T$ ordinary folds.
- **$\Pi^{\mathrm{dec}}$** ([KLNO24]): centred base-$b$ decomposition $\mathbf w = \sum_{j\in[L]}b^j\mathbf w_j$ with $\|\mathbf w_j\|\le\beta_{\mathrm{dig}}$; the images and evaluation values decompose with the same coefficients, giving public recombination checks $\mathbf y = \sum_jb^j\mathbf y_j$, $t_{\mathrm{check}} = \sum_jb^jt_j$; each digit becomes a fresh $\Xi^{\mathrm{lin}}$ instance under the *same* key and a *common* evaluation point — precisely the input format of $\Pi_{\mathrm{fold}}$.
- Pad to arity $K\ge L$ with zero witnesses and fold with a zero accumulator; the output has norm $K\Gamma_C\beta_{\mathrm{dig}}$, which must be $<\beta_{\mathrm{cap}}$ for the loop to close.

## 6. Soundness & Security

### 6.0 Knowledge-error term-by-term ledger

Each additive term of $\kappa$ in Theorem 1 maps to one bad event of the four-stage extractor:

| Term | Stage / event |
|---|---|
| $k/|C|$ | coordinate-wise forking loss (Lemma 6 with $\ell = k$, sp. soundness 2): $\ell(k-1)/N = k/|C|$ |
| $k\epsilon_C$ | some forked coordinate difference $\Delta_i$ non-unit (Definition 11, base transcript fixed, second sample uniform) |
| $\kappa_{\mathrm{proj}} = \sum_j\eta_j\kappa_j$ | layered JL lower tail fails on $w^*_{\mathrm{all}}$ (union over $\phi r_j$ blocks per coarse layer, 1 fine layer) |
| $\binom{\log_2 N_d}{\mu}\frac{1}{q^\mu}$ | all $\mu$ trace-batching points hit zeros of the (non-zero) MLE of $\mathrm{Tr}(Mw^*_{\mathrm{all}}) - \mathbf v_{\mathrm{tr}}$ — multilinear root bound (Lemma 7) with $\mu$ points, degree $\mu$ each |
| $1/q^e$ | claim batching fails to detect a false initial claim (per-NTT-slot cancellation) |
| $(2\sum_j\nu_j + 1)/q^a$ | RingSC soundness $\kappa_{\mathrm{sc}}(\ell, D)$ with $\ell = \sum\nu_j$, $D = 2$ (plus the terminal-opening check) |

With the Appendix-A extractor (Proposition 3): $k/|C| + k\epsilon_C$ → $2k(1/|C| + \epsilon_C)$ and $\beta_{\mathrm{sis}} = 6\Gamma_C\beta'_{\mathrm{out}}$.

Concrete sanity at the implementation parameters: $|C|\approx2^{100.5}$, $\epsilon_C\approx2^{-15}$ (Heuristic 1, $e = 2$, $\phi = 128$: $\phi/(2q^2)$ with $q\approx2^{50}$), $\kappa_{\mathrm{proj}}$ from $\kappa_j = 2^{-100}/(d\eta_j)$-type calibration, $\binom{\log_2 256}{2}/q^2 = 3\cdot2^{-100}$, $1/q^2\approx2^{-100}$, $(2\cdot43+1)/q^2\approx2^{-94}$ — the reported aggregate $\kappa\approx2^{-90}$ (the dominating terms are the almost-splitting $\epsilon_C$ and the RingSC term under the 50-bit modulus).

### 6.1 Theorem 1 proof anatomy (extractor in four stages)

Fix the malicious prover's coins; $p$ = probability its output lies in $\Xi^{\mathrm{lin}}_{\beta'_{\mathrm{out}}}$.

**Stage 1 — folding extraction and denominator clearing.** Fix the prefix through $(t'_i), t'_{\mathrm{acc}}$. Coordinate-wise forking (Lemma 6 = [FMN24] 7.1, $\ell = k$, special-soundness 2) returns $k+1$ accepting transcripts with challenges $\mathbf z^{(0)},\dots,\mathbf z^{(k)}$, where $\mathbf z^{(i)}$ and $\mathbf z^{(k)}$ differ only in coordinate $i$ (loss $k/|C|$). Output witnesses $u^{(j)}$, $\|u^{(j)}\|\le\beta'_{\mathrm{out}}$. Set $\Delta_i := z^{(i)}_i - z^{(k)}_i$, $\mathbf a_i := u^{(i)} - u^{(k)}$; non-unit differences charged $k\epsilon_C$. Then $\|\Delta_i\|_{\mathrm{op}}\le 2\Gamma_C$, $\|\mathbf a_i\|\le 2\beta'_{\mathrm{out}}$, $\mathbf F\mathbf a_i = \Delta_i\mathbf y_i$, $\mathrm{MLE}[\mathbf a_i](\mathbf r_{d,1}) = \Delta_it'_i$. Clear denominators: $\Delta := \prod_i\Delta_i$, $\Delta_{-i} := \prod_{j\ne i}\Delta_j$,
$$\mathbf a_{\mathrm{acc}} := \Delta u^{(k)} - \sum_i z^{(k)}_i\Delta_{-i}\mathbf a_i,\qquad \mathbf F\mathbf a_{\mathrm{acc}} = \Delta\,\mathbf y_{\mathrm{acc}},\ \ \mathrm{MLE}[\mathbf a_{\mathrm{acc}}](\mathbf r_{d,1}) = \Delta t'_{\mathrm{acc}},\ \ \|\mathbf a_{\mathrm{acc}}\|\le\beta_{\mathrm{bind}},\ \|\Delta\|_{\mathrm{op}}\le\rho_{\mathrm{bind}}.$$

**Stage 2 — binding two independent extractions.** Re-run Stage 1 with independent coins (expected 2 family extractions, each ≤ $k+1$ prover invocations). If $\mathbf x_i := \mathbf a_i\hat\Delta\hat{\Delta}_i - \hat{\mathbf a}_i\Delta\Delta_i \ne 0$: $\mathbf F\mathbf x_i = 0$, $\|\mathbf x_i\|\le 8\Gamma_C\beta'_{\mathrm{out}}$ → SIS-break. If $\mathbf x_{\mathrm{acc}} := \mathbf a_{\mathrm{acc}}\hat\Delta - \hat{\mathbf a}_{\mathrm{acc}}\Delta\ne0$: $\|\mathbf x_{\mathrm{acc}}\|\le 2\beta_{\mathrm{bind}}\rho_{\mathrm{bind}}$ → SIS-break (the dominant $\beta_{\mathrm{sis}}$ term — $(2\Gamma_C)^{2k}$, exponential in arity!). Otherwise the two extractions agree on normalised vectors $\mathbf w^*_i := \Delta_i^{-1}\mathbf a_i = \hat\Delta_i^{-1}\hat{\mathbf a}_i$, $\mathbf w^*_{\mathrm{acc}} := \Delta^{-1}\mathbf a_{\mathrm{acc}}$, and these are **independent of the second transcript's verifier coins** (crucial for Stage 3).

**Stage 3 — sumcheck and projection.** Pad all $h$ claims to $\ell$ variables; batch with $\mathbf d\leftarrow\$R_q^{h-1}$; false-batched-claim survives with prob $\le q^{-e}$ (per-slot cancellation argument); RingSC contributes $(2\sum\nu_j + 1)/q^a$. All $h$ initial claims true ⟹ $\mathrm{MLE}[\mathbf w^*_i](\mathbf s_i) = t_i$, $\mathrm{MLE}[\mathbf w^*_{\mathrm{acc}}](\mathbf s_{\mathrm{acc}}) = t_{\mathrm{acc}}$, and $(\mathbf v_{\mathrm{btd}})_i = \mathbf b_{\mathbf c_i}^TMw^*_{\mathrm{all}}$. Trace check gives $\mathbf b_{\mathbf c_i}^T(\mathrm{Tr}(Mw^*_{\mathrm{all}}) - \mathbf v_{\mathrm{tr}}) = 0$ for all $i\in[\mu]$; if the parenthesised vector is non-zero, its MLE is a non-zero multilinear polynomial in $\log_2 N_d$ variables and the $\mu$ independent uniform points hit zeros with probability $\le\binom{\log_2 N_d}{\mu}/q^\mu$ (Lemma 7). Outside that: $P\,\mathrm{coeff}(w^*_{\mathrm{all}}) = \mathbf v_{\mathrm{tr}}$, and $\|\mathbf v_{\mathrm{tr}}\|\le\omega$ was verified; the **modular lower tail** of Lemma 9 with threshold $\beta'_{\mathrm{in}}$ yields $\|w^*_{\mathrm{all}}\|\le\beta'_{\mathrm{in}}$ except with probability $\kappa_{\mathrm{proj}}$ — every fresh candidate is a valid input witness.

**Stage 4 — additive accumulator reconstruction.** Baseline transcript: $\tilde w_{\mathrm{acc}} := u^{(k)} - \sum_i z^{(k)}_i\mathbf w^*_i$ equals $\mathbf w^*_{\mathrm{acc}}$ mod $q$, satisfies the linear and original evaluation claims, and $\|\tilde w_{\mathrm{acc}}\|\le\beta'_{\mathrm{out}} + k\Gamma_C\beta'_{\mathrm{in}} = \beta'_{\mathrm{acc}}$ — purely **additive** growth. Output the $k$ fresh witnesses and $\tilde w_{\mathrm{acc}}$.

**Expected runtime**: $2$ family extractions × $(k+1)$ invocations = $2k+2$ expected prover calls.

### 6.2 Appendix A — eliminating the exponential $(2\Gamma_C)^{2k}$ loss

The naive Stage-2 comparison multiplies out all $2k$ denominators for the accumulator (which has no fork of its own). [WF26]'s idea (developed for Cyclo): obtain the **two families at the same folding challenge** and compare coordinate-by-coordinate — each comparison is then three products of a challenge difference with a single witness.

- **Lemma 20 (comparison at a common challenge)**: two families with shared $\mathbf z$, fork values $\zeta_i, \hat\zeta_i$, baselines $u, \hat u$ (both opening $\mathbf y_{\mathrm{acc}} + \sum_j z_j\mathbf y_j$), $\|u\|,\|\hat u\|,\|v_i\|,\|\hat v_i\|\le\beta'_{\mathrm{out}}$, unit differences. Exactly one of: (i) $u\ne\hat u$ and $\mathbf x_u := u - \hat u$ is a SIS break of norm $2\beta'_{\mathrm{out}}$; (ii) $u = \hat u$ but some $\mathbf w^*_i\ne\hat{\mathbf w}^*_i$, and $\mathbf x_i := \mathbf a_i\hat\Delta_i - \hat{\mathbf a}_i\Delta_i$ is a SIS break of norm $6\Gamma_C\beta'_{\mathrm{out}}$; (iii) both families define the same tuple and the common accumulator opening $\mathbf w^*_{\mathrm{acc}} := u - \sum_i z_i\mathbf w^*_i$.
- **The bias problem and its resolution (Lemmas 21, 22)**: the stored challenge was selected by success, so post-hoc sampling is biased; every loop must select on success alone, and every bad event is charged at its *pre-selection* probability. Entry-weighted accounting cancels the bias exactly: a challenge is stored with probability ∝ success probability at it, and retries cost the inverse of the same quantity. Each coordinate-resampling loop and the full-coin-resampling loop cost ≤ 1 expected invocation; non-unit coordinate differences are bounded by $1/|C| + \epsilon_C$ per loop (Definition 11 exactly covers the "old value fixed, new uniform" event).
- **Proposition 3**: Theorem 1 holds with $\beta_{\mathrm{sis}} = 6\Gamma_C\beta'_{\mathrm{out}}$ and knowledge error with $k/|C| + k\epsilon_C$ replaced by $2k(1/|C| + \epsilon_C)$. Total expected invocations $2k + 2$.

### 6.3 The JL theorem (Theorem 2) — proof anatomy

- **Single-row bound** $\Pr[|\langle w,u_j\rangle| > \gamma_1\|w\|]\le 2^{-(\lambda+1)}/(2\lambda)$: ternary entry $= (\varepsilon+\varepsilon')/2$ (two Rademachers) → Rademacher-sum comparison (Bentkus–Dzindzalieta, optimal constant $\kappa_{\mathrm{BD}} = 4\Pr[Z\ge\sqrt2]\approx 3.178$): $\gamma_1(\lambda) = \mathrm{erfc}^{-1}(2^{-(\lambda+1)}/(2\lambda\kappa_{\mathrm{BD}}))$.
- **Upper tail** $\Pr[\|Jw\| > \beta\|w\|]\le 2^{-(\lambda+1)}$: moment domination — every even moment of a ternary entry ≤ that of $\mathcal N(0,1/2)$ (Lemma 13), so $\mathbb E[(\|Jw\|^2)^p]\le\mathbb E[((1/2)\chi^2_{2\lambda})^p] = \Gamma(\lambda+p)/\Gamma(\lambda)$; Markov, optimise over integer $p$.
- **Lower tail** $\Pr[\|Jw\|\le\alpha\|w\|]\le 2^{-(\lambda+1)}$ — the hard part. Gaussian substitution fails uniformly ($w = e_1$ gives $\mathrm{Bin}(2\lambda,1/2)$ with heavier deep left tail, Figure 3). Route: Laplace transform $L_w(s) = \mathbb E[e^{-s\langle w,u\rangle^2}]$; Fourier identity (Lemma 15) $L_w(s) = \mathbb E_\xi\prod_j\cos^2(w_j\xi/2)$, $\xi\sim\mathcal N(0,2s)$; envelope $\mathrm{env}(s) := \max\{(1+e^{-s})/2,\ (1+s)^{-1/2}\}$ with branches meeting at $s^\times\approx 2.31057$, $\mathrm{env}(s^\times)\approx 0.549602$; peeling (Lemma 16) splits coordinates into ≤ 4 "large" ($|w_j|>0.45$) and the rest (bounded via $\cos^2y\le e^{-y^2}$ on $|y|\le\pi/2$); one dominant coordinate handled analytically (Lemma 17); 2–4 large coordinates by **branch-and-bound finite certification** (Proposition 1: 645 / 9,241 / 33,687 boxes for $d = 2,3,4$; largest accepted bound 0.549600938, $1.3\times10^{-6}$ below the envelope). Uniform bound (Proposition 2): $\sup_{\|w\|=1}L_w(s^\times)\le 0.5508 =: \Psi$. Chernoff (Eq. 2): $\alpha(\lambda) = -\frac{(\lambda+1)+2\lambda\log_2\Psi}{s^\times\log_2 e}\approx 0.216\lambda - 0.300$.
- **Modular bound** (three regimes, following [BS23, App. A]) — with $t := \ell\theta$ and auxiliary constants $T, D, A = rD, C = D/\sqrt{r^2-1}, \delta = 0.52\sqrt2/\sqrt{r^2-1}, \tau = \kappa_{\mathrm{BD}}\mathrm{erfc}(D/2)$:

| Regime | Hypothesis | Argument | Failure bound |
|---|---|---|---|
| 1 | $\theta\le\|w\|<q/D$ | either $\|Jw\|\le t\le\ell\|w\|$ (real lower tail) or some row has $|\langle w,u_j\rangle|\ge q(1-\ell/b)>\gamma_1q/D>\gamma_1\|w\|$ (single-row) | $2^{-(\lambda+1)}+(2\lambda)\frac{2^{-(\lambda+1)}}{2\lambda}=2^{-\lambda}$ |
| 2 | $\|w\|_\infty\ge q/A$ | condition each row on all entries but $u_{j,h}$: one of $u_{j,h}\in\{0,\pm1\}$ gives $|\langle w,u\rangle\bmod q|\ge|w_h|/2\ge q/2A$ w.p. $\ge1/2$; #such rows stochastically dominates $\mathrm{Bin}(2\lambda,1/2)$; $t<\ell q/b<Tq/2A$ forces $<T$ rows | $2^{-2\lambda}\sum_{i<T}\binom{2\lambda}i\le2^{-\lambda}$ |
| 3 | $\|w\|\ge q/D$, $\|w\|_\infty<q/A$ | disjoint-support split $w=v+(w-v)$, $q/C<\|v\|<q/D$; $X=\langle v,u\rangle$ Berry–Esseen-close to $\mathcal N(0,\|v\|^2/2)$; for each $Z\bmod q=a$ the wrap set $G_a$ has measure $\le2t$; density $\le1/(\sqrt\pi\|v\|)$ | per-row $\frac{2C\ell}{\sqrt\pi b}+2\delta+\tau<2^{-1/2}$ → $(2^{-1/2})^{2\lambda}=2^{-\lambda}$ |

  The three lower bounds on $b(\lambda)$ in Equation (4) — $\frac{\ell}{1-\gamma_1/D}$, $\frac{2A\ell}{\sqrt\pi}$, $\frac{2C\ell}{\sqrt\pi\sqrt{2-2\delta-\tau}}$ — are respectively $\Theta(\lambda)$, $\Theta(\sqrt\lambda)$, $\Theta(\lambda)$, so $b(\lambda) = \Theta(\lambda)$ and the admissible modular threshold is $q/b(\lambda) = \Theta(q/\lambda)$. Asymptotic calibrations: $T_\lambda = \Theta(\lambda)$, $D_\lambda = \gamma_1(\lambda)+1 = \Theta(\sqrt\lambda)$.

### 6.4 Challenge sampler guarantees

- Lemma 18 (exact): $C^{\mathrm{fw}}_{f,s,B}$ strong sampling with $|C| = (2B)^s\binom\phi s$, $\Gamma_C\le sB\max_i\|\zeta_f^i\|_{\mathrm{op}}$ (= $sB$ for power-of-two).
- Lemma 19 (rejection): uniform output, geometric trials $1/p_S(\gamma)$, strong sampling preserved, $\Gamma_C\le\gamma$.
- Heuristic 1 (almost-splitting): $\epsilon_C\approx\phi/(eq^e)$ if $|C|\ge q^e$; validated pointwise (Table 4: e.g. $q=127$, $s=3$: predicted $2^{-7.977}$ vs observed $2^{-7.959}$; $q=6143$, $s=5$: $2^{-19.169}$ vs $2^{-18.956}$ — agreement to ~0.3 bits).
- Remark 6: bounded-weight unions $C^{\mathrm{fw}}_{f,\le s,B}$ gain ≈0.165 bits over fixed weight at $(f,s,B) = (256,23,1)$ — dominated by the weight-$s$ layer; fixed weight is exactly samplable (Fisher–Yates + ±$B$ values) whereas bounded-weight needs mixture sampling; uniform-ternary-then-reject is hopeless ($\Pr[\mathrm{wt}\le23]\approx2^{-96.2}$ in degree 128).

### 6.5 Worked norm-budget arithmetic (concrete parameters)

At the implementation setting: $k = 2$, $d = 3$ layers of 256 rows, $\lambda = 128$ per-layer constants $\ell_j = \sqrt{27.37}\approx 5.232$, $u_j = \sqrt{343.2}\approx 18.53$, $b_j = 126$; $\beta_{\mathrm{in}}$ from coefficients uniform in $\{-2^{10},\dots,2^{10}\}$ over $m\phi$ coordinates: $\|w\|\approx\sqrt{m\phi}\cdot 2^{10}/\sqrt3\approx 2^{10}\sqrt{2^{20}\cdot128/3}\approx2^{18.3}$; $\Gamma_C = 8.357$; $\kappa = 2^{-90}$ target with $\kappa_j$ calibrated so $\kappa_{\mathrm{proj}}\approx 2^{-90}$ over $\eta_j = \phi r_j$ blocks:
- $\omega = \sqrt{k}\beta_{\mathrm{in}}\prod u_j = \sqrt2\cdot\beta_{\mathrm{in}}\cdot 18.53^3 \approx 1.41\cdot 6363\cdot\beta_{\mathrm{in}}\approx 8.97\times10^3\beta_{\mathrm{in}}$ — the sent trace must be below ~$2^{13}\beta_{\mathrm{in}}$, comfortably encoding in ~30 bits per coordinate given a 50-bit $q$ (fits $\approx q/2^{20}$… recheck: 30-bit coords cap $\|v_{\mathrm{tr}}\|\le\sqrt{256}\cdot2^{30} = 2^{34}$, and $\omega\approx2^{31.1}$ for $\beta_{\mathrm{in}}\approx2^{18.3}$ — consistent).
- $\beta'_{\mathrm{in}} = \omega/\prod\ell_j = 8.97\times10^3\beta_{\mathrm{in}}/5.232^3 \approx 62.7\beta_{\mathrm{in}}$ — the *extraction-side* fresh bound is ~63× looser than the correctness-side one; this is the price of approximate (JL) norm certification, absorbed by sizing the input relation's $\beta'_{\mathrm{in}}$-membership accordingly.
- Modular chain condition per layer: $\beta'_{\mathrm{in}}\prod_{h\le j}\ell_h\le q/b_j$, i.e. at $j=3$: $62.7\beta_{\mathrm{in}}\cdot5.232^3\approx 8.97\times10^3\beta_{\mathrm{in}}\le2^{50}/126\approx2^{43}$ ⟹ $\beta_{\mathrm{in}}\le2^{30.1}$ ✓ with huge margin (the binding constraint is usually the SIS cap, not the wrap-around).
- Per-fold accumulator growth: $k\Gamma_C\beta_{\mathrm{in}}\approx 2\cdot8.357\beta_{\mathrm{in}}\approx16.7\beta_{\mathrm{in}}$ — additive per fold; with rank $n$ sized for 32 folds: $\beta_{32}\approx\beta_0 + 32\cdot16.7\beta_{\mathrm{in}}\approx535\beta_{\mathrm{in}}$ plus resets — consistent with the 32-fold budget of Table 5's estimates.
- SIS cap: with the Appendix-A extractor, $\beta_{\mathrm{sis}} = 6\Gamma_C\beta'_{\mathrm{out}}\approx 50\beta'_{\mathrm{out}}$; the Lattice Estimator [APS15, commit 53da598] at $(q,n,m,\phi) = (2^{50}-2687, 12{\to}13, 2^{18..22}, 128)$ sizes the key for the 32-round worst case.

### 6.6 Design-space comparison (why LRP beats the alternatives)

| Strategy | Verifier work | In-protocol commitment? | Norm growth | Users |
|---|---|---|---|---|
| Dense $J$, send $v = Jw$ | linear in witness dim ✗ | no | multiplicative $(\alpha,\beta)$-certified | [BS23, NS24] (as sub-protocol, verifier sees matrix) |
| One layer $I_r\otimes J_0$ | succinct ✓ | **yes** (image still large) | multiplicative | [KLNO25, KLOT25, Osa26] |
| Range proof (A1) sumcheck | linear in $\beta$ ✗ | no | exact | [BC25a, NS26, GLLO26] (Cyclo inputs) |
| Monomial decomposition (A2) | succinct | **yes** (decomposition commitment) | exact | [BC25b] (LatticeFold+) |
| **LRP (this paper)** | succinct ✓ | **no** | multiplicative on extraction side, additive on accumulator | PikkuFold |

The LRP row achieves: the verifier evaluates only the $S_{\mathrm{JL}}$ ternary entries (like the one-layer case); the final image has $N_d = 256$ coordinates → sent directly (like the dense case); the accumulator keeps Cyclo-style additive growth because the projection attaches only to the fresh inputs.

## 7. Parameters & Concrete Efficiency

### 7.1 JL constants (Table 1, $2\lambda$ rows)

| $\lambda$ | $2\lambda$ | $\gamma_1$ | $\alpha$ | $\beta$ | $b$ |
|---|---|---|---|---|---|
| 64 | 128 | 6.97 | 13.53 | 171.8 | 73 |
| 96 | 192 | 8.43 | 20.45 | 257.5 | 100 |
| **128** | **256** | **9.66** | **27.37** | **343.2** | **126** |
| 192 | 384 | 11.75 | 41.21 | 514.6 | 176 |
| 256 | 512 | 13.51 | 55.05 | 686.0 | 224 |

Auxiliary modular constants (Table 2, $\lambda = 128$): $T_\lambda = 30$, $D_\lambda = 10.08$, $r_\lambda = 6.53$; derived $A_\lambda = r_\lambda D_\lambda$, $C_\lambda = D_\lambda/\sqrt{r_\lambda^2-1}$, $\delta_\lambda = 0.52\sqrt2/\sqrt{r_\lambda^2-1}$, $\tau_\lambda = \kappa_{\mathrm{BD}}\,\mathrm{erfc}(D_\lambda/2)$.

### 7.2 Sampler tradeoffs (Table 3, full transcription; challenge-collision target $2^{-100}$ / $2^{-128}$; $B_{64} = 2$, $B_{128} = B_{256} = 1$; expected-trial targets $T\in\{1,4,16,64\}$; calibration on $2^{18}$ samples)

| Target | $\phi$ | $s$ | $B$ | Base cardinality | Exp. trials | Accepted cardinality | Threshold $\gamma$ |
|---|---|---|---|---|---|---|---|
| $2^{-100}$ | 64 | 22 | 2 | $\approx2^{100.157}$ | 1.00 | $\approx2^{100.157}$ | 44.000 |
| $2^{-100}$ | 64 | 23 | 2 | $\approx2^{103.026}$ | 4.00 | $\approx2^{101.025}$ | 13.602 |
| $2^{-100}$ | 64 | 24 | 2 | $\approx2^{105.798}$ | 15.87 | $\approx2^{101.810}$ | 12.540 |
| $2^{-100}$ | 64 | 25 | 2 | $\approx2^{108.477}$ | 64.05 | $\approx2^{102.475}$ | 11.940 |
| $2^{-100}$ | 128 | 21 | 1 | $\approx2^{100.026}$ | 1.00 | $\approx2^{100.026}$ | 21.000 |
| $2^{-100}$ | 128 | 22 | 1 | $\approx2^{103.308}$ | 4.00 | $\approx2^{101.307}$ | 9.259 |
| $2^{-100}$ | 128 | 23 | 1 | $\approx2^{106.512}$ | 15.86 | $\approx2^{102.525}$ | 8.773 |
| $2^{-100}$ | 128 | 23 | 1 | $\approx2^{106.512}$ | 62.56 | $\approx2^{100.545}$ | **8.357** (impl.) |
| $2^{-100}$ | 256 | 17 | 1 | $\approx2^{103.879}$ | 1.00 | $\approx2^{103.879}$ | 17.000 |
| $2^{-100}$ | 256 | 17 | 1 | $\approx2^{103.879}$ | 3.98 | $\approx2^{101.885}$ | 8.688 |
| $2^{-100}$ | 256 | 18 | 1 | $\approx2^{108.610}$ | 15.80 | $\approx2^{104.628}$ | 8.365 |
| $2^{-100}$ | 256 | 18 | 1 | $\approx2^{108.610}$ | 65.44 | $\approx2^{102.578}$ | 8.007 |
| $2^{-128}$ | 64 | 34 | 2 | $\approx2^{128.491}$ | 1.00 | $\approx2^{128.491}$ | 68.000 |
| $2^{-128}$ | 64 | 35 | 2 | $\approx2^{130.269}$ | 4.00 | $\approx2^{128.268}$ | 16.937 |
| $2^{-128}$ | 64 | 37 | 2 | $\approx2^{133.555}$ | 16.10 | $\approx2^{129.546}$ | 15.792 |
| $2^{-128}$ | 64 | 38 | 2 | $\approx2^{135.061}$ | 62.86 | $\approx2^{129.087}$ | 15.027 |
| $2^{-128}$ | 128 | 31 | 1 | $\approx2^{129.621}$ | 1.00 | $\approx2^{129.621}$ | 31.000 |
| $2^{-128}$ | 128 | 32 | 1 | $\approx2^{132.221}$ | 3.98 | $\approx2^{130.229}$ | 11.218 |
| $2^{-128}$ | 128 | 32 | 1 | $\approx2^{132.221}$ | 16.12 | $\approx2^{128.210}$ | 10.381 |
| $2^{-128}$ | 128 | 33 | 1 | $\approx2^{134.762}$ | 63.88 | $\approx2^{128.765}$ | 10.030 |
| $2^{-128}$ | 256 | 23 | 1 | $\approx2^{131.078}$ | 1.00 | $\approx2^{131.078}$ | 23.000 |
| $2^{-128}$ | 256 | 23 | 1 | $\approx2^{131.078}$ | 3.99 | $\approx2^{129.082}$ | 10.164 |
| $2^{-128}$ | 256 | 24 | 1 | $\approx2^{135.357}$ | 15.90 | $\approx2^{131.366}$ | 9.699 |
| $2^{-128}$ | 256 | 24 | 1 | $\approx2^{135.357}$ | 63.08 | $\approx2^{129.378}$ | 9.281 |

Reading guide: at degree 128 and target $2^{-100}$, allowing ~63 expected trials cuts the expansion-factor bound from 21 (no rejection) to 8.357 — a 2.5× reduction in per-fold accumulator growth $k\Gamma_C\beta_{\mathrm{in}}$, at the price of a 63× slower challenge sampler (amortised: 2 challenges per fold).

### 7.2b Almost-splitting pointwise measurements (Table 4, full; $e = 2$, $2^{24}$ samples, 16 worst anchors, $2^{24}$ fresh accepted challenges per anchor)

| $q$ | $s$ | $|C^{\mathrm{fw}}_{256,s,1}|$ | $\gamma$ | Exp. trials | $|C^{\mathrm{fw}}_{256,s,1}(\gamma)|$ | $\phi/(eq^e)$ (predicted) | Observed $\epsilon_C$ |
|---|---|---|---|---|---|---|---|
| 127 | 3 | $\approx2^{21.381}$ | 2.9 | 5.04 | $\approx2^{19.047}$ | $\approx2^{-7.977}$ | $\approx2^{-7.959}$ |
| 383 | 4 | $\approx2^{27.347}$ | 3.4 | 9.86 | $\approx2^{24.045}$ | $\approx2^{-11.162}$ | $\approx2^{-10.928}$ |
| 1151 | 4 | $\approx2^{27.347}$ | 3.7 | 2.92 | $\approx2^{25.802}$ | $\approx2^{-14.337}$ | $\approx2^{-14.089}$ |
| 1279 | 4 | $\approx2^{27.347}$ | 3.7 | 2.92 | $\approx2^{25.802}$ | $\approx2^{-14.642}$ | $\approx2^{-14.463}$ |
| 1663 | 4 | $\approx2^{27.347}$ | 3.8 | 1.71 | $\approx2^{26.572}$ | $\approx2^{-15.399}$ | $\approx2^{-15.286}$ |
| 2687 | 5 | $\approx2^{32.979}$ | 4.0 | 8.35 | $\approx2^{29.918}$ | $\approx2^{-16.784}$ | $\approx2^{-16.524}$ |
| 5119 | 5 | $\approx2^{32.979}$ | 4.0 | 8.35 | $\approx2^{29.918}$ | $\approx2^{-18.643}$ | $\approx2^{-18.385}$ |
| 6143 | 5 | $\approx2^{32.979}$ | 4.1 | 5.61 | $\approx2^{30.491}$ | $\approx2^{-19.169}$ | $\approx2^{-18.956}$ |

### 7.3 Communication estimates (Table 5, $k = 2$, $q = 2^{64}-59$, $\lambda = 128$, $\kappa = 2^{-100}$, 64-trial sampler, 32 sequential folds; witnesses uniform in $\{-2^{10},\dots,2^{10}\}$; "Comm." = $k$ fresh commitments, "Protocol" = in-protocol messages)

| Degree $\phi$ | $M=2^{25}$ Comm./Prot. (KB) | $M=2^{27}$ | $M=2^{29}$ |
|---|---|---|---|
| 64 | 18.41 / 4.80 | 18.41 / 4.92 | 19.38 / 5.04 |
| 128 | 17.44 / 7.16 | 19.38 / 7.28 | 19.38 / 7.40 |
| 256 | 19.38 / 11.97 | 19.38 / 12.09 | 19.38 / 12.21 |

### 7.4 Implementation runtimes (Table 6; $f = 256$, $\phi = 128$, $q = 2^{50}-2687$ ($e = a = 2$), $k = 2$, challenges $C^{\mathrm{fw}}_{256,23,1}(8.357)$ under Heuristic 1 → $\kappa\approx2^{-90}$, 3 projection layers × 256 rows, $\mu = 2$, rank $n$ for 32 folds; RoKoko-derived AVX-512 codebase; single thread, Intel i7-11850H; Fiat–Shamir non-interactive)

| $(k,m,\phi)$ | $(2,2^{18},128)$ | $(2,2^{20},128)$ | $(2,2^{22},128)$ |
|---|---|---|---|
| Commitment rank $n$ | 12 | 12 | 13 |
| Sumcheck rounds $\ell$ | 40 | 43 | 46 |
| Commitment (per input) | 191 ms | 803 ms | 2280 ms |
| **Prover (one fold)** | **455 ms** | **1699 ms** | **6539 ms** |
| **Verifier** | **3.87 ms** | **5.39 ms** | **9.80 ms** |
| **Communication** | **5.62 KB** | **5.72 KB** | **5.83 KB** |

SALSAA on the same machine, matched input sizes: commitment 413/1806 ms; **prover 7662/31668 ms (≈17×/19× slower)**; verifier 0.42/0.43 ms; communication 62.25/66.06 KB. SALSAA's largest instance exhausted the machine's memory. Prover time split: projections ≈ half, sumcheck ≈ quarter at every size. Verifier dominated by terminal evaluation of layer descriptions + expansion of projection matrices (scanning $S_{\mathrm{JL}}$ ternary entries). Terminal message: $k+1$ evaluations $t'_i$ + $\mu$ batched projections + $\mathbf v_{\mathrm{tr}}$ (short entries ≈ 30 bits each). Each round polynomial: two $\mathbb{F}_{q^2}$ coefficients (third fixed by consistency).

### 7.5 Cross-scheme communication (Table 7; every prover message of the fold, excluding incoming instances' commitments)

| Scheme | Fresh inputs | $\log_2 q$ | Coords/input | Communication |
|---|---|---|---|---|
| LatticeFold [BC25a] | 1 | 64 | $2^{32}$ | ≈ 250 KB |
| LatticeFold+ [BC25b] | 1 | 128 | $2^{27}$ | ≲ 100 KB |
| Neo [NS26] | 1 | 64 | $2^{26}$ | ≈ 140 KB |
| Scheme of [Osa26] | 1 | 64 | $2^{27}$ | ≈ 110 KB |
| ProtogaLattice [BNP26] | 1 | 64 | $2^{31}$ | ≈ 83 KB |
| SALSAA [KLOT25] | 4 | 50 | $2^{26}$ | 62.25 KB |
| Cyclo [GLLO26] | 1 | 50 | $2^{27}$ | 31.8 KB |
| **PikkuFold** | **2** | **50** | **$2^{27}$** | **5.72 KB** |

Cyclo's "extension commitment" alone ≈ 10 KB of its total. The advantage is not a modulus artefact: at the 64-bit modulus, degree 128 gives 7.3 KB and degree 64 ≈ 5 KB (Table 5). Caveat: figures indicative (moduli 50–128 bits, different arities/relations/soundness targets).

### 7.6 Analysis: why PikkuFold beats SALSAA and Cyclo (and where it doesn't)

**vs SALSAA [KLOT25]** (same machine, matched sizes): SALSAA's fold communicates 62–66 KB because it (a) commits to the JL-projected image (approach A3 — its accumulator needs two commitments), and (b) runs norm-upgrading exact checks with decompositions. Its prover is 17–19× slower: the projections plus the committed-image bookkeeping plus the larger transcript hashing. Its verifier is *faster* (0.42 ms vs 3.87 ms) — SALSAA's verifier does less terminal work because more was pushed into commitments; PikkuFold's verifier scans the layer descriptions ($O(S_{\mathrm{JL}})$) instead. At $(2,2^{22},128)$ SALSAA could not even run (memory exhausted) while PikkuFold completes in 6.5 s + 9.8 ms.

**vs Cyclo [GLLO26]**: Cyclo achieves additive norm growth with a single-relation accumulator (same paradigm PikkuFold adopts) but handles large-$\beta$ inputs via an "extension commitment" — essentially a recommitment to an aggressively decomposed witness — which alone costs ~10 KB and whose computation is expensive; for small-$\beta$ inputs it uses (A1) range proofs whose cost is linear in $\beta$. PikkuFold removes both: the LRP certifies norms at cost *independent of $\beta$*, and the certificate is sent, not committed. Result: 5.72 KB vs 31.8 KB at comparable instances. Cyclo folds 1 fresh input per step vs PikkuFold's $k = 2$ (arity is a knob; the knowledge error scales linearly in $k$ through $2k(1/|C|+\epsilon_C)$ and $\beta_{\mathrm{out}}$ grows as $k\Gamma_C\beta_{\mathrm{in}}$).

**vs LatticeFold+ [BC25b]**: LatticeFold+ folds full R1CS/CCS-derived linear relations with exact (monomial-based) range proofs — stronger relaxation semantics (exact bounds, unbounded folding without checkpoints) at ≲100 KB per fold and a much bigger prover (commitment-dominated). PikkuFold's ~17× smaller transcript buys bounded-depth folding (until a checkpoint) over principal/AIR relations. Choice depends on the target: constraint-system generality (LatticeFold+) vs minimal communication and prover speed (PikkuFold).

**Caveats carried by the PikkuFold numbers**: (i) 50-bit modulus (RoKoko codebase constraint) — Table 5 shows the 64-bit estimates stay in the same range (7.3 KB at degree 128, ≈5 KB at degree 64); (ii) $\kappa\approx2^{-90}$ under Heuristic 1 rather than $2^{-128}$ exact; (iii) no zero knowledge; (iv) the comparison table mixes moduli/arities/relations, as the paper itself flags.

## 8. Implementation Notes

### 8.1 What to build on the `lzk` core engine

| `lzk` module | PikkuFold consumer |
|---|---|
| `rings.ZqX` ($X^\phi+1$, NTT) | $R_q$ arithmetic; $q = 2^{50}-2687$ with degree-2 slots ($e=2$); incomplete NTT over $\mathbb{F}_{q^2}$ |
| `fields.GF tower` | $\mathbb{F}_{q^2}$ for RingSC challenges and subfield batching ($a = 2$) |
| `commit.ajtai` | $\mathbf F\mathbf w = \mathbf y$; rank-$n$ keys sized for 32 folds |
| `sumcheck.ring_norm` (RingSC) | Definition 15 exactly: subfield batching + field sumcheck + $R_q$ terminal opening + omitted-coefficient round encoding |
| `sumcheck.multilinear` | the batched degree-2 chain over layer boundaries; table folding with boundary contraction |
| `encoding.tensor_lde` | $\widetilde{\mathrm{eq}}$, MLE, LMLE; $\mathrm{MLE}[I_r\otimes M]((x_0,x_1),(y_0,y_1)) = \mathrm{eq}(x_0,y_0)\mathrm{MLE}[M](x_1,y_1)$ |
| `transcript.fiat_shamir` | non-interactive derivation of $\delta$, $\mathbf c_i$, $\mathbf d$, round challenges, $\mathbf z$ |

New modules required:
1. **`trace.dual_basis`**: $b_i^\vee$ computation (solve $\mathrm{Tr}(b_ib_j^\vee) = \delta_{ij}$; for power-of-two conductors the dual of the power basis is explicit: $b_i^\vee = \frac1\phi X^{-i}$ — verify), $\mathrm{Lift}_{\mathrm{fine}}$/$\mathrm{Lift}_{\mathrm{coarse}}$ and the Lemma 4 identities as unit tests.
2. **`jl.ternary`**: layered matrix sampling $J_j\leftarrow\$\chi^{n_j\times m_j}$ from a seed; Table 1/2 constants as a lookup; the norm-preservation unit tests (sample $w$, check $\ell\|w\|\le\|Jw\|\le u\|w\|$ empirically).
3. **`sampler.fixed_weight`**: Fisher–Yates selection of $s$ positions + uniform $\pm B$ values; operator-norm test via canonical embedding ($\|c\|_{\mathrm{op}} = \|c\|_{\sigma,\infty}$ for $f = 2\phi$: compute $2\phi$ evaluations by FFT, take max modulus); rejection loop with expected-trial budget; entropy accounting $\log_2|C(\gamma)| = \log_2|C| + \log_2p$.
4. **`fold.pikkufold`**: the $\Pi_{\mathrm{fold}}$ driver + periodic-norm-reset checkpoint ($\Pi^{\mathrm{norm}}, \Pi^{\mathrm{dec}}$ from [KLOT25]).

### 8.2 Algorithms & data structures

- **Layer storage**: never materialise $I_{r_j}\otimes M_j$; store only $J_j$ ($n_jm_j$ ternary entries, 2 bits each) + dimensions. Prover applies layers blockwise; verifier evaluates MLEs from the ternary descriptions.
- **Sumcheck chain structure** (prover side): the batched polynomial is $\prod_j\mathrm{MLE}[I\otimes M_j](x_j,x_{j+1})\cdot\mathrm{MLE}[w_{\mathrm{all}}](x_d)$ (times eq-paddings and the fresh/acc evaluation tables). Standard MLE table folding: fix boundary $j$'s challenge, contract its table into the adjacent layer, discard. Each non-zero layer entry and each witness entry processed $O(1)$ times per round pair.
- **$\mathbf v_{\mathrm{tr}}$ encoding**: $N_d$ balanced representatives, ~30 bits each (empirically short since $\omega$ caps the norm) — centred/golomb-style encoding; this is the single largest message.
- **Terminal reconstruction**: verifier rebuilds $\mathrm{MLE}[w_{\mathrm{all}}](\mathbf r_{d,0},\mathbf r_{d,1}) = \sum_i\mathrm{eq}(\mathbf r_{d,0})_it'_i$ — never sends the generic RingSC terminal ring element.
- **Challenge sampler at concrete params**: $C^{\mathrm{fw}}_{256,23,1}$, reject above $\gamma = 8.357$, ≈ 62.6 expected trials per challenge, $k=2$ challenges per fold.
- **Accumulator state**: $(\mathbf F, \mathbf y_{\mathrm{acc}}, \mathbf s_{\mathrm{acc}}, t_{\mathrm{acc}})$ + prover-side $\mathbf w_{\mathrm{acc}}$; after each fold $\mathbf s_{\mathrm{fold}} := \mathbf r_{d,1}$ (the evaluation point migrates to the sumcheck terminal point — no old-point bookkeeping).

### 8.3 Complexity cheatsheet (constant shrinkage $\varsigma$; Corollary 1)

- Prover: $O\big(n_0N_0\frac{\varsigma}{\varsigma-1} + (k+1)m + \mu n_0 + km + kn\big)$ $R_q$-ops — note $\frac{\varsigma}{\varsigma-1}\to 1$ for aggressive shrinkage, so the projection cost approaches one dense pass of size $n_0N_0$.
- Verifier: $O\big(\varsigma n_0^2(d-1+\phi) + \mu n_0 + k\log_2 m + kn\big)$ $R_q$-ops.
- Communication: $(N_d + \phi(\mu+k+1) + 2aL_{\mathrm{sc}})b_q$ bits; $N_d = n_0 = $ final layer rows (256 concrete).

### 8.4 Pitfalls & edge cases

1. **$\|\cdot\|$ is the coefficient $\ell_2$ norm by default** — not $\ell_\infty$, not canonical. All bounds ($\beta_{\mathrm{in}}$, $\omega$, JL factors) are $\ell_2$; mixing conventions silently breaks Theorem 1.
2. **Balanced representatives everywhere** (Definition 2): modular reduction returns coordinate-wise balanced reps; the JL modular bound (Definition 16 item 2) is *false* for non-balanced reps, and the norm check $\|\mathbf v_{\mathrm{tr}}\|\le\omega$ must be computed on balanced values.
3. **Wrap-around margin**: the modular JL guarantee only holds for thresholds $\theta\le q/b(\lambda)$ — with $b = 126$ and 50-bit $q$, thresholds must be below $q/126$; the chain condition $\beta'_{\mathrm{in}}\prod_{h\le j}\ell_h\le q/b_j$ for **every** layer must be re-checked at setup (it is a per-layer constraint, not just the final one).
4. **$w_{\mathrm{all}}$ excludes the accumulator** — the projection certifies only the fresh witnesses. Accidentally including $\mathbf w_{\mathrm{acc}}$ breaks the soundness structure (the accumulator's shortness is never proven; it grows additively and is reset by checkpoints).
5. **The evaluation-point homogenisation order matters**: the fresh/acc claims must be converted to sumcheck form and batched *with* the projection claims so that all terminal claims land at the same $\mathbf r_{d,1}$ before the fold. The fold's $t_{\mathrm{fold}} = t'_{\mathrm{acc}} + \sum z_it'_i$ uses the *terminal* values, not the original $t_i$.
6. **RingSC omitted coefficient**: each round polynomial is transmitted as $D$ field elements with the consistency-fixed coefficient omitted — a naive "send all $D+1$" implementation changes the communication and the Fiat-Shamir transcript layout.
7. **Two-layer boundary indexing inversion**: variable set $x_i$ carries $\nu_{d-i}$ variables — boundary 0 is the projection output, boundary $d$ the witness. Off-by-one here scrambles the LMLE.
8. **Almost-splitting heuristic is a heuristic**: $\epsilon_C\approx\phi/(eq^e)$ is conjectural for the fixed-global-weight + rejection distribution; the concrete instantiation accepts $\kappa\approx2^{-90}$ (not $2^{-128}$) partly due to this. If the security target demands rigor, fall back to the exact Lemma 18 setting (larger $\gamma = sB$, worse $\Gamma_C$) or parallel-repetition amplification.
9. **Extractor bias (Appendix A)**: any reimplementation of the [WF26]-style improved extraction must select loops on success alone and charge bad events pre-selection; conditioning on success makes bounds unbounded (the paper is explicit about this trap).
10. **SIS-break bound with naive extraction is exponential in arity** ($2(k+1)\beta'_{\mathrm{out}}(2\Gamma_C)^{2k}$): for $k>2$ use Proposition 3's $6\Gamma_C\beta'_{\mathrm{out}}$; when porting to other schemes check which extraction stage you are in.
11. **$\mathrm{Tr}$ is $\mathbb{Z}_q$-linear, not $R_q$-linear**: the trace identities (Lemma 4) hold mod $q$ with the dual-basis pairing; do not "simplify" $\mathrm{Tr}(ab) = \mathrm{Tr}(a)\mathrm{Tr}(b)$ (false).
12. **Layer count vs rounds**: $L_{\mathrm{sc}} = d\log_2N_0 - \frac{d(d-1)}{2}\log_2\varsigma$ — the quadratic term means too many layers *reduces* rounds but multiplies $\prod u_j$ (norm inflation) and $\kappa_{\mathrm{proj}}$; 3 layers at 256 rows is the sweet spot at the concrete parameters.
13. **No zero knowledge**: the protocol leaks $\mathbf v_{\mathrm{tr}}$ (a norm certificate of $w_{\mathrm{all}}$) and terminal evaluations; ZK requires additional techniques (Libra-style, §1.3 Perspective).
14. **Fiat-Shamir**: protocol is non-interactive via FS; the transcript must fix the layer matrix $M$ *before* the challenges $\mathbf c_i$ (it is sampled as public randomness — in NI mode derive its seed first, then everything else in Figure 2 order).

### 8.5 Fiat-Shamir transcript layout (non-interactive form, one fold)

Absorb order (domain-separated labels; every derive point is a distinct challenge):
1. Absorb public parameters: commitment key seed (for $\mathbf F$), ring params $(f,\phi,q,e,a)$, layer dimensions $(r_j,m_j,n_j)_{j\in[d]}$, thresholds $\omega,\mu$.
2. Derive the projection seed → expand $J_0,\dots,J_{d-1}$ (ternary entries) — the layer matrix is public randomness sampled *first*.
3. Absorb the input instances: $(\mathbf y_i,\mathbf s_i,t_i)_{i\in[k]}$ and accumulator $(\mathbf y_{\mathrm{acc}},\mathbf s_{\mathrm{acc}},t_{\mathrm{acc}})$.
4. Absorb $\mathbf v_{\mathrm{tr}}$ → verifier-side check $\|\mathbf v_{\mathrm{tr}}\|\le\omega$ is a circuit predicate, not a challenge.
5. Derive trace-batching points $(\mathbf c_i)_{i\in[\mu]}$ → absorb $\mathbf v_{\mathrm{btd}}$.
6. Derive claim-batching vector $\mathbf d\leftarrow\$ R_q^{h-1}$ (in the public-coin reading the verifier samples it; in NI form derive from transcript).
7. Derive the subfield-batching vector $\delta\leftarrow\$(\mathbb{F}_{q^2})^{\phi/2}$.
8. For each of the $L_{\mathrm{sc}}$ RingSC rounds: absorb the 2 $\mathbb{F}_{q^2}$ coefficients → derive the round challenge.
9. Absorb terminal evaluations $(t'_i)_{i\in[k]}, t'_{\mathrm{acc}}$.
10. Derive folding challenges $\mathbf z\leftarrow\$ C^k$ — **last** challenge; the accumulator is never multiplied by anything derived later.
11. Output the folded instance $(\mathbf F,\mathbf y_{\mathrm{fold}},\mathbf s_{\mathrm{fold}} = \mathbf r_{d,1}, t_{\mathrm{fold}})$.

### 8.6 Memory & streaming plan

- $\mathbf F\in R_q^{n\times m}$: at $(m,\phi) = (2^{20},128)$, $n = 12$: $12\cdot2^{20}\cdot128\cdot50$ bits ≈ 9.6 GB — **never materialise**; expand block-columns from a seed on the fly (RoKoko-style), or precompute NTT form per block and stream. Commitment time (803 ms per input in the reference) suggests the reference keeps $\mathbf F$ resident or recomputes with AVX-512; in Python/numpy, generate column-blocks lazily and cache LRU.
- $w_{\mathrm{all}}$: $km\phi$ coefficients = $2\cdot2^{20}\cdot128$ ≈ 268M small coefficients (11 bits each) ≈ 370 MB — stream per boundary during sumcheck table folding.
- Layer matrices: $S_{\mathrm{JL}}\approx\varsigma n_0^2(d-1+\phi)\approx2\cdot256^2\cdot130\approx1.7\times10^7$ ternary entries ≈ 4 MB (2 bits each) — keep resident.
- Sumcheck tables: the largest is the boundary-0 table of size $N_0 = km$ ring elements; contract and discard after each boundary → peak memory $O(N_0)$ ring elements ≈ 5 GB if materialised naively; use the product-chain structure to keep only two adjacent boundary tables.

### 8.7 Parallelisation notes

- The projection applications ($I_{r_j}\otimes M_j$ per block) are embarrassingly parallel across blocks — the natural SIMD/threads axis.
- Sumcheck table folding halves each table per round; the two rounds per boundary can pipeline with the projection application of the next boundary.
- The reference implementation is single-threaded and already 17× faster than SALSAA's; the paper's bottleneck analysis (projections ≈ ½, sumcheck ≈ ¼ of prover time) tells you exactly where threads help.

### 8.8 Porting to other schemes (drop-in value)

- The certified JL constants (Theorem 2/Table 1) directly upgrade any protocol using ternary JL projections with heuristic constants (LaBRADOR [BS23], Greyhound [NS24], SLAP [AFLN24], the [LSS24] NIST submission): swap $n_{\mathrm{rp}},\alpha_{\mathrm{rp}},\beta_{\mathrm{rp}},b$ for the certified values at the matching $\lambda$ (a few percent cost vs the heuristic constants).
- The fixed-weight + operator-norm-rejection sampler is a drop-in replacement wherever short ring challenges with invertible differences are needed (LatticeFold/LatticeFold+/Neo/Cyclo/SALSAA/ProtogaLattice and the Schnorr-style argument family): pick the target $2^{-\lambda'}$ and expected-trial budget $T$ from Table 3's methodology, read off $\gamma$.
- The layered-projection trick itself generalises: any place where a JL image is currently *committed* (approach A3) can potentially send the image directly if the projection is layered down to a few hundred coordinates — the requirements are the sumcheck-ability of the layer product (LMLE) and the trace identity to integers.

### 8.9 Test vectors

- Lemma 4 identities on random $J, W, w$ (fine/coarse lifts) — exact mod-$q$ equality.
- Lemma 10 trace identity for $d\in\{1,2,3\}$ random layered matrices.
- Theorem 2 spot statistics: $\|Jw\|/\|w\|\in[\sqrt\alpha,\sqrt\beta]$ for random and adversarial $w$ (spike $e_1$, flat, mixed) at $\lambda=128$; modular wrap: $\|Jw\bmod q\|>\sqrt\alpha\theta$ for $\|w\|\ge\theta$ with $w\in[\pm q/2]^m$.
- Sampler: uniformity over accepted set (chi-square), expected trials within 10% of target, $\|c\|_{\mathrm{op}}\le\gamma$ exact via canonical embedding; strong-sampling spot check at small almost-splitting primes reproducing Table 4.
- End-to-end: $k=2$ fold at toy parameters ($\phi = 8$, small $q$, 2 layers), verify $\Xi^{\mathrm{lin}}_{\beta_{\mathrm{out}}}$ membership and $\beta$ accounting across 10 folds + one checkpoint ($\Pi^{\mathrm{norm}}+\Pi^{\mathrm{dec}}$) restoring $\beta_{\mathrm{reset}}$.
- Extraction simulation: honest-but-curious "malicious" prover with one out-of-range fresh witness → norm check must catch with prob $\ge 1-\kappa_{\mathrm{proj}}$.

### 8.10 Design-decision checklist

- [ ] Pick $\lambda$ and per-layer $\kappa_j$ first (they fix $\ell_j, u_j, b_j$ from Table 1), then choose $d$ and row counts $n_j$: the product $\prod_j u_j$ inflates $\omega$ (communication-side encoding width) while $\prod_j\ell_j$ deflates $\beta'_{\mathrm{in}}$ (extraction-side looseness) — 3 layers × 256 rows is the reference point.
- [ ] Verify the modular chain condition $\beta'_{\mathrm{in}}\prod_{h\le j}\ell_h\le q/b_j$ **for every $j$**, not only the last.
- [ ] Decide the challenge-sampler regime: exact (Corollary 2, larger $\Gamma_C = sB$) vs almost-splitting heuristic (small $\gamma\approx 8$, conjectural $\epsilon_C$) — document which soundness claim the implementation carries.
- [ ] Decide arity $k$: communication grows only through $k$ terminal values and $k$ folding challenges, but $\beta_{\mathrm{out}}$ grows as $k\Gamma_C\beta_{\mathrm{in}}$ and the naive extractor's SIS bound is exponential in $k$ — use Appendix A always for $k>1$.
- [ ] Fix the checkpoint cadence $T$ from Eq. 5 with the actual $\beta_{\mathrm{cap}}, \beta^*$ from the Lattice Estimator.
- [ ] Choose the terminal prover for the final accumulator instance (needed for a complete SNARK; not part of the paper).
- [ ] Plan the $\mathbf F$ expansion strategy (seeded streaming) before benchmarking — 9.6 GB at the reference parameters.
- [ ] If porting to 64-bit $q$ (Table 5 estimates): re-derive $\kappa$ (RingSC terms improve as $q^a$ grows), re-run the estimator for the rank $n$.

### 8.11 Cross-references within this repo

- `docs/papers/latticefold_plus.md`: the monomial-based exact range proof (approach A2) and the R1CS/CCS linearisation — the "expression-rich but heavier" alternative; PikkuFold's §1.1 cites its decomposition commitments as the communication cost driver.
- `docs/papers/cyclo.md`: the additive-norm-growth paradigm PikkuFold inherits and the partial range checks / pay-per-bit techniques that motivated replacing (A1) with the LRP certificate.
- `docs/papers/symphony.md`: high-arity folding in the ROM — orthogonal use of folding where the arity/communication tradeoffs differ.
- The `lzk` RingSC module should be shared verbatim between the LatticeFold+ and PikkuFold paths (both consume exactly Definition 15's interface: subfield batching + field sumcheck + ring terminal opening).

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
