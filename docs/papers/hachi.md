# Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields — Deep Analysis & Implementation Spec

> Source: `papers_txt/hachi.txt` (Nguyen–O'Rourke–Zhang, ePrint 2026/156, ~2.2k extracted
> lines). All lemma/theorem/figure/equation numbers below are cross-referenced to the paper.
> Cross-references to Akita's Appendix F.1 (which audits this paper) are marked **[Akita F.1]**.

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields |
| **Authors** | Ngoc Khanh Nguyen¹, George O'Rourke¹, Jiapeng Zhang² (¹ King's College London, ² University of Southern California) |
| **Venue/date** | IACR ePrint 2026/156; direct predecessor of Akita (LayerZero Labs), successor of Greyhound (CRYPTO 2024) |
| **Assumption** | Module-SIS in the $\ell_\infty$ norm (Def. 1: find $z$ with $Az=0$, $0<\|z\|_\infty\le\beta$, for uniform $A\in R_q^{n\times m}$); Fiat–Shamir in the ROM |
| **Headline** | Multilinear PCS over $R_q$ (and, via a generic reduction, over extension fields $\mathbb{F}_{q^k}$) with **succinct poly$(\ell,\lambda)$ proofs** and **square-root verifier** $\tilde O(\sqrt{2^\ell}\lambda)$ — an $\tilde O(\lambda)$ asymptotic improvement over Greyhound's $\tilde O(\lambda\cdot\sqrt{2^\ell\lambda})$, i.e. a concrete **12.5× verification speedup** at $\ell=30$ (2800 ms → 227 ms) with ~**55 KB** proofs. |

Key contributions:

1. **Faster verification via ring switching**: replaces Greyhound/LaBRADOR's
   Johnson–Lindenstrauss random-projection norm proof with a **sumcheck-based
   $\ell_\infty$-norm proof**; integrates Greyhound with the ring-switching technique of
   Huang–Mao–Zhang (ePrint 2025/199): lift $R_q$-relations to $\mathbb{Z}_q[X]$, evaluate at a
   random $X:=\alpha\in\mathbb{F}_{q^k}$, run sumcheck over $\mathbb{F}_{q^k}$. **The verifier
   performs no cyclotomic-ring multiplications at all** — unique among lattice
   SNARKs/PCSs/folding schemes.
2. **Generic reduction $\mathbb{F}_{q^k}\to R_q$** for polynomial-evaluation proofs (§3):
   generalizes SLAP in two directions — extension fields (for suitable parameter regimes)
   and univariate→multilinear. Embeds $\mathbb{F}_{q^k}$ as the fixed subring
   $R_q^H$ for $H=\langle\sigma_{-1},\sigma_{4^k+1}\rangle$; packs $d/k$ field elements
   into one ring element via a bijection $\psi$ with a trace identity
   $\mathrm{Tr}_H(\psi(a)\sigma_{-1}(\psi(b)))=\frac dk\langle a,b\rangle$ (Thm 2).
3. **Ring-dimension flexibility**: sumcheck runs over the extension field (independent of
   $d$), so $d$ can be chosen large (e.g. 1024 vs Greyhound's 64): faster NTT-based
   commitment (ring multiplications fall as $d^2$, NTT cost grows only $d\log d$) and
   sparser challenge sets. Measured **3–5× faster commitment**.
4. Prototype Rust implementation (github.com/georgeorourke/hachi-pcs): first-round
   verification 12–29× faster than Greyhound; ~55 KB end-to-end proof (7.3 KB Hachi round +
   4.8 KB handoff + 43 KB Greyhound tail).

**Comparison (paper Fig. 1):**

| Scheme | Multilinear | Extension fields | Asymptotic proof | Verifier | Concrete proof ($\ell=30$) | Verifier |
|---|---|---|---|---|---|---|
| Greyhound [NS24] | ✗ | ✗ | poly$(\ell,\lambda)$ | $\tilde O(\lambda\sqrt{2^\ell\lambda})$ | 53 KB | 2.8 s |
| **Hachi** | ✓ | ✓ | poly$(\ell,\lambda)$ | $\tilde O(\sqrt{2^\ell}\lambda)$ | 55 KB | 227 ms |

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter (128-bit target) |
| $\ell$ | number of variables of the committed multilinear polynomial; $L:=2^\ell$ |
| $q$ | odd prime, $q\equiv5\pmod 8$; concrete: $q=4294967197\approx2^{32}$ |
| $d:=2^\alpha$ | ring dimension (power of two); concrete $d=1024$ ($\alpha=10$) |
| $k:=2^\kappa$ | extension degree; must divide $d/2$; concrete $k=4$ ($\kappa=2$) |
| $R, R_q$ | $\mathbb{Z}[X]/(X^d+1)$, $\mathbb{Z}_q[X]/(X^d+1)$ |
| $R_q^H$ | fixed subring $\{x\in R_q:\sigma(x)=x\ \forall\sigma\in H\}$; isomorphic to $\mathbb{F}_{q^k}$ (Lemma 5) |
| $\sigma_i:X\mapsto X^i$ | Galois automorphism, $i\in\mathbb{Z}_{2d}^\times$; $\mathrm{Aut}(R)=\{\sigma_i\}$ |
| $H$ | $\langle\sigma_{-1},\sigma_{4^k+1}\rangle\subseteq\mathrm{Aut}(R)$ |
| $\mathrm{Tr}_H$ | $R_q$-trace $\mathrm{Tr}_H(a):=\sum_{\sigma\in H}\sigma(a)\in R_q^H$ |
| $\psi$ | packing bijection $(R_q^H)^{d/k}\to R_q$ (Thm 2, Eq. 8) |
| $\mathrm{cf}(y)$ | coefficient vector $(y_0,\dots,y_{d-1})\in\mathbb{F}_q^d$ |
| $r\bmod^\pm q$ / $r\bmod^+q$ | centered (in $[-\frac{q-1}2,\frac{q-1}2]$) / canonical (in $[0,q)$) representative |
| $\|w\|_\infty,\|w\|_p$ | norms over centered coefficient vectors ($\|w\|:=\|w\|_2$ by default) |
| $S_\beta$ | ring elements with coefficients in $[\lceil-\beta/2\rceil,\lceil\beta/2\rceil-1]$ |
| $b$ | decomposition base; concrete $b=16$ |
| $\delta:=\lceil\log_bq\rceil$ | gadget depth; concrete 8 |
| $\tau$ | gadget depth for $z$ ($\lceil\log_b\beta\rceil$); concrete 4 |
| $G_{b,n}$ | gadget matrix $I_n\otimes(1\ b\ b^2\cdots b^{\delta-1})\in R_q^{n\times n\delta}$; $G_{b,n}^{-1}$ balanced-decomposition right inverse |
| $J_n$ | $I_n\otimes(1\ b\ \cdots\ b^{\tau-1})$ — response-depth gadget |
| $m,r$ | folding split, $\ell=m+r$ (after $\mathbb{F}_{q^k}\to R_q$ reduction: $\ell-\alpha=m+r$); concrete $m=r=10$ |
| $n_A,n_B,n_D$ | module ranks of commitment matrices; concrete $(1,1,1)$ |
| $A,B,D$ | commitment key matrices: $A\in R_q^{n_A\times\delta2^m}$, $B\in R_q^{n_B\times n_A\delta2^r}$, $D\in R_q^{n_D\times\delta2^r}$ |
| $f_i$, $s_i$, $t_i$, $\hat t_i$ | per-block coefficient vectors; $s_i=G^{-1}_{2^m,1}(f_i)$ (Eq. 13); $t_i=As_i$; $\hat t_i=G^{-1}_{n_A}(t_i)$ |
| $u$ | outer commitment $u:=B(\hat t_1,\dots,\hat t_{2^r})\in R_q^{n_B}$ (Eq. 14) |
| $w_i$, $\hat w_i$, $v$ | partial evaluations $w_i:=a^\top G_{2^m}s_i$; digits $\hat w_i=G^{-1}_1(w_i)$; opening commitment $v:=D\hat w\in R_q^{n_D}$ (Eq. 16) |
| $\mathbf{a},\mathbf{b}$ | evaluation-point-derived public vectors: $b^\top:=(x_1^{i_1}\cdots x_r^{i_r})_{i\in\{0,1\}^r}\in R_q^{2^r}$; $a^\top:=(x_{r+1}^{j_1}\cdots x_\ell^{j_m})_{j\in\{0,1\}^m}\in R_q^{2^m}$ |
| $c=(c_1,\dots,c_{2^r})$ | folding challenges from $\mathcal{C}\subseteq\{c\in R_q:\|c\|_1\le\omega\}$ |
| $\omega$ | challenge $\ell_1$ bound; concrete 16 (16 non-zero ±1 coefficients) |
| $\beta$ | $\ell_\infty$ bound on $z$; concrete $z_{max}=30583$ |
| $\bar\beta,\bar\omega,\bar\gamma$ | $(2b^k,2\omega,b)$ weak-opening bounds (Lemma 8) |
| $z$, $\hat z$ | folded witness $z:=\sum_ic_is_i$; $\hat z=J^{-1}_{2^m}(z)$ |
| $\alpha$ | ring-switching challenge $\leftarrow\mathbb{F}_{q^k}$ (also used for $\log d$... note symbol overload: $\alpha=\log_2 d$ AND the evaluation point — the paper uses $\alpha$ for both) |
| $\tau_0,\tau_1$ | zero-check random points: $\tau_0\in\mathbb{F}_{q^k}^{\log\mu+\log d}$ (smallness), $\tau_1\in\mathbb{F}_{q^k}^{\log n}$ (linear relation) |
| $\tilde w$ | witness MLE over $\mathbb{F}_{q^k}$ (Eq. 21): $\tilde w(u,\ell)=z_{u,\ell}$ ($u\le\mu$), $r_{u-\mu,\ell}$ ($\mu<u\le\mu+n$) |
| $\tilde\alpha,\tilde M_\alpha$ | MLEs: $\tilde\alpha(\ell)=\alpha^\ell$; $\tilde M_\alpha(i,u)=M_{i,u}(\alpha)$, $-(\alpha^d+1)$ at $i+\mu=u$, else 0 |
| $H_0,H_\alpha$ | batched constraint polynomials (Eqs. 22/23) |
| $F_{0,\tau_0},F_{\alpha,\tau_1}$ | sumcheck summands |
| $y_i$ | partial evaluations sent in the $\mathbb{F}_q$-coefficients optimization (§3.2) |
| $\varphi(Z)$ | irreducible degree-$k$ polynomial defining $\mathbb{F}_{q^k}=\mathbb{F}_q[Z]/\varphi(Z)$ |
| $\mathrm{mle}[f]$ | multilinear extension over an arbitrary ring (Def. 2) |
| $\widetilde{eq}$ | $\prod_j(1-i_j)(1-x_j)+i_jx_j$ |
| $\mathfrak n,\ \beta$ (§4.5) | length/norm parameters of the recursive witness $\tilde w\in\mathbb{Z}_q^{\mathfrak n\cdot d}$ |
| $d'=2^{\alpha'}$ | next-iteration ring dimension (concrete 64 when handing off to Greyhound) |
| $\hat w_j$ | packed partial sums $\sum_i\tilde w_{j\|i}Z^{\sum i_t2^{t-1}}\in\mathbb{F}_{q^k}$ (Eq. 25) |
| $Z_0,Z_{k-j}$ | subfield basis elements $1$ and $X^{\frac d{2k}(k-j)}-X^{\frac d{2k}(k+j)}$ (§4.5) |

## 3. Algebraic Setting

- **Rings/fields**: $R_q=\mathbb{Z}_q[X]/(X^d+1)$, $q\equiv5\bmod8$ (minimal splitting: $X^d+1$
  factors into exactly 2 irreducibles mod $q$). $\mathbb{F}_{q^k}$ for $k\mid d/2$ embedded as the
  fixed subring $R_q^H$, $H=\langle\sigma_{-1},\sigma_{4^k+1}\rangle$.
- **Lemma 5 (subfields)**: $R_q^H\simeq\mathbb{F}_{q^k}$; each element has the form (Eq. 7)
  $a:=\sum_{j=1}^{k}a_{k-j}\big(\frac d{2k}\big)^{-1}\big(X^{\frac d{2k}(k-j)}-X^{\frac d{2k}(k+j)}\big)$
  (with $a_0$ coefficient), $k$ degrees of freedom $a_0..a_{k-1}\in\mathbb{Z}_q$.
- **Theorem 2 (inner product via trace — the core packing)**: with
  $\psi:(R_q^H)^{d/k}\to R_q$,
  $\psi(a_0,\dots,a_{d/k-1}):=\sum_{i=0}^{d/2k-1}a_i\cdot X^i+\sum_{i=0}^{d/2k-1}X^{d/2}\cdot a_{d/2k+i}\cdot X^i$
  (Eq. 8; two "banks" of $d/2k$ subfield elements, second bank multiplied by $X^{d/2}$):
  $\psi$ is a bijection and
  $\mathrm{Tr}_H(\psi(a)\cdot\sigma_{-1}(\psi(b)))=\frac dk\langle a,b\rangle$.
  Proof ingredients: $\langle4^k+1\rangle=\{(4k)\alpha+1\}$ (order $d/(2k)$);
  $\mathrm{Tr}_H(X^i)=0$ unless $d/2k\mid i$ (then $d/k$); $\mathrm{Tr}_H(X^{d/2})=0$.
- **Lemma 6**: $\|a\|_\infty\le\beta\Rightarrow\|\psi(a)\|_\infty\le2\beta$ (some packed
  coefficients are sums of two input coefficients).
- **Lemma 2 (Micciancio)**: $\|fg\|_\infty\le\|f\|_1\|g\|_\infty$.
- **Lemma 3 (LS18 invertibility)**: $q\equiv5\bmod8$ ⇒ any $f\in R_q$ with
  $0<\|f\|_\infty<q^{1/2}/\sqrt2$ or $0<\|f\|_2<q^{1/2}$ is invertible.
- **Gadget decomposition**: base-$b$ $G_{b,n}$, balanced digits in
  $[\lceil-b/2\rceil,\lceil b/2\rceil-1]$, $G_{b,n}G^{-1}_{b,n}(t)=t$; response gadget $J_n$
  with depth $\tau=\lceil\log_b\beta\rceil$.
- **Multilinear extensions over rings** (Def. 2): $\mathrm{mle}[f](x)=\sum_{i}f(i)\widetilde{eq}(i,x)$
  over an arbitrary ring $R$ (used over $R_q$, $\mathbb{Z}_q$, $\mathbb{F}_{q^k}$).
- **CWSS** (Def. 3 + Lemma 4, from FMN24): $(\ell_1..\ell_\mu)$-coordinate-wise
  $(k_1,..,k_\mu)$-special soundness with tree size
  $K=\prod_i(\ell_i(k_i-1)+1)=\mathrm{poly}(\lambda)$ ⇒ knowledge error
  $\sum_i\ell_ik_i/|S_i|^{\ell_i}$; Fiat–Shamir version holds in the ROM.
- **Module-SIS** (Def. 1): $\mathrm{MSIS}_{q,d,n,m,\beta}$, $\ell_\infty$ flavor.

## 4. Relations

### 4.1 The split-and-fold relation (Eq. 1, from BBC+18)

Knowledge of $s_1,\dots,s_r\in R_q^m$ with
$\begin{pmatrix}A\\B\end{pmatrix}\begin{pmatrix}s_1\\\dots\\s_r\end{pmatrix}=u\pmod q$,
$\|s_i\|\le\beta$. Fold: $z:=\sum_ic_is_i$; verify
$B(t_1,\dots,t_r)=u$, $Az=\sum_ic_it_i$, $\|z\|$ short, where $t_i=As_i$ are the
"partial evaluations" (split).

### 4.2 Multilinear evaluation as a quadratic equation (§4, Eq. 12/15)

For $\ell=m+r$ and evaluation point $(x_1,..,x_\ell)\in R_q^\ell$:
$f(x)=b^\top\begin{pmatrix}a^\top G_{2^m}\\ \dots\\ a^\top G_{2^m}\end{pmatrix}\begin{pmatrix}s_1\\\dots\\s_{2^r}\end{pmatrix}$
with $b^\top:=(x_1^{i_1}\cdots x_r^{i_r})_i\in R_q^{2^r}$,
$a^\top:=(x_{r+1}^{j_1}\cdots x_\ell^{j_m})_j\in R_q^{2^m}$,
$f_i:=(f_{i\|j})_j$, $s_i:=G^{-1}_{2^m,1}(f_i)$.

### 4.3 The full one-round relation (Eq. 20)

$(\hat w,\hat t,\hat z)\in S_b^{2^r\delta}\times S_b^{2n_A\delta}\times S_b^{2^m\delta\tau}$
(i.e. all coefficients in the balanced base-$b$ alphabet) satisfying:

$$\begin{pmatrix}D&0&0\\0&B&0\\b^\top G_{2^r}&0&0\\(c^\top\otimes G_1)&0&-a^\top G_{2^m}J_{2^m}\\0&c^\top\otimes G_{n_A}&-AJ_{2^m}\end{pmatrix}\begin{pmatrix}\hat w\\ \hat t\\ \hat z\end{pmatrix}=\begin{pmatrix}v\\u\\u\\0\\0\end{pmatrix}.$$

Rows: (i) opening commitment $v=D\hat w$; (ii) outer commitment
$u=B\hat t$; (iii) evaluation $u=b^\top G_{2^r}\hat w$; (iv) fold-consistency
$a^\top G_{2^m}z=(c^\top\otimes G_1)\hat w$ (Eq. 18); (v) inner consistency
$Az=(c^\top\otimes G_{n_A})\hat t$ (Eq. 19).

### 4.4 Weak openings (§4.1)

A weak opening for $u$: $(s_i,\hat t_i,c_i)_{i\in[2^r]}$ with
$\|c_is_i\|\le\bar\beta$, $\|c_i\|_1\le\bar\omega$, $c_i\in R_q^\times$,
$As_i=G_{n_B}\hat t_i$, $B(\hat t_i)_i=u$, $\|(\hat t_i)_i\|_\infty\le\bar\gamma$.
Message recovered via Eq. 13. Binding w.r.t. weak openings under MSIS
(Lemma 7: two distinct weak openings ⇒ $[A|B]z=0$ with
$0<\|z\|_\infty\le\max(2\bar\omega\bar\beta,2\bar\gamma)$).

### 4.5 Ring-switched linear relation (§4.3)

$\mathcal{R}^{lin}_{q,d,n,\mu,b}:=\{(z\in R_q^\mu,(M\in R_q^{n\times\mu},y\in R_q^n)):Mz=y\wedge\|z\|_\infty\le b-1\}$.
Ring switching: $Mz=y\iff\exists r\in(\mathbb{Z}_q^{<d}[X])^n$:
$Mz=y+(X^d+1)r$ (in $\mathbb{Z}_q[X]$). Gadget-decompose $r=\sum_ub^ur_u$; prove
$\|z\|_\infty,\|r_u\|_\infty\le b-1$. Evaluate at random $\alpha\in\mathbb{F}_{q^k}$:
$\forall i:\sum_jM_{i,j}(\alpha)z_j(\alpha)=y_i(\alpha)+(\alpha^d+1)r_i(\alpha)$.
Constraints as polynomials over $\mathbb{F}_{q^k}$ (with $\tilde w$ the MLE of $(z,r)$, Eq. 21):
- linear: $H_\alpha(t):=\sum_{i\in[n]}\widetilde{eq}(t,i)\big[\sum_{u,\ell}\tilde M_\alpha(i,u)\tilde w(u,\ell)\tilde\alpha(\ell)-y_i(\alpha)\big]$ (Eq. 22);
- smallness (vanishing over the balanced alphabet $\{0,\pm1,\dots,\pm(b-1)\}$):
  $H_0(t):=\sum_{\ell,u}\widetilde{eq}(t,(u,\ell))\tilde w(u,\ell)(\tilde w-1)(\tilde w+1)\cdots(\tilde w-b+1)(\tilde w+b-1)$ (Eq. 23).

### 4.6 $\mathbb{F}_{q^k}$ evaluation claims as $R_q$ relations (§3)

- **Generic (§3.1)**: $f\in\mathbb{F}_{q^k}[X_1..X_\ell]$, point $(x_1..x_\ell)\in\mathbb{F}_{q^k}^\ell$, $k=2^\kappa$,
  $d=2^\alpha$: rewrite as Eq. 10 (outer sum over $i\in\{0,1\}^{\ell-\alpha+\kappa}$, inner over
  $j\in\{0,1\}^{\alpha-\kappa}$); define $F_i:=\psi((f_{i\|j})_j)$ and
  $v:=\psi((x_{\ell-\alpha+\kappa+1}^{j_1}\cdots x_\ell^{j_{\alpha-\kappa}})_j)$; then
  $\frac dk y=\mathrm{Tr}_H(Y\cdot\sigma_{-1}(v))$ with
  $Y:=\sum_ix_1^{i_1}\cdots x_{\ell-\alpha+\kappa}^{i_{\ell-\alpha+\kappa}}F_i$.
  Prover sends the single ring element $Y$; remaining task: evaluation proof for the
  $(\ell-\alpha+\kappa)$-variate polynomial $F=(F_i)_i$ over $R_q$.
- **$\mathbb{F}_q$-coefficients optimization (§3.2)**: if $f\in\mathbb{Z}_q[X_1..X_\ell]$ but the point is over
  $\mathbb{F}_{q^k}$: send $k$ partial evaluations $y_i\in\mathbb{F}_{q^k}$ (only $k-1$ needed;
  $y_{0..0}$ derived) with $y=\sum_ix_1^{i_1}\cdots x_\kappa^{i_\kappa}y_i$ (Eq. 11); define
  $f'(X_{\kappa+1},..,X_\ell):=\sum_if_i(X_{\kappa+1},..,X_\ell)\cdot Z^{\sum_ti_t2^{t-1}}\in\mathbb{F}_{q^k}[\cdot]$
  and prove $f'(x_{\kappa+1},..,x_\ell)=\sum_iy_iZ^{\sum i_t2^{t-1}}$; generic transformation then
  yields an $(\ell-\alpha)$-variate (not $\ell-\alpha+\kappa$) $R_q$ claim.
  **[Akita F.1]**: *this §3.2 shortcut, as published, is unsound for $k>2$* — the two checks
  (multilinear recombination over the head variables + basis combination) leave a
  nontrivial joint kernel in $\mathbb{E}^k$; Akita replaces it with the Diamond–Posen
  tensor reduction. The Hachi authors have acknowledged and corrected it in
  non-public revisions. The generic §3.1 transformation is unaffected.
- **Costs (Fig. 2)**: $f\in\mathbb{F}_{q^k}$: $\ell-\alpha+\kappa$ variables, prover cost $d\log q$ bits.
  $f\in\mathbb{F}_q$: $\ell-\alpha$ variables, cost $(d+k(k-1))\log q$ bits.

### 4.7 Recursive-witness evaluation (§4.5)

$\mathrm{mle}[\tilde w](a_1..a_\ell)=y$ when only $\tilde w\in\mathbb{Z}_q^{\mathfrak n\cdot d}$ is
committed (no re-decomposition — coefficients already short): split
$\mathbf a=(a_1..a_{\ell-\kappa})$, $\mathbf a_1=(a_{\ell-\kappa+1}..a_\ell)$; send $k$
partials $y_i=\sum_j\tilde w_{j\|i}\widetilde{eq}(j,\mathbf a_0)$ (Eq. 24); pack
$\hat w_j:=\sum_i\tilde w_{j\|i}Z^{\sum i_t2^{t-1}}$ (Eq. 25); then
$\sum_j\hat w_j\widetilde{eq}(j,\mathbf a_1)=e^\top(f^\top\otimes I_{2^{r'}})\hat w_j$
(Eq. 27) and, by Theorem 2, equals the $R_{q'}$-trace of
$\hat p:=e^\top(\sigma_{-1}(\psi(f))^\top\otimes I_{2^{r'}})\psi(\hat w)$;
$\|\psi(\hat w)\|_\infty\le2\beta$ ⇒ commit without decomposition and prove the
quadratic relation natively in Greyhound. Handoff communication:
$(k-1)k\log q+d'\log q$ bits (Eq. 28).

## 5. Protocols — full step-by-step transcription

### 5.1 Commitment (§4.1, LaBRADOR-style inner/outer)

Key: $A\in R_q^{n_A\times\delta2^m}$, $B\in R_q^{n_B\times n_A\delta2^r}$ (both uniform).

1. View $f$ as $2^r$ blocks $f_i\in R_q^{2^m}$; decompose $s_i:=G^{-1}_{2^m,1}(f_i)\in R_q^{2^m\delta}$ (Eq. 13).
2. Inner commitments $t_i:=As_i\in R_q^{n_A}$; digitize $\hat t_i:=G^{-1}_{n_A}(t_i)$.
3. Outer commitment $u:=B(\hat t_1,\dots,\hat t_{2^r})\in R_q^{n_B}$ (Eq. 14).
   Opening: $(s_i,\hat t_i)_i$. (Same matrix reused when shapes coincide; regenerated from a
   seeded PRNG per invocation in the prototype.)

### 5.2 Figure 3 — one fold of the opening proof (interactive)

Public: $A\in R_q^{n_A\times\delta2^m}$, $B\in R_q^{n_B\times n_A\delta2^r}$,
$D\in R_q^{n_D\times\delta2^r}$ (uniform); statement: commitment
$u\in R_q^{n_B}$, evaluation $u$, vectors $\mathbf a,\mathbf b$ (Eq. 15).

**Prover**
1. For $i\in[2^r]$: $w_i:=a^\top G_{2^m}s_i$; $\hat w:=G^{-1}_{2^r,1}(w)$; send
   $v:=D\hat w\in R_q^{n_D}$ →
**Verifier**
2. Sample challenges $c:=(c_1,\dots,c_{2^r})\leftarrow\mathcal{C}^{2^r}$, where
   $\mathcal{C}\subseteq\{c\in R_q:\|c\|_1\le\omega\}$ → c
**Prover**
3. $z:=\sum_{i=1}^{2^r}c_is_i$; abort if $\|z\|_\infty>\beta$;
   $\hat z=J^{-1}_{2^m}(z)$; send $\hat t,\hat w,\hat z$ →
**Verifier**
4. Check $(\hat w,\hat t,\hat z)\in S_b^{2^r\delta}\times S_b^{2n_A\delta}\times S_b^{2^m\delta\tau}$
   and the 5-row linear system of Eq. 20.

In the final scheme the last message is NOT sent in the clear — knowledge of a valid
$(\hat w,\hat t,\hat z)$ is proved via §4.3/§5.3.

### 5.3 Figure 4 — ring switching: $R_q$ equations → $\mathbb{F}_{q^k}$

**Prover**: $t:=\mathrm{Com}(z,r)$ → **Verifier**: $\alpha\leftarrow\mathbb{F}_{q^k}$ → **Prover**: opens
$z,r$ → **Verifier** checks: $t=\mathrm{Com}(z,r)$; $z\in\mathbb{Z}_q^{<d}[X]$ and
$\|z\|_\infty,\|r\|_\infty\le b-1$; $\forall i\in[n]$:
$\sum_jM_{i,j}(\alpha)z_j(\alpha)=y_i(\alpha)+(\alpha^d+1)r_i(\alpha)$.
Soundness: degree $\le2d-1$ residual ⇒ $(2d-1)/|\mathbb{F}_{q^k}|$; formalized as
$2d$-special soundness (Lemma 9).

### 5.4 Figure 5 — zero-checks for $H_0$ and $H_\alpha$

**Verifier** sends $\tau_0\leftarrow\mathbb{F}_{q^k}^{\log\mu+\log d}$,
$\tau_1\leftarrow\mathbb{F}_{q^k}^{\log n}$ → **Prover** sends $\tilde w$ → **Verifier** checks
$t=\mathrm{Com}(\tilde w)$, reconstructs $H_0,H_\alpha$ (Eqs. 22/23), and checks
$H_0(\tau_0)=0$, $H_\alpha(\tau_1)=0$. CWSS with $D:=\max(2d,2b-1)$ transcripts
(Lemma 10: either extract a valid $\tilde w$ with $H_0\equiv0,H_\alpha\equiv0$, or break
Com binding).

### 5.5 Figure 6 — sumcheck round (reinterpreted)

For $H(X):=P(X)\cdot Q(\tilde w(X))$ with public $P,Q$: in round $i$ the prover sends
$g_i(X_i):=\sum_{b_j}H(a_{<i},X_i,b_{i+1},\dots,b_\ell)$; verifier checks
$g_i(0)+g_i(1)=z_{i-1}$, samples $a_i\leftarrow\mathbb{F}_{q^k}$, sets $z_i:=g_i(a_i)$;
final round: prover sends $\tilde w$; verifier checks $\mathrm{Com}$, all round equations,
and the running values. Special soundness with $D=\deg(H)+1$ transcripts (Lemma 11);
sumcheck special-soundness = composition of Figure 6 over all rounds.

### 5.6 Figure 7 — the complete ring-switched sumcheck ("Efficient Sumcheck via Ring Switching")

1. P: $t:=\mathrm{Com}(z,r)$; send $t$.
2. V: $\alpha\leftarrow\mathbb{F}_{q^k}$, $\tau_0\leftarrow\mathbb{F}_{q^k}^{\log\mu+\log d}$,
   $\tau_1\leftarrow\mathbb{F}_{q^k}^{\log n}$; send $(\alpha,\tau_0,\tau_1)$.
3. Sumcheck on $H_0(\tau_0)$ and $H_\alpha(\tau_1)$: per round $i$ P sends
   $g_i(X_i)$ → V sends $a_i\leftarrow\mathbb{F}_{q^k}$; repeat for $O(\ell+\alpha)$ rounds
   (degree: 2 coefficients per round for $F_{\alpha,\tau_1}$; $b+1$ for $F_{0,\tau_0}$).
4. P opens $t$ to evaluate $\tilde w(a_1,\dots,a_\ell)$.
5. V evaluates $\tilde M_\alpha(a_1,\dots,a_\ell)$ (the expensive part) and checks the
   sumcheck.

### 5.7 The full recursive evaluation protocol (§4.4–4.5)

Composition: (a) §3 transformation ($\mathbb{F}_{q^k}\to R_q$, or §3.2 for $\mathbb{F}_q$
coefficients); (b) Figure 3 fold with committed (not revealed) $(\hat w,\hat t,\hat z)$;
(c) Figure 7 ring-switched sumcheck over $\mathbb{F}_{q^k}$ for the Eq.-20 relation +
smallness; (d) recursion: the next statement is an evaluation claim for
$\mathrm{mle}[(z',r')]$ over $\mathbb{F}_{q^k}$ with short coefficients — handle via §4.5
(eq-splitting + $\psi$-packing, no re-decomposition) and either repeat Hachi or hand off
to Greyhound ($d'=64$, short witness $\psi(\hat w)$ of length $2^{26}/d'=2^{20}$ over
$R_{q'}$) or to LaBRADOR's JL projection when the witness is small enough (larger bases
$b$ ⇒ smaller $\delta$ ⇒ better recursion; the sumcheck route forces small $b$ because
each round costs $O(b)$ field elements).

### 5.8 Asymptotic parameters (§4.4)

$q=\mathrm{poly}(\lambda,L)$; $k=\lambda/\log q$ ($\mathbb{F}_{q^k}$ exponential);
$d=\mathrm{poly}(\lambda)$ ($\alpha=\log\lambda$); $n_A=n_B=n_D=O(1)$;
$\omega=O(d)$; $b=O(1)$, $\delta=O(\log q)$;
$\beta=2^r\omega b$ ⇒ $\tau=O(r+\alpha)$. Witness after one iteration:
$(n_A+1)2^r\delta d+(\tau+1)2^m)\delta d+(n_A+n_B+n_D+2)\delta d
=O((\ell+\alpha)^2\cdot2^{(\ell+\alpha)/2})$ $\mathbb{Z}_q$-elements; variable count
$\ell\mapsto\frac{\ell+\alpha}2+2\log(\ell+\alpha)+O(1)\le\frac{(\ell+\alpha)}3+O(1)$... 
(after $t$ iterations: $(2/3)^t\ell+(\tfrac23)^t\alpha+O(t)\le(\tfrac23)^t\ell+2\alpha+O(t)$);
$t=O(\log\ell)$ iterations ⇒ final witness $O(\log\ell+\alpha)$ variables, sent in the clear
for $\mathrm{poly}(\ell,\lambda)$ bits. One-iteration proof size:
$(n_B+n_D+1)d+(k-1)k+(b+2)k\cdot O(\ell+\alpha)$ $\mathbb{Z}_q$-elements
$=O(\tfrac\lambda{\log\lambda}\cdot\ell+\mathrm{poly}(\lambda))$. Verifier: trace-map
check $\mathrm{poly}(\lambda)$; $O(b)=O(1)$ per round; final $\tilde M_\alpha$ evaluations
($n=n_B+n_D+3=O(1)$ of them) at $O(\sqrt{(n_A+1)2^r+(\tau+1)2^m}\delta)=\tilde O(\sqrt{2^\ell/\lambda})$
$\mathbb{F}_{q^k}$-operations each (VSBW13 dynamic programming), each
$\mathbb{F}_{q^k}$-multiplication $\tilde O(k)$ $\mathbb{Z}_q$-ops ⇒ total
$\tilde O(\sqrt{2^\ell}\cdot\lambda)$.

## 6. Soundness & Security

| Result | Statement |
|---|---|
| **Lemma 7 (weak binding)** | Two weak openings of $u$ differing in some $s_j$ ⇒ deterministic extraction of $z\in R_q^{2^{m+r}+n_A\delta2^r}$ with $[A\|B]z=0$, $0<\|z\|_\infty\le\max(2\bar\omega\bar\beta,2\bar\gamma)$ — MSIS. (Proof identical to Greyhound Lemma 2.11.) |
| **Lemma 8 (CWSS of Figure 3)** | With $(\bar\beta,\bar\omega,\bar\gamma)=(2b^k,2\omega,b)$ and $\omega<q^{1/2}/\sqrt2$: from $2^r+1$ transcripts with challenges in $\mathrm{SS}(\mathcal C,2^r,2)$ (a central vector + per-coordinate siblings), either extract a weak opening satisfying Eq. 15, or solve $\mathrm{MSIS}_{q,d,n_B,\delta2^rn_A,2b}$ or $\mathrm{MSIS}_{q,d,n_D,\delta2^r,2b}$. Extraction: $s_j:=(z^{(j)}-z^{(0)})/(c_{j,j}-c_{0,j})$; differences $\bar c_j$ have $\|\bar c_j\|_1\le2\omega$ and are invertible by Lemma 3; $\|\bar c_js_j\|_\infty\le2b^k$. |
| **Lemma 9 (Fig. 4)** | $2d$ transcripts with $\alpha_i\in\mathrm{SS}(\mathbb{F}_{q^k},1,2d)$: extract $(\bar z,\bar r)$ with $Mz=y+(X^d+1)r$ over $\mathbb{Z}_q[X]$ (degree-$2d$ interpolation), or break Com binding. |
| **Lemma 10 (Fig. 5)** | $D=\max(2d,2b-1)$ transcripts over $(\tau_0,\tau_1)$-coordinates: extract $\tilde w$ with $H_0\equiv0,H_\alpha\equiv0$, or break binding. |
| **Lemma 11 (Fig. 6)** | $D=\deg(H)+1$ transcripts per round: extract $\tilde w$ with round-polynomial identities, or break binding; composable across rounds ⇒ sumcheck special soundness. |
| **Overall** | Figure 7 = composition of Figures 4+5+6 ⇒ CWSS ⇒ knowledge soundness via Lemma 4 (FMN24), incl. Fiat–Shamir in the ROM. |

**Norm-bound methodology comparison (§1.1)**: Hachi replaces (i) subtractive sets
(polynomial-size challenge families needing repetitions) and (ii) JL random projections
(verifier linear in $\lambda\cdot md$; batching the zero-constant-coefficient checks costs
$O(\lambda/\log q)$ ring elements) with sumcheck-based exact $\ell_\infty$ range proofs over
$\mathbb{F}_{q^k}$ (Eq. 23) — this is what removes ring multiplications from the verifier.
**Soundness-error note**: every $\mathbb{F}_{q^k}$-challenge step contributes
$\deg/|\mathbb{F}_{q^k}|$ (e.g. $(2d-1)/q^k$); $k=\lambda/\log q$ makes these negligible.

## 7. Parameters & Concrete Efficiency

### 7.1 Concrete parameters (Figure 9, $\ell=30$)

| variable | value | variable | value |
|---|---|---|---|
| $\ell$ | 30 | $q$ | 4294967197 |
| $k$ | 4 | $\alpha$ | 10 |
| $d$ | 1024 | $m$ | 10 |
| $r$ | 10 | $n_A,n_B,n_D$ | 1, 1, 1 |
| $z_{max}$ ($\beta$) | 30583 | $b$ | 16 |
| $\delta$ | 8 | $\tau$ | 4 |
| $\omega$ | 16 | $c$ (#nonzero challenge coeffs) | 16 |
| next witness size | $2^{26}$ | next witness norm | 8 |

One round reduces a 30-variable $\mathbb{Z}_q$ (32-bit) polynomial to a 26-variable
$\mathbb{Z}_{16}$ (4-bit) polynomial with evaluation point over $\mathbb{F}_{q^4}$ (factor-128
witness reduction "in one shot"; $n\cdot d\ge2^{10}$ heuristic for MSIS hardness).

### 7.2 Benchmarks (Figure 8; first round only — dominates total)

| Hardware | Variables | Commit (s) | Prove (s) | Verify (ms) |
|---|---|---|---|---|
| Mac Mini M4 | 30 | 149 | 268 | 96.5 |
| Mac Mini M4 | 28 | 34.2 | 114 | 49.3 |
| Mac Mini M4 | 26 | 8.79 | 51.3 | 26.6 |
| Server (AVX-512) | 30 | 87.3 | 495 | 185 |
| Server | 28 | 21.9 | 219 | 93.7 |
| Server | 26 | 5.49 | 103 | 39.0 |
| Greyhound (Xeon SPR, AVX-512) | 30 | 132 | 41.2 | 2800 |
| Greyhound | 28 | 21.2 | 8.21 | 1150 |
| Greyhound | 26 | 4.37 | 2.03 | 492 |

First-round verification 12–29× faster than Greyhound; commitment 3–5× faster for large
polynomials; evaluation-prove times currently *exceed* Greyhound (unoptimized; SIMD planned).

### 7.3 End-to-end estimate at $\ell=30$ (§5.2, the "~55 KB proof")

- §3 transformation (over $\mathbb{F}_q$, $k=1$): $d\log q\le4$ KB; commitment $v$: 4 KB;
  sumcheck over $\mathbb{F}_{q^4}$: $26\cdot4\cdot32\cdot(16+2)$ bits ≈ **7.3 KB**.
- Greyhound handoff (§4.5, $d'=64$): transformation $12\cdot32+64\cdot32$ bits ≈ 0.3 KB;
  commitment to $\psi(\hat w)$: 4.5 KB ⇒ **4.8 KB** preparation.
- Greyhound tail on the length-$2^{20}$ short witness over $R_{q'}$ (from [NS24] Table 1,
  $N=2^{26}$ column, $\delta_0=5$): ≈ **43 KB**.
- **Total: $7.3+4.8+43\approx55.1$ KB**; total runtimes ≈ 270 s prove / 227 ms verify
  (first round 495 s? — composed with Greyhound estimates: Greyhound prover 1220 ms +
  verifier 130 ms for the $2^{24}$-element tail; Hachi first round from Fig. 8).

### 7.4 Commitment-time comparison (Figure 10, $d=64$ vs Hachi parameters)

| Variables | Folding $(r,m)$ | Base | Commit (s, $d=64$) | vs Hachi |
|---|---|---|---|---|
| 30 | 16384, 1024 | 256 | 433 | 5.0× slower |
| 28 | 8192, 512 | 256 | 71.8 | 3.3× slower |
| 26 | 4096, 256 | 256 | 18.6 | 3.4× slower |

Reason: ring multiplications fall $\propto d^2$ while NTT cost grows $d\log d$.

## 8. Implementation Notes

### 8.1 Prototype details (§5.4; github.com/georgeorourke/hachi-pcs)

- **Data layout**: coefficients as u32/u64 slices; vectors/matrices as tightly packed
  coefficient arrays (AoS); sequential (non-SIMD) decomposition; commitment matrices
  re-sampled from a seeded PRNG per invocation (overhead included in benchmarks; same
  matrix reused when shapes match).
- **Field arithmetic**: $\mathbb{F}_{q^4}$ via ark-ff (representation + multiplication);
  base-field $\mathbb{Z}_q$ multiplication via naive u64 × u64 mod-$q$ (for tfhe-ntt
  compatibility; conversion costs exceed naive reduction); optimized mixed
  base-field × extension-field products.
- **Ring arithmetic**: built on tfhe-ntt (AVX2/AVX-512 NTT). $q$ is not NTT-friendly ⇒
  "Native NTT": multiply modulo several 64-bit primes $p_i$ (CRT over $\mathbb{Z}[X]$),
  then reduce coefficients mod $q$. Safe when the small operand has ≤22-bit coefficients
  (4-bit decomposition base, $d\le2^{10}$, $q<2^{32}$); mod-$q$ reduction adds ~5% cost.
  Products over $\mathbb{Z}_q[X]$ (needed for ring switching): pad to degree $2d-1$,
  multiply over $\mathbb{Z}_q[X]/(X^{2d}+1)$, then (optimized) polynomial division by
  $X^d+1$ for residues. Keep reused values in NTT form to minimize transforms.
- **Sparse challenge multiplication**: challenges have exactly 16 nonzero ±1 coefficients
  (Fisher–Yates partial permutation + sign bits); direct sparse product for both
  $\mathbb{Z}_q[X]$ and $R_q$ — competitive with AVX-512 NTT even without SIMD.
- **Witness streaming**: witness read from a file stream in chunks of $2^{-m}$ (~0.1%) of
  the total size — moderate memory for very large witnesses; overhead (incl.
  re-decomposition) counted.

### 8.2 What an implementer must build (dependency order)

1. `lzk` ring layer: $R_q$ with $d\in\{64,1024\}$, negacyclic NTT (CRT-native or
   NTT-friendly $q$), automorphisms $\sigma_i$, trace $\mathrm{Tr}_H$, subfield basis
   $\{Z_0,Z_{k-j}\}$, packing $\psi$ + inverse (Eq. 8/9), Lemma-3 invertibility checks.
2. Gadget machinery: balanced base-$b$ decomposition ($b=16$, $\delta=8$), response gadget
   $J$ ($\tau=4$).
3. Inner/outer commitment: $A$/$B$ (and $D$) MSMs; digitized $\hat t$; sparse-challenge
   folding $z=\sum c_is_i$.
4. $\mathbb{F}_{q^4}$ arithmetic (ark-ff-equivalent in Python: sympy/numpy poly mod $\varphi$).
5. Figure 3/4/5/6/7 drivers with Fiat–Shamir transcript; CWSS-friendly challenge derivation.
6. §3 transformations: Eq. 10/11 splits, $F_i=\psi(\cdot)$, $Y$ computation, trace check
   $\mathrm{Tr}_H(Y\sigma_{-1}(v))=\frac dky$; §3.2 partial-evaluations path (with the
   **Akita F.1 fix**: replace the unsound $k>2$ shortcut by the Diamond–Posen tensor
   reduction before trusting it).
7. Recursion/handoff: §4.5 eq-splitting + $\psi$-packing to the Greyhound-shaped
   quadratic relation (or to another Hachi round); optional LaBRADOR JL tail.
8. Verifier MLE evaluations (VSBW13 DP): $\tilde M_\alpha$ at the sumcheck point in
   $\tilde O(\sqrt{2^\ell/\lambda})$ field ops.

### 8.3 Complexity summary

| Operation | Prover | Verifier | Communication |
|---|---|---|---|
| Commit ($L=2^\ell$ coeffs) | $\tilde O(L)$ ring ops (3–5× faster than Greyhound at $d=1024$) | – | $n_Bd\log q$ bits ≈ 4 KB |
| One Hachi round | $\tilde O(L)$ | $\tilde O(\sqrt{2^\ell}\lambda)$ | $O(\frac\lambda{\log\lambda}\ell+\mathrm{poly}(\lambda))$ $\mathbb{Z}_q$-elts ≈ 7.3+4+4 KB |
| Full proof ($t=O(\log\ell)$ rounds or Greyhound tail) | $\tilde O(L)$ | $\tilde O(\sqrt{2^\ell}\lambda)$ (~227 ms at $\ell=30$) | ~55 KB |
| Variable reduction | $\ell\mapsto(\tfrac23)^t\ell+2\alpha+O(t)$ | – | – |

### 8.4 Pitfalls & edge cases

1. **§3.2 base-field shortcut is unsound for $k>2$ [Akita F.1]** — the published checks
   leave a joint kernel; use the tensor reduction (row partials in
   $\mathbb{F}_{q^k}\otimes_{\mathbb{F}_q}\mathbb{F}_{q^k}$) or restrict to $k\le2$.
2. **Symbol overload**: $\alpha$ is both $\log_2 d$ and the ring-switching challenge;
   $\tau$ is both the gadget depth and the zero-check points — careful transcript naming.
3. **$\psi$ norm inflation (Lemma 6)**: $\|\psi(a)\|_\infty\le2\|a\|_\infty$ — include the
   factor 2 in all response/norm bounds after packing.
4. **Challenge invertibility**: requires $\omega<q^{1/2}/\sqrt2$ (Lemma 3 with
   $\|\bar c\|_1\le2\omega$); the concrete $\omega=16$, $c=16$ (±1 coefficients) family
   satisfies this with large margin.
5. **Small base forced by sumcheck proof size** ($O(b)$ elements/round): hurts recursion
   depth vs LaBRADOR's large-base JL route — the paper itself switches to Greyhound/
   LaBRADOR for the tail; do not assume uniform Hachi recursion is optimal.
6. **NTT-unfriendly $q$**: the CRT-native-NTT trick requires the decomposed operand to
   have ≤22-bit coefficients (no 64-bit wrap); with $b=16$, $d\le2^{10}$, $q<2^{32}$ it
   holds, but changing parameters needs re-derivation.
7. **Verifier's expensive step** is $\tilde M_\alpha$ evaluation ($O(1)$ of them, each
   $\tilde O(\sqrt{2^\ell/\lambda})$) — the square-root verifier is *not* free; Akita's
   setup offloading later removes exactly this term.
8. **Weak openings**: extraction yields $s_i=(z^{(j)}-z^{(0)})/\bar c_j$ — the extracted
   $s_i$ need not be the canonical decomposition; knowledge soundness is stated w.r.t.
   weak openings only (same as Greyhound).
9. **Witness streaming** chunks are $2^{-m}$ of the witness — tune $m$ for memory vs
   I/O; re-decomposition on the prove side is charged.
10. **First-round domination**: benchmarks report first-round only; the composed
    Greyhound tail adds ~130 ms verify / 1.2 s prove at the stated parameters.

### 8.5 Reuse from the shared core engine (`lzk`)

- `Z_q[x]/(x^n+1)` NTT rings: direct reuse (both $d=64$ and $d=1024$ instances);
  negacyclic convolution = the fold; automorphism/trace layer new but built on the same
  ring type (also needed by Akita).
- GF($q^k$) extension fields: the sumcheck field — reuse the tower/extension machinery
  (here $\mathbb{F}_{q^4}$ with an irreducible $\varphi$; Akita uses the same
  $\mathbb{F}_{q^k}$ convention).
- Ajtai/SIS commitments: the inner/outer LaBRADOR commitment is the shared two-tier
  structure used across Akita/LaBRADOR/Greyhound.
- Multilinear sumcheck: Figure 6 is a standard sumcheck round; the ring-norm sumcheck
  (Eq. 23) is the same degree-$2b$ vanishing-polynomial family as Akita's range check
  (unbalanced alphabet $\{0,\pm1..\pm(b-1)\}$, no $w(w+1)$ symmetry trick).
- Tensor/LDE encodings: the $\psi$ packing + trace identity is the $k>1$ generalization
  of coefficient packing; the Akita "evaluation trace" opening method is a direct
  descendant of Theorem 2 here.
- Fiat–Shamir transcripts: CWSS accounting (Lemma 4) shared with Akita's §3.8.


## Appendix A — Prior-work context (§1.1, in full detail)

### A.1 The split-and-fold lineage

- **Baum et al. [BBC+18]**: first sublinear interactive protocol for Eq. 1. Split: prover
  sends partial evaluations $t_i=As_i$; verifier returns short challenges
  $c_1..c_r\in\mathcal C\subset R_q$; fold: $z=\sum_ic_is_i$ (Eq. 2). Verify (Eq. 3):
  $B(t_1,\dots,t_r)=u$, $Az=\sum_ic_it_i$, $\|z\|$ short. Communication $r+m$ ring
  elements ⇒ $\tilde O(\sqrt{N\lambda})$ proofs ($N=rm$).
- **BLNS20 / AFLN24 (SLAP) / CMNW24 / KLNO24 (RoK,paper,SISsors)**: polylog$(N)$ proofs
  by giving $A$ (and companions) tensor structure, so the final message $z$ is itself
  proven recursively instead of sent.
- **Greyhound [NS24]**: commits to the $(t_i)_i$ and $z$, proves the Eq.-3 verifications
  via LaBRADOR ⇒ $\tilde O(\lambda\sqrt{N\lambda})$ verification with ~53 KB proofs.

### A.2 Exact-norm-proof methodology zoo

- **Subtractive sets** [BLNS20, AL21, ACK21, CLM23, FMN24, AFLN24, KLNO24]: families
  $\mathcal C$ where $c-c'$ has *short inverse* for distinct $c,c'$; extractor deduces
  short $\bar s_i=\bar z_i/\bar c_i$. Disadvantage: all subtractive sets are of
  polynomial size [AL21] ⇒ many repetitions for negligible error.
- **Random (JL) projections** [BL17, LNS21, LNP22, GHL22, BS23, KLNO25]:
  $J\in\mathbb{Z}^{m_r\times md}$ small random entries; $\|Js'\|\approx\|s'\|$; prover
  returns $v=Js'$; soundness $\exp(-r)$ ⇒ $r=O(\lambda)$ rows; well-formedness of $v$
  reduces to $r$ zero-constant-coefficient claims, batched with $\sum\alpha_iu_i$
  (error $1/q$ per batch ⇒ $O(\lambda/\log q)$ repetitions, each costing ring elements).
  LaBRADOR's instantiation: ~60 KB proofs at $2^{30}$, but *linear-time verifier*
  ($O(\lambda\cdot md)$). KLNO25 tensor-structured $J$: polylog verify, 40× larger proofs.
- **Sumcheck-based norm proofs**: LatticeFold [BC24] (binary NTT coefficients — but
  sumcheck over $R_q$ itself, large messages); SALSAA [KLOT25] (exact Euclidean bounds via
  $R_q$-sumchecks); Neo [NS25] (maps $R_q$-relations to $\mathbb{Z}_q$ via skew-circulant
  matrices — sumcheck over $\mathbb{Z}_q$/$\mathbb{F}_{q^k}$ directly); LatticeFold+
  [BC25] (monomial/range commitments reduced to $O(d)$ $\mathbb{Z}_q$ sumchecks, but must
  commit to $md$ ring elements rather than $m$).
  **Hachi's position**: like Neo, runs sumcheck over $\mathbb{F}_{q^k}$, but via HMZ ring
  switching integrated into the Greyhound fold (private quotient $r$, evaluation at
  $\alpha$), keeping the $m$-element commitment structure and adding the §3
  extension-field bridge.

### A.3 Why the verifier gets faster (quantified)

Greyhound's verifier cost components: (i) processing the JL projection matrix
$J$ ($O(\lambda\cdot md)$), (ii) ring multiplications in the fold checks. Hachi replaces
both: the norm check becomes the $H_0$ sumcheck (Eq. 23) whose round messages cost
$O(b)=O(1)$ $\mathbb{Z}_q$-operations, and the linear checks become the $H_\alpha$
sumcheck evaluated at $\alpha\in\mathbb{F}_{q^k}$ — all $R_q$-arithmetic disappears from
the verifier, leaving only: trace-map consistency ($\mathrm{poly}(\lambda)$), $O(1)$ per
sumcheck round, and $O(1)$ MLE evaluations at $\tilde O(\sqrt{2^\ell/\lambda})$ cost.

## Appendix B — Technical overview walkthrough (§1.3, full)

1. **Galois setup**: $\mathrm{Aut}(R)=\{\sigma_i:i\in\mathbb{Z}_{2d}^\times\}$,
   $\sigma_i:X\mapsto X^i$; $R_q^H$ fixed subring; $\mathrm{Tr}_H$ trace. Gadget
   $G_n:=I_n\otimes(1\ 2\ 4\cdots2^{\delta-1})$ (base 2 in the overview; base $b$ in
   the body), $G_n^{-1}$ binary decomposition.
2. **$\mathbb{F}_{q^k}\to R_q$ (generic)**: split the $\ell$ variables as
   $\ell=(\ell-\alpha+\kappa)+(\alpha-\kappa)$ (Eq. 4/10); group the last
   $\alpha-\kappa$ variables' monomials into subfield elements, pack with $\psi$ into
   $F_i\in R_q$ (one per outer index $i$); also pack the last variables' *point powers*
   into $v\in R_q$. Since $\mathrm{Tr}_H$ is additively homomorphic and fixes $R_q^H$:
   $\frac dky=\mathrm{Tr}_H(Y\cdot\sigma_{-1}(v))$ with
   $Y=\sum_i(x_1^{i_1}\cdots x_{\ell-\alpha+\kappa}^{i_{\ell-\alpha+\kappa}})F_i$.
   Prover sends $Y$; remaining proof: evaluation of the $(\ell-\alpha+\kappa)$-variate
   $F$ over $R_q$.
3. **$\mathbb{F}_q$-coefficient optimization**: Eq. 5 split at the first $\kappa$
   variables; send $k$ (or $k-1$) partials $y_i$; combine into a single $\mathbb{F}_{q^k}$
   claim on $f'=\sum_if_iZ^{\sum i_t2^{t-1}}$; then apply the generic route ⇒
   $(\ell-\alpha)$-variate $R_q$ claim (saves $\kappa$ variables).
4. **Evaluation as quadratic equation**: $\mu=m+r$ split (Eq. 12);
   $f(x)=b^\top(a^\top\otimes I_{2^r})f=b^\top(a^\top G_{2^m}\otimes\text{?})\dots$
   — precisely $f(x)=b^\top(a^\top(g^\top\otimes I_{2^r})\otimes I_{2^r})s$ via the
   mixed-product property, where $g^\top$ collects the gadget powers. This is exactly
   Eq. 1, provable by split-and-fold with committed messages.
5. **Ring switching + sumcheck**: lift Eq. 6 ($Mz=w$, $z$ short) to $\mathbb{Z}_q[X]$
   with quotient $r$: $\sum_kM_k(X)z_k(X)=w(X)+(X^d+1)r(X)$; commit to
   $P:=\mathrm{mle}[(z',r')]$ over $\mathbb{F}_{q^k}$ BEFORE seeing
   $\alpha\leftarrow\mathbb{F}_{q^k}$; substitute $X=\alpha$ ⇒ inner-product claims over
   $\mathbb{F}_{q^k}$; transform into sumcheck form $\sum_iP(i)Q(i)=V$; end with
   $P(r^*_1..r^*_\mu)Q(r^*_1..r^*_\mu)=y^*$; send $P(r^*_1..r^*_\mu)$ and recurse.
   Shortness of $z$ becomes a plain field range proof (Eq. 23) — vs LaBRADOR/LatticeFold+
   which prove smallness over polynomial rings.
6. **Avoiding re-decomposition**: commit directly to $(z',r')$ (coefficients of $z'$
   already small); prove $\mathrm{mle}[(z',r')](x)=y'$ using the eq-multiplicativity
   identity $\widetilde{eq}(i,x_0)\widetilde{eq}(j,x_1)=\widetilde{eq}(i\|j,x_0\|x_1)$
   (§1.3) — the same shape as Eq. 4, so the protocol recurses without committing to
   coefficients of the MLE.

## Appendix C — Detailed check inventory for a reference implementation

Per Hachi round (input: $\mu$-variate $R_q$-polynomial claim, $\mu=m+r$):

| Step | Prover work | Verifier work | Message |
|---|---|---|---|
| Fold prep (Fig. 3, msg 1) | $w_i=a^\top G_{2^m}s_i$ for $2^r$ blocks; decompose; $v=D\hat w$ | – | $v\in R_q^{n_D}$ (~4 KB) |
| Challenges | fold $z=\sum c_is_i$, check $\|z\|_\infty\le\beta$, $\hat z=J^{-1}(z)$ | sample $c\leftarrow\mathcal C^{2^r}$ (sparse, $\omega=16$) | – |
| Com$(z,r)$ (Fig. 7) | inner/outer commit of the Eq.-20 witness | – | $t$ (~4 KB) |
| $\alpha,\tau_0,\tau_1$ | – | sample from $\mathbb{F}_{q^4}$ | – |
| Sumcheck (Fig. 6/7) | $O(\ell+\alpha)$ rounds; degree-2 (linear part) and degree-$2b$... concretely $2$ (resp. $b+1=17$) coefficients per round | $O(1)$ per round | ~7.3 KB |
| Final opening | $\tilde w(a_1..a_\ell)$ | evaluate $\tilde M_\alpha$ ($\tilde O(\sqrt{2^\ell/\lambda})$); check | evaluation value |
| Recurse/handoff | §4.5 eq-split + $\psi$-pack | trace check | $(k-1)k\log q+d'\log q$ bits (~0.3 KB) + tail |

Verification-time budget at $\ell=30$ (concrete): 185 ms first round on the AVX-512
server + ~130 ms Greyhound tail + poly($\lambda$) trace checks ≈ 227–315 ms total
(paper headline 227 ms).

## Appendix D — Relationship to successor papers (for lab planning)

- **Akita** (LayerZero Labs, ePrint 2026) supersedes Hachi: it (i) fixes the §3.2
  base-field shortcut via the Diamond–Posen tensor reduction (Akita §3.7 here / [Akita
  F.1]); (ii) generalizes one fold into folding-to-completion with per-matrix ring
  dimensions, subring challenges, two opening representations, quotient-free ring
  checking (transpose convolution), 128-byte compressed commitments, exact $\ell_2$
  certificates, and **setup offloading** which removes the remaining
  $\tilde O(\sqrt{2^\ell\lambda})$ scan (the very term that dominates Hachi's verifier)
  to reach $\tilde O(N^{1/\kappa_{root}})$; (iii) reports 61–72 KB proofs and 8–33 ms
  verification vs Hachi's 55 KB / 227 ms.
- **Twist & Shout** (Setty–Thaler) is the *consumer* of this PCS family: Jolt commits to
  one-hot polynomials whose sparsity profile exactly matches the Ajtai pay-per-nonzero
  commitment used here (identity source map; the "one-hot shape" of Akita §4.1).
- Implementation sequencing for `lzk`: the Hachi slice (rings + trace/ψ + inner/outer
  commitment + ring-switched sumcheck + Eq.-20 relation) is the natural precursor to the
  Akita slice (which reuses all of it); the Twist/Shout slice sits on top of whichever
  PCS is available.

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
