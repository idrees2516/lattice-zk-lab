# Cyclo: Lightweight Lattice-based Folding via Partial Range Checks — Deep Analysis & Implementation Spec

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Cyclo: Lightweight Lattice-based Folding via Partial Range Checks |
| **Authors** | Albert Garreta (Nethermind Research), Helger Lipmaa (U. Tartu), Urmas Luhaäär (U. Tartu), Michal Osadnik (Aalto U.) |
| ** Venue / status** | Cryptology ePrint (2025); companion code `github.com/osdnk/cyclo` |
| **Local text** | `papers_txt/cyclo.txt` (2654 lines; squeezed copy `/tmp/sq/cyclo.txt`) |
| **Family** | Lattice folding (Lova → LatticeFold → LatticeFold+ → Neo → **Cyclo**) |
| **Prior art it improves on** | LatticeFold+ [BC25b] (double commitments, multiplicative norm growth), Neo [NS25] (pay-per-bit Fq→Rq encoding; ad-hoc matrix machinery), LatticeFold [BC25a] (chunk decomposition + batched grand-product range checks) |
| **Headline claims** | Folding proofs ≈ 30 KB (order of magnitude smaller than LatticeFold+’s 100 KB); extension commitment ≈ 3.5× faster than LatticeFold+’s double commitment (36.7 s vs 129.4 s, single thread); prover-time dominated by $O(La'm\log_{2b}2B)$ $R_q$-multiplications |
| **Core ideas** | (1) **Amortized norm-refreshing folding**: never norm-check the *accumulated* witness; norm grows *additively* ($+L\gamma b$ per fold) so a bounded number of folds $\ell_{\mathrm{fold}}\in[2^7,2^{20}]$ is sound; refresh with LatticeFold+ every $\ell_{\mathrm{fold}}$ rounds. (2) **Extension commitment** (vertical decomposition into a *single* linear relation, Fig. 2). (3) **Partial range check** — $\ell_\infty$ range test via sum-check on $\prod_{j=-b}^{b}(f-j)$ (Fig. 1), applied *only* to input witnesses. (4) **$\theta_k$ module-homomorphism** reformulation of Neo’s Fq→Rq translation (Fig. 4). (5) **Approximate strong sampling sets** from biased ternary distributions (heuristic, via [BL25]) enabling incomplete NTT with $q\approx 2^{50}$. |
| **Relations defined** | Principal linear relation $\Xi^{\mathrm{lin}}$ (Eq. 6); slacked relation $\Xi^{\mathrm{lin\mbox{-}slack}}$ (App. A.1); SIS-break relation $\Xi^{\mathrm{sis}}$ (App. A.2); committed hybrid R1CS $\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}$ (§7.2); R1CS over $\mathbb{F}_q$ (§2.6) |
| **Figures to transcribe** | Fig. 1 = $\Pi^b_{\mathrm{range}}$; Fig. 2 = $\Pi^{\mathrm{ext}}_{b,C}$; Fig. 3 = folding scheme Cyclo $\Pi^{\mathrm{fs}}_{b,\mathcal{D},C}$; Fig. 4 = $\Pi^{\mathrm{hyb\mbox{-}R1CS}}$ |
| **Lab role** | Third lattice-folding protocol of the lab (with LatticeFold+ and ProtogaLattice PGL-Fold); supplies the Fq-native R1CS path + partial range check + refresh-by-hybrid design that the lab’s `cyclo` module must implement |

---

## 2. Notation Table (EVERY symbol)

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter |
| $[n]$ | $\{0,\dots,n-1\}$ (counting from 0); $(i,j,k)\in[n,m,\ell]$ ranges over the product |
| $f$ | cyclotomic conductor, $f\neq 2 \bmod 4$; power-of-two case $f=2\phi$ |
| $\Phi_f(X)$ | $f$-th cyclotomic polynomial |
| $\varphi = \varphi(f)$ | Euler totient = degree of $\Phi_f$ |
| $R$ | $\mathbb{Z}[X]/\langle\Phi_f(X)\rangle$ (cyclotomic ring) |
| $R_q$ | $R/qR$ for prime $q$ |
| $R_{q^e}$ | $\mathbb{F}_{q^e}[X]/\langle\Phi_f\rangle$; $\cong(\mathbb{F}_{q^e})^{\varphi}$ (Lemma 1) |
| $e$ | extension degree; multiplicative order of $q$ mod $f$; used to amplify sum-check soundness ($q^e$) |
| $\mathbb{Z}_q$ | balanced reps. $\{-\lceil q/2\rceil+1,\dots,\lfloor q/2\rfloor\}$ |
| $q$ | prime modulus (concrete: $\approx 2^{50}$, chosen for AVX-512-IFMA 52-bit lanes) |
| $\mathrm{ct}$ | constant-term map $R\to\mathbb{Z}$ (overview-only) |
| $\mathrm{cf}$ | coefficient embedding $R\to\mathbb{Z}^{\varphi}$ w.r.t. the **powerful basis** $\mathbf{b}=(1,X,\dots,X^{\varphi-1})$ (tensor generalization for composite $f$); $\mathrm{cf}^{-1}$ inverse |
| $\mathrm{cf}^\vee$ | dual-basis embedding: $\mathrm{cf}^\vee(a)=(a^\vee_i)$ with $a^\vee_0=a_0$, $a^\vee_i=-a_{\varphi-i}$ for $i>0$ (power-of-two case); general case via $\mathbf{b}^\vee$ of Lemma 2 |
| $\mathbf{b}^\vee$ | dual basis satisfying $\mathrm{Trace}(b_i b_j)=\delta_{i,j}\bmod q$; $b^\vee_j=f^\ddagger\Phi'_f(X)X^{\varphi-j-1}$, $f\cdot f^\ddagger\equiv1\pmod q$; for $f=2^k$: $b^\vee_0=\varphi^{-1}$, $b^\vee_j=\varphi^{-1}X^{\varphi-j}$ |
| $\mathrm{Trace}$ | field trace $\mathrm{Trace}_{M/L}(x)=\sum_{\sigma\in\mathrm{Gal}(M/L)}\sigma(x)$; unindexed = to $\mathbb{Q}$; key identity: $\mathrm{Trace}(\langle \mathrm{cf}^{-1\vee}(\mathrm{tensor}(u)), w\rangle)=\mathrm{MLE}[\mathrm{cf}(w)](u)$ |
| $\|\cdot\|$, $\|\cdot\|_\infty$ | $\ell_\infty$ norm of coefficient vectors under $\mathrm{cf}$ |
| $\|c\|_{\mathrm{op}}$ | operator norm $\sup_{t\neq0}\|t\cdot c\|_\infty/\|t\|_\infty$ |
| $\gamma$, $\gamma_{\mathcal{D}}$, $\gamma_\infty$ | operator norm bound of challenge set ($\mathcal{D}$ resp. $C$); $\gamma_S:=\max_{c\in S}\|c\|_{\mathrm{op}}$ |
| $C\subseteq R_q$ | strong sampling set for challenges (concrete: subfield $\mathbb{F}_{q^2}$ embedded in $R_q$) |
| $\mathcal{D}\subseteq R_q$ | folding-challenge set: exact or $\kappa_{\mathrm{nu}}$-**approximate** strong sampling set (ternary $\{-1,0,1\}^\varphi$) |
| $\kappa_{\mathrm{nu}}$ | per-coordinate probability that $c_0-c_1$ is a non-unit (zero divisor), $c_i\leftarrow\mathcal{D}$ |
| $B$ | norm bound of input relation witnesses (concrete $2^{10}$) |
| $b$ | decomposition base/digit bound for the extension commitment (concrete $b=1$, ternary digits) |
| $\ell$ | #digits of vertical decomposition, $\ell=\lceil\log_{2b}2B\rceil$ (also overloaded as sum-check var count $\ell=\lceil\log(m\varphi)\rceil$ in range test — disambiguate per context) |
| $L$ | #input relations folded simultaneously per folding round (concrete $L=1$) |
| $\ell_{\mathrm{fold}}$ / $T$ | bounded #folding rounds before norm refresh (concrete $T=64$; paper says usable up to $2^{20}$) |
| $m$ | #ring elements in witness vector $w\in R_q^m$ (concrete $2^{20}$) |
| $\hat m$, $\tilde m$ | $m\log_{2b}2B$ — decomposed/extended witness length ($\tilde m_i=m_i\log_{2b}2B$) |
| $a$ | rank (#rows) of Ajtai matrix $A$ (concrete 13) |
| $a'$ | rank of extension-commitment matrix $\mathbf{R}$ |
| $A\in R_q^{a\times m}$ | random Ajtai matrix for input relation |
| $\mathbf{R}\in R_q^{a'\times m\ell}$ | random Ajtai matrix for extension commitment |
| $y\in R_q^{a+k+n}$ | instance vector of $\Xi^{\mathrm{lin}}$: $y=(\,y_{\mathrm{A}},y_{M_0},\dots,y_{M_{k-1}},y_{b_0},\dots,y_{b_{n-1}}\,)$ |
| $w\in R_q^m$ | witness vector |
| $v\in R_q^{m\ell}$ | vertically decomposed (extended) witness $v=(w_0^T,\dots,w_{\ell-1}^T)^T$ |
| $k$ | #matrix constraints in $\Xi^{\mathrm{lin}}$ (concrete $k=3$, emulating R1CS) — ALSO overloaded as $\theta_k$ base and LS18 splitting parameter; disambiguate by context |
| $n$ | #evaluation-claim constraints (b-challenges) in $\Xi^{\mathrm{lin}}$ (concrete $n=1$) |
| $M_i\in R_q^{m_i\times m}$ | fixed constraint matrices |
| $r_i\in R_{q^e}^{\log m_i}$ | row-batching challenges for $M_i$ (one per matrix constraint) |
| $b_i\in R_{q^e}^{\log m}$ | evaluation-claim challenges |
| $\mathrm{eq}(x,t)$ | multilinear indicator $\prod_{i=0}^{\ell-1}(x_i t_i+(x_i-1)(t_i-1))$ |
| $\mathrm{tensor}(t)$ | $\big(\mathrm{eq}(j,t)\big)_{j\in\{0,1\}^\ell}\in\mathbb{Z}_q^{2^\ell}$, lexicographic |
| $\mathrm{MLE}[u]$ | multilinear extension of $u$ over the Boolean hypercube; $\langle\mathrm{tensor}(t),u\rangle=\mathrm{MLE}[u](t)$ |
| $\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[k]},a,n,m,B}$ | principal linear relation (Eq. 6) |
| $\Xi^{\mathrm{lin\mbox{-}slack}}_{\dots,\varrho}$ | slacked variant, witness divided by short unit $s$, $\|s\|_\infty\le\varrho$ |
| $\Xi^{\mathrm{sis}}_{A,a,m,B}$ | SIS-break relation: $Aw=0$, $\|w\|\le B$, $w\neq0$ |
| $\beta$ | norm bound of accumulator witness; grows to $\beta+Lb\gamma$ per round |
| $\hat\beta,\bar\beta,\delta$ | extractor-side bounds: $\bar\beta=\hat\beta(2\gamma)^L+L\cdot 2\hat\beta(2\gamma)^{L-1}$, $\delta=(2\gamma)^L$ (slack norm) |
| $\varrho$ | norm bound of slack $s$ |
| $\theta_k:R_q\to\mathbb{F}_q$ | $\theta_k(f(X))=f(k)\bmod q$ — $\mathbb{F}_q$-**module** homomorphism (not ring hom unless $q=\Phi_f(k)$) |
| $p_c(X)$ | canonical low-norm preimage of $c\in\mathbb{F}_q$: base-$k$ digits as coefficients, $\deg<\ell_k(q)$ |
| $\ell_k(q)$ | $\lfloor\log_k q\rfloor$ #digits; either $\varphi-1$ or $\varphi$ |
| $\theta_k^{-1}$ | right inverse choosing $p_c$ per coefficient (extended to vectors) |
| $\chi$ | biased ternary distribution over $\{-1,0,1\}$: $0$ w.p. $p$, $\pm1$ w.p. $(1-p)/2$ |
| $z$ | splitting parameter of LS18 Thm 6: $z=\prod p_i^{f_i}$, $1\le f_i\le e_i$; $q\equiv1\pmod z$, $\mathrm{ord}_z(q)=f/z$ |
| $\delta_0$ | root Hermite factor for MSIS security calibration (concrete 1.0045, 128-bit) |
| $\ddagger$ | max #additions before modular reduction (60-bit overflow avoidance for Barrett) |
| $T_{\mathrm{ntt}},T_+,T_q,T_*$ | measured runtimes: forward incomplete NTT, ring add, mod-reduction, NTT-domain multiply |
| $\kappa$ | knowledge error (per theorem) |

---

## 3. Algebraic Setting

### 3.0 Position w.r.t. the LatticeFold(+) framework (why "partial")

LatticeFold and LatticeFold+ share one framework, drawn in the paper as Eq. (1):

$$
(\Xi^{\mathrm{lin}}_{\mathrm{acc}})^\ell\ \xrightarrow{\ \mathrm{norm\mbox{-}check}\ }\ (\Xi^{\mathrm{lin}}_{\mathrm{acc}})^{\ell'}\ \xrightarrow{\ \mathrm{fold}\ }\ \Xi^{\mathrm{lin}}_{\mathrm{folded}}\ \xrightarrow{\ \mathrm{decomposition}\ }\ (\Xi^{\mathrm{lin}}_{\mathrm{output}})^\ell,\qquad
\Xi^{\mathrm{lin}}_{\mathrm{input}}\ \xrightarrow{\ \mathrm{norm\mbox{-}check}\ }\ \Xi^{\mathrm{lin}}_{\mathrm{input}}{}'.
$$

Both the accumulated *and* the fresh input witness get norm-checked (extraction checkpoint), and the folded witness gets decomposed into $\ell$ digits (correctness checkpoint). Cost profile:

- **LatticeFold**: grand-product-sum range checks with tiny bound $b=2$ (cheap individually) but decomposition into $k$ chunks each committed and range-checked — prover time linear in $2^k$ after batching; the Res24 Nethermind report documents the pain.
- **LatticeFold+**: decomposition into only 2 vectors ("monomial" decomposition), but the range check is a **double commitment**: at least $\varphi$ single Ajtai commitments plus recommit — expensive over $R_q$, and the norm bound $B$ is too large for grand-product tricks. $\ell_2$-style norm checks ([BS23, KLNO24, KLNO25b]) transfer almost directly but are not exploited here.

Cyclo's **amortized norm-refreshing framework** instead runs

$$
\Xi^{\mathrm{lin}}_{\mathrm{acc}}\quad \Xi^{\mathrm{lin}}_{\mathrm{input}}\ \xrightarrow{\ \mathrm{decomposition}^{*}\ }\ \Xi^{\mathrm{lin}}_{\mathrm{input}}{}'\ \xrightarrow{\ \mathrm{norm\mbox{-}check}\ }\ \Xi^{\mathrm{lin}}_{\mathrm{input}}{}''\ \xrightarrow{\ \mathrm{fold}\ }\ \Xi^{\mathrm{lin}}_{\mathrm{output}}
$$

with the accumulated branch *never* checked. The price: norm grows additively per round so the number of rounds is capped at $\ell_{\mathrm{fold}}$ (paper: $2^7$–$2^{20}$), after which a LatticeFold+ (or similar) round refreshes the norm — a hybrid scheme, analogous to FHE bootstrapping but cheap because LatticeFold+'s linear relation is almost exactly Cyclo's accumulator relation (up to notation). The benefit: because the accumulated input needs no check at all, the decomposition+range-check pair itself can be redesigned lightweight — the **extension commitment** is only usable in this new framework.

### 3.1 Cyclotomic rings and embeddings

- Work over the **full family of cyclotomic rings** $R=\mathbb{Z}[X]/\langle\Phi_f(X)\rangle$, $f\neq 2\bmod 4$, degree $\varphi=\varphi(f)$. Concrete instantiations use power-of-two $f=2\varphi$ ($\Phi_f=X^{\varphi}+1$).
- Geometry via the coefficient embedding w.r.t. the **powerful basis**: prime-power conductor $\mathbf{b}=(1,X,\dots,X^{\varphi-1})$; composite $f=\prod f_i^{e_i}$ via tensor $\bigotimes_i(1,X^{f_i},\dots,X^{f_i^{\varphi(f_i)-1}})$. Norms are always $\ell_\infty$ on coefficient vectors.
- **Dual basis / trace trick** (Lemma 2, from [KLNO25b]): for unramified prime $q\nmid f$ there exists $\mathbf{b}^\vee$ with $\mathrm{Trace}(b_i b_j)=\delta_{i,j}\bmod q$. For $f=2^k$: $b^\vee_0=\varphi^{-1}$, $b^\vee_j=\varphi^{-1}X^{\varphi-j}$. This yields the central identity used by the range test:
  $$\mathrm{ct}(a\cdot b)=\langle \mathrm{cf}(a),\mathrm{cf}^\vee(b)\rangle\quad\text{(power-of-two case)},$$
  generalized to $\mathrm{Trace}(\langle\mathrm{cf}^{-1\vee}(\mathrm{tensor}(u)),w\rangle)=\mathrm{MLE}[\mathrm{cf}(w)](u)$ for all cyclotomics.
- **Extension ring** (Lemma 1): if $\mathrm{ord}_f(q)=e$ so $R_q\cong(\mathbb{F}_{q^e})^{\varphi/e}$, then $R_{q^e}=\mathbb{F}_{q^e}[X]/\langle\Phi_f\rangle\cong(\mathbb{F}_{q^e})^{\varphi}$. Sum-checks run over $\mathbb{F}_{q^e}$ (cheaper) or over $R_{q^e}$ = $\varphi$ parallel $\mathbb{F}_{q^e}$ sum-checks batched through NTT slots; soundness error $k\ell/q^e$ (field) resp. $(k\ell+\varphi/e)/q^e$ resp. $(k\ell+\varphi)/q^e$ (rings).
- **Ajtai commitment**: $y=Aw \bmod q$ with random $A\in R_q^{a\times m}$ is binding only for short $\|w\|\le B$ — this single fact drives the whole design (norm control).

### 3.2 The $\theta_k$ bridge between $R_q$ and $\mathbb{F}_q$ (Neo, reformulated)

$$\theta_k: R_q\to\mathbb{F}_q,\qquad \theta_k(f(X))=f(k)\bmod q .$$

- $\theta_k$ is an $\mathbb{F}_q$-**module** homomorphism when $R_q$ is viewed as the $\mathbb{F}_q$-vector space of polynomials of degree $<\varphi$ (Lemma 5). It is a ring homomorphism iff $\Phi_f(k)\equiv0\pmod q$ (Remark 4) — *not* needed here.
- Canonical low-norm preimage (Eq. 8): with $\ell_k(q)=\lfloor\log_k q\rfloor<\varphi$ and base-$k$ digits $c=\sum_{i=0}^{\ell_k(q)}c_i k^i$, $c_i\in[0,k-1]$:
  $$p_c(X)=\sum_{i=0}^{\ell_k(q)}c_i X^i\in R_q,\qquad \theta_k(p_c)=c,\qquad \|p_c\|_\infty\le k .$$
  Set $\theta_k^{-1}(c):=p_c$; extend componentwise to vectors. The base-$k$ representation of $c$ *is* $\mathrm{cf}(p_c)$ (Remark 5).
- **MLE compatibility** (Lemma 6): $\theta_k(\mathrm{MLE}[v](x))=\mathrm{MLE}[\theta_k(v)](x)$ for $v\in R_q^m$, $x\in\mathbb{F}_q^{\log m}$ — because $\mathrm{eq}(b,x)\in\mathbb{F}_q$. This is what lets the R1CS sum-check run over $\mathbb{F}_{q^e}$ while the witness stays in $R_q^m$.
- $\theta_k$ extends to $\theta_k:R_{q^e}\to\mathbb{F}_{q^e}$ ($\mathbb{F}_{q^e}$-module homomorphism) for challenge/claim handling.
- **Pay-per-bit**: committing to $z\in\mathbb{F}_q^m$ via $A\,\theta_k^{-1}(z)$ costs time *linear in the number of nonzero base-$k$ digits* of entries of $z$ (Neo’s technique, inherited): each digit contributes a shifted ring element times a scalar in $[0,k-1]$.

### 3.2.1 Worked example: $\theta_2$ bit packing (lab reference values)

Take $q=2^{50}$-ish prime, $\varphi=128$, $f=256$ ($\Phi_f=X^{128}+1$), $k=2$, so $\ell_2(q)=50$ digits per field element and one ring element packs one $\mathbb{F}_q$ element ($50<128$, plenty of room; the remaining 78 coefficients stay zero):

- $c\in\mathbb{F}_q$ with binary digits $c=\sum_{i=0}^{49}c_i2^i$, $c_i\in\{0,1\}$ maps to $p_c(X)=\sum_i c_iX^i$ with $\|p_c\|_\infty\le2$; $\theta_2(p_c)=p_c(2)=c$.
- A witness $w\in\mathbb{F}_q^m$ becomes $\theta_2^{-1}(w)\in R_q^m$ with coefficient vector in $\{0,1\}^{50m}$ — an $\ell_\infty$ norm of 2, i.e. *already below $b=1{+}1$*, which is exactly why the extension commitment can be **skipped** on the $\mathbb{F}_q$-native path ($k\le b$ rule, §2.6 of the paper).
- Ajtai commit $y=A\,\theta_2^{-1}(z)$: expand $A$ column-wise; column $i$ contributes $c_i\cdot(A\text{ col }i\text{ shifted by }X^i)$ — only nonzero bits contribute (pay-per-bit; expected 25 mults per element instead of 50).
- Soundness of the R1CS check: $(M_0\theta_2(z))\circ(M_1\theta_2(z))=M_2\theta_2(z)$ is just the original $\mathbb{F}_q$ R1CS rewritten — no ring arithmetic in the constraint at all.

### 3.2.2 Why not NTT slot packing?

The classic alternative ($R_q\cong\mathbb{F}_q^{\varphi}$ when $\Phi_f$ splits completely, CRT on roots, pack $\varphi$ field elements per ring element) fails here for four documented reasons: (1) slot packing needs many parallel relation instances, else pad-to-fill inflates complexity; (2) an $\mathbb{F}_q$-short witness gives no $R_q$-shortness guarantee — a second decomposition is still needed; (3) folding over $R_q$ wastes prover time vs $\mathbb{F}_q$; (4) complete splitting of $\Phi_f$ over-constrains $q$ and conflicts with invertibility-of-small-elements requirements ([LS18, ACX19, BS23]) and large-subfield tricks ([KLNO24]). $\theta_k$ sidesteps all four: no slots, norm controlled by digit size, heavy work in $\mathbb{F}_{q^e}$, any splitting behavior tolerated.

### 3.3 Strong sampling sets (challenge spaces)

- **Exact** (Lemma 7, from LS18 Thm 6 / Cor. 1.2): if $q\equiv 2k{+}1\pmod{4k}$ prime, $X^\varphi{+}1$ splits into $k$ irreducible degree-$\varphi/k$ factors; any $y$ with $\|y\|_\infty<\tfrac{1}{\sqrt{k}}q^{1/k}$ (or $\|y\|_2<q^{1/k}$) is invertible. Uniform $\|c\|_\infty\le\beta<\tfrac{1}{2\sqrt k}q^{1/k}$ gives an exact strong sampling set of cardinality $(2\beta+1)^\varphi$ (norm $\beta\gamma_\infty$); with Hamming weight $h$: cardinality $(2\beta+1)^h$, norm $\beta h$.
- **Approximate** (Lemma 9, heuristic from [BL25]/[ALS20]): biased ternary $\chi$ with $p=1/3$ (uniform over $\{-1,0,1\}$) per coefficient; $\mathcal{D}=\chi^\varphi$ is $\kappa_{\mathrm{nu}}$-approximate strong with
  $$\kappa_{\mathrm{nu}}\approx k/q^{\varphi/k}\quad(\text{power-of-two } \varphi\ge k>1,\ q\equiv2k{+}1\!\!\pmod{4k}).$$
  Concrete ($q\approx2^{50}$, $\varphi=128$, $k=64$ i.e. split down to $\mathbb{F}_{q^2}$): $\kappa_{\mathrm{nu}}\approx2^{-94}$. Well-spreadness bound (Lemma 8): $\epsilon=\max_{j\in[k]}\big(\tfrac1q+\tfrac{p}{q}+(1-p)\max_{t}\prod_i\cos(\tfrac{2\pi(t+1)r_j^i}{q})\big)^{\varphi/k}$.
- **Design consequence**: exact sets force small $k$ (e.g. 16 for 50-bit $q$, $\varphi=128$) ⇒ poor NTT splitting ⇒ RNS tricks; approximate sets allow split-to-$\mathbb{F}_{q^2}$ **incomplete NTT** (used in FHE practice: [CHK+21, LSS+21, HYJ+25, PMH+25]) — Cyclo benchmarks use it.
- For the $\Pi^{\mathrm{ext}}$ challenge set $C$ (norm irrelevant): use the embedded subfield $\mathbb{F}_{q^2}\subset R_q$ — a strong sampling set for free.

### 3.4 Concrete ring profile for the lab (incomplete NTT down to $\mathbb{F}_{q^2}$)

The benchmarked instantiation: $\varphi=128$, $f=256$, $q\approx2^{50}$ prime with $q\equiv2k{+}1\pmod{4k}$, $k=64$, so
$$X^{128}+1\ \equiv\ \prod_{j\in[64]}\big(X^2-r_j\big)\pmod q,\qquad R_q\cong(\mathbb{F}_{q^2})^{64}.$$

- **Incomplete NTT**: 6 levels of butterfly (128→2-point residuals), each residual a quadratic $\mathbb{F}_{q^2}=\mathbb{F}_q(r^{1/2})$; pointwise mults become $\mathbb{F}_{q^2}$ mults (3 $\mathbb{F}_q$ mults each, Karatsuba) plus twiddle handling. This is the standard FHE-practice incomplete NTT ([CHK+21, LSS+21, HYJ+25, PMH+25]) and it vectorizes on AVX-512-IFMA 52-bit lanes.
- **Why $q\approx2^{50}$ and not $2^{128}$ like LatticeFold+:** smaller lanes ⇒ IFMA acceleration and smaller proofs ($|R_q|$-sized items dominate); security is recovered by rank ($a=13$ vs 9) and degree ($\varphi=128$ vs 64) at equal $\varphi m=2^{27}$ coefficient count.
- **Challenge sets on this ring:** $\mathcal{D}$ = uniform ternary $\{-1,0,1\}^{128}$ (approximate strong, $\kappa_{\mathrm{nu}}\approx2^{-94}$, $\|\mathcal{D}\|_{\mathrm{op}}$ small); $C$ = embedded subfield $\mathbb{F}_{q^2}\subset R_q$ (exact strong — any two distinct subfield elements differ by a unit since the subfield is a field).
- **General conductors:** all protocol statements hold for any $f\neq2\bmod4$; only the dual basis ($\mathbf{b}^\vee$) and the powerful-basis tensor change. For the lab keep power-of-two first; add a composite-conductor profile only if the Gröbner/ProtogaLattice tracks need $\mathbb{Z}_{2^k}$-adjacent rings.

---

## 4. Relations (exact equations)

### 4.1 Principal linear relation (Eq. 6)

$$
\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[k]},a,n,m,B}:=\left\{\begin{array}{l}
\big((r_i)_{i\in[k]},(b_i)_{i\in[n]},y\big),\ w\ :\\[2pt]
\quad M_i\in R_q^{m_i\times m},\ r_i\in R_{q^e}^{\log m_i},\ (b_i\in R_{q^e}^{\log m})_{i\in[n]},\\
\quad A\in R_q^{a\times m},\ y=\binom{y_A}{y_{R_{q^e}}}\in R_q^{a+k+n},\ w\in R_q^m,\ \|w\|\le B,\\[4pt]
\quad \begin{pmatrix}
A\\ \mathrm{tensor}(r_0)^T M_0\\ \vdots\\ \mathrm{tensor}(r_{k-1})^T M_{k-1}\\ \mathrm{tensor}(b_0)^T\\ \vdots\\ \mathrm{tensor}(b_{n-1})^T
\end{pmatrix} w \ =\ y \bmod q
\end{array}\right\}
$$

Three constraint families: (i) random $A$ → forgery reduces to **MSIS**; (ii) $(M_i,r_i)$ → matrix/row-batching constraints emitted by the R1CS/CCS reduction; (iii) $(b_i)$ → deferred sum-check evaluation claims (appended lazily — this is the “delayed proof” pattern throughout).

### 4.2 Slacked relation (App. A.1) — for extractors

Same as $\Xi^{\mathrm{lin}}$ but witness carries a **short denominator** (slack) $s\in R_q^\times$, $\|s\|_\infty\le\varrho$:
$$\begin{pmatrix}A\\ \mathrm{tensor}(r_0)^TM_0\\ \vdots\\ \mathrm{tensor}(b_{n-1})^T\end{pmatrix}(w/s)=y\bmod q,\qquad \|w\|\le B,\ \|s\|_\infty\le\varrho .$$

### 4.3 SIS-break relation (App. A.2)

$$\Xi^{\mathrm{sis}}_{A,a,m,B}:=\{A,w:\ A\in R_q^{a\times m},\ w\in R_q^m,\ Aw=0\bmod q,\ \|w\|\le B,\ w\neq0\}.$$
($\Xi^{\mathrm{lin}}$ with $k=n=0$ and zero image.) Every knowledge-soundness proof terminates in: *either* a valid witness for the target relation *or* a $\Xi^{\mathrm{sis}}$ witness ⇒ MSIS break.

### 4.4 R1CS over $\mathbb{F}_q$ and committed hybrid R1CS

$$\Xi^{\mathrm{R1CS}}_{\mathbb{F}_q,(M_i)_{i\in[3]},a,m,\ell,B}:=\Big\{x,w:\ x\in\mathbb{F}_q^{\ell},\ w\in\mathbb{F}_q^{m-\ell-1},\ M_i\in\mathbb{F}_q^{m\times m},\ z=(x,1,w),\ (M_0z)\circ(M_1z)=M_2z\Big\}
$$

$$
\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}_{R_q,\theta_k,A,(M_i)_{i\in[3]},a,m,\ell,B}:=\left\{\begin{array}{l}
(x,y),w:\ x\in R_q^{\ell},\ y\in R_q^{a},\ w\in R_q^{m-\ell-1},\\
\quad M_i\in\mathbb{F}_q^{m\times m},\ A\in R_q^{a\times m},\ z=(x,1,w)\in R_q^{m},\\
\quad (M_0\cdot\theta_k(z))\circ(M_1\cdot\theta_k(z))-M_2\cdot\theta_k(z)=0,\\
\quad Az=y,\ \ \|z\|_\infty\le k
\end{array}\right\}
$$

The R1CS constraint itself is **never lifted to $R_q$** — it is evaluated on $\theta_k(z)\in\mathbb{F}_q^m$; only the *commitment* lives over $R_q$. Theorem 4: $(x,w)\in\Xi^{\mathrm{R1CS}}$ iff $((\theta_k^{-1}(x),Az'),\theta_k^{-1}(w))\in\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}$ for $z'=(\theta_k^{-1}(x),1,\theta_k^{-1}(w))$; base-$k$ digits of $w_i$ equal $\mathrm{cf}(w'_i)$ (bit-size preserving). CCS generalizes verbatim (Remark 6).

### 4.5 Accumulator family and norm-growth bookkeeping

- $\Xi^{\mathrm{acc},\beta}_{\mathrm{lin}}:=\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',1,m\log_{2b}2B,\beta}$; initialized to all-zero instance/witness.
- **Folding (completeness) direction**: $\|v+\sum_j s_jv_j\|_\infty\le\beta+Lb\gamma$ — **additive** per round (challenge only multiplies the *range-checked, b-bounded extended* inputs). Contrast: LatticeFold+’s folded pair forces multiplicative growth.
- **Extraction direction**: input witnesses exactly bounded by $b$ (range check); accumulator extraction adds $L\gamma b$; extractor slack norm $\delta=(2\gamma)^L$, witness norm $\bar\beta=\hat\beta(2\gamma)^L+L\cdot2\hat\beta(2\gamma)^{L-1}$.
- With $B=2^{10}$, $b=1$, $\gamma=\varphi$-sized small: $T=2^6$ rounds keep $\beta$ within MSIS budget at $a=13$; $T$ raised to $2^{10}$ ($2^{20}$) costs only ≈39.7 KB (41.7 KB) of proof.

### 4.6 Norm ledger, worked over rounds

With $L=1$, $b=1$, folding challenge norm $\gamma$ per round and initial accumulator $\beta_0=0$ (zero witness):

| Round $t$ | Completeness bound $\beta_t=\beta_{t-1}+Lb\gamma$ | Extraction accumulator bound | Input-side bound |
|---|---|---|---|
| 1 | $b\gamma$ | $b$ (exact, range-checked) | $b$ (exact) |
| 2 | $2b\gamma$ | $\le\beta_1+\gamma b$ | $b$ |
| $t$ | $t\,b\gamma$ | $\le\beta_{t-1}+\gamma b\le t\,b\gamma$ | $b$ |
| $T$ | $Tb\gamma$ | $\le Tb\gamma$; with slack machinery $\bar\beta_T=\hat\beta(2\gamma)^L+L\cdot2\hat\beta(2\gamma)^{L-1}$ | $b$ |

Contrast with LatticeFold+ where each round multiplies the pair-structured accumulator norm by $\gamma$ (hence $\gamma^T$ after $T$ rounds) — the additive-vs-multiplicative distinction is the entire architecture. SIS ranks are then selected against $\max(B,\,2\bar\beta\delta)$ at the terminal round, which is why raising $T$ from $2^6$ to $2^{20}$ moves proof size by only ~10 KB (logarithmic) while ranks stay nearly unchanged.

---

## 5. Protocols (full numbered transcriptions)

### 5.0 Dependency graph

```
R1CS/CCS over F_q
   |  (1) theta_k^{-1} digit packing + Ajtai commit          [Thm 4: equivalence]
   v
Xi^{com-hyb-R1CS}
   |  (2) Pi^{hyb-R1CS}: sum-check over F_{q^e}, d_i claims   [Fig. 4, Thm 5]
   v
Xi^{lin} (k=3 matrices, n=1 eval claim)
   |  (3) Pi^{ext}: vertical base-(2b) decomposition          [Fig. 2, Thm 2]
   |      (SKIP on the F_q-native path when k <= b)
   v
Xi^{lin} (k+1 matrices, m -> m*log_{2b}2B, bound b)
   |  (4) Pi^{range}: l_infty range check via sum-check       [Fig. 1, Thm 1]
   v
Xi^{lin} (n+1 eval claims, bound b)
   |  (5) unification sum-check over R_{q^e} NTT slots        [Fig. 3 step 4]
   |  (6) short-challenge random linear combination            [Fig. 3 steps 5-6, Thm 3]
   v
Xi^{lin}_{acc, beta+Lb*gamma}   --- repeat <= T rounds ---> refresh via LatticeFold+
```

### 5.1 Figure 1 — Range test $\Pi^b_{\mathrm{range}}$

**Statement.** $((r_i)_{i\in[k]},(b_i)_{i\in[n]},y),w\in\Xi^{\mathrm{lin}}_{n,b}$ (i.e. prove $\|w\|_\infty\le b$ for the committed input witness) → output $\Xi^{\mathrm{lin}}_{n+1,b}$ (one appended evaluation claim).

Common data: $\ell=\lceil\log(m\varphi)\rceil$; $\mathrm{tensor}(\cdot)\in\mathbb{F}_{q^e}^{m\varphi}$ s.t. $\langle\mathrm{tensor}(z),\mathrm{cf}(w)\rangle=\mathrm{MLE}[\mathrm{cf}(w)](z)$.

1. **P:** define $f:=\mathrm{MLE}[\mathrm{cf}(w)]\in\mathbb{Z}_q[X_0,\dots,X_{\ell-1}]$.
2. **V:** sample $\eta=(\eta_0,\dots,\eta_{\ell-1})\leftarrow\mathbb{F}_{q^e}$; set separator $\omega(X):=\mathrm{eq}(X;\eta)$.
3. **P:** set $\hat f(X):=\prod_{j=-b}^{b}(f(X)-j)\cdot\omega(X)\in\mathbb{F}_{q^e}[X_0,\dots,X_{\ell-1}]$.
4. **P↔V:** sum-check over $\mathbb{F}_{q^e}$ reducing $\sum_{z\in\{0,1\}^\ell}\hat f(z)\stackrel?=0$ to $\hat f(u)\stackrel?=s$, challenge vector $u$ from V, leaf claim $s\in\mathbb{F}_{q^e}$ sent by P.
5. **P:** compute $u':=\mathrm{cf}^{-1\vee}(\mathrm{tensor}(u))\in R_{q^e}^m$ and $t̃:=\langle u',w\rangle\in R_{q^e}$; **send $t̃$** (1 ring element).
6. **V:** compute $t:=\mathrm{Trace}(t̃)\in\mathbb{F}_{q^e}$ and check
   $$s\stackrel?=\\ \omega(u)\cdot\prod_{j=-b}^{b}(t-j).$$
   (Correct because $\mathrm{Trace}(t̃)=\mathrm{MLE}[\mathrm{cf}(w)](u)=f(u)$ by the dual-basis trace identity.)
7. **Output (P and V):** $\big((r_i)_{i\in[k]},((b_i)_{i\in[n]},u'),t̃,w\big)\in\Xi^{\mathrm{lin}}_{n+1,b}$ — i.e. instance gains one $b$-challenge (namely $u'$) and one $R_{q^e}$ image entry $t̃$; the proof that $t̃=\langle u',w\rangle$ is *deferred* into the relation itself.

**Communication:** $1$ $R_{q^e}$ element $t̃$ + $(2b{+}2)\ell+1$ $\mathbb{F}_{q^e}$ elements (degree-$2b{+}2$ unis, constant term skipped).
**Knowledge error (Thm 1):** $\kappa=\ell(2b+2)/q^e$; extractor: rewind for $(w^*,s^*),(w',s')$; if $w^*/s^*\neq w'/s'$ output $\Xi^{\mathrm{sis}}$ witness $A(w^*s'-w's^*)$ with norm $\le2\tilde b\gamma\varrho$; else Schwartz–Zippel on multilinear $f$ + degree $D\le\ell(2b+2)$.

**Completeness walk-through (implement this as the reference):** for $\mathrm{cf}(w)\in[-b,b]^{m\varphi}$ and any $z\in\{0,1\}^\ell$, one factor of $\prod_{j=-b}^{b}(f(z)-j)$ vanishes, so $\hat f(z)=\omega(z)\cdot0=0$ and the sum-check total is $0$. At the leaf, $t=\mathrm{Trace}(t̃)=f(u)$ by the dual-basis trace identity (Lemma 2), so $\omega(u)\prod_j(t-j)=\hat f(u)=s$. The degree bookkeeping: $\deg_{X_i}\hat f\le(2b{+}1)+1=2b+2$ (product degree from $2b{+}1$ factors plus $\omega$'s degree 1), hence $(2b{+}2)$ coefficients per round and $D\le\ell(2b{+}2)$ for the final Schwartz–Zippel.

### 5.2 Figure 2 — Extension commitment $\Pi^{\mathrm{ext}}_{b,C}$

**Statement.** $((r_i)_{i\in[k]},(b_i)_{i\in[n]},y),w\in\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[k]},a,n,m,B}$ → $\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',n,m\ell,b}$. Parameters: $\ell=\lceil\log_{2b}2B\rceil$, $\ell_C=\lceil\log a\rceil$, challenge set $C\subseteq R_q$ strong sampling (norm-irrelevant).

1. **P:** split the witness vertically into base-$2b$ digits with sign:
   $v^T=(w_0^T,\dots,w_{\ell-1}^T)$, $\ w=\sum_{i=0}^{\ell-1}w_i(2b)^i$, $\ \|w_i\|_\infty\le b$.
2. **P:** **send extended commitment** $t:=\mathbf{R}v\in R_q^{a'}$.
3. **V:** sample $\hat c\leftarrow C^{\ell_C}$; define $c:=\mathrm{tensor}(\hat c)\in R_{q^e}^{a}$.
4. **P and V (public derivation):** for $i\in[k]$:
   (i) $\tilde b_i:=\big((2b)^0,(2b)^1,\dots,(2b)^{\ell-1}\big)\otimes b_i^T\in R_{q^e}^{\lceil\log m\rceil+\ell}$ — the old evaluation challenge, **digit-extended**;
   (ii) $\tilde M_i:=\big((2b)^0,(2b)^1,\dots,(2b)^{\ell-1}\big)\otimes M_i\in R_q^{m_i\times m\ell}$;
   (iii) $\tilde M_k:=\big((2b)^0,\dots,(2b)^{\ell-1}\big)\otimes A\in R_q^{a\times m\ell}$ — the Ajtai block becomes the $(k{+}1)$-th matrix constraint.
5. **Output:** augmented instance
   $$\big(((r_i)_{i\in[k]},c),(\tilde b_i)_{i\in[n]},\tilde y\big),\ v\in\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',n,m\ell,b},$$
   $$\tilde y:=\big(t^T,\ y_a,\dots,y_{a+k-1},\ \langle c,(y_0,\dots,y_{a-1})\rangle,\ y_{a+k},\dots,y_{a+k+n-1}\big).$$
   The single new $R_{q^e}$ entry $\langle c,(y_0,\dots,y_{a-1})\rangle$ **folds the old Ajtai images into one check**; its correctness for a genuinely decomposed $v$ follows from
   $$\big((2b)^0,(2b)^1,\dots,(2b)^{\ell-1}\big)\otimes A\Big)v=\Big(\sum_i(2b)^iA w_i\Big)=Aw=y .$$

**Communication:** $a'$ elements of $R_q$ (just $t$).
**Knowledge error (Thm 2):** $\ell_C/|C|$; extractor reconstructs $w^*=\sum_i v^*_i(2b)^i$, checks $Aw^*=y$; else fork on $\hat c$ and apply the **ring zero bound** (Lemma 3, [BCPS18] Thm 4.2: $\Pr[f(r)=0]\le\deg f/|C|$ over strong sampling sets) to the degree-$\ell_C$ multilinear polynomial in $\hat c$; if $v^*\neq v'$ get $\Xi^{\mathrm{sis}}_{\mathbf{R},a',m\ell,2b}$.
**Cost:** $a'm\ell=a'm\log_{2b}2B$ ring multiplications — the dominant prover cost of Cyclo; $b$ trades extension-commitment cost against range-check cost (linear in $2b{+}2$).

### 5.3 Figure 3 — Folding scheme Cyclo $\Pi^{\mathrm{fs}}_{b,\mathcal{D},C}$

**Statement.**
$$\Pi^{\mathrm{fs}}_{b,\mathcal{D},C}:\ \ \big(((r_i)_{i\in[k]},b,y),v\in\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',1,m\log_{2b}2B,\beta}\big)\times\Big(\big((r'_{i,j})_{i\in[k]},(b'_{i,j})_{i\in[n]},y'_j\big),w'_j\Big)_{j\in[L]}\in(\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[k]},a',n,m,B})^L\ \longrightarrow\ \Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',1,m\log_{2b}2B,\ \beta+Lb\gamma}.$$

1. **P↔V, extension:** for each $j\in[L]$, run $\Pi^{\mathrm{ext}}_{b,C}$ (Fig. 2):
   $((r''_{i,j})_{i\in[k+1]},(b'_{i,j})_{i\in[n]},t'_j),v'_j\leftarrow\Pi^{\mathrm{ext}}\big(((r'_{i,j})_{i\in[k]},(b'_{i,j})_{i\in[n]},y'_j),w'_j\big)$.
2. **P↔V, range:** for each $j\in[L]$, run $\Pi^b_{\mathrm{range}}$ (Fig. 1) on the extended instance:
   $((r''_{i,j})_{i\in[k+1]},(b''_{i,j})_{i\in[n+1]},t'_j),v'_j\leftarrow\Pi^b_{\mathrm{range}}(\dots)$ — now each input witness is *certified* $\|v'_j\|_\infty\le b$.
3. **V:** sample $d\leftarrow\mathbb{F}_{q^e}^{\lceil\log\varphi(2+k+L(2+n+k))\rceil}$ (batching randomness).
4. **Unification sum-check.** Let $\tilde m:=m\log_{2b}2B$, $\tilde m_i:=m_i\log_{2b}2B$. Express the linear equalities of all $(L{+}1)$ instances as sum-check claims:
   - (a) $\sum_{z\in\{0,1\}^{\log\tilde m_i}}\mathrm{MLE}[\tilde M_i v_j](z)\,\mathrm{eq}(z;r''_{i,j})=t'_{j,a'+i}$, for $i\in[k{+}1]$, $j\in[L]$;
   - (b) $\sum_z\mathrm{MLE}[\tilde M_i v](z)\,\mathrm{eq}(z;\tilde r_i)=y'_{a'+i}$, for $i\in[k{+}1]$ (accumulator);
   - (c) $\sum_z\mathrm{MLE}[v_j](z)\,\mathrm{eq}(z;b'_{i,j})=t'_{j,a'+k+1+i}$, for $i\in[n{+}1]$, $j\in[L]$;
   - (d) $\sum_z\mathrm{MLE}[v](z)\,\mathrm{eq}(z;b)=y'_{a'+k+1}$ (accumulator).
   Batch all claims with $d$ and run **one** sum-check over the NTT slots of $R_{q^e}$ (equivalently $\mathbb{F}_{q^e}$-parallel), reducing to claims over a **shared random point**, yielding
   $((\tilde r_i)_{i\in[k]},\tilde r,\tilde y),v\in\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]}}$ and $((\tilde r_i)_{i\in[k]},\tilde e'_j),v_j\in\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[k]}}$ for $j\in[L]$.
   P sends the new evaluation claims $\tilde y[a',|\tilde y|]$ and $\tilde y'_j[a',|\tilde y'_j|]$ (over $R_{q^e}$).
   *(Footnote: batching sum-checks with different variable counts pads shorter functions with unused auxiliary variables and erases the corresponding coordinates from the output point.)*
5. **V:** send short folding challenge $s\leftarrow\mathcal{D}^L$ (coordinate-wise independent via domain-separated ROM tags).
6. **Output (P and V):**
   $$\Big(\big((\tilde r_i)_{i\in[k]},\tilde r,\ \tilde y+\textstyle\sum_{j\in[L]}s_j\tilde y'_j\big),\ v+\sum_{j\in[L]}s_jv_j\Big)\in\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',1,\tilde m,\beta+Lb\gamma}.$$
   **The accumulator witness is never multiplied by the challenge** — only the $b$-bounded inputs are; this is the source of additive norm growth.

**Communication (Thm 3):** $La'+L$ elements in $R_q$; $(k{+}2)\cdot(L{+}1)$ elements in $R_{q^e}$; $2\lceil\log m\varphi(\log_{2b}2B)\rceil$ $\mathbb{F}_{q^e}$ elements (unification sum-check, degree 2); $L(2b{+}2)\lceil\log(m\varphi(\log_{2b}2B))\rceil$ $\mathbb{F}_{q^e}$ elements (range sum-checks). **Remark 2:** merging the $L$ range sum-checks into 2 total cuts the last term to $(2b{+}2)\lceil\log(\cdot)\rceil$ with negligible soundness impact — **implement the merged variant**.

### 5.4 Figure 4 — Reduction $\Pi^{\mathrm{hyb\mbox{-}R1CS}}$ (committed hybrid R1CS → principal linear relation)

**Statement.** $((x\in R_q^{\ell},y\in R_q^{a}),w\in R_q^{m-\ell-1})\in\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}_{R_q,\theta_k,A,(M_i)_{i\in[3]},a,m,\ell,B}$ → $((r'_i\in R_{q^e}^{3\times\log m})_{i\in[1]},b'\in R_{q^e}^{\log m}),y'\in R_q^{a}\times R_{q^e}^{4},w'\in R_q^{m})\in\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[3]},a,1,m,B}$.

1. **V:** sample $r\in\mathbb{F}_{q^e}^{\log m}$, send to P.
2. **Common:** $w'=(x,1,w)\in R_q^m$; $\theta_k(w')\in\mathbb{F}_q^m$; define over $\mathbb{F}_q$, variables $Y=(Y_0,\dots,Y_{\log m-1})$:
   $$Q(Y)=Q_0(Y)Q_1(Y)-Q_2(Y),\qquad Q_i(Y)=\sum_{b'\in\{0,1\}^{\log m}}\mathrm{MLE}[M_i](Y,b')\,\mathrm{MLE}[\theta_k(w')](b').$$
3. **P↔V:** sum-check **over $\mathbb{F}_{q^e}$** (crucially *not* $R_{q^e}$): reduce $\sum_{b\in\{0,1\}^{\log m}}Q(b)\mathrm{eq}(b;r)\stackrel?=0$ to $Q(u)\mathrm{eq}(u,r)=c$ for challenges $u\in\mathbb{F}_{q^e}^{\log m}$ and computed $c\in\mathbb{F}_{q^e}$.
4. **P:** compute $d_i=\sum_{b'\in\{0,1\}^{\log m}}\mathrm{MLE}[M_i](u,b')\mathrm{MLE}[w'](b')\in R_{q^e}$ for $i\in[3]$; **send $d_0,d_1,d_2$** (3 ring elements).
5. **V:** assert $\big(\theta_k(d_0)\theta_k(d_1)-\theta_k(d_2)\big)\mathrm{eq}(u;r)=c$.
   (Soundness bridge: by Lemma 6, $\theta_k(d_i)=Q_i(u)$, so the check pins the *field-side* products to the sum-check leaf.)
6. **V:** sample $v\in C^{\log(\ell)+1}$, send to P (prefix-pinning point).
7. **P and V:** compute $e=\mathrm{MLE}[(x,1)](v)\in R_{q^e}$; output
   $$r'_i=(u,u,u)\in R_{q^e}^{3\times\log m},\quad b'=(v,0)\in R_{q^e}^{\log m},\quad y'=(y,d_0,d_1,d_2,e),\quad w'=(x,1,w),$$
   with relation $\Xi^{\mathrm{lin}}_{A,(M_i)_{i\in[3]},a,1,m,B}$ — the public prefix $(x,1)$ is *dropped* from the relation and its presence is enforced by the appended evaluation claim $\mathrm{tensor}(b')^Tw'=\mathrm{MLE}[(x,1,w)](v,0)=e$ (Schwartz–Zippel over $C$).

**Communication (Thm 5):** $3\log(m)$ $\mathbb{F}_{q^e}$ elements + $3$ $R_q$ elements.
**Knowledge error:** $\kappa=\log(\ell)+1/|C|+4\log(m)/q^e$.

**Design note — why the $d_i$ are published ring-side:** the prover *could* publish the field-side $Q_i(u)$ values and let the verifier multiply them in $\mathbb{F}_{q^e}$; instead it publishes $d_i=\sum_{b'}\mathrm{MLE}[M_i](u,b')\mathrm{MLE}[w'](b')\in R_{q^e}$ and the verifier checks $(\theta_k(d_0)\theta_k(d_1)-\theta_k(d_2))\mathrm{eq}(u;r)=c$. Ring-side $d_i$ make the three claims directly appendable to $\Xi^{\mathrm{lin}}$ as matrix-constraint images $\mathrm{tensor}(u)^TM_iw'=d_i$ (Step 7), which is what the folding scheme consumes; the field-side check pins them to the sum-check leaf. Lemma 6 guarantees $\theta_k(d_i)=Q_i(u)$, closing the loop.

### 5.5 Full pipeline (R1CS over $\mathbb{F}_q$ → IVC-style folding)

1. Encode $z=(x,1,w)$: $z'=\theta_k^{-1}(z)$ (base-$k$ digits as coefficients; pay-per-bit Ajtai commit $y=Az'$).
2. $\Pi^{\mathrm{hyb\mbox{-}R1CS}}$ (Fig. 4) → principal linear instance ($k=3$ matrices, $n=1$ evaluation claim).
3. **Skip $\Pi^{\mathrm{ext}}$** if $k\le b$ (norm already $\le b$; the $F_q$-native path) — otherwise run it.
4. $\Pi^b_{\mathrm{range}}$ on the (extended) input witness.
5. Unification sum-check + short-challenge fold into accumulator (Fig. 3 steps 3–6).
6. Repeat up to $\ell_{\mathrm{fold}}$ rounds; then optionally hand the accumulator to **LatticeFold+ as a norm-refresh/merge step** (hybrid scheme; dual role: merge accumulators + refresh norm). IVC follows generically from folding; **PCD is not directly resolved** (accumulator type/parameters differ from input relation and accumulator plays a special unchallenged role) — sequential branches + separate merging protocol is the envisioned deployment.

### 5.6 Communication inventory per folding round (concrete params)

With $L=1$, $k=3$, $n=1$, $a'=a=13$, $e=2$, $b=1$, $\varphi=128$, $m=2^{20}$, $B=2^{10}$, $\log_{2b}2B=11$, $\tilde m=m\cdot11$, $|R_q|=50$ bits, $|\mathbb{F}_{q^e}|=100$ bits:

| Item | Count | Size |
|---|---|---|
| Extension commitment $t$ | $a'=13$ $R_q$ | 13·50/8 ≈ 81 B |
| Range $t̃$ | $L=1$ $R_{q^e}$ | 100/8 ≈ 13 B |
| Range sum-check unis | $(2b{+}2)\cdot\lceil\log(\tilde m\varphi)\rceil=4\cdot\lceil\log(2^{20}\cdot11\cdot128)\rceil\approx4\cdot31$ $\mathbb{F}_{q^e}$ | ≈155 B |
| Unification unis | $2\lceil\log(m\varphi\log_{2b}2B)\rceil\approx2\cdot31$ $\mathbb{F}_{q^e}$ | ≈78 B |
| $R_{q^e}$ claims | $(k{+}2)(L{+}1)=10$ | ≈125 B |
| **Total** | | **≈ 0.4 KB/round + 30 KB terminal** ⇒ 31.8 KB at $T=64$ |

(The terminal cost is the final opening/decider proof for the accumulated relation — the sum-check claims that were deferred throughout get discharged once; the per-round costs above are what the streaming prover emits each step.)

---

## 6. Soundness & Security

### 6.1 Theorem statements

- **Theorem 1 (KS of range).** $\Pi^b_{\mathrm{range}}$: $\Xi^{\mathrm{lin}}_{A,a,n,b}\to\Xi^{\mathrm{lin}}_{A,a,n+1,b}$ perfectly correct; knowledge sound with $\kappa=\ell(2b+2)/q^e$, $\ell=\lceil\log(m\varphi)\rceil$:
  $$\Xi^{\mathrm{lin}}_{A,a,n,b}\ \cup\ \Xi^{\mathrm{sis}}_{\hat b=2\tilde b\gamma\varrho}\ \leftarrow\ \Xi^{\mathrm{lin\mbox{-}slack}}_{A,n+1,\tilde b,\varrho}.$$
- **Theorem 2 (KS of extension commitment).** $\Pi^{\mathrm{ext}}_{b,C}$: $\Xi^{\mathrm{lin}}_{A,(M_i),a,n,m,B}\to\Xi^{\mathrm{lin}}_{\mathbf{R},(\tilde M_i)_{i\in[k+1]},a',n,m\ell,b}$ perfectly correct; knowledge error $\ell_C/|C|$, $\ell_C=\lceil\log_2 a\rceil$; soundness target $\Xi^{\mathrm{lin}}_{A,(M_i),a,n,m,B}\cup\Xi^{\mathrm{sis}}_{\mathbf{R},a',m\ell,2b}\leftarrow\Xi^{\mathrm{lin}}_{\mathbf{R},a',n,m\ell,b}$.
- **Theorem 3 (KS of Cyclo folding).** Perfectly correct $\Xi^{\mathrm{lin}}_{\mathrm{acc},\beta}\times(\Xi^{\mathrm{lin}}_{a,n,m,B})^L\to\Xi^{\mathrm{lin}}_{\mathrm{acc},\beta+Lb\gamma}$; knowledge sound with
  $$\kappa\ \le\ \underbrace{L/|\mathcal{D}|}_{\kappa_a\ \text{(unit part)}}+\underbrace{(\ell_0+\ell_1)/q^e}_{\kappa_b}+\underbrace{L\ell_1(2b+2)/q^e}_{\kappa_c}+\underbrace{L\ell_C/|C|}_{\kappa_d}+\underbrace{L\kappa_{\mathrm{nu}}}_{\text{non-units}},$$
  $\ell_0=\lceil\log\varphi(2+k+L(2+n+k))\rceil$, $\ell_1=\lceil\log(m\varphi\log_{2b}2B)\rceil$, $\ell_C=\lceil\log a\rceil$; target
  $$\Xi^{\mathrm{sis}}_{\mathbf{R},2\bar\beta\delta}\ \cup\ \Xi^{\mathrm{lin}}_{\mathrm{acc},\hat\beta+Lb\gamma}\times(\Xi^{\mathrm{lin}}_{a,n,m,B})^L\ \leftarrow\ \Xi^{\mathrm{lin}}_{\mathrm{acc},\hat\beta},\qquad\bar\beta=\hat\beta(2\gamma)^L+L\cdot2\hat\beta(2\gamma)^{L-1},\ \delta=(2\gamma)^L .$$
- **Theorem 4 (R1CS ↔ hybrid).** Equivalence of $\Xi^{\mathrm{R1CS}}$ and $\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}$ instances via $\theta_k^{-1}$, assuming MSIS-hard $(A,a,B)$ and $2k<B$.
- **Theorem 5 (KS of hyb-R1CS reduction).** $\kappa=\log(\ell)+1/|C|+4\log(m)/q^e$; target $\Xi^{\mathrm{lin}}_{A,(M_i),a,n,m,B}\cup\Xi^{\mathrm{sis}}_{A,a,m,2B'}\leftarrow\Xi^{\mathrm{com\mbox{-}hyb\mbox{-}R1CS}}$.
- **Theorem 6 (LS18).** Splitting $+$ invertibility of small elements (basis of exact strong sampling sets).
- **Lemmas.** L1: $R_{q^e}\cong(\mathbb{F}_{q^e})^\varphi$. L2: dual basis exists mod $q$. L3 (BCPS18): ring zero bound $\Pr[f(r)=0]\le\deg f/|C|$ over strong sampling sets. L4: coordinate-wise forking for CWSS (below). L5–L6: $\theta_k$ module hom + MLE commutation. L7: exact strong sampling set. L8–L9: approximate sets (biased ternary).

### 6.2 Extractor logic (Theorem 3, four stages)

- **(a) Folding — coordinate-wise forking (Lemma 4).** Sample $s\in\mathcal{D}^L$; rewind **one coordinate at a time**, reprogramming (ROM, domain-separated tags) only the $i$-th query to resample $s'_i\leftarrow\mathcal{D}$; get $L{+}1$ accepting transcripts w.p. $\ge\epsilon-L/|\mathcal{D}|$. Differences $\Delta_i=s'_i-s_i$; except w.p. $L/|\mathcal{D}|+L\kappa_{\mathrm{nu}}$ all $\Delta_i$ are units with $\|\Delta_i\|_{\mathrm{op}}\le2\gamma$. Then per input $j$: $\big((\tilde r_i)_i,\tilde e'_j\big),(ṽ_j{}^*,\Delta_j)\in\Xi^{\mathrm{lin\mbox{-}slack}}_{2\hat\beta,2\gamma}$ via $ṽ_j{}^*=(ṽ^{(j)}-ṽ^{(L)})/\Delta_j$; accumulator witness reconstructed as
  $$v^*=\frac{ṽ^{(L)}}{\Delta^*}+\sum_{i\in[L]}\frac{ṽ_i^*}{\Delta_i},\qquad \Delta^*=\prod_{i\in[L]}\Delta_i,\qquad\|v^*\|\le\bar\beta,\ \|\Delta^*\|_{\mathrm{op}}\le\delta .$$
- **(b) Sum-check stage.** Fork for fresh challenges on $(ṽ_j{}^*,\hat s_j^*)$ / $(v^*,s^*)$; differing quotients ⇒ $R(ṽ^*s'-ṽ's^*)=0$ ⇒ $\Xi^{\mathrm{sis}}_{\mathbf{R},2\bar\beta\delta}$; equal quotients ⇒ Schwartz–Zippel/sum-check error $(\ell_0+\ell_1)/q^e$.
- **(c) Range stage.** Run $\Pi^b_{\mathrm{range}}$ extractor per $j$: valid $\|w_j^*\|\le b$ witnesses or SIS break; error $L\ell_1(2b+1)/q^e$ (union bound). Accumulator: $w^*=v^*-\sum_j w_j^*\in\Xi^{\mathrm{lin}}_{\hat\beta+Lb\gamma}$.
- **(d) Extension stage.** Run $\Pi^{\mathrm{ext}}$ extractor per $j$: recover $\hat w_j\in\Xi^{\mathrm{lin}}_{a,n,m,B}$ or $\Xi^{\mathrm{sis}}_{\mathbf{R},2\bar\beta\delta}$; error $L\ell_C/|C|$.
- All extractors are expected-polynomial-time by standard forking ($1/\epsilon$ rewinds); total error by union bound.

### 6.3 Security anchors

- **MSIS hardness** of $A$ (rank $a$) resp. $\mathbf{R}$ (rank $a'$) with the *terminal* norm bounds $B$ resp. $2\bar\beta\delta$ / $2b$; calibrated with LatticeEstimator, root Hermite factor $\delta_0=1.0045$ (128-bit), BKZ, $\ell_\infty\to\ell_2$ translation.
- **Fiat–Shamir** in ROM: verifier challenges ($\eta,u,d,s,v,r$) derived from hashes; coordinate independence of $s$ via domain separation (Lemma 4 requirement).
- Statistical vs. computational separation: security level $\lambda$ ⇒ ranks $a,a'$ (≈linear); soundness $\kappa$ ⇒ $q^e\approx1/\kappa$ (increase $e$ or $q$; homogenization sum-check cost linear in $e$).

### 6.4 Fiat–Shamir transcript layout (implementation contract)

One folding round is compiled non-interactively; every challenge below is a hash output over the running transcript with a domain tag:

1. `ext-c` : $\hat c\leftarrow C^{\ell_C}$ — after commitments $t_j$ (Fig. 2 step 3). Tag distinct per instance $j$.
2. `range-eta` : $\eta\leftarrow\mathbb{F}_{q^e}^{\ell}$ — after nothing (opens the range sum-check; Fig. 1 step 2).
3. `range-u[i]` : $u_i\leftarrow\mathbb{F}_{q^e}$ per round $i$ of the range sum-check (after each univariate).
4. `lin-u[i]` : challenges of the $\Pi^{\mathrm{hyb}\mbox{-}R1CS}$ sum-check, then `lin-v` : $v\leftarrow C^{\log(\ell)+1}$ (Fig. 4 steps 1,3,6).
5. `uni-d` : $d\leftarrow\mathbb{F}_{q^e}^{\ell_0}$ — after all evaluation claims (Fig. 3 step 3).
6. `uni-z[i]` : challenges of the unification sum-check.
7. `fold-s[j]` : $s_j\leftarrow\mathcal{D}$ — **one independent tag per coordinate $j\in[L]$** (Lemma 4's reprogramming argument needs coordinate-wise independence; a single hash over all coordinates breaks the forking lemma's $\epsilon-L/|\mathcal{D}|$ bound).

Total FS error accounting mirrors the interactive $\kappa$ of Theorem 3 plus the standard FS amplification over the (polynomially many) challenges.

### 6.5 Knowledge-soundness skeleton shared by all four protocols

Every proof in the paper follows the same lattice-extractor template — reproduce it once in the lab's proof-review docs:

1. Run $P^*$ on random challenges; rewind for a second accepting transcript with (partially) fresh challenges.
2. If the two extracted witnesses differ after slack normalization $w/s$, their difference/combination satisfies the **random-matrix homogeneous system** ⇒ output a $\Xi^{\mathrm{sis}}$ witness (norm = sum/combination of the two bounds, e.g. $2\tilde b\gamma\varrho$, $2b$, $2\bar\beta\delta$, $2B'$).
3. If they coincide, the *verifier check* itself must have been fooled: bound its acceptance with (a) sum-check soundness + Schwartz–Zippel over $\mathbb{F}_{q^e}$ (field side: $D/q^e$), or (b) the **ring zero bound** (Lemma 3) over strong sampling sets ($\deg f/|C|$), or (c) both (batched $R_{q^e}$ sum-check: $(k\ell+\varphi)/q^e$).
4. Union-bound all error terms; expected polynomial time via $1/\epsilon$ forking.

### 6.6 From folding to IVC and PCD — scope notes

- **IVC**: generic from any folding scheme (Val08/NPR19-style accumulation); Cyclo needs no extra machinery beyond the standard wrapper.
- **PCD**: *not* directly supported — two obstructions stated in the paper: (a) the accumulator relation has different parameters ($m\to\tilde m$, $k\to k{+}1$, bound $\beta$ vs $B$) than the input relation, so accumulation trees do not re-fold cleanly; (b) the accumulator plays a *special role*: it is never norm-checked and its witness is never multiplied by the challenge, so it cannot be an ordinary child of another fold.
- **Envisioned deployment** (the lab should mirror this): prove long sequential computation *branches* with Cyclo (cheap per-round folding, bounded $T$), then merge/refresh accumulators with LatticeFold+ rounds (dual role: merger + norm refresher) — a two-tier schedule. Refresh policy: refresh when $\beta$ approaches the MSIS-calibrated ceiling or when a DAG merge is required, whichever comes first.

---

## 7. Parameters & Concrete Efficiency

### 7.1 Main parameter comparison (Table 2 of the paper)

| Parameter | LatticeFold+ [BC25b] | **Cyclo** |
|---|---|---|
| Rank ($a$) | 9 | 13 |
| Modulus ($q$) | $\approx2^{128}$ | $\approx2^{50}$ |
| Degree ($\varphi$) | 64 | 128 |
| Folding depth ($T$) | $\infty$ | 64 (usable to $2^{20}$) |
| Initial norm ($B$) | $2^{10}$ | $2^{10}$ |
| Challenge distribution | $\{-1,0,1,2\}^{\varphi}$ | $\{-1,0,1\}^{\varphi}$ |
| Witness size ($m$) | $2^{21}$ | $2^{20}$ |
| #coefficients $\varphi\cdot m$ | $2^{27}$ | $2^{27}$ |
| #relations folded | 2 (accumulator) + 1 | 1 (accumulator) + 1 |
| Other | $L=3$ | $e=2$, $L=1$, $k=3$, $n=1$, $b=1$ |
| **Proof size** | **100 KB** | **31.8 KB** |

### 7.2 Folding proof sizes (Table 1)

| $m\varphi$ | $2^{25}$ | $2^{27}$ | $2^{29}$ |
|---|---|---|---|
| Proof size (KB) | 31.4 | 31.8 | 32.9 |

### 7.3 Scaling knobs (Remark 9)

- $T\to2^{10}$: proof ≈ 39.7 KB; $T\to2^{20}$: ≈ 41.7 KB (logarithmic growth in rounds only).
- 256-bit security: ≈ 40.4 KB. Soundness $2^{-200}$ via $e=4$: ≈ 52.4 KB. Both: ≈ 61 KB.

### 7.4 Asymptotic complexity (Remark 3)

- **Prover time:** $O(La'm\log_{2b}2B)$ $R_q$-multiplications (dominated by extension commitment).
- **Verifier time (excl. hashing):** $O(La')$ $R_q$-multiplications.
- **Online instance size:** $L(a'+k+n)$ $R_q$-elements; **accumulator size:** $(a'+k+1)$ $R_q$-elements.
- **Folding proof size:** $La'+L$ elements in $R_q$, $(k{+}2)(L{+}1)$ in $R_{q^e}$, $2\lceil\log m\varphi(\log_{2b}2B)\rceil$ $\mathbb{F}_{q^e}$, $(2b{+}2)\lceil\log(m\varphi(\log_{2b}2B))\rceil$ $\mathbb{F}_{q^e}$ (halve the last via Remark 2 merging).

### 7.5 Microbenchmarks (Tables 3–5; single thread, AVX-512-IFMA)

| Component | Runtime |
|---|---|
| $T_{\mathrm{ntt}}$: forward incomplete NTT | 179.03 ns |
| $T_+$: ring add (no reduction) | 40.077 ns |
| $T_q$: modular reduction | 97.102 ns |
| $T_*$: NTT-domain multiply | 186.53 ns |

| Protocol | Expression | Time |
|---|---|---|
| Double commitment [BC25b] | $(k\varphi ma)\cdot(T_+ + T_q/\ddagger)$ | 129.4 s |
| **Extension commitment (Cyclo)** | $(m\log_{2b}2B)\cdot(T_{\mathrm{ntt}}+a(T_*+T_+ + T_q/\ddagger))$ | **36.7 s (≈3.53× faster)** |

Hardware: Dell PowerEdge XE8640, 2×48-core Xeon Platinum 8468 (Sapphire Rapids), 192 vcores/1 used, 1 TB DDR5-4800, CentOS 7.

### 7.6 Sum-check cost estimates (App. C.3)

- **Range sum-check:** ℓ rounds, degree $2b+2$, over $\mathbb{F}_{q^e}$; first round needs $\hat m\varphi/2$ interpolations of partially-evaluated $\hat f$; using $(X-1)X(X+1)=X^3-X$ (Karatsuba-style, 5 mults per leaf-pair) ⇒ total ≈ $6\hat m\varphi$ $\mathbb{F}_{q^e}$-mults ≈ $6\hat m e$ $R_q$-mults; with $e=2$: coefficient 12 < rank 13 ⇒ below commitment cost.
- **Unification sum-check:** degree 2; dominated by the single accumulator MLE claim (all other claims structured/precomputable); ≈ $4\hat m$ $R_{q^e}$-mults ≈ $4\hat m e$ $R_q$-mults; $4e=8<13$ ⇒ below commitment cost.

### 7.7 Memory (App. C.4)

- Cyclo: store + sum-check over $(L+1)m\log_{2b}2B$ ring elements ⇒ **1.56 GB** (Table 2 params). Similar to LatticeFold [BC25a].
- LatticeFold+ [BC25b]: $(L+1)m\varphi\log_\varphi B$ ring elements = 16 GB nominal, ≈256 MB optimistic with sparse-monomial sum-check.

### 7.8 What Cyclo borrows from Neo, and what it replaces

| Aspect | Neo [NS25] | Cyclo |
|---|---|---|
| Fq→Rq encoding | base-$b$ digits as coefficients of a ring element ("matrix commitments", commutative subrings of matrices, ad-hoc machinery) | same encoding recast as $\theta_k$ module homomorphism + canonical preimage $p_c(X)$ (Thm 4 = Neo's construction) |
| Folding step | linearization (Hypernova-style) done over $\mathbb{F}_q$ | same (Fig. 4 sum-check over $\mathbb{F}_{q^e}$) — explicitly via Lemma 6 |
| Norm control on inputs | decomposition machinery inside folding | **skipped** when $k\le b$; otherwise extension commitment (Fig. 2) |
| Norm control on accumulator | double commitment analog | **none** (amortized norm-refreshing; bounded rounds + refresh) |
| Witness decomposition when folding Fq constraints | required | **never** (partial range checks only on input side) |
| Pay-per-bit commitment | yes (cost ∝ nonzero base-$k$ digits) | inherited verbatim ($A\theta_k^{-1}(z)$) |

**Reading for the lab:** treat Cyclo as the "algebraically clean Neo + LatticeFold+-compatible accumulator": the $\theta_k$ reformulation is the piece to port into any Fq-native protocol that needs Ajtai commitments (including SALSAA/ProtogaLattice front-ends); the extension-commitment/range-check pair is the piece that replaces LatticeFold+’s double commitment wherever the *accumulator is not norm-checked*.

### 7.9 Position within the lab's folding stack

- `latticefold_plus.md` documents the double-commitment/monomial-decomposition folding that Cyclo uses as its **refresh step** — the two relations are "almost exactly the same up to notation" (paper §2.2), so a shared `Xi^lin` implementation serves both.
- `protogalattice.md` (PGL-Fold/PGL-Boot) is the Gröbner-flavored sibling; its $e^*$-check / relaxed-witness linearization parallels Cyclo's slacked-relation extraction bookkeeping — share the slack machinery ($\Xi^{\mathrm{lin\mbox{-}slack}}$, $\bar\beta,\delta$ formulas) between the two.
- `pikkufold.md` is the non-lattice minimalist folding baseline; keep its instance-witness API shape so the benchmark harness can run all folders uniformly.

---

## 8. Implementation Notes

### 8.1 Data structures

- `RingElt`: `int64[φ]` (or `uint64` + Barrett) coefficients in balanced rep; NTT-domain form as $\varphi/2$ quadratic-slot pairs for the incomplete NTT ($R_q\cong(\mathbb{F}_{q^2})^{\varphi/2}$).
- `LinInstance`: `{r: [Rqe^log mi; k], b: [Rqe^log m; n], y: Rq^{a+k+n}}` plus bound $B$; `Accumulator` = same with $k{+}1$ matrix slots and $m\to\tilde m$, $\beta$.
- `Witness`: `Rq^m` (input) / `Rq^{mℓ}` (accumulator); keep **both** coefficient form (for $\mathrm{cf}^\vee$/range MLE) and NTT form (for commitments).
- Matrices $M_i$ fixed per circuit — precompute $\mathrm{MLE}[M_i]$ row-MLEs and the digit-extended $\tilde M_i=((2b)^i)\otimes M_i$ once.
- Challenges: $\eta,u,r,v\in\mathbb{F}_{q^e}$ ($e=2$ ⇒ pairs), $s\in\{-1,0,1\}^{\varphi}$ per coordinate, $c\in\mathbb{F}_{q^2}\subset R_q$ for $\Pi^{\mathrm{ext}}$.

### 8.2 Algorithms & reuse from `lzk` core engine

| Cyclo component | `lzk` reuse |
|---|---|
| $R_q$ arithmetic, incomplete NTT (split to $\mathbb{F}_{q^2}$) | `lzk.ring` NTT (extend: power-of-two $\varphi=128$, $q\equiv2k{+}1\bmod 4k$ with $k=64$; Karatsuba in each quadratic slot — or full NTT if a $q$ with complete splitting is chosen and only the *approximate* set is needed for $\mathcal{D}$) |
| Ajtai commitment $t=\mathbf{R}v$, $y=Az$ | `lzk.ajtai` (pay-per-bit variant: multiply by sparse digit-scaled shifts; cost ∝ nonzero digits) |
| Sum-check over $\mathbb{F}_{q^e}$ (range, unification, R1CS linearization) | `lzk.sumcheck.multilinear` with field-switch to $\mathbb{F}_{q^2}$; degree-$d$ unis with skipped constant term |
| Sum-check over $R_{q^e}$ = $\varphi$ batched $\mathbb{F}_{q^e}$ sum-checks | `lzk.tensor`/LDE + batched sum-check; challenges bound per NTT slot |
| $\mathrm{eq}/\mathrm{tensor}/\mathrm{MLE}$ machinery | `lzk.sumcheck.eq`, `tensor(t)` in lexicographic order (bit order must match MLE indexing everywhere) |
| $\mathrm{cf}^\vee$, dual basis, Trace | new small module: negacyclic twist ($a^\vee_i=-a_{\varphi-i}$) for power-of-two $\varphi$; $\mathrm{Trace}$ = fold over NTT slots (conjugation + sum) |
| $\theta_k,\theta_k^{-1}$ (base-$k$ digit packing) | new: vectorized digit decomposition of $\mathbb{F}_q$ elements ($k=2$ ⇒ bits; pay-per-bit sparsity) |
| Fiat–Shamir | `lzk.fs` transcript with **domain-separated tags per $s$-coordinate** (Lemma 4 requirement) and per challenge type |

Key new algorithms to write: (1) vertical digit decomposition $w\mapsto(w_0,\dots,w_{\ell-1})$ base $2b$ with balanced digits; (2) extension-commitment step (Fig. 2) incl. $\langle c,(y_0,\dots,y_{a-1})\rangle$ folding of Ajtai images; (3) range-check sum-check with the $2b{+}2$-degree univariate and the $X^3-X$ 5-mult leaf optimization; (4) unification sum-check with variable-count padding; (5) Fig. 4 linearization (Hypernova-style) with $d_i$ ring-side computation and $\theta_k$ final check; (6) the merged-variant of Remark 2; (7) accumulator bookkeeping $\beta\mathrel{+}=Lb\gamma$ with hard cap $\ell_{\mathrm{fold}}$ + LatticeFold+ refresh hook.

### 8.3 Complexity summary

- One folding round (input side): extension commitment $a'm\log_{2b}2B$ ring-mults; range sum-check $\approx6\hat m e$; unification $\approx4\hat m e$; folding itself $O(L\tilde m)$ adds. Verifier: $O(La')$ ring-mults + hash.
- $b$ is the central trade-off: larger $b$ ⇒ smaller $\ell=\log_{2b}2B$ (cheaper commitment, shorter $v$) but degree-$2b{+}2$ range sum-check and $2\tilde b\gamma\varrho$ SIS slack. Paper uses $b=1$ (ternary) and suggests $b=2$ (base 4) as future speedup of commitment.

### 8.4 Pitfalls (hard-won specifics)

1. **Base confusion in Fig. 2:** the body text defines digits w.r.t. base $2b$ ($w=\sum w_i(2b)^i$, sign-amortized) while the figure line reads $w=\sum w_i b^i$ with the $\otimes$ row using $(2b)^i$ — implement base **2b** consistently; mismatch silently breaks the $\tilde M v\mapsto Aw=y$ identity.
2. **$\theta_k$ is module-only:** never reorder $\theta_k$ past ring multiplication ($\theta_k(ab)\neq\theta_k(a)\theta_k(b)$ in general); the only allowed commute is $\mathbb{F}_q$-linearity (Lemma 6). The R1CS check must run on $\theta_k(z)$ *after* ring-side matrix products are pushed through $\theta_k$ one side at a time.
3. **Trace/dual-basis direction:** $\mathrm{Trace}(t̃)$ must be the *algebraic* trace over the NTT slots of $R_{q^e}$; using the constant term instead only works for $f=2\varphi$ power-of-two rings and breaks the Lemma-2 generalization. Keep `cf_inv_dual(tensor(u))` consistent with the chosen basis (dual twist sign $-a_{\varphi-i}$).
4. **Sum-check batching with different arities** (claims (a)–(d)): pad with auxiliary variables and *erase* the padded coordinates from the output point — forgetting the erase step yields wrong folded instances.
5. **Challenge-set duality:** $C$ (for $\Pi^{\mathrm{ext}}$, needs strong-sampling only, norm-free ⇒ subfield $\mathbb{F}_{q^2}$) vs. $\mathcal{D}$ (folding, needs small operator norm ⇒ ternary, only *approximately* strong). Swapping them breaks either soundness ($\kappa_{\mathrm{nu}}$ explodes) or norm bounds.
6. **$\kappa_{\mathrm{nu}}$ is heuristic:** Lemma 9’s $\kappa_{\mathrm{nu}}\approx k/q^{\varphi/k}$ is supported by experiments (`invertibility.ipynb`); for the lab, re-run that experiment for the chosen $(q,\varphi,k)$ and record the empirical non-unit rate; fall back to the exact LS18 set (with RNS arithmetic) if it exceeds the budget.
7. **Norm ledger discipline:** track $\beta$ (completeness), $\hat\beta,\bar\beta,\delta$ (extraction) separately; the SIS call at the end uses $2\bar\beta\delta$ — under-tracking $\gamma=\|\mathcal{D}\|_{\mathrm{op}}$ (ternary ⇒ up to $\varphi\cdot\max|s_i|$? no: for ternary $s$, $\|s\|_{\mathrm{op}}$ can reach $\varphi$ in the worst case — the paper’s concrete $\gamma$ comes from the instantiation; **use the instantiated $\gamma$, not the worst case**) invalidates rank selection.
8. **Bounded fold count:** enforce $\ell_{\mathrm{fold}}\le T$ in the API (soundness *fails* beyond); expose the LatticeFold+ refresh as the escape hatch; do not silently continue.
9. **Public prefix handling:** the Fig. 4 trick appends $\mathrm{MLE}[w'](v,0)=e$ with $b'=(v,0)$ — the trailing zeros are part of the claim; dropping them changes $n$ and the tensor width.
10. **AVX-512-IFMA 50-bit lanes:** $\ddagger$ (adds before reduction) must keep intermediates < $2^{60}$ for Barrett; audit every accumulation loop.
11. **Verifier-side cheapness:** the folding verifier does $O(La')$ ring-mults *only because* the accumulated witness is never multiplied by $s$; any “symmetrization” of the fold (multiplying $v$ by $s^{-1}$-style tricks) reintroduces multiplicative growth — don’t.
12. **Recursive-verification caveat (Remark 1):** efficiency claims are for the folding protocol itself; in-circuit verification changes the picture (witness rep. size grows when encoding $\mathbb{F}_q$ into $R_q$, but fewer verifier ops ⇒ smaller circuit; keeping $x$ outside the Ajtai commitment as field elements helps further).
13. **Range check lives over the field, batching over the ring:** per-repetition error of the range test is $D/q^e$ (field bound) while extension/batching use the ring bound $\deg f/|C|$ — do not mix the two error formulas when tallying $\kappa$.
14. **Lexicographic order discipline:** `tensor(t)` entries and MLE Boolean points must share one global bit order; the range sum-check indexes $\mathrm{cf}(w)$ as a flat $m\varphi$ vector whose index decomposes as (ring-element index, coefficient index) — fix the convention (paper: lexicographic over $\{0,1\}^{\log(m\varphi)}$) and assert it in tests.

### 8.5 Proposed lab module layout

```
lzk/protocols/cyclo/
  __init__.py        # CycloFS, CycloAccumulator, fold() entry points
  relation.py        # Xi^lin, Xi^lin-slack, Xi^sis, Xi^com-hyb-R1CS dataclasses + checkers
  theta.py           # theta_k / theta_k^{-1}, digit packing, pay-per-bit sparsity
  dual.py            # cf_dual / cf_inv_dual / Trace (power-of-two + general dual basis)
  extcommit.py       # Fig. 2 Pi^ext  (vertical decomposition, R v = t, image folding)
  rangecheck.py      # Fig. 1 Pi^range (product-poly sum-check, t~ = <cf_inv_dual(tensor(u)), w>)
  unify.py           # Fig. 3 step 4 (batched claims (a)-(d), arity padding)
  fold.py            # Fig. 3 steps 5-6 (short-challenge fold, norm ledger, T cap)
  r1cs_reduction.py  # Fig. 4 Pi^hyb-R1CS (linearization sum-check over F_{q^e})
  params.py          # Table 2 presets + LatticeEstimator-driven rank selection
  bench.py           # replicate Tables 1,3,4 component benchmarks
tests/test_cyclo_*.py
```

### 8.6 Test plan (completeness + targeted soundness probes)

1. **Relation round-trips:** for random short $w$, assert $\Xi^{\mathrm{lin}}$ checker accepts; assert Fig. 2 output instance checks $\tilde M_k v=Aw=y$ on the nose.
2. **$\theta_k$ unit tests:** $\theta_k\theta_k^{-1}=\mathrm{id}$ on $\mathbb{F}_q$; Lemma 6 MLE commutation on random vectors; $\|p_c\|_\infty\le k$.
3. **Digit decomposition:** reconstruct $w=\sum_i w_i(2b)^i$ bit-exact; all $\|w_i\|_\infty\le b$; balanced reps.
4. **Range test:** honest $w$ passes end-to-end; malicious $w$ with one coefficient $=b{+}1$ rejected with prob $\ge1-\ell(2b+2)/q^e$ over random $\eta,u$.
5. **One full fold (L=1):** fresh $\Xi^{\mathrm{lin}}$ + zero accumulator → verify folded instance + norm ledger $\beta\to\beta+b\gamma$; then $T$ folds in a loop, assert $\beta_T=Tb\gamma$ and MSIS rank still valid at terminal bound.
6. **R1CS path:** small random R1CS over $\mathbb{F}_q$ (e.g. $m=16$), encode via $\theta_2$, run Fig. 4, then fold; verify final decider opens $Az=y$ and all tensor claims.
7. **Forking simulation (soundness sanity):** two adversarial transcripts with differing $v$ must yield an $R(v^*-v')=0$ SIS witness in the unit test (construct directly).
8. **Merged-sum-check equivalence (Remark 2):** identical folded instances from merged vs. per-instance range sum-checks.
9. **Benchmark parity:** reproduce Table 3 timings within 2× on lab hardware (Python/numpy will be slower than AVX-512 HEXL; record scaling instead).
10. **FS determinism:** re-derive all challenges from a serialized transcript; bit-reproducibility across platforms.

---

## 9. Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- ✅ The fold with the PARTIAL range check (pay-per-bit): the cross term's
  high bits checked via digit decomposition, the low residual joining the
  norm sumcheck (fold_with_partial_range + verify_partial_range).
- □ Not implemented: the full constraint-system folding (AIR-level), the
  Neo pay-per-bit bit-level accounting, the comparison vs LatticeFold+.

**(replacing the placeholder)**

- DONE: the fold with the PARTIAL range check (pay-per-bit): the cross term's high bits checked via digit decomposition, the low residual joining the norm sumcheck (fold_with_partial_range + verify_partial_range).
- NOT implemented: the full constraint-system folding (AIR-level), the Neo pay-per-bit bit-level accounting, the comparison vs LatticeFold+.
