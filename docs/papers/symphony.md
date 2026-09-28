# Symphony: Scalable SNARKs in the ROM from Lattice-Based High-Arity Folding — Deep Analysis & Implementation Spec

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Symphony: Scalable SNARKs in the Random Oracle Model from Lattice-Based High-Arity Folding |
| **Author** | Binyi Chen (Tsinghua University; work done while at Stanford University) |
| **Date / status** | August 20, 2026 |
| **Local text** | `papers_txt/symphony.txt` (3172 lines; squeezed copy `/tmp/sq/symphony.txt`, 3044 lines) |
| **Paradigm shift** | First proving paradigm that uses folding schemes **as a black box without embedding hash functions (random oracles) into SNARK circuits** — an alternative to IVC/PCD as the way to leverage folding |
| **Core contributions** | (1) **High-arity lattice folding** $\Pi_{\mathrm{fold}}$ (Theorem 4.1): compresses $\ell_{\mathrm{np}}=\mathrm{poly}(\lambda)$ (e.g. $2^{10}=1024$) NP-complete statements in a **single shot**; prover time dominated by committing to input witnesses + one degree-3 sumcheck over an extension field. (2) **Generic compiler** (Theorem 6.1): folding RoK → SNARK in ROM via Commit-and-Open transcript compression + CP-SNARK, with **no FS circuit inside proven statements**. (3) **Two-layer folding** (Section 8) via a new *splitting RoK* for constant folding depth. |
| **Why not IVC/PCD** | IVC/PCD requires recursive statements embedding the folding verifier incl. Fiat–Shamir hash over $R_q$ elements (SHA-256 ≈ tens of thousands of R1CS constraints; even SNARK-friendly hashes ≈ hundreds); security heuristic when oracles instantiated in-circuit (practical attacks exist for GKR-based SNARKs [KRS25]); folding arity limited to 2–3; rewinding-based IVC/PCD secure only for constant folding depth ([LS24; BMNW25a]) |
| **Headline numbers** | $2^{16}$ R1CS statements ($2^{16}$ constraints each, 64-bit field) = $2^{32}$ total constraints; proof < 200 KB post-quantum (WHIR/LaBRADOR-based), < 50 KB with pairings (Hyperplonk+KZG); prover memory independent of #statements, $O(\log\log n)$ passes; prover time ≈ $3\cdot2^{32}$ mults of arbitrary $R_q$-elements with low-norm ($\ell_\infty\le8$) elements over $R_q=\mathbb{Z}_q[X]/\langle X^{64}+1\rangle$; MSIS at 117-bit security |
| **Deployments cited** | 0xPARC: verify Llama 3 inferences; Syscoin: shrink SP1 verifier circuits |
| **Limitations (stated)** | Not fully online streaming (streams over a *known* batch); verification linear in #statements; single-layer CP-SNARK circuit grows as $O(\ell_{\mathrm{np}}\cdot\ell)$ $R_q$-mults (fixed by two-layer at the price of a stronger structured-MSIS assumption) |
| **Figures to transcribe** | Fig. 1 $\Pi_{\mathrm{had}}$ (Hadamard RoK); Fig. 2 $\Pi_{\mathrm{rg}}$ (approximate range proof w/ random projection + monomial lookup); Fig. 3 $\Pi_{\mathrm{gr1cs}}$ (single-instance reduction, interleaving Fig. 1+2); Fig. 4 $\Pi_{\mathrm{fold}}$ (high-arity folding, Parts I+II); App. A $\Pi_{\mathrm{mon}}$ (monomial RoK); Construction 6.1 (SNARK compiler); Section 8 splitting RoK |
| **Lab role** | The lab's ROM-SNARK endpoint: consumes the Ajtai-commitment + sumcheck + monomial-lookup machinery shared with LatticeFold+/Cyclo and produces the *outer* CP-SNARK architecture; the $\varphi$ map of §4.1 is literally Cyclo's $\theta_k$ — share implementations |

---

## 2. Notation Table (EVERY symbol)

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter; $\mathrm{negl}(\lambda)$, $\mathrm{poly}(\lambda)$ standard |
| $\log(\cdot)$ | $\log_2$; $(l,r)=\{l{+}1,\dots,r{-}1\}$, $[l,r)=[l{-}1,r)$, $[n]=[1,n]$ (⚠️ 1-indexed, unlike Cyclo) |
| $q$ | prime modulus; $\mathbb{Z}_q$ with reps in $[-q/2,q/2)$ |
| $d=2^k$ | ring dimension of $R$ **and** R1CS batching factor (concrete 64) |
| $R$, $R_q$ | $R=\mathbb{Z}[X]/\langle X^d{+}1\rangle$; $R_q=R/qR=\mathbb{Z}_q[X]/\langle X^d{+}1\rangle$ |
| $\mathrm{cf}(f)$, $\mathrm{ct}(f)$ | coefficient vector $\in\mathbb{Z}_q^d$ / constant term; for $f\in R_q^n$: coefficient matrix $\mathrm{cf}(f)\in\mathbb{Z}_q^{n\times d}$, first column $\mathrm{ct}(f)$; $\mathrm{cf}^{-1}$ inverses |
| $\mathrm{flt}(M)$ | vertical concatenation of rows of $M$: $\mathrm{flt}(M)=(M_{1,*},\dots,M_{n,*})\in\bar R^{nm}$ |
| $\|F\|_\infty,\|F\|_2$ | entrywise max / Frobenius norm of the canonical lift to $\mathbb{Z}$ |
| $\|a\|_{\mathrm{op}}$ | $\sup_{y\in R}\|a\cdot y\|_2/\|y\|_2$; $\|S\|_{\mathrm{op}}=\max_{a\in S}\|a\|_{\mathrm{op}}$ (concrete: 15) |
| $S\subset R_q$ | folding challenge set as in LaBRADOR: coefficients in $\{0,\pm1,\pm2\}$, $\|S\|_{\mathrm{op}}\le15$, $S-S$ invertible over $R_q$ [LS18 Cor. 1.2] |
| $\beta$ | folding challenge vector $\beta\leftarrow S^{\ell_{\mathrm{np}}}$ (also $\beta_{\mathrm{SIS}}$ MSIS norm bound — disambiguate) |
| $\chi$ | projection distribution over $\{0,\pm1\}$: $\Pr[0]=1/2$, $\Pr[\pm1]=1/4$ each |
| $\ell_{\mathrm{np}}$ | folding arity — number of input statements folded in one shot (concrete $2^{10}$) |
| $\ell_h$ | projection input length (block size of $M_J$); divides $n$ (concrete $2^{14}$) |
| $\lambda_{\mathrm{pj}}$ | projection output length (concrete 256) |
| $J$, $M_J$ | $J\leftarrow\chi^{\lambda_{\mathrm{pj}}\times\ell_h}$; structured projection $M_J:=I_{n/\ell_h}\otimes J\in\mathbb{Z}_q^{(n\lambda_{\mathrm{pj}}/\ell_h)\times n}$ |
| $m$ | #R1CS constraints per instance / rows of $M_i$ (concrete $2^{16}$); also $m:=n\lambda_{\mathrm{pj}}/\ell_h$ in §3.4 — disambiguate per context |
| $m_J$ | $n\lambda_{\mathrm{pj}}/\ell_h$ (rows of $M_J$; power of two, $m_J\le m\le n$) |
| $\bar n$, $n$ | R1CS witness length per original statement ($2^{16}$) / generalized witness length $\bar n k_{\mathrm{cs}}$ ($2^{20}$) |
| $n_{\mathrm{in}},n_w$ | public-input / private-witness lengths of the generalized relation, $n=n_{\mathrm{in}}+n_w$ |
| $k_{\mathrm{cs}}$, $b$ | R1CS witness decomposition factor $1+\lfloor\log_b q\rfloor$ (16) and base (16); $\mathrm{decomp}_{b,k}$: $\|g_i\|_\infty\le b/2$, $f_i=\langle g_i,(1,b,\dots,b^{k-1})\rangle$ |
| $k_g$ | #monomial vectors in range proof: minimal with $B_{d,k_g}:=(d'/2)(1+d'+\dots+d'^{k_g-1})\ge9.5B$ (concrete 3) |
| $d'$ | $d-2$ (range digit base) |
| $B$ | input witness norm bound for $\mathrm{VfyOpen}_{\ell_h,B}$ (concrete $2^{10}$, with $0.5b\sqrt{\ell_h}\le B\le B_{d,k_g}/9.5$) |
| $B'$ | relaxed norm bound $16B_{d,k_g}/\sqrt{30}$ (concrete ≈353806) |
| $B_{\mathrm{bnd}},B_{\mathrm{rbnd}}$ | strict / relaxed opening $\ell_2$-bounds of CM: $B_{\mathrm{rbnd}}=2B_{\mathrm{bnd}}$ (concrete $B_{\mathrm{rbnd}}=\beta_{\mathrm{SIS}}/(4\|S\|_{\mathrm{op}})\approx2^{31}$, $B_{\mathrm{bnd}}=2^{30}$) |
| $\beta_{\mathrm{SIS}}$ | MSIS $\ell_2$-norm bound (concrete $2^{37}$) |
| $\kappa$ | MSIS rank / commitment length ($R_q^\kappa$; concrete 12) — NOT knowledge error here |
| $\mathbb{M}$ | $d$-monomial set $\{0,1,X,\dots,X^{d-1}\}\subset R_q$ (Eq. 2) |
| $t(X)$ | table polynomial $\sum_{i\in[1,d/2)}i\cdot(X^i+X^{-i})=\sum_i i\cdot(X^i-X^{d-i})\in R_q$ (Eq. 3) |
| $\mathrm{sgn}(a)$, $\mathrm{Exp}(a)$ | sign of $a\in(-d/2,d/2)$; $\mathrm{Exp}(a):=\mathrm{sgn}(a)X^{|a|}\in\mathbb{M}$; entrywise $\mathrm{Exp}(M)$ |
| $K=\mathbb{F}_{q^t}$ | sumcheck extension field (concrete $t=2$: $\mathbb{F}_{q^2}$) |
| $E$ | $E:=K[X]/\langle X^d{+}1\rangle\cong K\otimes_{\mathbb{F}_q}R_q$ — **tensor of rings**; element = degree-$<d$ poly over $K$ |
| $\mathrm{ts}(r)$ | tensor $(\mathrm{eq}_b(r))_{b\in\{0,1}^k}\in K^{2^k}$ (Eq. 14); $\mathrm{eq}_b(r)=\prod_i(1-b_i)(1-r_i)+b_ir_i$ |
| $\hat f$ / $f(b)$ | MLE $\hat f\in K^{\le1}[X_1..X_{\log n}]$ and its evaluation vector $(\hat f(b))_{b}\in K^n$; $\hat f(r)=\langle f,\mathrm{ts}(r)\rangle$ |
| $\epsilon_{\mathrm{sum}}$ | sumcheck soundness error $D\log(n)/|K|$ |
| $\mathrm{ev}_a(\beta)$ | for $a=\sum a_iX^{i-1}\in R_q$ and $\beta\in K$: $\mathrm{ev}_a(\beta)=\sum a_i\beta^{i-1}\in K$ (canonical map $R_q\to K[X]$); $\mathrm{ev}_e(\beta)$ same for $e\in E$ w.r.t. $K$-coefficients |
| $c_{\mathrm{fs},i}$, $m_i$, $r_i$ | FS-transcript round commitment / prover message / verifier challenge ($i\in[\mathrm{rnd}]$, plus $r_{\mathrm{rnd}+1}$) |
| $\Pi_{\mathrm{cm}}$ | outer (transcript) commitment: Merkle or KZG; must be **straightline extractable**, not nec. linearly homomorphic |
| $\mathrm{CM}[ \Pi_{\mathrm{cm}},\Pi_{\mathrm{rok}}]$, $\mathrm{FS}^H[\cdot]$ | Commit-and-Open transformation / its Fiat–Shamir compile |
| $H$, $H_{\mathrm{fd}}$ | random oracles ($H_{\mathrm{fd}}:\{0,1\}^L\to S^{\ell_{\mathrm{np}}}$ for the folding challenge; domain-separated in practice) |
| $Q$ | #random-oracle queries of the adversary (FS knowledge-error factor) |
| $\mathrm{rnd}$ | #rounds of the RoK ($\mathrm{rnd}=\mathrm{poly}(\log\lambda)$ for the compiler) |
| $R_{\mathrm{lin}}^{\mathrm{aux}}$, $R_{\mathrm{had}}^{\mathrm{aux}}$, $R_{\mathrm{rg}}^{\ell_h,B}$, $R_{\mathrm{mon},k_g}$, $R_{\mathrm{batchlin},k_g}$, $R_{\mathrm{gr1cs}}^{\mathrm{aux}}$, $R_{\mathrm{r1cs}}$, $R_{\mathrm{sum}}$, $R_{\mathrm{eval}}$, $R_{\mathrm{cp}}$, $R_o$ | relations — see Section 4 |
| $\varphi:R_q\to\mathbb{Z}_q$ | Neo-style map $v(X)\mapsto v(b)$ ($\mathbb{Z}_q$-module hom; same object as Cyclo's $\theta_k$) |
| $k_b$ | 2nd-layer decomposition factor ($\le4$) in Section 8 |
| $A$, $A'$, $r_i$ (§8) | MSIS matrix $A=[r_1A',\dots,r_\ell A']$ (Eq. 56) for the splitting RoK |
| $\mathrm{Estimate}^A_\lambda(\delta)$ | black-box success-probability estimator (Chernoff-backed; $U$ successes, $\hat\epsilon=U/K$) |
| $u\equiv_i u'$ | vectors differ only in coordinate $i$ (CWSS) |

---

## 3. Algebraic Setting

### 3.1 Rings, tensor-of-rings, and the three multiplications

- **Base ring**: power-of-two cyclotomic $R_q=\mathbb{Z}_q[X]/\langle X^d+1\rangle$, $d=2^k$ (concrete $d=64$; $q$ a 64-bit prime). Coefficient matrix view: $f\in R_q^n\leftrightarrow\mathrm{cf}(f)\in\mathbb{Z}_q^{n\times d}$; **norms always on the canonical integer lift**.
- **Extension field** $K=\mathbb{F}_{q^t}$ ($t=2$): all sum-checks run here; soundness denominators are $|K|$.
- **Tensor ring** (Section 2.3, following [BC25b; DP24; NS25]):
  $$E:=K[X]/\langle X^d{+}1\rangle\ \cong\ K\otimes_{\mathbb{F}_q}R_q .$$
  Since $\mathbb{Z}_q\subseteq K$, $R_q$ embeds in $E$. Three multiplication modes, all needed by the protocols:
  1. $K$-scalar × $E$: coefficientwise scalar mult (sumcheck world);
  2. $R_q$-poly × $E$: polynomial multiplication mod $X^d{+}1$ after canonically lifting the $R_q$ factor to $E$ (folding with low-norm challenges);
  3. $K$-scalar × $R_q$-poly: lift either side, same result (bridge world — this is how evaluation claims over $K$ attach to committed $R_q$ witnesses).
- **Interleaving principle**: sumcheck challenges and folding challenges live in different structures ($K$ vs. $S\subset R_q$) yet combine through $E$; this is what lets one fold *evaluation claims* as if they were ring vectors.

### 3.2 Monomial embedding lookup (from LatticeFold+)

- $\mathbb{M}=\{0,1,X,\dots,X^{d-1}\}\subset R_q$; table polynomial $t(X)=\sum_{i\in[1,d/2)}i(X^i-X^{d-i})$ embeds $(-d/2,d/2)$ onto coefficients.
- **Lemma 2.1** ([BC25b] L2.2): for $a\in(-d/2,d/2)$, $b=\mathrm{Exp}(a)=\mathrm{sgn}(a)X^{|a|}$: $\mathrm{ct}(b\cdot t(X))=a$; conversely $\mathrm{ct}(b\cdot t(X))=a\wedge b\in\mathbb{M}\Rightarrow a\in(-d/2,d/2)$. Range checking an integer = monomial membership + one constant-term extraction.
- **Lemma A.1** ([BC25b] Cor 4.1): for $\beta\in K$: $a\in\mathbb{M}\Rightarrow\mathrm{ev}_a(\beta)^2=\mathrm{ev}_a(\beta^2)$ always; $a\notin\mathbb{M}\Rightarrow\Pr_\beta[\mathrm{ev}_a(\beta)^2=\mathrm{ev}_a(\beta^2)]<2d/|K|$. Monomial membership is testable by a *random point identity* — the anchor of $\Pi_{\mathrm{mon}}$.

### 3.3 Random projection (LaBRADOR-style, sublinear verifier)

- **Lemma 2.2** ([GHL22] Cor 3.3 / [BS23] L4.2): with $\chi$ over $\{0,\pm1\}$ ($0$ w.p. $1/2$): $\Pr_{u\leftarrow\chi^n}[|\langle u,v\rangle|>9.5\|v\|_2]\lesssim2^{-141}$; and for $B\le q/125$, $v\in[-q/2,q/2)^n$ with $\|v\|_2>B$: $\Pr_{J\leftarrow\chi^{256\times n}}[\|Jv\bmod q\|_2\le30B]\lesssim2^{-128}$.
- **Structured projection** ([KLNO25]): $M_J=I_{n/\ell_h}\otimes J$ with narrow $J\in\chi^{\lambda_{\mathrm{pj}}\times\ell_h}$ gives a **sublinear verifier** (only $\lambda_{\mathrm{pj}}\ell_h$ random bits to specify) at the cost of checking the projected matrix $H=M_J\mathrm{cf}(f)$ rather than $f$ itself.

### 3.4 Lattice commitment (Construction 2.1)

- $\mathrm{pp}_{\mathrm{cm}}=A\leftarrow R_q^{\kappa\times n}$; commitment $c=Am\in\mathcal{C}:=R_q^\kappa$.
- Message space $\mathcal{M}^*=\{m:\exists(f,s)\in\mathcal{O}'_{\mathrm{rbnd}},\ s\cdot m=f\}$ with relaxed opening space $\mathcal{O}'_{\mathrm{rbnd}}=\mathcal{O}_{\mathrm{rbnd}}\times(S-S)$, $\mathcal{O}_{\mathrm{rbnd}}=\{f\in R_q^n:\|f\|_2\le B_{\mathrm{rbnd}}\}$, $B_{\mathrm{rbnd}}=2B_{\mathrm{bnd}}$.
- **Strict opening** $\mathrm{VfyOpen}$: $s=1\wedge Af=c\wedge\|f\|_2<B_{\mathrm{bnd}}\wedge m=f$ (honest prover always strict).
- **Relaxed opening** $\mathrm{RVfyOpen}$: $Af=s\cdot c\wedge o\in\mathcal{O}\wedge s\cdot m=f$ (Eq. 10) — used only in knowledge-soundness proofs (slack $s\in S-S$).
- Binding reduces to $\mathrm{MSIS}_{q,\kappa,n,4\|S\|_{\mathrm{op}}B_{\mathrm{rbnd}}}$ (Def. 2.2).
- **Fine-grained opening** $\mathrm{VfyOpen}_{\ell_h,B}$ (Eq. 12): $Af=c$ and every $\ell_h\times d$ row-block $F_{i,j}$ of $\mathrm{cf}(f)$ has $\|F_{i,j}\|_2\le B$; if $B\sqrt{nd/\ell_h}\le B_{\mathrm{bnd}}$ then fine-grained ⇒ strict. This is the relation the range proof actually consumes.

### 3.5 Generalized RoK, CP-SNARKs, probability tools

- **Definition 2.3–2.6**: RoK $\Pi$ from $R_1$ to $R_2$ with relaxed input $R'_1$: $\epsilon$-completeness, $\kappa$-knowledge-soundness w.r.t. $R'_1$, public reducibility $x_o=f(x,(m_i),(r_i))$ — the deterministic map the CP-SNARK will check.
- **Sumcheck as RoK**: $R_{\mathrm{sum}}\to R_{\mathrm{eval}}$ with error $D\log n/|K|$; the "special form" simplification to $R'_{\mathrm{eval}}$ (Eq. 17–18): $\forall i:\langle f_i,\mathrm{ts}(r)\rangle=u_i\wedge h(u)=v$ — evaluation claims become **inner products with the tensor**, i.e., linear statements over $E$.
- **Sumcheck batching**: $k$ claims $\to$ one via $\sum\alpha^{i-1}g_i$, $\alpha\leftarrow K$.
- **CWSS** (Lemma 2.3, [FMN24] L7.1): predicate $\Psi$ over $U=S^\ell$; oracle extractor outputs $\ell{+}1$ transcripts $u_\ell\equiv_\ell u_0$ with prob $\ge\epsilon_\Psi(A)-\ell/|S|$, $1+\ell$ expected calls. ROM variant (Lemma B.1): error $(Q{+}1)\ell/|S|$ with programmed oracle $H_{\mathrm{fd}}[y_L,u_i]$.
- **Estimate** (Prop 2.1–2.2, Lemma 2.4): Chernoff-backed black-box estimator; $\hat\epsilon/\epsilon\in[1-\delta,1+\delta]$ w.p. $1-2^{-\lambda}$; $\mathbb{E}[K]=U/\epsilon$. Used by the $\Pi_{\mathrm{rg}}$ extractor to find a *good* projection $J$.
- **CP-SNARK** (Def. 2.8): SNARK for relation $R'=\{i'=(\mathrm{pp}_{\mathrm{cm}},i),\ x'=(x,(c_i)_{i\in[\ell]}),\ w=((w_i,o_i),w^*):\ (i,x,w)\in R\wedge\forall i:\mathrm{RVfyOpen}(\mathrm{pp},c_i,w_i,o_i)\}$.

---

## 4. Relations (exact equations)

### 4.1 Generic committed linear relation (Eq. 21) — the anchor

$$R_{\mathrm{lin}}^{\mathrm{aux}}:=\left\{\begin{array}{l}x=(c\in\mathcal{C},\ x\in R_q^{n_{\mathrm{in}}},\ r\in K^{\log M},\ v\in E^{k_x}),\\ w=f\in R_q^n\ :\ x=f[1..n_{\mathrm{in}}]\ \wedge\ \mathrm{VfyOpen}(\mathrm{pp}_{\mathrm{cm}},c,f)=1\\ \qquad\qquad\wedge\ \forall i\in[k_x]:\ \langle\mathrm{ts}(r)[1..m_i],\ M_if\rangle=v_i\end{array}\right\}$$
with $\mathrm{aux}=(n_{\mathrm{in}},(M_i\in\mathbb{Z}_q^{m_i\times n})_{i=1}^{k_x})$, $M=\max m_i$. Everything in Symphony reduces to *this* shape (plus $R_{\mathrm{batchlin},k_g}$).

### 4.2 Hadamard relation (Eq. 22–23)

$$R_{\mathrm{had}}^{\mathrm{aux}}:=\big\{x=c\in\mathcal{C},\ w=F\in\mathbb{Z}_q^{n\times d}:\ (M_1F)\circ(M_2F)=M_3F\ \wedge\ \mathrm{VfyOpen}(\mathrm{pp},c,\mathrm{cf}^{-1}(F))=1\big\}$$
Output: $R_{\mathrm{lin}}^{\mathrm{aux}}$ with $x=(c,r\in K^{\log m},v\in E^3)$, checks $\forall i\in[3]:\langle(M_if),\mathrm{ts}(r)\rangle=v_i$.

### 4.3 Monomial relations (Eq. 26–27)

$$R_{\mathrm{mon},k_g}:=\big\{x=(c^{(i)}\in\mathcal{C})_{i=1}^{k_g},\ w=(g^{(i)}\in R_q^n)_{i=1}^{k_g}:\ \forall i:\ \mathrm{VfyOpen}(\mathrm{pp},c^{(i)},g^{(i)})=1\ \wedge\ g^{(i)}\in\mathbb{M}^n\big\}$$
$$R_{\mathrm{batchlin},k_g}:=\Big\{x=\big(r\in K^{\log n},[c^{(i)}\in\mathcal{C},u^{(i)}\in E]_{i=1}^{k_g}\big),\ w=(g^{(i)}\in R_q^n)_{i=1}^{k_g}:\ \forall i:\ \mathrm{VfyOpen}(\mathrm{pp},c^{(i)},g^{(i)})=1\ \wedge\ \langle g^{(i)},\mathrm{ts}(r)\rangle=u^{(i)}\Big\}$$

### 4.4 Approximate range relation (Eq. 29–30)

Input: $R_{\mathrm{rg}}^{\ell_h,B}:=\{x=c,\ w=f\in R_q^n:\ \mathrm{VfyOpen}_{\ell_h,B}(\mathrm{pp},c,f)=1\}$. Output: $R_{\mathrm{lin}}^{\mathrm{aux}_J}\times R_{\mathrm{batchlin},k_g}$ where $\mathrm{aux}_J=(n_{\mathrm{in}}=0,M_J=I_{n/\ell_h}\otimes J)$ and
$$R_{\mathrm{lin}}^{\mathrm{aux}_J}=\{x=(c,r\in K^{\log m},v\in E),\ w=f:\ \mathrm{VfyOpen}(\mathrm{pp},c,f)=1\ \wedge\ \langle(M_Jf),\mathrm{ts}(r)\rangle=v\}.$$
Digit bound: $B_{d,k_g}=(d'/2)(1+d'+\cdots+d'^{k_g-1})\ge9.5B$, $d'=d-2$.

### 4.5 Generalized committed R1CS (Eq. 35–36)

$$R_{\mathrm{gr1cs}}^{\mathrm{aux}}:=\left\{\begin{array}{l}x=(c\in\mathcal{C},X_{\mathrm{in}}\in\mathbb{Z}_q^{n_{\mathrm{in}}\times d}),\ w=W\in\mathbb{Z}_q^{n_w\times d}:\\ F^\top:=[X_{\mathrm{in}}^\top,W^\top]\in\mathbb{Z}_q^{d\times n}\\ (M_1\times F)\circ(M_2\times F)=M_3\times F\\ \wedge\ \mathrm{VfyOpen}_{\ell_h,B}(\mathrm{pp},c,\mathrm{cf}^{-1}(F))=1\end{array}\right\}$$
— $d$ R1CS statements over $\mathbb{Z}_q$ batched in columns (SIMD-native).

**Arbitrary-witness conversion (standard trick):** $k_{\mathrm{cs}}=1+\lfloor\log_bq\rfloor$; $M_i:=\bar M_i\otimes[1,b,\dots,b^{k_{\mathrm{cs}}-1}]$, $n=\bar nk_{\mathrm{cs}}$; honest prover sets $X_{\mathrm{in}},W$ columnwise to $\mathrm{decomp}_{b,k_{\mathrm{cs}}}$ of the original vectors; bound $B=0.5b\sqrt{\ell_h}$. Recovering: combine every $k_{\mathrm{cs}}$ rows with $[1,b,\dots,b^{k_{\mathrm{cs}}-1}]$.

**Neo-style alternative for single statements (no vertical expansion):** $\varphi:R_q\to\mathbb{Z}_q$, $v(X)\mapsto v(b)$; committed relation $R_{\mathrm{r1cs}}$ (Eq. 38): $(M_1\times\varphi(f))\circ(M_2\times\varphi(f))=M_3\times\varphi(f)$ with $\|\mathrm{cf}(f)\|_\infty\le b/2$, witness length stays $n$. *(This is exactly Cyclo's $\theta_k$; substitute Neo's sumcheck for $\Pi_{\mathrm{had}}$ and every folding protocol in the paper supports single instances without expansion.)*

### 4.6 CP-SNARK relation (Eq. 54–55) and output relation

- $x_{\mathrm{cp}}:=(x,(r_i)_{i=1}^{\mathrm{rnd}+1},(c_{\mathrm{fs},i})_{i=1}^{\mathrm{rnd}},x_o)$, $w=(w_{\mathrm{cp}}=(m_i)_{i=1}^{\mathrm{rnd}},w_e)$: checks $x_o=f(x,(m_i),(r_i))$ and $c_{\mathrm{fs},i}=\Pi_{\mathrm{cm}}.\mathrm{Commit}(\mathrm{pp},m_i)$.
- Output relation of $\Pi_{\mathrm{fold}}$: $R_o:=R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},k_g}$ with $\mathrm{aux}_{\mathrm{cs}}=(n_{\mathrm{in}},(M_i)_{i=1}^{4})$, $M_4=M_J$ (Eq. 44).

### 4.7 Splitting relations (Section 8, Eq. 57–58)

With $A=[r_1A',\dots,r_\ell A']$ and $M=I_\ell\otimes M'$:
$$R_{\mathrm{lin}}^{\mathrm{aux}'}:\ x=(c,r\in K^{\log\ell},s\in K^{\log m'},v\in E),\ w=(f_1,\dots,f_\ell)\in R_q^{n'\ell}:\ \mathrm{VfyOpen}(\mathrm{pp},c,f)\wedge\langle\mathrm{ts}(r\|s),Mf\rangle=v$$
reduces to $\ell$ statements $R'=\{x=(c,s,v),\ w=f\in R_q^{n'}:\ \mathrm{VfyOpen}(A',c,f)\wedge\langle\mathrm{ts}(s),M'f\rangle=v\}$.

### 4.8 Worked example: SIMD packing with Table 1 numbers

Original: $\bar n=2^{16}$ witness entries per statement, $q$ 64-bit, base $b=16$, $k_{\mathrm{cs}}=1+\lfloor\log_{16}q\rfloor=16$ digits. One ring element ($d=64$ coefficients, each $\ell_\infty\le b/2=8$) holds a column of the matrix view; per statement the witness matrix is $W\in\mathbb{Z}_q^{n_w\times d}$ with $n_w=\bar n_wk_{\mathrm{cs}}=2^{20}$ rows — i.e. **one generalized statement = $d=64$ original R1CS instances** sharing matrices (SIMD), each entry base-16-decomposed into 16 rows.

- Norm check: $B=0.5b\sqrt{\ell_h}=8\cdot\sqrt{2^{14}}=8\cdot128=2^{10}$; fine-grained blocks of $\ell_h=2^{14}$ rows ⇒ each block's $\ell_2\le B$, and $B\sqrt{nd/\ell_h}=2^{10}\cdot\sqrt{2^{20}\cdot64/2^{14}}=2^{10}\cdot2^5=2^{15}\ll B_{\mathrm{bnd}}=2^{30}$ — comfortably a strict opening.
- Range proof: $H=M_J\mathrm{cf}(f)$ has $m=n\lambda_{\mathrm{pj}}/\ell_h=2^{20}\cdot2^8/2^{14}=2^{14}$ rows; $\|H\|_\infty\le9.5B=9720\le B_{d,3}=121117$ w.h.p.; digits in base $d'=62$ with $\|H^{(i)}\|\infty\le31$; each $h^{(i)}=\mathrm{flt}(H^{(i)})\in\mathbb{Z}_q^{2^{14}\cdot64=2^{20}}$ — exactly the length $n$ the monomial relation expects.
- Folding arity $\ell_{\mathrm{np}}=2^{10}$ folds $2^{10}\cdot64=2^{16}$ original statements; total constraints $2^{16}\cdot2^{16}=2^{32}$.

### 4.9 Worked norm ledger for the fold (Eq. 50 sanity)

Per-input $\|f^\ell\|_2\le B\sqrt{nd/\ell_h}=2^{15}$ (above); monomial $\|g^{i,\ell}\|_2\le\sqrt n=2^{10}$. Folded worst case: $\ell_{\mathrm{np}}\|S\|_{\mathrm{op}}\cdot2^{15}=2^{10}\cdot15\cdot2^{15}\approx2^{29.9}\le B_{\mathrm{bnd}}=2^{30}$ ✓ (and $2^{10}\cdot15\cdot2^{10}\ll2^{30}$ for the monomial side) — Eq. (50) holds with the concrete table *only just* on the $f$-side, which explains why the paper flags it as worst-case and why two-layer folding (smaller $\ell$ per layer) relaxes it.

---

## 5. Protocols (full numbered transcriptions)

### 5.0 Dependency graph and reading order

```
ℓ_np generalized committed R1CS statements (x_ℓ, W_ℓ)         [Eq. 36; decomp_{b,kcs} or φ-map]
   |
   |  per instance: Π_gr1cs (Fig. 3) = Π_had (Fig. 1) ⨝ Π_rg (Fig. 2)
   |     Π_had: Hadamard -> 3 linear eval claims over E (degree-3 sumcheck, size m)
   |     Π_rg : norm -> projected-matrix claim + k_g monomial claims
   |             Π_rg uses Π_mon (App. A): monomial membership via ev_u(β)² = ev_u(β²)
   v
ℓ_np reduced pairs (x_{o,ℓ}, w_{o,ℓ}) in R_lin^{aux_cs} × R_batchlin,kg   [Eqs. 46-47]
   |
   |  Π_fold (Fig. 4): shared challenges J, s', α; 2ℓ_np sumchecks merged to 2;
   |  β ← S^{ℓ_np}; linear-combine instances+evaluations (V) and witnesses (P)
   v
ONE folded pair (x_o, w_o) in R_lin^{aux_cs} × R_batchlin,kg             [Thm 4.1, Eq. 50]
   |
   |  FS: Commit-and-Open (round messages -> c_fs,i) + FS^H               [Section 5, Thm 5.1]
   v
Non-interactive folding proof (ROM) — challenges recomputed from c_fs,i
   |
   |  Compiler (Construction 6.1): CP-SNARK proves "openings of c_fs,i form a
   |  valid folding proof w.r.t. PUBLIC challenges" + SNARK for R_o        [Thm 6.1]
   v
SNARK π* = (π_cp, π, (c_fs,i), x_o) — NO hash circuit in any proven statement
   |
   (optional) two-layer: split (x_o, w_o) via splitting RoK -> ℓ statements;
   decompose (k_b ≤ 4) -> ℓ·k_b low-norm linear statements; fold + compile again
```

### 5.1 Figure 1 — $\Pi_{\mathrm{had}}$: Hadamard RoK

**Statement.** $(x=c,\ w=F)\in R_{\mathrm{had}}^{\mathrm{aux}}$ ($\mathrm{aux}=(n_{\mathrm{in}}=0,(M_i\in\mathbb{Z}_q^{m\times n})_{i=1}^3)$, $m$ a power of two) → $x_o=(c,r\in K^{\log m},v\in E^3)$, $w_o=\mathrm{cf}^{-1}(F)\in R_q^n$.

1. **V→P:** send $s\leftarrow K^{\log m}$ and $\alpha\leftarrow K$.
2. **P↔V:** sumcheck for the claim
   $$\sum_{b\in\{0,1\}^{\log m}}\ \sum_{j=1}^{d}\alpha^{j-1}\cdot f_j(b)=0\qquad(\text{Eq. 24})$$
   where $f_j(X)=\mathrm{eq}(s,X)\cdot\big(g_{1,j}(X)g_{2,j}(X)-g_{3,j}(X)\big)$ and $g_{i,j}=\mathrm{MLE}$ of $M_iF_{*,j}\in\mathbb{Z}_q^m$. Reduces to $\sum_j\alpha^{j-1}f_j(r)=v_{\mathrm{ev}}$ with challenge $r\leftarrow K^{\log m}$ and prover value $v_{\mathrm{ev}}\in K$.
3. **P→V:** send $U\in K^{3\times d}$, $U_{i,j}:=g_{i,j}(r)$.
4. **V:** compute $\mathrm{eq}(s,r)$ and check
   $$\sum_{j=1}^{d}\alpha^{j-1}\cdot\mathrm{eq}(s,r)\cdot\big(U_{1,j}\cdot U_{2,j}-U_{3,j}\big)\stackrel?=v_{\mathrm{ev}}.\qquad(\text{Eq. 25})$$
   Abort on failure; else output $x_o:=(c,r,v\in E^3)$ where $v_i\in E$ is the polynomial with coefficients $U_{i,*}$.
5. **P:** output $w_o:=\mathrm{cf}^{-1}(F)$.

**Knowledge error:** $(d+\log m)/|K|+\epsilon_{\mathrm{sum}}+\epsilon_{\mathrm{bind}}$ (union of Bad_bind/Bad_sum/Bad_had; Bad_had via Schwartz–Zippel over $s$ then $\alpha$).
**Costs (Prop 3.2):** one degree-3 sumcheck over $K$ of size $m$; extra prover: $3d$ inner products $\mathbb{Z}_q^m\otimes K^m$ (for $U$) + computing $(M_iF)_i$ ($O((m+n)d)$ $\mathbb{Z}_q$-mults if sparse); verifier $O(d+\log m)$ $K$-ops; randomness $O(\log m)$ $K$-elements.

### 5.2 Appendix A — $\Pi_{\mathrm{mon}}$: monomial RoK (simplified from LatticeFold+)

**Statement.** $(x=c,\ w=g\in R_q^n)\in R_{\mathrm{mon},1}$ → $(x_o=(r\in K^{\log n},c,u\in E),\ w_o=g)\in R_{\mathrm{batchlin},1}$.

1. **V→P:** send $c\leftarrow K^{\log n}$ and $\beta\leftarrow K$.
2. **P↔V:** define $v_{g,\beta}:=(\mathrm{ev}_{g_1}(\beta),\dots,\mathrm{ev}_{g_n}(\beta))\in K^n$ and $v_{g,\beta^2}$ analogously; run sumcheck for
   $$\sum_{b\in\{0,1\}^{\log n}}\mathrm{eq}(c,b)\cdot\big(\hat v_{g,\beta}(b)^2-\hat v_{g,\beta^2}(b)\big)=0\qquad(\text{Eq. 59})$$
   reducing to $\mathrm{eq}(c,r)\cdot\big(\hat v_{g,\beta}(r)^2-\hat v_{g,\beta^2}(r)\big)\stackrel?=v$ with challenge $r\leftarrow K^{\log n}$, value $v\in K$.
3. **P→V:** send $u=\hat g(r)=\langle g,\mathrm{ts}(r)\rangle\in E$.
4. **V:** check $\mathrm{eq}(c,r)\cdot\big(\mathrm{ev}_u(\beta)^2-\mathrm{ev}_u(\beta^2)\big)\stackrel?=v$ (Eq. 60). Abort on failure.
5. **Output:** $(x_o=(r,c,u),g)\in R_{\mathrm{batchlin},1}$.

**Soundness core:** Lemma A.1 — monomial ⇒ identity holds identically; non-monomial passes w.p. $<2d/|K|$; the sumcheck + $c$-challenge batch the $n$ membership tests into one claim.
**Costs (Lemma 3.1):** one degree-3 sumcheck over $K$ of size $n$; prover $O(nk_g)$ $K$-adds + $O(n)$ $K$-ops; verifier $O(k_gd+\log n)$ $K$-ops. Generalizes to $k_g$ vectors sharing one challenge $r$.

### 5.3 Figure 2 — $\Pi_{\mathrm{rg}}$: approximate range proof for ring vectors

**Statement.** $(x=c,\ w=f\in R_q^n)\in R_{\mathrm{rg}}^{\ell_h,B}$ → $(x_o,x_{\mathrm{bat}})$ with $x^*=(c,r\in K^{\log m},v\in E)$ and $x_{\mathrm{bat}}=((r,s)\in K^{\log n},[c^{(i)}\in\mathcal{C},u^{(i)}\in E]_{i=1}^{k_g})$; $w_o=(f,(g^{(i)}\in\mathbb{M}^n)_{i=1}^{k_g})$.

1. **V→P:** send the projection matrix $J\leftarrow\chi^{\lambda_{\mathrm{pj}}\times\ell_h}$.
2. **P:** compute $H:=(I_{n/\ell_h}\otimes J)\times\mathrm{cf}(f)\in\mathbb{Z}_q^{m\times d}$. **Abort if $\|H\|_\infty>B_{d,k_g}$.** Otherwise decompose
   $$H=H^{(1)}+d'H^{(2)}+\cdots+d'^{\,k_g-1}H^{(k_g)},\qquad\|H^{(i)}\|_\infty\le d'/2,\qquad(\text{Eq. 32})$$
   and flatten each $h^{(i)}:=\mathrm{flt}(H^{(i)})\in\mathbb{Z}_q^{md}$.
3. **P→V:** for $i\in[k_g]$ send $c^{(i)}:=A\times g^{(i)}\in\mathcal{C}$ where $g^{(i)}:=\mathrm{Exp}(h^{(i)})\in\mathbb{M}^n$.
4. **P↔V:** run $\Pi_{\mathrm{mon}}$ (Lemma 3.1) on $((c^{(i)})_{i=1}^{k_g},(g^{(i)})_{i=1}^{k_g})$:
   - $r\leftarrow K^{\log m}$ = challenges of the first $\log m$ rounds; $s\leftarrow K^{\log d}$ = last $\log d$ rounds;
   - $u^{(i)}:=\langle\mathrm{ts}(r\|s),g^{(i)}\rangle\in E$; reduces to $(x_{\mathrm{bat}},(g^{(i)}))\in R_{\mathrm{batchlin},k_g}$ (Eq. 27).
5. **P→V:** send $v\in E$ defined by $\mathrm{cf}(v)=H^\top\mathrm{ts}(r)\in K^d$.
6. **V:** for $i\in[k_g]$ extract $ut_1^{(i)},\dots,ut_d^{(i)}\in K^d$ = coefficients of $u^{(i)}\cdot t(X)\in E$ over $K$; **reject if**
   $$\sum_{i\in[k_g]}d'^{\,i-1}\cdot ut_1^{(i)}\ \neq\ \langle\mathrm{ts}(s),\mathrm{cf}(v)\rangle.$$
7. **V:** output $x_o:=(x^*,x_{\mathrm{bat}})$.
8. **P:** output $w_o=(f,(g^{(i)})_{i=1}^{k_g})$.

**Completeness chain (Lemma 3.2):** $\|H\|_\infty\le9.5B\le B_{d,k_g}$ w.p. $1-\epsilon$ (projection lemma + union bound); $u^{(i)}\cdot t(X)=\langle\mathrm{ts}(r\|s),\mathrm{Exp}(h^{(i)})\cdot t(X)\rangle$ and its constant term is $\langle\mathrm{ts}(s),H^{(i)\top}\mathrm{ts}(r)\rangle$ (Lemma 2.1); the Step-6 check is exactly $\langle\mathrm{ts}(s),H^\top\mathrm{ts}(r)\rangle=\langle\mathrm{ts}(s),\mathrm{cf}(v)\rangle$.
**Knowledge soundness (Lemma 3.3, the delicate part):** extractor runs `Estimate` on $P^*$; then **resamples $J$ until** $\lnot\mathrm{Bad}_{\mathrm{proj}}(\hat f,J)$ (i.e. the fixed-J success prob stays $\ge\epsilon_{P^*}/(2(1+\delta))$) — each resample succeeds w.p. $\ge1/\mathrm{poly}$ by Lemma 2.2 Eq. (6); then one more simulation with the *same fixed* $J$ and fresh remaining randomness; if it outputs exactly $(f,(g^{(i)}))$, Schwartz–Zippel over the fresh $r,s$ forces $H=H^{(1)}+d'H^{(2)}+\dots$ (Eq. 34) contradicting $\|H\|_\infty>B_{d,k_g}$. Bad events: $\mathrm{Bad}_{\mathrm{bind}}$ (relaxed binding), $\mathrm{Bad}_{\mathrm{mon}}$ (Lemma 3.1), $\mathrm{Bad}_{\mathrm{rg}}$ (the S-Z step).
**Theorem 3.1:** RoK w.r.t. relaxed input $R_{\mathrm{rg}}^{\ell_h,B'}$, $B'=16B_{d,k_g}/\sqrt{30}$; completeness error $\epsilon\approx n\lambda_{\mathrm{pj}}d/(\ell_h\cdot2^{141})$.
**Costs (Prop 3.3):** one degree-3 sumcheck over $K$ of size $n$; prover: $nd\lambda_{\mathrm{pj}}$ low-norm $\mathbb{Z}$-adds (Step 2), $O(k_g\kappa n)$ $R_q$-adds (Step 3), $O(n)$ $K$-ops (Step 5) + $T_p^{\mathrm{mon}}$; verifier: $k_gt$ $R_q$-ops, $k_g+d$ $K$-ops + $T_v^{\mathrm{mon}}$; randomness $\lambda_{\mathrm{pj}}\ell_h$ bits + $\Pi_{\mathrm{mon}}$'s.

### 5.4 Figure 3 — $\Pi_{\mathrm{gr1cs}}$: single-instance reduction (interleaving $\Pi_{\mathrm{rg}}$ and $\Pi_{\mathrm{had}}$)

**Statement.** $(x=(c,X_{\mathrm{in}}),w=W)\in R_{\mathrm{gr1cs}}^{\mathrm{aux}}$ → $(x_o=(x^*,x_{\mathrm{bat}}),w_o)\in R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},k_g}$.

1. **V→P:** send, in one batch: $J\leftarrow\chi^{\lambda_{\mathrm{pj}}\times\ell_h}$ (for $\Pi_{\mathrm{rg}}$ Step 1), $s'\leftarrow K^{\log m}$ and $\alpha\leftarrow K$ (for $\Pi_{\mathrm{had}}$ Step 1).
2. **P→V:** send the helper monomial commitments $(c^{(i)}:=A\times g^{(i)})_{i=1}^{k_g}$ ($\Pi_{\mathrm{rg}}$ Step 3).
3. **P↔V:** run **two sumchecks in parallel** — the $\Pi_{\mathrm{had}}$ claim (Eq. 24) with $\log m$ rounds and the $\Pi_{\mathrm{mon}}$ claim ($\Pi_{\mathrm{rg}}$ Step 4) with $\log n$ rounds — **sharing the challenge stream**
   $$(\bar r\in K^{\log(m_J)},\ \bar s\in K^{\log(m)-\log(m_J)},\ s\in K^{\log(n)-\log(m)})$$
   so that $(\bar r,\bar s)$ serve as $\Pi_{\mathrm{had}}$'s $(r)$ and $(\bar r,\bar s,s)$ as $\Pi_{\mathrm{mon}}$'s $(r\|s)$.
4. **P↔V:** execute the remainder of $\Pi_{\mathrm{had}}$ and $\Pi_{\mathrm{rg}}$: $\Pi_{\mathrm{had}}$ outputs $(c,(\bar r,\bar s),v'\in E^3,f)$; $\Pi_{\mathrm{rg}}$ outputs $((c,\bar r,v),x_{\mathrm{bat}},(f,(g^{(i)})))$.
5. **V:** output $x_o=(x^*,x_{\mathrm{bat}})$ where $x^*=(c,\ x_{\mathrm{in}}:=\mathrm{cf}^{-1}(X_{\mathrm{in}}),\ r:=(\bar r,\bar s),\ v:=(v',v)\in E^4)$.
6. **P:** output $w_o=w_{\mathrm{rg},o}=(f,(g^{(i)}))$.

**Lemma 4.1:** RoK $R_{\mathrm{gr1cs}}^{\mathrm{aux}}\to R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},k_g}$ w.r.t. relaxed $R_{\mathrm{gr1cs}}^{\mathrm{aux}'}$ ($B' = 16B_{d,k_g}/\sqrt{30}$); completeness error = that of $\Pi_{\mathrm{rg}}$.
**Costs (Prop 4.1):** two degree-3 sumchecks over $K$ (sizes $n$, $m$); $T_p^{\mathrm{gr1cs}}=T_p^{\mathrm{had}}(m)+T_p^{\mathrm{rg}}(k_g,n)$; verifier and randomness additive.

### 5.5 Figure 4 — $\Pi_{\mathrm{fold}}$: the high-arity folding scheme (Parts I + II)

**Statement.** $\ell_{\mathrm{np}}$ input instance-witness pairs $(x_\ell=(c_\ell,X^{\ell}_{\mathrm{in}}),\ w_\ell=W_\ell)_{\ell=1}^{\ell_{\mathrm{np}}}$ of $R_{\mathrm{gr1cs}}^{\mathrm{aux}}$, with $f^\ell:=\mathrm{cf}^{-1}([X^{\ell\top}_{\mathrm{in}},W_\ell^\top]^\top)$ → one folded pair $(x_o=(x^*,x_{\mathrm{bat}}),\ w_o=(f^*,(g^{*(i)})_{i=1}^{k_g}))\in R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},k_g}$.

**Part I (Figure 4, steps 1–3):**

*(Why the merge works: every per-instance sumcheck claim has the form “$\sum_b \mathrm{(degree\le3\ poly}_\ell)(b)=0$”; multiplying the $\ell$-th claim by $\alpha^{(\ell-1)d+j-1}$-style powers and summing preserves both the total (0) and the per-round structure, so the two merged sumchecks have degree ≤ 3 and sizes $m$, $n$ regardless of $\ell_{\mathrm{np}}$ — the sumcheck cost is **independent of the folding arity after batching** (footnote 11). The verifier's Step-3 consistency check is then exactly: the merged leaf values $e^*,u^*$ equal the same random combination of the per-instance leaf values $(v_\ell),(u_\ell^{(i)})$ that the folded instance will later linear-combine with $\beta$ — one $K$-arith identity per instance, $O(\ell_{\mathrm{np}})$ total.)*

1. **P↔V:** run $\ell_{\mathrm{np}}$ parallel instances of $\Pi_{\mathrm{gr1cs}}$, the $\ell$-th taking $(x_\ell,w_\ell)$, with three optimizations:
   - **shared challenges:** the same $J,s',\alpha$ across all $\ell_{\mathrm{np}}$ executions;
   - **merged sumchecks:** the $2\ell_{\mathrm{np}}$ sumcheck claims merge into **two**:
     - 1st claim (Eq. 45):
       $$\sum_{b\in\{0,1\}^{\log m}}\sum_{\ell=1}^{\ell_{\mathrm{np}}}\sum_{j=1}^{d}\alpha^{(\ell-1)d+j-1}\cdot f^{\ell,j}(b)=0,$$
       where $f^{\ell,j}(X)=\mathrm{eq}(s',X)\cdot\big(g_1^{\ell,j}(X)g_2^{\ell,j}(X)-g_3^{\ell,j}(X)\big)$, $g_i^{\ell,j}=\mathrm{MLE}$ of $M_i\mathrm{cf}(f^\ell)_{*,j}$;
     - 2nd claim: the $\Pi_{\mathrm{mon}}$ claims of all instances randomly combined with powers of $\alpha$;
     - 1st sumcheck: $\log m$ rounds; 2nd: $\log n$ rounds; shared challenge $(\bar r,\bar s,s)$ as in $\Pi_{\mathrm{gr1cs}}$;
   - the two sumchecks reduce to evaluation values $e^*\in E$ (1st) and $u^*\in E$ (2nd).
2. **P↔V:** the $\ell$-th execution of $\Pi_{\mathrm{gr1cs}}$ has been reduced to $(x_{o,\ell}=(x^*_\ell,x_{\mathrm{bat},\ell}),w_{o,\ell})$ (Eqs. 46–47):
   $x^*_\ell=(c_\ell,\mathrm{cf}^{-1}(X^\ell_{\mathrm{in}}),(\bar r,\bar s),v_\ell\in E^4)$, $x_{\mathrm{bat},\ell}=((\bar r,\bar s,s),[c_\ell^{(i)},u_\ell^{(i)}\in E]_{i=1}^{k_g})$, $w_{o,\ell}=(f^\ell,(g^{i,\ell})_{i=1}^{k_g})$.
3. **V:** check that the evaluations $(v_\ell)_{\ell=1}^{\ell_{\mathrm{np}}}$ and $(u_\ell^{(i)})_{i\in[k_g],\ell}$ are **consistent with $e^*,u^*$** according to Eq. (45) and the randomly-combined monomial claim (i.e., the merged-leaf identities hold).

**Part II (Figure 4, steps 4–6):**

4. **V→P:** send the low-norm folding challenge $\beta\leftarrow S^{\ell_{\mathrm{np}}}$.
5. **V:** set $x^*:=(c^*\in\mathcal{C},\ x^*_{\mathrm{in}}\in R_q^{n_{\mathrm{in}}},\ (\bar r,\bar s)\in K^{\log m},\ v^*\in E^4)$ where
   $$(c^*,\ x^*_{\mathrm{in}},\ v^*):=\sum_{\ell=1}^{\ell_{\mathrm{np}}}\beta^\ell\cdot(c_\ell,\ \mathrm{cf}^{-1}(X^\ell_{\mathrm{in}}),\ v_\ell),$$
   and $x_{\mathrm{bat}}:=((\bar r,\bar s,s),[c^{(i)}\in\mathcal{C},u^{(i)}\in E]_{i=1}^{k_g})$ with, for $i\in[k_g]$:
   $$(c^{(i)},\ u^{(i)}):=\sum_{\ell=1}^{\ell_{\mathrm{np}}}\beta^\ell\cdot(c_\ell^{(i)},\ u_\ell^{(i)}).\qquad(\text{Eq. 48})$$
   Output $x_o:=(x^*,x_{\mathrm{bat}})$.
6. **P:** output $w_o=(f^*\in R_q^n,(g^{*(i)}\in R_q^n)_{i=1}^{k_g})$ where
   $$f^*:=\sum_{\ell=1}^{\ell_{\mathrm{np}}}\beta^\ell f^\ell,\qquad g^{*(i)}:=\sum_{\ell=1}^{\ell_{\mathrm{np}}}\beta^\ell g^{i,\ell}.\qquad(\text{Eq. 49})$$

**Norm bookkeeping (completeness):** each $\|f^\ell\|_2\le B\sqrt{nd/\ell_h}$, each $\|g^{i,\ell}\|_2\le\sqrt n$; folded norms $\le\ell_{\mathrm{np}}\|S\|_{\mathrm{op}}B\sqrt{nd/\ell_h}$ resp. $\ell_{\mathrm{np}}\|S\|_{\mathrm{op}}\sqrt n$; valid strict openings require Eq. (50):
$$\sqrt{B_{\mathrm{rbnd}}/2}=B_{\mathrm{bnd}}\ \ge\ \ell_{\mathrm{np}}\cdot\|S\|_{\mathrm{op}}\cdot\max\big(B\sqrt{nd/\ell_h},\ \sqrt n\big)\qquad(\text{Eq. 50})$$
(a worst-case bound — Remark 4.3: symmetric $\beta$ makes real norms much smaller; concrete analysis open).
**Remark 4.1 (output compression):** since all $(g^{*(i)})_{i\in[k_g]}$ share the relation $R_{\mathrm{batchlin},1}$-compatible structure, fold them into a single vector: $(R_{\mathrm{gr1cs}}^{\mathrm{aux}})^{\ell_{\mathrm{np}}}\to R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},1}$.
**Remark 4.2 (memory-efficient prover):** $O(\log\log n)$ passes; (1) stream-compute the $\ell_{\mathrm{np}}$ input commitments, get first-round challenges; (2) after $\alpha$, run the [Baw+25] §4 streaming sumcheck: per pass linearly combine per-instance evaluation tables — time $O(n\log\log n)$ + table-combining (dominant); (3) after $\beta$, re-stream witnesses and combine into $f^*,g^{*(i)}$.

### 5.6 Section 5 — Fiat–Shamir: Commit-and-Open + FS on a compressed transcript

- **$\mathrm{CM}[\Pi_{\mathrm{cm}},\Pi_{\mathrm{rok}}]$ (Commit-and-Open):** replace each prover round message $m_i$ ($i\in[\mathrm{rnd}]$) of the $(2\mathrm{rnd}{+}1)$-message public-coin RoK by a commitment $c_i:=\Pi_{\mathrm{cm}}.\mathrm{Commit}(\mathrm{pp},m_i)$; at the end the prover *also* sends the openings $(m_i)_{i=1}^{\mathrm{rnd}}$; the verifier runs the original RoK verifier on $(m_i)$ + challenges and checks the openings. Still an RoK with same relations (Protostar-style argument).
- **$\mathrm{FS}^H[\Pi_{\mathrm{cm}},\Pi_{\mathrm{rok}}]$:** transcript starts with $x$; $r_1:=H(x)$; each round appends $(r_i,c_i=\Pi_{\mathrm{cm}}.\mathrm{Commit}(m_i))$ and $r_{i+1}$ is derived from the transcript. The *folding proof* includes openings $(m_i)$ (needed for folding verification); the *SNARK proof* of Construction 6.1 does **not**.
- **Theorem 5.1:** if $\Pi_{\mathrm{cm}}$ is binding **and straightline extractable**, $\mathrm{FS}^H[\Pi_{\mathrm{cm}},\Pi_{\mathrm{fold}}]$ is an RoK $(R_{\mathrm{gr1cs}}^{\mathrm{aux}})^{\ell_{\mathrm{np}}}\to R_{\mathrm{lin}}^{\mathrm{aux}_{\mathrm{cs}}}\times R_{\mathrm{batchlin},k_g}$ w.r.t. relaxed input. Proof (App. B): (i) committed sumchecks remain sound under FS via **round-by-round soundness** [Can+19; CMS19] (Lemma B.2: doomed-state argument, adversary must have queried $H$ on $(r_1|c_{\mathrm{fs},1}|\dots|r_i|c_{\mathrm{fs},i})$; mental experiment samples the $q$-th query, extracts $m_j$, recomputes monomial vectors from $(I_{n/\ell_h}\otimes J)\mathrm{cf}(f)$; error $\le Q(\epsilon_{\mathrm{rbr}}+\mathrm{negl})$); (ii) Lemma 2.3 replaced by the ROM CWSS variant (Lemma B.1, from [FMN24] §8.2): success $\epsilon_\Psi-(Q{+}1)\ell_{\mathrm{np}}/|S|$ with **oracle programming** $H_{\mathrm{fd}}[y_L,u_i]$ — the extractor divides out $u_\ell[\ell]-u_0[\ell]\in S-S$ (invertible) exactly as in the interactive case (Eqs. 63–64).
- **Remark 5.1:** FS multiplies knowledge error by $Q$; compensate by enlarging $K$ and $S$ — minor cost vs. witness committing.

### 5.7 Construction 6.1 — the SNARK compiler (ROM)

**Ingredients:** RoK $\Pi_{\mathrm{rok}}$ ($\mathrm{rnd}=\mathrm{poly}(\log\lambda)$ rounds, $|x_o|=\mathrm{poly}(\lambda,|x|,\log|w|)$, $\sum_{i=1}^{\mathrm{rnd}+1}|r_i|=\mathrm{poly}(\lambda,|x|,\log|w|)$); SNARK $\Pi_{\mathrm{snark}}$ for $R_o$; CP-SNARK $\Pi_{\mathrm{cp}}$ for $R_{\mathrm{cp}}$ w.r.t. straightline-extractable $\Pi_{\mathrm{cm}}$ (Merkle or KZG — **not** required to be linearly homomorphic).

- **Setup$(R)$:** $\mathrm{pp}_{\mathrm{cm}}\leftarrow\Pi_{\mathrm{cm}}.\mathrm{Setup}$; $(\mathrm{pk}_{\mathrm{cp}},\mathrm{vk}_{\mathrm{cp}})\leftarrow\Pi_{\mathrm{cp}}.\mathrm{Setup}(\mathrm{pp}_{\mathrm{cm}},R_{\mathrm{cp}})$; $(\mathrm{pk},\mathrm{vk})\leftarrow\Pi_{\mathrm{snark}}.\mathrm{Setup}(R_o)$; output $\mathrm{pk}^*=(\mathrm{pp}_{\mathrm{cm}},\mathrm{pk}_{\mathrm{cp}},\mathrm{pk})$, $\mathrm{vk}^*=(\mathrm{pp}_{\mathrm{cm}},\mathrm{vk}_{\mathrm{cp}},\mathrm{vk})$.
- **Prover$^H(\mathrm{pk}^*,R,x,w)\to\pi^*$:**
  1. transcript $\mathrm{tr}:=x$;
  2. for $i\in[\mathrm{rnd}]$: derive $r_i$ from $\mathrm{tr}$ and $H$; run $\Pi_{\mathrm{rok}}$ to get $m_i$; append $(r_i,\ c_{\mathrm{fs},i}:=\Pi_{\mathrm{cm}}.\mathrm{Commit}(\mathrm{pp},m_i))$;
  3. derive $r_{\mathrm{rnd}+1}$; run $\Pi_{\mathrm{rok}}$ to obtain $(x_o,w_o)$;
  4. compute $w_e$ s.t. $(x_{\mathrm{cp}},(w_{\mathrm{cp}},w_e))\in R_{\mathrm{cp}}$ with $w_{\mathrm{cp}}=(m_i)_{i=1}^{\mathrm{rnd}}$;
  5. $\pi_{\mathrm{cp}}\leftarrow\Pi_{\mathrm{cp}}.\mathrm{Prove}(\mathrm{pk}_{\mathrm{cp}},R_{\mathrm{cp}},x_{\mathrm{cp}},w_{\mathrm{cp}},w_e)$;
  6. $\pi\leftarrow\Pi_{\mathrm{snark}}.\mathrm{Prove}(\mathrm{pk},R_o,x_o,w_o)$;
  7. output $\pi^*:=(\pi_{\mathrm{cp}},\pi,(c_{\mathrm{fs},i})_{i=1}^{\mathrm{rnd}},x_o)$.
- **Verifier$^H(\mathrm{vk}^*,R,x,\pi^*)\to b$:** parse; **recompute $(r_i)_{i=1}^{\mathrm{rnd}+1}$ from $x,(c_{\mathrm{fs},i}),H$** (this is why challenges are *public inputs*, not proven hash computations); derive $x_{\mathrm{cp}}$; output $\Pi_{\mathrm{cp}}.\mathrm{Vf}(\mathrm{vk}_{\mathrm{cp}},R_{\mathrm{cp}},x_{\mathrm{cp}},\pi_{\mathrm{cp}})\wedge\Pi_{\mathrm{snark}}.\mathrm{Vf}(\mathrm{vk},R_o,x_o,\pi)$.

**Why no hash circuit:** the challenges $(r_i)$ are recomputed by the *SNARK verifier outside the circuit*; the CP-SNARK proves "the openings of $(c_{\mathrm{fs},i})$ form a valid folding proof w.r.t. **public** challenges" — a pure linear-algebra statement. The ROM instantiation of $H$ lives only in the outer verification.
**Remark 6.1 (instance compression):** if $x$ is large, commit to it: $c_{\mathrm{fs},0}:=\Pi_{\mathrm{cm}}.\mathrm{Commit}(x)$ (32 B Merkle / 48 B KZG); CP-SNARK treats $c_{\mathrm{fs},0}$ as instance, $x$ as witness; verifier checks consistency of $(X^\ell_{\mathrm{in}})$ with $c_{\mathrm{fs},0}$ outside the circuit.
**Remark 6.2:** one CP-SNARK can prove both $R_{\mathrm{cp}}$ and $R_o$ (drops $\pi$).
**Theorem 6.1:** Construction 6.1 is a SNARK (succinctness: $c_{\mathrm{fs},i}$ polylog-many + succinct commitments; $x_o$ succinct by assumption; verifier hashes a sublinear transcript). Knowledge soundness: SNARK extractor → CP-SNARK extractor pulls $(m_i)$ from $c_{\mathrm{fs},i}$ (straightline) + $\Pi_{\mathrm{snark}}$ extractor pulls $w_o$ → yields an adversary against $\mathrm{FS}^H[\Pi_{\mathrm{cm}},\Pi_{\mathrm{rok}}]$ → its RoK extractor outputs $w$ for the relaxed input relation.
**Corollary 6.2:** plugging $\Pi_{\mathrm{fold}}$: SNARK in ROM for $(R_{\mathrm{gr1cs}}^{\mathrm{aux}})^{\ell_{\mathrm{np}}}$ for any $\ell_{\mathrm{np}}=\mathrm{poly}(\lambda)$ satisfying Eq. (50).

### 5.8 Section 8 — splitting RoK and two-layer folding

**Splitting RoK** ($R_{\mathrm{lin}}^{\mathrm{aux}'}$ with $A=[r_1A',\dots,r_\ell A']$, $M=I_\ell\otimes M'$ → $\ell$ statements in $R'$):

1. **P→V:** for all $i\in[\ell]$ send $c_i:=A'f_i$ and $v_i:=\langle\mathrm{ts}(s),M'f_i\rangle$.
2. **V:** check $c=\sum_{i=1}^{\ell}r_i\cdot c_i$ and $\langle\mathrm{ts}(r),(v_1,\dots,v_\ell)\rangle=v$. Abort on failure.
3. **V:** output $x_i=(c_i,s,v_i)$ for $i\in[\ell]$.
4. **P:** output $w_i=f_i$.

**Two-layer folding SNARK** (batch-proves $\ell_{\mathrm{np}}\cdot\ell$ statements): (a) 1st layer packs every $\ell$ consecutive witnesses into one ($A$ structured as Eq. 56, $M_i=I_\ell\otimes M'_i$), runs $\Pi_{\mathrm{fold}}$+compiler; (b) split the folded $(x_o,w_o)\in R_o$ into $\ell$ statements in $R'_o$ via the splitting RoK; (c) **decomposition RoK** ([BC24; BC25b]) reduces the $\ell$ (large-norm) statements to $\ell\cdot k_b$ low-norm statements ($k_b\le4$) in $R'$ with fine-grained $\mathrm{VfyOpen}_{\ell_h,B'}$; (d) run high-arity folding + CP compiler again on those (no Hadamard protocol needed — inputs already linear); the CP-SNARK additionally verifies the splitting and decomposition verifier checks. **Final output: two CP-SNARK proofs + one SNARK proof.** CP-SNARK statements check $O(\ell_{\mathrm{np}}+\ell)$ instead of $O(\ell_{\mathrm{np}}\ell)$ $R_q$-mults; smaller norm blowup ⇒ smaller modulus/dimension; price: MSIS must hold for the structured $A$ (Eq. 56), and sumchecks become $\ell\times$ larger — again handled by [Baw+25] streaming: time $O(n'\ell\log\log(n'\ell))$, space $O((n'\ell)^{1/k})$, $O(k+\log\log(n'\ell))$ passes.

---

## 6. Soundness & Security

### 6.1 Theorem/lemma inventory

| # | Statement (informal) | Error / assumption |
|---|---|---|
| Lemma 2.1 | $\mathrm{ct}(\mathrm{Exp}(a)\cdot t(X))=a$; converse forces $a\in(-d/2,d/2)$ | exact |
| Lemma 2.2 | random projection preserves norm | $\lesssim2^{-141}$ / $\lesssim2^{-128}$ |
| Lemma 2.3 / B.1 | CWSS extractor (interactive / ROM) | $\ell/|S|$ / $(Q{+}1)\ell/|S|$ |
| Lemma 3.1 / A.1 | monomial RoK | $2d/|K|$ per element, batched |
| Prop 3.1 | $\Pi_{\mathrm{had}}$ RoK | $(d{+}\log m)/|K|+\epsilon_{\mathrm{sum}}+\epsilon_{\mathrm{bind}}$ |
| Thm 3.1 | $\Pi_{\mathrm{rg}}$ RoK w.r.t. relaxed $R^{\ell_h,B'}_{\mathrm{rg}}$, $B'=16B_{d,k_g}/\sqrt{30}$ | completeness $\epsilon\approx n\lambda_{\mathrm{pj}}d/(\ell_h2^{141})$; soundness via extractor below |
| Lemma 4.1 | $\Pi_{\mathrm{gr1cs}}$ RoK w.r.t. relaxed $R^{\mathrm{aux}'}_{\mathrm{gr1cs}}$ | negligible |
| **Thm 4.1** | $\Pi_{\mathrm{fold}}$ RoK $(R^{\mathrm{aux}}_{\mathrm{gr1cs}})^{\ell_{\mathrm{np}}}\to R^{\mathrm{aux}_{\mathrm{cs}}}_{\mathrm{lin}}\times R_{\mathrm{batchlin},k_g}$ w.r.t. relaxed input; needs Eq. (50) and $|S|=\omega(\mathrm{poly})$, $S-S$ invertible | completeness $\ell_{\mathrm{np}}\epsilon$; KS error $\ell_{\mathrm{np}}/|S|+\ell_{\mathrm{np}}\cdot\mathrm{negl}$ |
| **Thm 5.1** | $\mathrm{FS}^H[\Pi_{\mathrm{cm}},\Pi_{\mathrm{fold}}]$ RoK (needs straightline extractability of $\Pi_{\mathrm{cm}}$) | error × $Q$ |
| Lemma B.2 | FS'd $\Pi_{\mathrm{gr1cs}}$ sound via round-by-round soundness | $\le Q(\epsilon_{\mathrm{rbr}}+\mathrm{negl})$ per round transition |
| **Thm 6.1** | Construction 6.1 is a SNARK | inherits all above |
| Cor 6.2 | ROM SNARK for $(R^{\mathrm{aux}}_{\mathrm{gr1cs}})^{\ell_{\mathrm{np}}}$ | Eq. (50) |

### 6.2 Extractor logic — the two templates

**Template A (Theorem 4.1, interactive folding; CWSS):** predicate $\Psi(u,y)$ = "transcript accepting with folding challenge $u$ AND output in target relation". Fix extra verifier randomness $r_v$; $A_{r_v}(u)$ simulates $P^*$ at challenge $u$. Run the Lemma-2.3 oracle extractor → $\ell_{\mathrm{np}}{+}1$ transcripts with $u_\ell\equiv_\ell u_0$. Per coordinate divide out the invertible difference:
$$f^\ell:=(f^{*,\ell}-f^{*,0})/(u_\ell[\ell]-u_0[\ell]),\qquad h^{i,\ell}:=(g^{(i,\ell)}-g^{(i,0)})/(u_\ell[\ell]-u_0[\ell]).$$
Each $f^\ell$ opens $c_\ell$ *relaxedly* with slack $u_\ell[\ell]-u_0[\ell]\in S-S$; the folded-relation checks then transfer to the relaxed relations $\hat R_{\mathrm{lin}},\hat R_{\mathrm{batchlin}}$; union bound + Lemma 4.1-style argument gives witnesses $(W_\ell)_{\ell=1}^{\ell_{\mathrm{np}}}$ for the (relaxed) input relation; abort if the public prefix $X^\ell\neq X^\ell_{\mathrm{in}}$.

**Template B (Theorem 3.1, $\Pi_{\mathrm{rg}}$; the $J$-resampling extractor):** the subtlety — after rewinding, the monomial commitments of the second simulation depend on the *unpredictable* $J$, so one cannot directly fix $g$ across simulations. Solution: (1) `Estimate` the success probability; (2) **resample $J$ until** the fixed-$J$ success probability stays $\ge\epsilon_{P^*}/(2(1+\delta))$ *and* $\lnot\mathrm{Bad}_{\mathrm{proj}}$ (each try succeeds w.p. $\ge(\epsilon/2-2^{-\lambda})-2^{-\lambda}=1/\mathrm{poly}$ by Lemma 2.2 Eq. (6)); (3) only then rewind with that **fixed** $J$ and fresh remaining randomness; (4) if the last simulation outputs exactly $(f,(g^{(i)}))$, then Schwartz–Zippel over fresh $r,s$ (fixed witnesses) forces the decomposition identity (Eq. 34), contradiction with $\|H\|_\infty>B_{d,k_g}$. Expected polytime via the $2^\lambda$ cap on $P^*$ calls.

### 6.3 Security anchors & FS discipline

- **MSIS$_{q,\kappa,n,\beta_{\mathrm{SIS}}}$** for the Ajtai commitment (concrete 117-bit via lattice estimator); two-layer adds the *structured*-MSIS assumption on $A=[r_1A',\dots,r_\ell A']$.
- **ROM**: $H$ and $H_{\mathrm{fd}}$ domain-separated; FS knowledge error ×$Q$ — enlarge $K$ and $S$ to compensate (sets sized $>2^{128}\cdot Q$).
- **No oracle-in-circuit**: the security proof does *not* require the proven statement to compute $H$ — this is both an efficiency and a security feature (contrast [KRS25] attacks on GKR-based SNARKs that let the statement compute the FS hash).
- **Straightline extractability of $\Pi_{\mathrm{cm}}$** (Merkle/KZG in idealized models) — Remark B.1 conjectures plain binding suffices; open problem.

### 6.4 The IVC/PCD alternative — when Symphony is the right tool

The paper's framing replaces the IVC/PCD recipe ("fold an accumulated statement with an online statement that checks the step function *and the previous folding step*") with a batch recipe ("reduce $\ell_{\mathrm{np}}$ statements to one linear statement in a single interaction, then prove that linear statement once"):

| Property | IVC/PCD from folding | **Symphony (high-arity + compiler)** |
|---|---|---|
| What the prover proves per unit work | one step + folding-verification circuit (incl. FS hash over $R_q$) | one fold of $\ell_{\mathrm{np}}$ statements + one CP-SNARK over *linear* checks |
| Random oracle instantiation inside statements | required | **never** (challenges are public inputs; $H$ lives in the outer verifier) |
| Folding depth | must be constant (rewinding-based security; [LS24; BMNW25a] attacks beyond) | 1 (or 2 with two-layer); depth is architectural, not a soundness budget |
| Witness arrival | fully online (statements can arrive over time) | batch known upfront (streaming *over* the batch; $O(\log\log n)$ passes) |
| Final proof | IVC proof, polylog verifier | SNARK, polylog per *block*; verifier linear in $\ell_{\mathrm{np}}$ (per statement) |
| Parallelism | limited by chain/tree shape | fold is embarrassingly parallel across $\ell_{\mathrm{np}}$ until the merge |

**Guidance for the lab:** implement both paths on the same core (`lzk`): Cyclo covers the streaming/IVC-shaped workloads (sequential branches, bounded rounds, refresh); Symphony covers the batch workloads (aggregate signatures, SIMD/ML inference batches, video provenance) where all statements are known and the prover is memory-bound. The two share: Ajtai commitments, $R_q$ arithmetic, sumcheck, CWSS forking, monomial/table machinery, and the $\theta_k/\varphi$ digit packing — the lab's real differentiation is the *compiler* (Construction 6.1), which is unique to Symphony.

### 6.5 Knowledge-soundness skeleton (shared template)

All extractor proofs in the paper reduce to one of two templates (already detailed in §6.2): (A) CWSS coordinate-wise forking + division by invertible challenge differences — used by $\Pi_{\mathrm{fold}}$ and its FS compile; (B) rewind-with-fixed-$J$ + Schwartz–Zippel over the remaining randomness — used by $\Pi_{\mathrm{rg}}$ (the $J$-resampling subtlety). Everything else (binding, monomial membership, Hadamard) plugs into these as "bad events" with negligible probabilities. When porting proofs to the lab's security-review docs, keep the two templates as reusable lemmas and instantiate the bad-event inventory per protocol.

---

## 7. Parameters & Concrete Efficiency

### 7.1 Table 1 — candidate instantiation (117-bit MSIS)

| Variable | Description | Instantiation |
|---|---|---|
| $q$ | prime modulus | 64-bit prime |
| $d$ | ring dimension & R1CS batching factor | 64 |
| $\kappa$ | MSIS rank | 12 |
| $\beta_{\mathrm{SIS}}$ | MSIS $\ell_2$ bound | $2^{37}$ |
| $K$ | sumcheck extension field | $\mathbb{F}_{q^2}$ |
| $\ell_{\mathrm{np}}$ | folding arity | $2^{10}$ |
| $\ell_h$ | projection input length | $2^{14}$ |
| $\lambda_{\mathrm{pj}}$ | projection output length | $2^8$ (256) |
| $\bar n$ | R1CS witness length per instance | $2^{16}$ |
| $m$ | #constraints per instance | $2^{16}$ |
| $k_{\mathrm{cs}}$ | R1CS decomposition factor | 16 |
| $b$ | decomposition base | $2^4$ (16) |
| $n$ | generalized witness length | $\bar nk_{\mathrm{cs}}=2^{20}$ |
| $S$ | folding challenge set | as in [BS23], $\|S\|_{\mathrm{op}}\le15$ |
| $B_{\mathrm{rbnd}}$ | relaxed opening bound | $\beta_{\mathrm{SIS}}/(4\|S\|_{\mathrm{op}})\approx2^{31}$ |
| $B_{\mathrm{bnd}}$ | strict opening bound (Eq. 50) | $2^{30}$ |
| $k_g$ | #monomial vectors | 3 |
| $B_{d,k_g}$ | range digit bound (Eq. 28) | $121117=31\cdot(1+62+62^2)$ |
| $B$ | input witness norm bound | $2^{10}$ ($=0.5\cdot16\cdot\sqrt{2^{14}}$, and $\le B_{d,k_g}/9.5$) |
| $B'$ | relaxed input bound | $16B_{d,k_g}/\sqrt{30}\approx353806$ |

### 7.2 Derived costs (Propositions 4.2, 6.1 + §7 estimates)

- **Prover time (dominant):** $\kappa n\ell_{\mathrm{np}}=3\cdot2^{32}$ multiplications of arbitrary $R_q$-elements with bounded elements ($\ell_\infty\le0.5b=8$) — the $\ell_{\mathrm{np}}$ input Ajtai commitments. Plus: $n\ell_{\mathrm{np}}$ mults $S\times R_q$ (fold $f^*$), $k_gn\ell_{\mathrm{np}}$ mults $S\times\mathbb{M}$ (fold $g^{*(i)}$), $\ell_{\mathrm{np}}\cdot T_p^{\mathrm{gr1cs}}$, SNARK proving, $[\mathrm{rnd}]$ outer commitments.
- **Batch proven:** $\ell_{\mathrm{np}}\cdot d=2^{16}$ R1CS statements over $\mathbb{Z}_q$, each $2^{16}$ constraints ⇒ $2^{32}$ constraints total; in principle arity $2^{14}$ (a million statements, a billion RISC-V instructions at 1k instr/statement) with larger moduli/dimensions.
- **CP-SNARK circuit ($\Pi_{\mathrm{cp}}$):** folding-verifier logic $T_v^{\mathrm{fold}}$ ≈ $2^{16}$–$2^{17}$ mults between $S$ and $R_q$ under Table 1.
- **Inner SNARK circuit ($\Pi_{\mathrm{snark}}$, relation $R_o$):** $k_g$ inner products $\mathbb{M}^n\times K^n$, 3 inner products $R_q^m\times K^m$, 1 inner product $R_q^{m_J}\times K^{m_J}$ ⇒ ≈$2^{25}$ constraints over $\mathbb{Z}_q$ — "just 7 polynomial evaluation proofs".
- **Proof size:** $\log n+O(1)$ $\mathcal{C}_{\mathrm{FS}}$-elements, $1+k_g$ $\mathcal{C}_{\mathrm{fold}}$-elements ($R_q^\kappa$), $4+k_g$ $E$-elements, $n_{\mathrm{in}}$ $R_q$-elements, two SNARK proofs ⇒ **< 200 KB PQ** (WHIR/LaBRADOR 50–100 KB each), **< 50 KB** with Hyperplonk+KZG.
- **Verifier:** two SNARK verifications + FS over a $\log n+O(1)$-element transcript + randomness $\Gamma_v^{\mathrm{fold}}$; FS randomness dominated by the projection matrix $\le2\ell_h\lambda_{\mathrm{pj}}=2^{23}$ bits (≈1 MB, SHA-3 < 1 ms) — but the CP-SNARK takes it as public input, so verification is linear in those bits (open problem).
- **Prover memory:** $O(n)$ — one statement's witness (Remark 4.2); $O(\log\log n)$ passes over input.
- **Remark 7.1:** natively low-norm witnesses (e.g. 8-bit signed integers in ML inference) shrink $k_{\mathrm{cs}}$ ⇒ up to 8× speedup.

### 7.3 Comparison table (from §1.1–1.3)

| Aspect | IVC/PCD from folding | **Symphony** |
|---|---|---|
| Random oracle in circuit | yes (FS hash over $R_q$; SHA-256 ≈10⁴ R1CS constraints) | **no** |
| Folding arity | 2–3 (hash circuit cost) | $2^{10}$–$2^{14}$ |
| Security model | heuristic after instantiation | ROM proof |
| Streaming | fully online | known-batch streaming, $O(\log\log n)$ passes |
| Verifier | polylog | **linear in #statements** |
| vs. monolithic low-memory SNARKs | — | modular (swap folders/CP-SNARKs), scales $O_\lambda(\ell n)$; Gemini quasilinear-time, LaBRADOR $\Omega(n\ell^2)$ cross terms, [Baw+24] $O(\ell n)$ EC ops |

### 7.4 Proof-size budget, itemized (Table 1, $n_{\mathrm{in}}=0$)

| Component | Count | Bits each | Bytes |
|---|---|---|---|
| $c_{\mathrm{fs},i}$ (outer commitments, $\mathrm{rnd}=O(\log n)$ rounds) | $\log n+O(1)\approx20$ | 256 (Merkle root) | ≈640 |
| Folded commitments $c^*,c^{(i)}$ ($R_q^\kappa$) | $1+k_g=4$ | $\kappa\cdot d\cdot64=12\cdot64\cdot64$ | ≈24.6 KB |
| Evaluations $v^*,u^{(i)}\in E$ | $4+k_g=7$ | $d\cdot2\cdot64$ | ≈3.6 KB |
| $\pi_{\mathrm{cp}}$ (CP-SNARK, WHIR/LaBRADOR-class) | 1 | — | 50–100 KB |
| $\pi$ (inner SNARK for $R_o$) | 1 | — | 50–100 KB |
| **Total (PQ)** | | | **< 200 KB** |
| With Hyperplonk+KZG for both SNARKs (non-PQ) | | | **< 50 KB** |

The $R_q^\kappa$ commitment items dominate the non-SNARK part — Remark 6.2 (single CP-SNARK proving $R_{\mathrm{cp}}\wedge R_o$) and the LatticeFold+-style double-commitment compression are the natural follow-up optimizations.

### 7.5 Scaling beyond $2^{32}$ constraints

- **Higher arity in principle:** $\ell_{\mathrm{np}}=2^{14}$ batches >1M statements (a billion RISC-V instructions at 1k instr/statement); cost: norm blowup in Eq. (50) grows linearly in $\ell_{\mathrm{np}}$ ⇒ larger $q$/$\kappa$, and the CP-SNARK must prove more $S\times R_q$ mults.
- **Two-layer (Section 8):** layer-1 folds $\ell_{\mathrm{np}}$ packed statements; the splitting RoK unpacks to $\ell$ mid-size statements; layer-2 folds $\ell\cdot k_b$ decomposed statements. CP-SNARK work drops from $O(\ell_{\mathrm{np}}\ell)$ to $O(\ell_{\mathrm{np}}+\ell)$ $R_q$-mults; norm blowup per layer stays small ⇒ smaller $q$/$\kappa$ than a single-layer equivalent.
- **Hybrid with recursive SNARKs (the paper's own fallback for full succinctness/streaming):** partition online statements into blocks of $\ell_{\mathrm{np}}$; Symphony per block; a recursive SNARK absorbs Symphony's (linear) verification. Oracles enter the *outer* recursive statements only — much cheaper than naive IVC/PCD, and Symphony's own core remains oracle-free.

### 7.6 Position within the lab's stack

- Shares the **LaBRADOR ring profile** ($d=64$, 64-bit $q$, $\{0,\pm1,\pm2\}$ challenges with $\|S\|_{\mathrm{op}}\le15$) with `salsaa.md`/LaBRADOR tracks — one `lzk.ring` configuration serves all.
- The **monomial lookup + table polynomial** machinery is *identical* to LatticeFold+'s (`latticefold_plus.md`); Symphony's contribution is removing the double commitments by folding *projected* vectors — keep one `monomial.py` with both consumers.
- The **$\varphi$ map** of §4.1 is Cyclo's $\theta_k$ (`cyclo.md` §3.2): one module, two protocols (pay-per-bit single-instance path here, R1CS-to-hybrid there).
- The **CWSS forking lemma** (Lemma 2.3/B.1) is the same machinery as Cyclo's Lemma 4 — factor as `lzk.forking.cwss` with an ROM mode.
- Complements `symphony` vs `cyclo`: Cyclo = streaming folder with bounded rounds and refresh; Symphony = one-shot batch folder compiled to a ROM SNARK without recursion. A lab benchmark matrix {Cyclo, LatticeFold+, Symphony} × {proof size, prover time, memory, verifier} is the deliverable.

---

## 8. Implementation Notes

### 8.1 Data structures

- `RingElt`: `int64[64]` over the 64-bit $q$ (full NTT possible if $q\equiv1\bmod128$, else Karatsuba/naïve $d=64$ is already cheap; note $S$ requires only $S-S$ invertibility per LS18 — pick $q$ with $X^{64}+1$ splitting into 32 quadratics, LaBRADOR-style).
- `E-elt`: `K[64]` with $K=\mathbb{F}_{q^2}$ as pairs; implement the **three multiplications** of §2.3 as separate kernels (`scalar_mul`, `ring_mul_lift`, `mixed_mul`) — correctness of the tensor framework depends on never confusing them.
- `LinInstance` ($R_{\mathrm{lin}}^{\mathrm{aux}}$): `{c: Rq^kappa, x: Rq^nin, r: K^log M, v: E^kx}`; `BatchLinInstance`: `{r, [(c_i, u_i)]}`.
- Monomial vectors $g^{(i)}$: store as exponent+sign arrays (`int8` exponents, sign bit) and materialize $R_q$ form lazily — the $\mathrm{Exp}$ map and $\mathrm{ct}(g\cdot t(X))$ table lookups are the hot path.
- Projection $J$: sampled from a seeded RNG inside the FS transcript ($\lambda_{\mathrm{pj}}\ell_h$ bits; expand with SHAKE/SHA-3 domain-separated — this is also the verifier's cost driver).
- FS transcript: Merkle tree (leaves = round messages $m_i$) or KZG; each $c_{\mathrm{fs},i}$ is the root/commitment; openings go into the CP-SNARK witness.

### 8.2 Algorithms to build, with `lzk` reuse

| Symphony component | `lzk` reuse / new |
|---|---|
| $R_q=\mathbb{Z}_q[X]/\langle X^{64}{+}1\rangle$ arithmetic | `lzk.ring` NTT (64-dim, 64-bit $q$; LaBRADOR profile — same as LaBRADOR/SALSAA modules) |
| Ajtai commitment $c=Am$, strict/relaxed/fine-grained openings | `lzk.ajtai` + new `VfyOpen_{lh,B}` block-norm checker |
| Challenge set $S$ (ternary-ish, $\{0,\pm1,\pm2\}$, $\|S\|_{\mathrm{op}}\le15$, $S-S$ invertible) | `lzk` LaBRADOR-style sampler; unit test: sampled differences invertible |
| $\mathrm{ts}(r)$, MLE, sumcheck over $K=\mathbb{F}_{q^2}$ | `lzk.sumcheck` + `lzk.tensor`; degree-3 univariate mode |
| Sumcheck batching with powers of $\alpha$ (2ℓ_np→2 claims) | new thin layer over `lzk.sumcheck` |
| Monomial RoK $\Pi_{\mathrm{mon}}$ (Lemma A.1 test $\mathrm{ev}_u(\beta)^2=\mathrm{ev}_u(\beta^2)$) | new; needs `ev` maps $R_q\to K$, $E\to K$ |
| Table polynomial $t(X)$, $\mathrm{Exp}$, Lemma 2.1 | new tiny module (shared with LatticeFold+ doc) |
| Random projection $M_J=I_{n/\ell_h}\otimes J$, $H=M_J\mathrm{cf}(f)$ | new; exploit block structure — $H$'s rows are $\chi$-combinations of $\ell_h$-blocks, $nd\lambda_{\mathrm{pj}}$ **additions** only |
| Digit decomposition $H=\sum d'^{i-1}H^{(i)}$ | new (base $d'=62$, balanced) |
| $\Pi_{\mathrm{had}}$, $\Pi_{\mathrm{rg}}$, $\Pi_{\mathrm{gr1cs}}$, $\Pi_{\mathrm{fold}}$ | new protocol modules (Figs. 1–4) |
| FS Commit-and-Open + CP-SNARK compiler (Construction 6.1) | new; `lzk.fs` for the ROM transcript with $H$/$H_{\mathrm{fd}}$ domain separation |
| Streaming sumcheck ($O(\log\log n)$ passes) | optional; port [Baw+25] §4 table-combining algorithm |
| Two-layer: splitting RoK + decomposition RoK | new (Section 8); decomposition RoK shared with LatticeFold+ |

### 8.3 Complexity summary (what to benchmark first)

1. **Witness committing** ($\kappa n\ell_{\mathrm{np}}$ mults, ≈70% of prover time at Table 1 params): benchmark `lzk.ajtai` with bounded-operand specialization (operands $\ell_\infty\le8$: use small-multiplier NTT trick or schoolbook with 8-bit lanes).
2. **Streaming sumcheck table combining** (2 merged claims, sizes $m,n$): the $\ell_{\mathrm{np}}$-table combination dominates after commitments.
3. **Fold step** ($S\times R_q$ mults, $n\ell_{\mathrm{np}}$ + $k_gn\ell_{\mathrm{np}}$): cheap ($S$ entries have 3 non-zero coefficients).
4. **Verifier / CP-SNARK circuit**: $(1+k_g)\ell_{\mathrm{np}}$ + $\ell_{\mathrm{np}}n_{\mathrm{in}}$ + $(4+k_g)t\ell_{\mathrm{np}}$ $S$-mults — grows linearly in $\ell_{\mathrm{np}}$; this is what two-layer folding removes.

### 8.4 Pitfalls

1. **1-indexing vs 0-indexing:** Symphony uses $[n]=[1,n]$ and $f_i$ for $i\in[n]$; Cyclo/LaBinius use $[n]=\{0,\dots,n-1\}$. Wrap all shared `lzk` tensor/MLE code with an explicit convention and assert equality in cross-protocol tests.
2. **The three $E$-multiplications:** mixing K-scalar mult with $R_q$-lifted polynomial mult silently corrupts evaluation claims (they agree only on the intersection where the $R_q$ factor is a constant). Type-check operands.
3. **$\mathrm{Exp}$ sign handling:** $\mathrm{Exp}(a)=\mathrm{sgn}(a)X^{|a|}$ over $R_q$ uses $X^{d-|a|}$ for negatives? No — $\mathrm{sgn}(a)X^{a}$ with $a$ negative means $\pm X^{-|a|}=\mp X^{d-|a|}$; the table polynomial identity (Lemma 2.1) depends on getting this exactly right; unit-test $\mathrm{ct}(\mathrm{Exp}(a)\cdot t(X))=a$ for all $a\in(-32,32)$, $d=64$.
4. **$B_{d,k_g}$ arithmetic:** with $d=64$: $d'=62$, $B_{d,3}=31(1+62+3844)=121117$; $k_g$ is *minimal* s.t. $B_{d,k_g}\ge9.5B$ — off-by-one here either breaks completeness (abort in Step 2 too often) or wastes a monomial commitment.
5. **Eq. (50) is worst-case:** $\ell_{\mathrm{np}}\|S\|_{\mathrm{op}}\max(B\sqrt{nd/\ell_h},\sqrt n)\le B_{\mathrm{bnd}}$ must be validated *at parameter-selection time*; the concrete 117-bit table satisfies it, but any change to $\ell_{\mathrm{np}}$, $\ell_h$, $B$, or $S$ requires re-solving Eq. (50) and re-running the lattice estimator.
6. **The $J$-resampling extractor is not implementable as stated** (expected-poly, $2^\lambda$ cap) — but its *existence* is what licenses the FS compile; do not "optimize" the protocol by making $J$ prover-chosen or reusing it across folds without redoing Template-B analysis.
7. **Challenge sharing discipline (Fig. 3/4):** the interleaved sumchecks share the challenge stream $(\bar r,\bar s,s)$ *by segment* — $\log m_J$ / $\log m-\log m_J$ / $\log n-\log m$ coordinates; misaligned segmentation makes the monomial and Hadamard claims unverifiable against each other.
8. **Public reducibility map $f$:** the CP-SNARK literally checks $x_o=f(x,(m_i),(r_i))$ — the implementation must expose the folding verifier as a *pure deterministic function* over serialized messages, or the CP-SNARK statement and the interactive verifier drift apart.
9. **$r_{\mathrm{rnd}+1}$ ordering (Lemma B.2 footnote):** in the mental experiment, $r_{i+1}$ must be sampled *after* extracting $m'_1$ and $(m_j)_{j=2}^i$ ("otherwise $r_{i+1}$ may be correlated with the prover messages") — mirror this in any FS reimplementation: hash only *committed* material.
10. **Straightline extractability of the outer commitment:** Merkle/KZG only; do not substitute the Ajtai commitment as $\Pi_{\mathrm{cm}}$ (it is not straightline extractable in the required sense) — the *inner* commitments stay Ajtai/MSIS, the *outer* transcript commitments are separate.
11. **Verification is linear in $\ell_{\mathrm{np}}$ (and in the $2^{23}$ FS bits for $J$):** fine for batch-proof scenarios (aggregate verification of $2^{16}$ statements); if the deployment needs succinct verification, combine with a recursive SNARK over blocks (the paper's own hybrid suggestion) — that reintroduces oracles in circuits *outside* Symphony's proven core.
12. **$t=2$ field:** all soundness terms are $/|K|=/q^2$ with 64-bit $q$ ⇒ ≈$2^{-128}$ per Schwartz–Zippel; the FS factor $Q$ pushes toward $2^{128}\cdot Q$ set sizes — the paper sizes $K$ and $S$ above $2^{128}$ for exactly this reason; do not shrink $q$ to 32 bits without re-deriving every error term.

### 8.5 Proposed lab module layout

```
lzk/protocols/symphony/
  __init__.py        # SymphonySNARK: prove/verify entry; compiler (Construction 6.1)
  relations.py       # R_lin, R_had, R_mon, R_batchlin, R_rg, R_gr1cs, R_cp, splitting R'
  commitment.py      # Construction 2.1: Commit/VfyOpen/RVfyOpen/VfyOpen_{lh,B}
  tensor_rings.py    # E = K[X]/<X^d+1>; three multiplication kernels; ev maps
  monomial.py        # M set, t(X), Exp, Lemma 2.1 checks; Pi_mon (App. A)
  hadamard.py        # Figure 1 Pi_had
  rangeproof.py      # Figure 2 Pi_rg (projection, decomposition, monomial lookup)
  gr1cs.py           # Figure 3 Pi_gr1cs (interleaving) + decomp_{b,kcs} conversion + phi-map path
  folding.py         # Figure 4 Pi_fold (high-arity, merged sumchecks, beta-fold)
  fs.py              # Commit-and-Open + FS^H; H/H_fd domain separation
  compiler.py        # CP-SNARK relation, instance compression (Remark 6.1)
  twolayer.py        # splitting RoK + two-layer driver (Section 8)
  params.py          # Table 1 preset; Eq. (28)/(50) solvers; estimator hooks
  bench.py           # 3*2^32 commitment benchmark; streaming sumcheck profile
tests/test_symphony_*.py
```

### 8.6 Test plan

1. **Lemma 2.1 / A.1 exhaustive:** all $a\in(-d/2,d/2)$ for $d=8,16$; random $\beta$: identity always for monomials, breaks for random polys.
2. **$\Pi_{\mathrm{mon}}$ end-to-end:** honest monomial vector accepted; vector with one non-monomial entry rejected w.p. $\ge1-2d/|K|$.
3. **$\Pi_{\mathrm{rg}}$:** random short $f$, run all 8 steps; verify Step-6 identity algebraically; malicious $f$ with $\|F_{i,j}\|_2>B$ but passing requires breaking projection — statistically verify rejection rate on small params.
4. **$\Pi_{\mathrm{had}}$/$\Pi_{\mathrm{gr1cs}}$:** small R1CS (e.g. Fibonacci $m=n=16$) through the decomp conversion and Neo $\varphi$ path; both must fold.
5. **$\Pi_{\mathrm{fold}}$ with $\ell_{\mathrm{np}}=8$:** check Eq. (45) merged claim equals the 16 individual claims; check folded instance/witness satisfies $R_o$ checker; check norm ledger against Eq. (50) with slack.
6. **CWSS forking simulation:** construct two transcripts differing in one $\beta$ coordinate; verify division $f^\ell=(f^{*,\ell}-f^{*,0})/(\Delta)$ recovers the input witness.
7. **FS round-trip:** recompute all $r_i$ from $(x,(c_{\mathrm{fs},i}))$; bit-reproducible; CP-SNARK statement matches the interactive public-reducibility map $f$ on random transcripts.
8. **Streaming:** $O(\log\log n)$-pass sumcheck equals in-memory sumcheck outputs.
9. **Two-layer:** splitting RoK round-trip ($c=\sum r_ic_i$; $\langle\mathrm{ts}(r),(v_i)\rangle=v$); end-to-end $\ell_{\mathrm{np}}\ell$ statements → 2 CP-SNARK proofs + 1 SNARK proof.

### 8.7 Estimated lab (Python) build effort

| Module | LOC est. | Depends on | Notes |
|---|---|---|---|
| `tensor_rings.py` | ~150 | `lzk.ring`, GF($q^2$) | 3 multiplication kernels + `ev` maps; property tests |
| `commitment.py` | ~120 | `lzk.ajtai` | strict/relaxed/fine-grained openers |
| `monomial.py` | ~100 | — | $t(X)$, `Exp`, Lemma 2.1 self-check |
| `hadamard.py` | ~120 | `lzk.sumcheck` | Fig. 1 |
| `rangeproof.py` | ~200 | `monomial.py`, `lzk.sumcheck` | Fig. 2 incl. block-projection and digit split |
| `gr1cs.py` | ~180 | `hadamard.py`, `rangeproof.py` | Fig. 3 + `decomp`/`φ` front-ends |
| `folding.py` | ~200 | `gr1cs.py` | Fig. 4 with merged claims + β-fold + norm ledger |
| `fs.py` + `compiler.py` | ~250 | `lzk.fs`, a Merkle tree | Construction 6.1; CP-SNARK stub interface |
| `twolayer.py` | ~150 | `folding.py` | splitting + decomposition RoK driver |
| `params.py` | ~100 | — | Table 1 preset, Eq. (28)/(50) solvers |
| tests | ~500 | all | §8.6 plan |

Suggested staging for the implementer: (1) `tensor_rings`+`monomial` with Lemma 2.1/A.1 tests; (2) `commitment` + `hadamard` on a toy R1CS; (3) `rangeproof` (the hardest unit — projection, digit split, Step-6 identity); (4) `folding` at $\ell_{\mathrm{np}}=8$; (5) FS + compiler with a *simulated* CP-SNARK (native checker standing in for the SNARK) to validate the architecture before integrating WHIR/LaBRADOR; (6) two-layer. The CP-SNARK and inner SNARK are external dependencies — define the interface (`prove(rel, x, w) -> π`, `vfy(...)`) and mock them first; the lab's WHIR/LaBRADOR work fills them later.

---

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
