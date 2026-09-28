# HyperWolf: Efficient Polynomial Commitment Schemes from Lattices — Deep Analysis & Implementation Spec

> Source: eprint 2025/922 (recovered from `https://eprint.iacr.org/archive/2025/922/1747892571.pdf`),
> extracted text `papers_txt/hyperwolf.txt` (2020 lines, 35 pp. layout).
> This document is an implementation-grade transcription: every protocol figure is
> transcribed line-by-line with all formulas, all soundness bounds, all concrete numbers,
> plus implementation analysis targeted at the shared `lzk` Python core engine.

---

## 1. Metadata

| Field | Value |
|---|---|
| Title | HyperWolf: Efficient Polynomial Commitment Schemes from Lattices |
| Name expansion | **Hyper**cube-**W**ise **O**pti**m**ized polynomial commitment scheme based on **L**attices over ring **F**ields |
| Authors | Lizhen Zhang, Shang Gao, Bin Xiao — The Hong Kong Polytechnic University (HK PolyU) |
| Note | Footnote: "In the future, this scheme will be implemented by Mr. Kurt Pan, and he will be included in the author list at that time." (same group as Serval and Quasar) |
| Venue/eprint | IACR eprint 2025/922 |
| Security assumption | Module-SIS $\mathrm{MSIS}_{\kappa,n,q,\beta}$ over $R_q=\mathbb{Z}_q[X]/(X^d+1)$ — **standard**, $\ell_2$-norm flavour |
| Setup | Fully **transparent** (public randomness only; no CRS, no trusted setup) |
| Headline contribution | $O(\log N)$ proof size **and** $O(\log N)$ verifier time with **linear** prover; unified univariate + multilinear framework; $k$-dimensional tensor (hypercube) generalization of Brakedown's 2-D tensor structure; $k$-round recursive dimension-reduction protocol with per-round cost $O(N^{1/k})$, total $O(kN^{1/k})$; $k=\log N$ ⇒ near-optimal |
| Concrete claim ($N=2^{25}$, 128-bit sec.) | proof 8× smaller than Cini et al. [CMNW24] (Crypto'24), >200× smaller than SLAP [AFLN24] (Eurocrypt'24); similar magnitude to Greyhound [NS24] (Crypto'24) with **significantly lower verifier time** |
| Functionality | PCS over $\mathbb{Z}_q^{<N}[X]$ (univariate) and multilinear $\mathbb{Z}_q[X_0,\dots,X_{\ell-1}]$, $N=2^\ell$ |
| Future work (authors) | Rust implementation + lattice PCS library; replace constant-term extraction with NTT-based ring mapping (better data utilization); better batching |

**Positioning vs. prior lattice PCS (paper's own taxonomy):**

- *Inner-product-relation family* [ACL+22, dCP23, WW23a, CLM23, BCS23, FLV23]: Bulletproofs-style; linear-time verification; most lack extractability; those with it rely on non-standard (and partially broken, cf. $k$-M-SIS [WW23a]) assumptions.
- *Recursive/split-and-fold family*: [FMN24] (PowerBASIS, quadratic CRS); SLAP [AFLN24] (M-SIS $\ell_2$, trusted setup, quasi-linear prover); Greyhound [NS24] (transparent, **univariate only**, $\ell_\infty$-flavoured, Labrador-based, $O(\log\log N)$ proof but $O(\sqrt N)$ verifier); [CMNW24] (transparent, uni+multilinear, but heavy **integer-field arithmetic** — no ring packing).
- HyperWolf: standard M-SIS ($\ell_2$), transparent, uni+multilinear, $O(\log N)$/round-structure proof & verifier, linear prover.

---

## 2. Notation Table

Every symbol used in the paper (paper §2.1 plus symbols introduced in §3–5 and appendices):

| Symbol | Meaning |
|---|---|
| $\lambda$ | Security parameter (implicit input to all algorithms); concrete value 128 |
| $\mathrm{neg}(\lambda)$ | Negligible function; all key parameters assumed $\mathrm{poly}(\lambda)$ |
| $[n]$ | $\{0,1,\dots,n-1\}$ |
| $[a\!:\!b]$ | $\{a,a+1,\dots,b-1\}$ for integers $a<b$ |
| $q$ | Odd prime modulus; $\mathbb{Z}_q:=\mathbb{Z}/q\mathbb{Z}$; concrete: 128-bit prime, $q\equiv 5 \pmod 8$ (see §7) |
| $d$ | Ring degree, power of two; $R:=\mathbb{Z}[X]/(X^d+1)$, $R_q:=\mathbb{Z}_q[X]/(X^d+1)$; concrete $d=64$ |
| $\mathrm{ct}(f)$ | Constant term of ring element $f=\sum_{i} f_iX^i$, i.e. $f_0$ |
| $\vec f=(f_0,\dots,f_{n-1})$ | Vector in $\mathbb{Z}_q^n$ (or $R_q^n$); $i$-th entry $f_i$ or $f[i]$ |
| $\vec 1_m$ | All-ones vector of length $m$ |
| $\mathbf{f}$ (bold, non-challenge) | Ring element of $R_q$; bold uppercase $\mathbf{A},\mathbf{B}$ = matrices over $R_q$ |
| $(\vec f,\vec g)$ | Concatenation of length-$n$ vectors → length $2n$; $(\vec f_i)_{i\in[k]}$ concatenation of $k$ vectors → $R_q^{kn}$; $[\mathbf{A}\ \mathbf{B}]$ horizontal matrix concatenation |
| $\|\cdot\|_1,\|\cdot\|_2,\|\cdot\|_\infty$ | For $f=\sum_{i=0}^{d-1}f_iX^i\in R_q$: $\|f\|_1=\sum|f_i|$, $\|f\|_2=(\sum f_i^2)^{1/2}$, $\|f\|_\infty=\max_i\|f_i\|$ (coordinates taken in balanced rep.) |
| $\|\vec f\|$ ($\vec f\in R_q^m$) | $\|\vec f\|_1=\sum_i\|f_i\|_1$; $\|\vec f\|_2=(\sum_i\|f_i\|_2^2)^{1/2}$; $\|\vec f\|_\infty=\max_i\|f_i\|_\infty$. **Default $\|\cdot\|$ = $\ell_2$** |
| $\|c\|_{\mathrm{op}}$ | Operator norm: $\sup_{v\in R_q}\|cv\|/\|v\|$ (max amplification of multiplication by $c$) |
| $\mathcal{C}\subset R_q$ | Challenge space: differences of any two distinct elements **invertible** in $R_q$; $\|c\|\le\tau$, $\|c\|_{\mathrm{op}}\le T$ $\forall c\in\mathcal{C}$ ($\tau,T$ integer constants) |
| $\tau$ | $\ell_2$-norm bound on challenges ($\omega(1)$; concrete $\sqrt{71}\approx 8.43$) |
| $T$ | Operator-norm bound on challenges ($\omega(1)$; concrete $15$) |
| $\vec g_a$ | Gadget vector $(1,a,a^2,\dots,a^{\iota-1})$, $\iota=\lceil\log_a q\rceil$ |
| $\iota$ | Gadget length for base $\delta$: $\iota=\lceil\log_\delta q\rceil$ (concrete 32) |
| $\iota'$ | Gadget length for base $\delta_t$: $\iota'=\lceil\log_{\delta_t} q\rceil$ (concrete 32) |
| $G_{a,m}$ | Gadget matrix $I_m\otimes \vec g_a^T\in\mathbb{Z}_q^{m\times \iota m}$ (compose direction) |
| $G^{-1}_{a,m}$ | Decomposition map $R_q^{m\times n}\to R_q^{\iota m\times n}$ with $G_{a,m}G^{-1}_{a,m}(A)=A$; per column $\|\tilde A_i\|\le \frac a2\sqrt{\iota m}$ |
| $\sigma_{-1}$ | Conjugation automorphism $\sigma_{-1}(f):=\sum_{i=0}^{d-1}f_iX^{-i}$ (negacyclic conjugate); entrywise on vectors/matrices |
| $\langle\vec a,\vec b\rangle$ | Inner product; for ring vectors: $\sum_i a_ib_i\in R_q$; integer inner product of coefficient replications = $\mathrm{ct}(\langle\sigma_{-1}(\vec a),\vec b\rangle)$ |
| $M_R$ | Integer-to-ring map $\mathbb{Z}_q^{nd}\to R_q^n$: $M_R(\vec f)_k=\sum_{j=0}^{d-1}f_{kd+j}X^j$ (groups of $d$ consecutive coordinates) |
| $\mathrm{MSIS}_{\kappa,n,q,\beta}$ | Module-SIS: given uniform $\mathbf{A}\in R_q^{\kappa\times n}$ find $\vec z\ne 0$, $\mathbf{A}\vec z=\vec 0$, $\|\vec z\|\le\beta$ |
| $\kappa$ | Commitment matrix height; concrete $\kappa=2\iota=64$; requirement $\kappa\ge 2\iota$ |
| $\beta$ | Generic Ajtai binding norm bound (binding holds under $\mathrm{MSIS}_{\kappa,n,q,2\beta}$) |
| $N$ | Number of coefficients of $f$; $N=\prod_{i=0}^{k-1}b_i\cdot d$; with uniform $b$: $N=b^kd$ |
| $b_i$ | Size of the $i$-th hypercube axis ($i$-th "dimension"), $i\in[k]$ (0 = innermost/last axis) |
| $b$ | Uniform axis size; concrete $b=2$; $b=(N/d)^{1/k}$ |
| $k$ | Hypercube dimensionality / number of axes = number of evaluation vectors; $k=\log_b(N/d)$; concrete $k=\log_2 N-6$ |
| $[F]$ | $k$-dimensional coefficient hypercube, shape $b_{k-1}\times b_{k-2}\times\cdots\times b_0$ |
| $F(\cdot)$ | Reshape operator: maps a $(k-i)$-dim hypercube of size $b_{k-1}\times\cdots\times b_i$ to a matrix of size $(b_{k-1}\cdots b_{i+1})\times b_i$ (last axis becomes columns) |
| $\vec a_j$ | $j$-th auxiliary evaluation vector; $\vec a_j\in\mathbb{Z}_q^{b_j}$ for $j\ge 1$; $\vec a_0\in\mathbb{Z}_q^{b_0d}$ (pre-expansion), expanded to $R_q^{b_0\iota}$ |
| $\otimes$ | Tensor / Kronecker product (of vectors and matrices) |
| $\mathrm{Fold}^{(k)}$ | Full fold operator (Eq. 4): $F(\cdots F(F(s^{(k)})\cdot\sigma_{-1}(M_R(\vec a_0)))\cdot\vec a_1)\cdots)\cdot\vec a_{k-2}$; output $\in R_q^{b_{k-1}}$ |
| $\mathrm{fold}^{(k-r)}$ | Prover message: the folded vector at round $r$, $\in R_q^{b_{k-r-1}}$ |
| $s^{(k)}$ | Witness hypercube $\in R_q^{b_{k-1}\times b_{k-2}\times\cdots\times b_0\iota}$ (last axis is gadget-decomposed) |
| $s_i^{(k-1)}$ | The $i$-th slice of $s^{(k)}$ along the outermost ($k$-th, 1-indexed) axis, $i\in[b_{k-1}]$; a $(k-1)$-dim hypercube |
| $D$ | Flattening $F^{b_{r-1}\times\cdots\times b_0}\to F^{\prod_{j=0}^{r-1}b_j}$: sequential concatenation of edges (row-major, first index slowest) |
| $D(s_i^{(k-1)})$ | Flattened slice $\in R_q^{(\prod_{j=0}^{k-2}b_j)\iota}$ |
| $\mathbf{A},\mathbf{B}$ | Base public commitment keys: $\mathbf{A}\in R_q^{\kappa\times b_0\iota}$ (inner), $\mathbf{B}\in R_q^{\k\times\k\iota'}$ — i.e. $R_q^{\kappa\times\kappa\i'}$ (outer) |
| $\mathbf{A}^{(k-r)}$ | Expanded inner key $\vec 1^T_{\prod_{j=1}^{k-r-2}b_j}\otimes\mathbf{A}\in R_q^{\kappa\times(\prod_{j=0}^{k-r-2}b_j)\iota}$ |
| $\mathbf{B}^{(k-r)}$ | Expanded outer key $\vec 1^T_{b_{k-r-1}}\otimes\mathbf{B}\in R_q^{\kappa\times b_{k-r-1}\kappa\i'}$ |
| $c^{(k-1)}_{\min,i}$ | Inner Ajtai commitment of slice $i$: $\mathbf{A}^{(k)}D(s_i^{(k-1)})\in R_q^\kappa$ |
| $\mathrm{cm}_{\mathrm{out}}^{(k)}$ | Outer commitment $\mathbf{B}^{(k)}G^{-1}_{\delta_t,b_{k-1}\kappa}((c_{\min,i}^{(k-1)})_{i\in[b_{k-1}]})\in R_q^\kappa$ |
| $\mathrm{cm}'$ | Gadget-decomposed stack of inner commitments: $G^{-1}_{\delta_t,b\kappa}((c_{\min,i})_{i\in[b]})$ |
| $\Pi$ | JL projection matrix $\in\{0,\pm1\}^{256\times b_0\iota d}$, iid entries with $\Pr[\pm1]=\frac14,\ \Pr[0]=\frac12$ |
| $\Pi^{(k-r)}$ | Expanded projection matrix $\vec 1^T_{\prod_{j=1}^{k-r-2}b_j}\otimes M_R(\Pi)\in R_q^{256\times(\prod_{j=0}^{k-r-2}b_j)\iota}$ |
| $\vec p_i^{(k-r)}$ | JL projection of slice $i$ at round $r$: $\sigma_{-1}(\Pi^{(k-r)})\,D(s_i^{(k-r-1)})\in R_q^{256}$ |
| $y^{(k)}$ | Claimed evaluation as ring element (constant term = evaluation value) |
| $y^{(k-r-1)}$ | Next-round claim: $\langle\mathrm{fold}^{(k-r)},\vec C^{(k-r)}\rangle$ |
| $\vec C^{(k-r)}$ | Round-$r$ challenge vector $\in\mathcal{C}^{\,b_{k-r-1}}$ (components $C^{(k-r)}_i\in\mathcal{C}$) |
| $\beta^{(k-1)}$ | Norm bound on initial flattened slices $D(s_i^{(k-1)})$ (gadget bound) |
| $\beta^{(k-r-1)}$ | Norm bound at round $r$; recursion below (§6) |
| $\beta^{(0)}$ | Final norm bound on $s^{(1)}$ |
| $\gamma$ | Extraction MSIS scale: $\gamma=\max_{r\in[k]}\sqrt{b\,\beta^{(k-r)}}$ (≈ $2\beta^{(0)}$ for $b=2$) |
| $\beta'$ | Outer-binding MSIS bound: $(\delta_t/2)\sqrt{b\kappa\iota'}$ |
| $\delta$ | Decomposition base 1 (witness gadget); concrete 16 |
| $\delta_t$ | Decomposition base 2 (commitment stack gadget); concrete 16 |
| $S,\ \ell$ | CWSS parameters: per-round challenge = vector in $S^\ell$; here $S=\mathcal{C}$, $\ell=b$ |
| $\equiv_i$ | $\vec x\equiv_i\vec y \Leftrightarrow x_i\ne y_i \wedge \forall j\ne i:\ x_j=y_j$ |
| $SS(S,\ell,k)$ | Set of $K=\ell(k-1)+1$ challenge vectors with a "center" $\vec x_e$ s.t. per coordinate $i$ there are $k-1$ others differing only at $i$ |
| $\mu$ | Number of interactive rounds ($(2\mu+1)$-message protocol); here $\mu=k-1$ |
| $\epsilon(\lambda)$ / $\varepsilon(\lambda)$ | Completeness error / knowledge error |
| $\mathrm{SL}$ | Slack space of the PCS (relaxation factors $s$ for `Open`) |
| $\bar\beta,\ \bar\tau$ | Relaxed norm bounds used by `Open` (slack) |
| $\bar c_v^{(k-r)}$ | Challenge difference $\vec C_b^{(k-r)}-\vec C_v^{(k-r)}$ (nonzero only in coordinate $v$) |
| $\bar D(\cdot),\ \bar s$ | Extractor-reconstructed ("weak") openings/witness |
| $\vec S_m^{(k-r-1)}$ | Concatenation of next-round flattened slices of transcript $m$ = $D(s_m^{(k-r-1)})$ (full flattening) |
| $\mathrm{eq}(\vec b,\vec x)$ | Multilinear equality polynomial $\prod_{i=0}^{\log N-1}(b_i x_i+(1-b_i)(1-x_i))$ (batching appendix) |
| $\mathrm{Com}$ | Generic Ajtai commit $\mathrm{cm}:=\mathbf{G}\vec f$ |
| $x^{(k)}, w$ | Statement / witness of relation $R_k$ (see §4) |
| $\hat t_c$ | $G^{-1}_{\delta_t,b_{k-r-1}\kappa}((c^{(k-r-1)}_{\min,i})_{i\in[b_{k-r-1}]})$ — decomposed commitment stack |

---

## 3. Algebraic Setting

### 3.1 Rings, fields, modulus

- Ring of integers: $R=\mathbb{Z}[X]/(X^d+1)$; working ring $R_q=\mathbb{Z}_q[X]/(X^d+1)$, $d$ a power of two (concrete $d=64$; the paper writes the concrete ring as $\mathbb{Z}_q[X]/(X^{64}+1)$).
- $q$: odd prime with $q\equiv 5\pmod 8$ (concrete ~128 bits — derived, see §7.3).
- $q\equiv 5\pmod 8$ matters for **Lemma 1 (Invertibility Condition, Lyubashevsky–Seiler [LS18])**:
  when $q\equiv 5\pmod 8$, any $f\in R_q$ with $0<\|f\|<q^{1/2}$ has an inverse in $R_q$.
  This underwrites the challenge-space requirement that differences of distinct challenges are invertible
  (challenge differences have $\ell_2$-norm $\le 2\tau\approx 16.9\ll q^{1/2}$).
- $\mathbb{Z}_q$ elements are identified with constant ring elements (no boldface).

### 3.2 Norms

- Coordinate norms for $f=\sum_{i=0}^{d-1}f_iX^i$: $\|f\|_1=\sum_i|f_i|$, $\|f\|_2=\big(\sum_i f_i^2\big)^{1/2}$, $\|f\|_\infty=\max_{i\in[d]}|f_i|$.
- Extension to $\vec f=(f_0,\dots,f_{m-1})\in R_q^m$: $\|\vec f\|_1=\sum_i\|f_i\|_1$, $\|\vec f\|_2=\big(\sum_i\|f_i\|_2^2\big)^{1/2}$, $\|\vec f\|_\infty=\max_i\|f_i\|_\infty$.
- **Unless stated otherwise, $\|\cdot\|$ is the $\ell_2$ norm** (this is the M-SIS($\ell_2$) flavour — contrast with Greyhound which works with $\ell_\infty$).
- Operator norm: $\|c\|_{\mathrm{op}}:=\sup_{v\in R_q}\|cv\|/\|v\|$ — the max singular value of the negacyclic convolution matrix of $c$.

### 3.3 Challenge space

$\mathcal{C}\subset R_q$ is a challenge space iff (i) for any two distinct $c,c'\in\mathcal{C}$, $c-c'$ is invertible in $R_q$; (ii) $\|c\|\le\tau$ and $\|c\|_{\mathrm{op}}\le T$ for all $c\in\mathcal{C}$, with $\tau,T$ integer constants.

**Ring-field optimization (paper's third contribution):** because challenges are *ring elements*, the challenge space is huge under a small $\ell_2$ bound. Concrete instantiation (same as Labrador [BS23]): $R_q=\mathbb{Z}_q[X]/(X^{64}+1)$, each challenge has **23 zero coefficients, 31 coefficients in $\{\pm1\}$, 10 coefficients in $\{\pm2\}$**:
$\tau=\sqrt{31\cdot1+10\cdot4}=\sqrt{71}\approx 8.43$,
$|\mathcal{C}|=\binom{64}{23}\binom{41}{31}2^{41}>2^{128}$.
By **reject sampling 5–6 times**, the operator norm is restricted to $T<15$. Soundness error is then $O(2^{-\lambda})$.

### 3.4 Gadget decomposition / composition

- Gadget vector $\vec g_a=(1,a,a^2,\dots,a^{\iota-1})$, $\iota=\lceil\log_a q\rceil$.
- Gadget matrix $G_{a,m}:=I_m\otimes\vec g_a^T\in\mathbb{Z}_q^{m\times\iota m}$; decomposition $G^{-1}_{a,m}:R_q^{m\times n}\to R_q^{\iota m\times n}$ with $G_{a,m}G^{-1}_{a,m}(A)=A$ (apply to vectors: $G^{-1}_{a,m}(\vec v)$ decomposes each *ring element* of $\vec v$ into $\iota$ digit ring elements by decomposing each *coefficient* in base $a$ with digits in $(-a/2,a/2]$).
- Norm bound: for each column $\tilde A_i$ of $\tilde A=G^{-1}_{a,m}(A)$: $\|\tilde A_i\|\le\frac a2\sqrt{\iota m}$.
- Two bases are used: $\delta$ (witness decomposition, length $\iota$) and $\delta_t$ (commitment-stack decomposition, length $\iota'$). Concrete $\delta=\delta_t=16$, $\iota=\iota'=32$ (for $q\le 2^{128}$).

### 3.5 Conjugation automorphism and ring inner products

$\sigma_{-1}:R_q\to R_q$, $\sigma_{-1}(f):=\sum_{i=0}^{d-1}f_iX^{-i}$ (i.e. $X^i\mapsto X^{d-i}$ for $i>0$). For $\vec a,\vec b\in R_q^n$ with coefficient representations $\vec{\mathbf a},\vec{\mathbf b}\in\mathbb{Z}_q^{nd}$:
$$\langle \vec{\mathbf a},\vec{\mathbf b}\rangle_{\mathbb{Z}} = \mathrm{ct}\big(\langle \sigma_{-1}(\vec a),\vec b\rangle\big).$$
This identity is the load-bearing trick that converts *integer* inner products (JL projections, evaluation inner products) into *ring* arithmetic where only the constant term is consumed. (The authors note as future work that only $1/d$ of each ring product is currently used — an NTT-based mapping could recover the other coefficients.)

### 3.6 Integer-to-ring mapping

$M_R:\mathbb{Z}_q^{nd}\to R_q^n$:
$$M_R(\vec f)=\Big(\sum_{j=0}^{d-1}f_jX^j,\ \sum_{j=0}^{d-1}f_{d+j}X^j,\ \dots,\ \sum_{j=0}^{d-1}f_{(n-1)d+j}X^j\Big).$$
Applied to a matrix (e.g. $\Pi$), it maps each row of $n\cdot d$ integers to $n$ ring elements.

### 3.7 Module-SIS and Ajtai commitment

**Definition 1 (MSIS$_{\kappa,n,q,\beta}$).** Given uniform $\mathbf{A}\in R_q^{\kappa\times n}$ ($\kappa=\mathrm{poly}(n)$), find nonzero $\vec z\in R_q^n$ with $\mathbf{A}\vec z=\vec 0$ over $R_q$ and $\|\vec z\|\le\beta$.

Hardness heuristic (Micciancio–Regev [MR09], as quoted): an MSIS algorithm is expected to produce solutions only of norm
$\|\vec z\|\ge\min\big(q,\ \sqrt{2\,d\,\kappa\log q\log(1.0045)}\big)$-type bounds (paper prints a garbled variant of this standard estimator bound; in practice use the Albrecht et al. lattice estimator). Paper's own feasibility conclusion: with $\delta=\delta_t=16$, $\kappa=2\iota$, $T=15$, soundness holds for $N<2^{32}$.

**Definition 2 (Ajtai commitment [Ajt96]).** $\mathrm{Setup}(1^\lambda)$: $\mathbf{G}\xleftarrow{\$}R_q^{\kappa\times n}$, $\mathrm{pp}:=\mathbf{G}$. $\mathrm{Commit}(\mathrm{pp},\vec f)$: for $\|\vec f\|\le\beta$, $\mathrm{cm}:=\mathbf{G}\vec f$.
Binding for $\|\vec f\|<\beta$ under $\mathrm{MSIS}_{\kappa,n,q,2\beta}$; hiding by appending a small random vector (treated as part of the witness in all protocols below).

### 3.8 Modular Johnson–Lindenstrauss lemma (norm checking)

Verifier samples $\Pi\in\mathbb{Z}^{256\times n}$ with iid entries in $\{-1,0,+1\}$, $\Pr[\pm1]=\tfrac14$, $\Pr[0]=\tfrac12$ (distribution $\mathcal{D}$). The prover reveals $\vec p=\Pi\vec a$ and the verifier uses $\|\vec p\bmod q\|$ to infer $\|\vec a\|$.

**Lemma 3 (Modular JL variant [GHL22, BS23]).** Let $q\in\mathbb{N}$, $\mathcal{D}$ as above. For every $\vec a\in\mathbb{Z}_q^n$ with $\|\vec a\|\le b$ and $b\le q/125$:
$$\Pr_{\Pi\leftarrow\mathcal{D}^{256\times n}}\big[\|\Pi\vec a \bmod q\|_2^2<30b^2\big]\lesssim 2^{-128}.$$

*Implementation note (direction of use):* as literally printed the lemma is stated for short $\vec a$, but the way Theorem 4 uses it is the **contrapositive/lower-tail direction** (identical to Labrador's Lemma): a vector whose norm *exceeds* the threshold $b$ has its 256-dimensional modular projection stay above $\sqrt{30}\,b$ except with probability $\approx2^{-128}$. The protocol checks $\sum_{j=0}^{255}\mathrm{ct}(p_j)^2\le128\beta^2$ and concludes $\|s\|\le\sqrt{128/30}\,\beta\approx2.066\,\beta$ — i.e. constant slack $\sqrt{128/30}$. For an honest $\vec a$ with $\|\vec a\|\le\beta$: $\mathbb{E}[\|\Pi\vec a\|^2]=128\cdot\|\vec a\|^2\cdot(\tfrac12\cdot\tfrac{256}{256})=128\|\vec a\|^2/1$ — precisely, each projection row has variance $\tfrac12\|\vec a\|^2$, so $\mathbb{E}[\sum_j p_j^2]=256\cdot\tfrac12\|\vec a\|^2=128\|\vec a\|^2$; the check threshold $128\beta^2$ sits exactly at the mean when $\|\vec a\|=\beta$. Completeness therefore relies on the honest norm being *strictly below* $\beta$ (which holds because $\beta$ is the worst-case gadget bound $(\delta/2)\sqrt{\#}$ while actual digits are $\approx\delta/\sqrt{12}$-RMS, giving ~1.7× margin, plus $\chi^2$ concentration over 256 dof ~6%). See §8.6 pitfalls.

### 3.9 Proof-system definitions used

- Ternary relation $\mathcal{R}\subseteq\{0,1\}^*\times\{0,1\}^*\times\{0,1\}^*$ with $(\mathrm{pp},x,w)$; $\mathcal{R}(\mathrm{pp},x):=\{w:(\mathrm{pp},x,w)\in\mathcal{R}\}$.
- Def. 3 interactive proof $(S,P,V)$; Def. 4 completeness with error $\epsilon$ (perfect if $\epsilon=0$); Def. 5 knowledge soundness with knowledge error $\varepsilon$ and black-box rewinding extractor.
- Def. 6 PCS $=$ (Setup, Commit, Open, Eval) over $\mathcal{M}=\mathbb{Z}_q^{<N}[X]$ with slack space $\mathrm{SL}$: `Open(pp,cm,f,st,s)` takes a relaxation factor $s\in \mathrm{SL}$ (implicitly outputs 0 if $s\notin\mathrm{SL}$); `Eval(pp,cm,x,y;(f,st))` is a protocol proving "$f$ opens cm and $f(x)=y$". Properties: evaluation completeness (Def. 7), weak binding (Def. 8: no PPT adversary produces $f\ne f'$, both in $R^{<N}[X]$, both accepting openings of the same cm), knowledge soundness (Def. 9, with extractor outputting $(f,st,s)$ such that `Open` accepts and $f(u)=z$).

### 3.10 Coordinate-wise special soundness (CWSS) machinery (from [FMN24]/[CMNW24])

- $\vec x\equiv_i\vec y \Leftrightarrow x_i\neq y_i\wedge\forall j\neq i:\ x_j=y_j$.
- $SS(S,\ell,k):=\{\vec x_1,\dots,\vec x_K\}\subseteq(S^\ell)^K$ with $K=\ell(k-1)+1$: $\exists e\in[K]$ (a "center") s.t. $\forall i\in[\ell]$ $\exists J=\{j_1,\dots,j_{k-1}\}\subseteq[K]\setminus\{e\}$ with $\forall j\in J:\ \vec x_e\equiv_i\vec x_j$. I.e. for every coordinate there are $k$ vectors pairwise-differing only there, one of them the center.
- **Def. 10 (CWSS, multi-round):** a public-coin $(2\mu+1)$-round protocol with per-round challenge space $\mathcal{C}=S^\ell$ is $\ell$-coordinate-wise $k$-special sound if from a tree of $K=(\ell(k-1)+1)^\mu$ accepting transcripts (each node's $K$ children carry challenges forming an $SS(S,\ell,k)$ set) one can extract a witness in poly time. ($\ell=1$ recovers standard $k$-special soundness.)
- **Def. 11 (Round-by-round CWSS):** for a recursively structured protocol with relation sequence $(\mathcal{R}_{\mu-i})_{i\in[\mu+1]}$: for each $i\in[\mu]$ there is an extractor $\mathrm{Ext}_i$ that, given a statement $x_i$ and $\ell(k-1)+1$ accepting transcripts $(\pi_i,c_{i,j},w_{i+1,j})$ with challenges in $SS(S,\ell,k)$ and each $w_{i+1,j}$ a valid next-round witness, outputs $w_i$ with $(x_i,w_i)\in\mathcal{R}_{\mu-i}$.
- **Lemma 2 (= Theorem 2 of [CMNW24]):** if a $(2\mu+1)$-message public-coin recursive protocol is round-by-round $\ell$-CW $k$-special sound and $(\ell+1)^\mu=\mathrm{poly}(\lambda)$, then it is knowledge sound for $\mathcal{R}$ with knowledge error $\ \mu\,\ell(k-1)/|S|$.

### 3.11 Reduction of knowledge (Kothapalli–Parno [KP23])

Def. 12: protocol $\Pi$ from $\mathcal{R}_1$ to $\mathcal{R}_2$: $\langle P(\mathrm{pp},u_1,w_1),V(\mathrm{pp},u_1)\rangle\to(u_2,w_2)$ with completeness, knowledge soundness ($\Pr[u_1,E(\mathrm{pp},u_1,w_1^*)\in\mathcal{R}_1]\approx\Pr[\langle P^*,V\rangle\in\mathcal{R}_2]$) and **public reducibility** (deterministic poly-time $f$ with $f(\mathrm{pp},u_1,\mathrm{tr})=u_2$).
Theorem 1 (KP23 Thm 5): sequential composition $\Pi_1\diamond\Pi_2$ reduces $\mathcal{R}_1\to\mathcal{R}_3$.
Theorem 2 (KP23 Thm 6): parallel composition $\Pi_1\times\Pi_2$ reduces $\mathcal{R}_1\times\mathcal{R}_3\to\mathcal{R}_2\times\mathcal{R}_4$.
HyperWolf's core protocol = $(k-1)$ sequential reductions of knowledge $\mathcal{R}_k\to\mathcal{R}_{k-1}\to\cdots\to\mathcal{R}_1$ plus a base proof for $\mathcal{R}_1$.

---

## 4. Relations

### 4.1 The unified evaluation identity (technique overview, paper §3.1)

Both univariate and multilinear evaluation are instances of a tensor/hypercube contraction. With $N=b_1b_0$ (2-D case, Brakedown-style [GLS+21]):

$$y=\Big[F\cdot\vec a_0\Big)\cdot\vec a_1,\qquad F=\begin{pmatrix} f_0&f_1&\cdots&f_{b_0-1}\\ f_{b_0}&f_{b_0+1}&\cdots&f_{2b_0-1}\\ \vdots&&&\vdots\\ f_{(b_1-1)b_0}&\cdots&&f_{b_1b_0-1}\end{pmatrix}$$

- **Univariate** $f(X)=\sum_{i=0}^{N-1}f_iX^i$, point $u\in\mathbb{Z}_q$:
  $\vec a_0=(1,u,u^2,\dots,u^{b_0-1})\in\mathbb{Z}_q^{b_0}$, $\vec a_1=(1,u^{b_0},u^{2b_0},\dots,u^{(b_1-1)b_0})\in\mathbb{Z}_q^{b_1}$.
- **Multilinear** $f=\sum f_{\mathrm{bits}}\prod X_i^{\mathrm{bit}}$, $N=2^\ell$, point $\vec u\in\mathbb{Z}_q^\ell$:
  $\vec a_0=\bigotimes_{i=0}^{\log b_0-1}(1,u_i)$, $\vec a_1=\bigotimes_{i=\log b_0}^{\ell-1}(1,u_i)$.
- In both cases $\vec a_1\otimes\vec a_0=\vec x$ = the evaluation vector (powers of $u$ resp. subset-products of the $u_i$).

**HyperWolf generalization ($k$-D).** Reshape the length-$N$ coefficient vector, $N=\prod_{i=0}^{k-1}b_i$ (then further ring-pack and gadget-decompose the innermost axis), into a $b_{k-1}\times\cdots\times b_0$ hypercube $[F]$; prepare $k$ evaluation vectors $\vec a_0,\dots,\vec a_{k-1}$; evaluation:

$$y=\Big(\cdots\big(F(F([F])\cdot\vec a_0)\cdot\vec a_1\big)\cdot\vec a_2\cdots\Big)\cdot\vec a_{k-1}\tag{Eq. 2}$$

$F(\cdot)$ maps a $(k-i)$-dim hypercube of size $b_{k-1}\times\cdots\times b_i$ to a "$(k-i-1)$-dim hypercube matrix" of size $(b_{k-1}\cdots b_{i+1})\times b_i$ — i.e. the *last* axis becomes the column axis and is contracted with $\vec a_i$.

Auxiliary vectors, general $(b_j)$:

- Univariate: $\vec a_i=\big(1,\ u^{\prod_{j=0}^{i-1}b_j},\ u^{2\prod_{j=0}^{i-1}b_j},\ \dots,\ u^{(b_i-1)\prod_{j=0}^{i-1}b_j}\big)$ for $i\in[k]$ — the hypercube multi-index $(i_{k-1},\dots,i_0)$ is exactly the base-$(b_0,\dots,b_{k-1})$ decomposition of the monomial exponent $\sum_j i_j\prod_{j'<j}b_{j'}$.
- Multilinear: $\vec a_i=\bigotimes_{j=\sum_{j'<i}\log b_{j'}}^{\sum_{j'\le i}\log b_{j'}-1}(1,u_j)$, and $\bigotimes_{i=0}^{k-1}\vec a_i=\vec x$.

Footnote 3 of the paper: unlike standard MLEs, coefficients are *not* placed on Boolean hypercube vertices of a multilinear extension; they are placed in a multidimensional array (only the multilinear *evaluation point* structure is tensorial). Figure 1 illustrates $k=3$.

### 4.2 The generalized relation $\mathcal{R}_k$ (paper Eq. 3)

Accounting for the ring-packing factor $d$ and gadget factor $\iota$, define $\bar N=\prod_{i=0}^{k-1}b_i\,d$ (the paper writes both $N=\prod b_i$ and $N=\prod b_i d$ depending on context; the operative length is $N=b^kd$ integer coefficients).

$$
\boxed{
\begin{aligned}
\mathcal{R}_k=\Big\{&\big(x^{(k)},w\big):\\
&x^{(k)}=\Big(\mathrm{pp}^{(k)},\ \mathrm{cm}^{(k)}_{\mathrm{out}},\ y^{(k)},\ (\vec a_j)_{j\in[k]}\Big),\quad \mathrm{pp}^{(k)}=(\mathbf A^{(k)},\mathbf B^{(k)});\\
&w=\Big(s^{(k)},\ \big(D(s_i^{(k-1)}),\ c_{\min,i}^{(k-1)}\big)_{i\in[b_{k-1}]}\Big);\\
&\forall i\in[b_{k-1}]:\quad \mathrm{Com}\big(D(s_i^{(k-1)})\big)=c_{\min,i}^{(k-1)},\qquad \big\|D(s_i^{(k-1)})\big\|\le\beta^{(k-1)};\\
&\hat t_c=G^{-1}_{\delta_t,\,b_{k-1}\kappa}\big((c_{\min,i}^{(k-1)})_{i\in[b_{k-1}]}\big),\qquad \mathrm{cm}^{(k)}_{\mathrm{out}}=\mathbf B^{(k)}\,\hat t_c;\\
&\mathrm{Fold}^{(k)}\big(s^{(k)},(\vec a_j)_{j\in[k-1]}\big)\cdot\vec a_{k-1}=y^{(k)}\ \Big\}
\end{aligned}}
\tag{Eq. 3}
$$

Where:

- $D:\ F^{b_{r-1}\times\cdots\times b_0}\to F^{\prod_{j=0}^{r-1}b_j}$ is the **flattening** operator (sequential concatenation of edges — row-major with the *first* index slowest, the innermost/last index fastest).
- The **witness** $s^{(k)}\in R_q^{b_{k-1}\times b_{k-2}\times\cdots\times b_0\iota}$ (a $k$-dim hypercube of ring elements whose last axis is the gadget-decomposed innermost axis, size $b_0\iota$).
- The $b_{k-1}$ **flattened slices** $D(s_i^{(k-1)})\in R_q^{(\prod_{j=0}^{k-2}b_j)\iota}$ are the slices of $s^{(k)}$ along the $k$-th dimension (the *outermost* axis, index $i\in[b_{k-1}]$).
- $c_{\min,i}^{(k-1)}=\mathbf A^{(k)}\,D(s_i^{(k-1)})\in R_q^\kappa$ — inner Ajtai commitments (one per slice).
- The **statement** carries: commitment parameters $\mathrm{pp}^{(k)}=(\mathbf A^{(k)},\mathbf B^{(k)})$, the outer commitment $\mathrm{cm}^{(k)}_{\mathrm{out}}$ (which binds the gadget-decomposed stack of inner commitments), a ring element $y^{(k)}$ (constant term = evaluation result), and the $k$ integer evaluation vectors $(\vec a_j)_{j\in[k]}$.
- Three witness obligations: (1) binding to inner/outer commitments; (2) norm bound $\beta^{(k-1)}$ per flattened slice; (3) folded inner product $=\ y^{(k)}$.

The **Fold operator** (Eq. 4) — the algebraic heart:

$$\mathrm{Fold}^{(k)}\big(s^{(k)},(\vec a_j)_{j\in[k-1]}\big)=F\Big(\cdots F\big(F(s^{(k)})\cdot\sigma_{-1}(M_R(\vec a_0))\big)\cdot\vec a_1\big)\cdot\vec a_2\cdots\Big)\cdot\vec a_{k-2}\tag{Eq. 4}$$

Notes on Eq. 4:

- The **first** contraction is along the *innermost* (gadget-decomposed, size $b_0\iota$) axis, with the ring vector $\sigma_{-1}(M_R(\vec a_0))$ where $\vec a_0$ is the *gadget-expanded* evaluation vector (see Protocol 3 step 3: $\vec a_0\leftarrow G^T_{\delta,b_0d}\vec a_0$ first). The constant-term identity of §3.5 makes this equal the plain integer inner product $\langle\text{coeffs},\vec a_0\rangle$.
- Subsequent contractions (axes $b_1,\dots,b_{k-2}$) use plain integer vectors $\vec a_j$ (scalars lifted into $R_q$).
- Output: $\mathrm{fold}^{(k)}\in R_q^{b_{k-1}}$ (only the outermost axis survives); the relation then takes $\langle\mathrm{fold}^{(k)},\vec a_{k-1}\rangle=y^{(k)}$.

**Exact dimension bookkeeping (uniform $b$, verified against the paper):**

| object | shape / length |
|---|---|
| $f$'s coefficient vector | $N=b^kd$ integers |
| ring-packed $\vec f=(f_0,\dots,f_{b^k-1})$, $f_i=\sum_{j=0}^{d-1}f_{id+j}X^j$ | $b^k$ ring elements |
| $\vec s=G^{-1}_{\delta,b^k}(\vec f)$ | $b^k\iota$ ring elements |
| $s^{(k)}$ (parse of $\vec s$) | axes $(b,\dots,b\ [\times k-1],\ b\iota)$ — $k$ axes |
| $D(s_i^{(k-1)})$, $i\in[b]$ | $b^{k-1}\iota$ ring elements each ($b^{k-1}\iota d$ integers) |
| $s^{(k-r)}$ (after $r$ folds) | axes $(b,\dots,b\ [\times k-r-1],\ b\iota)$ |
| $D(s_i^{(k-r-1)})$, $i\in[b]$ | $b^{k-r-1}\iota$ ring elements |
| $s^{(1)}$ (final) | $b\iota$ ring elements (1-D) |
| $\mathbf A^{(k-r)}=\vec 1^T_{b^{k-r-2}}\otimes\mathbf A$ | $\kappa\times b^{k-r-1}\iota$ |
| $\mathbf B^{(k-r)}=\vec 1^T_{b}\otimes\mathbf B$ | $\kappa\times b\kappa\iota'$ |
| $\Pi^{(k-r)}=\vec 1^T_{b^{k-r-2}}\otimes M_R(\Pi)$ | $256\times b^{k-r-1}\iota$ (over $R_q$) |

### 4.3 Relation to Brakedown / Greyhound two-dimensional structure

[GLS+21] (Brakedown) and [NS24] (Greyhound, via Labrador) reshape $\vec f\in\mathbb{Z}^N$ into an $n\times n$ matrix ($n^2=N$) and split $f(x)=y$ into two sub-relations: an inner product of a length-$n$ vector with an $n\times n$ matrix, then an inner product of two length-$n$ vectors proved with a (bi)variate sumcheck — $O(n)=O(\sqrt N)$ proof & verification. HyperWolf:

- generalizes the 2-D tensor to a **$k$-D tensor (hypercube)** $b_{k-1}\times\cdots\times b_0$;
- replaces the one-shot bivariate sumcheck with a **$k$-round recursive reduction of knowledge**, each round folding the *outermost* axis with a challenge vector $\vec C^{(k-r)}\in\mathcal{C}^{b_{k-r-1}}$ (dimension drops by one);
- per-round communication & verification are $O(N^{1/k})$ (dominated by $b$ slices × 256 ring projections + $b$ commitments), total $O(kN^{1/k})$;
- setting $b=2$, $k=\log_2(N/d)$ gives $O(\log N)$ proof & verifier;
- keeps the prover **linear** because each round touches the (geometrically shrinking) hypercube once: $O(b^k+b^{k-1}+\cdots+b)=O(2b^k)=O(N)$ ring-element operations;
- moves everything into $R_q$ (ring packing) so both the normslack (M-SIS $\ell_2$) and the commitment sizes stay small, and challenges become *ring* elements with a $>2^{128}$-sized space under $\tau=\sqrt{71}$.

---

## 5. Protocols

This section transcribes every protocol figure line-by-line.

### 5.1 Protocol 1 — Core Protocol for proving $\mathcal{R}_k$ (paper §4.1)

```
Public Inputs:
    A ∈ R_q^{κ×b0·ι},  B ∈ R_q^{κ×κι'},                       (base keys)
    (a_j ∈ Z_q^{b_j})_{j∈[k]\{0}},  a0 ∈ Z_q^{b0·ι} (gadget-expanded, see §5.4),
    y^{(k)} ∈ Z_q,  cm_out^{(k)} ∈ R_q^κ

Private Inputs (witness w):
    s^{(k)} ∈ R_q^{b_{k-1}×...×b0·ι},
    (D(s_i^{(k-1)}) ∈ R_q^{(∏_{j=0}^{k-2} b_j)·ι},  c_min,i^{(k-1)} ∈ R_q^κ)_{i∈[b_{k-1}]}
```

**Initial Phase**

- **V → P:** $\Pi\leftarrow\mathcal{D}^{256\times b_0\iota d}$ — the JL matrix with iid entries $-1/0/+1$ w.p. $1/4,\ 1/2,\ 1/4$.

**Round loop:** for $r=0$ to $k-2$ (i.e. $k-1$ rounds), reducing $\mathcal{R}_{k-r}\to\mathcal{R}_{k-r-1}$:

1. **P and V construct** (deterministically, from the base keys):
   - $\mathbf A^{(k-r)}=\vec 1^T_{\prod_{j=1}^{k-r-2}b_j}\otimes\mathbf A\ \in R_q^{\kappa\times(\prod_{j=0}^{k-r-2}b_j)\iota}$  (horizontal tiling; for $r=0$ this is $\vec 1^T_{b^{k-2}}\otimes\mathbf A$; note $\prod_{j=1}^{k-r-2}b_j=1$ when $k-r=2$),
   - $\mathbf B^{(k-r)}=\vec 1^T_{b_{k-r-1}}\otimes\mathbf B\ \in R_q^{\kappa\times b_{k-r-1}\kappa\iota}$,
   - $\Pi^{(k-r)}=\vec 1^T_{\prod_{j=1}^{k-r-2}b_j}\otimes M_R(\Pi)\ \in R_q^{256\times(\prod_{j=0}^{k-r-2}b_j)\iota}$.
2. **P computes:**
   - the folded vector $\mathrm{fold}^{(k-r)}=\mathrm{Fold}^{(k-r)}\big(s^{(k-r)},(\vec a_j)_{j\in[k-r-1]}\big)\in R_q^{b_{k-r-1}}$ (Eq. 4 with $k\to k-r$; the *final* $\vec a_{k-r-1}$ contraction is *not* applied here — it is the verifier's check),
   - for each $i\in[b_{k-r-1}]$: the JL projection $\ \vec p_i^{(k-r)}=\sigma_{-1}(\Pi^{(k-r)})\cdot D(s_i^{(k-r-1)})\in R_q^{256}$.
3. **P → V (round message $\pi_r$):**
   $$\pi_r=\Big(\mathrm{fold}^{(k-r)},\ \big(\vec p_i^{(k-r)},\ t_i^{(k-r-1)}\big)_{i\in[b_{k-r-1}]}\Big),\qquad t_i^{(k-r-1)}\equiv c_{\min,i}^{(k-r-1)}\in R_q^\kappa\ \text{(the inner commitments, sent in the clear)}.$$
4. **V checks:**
   1. $\langle\mathrm{fold}^{(k-r)},\vec a_{k-r-1}\rangle\stackrel{?}{=}y^{(k-r)}$;
   2. $\displaystyle\sum_{j=0}^{255}\big(\mathrm{ct}(\vec p_{i,j}^{(k-r)})\big)^2\ \le\ 128\cdot\big(\beta^{(k-r-1)}\big)^2,\qquad\forall i\in[b_{k-r-1}]$  (JL norm check on constant terms of the 256 projections);
   3. let $\hat t_c=G^{-1}_{\delta_t,\,b_{k-r-1}\kappa}\big((c_{\min,i}^{(k-r-1)})_{i\in[b_{k-r-1}]}\big)$; verify $\ \mathbf B^{(k-r)}\,\hat t_c\stackrel{?}{=}\mathrm{cm}^{(k-r)}_{\mathrm{out}}$  (outer binding);
   4. **if $r>0$** (cross-round consistency): $\displaystyle\sum_{j=0}^{b_{k-r}-1}C_j^{(k-r+1)}\,\vec p_j^{(k-r+1)}\ \stackrel{?}{=}\ \sum_{i=0}^{b_{k-r-1}-1}\vec p_i^{(k-r)}$.
5. **V → P:** challenge $\vec C^{(k-r)}\in\mathcal{C}^{\,b_{k-r-1}}$ (each component an invertible-difference ring challenge).
6. **P computes the next-round witness** $w_{r+1}=\big(s^{(k-r-1)},(D(s_i^{(k-r-2)}),c_{\min,i}^{(k-r-2)})_{i\in[b_{k-r-2}]}\big)$:
   - $\displaystyle s^{(k-r-1)}=\sum_{i=0}^{b_{k-r-1}-1}C_i^{(k-r)}\,s_i^{(k-r-1)}$  (fold the outermost axis),
   - $c_{\min,i}^{(k-r-2)}=\mathbf A^{(k-r-1)}\,D(s_i^{(k-r-2)})$  (re-commit the new slices).
7. **P and V compute the next statement** $x_{r+1}=\big(\mathrm{pp}^{(k-r-1)},(\vec a_j)_{j\in[k-r-1]},y^{(k-r-1)},\mathrm{cm}^{(k-r-1)}_{\mathrm{out}}\big)$:
   - $\ y^{(k-r-1)}=\langle\mathrm{fold}^{(k-r)},\vec C^{(k-r)}\rangle$ (both parties);
   - $\ \mathrm{cm}^{(k-r-1)}_{\mathrm{out}}=\mathbf B\,G^{-1}_{\delta_t,\kappa}\big(\sum_{i=0}^{b_{k-r-1}-1}C_i^{(k-r)}\,c_{\min,i}^{(k-r-1)}\big)$ (both parties — from the *prover-sent* inner commitments of round $r$ and the fresh challenge; note this is the $\kappa$-length stack form, and it coincides with the $b_{k-r-2}\kappa$ form $\mathbf B^{(k-r-1)}G^{-1}_{\delta_t,\,b_{k-r-2}\kappa}((c_{\min,i}^{(k-r-2)})_i)$ used in the completeness proof, Eq. 5 — the prover-side next-round commitments bind to the same value).

**Final Check (Round $k-1$, base relation $\mathcal{R}_1$):**

- **P → V:** $s^{(1)}\in R_q^{b_0\iota}$ — the fully-folded 1-D witness, sent in the clear (with small-coefficient encoding).
- **V checks:**
  1. $\mathrm{ct}\big(\langle\sigma_{-1}(M_R(\vec a_0)),s^{(1)}\rangle\big)\stackrel{?}{=}\mathrm{fold}^{(2)}\cdot\vec C^{(2)}=y^{(1)}$  (evaluation consistency pinned to the revealed witness);
  2. $\sigma_{-1}(\Pi)\,s^{(1)}\stackrel{?}{=}\sum_{i=0}^{b_1-1}C_i^{(2)}\,\vec p_i^{(2)}$  (JL projection consistency pinned to the revealed witness);
  3. $\|s^{(1)}\|\stackrel{?}{=}\beta^{(0)}$ bound: $\ \sigma_{-1}(\Pi)s^{(1)}=\sum_i C_i^{(2)}\vec p_i^{(2)}$, $\ \mathbf A\,s^{(1)}\stackrel{?}{=}\sum_{i=0}^{b_1-1}C_i^{(2)}\,t_i^{(1)}$  (inner-commitment binding pinned to the revealed witness), and $\|s^{(1)}\|\le\beta^{(0)}$.

**Why the cross-round consistency (check 4) works.** With the row-major flattening $D$ (first index slowest), the concatenation of the current-round slices *is* the full flattening of the current hypercube, and
$$\sum_j C_j^{(k-r+1)}\vec p_j^{(k-r+1)}=\sigma_{-1}(\Pi^{(k-r+1)})\,D(s^{(k-r)})=\sigma_{-1}(\Pi^{(k-r)})\!\!\sum_{i}\!D(s_i^{(k-r-1)})=\sum_i\vec p_i^{(k-r)},$$
because $\Pi^{(k-r+1)}$ and $\Pi^{(k-r)}$ are tilings of the *same* $M_R(\Pi)$ and each block of $b_0\iota$ consecutive columns is multiplied by the same block matrix. (The verifier never needs the expanded matrices explicitly — only the seed of $\Pi$ and the current block count.)

**What is committed / sampled / collapsed per round (summary):**

| item | round $r$ |
|---|---|
| committed (prover→verifier, in clear) | $\mathrm{fold}^{(k-r)}\in R_q^{b}$; $\vec p_i^{(k-r)}\in R_q^{256}$ for $i\in[b]$; $c_{\min,i}^{(k-r-1)}\in R_q^{\kappa}$ for $i\in[b]$ |
| challenge sampled | $\vec C^{(k-r)}\in\mathcal{C}^b$ ($b$ ring challenges, pairwise invertible differences) |
| dimension collapse | outermost axis $b_{k-r-1}$ folded away: $s^{(k-r)}\ (\,b_{k-r-1}\!\times\!\cdots)\ \to s^{(k-r-1)}\ (\,b_{k-r-2}\!\times\!\cdots)$; statement updated: $y^{(k-r-1)}=\langle\mathrm{fold}^{(k-r)},\vec C^{(k-r)}\rangle$, $\mathrm{cm}_{\mathrm{out}}^{(k-r-1)}=\mathbf B\,G^{-1}_{\delta_t,\kappa}(\sum_i C_i^{(k-r)}c_{\min,i}^{(k-r-1)})$ |
| JL matrix | fixed $\Pi$ (seeded), tiled per level: $\Pi^{(k-r)}=\vec 1^T_{b^{k-r-2}}\otimes M_R(\Pi)$ |

#### 5.1.1 Per-round dimension trace (concrete, $b=2$, $d=64$, $\iota=32$, $\kappa=64$)

For $N=2^{15}$ ($k=9$, rounds $r=0..7$) — every row is one round of Protocol 1:

| $r$ | relation | witness shape $s^{(k-r)}$ | slices $D(s_i)$ len (ring elts) | $\mathbf A^{(k-r)}$ cols | $\Pi^{(k-r)}$ cols | $\mathrm{fold}^{(k-r)}$ len | $\vec C$ len | msg size (ring elts) |
|---|---|---|---|---|---|---|---|---|
| 0 | $\mathcal{R}_9$ | $2\times2\times2\times2\times2\times2\times2\times2\times64$ | $2^8\cdot32=8192$ | $8192$ | $8192$ | $2$ | $2$ | $642$ |
| 1 | $\mathcal{R}_8$ | $2^7\times64$ | $4096$ | $4096$ | $4096$ | $2$ | $2$ | $642$ |
| 2 | $\mathcal{R}_7$ | $2^6\times64$ | $2048$ | $2048$ | $2048$ | $2$ | $2$ | $642$ |
| 3 | $\mathcal{R}_6$ | $2^5\times64$ | $1024$ | $1024$ | $1024$ | $2$ | $2$ | $642$ |
| 4 | $\mathcal{R}_5$ | $2^4\times64$ | $512$ | $512$ | $512$ | $2$ | $2$ | $642$ |
| 5 | $\mathcal{R}_4$ | $2^3\times64$ | $256$ | $256$ | $256$ | $2$ | $2$ | $642$ |
| 6 | $\mathcal{R}_3$ | $2^2\times64$ | $128$ | $128$ | $128$ | $2$ | $2$ | $642$ |
| 7 | $\mathcal{R}_2$ | $2\times64$ | $64$ | $64$ | $64$ | $2$ | $2$ | $642$ |
| final | $\mathcal{R}_1$ | $s^{(1)}\in R_q^{64}$ sent | — | $\mathbf A$ ($64$ cols) | $\Pi$ ($64$ cols) | — | — | $64$ (small digits) |

(the "last axis" of every $s^{(k-r)}$ is the $b\iota=64$ gadget-decomposed innermost axis; each round removes one outer $\times2$ axis.) Total proof = $8\times642+64$ ring elements $=5200$ ring elements $\times16$ B $=80.3$ KB ✓ matches Table 2.

For $N=2^{25}$: same table with 18 rounds; witness at round 0 has $2^{18}\cdot32=2^{23}$ ring elements per slice × 2 slices.

#### 5.1.2 Prover pseudocode (Python-like, `lzk` style)

```python
def hyperwolf_prover(pp, st, a_vecs, y_claim, fs):
    # pp: (A in R_q^{kappa x b0*iota}, B in R_q^{kappa x kappa*iota'})
    # st: (s_k hypercube ndarray of ring elts, slices D(s_i), c_min[i])
    A, B, Pi_seed = pp.A, pp.B, fs.sample_jl()          # V -> P: Pi <- D^{256 x b0*iota*d}
    Pi = expand_jl(Pi_seed)                               # int8 array (256, b0*iota*d)
    PiR = M_R_matrix(Pi)                                 # R_q^{256 x b0*iota}
    PiR_conj = sigma_conj_matrix(PiR)                    # entrywise sigma_{-1}
    a0_ext = expand_a0(a_vecs[0])                         # R_q^{b0*iota}: tile delta^e * M_R(a0)[t], e in [iota]
    s, c_min, Ds = st.s, st.c_min, st.slices
    y, proof = y_claim, []
    C_prev, p_prev, fold_prev = None, None, None
    for r in range(0, k-1):
        m = s.shape[0]                                   # b_{k-r-1} = number of slices
        # 1. fold vector: contract innermost axis with a0_ext, then axes 1..k-r-2
        fold = fold_engine(s, a0_ext, a_vecs[1:k-r-1])   # R_q^{m}, Eq. 4
        # 2. JL projections of each slice
        Pi_lvl = tile(PiR_conj, blocks=num_blocks(s))    # sigma_{-1}(Pi^{(k-r)})
        p = [ring_matvec(Pi_lvl, Ds[i]) for i in range(m)]   # each in R_q^{256}
        # 3. send message
        proof.append((fold, p, c_min))
        # 4. challenge (Fiat-Shamir)
        C = fs.sample_challenges(b=m)                    # C^~(k-r) in C^m, op-norm rejected
        # 5. fold the witness along the outermost axis
        s = sum(C[i] * s[i] for i in range(m))           # new hypercube, one axis fewer
        Ds = [flatten(s[i]) for i in range(s.shape[0])]  # new slices
        # 6. re-commit new slices with A^{(k-r-1)} = tile trick
        A_next_cols = Ds[0].length
        c_min = [block_sum_matvec(A, Ds[i], block=b0*iota) for i in range(len(Ds))]
        # 7. statement update (both parties)
        y = ring_dot(fold, C)                             # <fold, C> in R_q
        cm_out = B @ gadget_decompose(stack(c_min), base=delta_t)  # kappa form
        C_prev, p_prev, fold_prev = C, p, fold
    # final round: reveal s^{(1)}
    proof.append(s)                                      # s in R_q^{b0*iota}
    return proof
```

#### 5.1.3 Verifier pseudocode

```python
def hyperwolf_verifier(pp, cm, a_vecs, y_claim, proof, fs):
    A, B = pp.A, pp.B
    Pi = expand_jl(fs.sample_jl());  PiR = sigma_conj(M_R_matrix(Pi))
    a0_ext = expand_a0(a_vecs[0])
    y, cm_out, C_hist, p_hist = y_claim, cm, [], []
    for r in range(0, k-1):
        fold, p, c_min = proof[r]
        m = len(p)
        # check 1: evaluation
        assert z_dot(fold, a_vecs[k-r-1]) == y                       # scalar IP mod q
        # check 2: JL norm bound per slice
        for i in range(m):
            assert sum(int(ct(p[i][j]))**2 for j in range(256)) <= 128 * beta[k-r-1]**2
        # check 3: outer commitment binding
        t_hat = gadget_decompose(stack(c_min), base=delta_t)         # R_q^{m*kappa*iota'}
        assert block_tile_matvec(B, t_hat, block=kappa*iota') == cm_out
        # check 4: cross-round projection consistency
        if r > 0:
            lhs = sum(C_hist[-1][j] * p_hist[-1][j] for j in range(len(p_hist[-1])))
            rhs = sum(p[i] for i in range(m))
            assert lhs == rhs
        # challenge + statement update
        C = fs.sample_challenges(b=m)
        y = ring_dot(fold, C)
        cm_out = B @ gadget_decompose(stack(c_min), base=delta_t)   # B G^{-1}(sum C_i c_min_i)
        # NOTE: uses sum(C_i * c_min[i]) for the kappa form
        C_hist.append(C); p_hist.append(p)
    # final checks
    s1 = proof[k-1]
    assert ct(ring_inner(sigma_conj(a0_ext), s1)) == y
    assert ring_matvec(sigma_conj(PiR), s1) == sum(C_hist[-1][i] * p_hist[-1][i] for i in range(len(p_hist[-1])))
    assert A @ s1 == sum(C_hist[-1][i] * proof[k-2][2][i] for i in range(len(p_hist[-1])))
    assert ring_norm(s1) <= beta[0]
    return True
```

*(pseudocode elides: hiding randomness, canonical serialization for FS, block-tiling implementations of $\mathbf A^{(k-r)},\mathbf B^{(k-r)},\Pi^{(k-r)}$, and the dual form of the $\mathrm{cm}_{\mathrm{out}}$ update — see §8.4 pitfall 12.)*

### 5.2 Protocol 4 (Appendix A) — worked example, $k=3$ ($N=b_2b_1b_0d$)

Transcribed verbatim (with $\vec 1_m$ the all-one vector of length $m$):

```
Public inputs:
    A ∈ R_q^{κ×b0·ι}, B ∈ R_q^{κ×κι'},
    a2 ∈ Z_q^{b2}, a1 ∈ Z_q^{b1}, a0 ∈ Z_q^{b0·ι} (expanded), y^{(3)} ∈ Z_q, cm_out^{(3)}
Private inputs:
    s^{(3)} ∈ R_q^{b2×b1×b0·ι},
    (D(s_i^{(2)}) ∈ R_q^{b1·b0·ι}, c_min,i^{(2)} ∈ R_q^κ)_{i∈[b2]}
```

**Round 0: $\mathcal{R}_3\to\mathcal{R}_2$**

1. V → P: $\Pi\leftarrow\mathcal{D}^{256\times b_0\iota d}$.
2. P and V construct: $\mathbf A^{(3)}=\vec 1^T_{b_1}\otimes\mathbf A$, $\mathbf B^{(3)}=\vec 1^T_{b_2}\otimes\mathbf B$, $\Pi^{(3)}=\vec 1^T_{b_1}\otimes M_R(\Pi)$.
3. P computes: $\mathrm{Fold}^{(3)}$ and $\vec p_i^{(3)}=\sigma_{-1}(\Pi^{(3)})D(s_i^{(2)})$ for all $i\in[b_2]$.
4. P → V: $\big(\mathrm{Fold}^{(3)},(\vec p_i^{(3)},c_{\min,i}^{(2)})_{i\in[b_2]}\big)$.
5. V checks:
   - (a) $\langle\mathrm{Fold}^{(3)},\vec a_2\rangle\stackrel{?}{=}y^{(3)}$;
   - (b) $\sum_{j=0}^{255}\mathrm{ct}(\vec p_{i,j}^{(3)})^2\le128\cdot(\beta^{(2)})^2$ for all $i\in[b_2]$;
   - (c) $\mathbf B^{(3)}\big(G^{-1}_{\delta_t,b_2\kappa}((c_{\min,i}^{(2)})_{i\in[b_2]})\big)\stackrel{?}{=}\mathrm{cm}^{(3)}_{\mathrm{out}}$.
6. V → P: $\vec C^{(3)}\in\mathcal{C}^{b_2}$.
7. P computes: $\ s^{(2)}=\sum_{i=0}^{b_2-1}C_i^{(3)}s_i^{(2)}\in R_q^{b_1\times b_0\iota}$, and $\big(D(s_i^{(1)})\in R_q^{b_0\iota},c_{\min,i}^{(1)}\in R_q^\kappa\big)_{i\in[b_1]}$.
8. P and V construct: $\mathbf A^{(2)}=\mathbf A$, $\mathbf B^{(2)}=\vec 1^T_{b_1}\otimes\mathbf B$, $\Pi^{(2)}=\Pi=M_R(\Pi)$.
9. P and V compute: $\ y^{(2)}=\langle\mathrm{Fold}^{(3)},\vec C^{(3)}\rangle$, $\ \mathrm{cm}^{(2)}_{\mathrm{out}}=\mathbf B\big(G^{-1}_{\delta_t,\kappa}(\sum_{i=0}^{b_2-1}C_i^{(3)}c_{\min,i}^{(2)})\big)$.

**Round 1: $\mathcal{R}_2\to\mathcal{R}_1$**

1. P computes: $\mathrm{Fold}^{(2)}=s^{(2)}\cdot\sigma_{-1}(M_R(\vec a_0))$ (with the last-axis contraction), and $\vec p_i^{(2)}=\sigma_{-1}(\Pi)\,D(s_i^{(1)})$ for $i\in[b_1]$. *(The paper prints "$\vec p_i^{(2)}=\Pi D(s_i^{(1)})$" here — a typographical omission of the $\sigma_{-1}$; Protocol 1 and the final check both require $\sigma_{-1}(\Pi)$, otherwise check (b) of Round 2 is inconsistent.)*
2. P → V: $\big(\mathrm{Fold}^{(2)},(\vec p_i^{(2)},c_{\min,i}^{(1)})_{i\in[b_1]}\big)$.
3. V checks:
   - (a) $\langle\mathrm{Fold}^{(2)},\vec a_1\rangle\stackrel{?}{=}y^{(2)}$;
   - (b) $\sum_{j=0}^{255}\mathrm{ct}(\vec p_{i,j}^{(2)})^2\le128\cdot(\beta^{(1)})^2$ for all $i\in[b_1]$;
   - (c) $\sum_{i=0}^{b_2-1}C_i^{(3)}\vec p_i^{(3)}\stackrel{?}{=}\sum_{i=0}^{b_1-1}\vec p_i^{(2)}$;
   - (d) $\mathbf B^{(2)}\big(G^{-1}_{\delta_t,b_1\kappa}((c_{\min,i}^{(1)})_{i\in[b_1]})\big)\stackrel{?}{=}\mathrm{cm}^{(2)}_{\mathrm{out}}$.
4. V → P: $\vec C^{(2)}\in\mathcal{C}^{b_1}$. P computes $s^{(1)}=\sum_{i=0}^{b_1-1}C_i^{(2)}s_i^{(1)}\in R_q^{b_0\iota}$.
5. P and V compute: $\ y^{(1)}=\langle\mathrm{Fold}^{(2)},\vec C^{(2)}\rangle$, $\ \mathrm{cm}^{(1)}_{\mathrm{out}}=\mathbf B\big(G^{-1}_{\delta_t,\kappa}(\sum_{i=0}^{b_1-1}C_i^{(2)}c_{\min,i}^{(1)})\big)$.

**Round 2 (Final Check):**

1. P → V: $s^{(1)}$.
2. V checks:
   - (a) $\langle s^{(1)},\sigma_{-1}(M_R(\vec a_0))\rangle\stackrel{?}{=}y^{(1)}$; $\ \|s^{(1)}\|\le\beta^{(0)}$;
   - (b) $\sigma_{-1}(\Pi)s^{(1)}\stackrel{?}{=}\sum_{i=0}^{b_1-1}C_i^{(2)}\vec p_i^{(2)}$; $\ \mathbf A\,s^{(1)}\stackrel{?}{=}\sum_{i=0}^{b_1-1}C_i^{(2)}c_{\min,i}^{(1)}$.

### 5.3 Protocol 2 — PC.Commit & PC.Open (paper §5.1)

```
Public parameters: pp = (A ∈ R_q^{κ×b0·ι}, B ∈ R_q^{κ×κι'})
```

**Commit(pp, $f\in\mathbb{Z}_q^{<N}[X]$ or $\mathbb{Z}_q[X_0,\dots,X_{\ell-1}]$) → (Com, st):**

1. Represent $f$ as $\vec f=(f_0,f_1,\dots,f_{N-1})$ (coefficients; multilinear order: $f_0+f_1X_0+f_2X_1+\cdots+f_{N-1}X_0X_1\cdots X_{\ell-1}$).
2. For $i=0,1,\dots,b^k-1$: $f_i=\sum_{j=0}^{d-1}f_{id+j}X^j\in R_q$ — ring-pack $d$ consecutive coefficients.
3. Let $\vec f=(f_0,\dots,f_{b^k-1})\in R_q^{b^k}$, compute $\vec s=G^{-1}_{\delta,b^k}(\vec f)$ — gadget-decompose every ring element into $\iota$ digit ring elements ($\vec s\in R_q^{\iota b^k}$).
4. Parse $\vec s$ into the $k$-dim hypercube $s^{(k)}$ of shape $b\times\cdots\times b\times b\iota$:
   - let $(s_i^{(k-1)})_{i\in[b]}$ be the slices of $s^{(k)}$ along the $k$-th (outermost) dimension;
   - $D(s_i^{(k-1)})\in R_q^{b^{k-1}\iota}$ the flattened slice;
   - $\mathbf A^{(k)}=\vec 1^T_{b^{k-2}}\otimes\mathbf A\in R_q^{\kappa\times b^{k-1}\iota}$;
   - for each $i\in[b]$: $c_{\min,i}^{(k-1)}=\mathbf A^{(k)}\,D(s_i^{(k-1)})$.
5. Define $\mathrm{cm}'=G^{-1}_{\delta_t,b\kappa}\big((c_{\min,i})_{i\in[b]}\big)$ and $\mathrm{cm}_{\mathrm{out}}=\mathbf B^{(k)}\,\mathrm{cm}'$, where $\mathbf B^{(k)}=\vec 1^T_b\otimes\mathbf B\in R_q^{\kappa\times b\kappa\iota}$.
6. $\mathrm{st}:=\big(s^{(k)},(D(s_i^{(k-1)}),c_{\min,i}^{(k-1)})_{i\in[b]}\big)$.
7. Return $(\mathrm{cm}_{\mathrm{out}},\mathrm{st})$.

**Open(pp, Com, $f$, st, $(c_i)_{i\in[b]}$) → {0,1}:**

1. Represent $f$ as $\vec f=(f_0,\dots,f_{N-1})$.
2. For $i=0,\dots,b^k-1$: $f_i=\sum_{j=0}^{d-1}f_{id+j}X^j\in R_q$.
3. Let $\vec f\in R_q^{N/d}$ and compute $\vec s=G^{-1}_{\delta,b^k}(\vec f)$.
4. If $\big(D(s_i^{(k-1)})\big)_{i\in[b]}\ne$ (stored slices of $s^{(k)}$) $\ \lor\ G_{\delta,b^k}(\vec s)\ne\vec f$: return 0. (Recomposition check: $G_{\delta,b^k}(G^{-1}_{\delta,b^k}(\vec f))=\vec f$ and the stored state is consistent with the claimed $f$.)
5. For each $i\in[b]$:
   - if $\mathbf A^{(k)}D(s_i^{(k-1)})\ne c_{\min,i}^{(k-1)}$ $\ \lor\ \mathbf B^{(k)}G^{-1}_{\delta_t,b\kappa}((c_{\min,i}^{(k-1)})_{i\in[b]})\ne\mathrm{cm}_{\mathrm{out}}$: return 0;
   - if $\|c_i\cdot D(s_i^{(k-1)})\|\ge\bar\beta$ $\ \lor\ \|c_i\|\ge\bar\tau$ $\ \lor\ c_i\notin R_q^\times$: return 0. (Slack/relaxation factors $(c_i)_{i\in[b]}$ from the slack space $\mathrm{SL}$.)
6. Return 1.

### 5.4 Protocol 3 — PC.Eval (paper §5.1)

```
Public parameters: pp = (A ∈ R_q^{κ×b0·ι}, B ∈ R_q^{κ×κι'})
Eval(pp, cm, u (univariate) or u⃗ ∈ Z_q^ℓ (multilinear), y; (f, st))
```

1. **Univariate case** ($f(X)\in\mathbb{Z}_q^{<N}[X]$): for $i=1,2,\dots,k-1$ compute
   $$\vec a_i=\big(1,u^{b^i},u^{2b^i},\dots,u^{(b-1)b^i}\big),\qquad \vec a_0=\big(1,u,u^2,\dots,u^{bd-1}\big)\in\mathbb{Z}_q^{bd}.$$
   (General $(b_j)$: $\vec a_i=(1,u^{\prod_{j<i}b_j},u^{2\prod_{j<i}b_j},\dots,u^{(b_i-1)\prod_{j<i}b_j})$; $\vec a_0$ spans the innermost $b_0d$ coefficient positions.)
2. **Multilinear case** ($f\in\mathbb{Z}_q[X_0,\dots,X_{\ell-1}]$, $N=2^\ell=2^{\log b\cdot k+\log d}$): compute
   $$\vec a_i=\bigotimes_{j=i\log b}^{(i+1)\log b-1}(1,u_j),\qquad \vec a_0=\bigotimes_{j=0}^{\log b+\log d-1}(1,u_j).$$
   (With $b=2$: $\vec a_i=(1,u_i)$ for each $i\ge1$ — one variable folded per round; $\vec a_0$ covers the first $\log(bd)$ variables.)
3. **Update** $\vec a_0\leftarrow G^T_{\delta,bd}\,\vec a_0$ — lift the innermost evaluation vector through the transpose gadget so it matches the decomposed innermost axis (see §8.4 for the exact index layout that this shorthand implies).
4. **P computes** $\ y=\big\langle\mathrm{Fold}^{(k)}\big(\mathrm{st}.s^{(k)},(\vec a_j)_{j\in[k-1]}\big),\vec a_{k-1}\big\rangle$.
5. **P and V define the instance–witness pair:** $x=\big(\mathrm{pp}^{(k)},\mathrm{cm}_{\mathrm{out}},(\vec a_j)_{j\in[k]},y\big)$, $w=\mathrm{st}$.
6. **P and V execute Protocol 1** to prove $(x,w)\in\mathcal{R}_k$.
7. **V checks** $\mathrm{ct}(y)\stackrel{?}{=}y$ (the claimed evaluation equals the constant term of the ring element $y$).

**Theorem 7.** The PC of Protocols 2+3 satisfies evaluation completeness, weak binding, and knowledge soundness under Module-SIS. (Completeness ← Thm 3; weak binding ← Thm 4; knowledge soundness ← Thm 5.)

### 5.4.1 Worked micro-example of the Fold operator ($k=2$, $b=2$, $d=2$, $\iota=2$)

To make Eq. 4 concrete, take $N=b^kd=8$ coefficients $f_0,\dots,f_7$, $d=2$, $b=2$, $\delta$ with $\iota=2$ digits. Then $\vec f\in R_q^{b^2}=R_q^4$ with $f_0=f_0+f_1X$, $f_1=f_2+f_3X$, $f_2=f_4+f_5X$, $f_3=f_6+f_7X$; $\vec s=G^{-1}_{\delta,4}(\vec f)\in R_q^{8}$; hypercube $s^{(2)}\in R_q^{2\times4}$ (2 slices, last axis $b\iota=4$):

- slice 0: $D(s_0^{(1)})=(\mathrm{dig}_0(f_0),\mathrm{dig}_1(f_0),\mathrm{dig}_0(f_1),\mathrm{dig}_1(f_1))$ — digits of the first two ring components;
- slice 1: $D(s_1^{(1)})=(\mathrm{dig}_0(f_2),\mathrm{dig}_1(f_2),\mathrm{dig}_0(f_3),\mathrm{dig}_1(f_3))$.

$\vec a_0=(1,u,u^2,u^3)$ ($b_0d=4$ positions), $\vec a_1=(1,u^4)$ ($b_1=2$). Expand $\vec a_0$ (§8.4 rule): for each ring-lift $M_R(\vec a_0)[t]=a_0[2t]+a_0[2t+1]X$ and digit $e\in\{0,1\}$:
$a^{ext}_0[t\iota+e]=\delta^eM_R(\vec a_0)[t]$, i.e. $a^{ext}_0=(\,a_0{+}a_1X,\ \delta(a_0{+}a_1X),\ a_2{+}a_3X,\ \delta(a_2{+}a_3X)\,)\in R_q^4$. Then

$$\mathrm{fold}^{(2)}=s^{(2)}\cdot\sigma_{-1}(a_0^{ext})=\Big(\sum_{j=0}^{3}s_0[j]\,\sigma_{-1}(a^{ext}_0[j]),\ \sum_{j=0}^{3}s_1[j]\,\sigma_{-1}(a^{ext}_0[j])\Big)\in R_q^2,$$

and $y=\langle\mathrm{fold}^{(2)},\vec a_1\rangle=\mathrm{fold}^{(2)}_0+u^4\,\mathrm{fold}^{(2)}_1$. One checks on each coefficient that this equals $\sum_{i=0}^{7}f_iu^i$: the constant-term identity of §3.5 gives $\mathrm{ct}(s_0[j]\sigma_{-1}(a^{ext}_0[j]))=\langle\mathrm{coeffs}(\mathrm{dig}(f)),a_0\rangle$-terms, and $G\vec s=\vec f$ recombines the digits with weights $\delta^e$. *(Build this as a unit test with $\delta=4$, $q=257$, $d=2$, $b=2$.)*

### 5.5 Batching (Appendix B)

Three cases:

1. **Multiple polynomials, single point** ($f_i(u)=v_i$ for $i\in[n]$): V samples $\vec\alpha\in\mathbb{Z}_q^n$; both compute $f=\sum_{i=0}^{n-1}\alpha_if_i$ and $y=\sum_i\alpha_iv_i$; run the evaluation protocol on $(f,u,y)$.
2. **Single polynomial, multiple points** ($f(u_i)=v_i$):
   - *Multilinear:* build the multilinear extension $\tilde f(\vec x)=\sum_{\vec b\in\{0,1\}^{\log N}}f(\vec b)\,\mathrm{eq}(\vec b,\vec x)$ with $\mathrm{eq}(\vec b,\vec x):=\prod_{i=0}^{\log N-1}\big(b[i]x[i]+(1-b[i])(1-x[i])\big)$; build $g(\vec x)=\sum_{i=0}^{n-1}\alpha_i\,\tilde f(\vec x)\,\mathrm{eq}(\vec x,\vec u_i)$ with V-sampled $\vec\alpha$; run a sumcheck for $\sum_{i=0}^{n-1}\alpha_iv_i=\sum_{\vec b\in\{0,1\}^{\log N}}g(\vec b)$; this reduces to checking $f(\vec r)=v$ and $\mathrm{eq}(\vec r,\vec u_i)=z_i$ at a verifier-random $\vec r$ — the latter computable by V, the former by the PCS of §5.3–5.4.
   - *Univariate:* substitute $X_i:=X^{2^i}$ to rewrite $f(X)=\sum f_jX^j$ in multilinear form $f(X_0,\dots,X_{\ell-1})=\sum_j f_j\prod X_i^{\mathrm{bit}_i(j)}$ with the same coefficient vector; set $\vec u_i=(u_i,u_i^2,\dots,u_i^{2^{\ell-1}})$ so that $f(\vec u_i)=f(u_i)$; then proceed as multilinear.
3. **Multiple polynomials, multiple points** ($f_i(\vec u_i)=v_i$): V samples $\vec\alpha$; P builds $g(\vec x)=\sum_{i=0}^{n-1}\alpha_i f_i(\vec x)\,\mathrm{eq}(\vec x,\vec u_i)$; sumcheck for $\sum_i\alpha_iv_i=\sum_{\vec b}g(\vec b)$; reduces to the evaluations of the $f_i$ at a common random $\vec r$, handled by case 1.

### 5.6 Fiat–Shamir / non-interactive form

The paper presents the interactive public-coin protocol; the NIZK is obtained by standard Fiat–Shamir: the initial $\Pi$ (or its seed) and each round's $\vec C^{(k-r)}\in\mathcal{C}^b$ are derived by hashing the evolving transcript (statement + all prover messages so far). Challenge derivation must sample ring elements from the Labrador distribution (23 zeros / 31 ±1 / 10 ±2) with 5–6× rejection for $\|c\|_{\mathrm{op}}<15$ — implement via seeded sampling from the FS digest (rejection is fine since acceptance probability is constant). No granular challenge-domain separation is specified in the paper — an implementer should fix a canonical transcript serialization and domain separators per round.

**Canonical transcript layout (implementation contract):**

```
T0 := H("hw:v1:param",  q, d, b, k, kappa, iota, iota', delta, delta_t,
         seed_A, seed_B)                          # public parameters
T1 := H("hw:v1:stmt",   T0, cm_out, ct(y),
         serialize(a_1..a_{k-1}), serialize(a0_ext), N, "uni"|"mul")
S_pi := H("hw:v1:jl",    T1)                     # seed -> Pi (256 x b0*iota*d trits)
for r in 0..k-2:
    M_r := H("hw:v1:msg",  T1, r, serialize(fold^{(k-r)}, p_i^{(k-r)}, c_min,i^{(k-r-1)}))
    C^{(k-r)} := SampleChallenges(H("hw:v1:chal", M_r), b)   # Labrador dist + op-norm reject
T_final := H("hw:v1:open", T1, serialize(s^{(1)}))
```

Each `serialize` is length-prefixed little-endian with balanced-representation ring elements; challenges are sampled with a deterministic PRG keyed by the digest and a fixed rejection policy (retry counter included in the derivation so prover/verifier agree). The proof $\pi=(\Pi\text{-seed is implicit},(M_r\text{ messages}),s^{(1)})$.

---

## 6. Soundness & Security

### 6.1 Theorem 3 (Completeness)

Let $\mathcal{C}\subset R_q$ have challenges with $\ell_2$ norm $\le\tau$ and operator norm $\le T$. Define $\bar N=\prod_{i=0}^{k-1}b_id$, $\iota=\lceil\log_\delta q\rceil$,
$$\beta^{(k-1)}=\frac\delta2\sqrt{b^{k-1}\iota d}\ \Big(=\ \sqrt{\bar N\iota/b}\cdot\tfrac\delta2\ \text{in the paper's Theorem-4 printing}\Big),\qquad
\beta^{(k-r-1)}=\sqrt{\tfrac{T\,b_{k-r}}{b_{k-r-1}}}\,\beta^{(k-r)}\ \ \text{(uniform }b:\ \sqrt T\cdot\beta^{(k-r)}\text{)}.$$
*(The PDF extraction of the two printed recursions is imperfect — Theorem 3 prints $\sqrt{T\,b_{k-r}/b_{k-r-1}}$, §5.2 uses a per-round growth of $\sqrt{2T}$ via $\gamma=2\beta^{(0)}=2(\sqrt{2T})^{k-1}\cdot(\ldots)$; the completeness proof's intermediate bound is $T\sqrt{b_{k-r-1}/b_{k-r-2}}\cdot\beta$. See §8.6 for the safe engineering choice.)*

Then Protocol 1 is complete.

**Proof structure (transcribed):** the interaction minus the initial $\Pi$ is a reduction of knowledge $\mathcal{R}_k\to\mathcal{R}_1$ plus a proof of $\mathcal{R}_1$. For each round $r$ one shows (i) $(x_r,w_r)\in\mathcal{R}_{k-r}\Rightarrow(x_{r+1},w_{r+1})\in\mathcal{R}_{k-r-1}$ and (ii) V accepts whenever $(x_r,w_r)\in\mathcal{R}_{k-r}$:

- *Inner product:* $\mathrm{Fold}^{(k-r-1)}(s^{(k-r-1)},(\vec a_j)_{j\in[k-r-2]},\vec a_{k-r-2}) = \mathrm{Fold}^{(k-r)}(s^{(k-r)},(\vec a_j)_{j\in[k-r-1]},\vec C^{(k-r)})=\langle\mathrm{fold}^{(k-r)},\vec C^{(k-r)}\rangle=y^{(k-r-1)}$ — multilinearity of the fold in the hypercube entries.
- *Norm:* $\ D(s_i^{(k-r-2)})=\sum_{j=0}^{b_{k-r-1}-1}C_j^{(k-r)}\,D(s_j^{(k-r-1)})[il:(i+1)l-1]$ with $l=\mathrm{len}(D(s_i^{(k-r-2)}))=(\prod_{j=0}^{k-r-3}b_j)\iota$, so $\|D(s_i^{(k-r-2)})\|\le\sqrt{T\,b_{k-r-1}/b_{k-r-2}}\,\beta^{(k-r-1)}=\beta^{(k-r-2)}$ (balanced-block heuristic; worst case gives $T\sqrt{b_{k-r-1}}\,\beta$ — see §8.6).
- *Inner-commitment binding:* $c_{\min,i}^{(k-r-1)}=\mathbf A^{(k-r)}D(s_i^{(k-r-1)})=[\mathbf A^{(k-r-1)}\cdots\mathbf A^{(k-r-1)}]\cdot$ (stacked blocks of $D(s_i^{(k-r-1)})$) — i.e. $\mathbf A^{(k-r)}$'s tiling means the commitment of each *sub-block* uses $\mathbf A^{(k-r-1)}$; hence
  $$\sum_{i=0}^{b_{k-r-1}-1}C_i^{(k-r)}c_{\min,i}^{(k-r-1)}=\mathbf A^{(k-r-1)}\!\!\sum_{j=0}^{b_{k-r-2}-1}\!\!D(s_j^{(k-r-2)})\qquad(\text{Eq. 5})$$
  and the new outer commitment satisfies $\mathrm{cm}^{(k-r-1)}_{\mathrm{out}}=\mathbf B^{(k-r-1)}G^{-1}_{\delta_t,b_{k-r-2}\kappa}((c_{\min,j}^{(k-r-2)})_j)=\mathbf B\,G^{-1}_{\delta_t,\kappa}\big(\sum_i C_i^{(k-r)}c_{\min,i}^{(k-r-1)}\big)$.
- *Projection consistency:* $\sum_{i=0}^{b_{k-r-2}-1}\vec p_i^{(k-r-1)}=\sigma_{-1}(\Pi^{(k-r-1)})\big(\sum_j C_j^{(k-r)}D(s_j^{(k-r-1)})[il:(i+1)l-1]\big)$-blocks $=\sum_j C_j^{(k-r)}\vec p_j^{(k-r)}$.

### 6.2 Theorem 4 (Round-by-round coordinate-wise special soundness)

Let $b_0=\cdots=b_{k-1}=b=(\bar N/d)^{1/k}$, $\beta^{(k-1)}=\sqrt{\bar N\iota/b}\cdot\delta/2$, $\beta^{(k-r-1)}=\sqrt{T/b_{k-r-1}}\cdot\beta^{(k-r)}$ *(as printed; see flag above)* for $r\in\{1,\dots,k-1\}$, with the constraint $\beta^{(r)}\le\sqrt{128/125}\cdot q$ — as printed; the operative requirement is Lemma 3's $b\le q/125$ plus JL slack so modular wrap-around cannot mask a long vector. Define
$$\gamma=\max_{r\in[k]}\big(\sqrt{b\,\beta^{(k-r)}}\big)\ \big(\approx\sqrt{2b}\,\beta^{(0)}=2\beta^{(0)}\ \text{for } b=2\big),\qquad
\beta'=\frac{\delta_t}{2}\sqrt{b\kappa\iota'}\ ,\quad \iota'=\lceil\log_{\delta_t}q\rceil .$$
Assuming MSIS hard for rank $\kappa$ and norm bound $\max(8T\gamma,\ \beta')$, Protocol 1 is round-by-round coordinate-wise special sound: for each round $r\in[k-1]$ there is a poly-time extractor $\mathrm{Ext}_r$ which, given $(b+1)$ accepting transcripts, extracts a valid witness $w_r\in\mathcal{R}_{k-r}(x_r)$ with soundness error $\le 2^{-126}$ and constant norm slack $\sqrt{128/30}\approx2$.

**Extractor logic (full transcription).** Fix round $r$. The $(b+1)$ transcripts share the first message $\pi_r$ and differ in challenges:
$$x_r=(\mathbf A^{(k-r)},\mathbf B^{(k-r)},(\vec a_j)_{j\in[k-r]},y^{(k-r)},\mathrm{cm}^{(k-r)}_{\mathrm{out}}),\quad
\pi_r=\big(\mathrm{fold}^{(k-r)},(\vec p_i^{(k-r)},c_{\min,i}^{(k-r-1)})_{i\in[b]}\big),$$
$$\vec c_{r,m}=(C_{m,i}^{(k-r)})_{i\in[b]},\qquad
w_{r+1,m}=\big(s_m^{(k-r-1)},(D(s_{i,m}^{(k-r-2)}),c_{\min,i,m}^{(k-r-2)})_{i\in[b]}\big),\ m\in[b+1],$$
with $(\vec c_{r,m})_{m\in[b+1]}\in SS(\mathcal{C},b,2)$ and $(x_{r+1,m},w_{r+1,m})\in\mathcal{R}_{k-r-1}$.

1. **Weak commitment opening.** Concatenate all $(D(s_{i,m}^{(k-r-2)}))_{i\in[b]}$ into $\vec S_m^{(k-r-1)}$ (length $b^{k-r-1}\iota$) — the full flattening of the next-round witness. It satisfies
   $$\vec S_m^{(k-r-1)}=\sum_{i=0}^{b-1}C_{m,i}^{(k-r)}\,D(s_i^{(k-r-1)})\tag{Eq. 6}$$
   (flattening of the fold). Fix $v\in[b]$; let $\vec C_b^{(k-r)}$ be the center and $\vec C_v^{(k-r)}$ differ from it only in coordinate $v$. Then
   $$\bar D(s_v^{(k-r-1)})=\frac{\vec S_b^{(k-r-1)}-\vec S_v^{(k-r-1)}}{\bar c_v^{(k-r)}},\qquad \bar c_v^{(k-r)}=\vec C_{b,v}^{(k-r)}-\vec C_{v,v}^{(k-r)}\ne0\ \text{(invertible)},\tag{Eq. 7}$$
   with $\|\bar c_v^{(k-r)}\cdot\bar D(s_v^{(k-r-1)})\|\le\sqrt{2b}\,\beta^{(k-r-2)}$ (difference of two flattenings, each $\le\sqrt b\,\beta^{(k-r-2)}$, Cauchy–Schwarz). Concatenating $(\bar D(s_i^{(k-r-1)}))_{i\in[b]}$ and reshaping gives the reconstructed hypercube $\bar s^{(k-r)}$. The $(t_i^{(k-r-1)})_i$ (= $c_{\min,i}$) are output unchanged (they were sent by the prover).
2. **Inner binding.** From Eq. 5 and the next-round validity: $\sum_i C_{m,i}^{(k-r)}c_{\min,i}^{(k-r-1)}=\sum_i c_{\min,i,m}^{(k-r-2)}=\mathbf A^{(k-r)}\vec S_m^{(k-r-1)}$. Combining with Eq. 7: $\bar c_v^{(k-r)}\mathbf A^{(k-r)}\bar D(s_v^{(k-r-1)})=\bar c_v^{(k-r)}c_{\min,v}^{(k-r-1)}$, hence $\mathbf A^{(k-r)}\bar D(s_v^{(k-r-1)})=c_{\min,v}^{(k-r-1)}$. If an alternative weak opening $(\bar D^*(s_v),(\bar c_v^{(k-r)})^*)$ also satisfied $\|(\bar c_v)^{*}\bar D^*\|\le\sqrt{2b}\beta^{(k-r-2)}$ and $\mathbf A^{(k-r)}\bar D^*=(c_{\min,v})$, then
   $$\mathbf A^{(k-r)}\Big(\bar c_v(\bar c_v)^*\bar D^*-\bar c_v(\bar c_v)^*\bar D\Big)=0\ \Rightarrow\ \text{nonzero MSIS solution of norm}\ \le4T\sqrt{2b}\,\beta^{(k-r-2)}\le8T\gamma,$$
   contradicting $\mathrm{MSIS}_{\kappa,\cdot,q,8T\gamma}$.
3. **Outer binding.** The check $\mathbf B^{(k-r)}G^{-1}_{\delta_t}((c_{\min,i})_i)=\mathrm{cm}^{(k-r)}_{\mathrm{out}}$ binds the outer commitment to the sent inner commitments under MSIS with rank $\kappa$ and norm bound $\beta'=(\delta_t/2)\sqrt{b\kappa\iota'}$ (the norm of the gadget-decomposed stack).
4. **Norm of the extracted witness (JL argument).** If $(\vec p_i^{(k-r)})$ are honestly computed, Lemma 3 gives $\Pr[\|\bar D(s_i^{(k-r-1)})\|>\sqrt{128/30}\,\beta^{(k-r-1)}\ \wedge\ \text{check 2 passes}]\le2^{-128}$. If they are dishonest (some $p_{i,j}\ne$ the true projection of $D(s_i^{(k-r-1)})$), then the round-$(r{+}1)$ consistency check (check 4) fails except with probability $q^{-d/2}\le2^{-128}$: given the next-round witnesses, the RHS $\sum_i\vec p_i^{(k-r-1)}$ is deterministic, and $\sum_jC_{m,j}\vec p_j^{(k-r)}=0$-type collisions over the ring impose probability $\le q^{-d/2}$ per ring coordinate. Crucially the honesty of round-$r$ $\vec p$'s is *verified in round $r{+}1$*, anchored at the final round where $s^{(1)}$ is revealed and $\sigma_{-1}(\Pi)s^{(1)}$ pins the true values, then recursively upward. Total per-round norm failure $\le2^{-128}+q^{-d/2}\le2^{-127}$.
5. **Folded inner product.** For honest $\mathrm{fold}^{(k-r)}$, a wrong extracted fold passes $\langle\mathrm{fold}^{(k-r)},\vec a_{k-r-1}\rangle=y^{(k-r)}$ with prob $\le1/q$; dishonest $\mathrm{fold}^{(k-r)}$ passes with prob $\le q^{-d/2}$ per round, again verified recursively from the final check $\mathrm{ct}[\sigma_{-1}(M_R(\vec a_0)),s^{(1)}]=\mathrm{fold}^{(2)}\cdot\vec C^{(2)}$ upward. Total $\le2^{-128}+q^{-d/2}\le2^{-127}$.

Extractor output: $w_r=\big(\bar s^{(k-r)},(\bar D(s_i^{(k-r-1)}),c_{\min,i}^{(k-r-1)})_{i\in[b]}\big)$ with success $\ge1-2^{-126}$ and slack $\sqrt{128/30}$.

#### 6.2.1 Index-level derivation of the extraction equations (for implementers of the extractor/tests)

Let $m=b_{k-r-1}$, $l=\mathrm{len}(D(s_i^{(k-r-2)}))=(\prod_{j=0}^{k-r-3}b_j)\iota$. Flattenings (row-major, first axis slowest):

- $D(s^{(k-r)})=\big\|\big\|_{i\in[m]} D(s_i^{(k-r-1)})$ (concatenation of the $m$ current slices, each of length $m'\!\cdot l$ with $m'=b_{k-r-2}$),
- $D(s^{(k-r)}_{\text{(new)}})$ (the *next* witness, shape $b_{k-r-2}\times\cdots\times b_0\iota$) $=\big\|\big\|_{i\in[m']} D(s^{(k-r-2)}_i)$, each of length $l$.

The fold $s^{(k-r-1)}=\sum_{i\in[m]}C_i^{(k-r)}s_i^{(k-r-1)}$ flattens to
$$D(s^{(k-r-1)})=\sum_{i\in[m]}C_i^{(k-r)}\,D(s_i^{(k-r-1)})=\vec S^{(k-r-1)}\ \ \text{(Eq. 6, per transcript }m\text{)},$$
and, blockwise, $D(s_i^{(k-r-2)})=\sum_{j\in[m]}C_j^{(k-r)}\,D(s_j^{(k-r-1)})[il:(i+1)l-1]$ (block $i$ of each old slice).

With the center transcript $b$ and the $v$-deviating transcript $v$ (challenges differ only in coordinate $v$):
$$\vec S_b-\vec S_v=\sum_i(C_{b,i}-C_{v,i})D(s_i^{(k-r-1)})=(C_{b,v}-C_{v,v})\,D(s_v^{(k-r-1)})=\bar c_v^{(k-r)}\,\bar D(s_v^{(k-r-1)}),$$
so division by the invertible ring scalar $\bar c_v^{(k-r)}$ (Lemma 1: $\|\bar c_v\|\le2\tau\ll\sqrt q$) recovers every slice. **Extraction requires exactly $b+1$ transcripts** (center + one deviant per coordinate): the $b$ recovered slices then satisfy the fold equations for *all* $b+1$ challenges — an over-determined system; this is exactly the $SS(\mathcal{C},b,2)$ structure of Def. 10 with $K=b+1$.

For a *test suite*, implement a malicious-prover harness that forks at each round and produces the $(b+1)$ transcripts, then run the extractor and check the recovered $\bar D(s_i)$ passes the relation (norm slack $\sqrt{128/30}$ allowed).

### 6.3 Theorem 5 (Knowledge soundness of Protocol 1)

Protocol 1 is knowledge sound for $\mathcal{R}_k$ with total knowledge error
$$\varepsilon\ \le\ \frac{(k-1)\,b}{|\mathcal{C}|}\ +\ 2^{-126}(k-1).$$
*Proof:* Protocol 1 is round-by-round $b$-coordinate-wise 2-special sound (Theorem 4, per-round error $2^{-126}$); Lemma 2 with $\ell=b$, $k=2$, $\mu=k-1$ gives knowledge error $\mu\ell(k-1)/|S|=(k-1)b/|\mathcal{C}|$; union bound over rounds adds $2^{-126}(k-1)$. (Note: $(\ell+1)^\mu=3^{k-1}$ must be $\mathrm{poly}(\lambda)$ — fine for $k=O(\log N)$, $N<2^{32}$.)

### 6.4 Theorem 6 (Efficiency)

With $b=(\bar N/d)^{1/k}$:

- **Proof size** $O(k\bar N^{1/k})$: per round $\pi_r$ contains $\mathrm{fold}^{(k-r)}\in R_q^b$, $\vec p_i^{(k-r)}\in R_q^{256}$ ($i\in[b]$), $c_{\min,i}^{(k-r-1)}\in R_q^\kappa$ ($i\in[b]$); final message $s^{(1)}$. Total: $\big((k-1)(257+\kappa)b+b\big)\cdot\lceil\log q\rceil$ bits.
- **Prover** per round: projection $O(256\,b^{k-r}\iota)$ ring ops; folding $O(b^{k-r+1})$ integer ops; next-round witness & commitments $O(b^{k-r}\iota+\kappa b^{k-r-1}\iota)$; statement update $O(b+\kappa b+\kappa^2\iota')$. Total $O(b^{k}+b^{k-1}+\cdots+b)=O(2b^k)=O(\bar N)$ — **linear**.
- **Verifier** per round: inner product $O(b)$; norm checks $O(256b)$; consistency $O(256b)$; commitment binding $O(\kappa^2b\iota')$; statement update $O(b+\kappa b+\kappa^2\iota')$. Total $O(k\bar N^{1/k})$.
- $k=\log N-\log d$ ⇒ $O(\log N)$ proof size and verification.

### 6.5 Theorem 7 (PCS security)

PC (Protocols 2, 3) has evaluation completeness (Thm 3), weak binding (Thm 4: two distinct openings of the same cm yield an MSIS solution via the inner/outer binding contradiction), and knowledge soundness (Thm 5, with the Def.-9 extractor composing the round extractors and the final `Open` check).

---

## 7. Parameters & Concrete Efficiency

### 7.1 Table 1 (asymptotic comparison; paper's Table 1)

| Scheme | Assump. | Transp. | CRS | Commit Size | Proof Size | Prover | Verifier | Sound. Error |
|---|---|---|---|---|---|---|---|---|
| [ZCF24] Basefold | Hash | Y | / | $O(1)$ | $O(\log N)$ | $O(N\log N)$ | $O(\log^2N)$ | neg$(\lambda)$ |
| [GLS+21] Brakedown | Hash | Y | / | $O(1)$ | $O(\sqrt N)$ | $O(N)$ | $O(\sqrt N)$ | neg$(\lambda)$ |
| [FMN24] | P-BASIS | N | $O(N^2)$ | $O(1)$ | $O(\log N)$ | $O(N^2)$ | $O(\log N)$ | $1/\mathrm{poly}(\lambda)$ |
| [AFLN24] SLAP | M-SIS($\ell_2$) | N | $O(\log N)$ | $O(1)$ | $O(\log^2N)$ | $O(N)$ | $O(\log^2N)$ | neg$(\lambda)$ |
| [CMNW24] | M-SIS($\ell_\infty$) | Y | / | $O(\log N)$ | $O(\log^2N)$ | $O(N)$ | $O(\log N)$ | neg$(\lambda)$ |
| [NS24] Greyhound | M-SIS($\ell_\infty$) | Y | / | $O(1)$ | $O(\log\log N)$ | $O(N)$ | $O(\sqrt N)$ | neg$(\lambda)$ |
| **HyperWolf** | **M-SIS($\ell_2$)** | **Y** | **/** | **$O(1)$** | **$O(\log N)$** | **$O(N)$** | **$O(\log N)$** | **neg$(\lambda)$** |

### 7.2 Table 2 (concrete proof sizes, 128-bit security; paper's Table 2)

| Scheme | $N=2^{15}$ | $N=2^{20}$ | $N=2^{25}$ | $N=2^{30}$ |
|---|---|---|---|---|
| [FMN24] | – | 36.5 MB | – | 767 MB |
| [NS24] Greyhound | – | – | 46 KB | 53 KB |
| [CMNW24] | 120 KB | 501 KB | 1.51 MB | 5.17 MB |
| **HyperWolf** | **80.28 KB** | **130.44 KB** | **180.59 KB** | **230.8 KB** |

### 7.3 Table 3 (HyperWolf asymptotic with $b=2$, $k=\log(N/d)$; paper's Table 3)

| Commit Size | Eval Proof Size | Prover Cost | Verifier Cost | Soundness Error |
|---|---|---|---|---|
| $O(1)$ | $O(\log N)$ | $O(N)$ | $O(\log N)$ | $\dfrac{2(\log N-7)}{|\mathcal{C}|}+2^{-126}(\log N-7)$ |

(The $\log N-7$ factor is $k-1=\log_2N-\log_2d-1$ with $d=64$.)

### 7.4 Table 4 (notation & asymptotic instantiation; paper's Table 4)

| Notation | Explanation | Asymptotic / concrete |
|---|---|---|
| $\lambda$ | security parameter | 128 |
| $q$ | prime modulus | $O(\lambda)$, $q\equiv5\pmod 8$ |
| $d$ | ring dimension | power of two, 64 |
| $N$ | number of coefficients | $N=b^kd$ |
| $b$ | length of auxiliary vectors | 2 |
| $k$ | hypercube dimension | $O(\log N)$ |
| $\kappa$ | height of $\mathbf A,\mathbf B$ | $O(1)$ (concrete 64) |
| $\delta$ | decomposition base 1 | $q^{1/O(1)}$ (16) |
| $\iota$ | $\lceil\log_\delta q\rceil$ | $O(1)$ (32) |
| $\delta_t$ | decomposition base 2 | $q^{1/O(1)}$ (16) |
| $\iota'$ | $\lceil\log_{\delta_t}q\rceil$ | $O(1)$ (32) |
| $\tau$ | challenge $\ell_2$ norm | $\omega(1)$ ($\sqrt{71}\approx8.43$) |
| $T$ | challenge operator norm | $\omega(1)$ (15) |
| $\beta^{(k-r)}$ | round-$r$ witness norm bound | $<q/125$ (with $\sqrt{128}$-style JL slack) |
| $\mathcal{C}$ | challenge space | $|\mathcal{C}|\approx2^{128}$ |

### 7.5 Derived concrete parameter set (reverse-engineered & verified against the reported proof sizes)

The paper does not print a single consolidated concrete table beyond the above; the following is *derived* and **numerically verified** to reproduce all four proof sizes of Table 2 to 3 significant figures:

- $q$ = 128-bit prime, $q\equiv5\pmod8$ (so $\lceil\log_2q\rceil=128$);
- $d=64$; $\delta=\delta_t=16$; $\iota=\iota'=\lceil\log_{16}q\rceil=32$; $\kappa=2\iota=64$;
- $b=2$, $k=\log_2(N/d)$, rounds $=k-1=\log_2N-7$;
- challenge space: 64 coefficients, 23 zeros, 31 in $\{\pm1\}$, 10 in $\{\pm2\}$ ($\tau=\sqrt{71}$), reject-sampled 5–6× for $T=15$; $|\mathcal{C}|>2^{128}$;
- feasibility constraint: $N<2^{32}$.

**Verification of the per-round proof size:** per round the prover sends
$\mathrm{fold}\in R_q^{2}$ (2 ring elts) $+\ 2\times\vec p\in R_q^{256}$ (512) $+\ 2\times c_{\min}\in R_q^{64}$ (128) $=642=2\cdot(257+\kappa)$ ring elements $=642\cdot16\ \mathrm{B}=10{,}272\ \mathrm{B}=10.03125\ \mathrm{KB}$:

| $N$ | rounds $k-1$ | predicted | reported |
|---|---|---|---|
| $2^{15}$ | 8 | $8\times10.031=80.25$ KB | 80.28 KB |
| $2^{20}$ | 13 | $13\times10.031=130.41$ KB | 130.44 KB |
| $2^{25}$ | 18 | $18\times10.031=180.56$ KB | 180.59 KB |
| $2^{30}$ | 23 | $23\times10.031=230.72$ KB | 230.8 KB |

(The sub-0.1% residual is the final $s^{(1)}$ message plus rounding of $\lceil\log q\rceil$; $s^{(1)}\in R_q^{b\iota}=R_q^{64}$ can be sent with 5-bit signed digits ≈ 2.5 KB, or compressed further.)

Other concrete quantities:

- Commitment size: $\mathrm{cm}_{\mathrm{out}}\in R_q^{\kappa}=64$ ring elements $=1$ KB (constant).
- Public key sizes: $\mathbf A\in R_q^{64\times64}$ (64·64 ring elts = 64 KB), $\mathbf B\in R_q^{64\times64\cdot32}$ ($=64\times2048$ ring elts = 2 MB) — both seed-derived in a transparent instantiation.
- $\Pi$: $256\times b_0\iota d=256\times4096$ trits — must be seed-expanded (≈415 KB if stored raw).
- Soundness (uniform): $(k-1)\cdot2/2^{128}+2^{-126}(k-1)$; for $N=2^{25}$: $36/2^{128}+18\cdot2^{-126}\approx2^{-120.8}$ — negligible.
- Norm ladder for $N=2^{25}$ (using $\beta^{(k-1)}=\frac\delta2\sqrt{b^{k-1}\iota d}=8\sqrt{2^{18}\cdot2^{11}}=2^{17.5}$ and per-round growth $\sqrt{2T}$): $\beta^{(0)}\approx30^{9}\cdot2^{17.5}\approx2^{61.8}$, $\gamma=2\beta^{(0)}\approx2^{62.8}$, MSIS bound $8T\gamma\approx2^{68.8}<q\approx2^{128}$ ✓ (matches the paper's $N<2^{32}$ feasibility with a 128-bit $q$; the $\sqrt T$-per-round variant gives $2^{51.8}$, even safer).

### 7.6 Detailed per-round proof & memory accounting (derived)

**Per-round message breakdown** ($b=2$, $\kappa=64$, $\lceil\log q\rceil=128$ bits = 16 B/ring elt):

| component | count | ring elts | bytes |
|---|---|---|---|
| $\mathrm{fold}^{(k-r)}\in R_q^2$ | 1 | 2 | 32 |
| $\vec p_i^{(k-r)}\in R_q^{256}$, $i\in[2]$ | 2 | 512 | 8,192 |
| $c_{\min,i}^{(k-r-1)}\in R_q^{64}$, $i\in[2]$ | 2 | 128 | 2,048 |
| **round total** | | **642** | **10,272 (10.03 KB)** |
| final $s^{(1)}\in R_q^{64}$ (5–7 bit signed digits) | 1 | 64 | ~2.5 KB (or 1,024 B at full width) |

**Optional compressions an implementer may exploit (not in the paper's numbers):** the $\vec p_i$ are only ever consumed through their 256 constant terms (checks 2 and 4 use $\mathrm{ct}(\vec p_{i,j})$; the final check consumes the full ring vector $\sigma_{-1}(\Pi)s^{(1)}$ — but the *folded* LHS $\sum_iC_i\vec p_i$ is a ring vector whose non-constant coefficients are needed too, so $\vec p_i$ must be sent as full ring elements; the constant-term-only shortcut does **not** work — do not "optimize" this away). The $c_{\min,i}$ are uniformly random-looking (commitments) — incompressible. $\mathrm{fold}$: ring elements, incompressible. So 10.03 KB/round is essentially tight given the parameters.

**Prover memory profile** ($N=2^{25}$): decomposed witness $2^{19}\cdot32=2^{24}$ ring elts = 256 MB at 16 B — but the prover can stream: at round $r$ only the current hypercube $s^{(k-r)}$ ($2^{k-r}\cdot\iota$ ring elts) + the fold accumulator are needed; peak = round 0. Inner commitments: $2\times64$ ring elts per round. JL projection work: $2\times256\times(2^{k-r-1}\iota)$ ring mults at round $r$ — dominated by round 0 ($2^{24}$ ring mults ≈ $2^{30}$ coefficient mults ≈ 1–2 min in numpy object dtype, seconds with limb-packed uint64 + Karatsuba).

**Verifier time profile:** per round $\sim(257+\kappa)\cdot b$ ring ops for checks 1–2–4 + $O(\kappa b\iota'd)$ coefficient ops for the gadget decompose in check 3 + $\kappa\cdot b\kappa\iota'$ ring-mults for the $\mathbf B^{(k-r)}$ matvec (use the block-tiling: $\mathbf B$ applied to a $b\kappa\iota'$-vector) — total $O(k\cdot N^{1/k})$ ring operations $\approx 18\times(\text{few thousand})$ — milliseconds.

### 7.7 Comparison synthesis (what to report in `lzk` benchmarks)

Reproduce, per $N\in\{2^{15},2^{20},2^{25}\}$: commitment size (1 KB), proof size (formula $(k-1)\cdot642\cdot16$ B + final), prover wall-clock, verifier wall-clock, and the check-by-check verifier cost split; then the same for the `lzk` Cini/SLAP/Greyhound modules for the 8× / 200× / verifier-time claims.

---

## 8. Implementation Notes

Target: Python package `lzk` (numpy/sympy; rings $\mathbb{Z}_q[x]/(x^n+1)$ with NTT, Ajtai/SIS commitments, multilinear sumcheck, ring-norm sumcheck, tensor/LDE encodings, Fiat–Shamir transcripts).

### 8.1 What to build (module inventory for `lzk.hyperwolf`)

1. **Ring context** $R_q=\mathbb{Z}_q[X]/(X^{64}+1)$, $q\equiv5\pmod 8$ prime: negacyclic multiply. ⚠ *$q\equiv5\pmod8$ is NTT-hostile* ($v_2(q-1)=2$, so only length-4 NTTs exist): use schoolbook ($64^2=4096$ coefficient mults) or Karatsuba per ring multiply; vectorize with numpy (`np.convolve` + fold, mod q). Batch multiplies as `(n,64)·(m,64) → (n,m,64)` einsum-style loops or FFT-free Kronecker tricks. (The `lzk` NTT core is still reusable for *other* papers; HyperWolf needs the non-NTT path, or an FFT over $\mathbb{C}$/three-prime CRT with final mod-$q$ reduction — safe because $q\approx2^{128}$ needs 3×64-bit primes or exact integer FFT.)
2. **Gadget decomposition** `g_decompose(v, base, ell)` and compose `g_compose`: per *ring element*, per *coefficient*: balanced digits in $(-\delta/2,\delta/2]$, $\iota=\lceil\log_\delta q\rceil$ digits. Layout: **component-major** — output index $c\cdot\iota+e$ = digit $e$ of ring component $c$ (this matches $G_{a,m}=I_m\otimes\vec g_a^T$). Norm bound per column $\frac a2\sqrt{\iota m}$.
3. **Challenge sampler**: 64-length vector, 23 zeros, 31 ±1, 10 ±2; rejection-sample until $\|c\|_{\mathrm{op}}\le T=15$ (operator norm of negacyclic convolution matrix = largest singular value of the $64\times64$ negacyclic matrix — compute via SVD of the (real) circulant-ish matrix; ~5–6 retries expected). Differences of distinct samples are invertible by Lemma 1 ($\|c-c'\|\le2\sqrt{71}<\sqrt q$).
4. **Hypercube witness container**: `s[k]` as an ndarray of ring elements with shape $(b,\dots,b,b\iota)$, plus its slice-flattenings $D(s_i)$ (views/reshapes — $D$ is row-major with the *first* axis slowest, so slicing along axis 0 and `.reshape(-1)` is exactly $D$).
5. **Fold engine** (Eq. 4): contract the innermost axis with $\sigma_{-1}(M_R(\vec a_0^{ext}))$ (ring-inner-product per position, take ct when a scalar is needed), then contract axes $1..k-2$ with integer vectors $\vec a_j$, leaving the outermost axis. Complexity $O(N)$ ring ops; implement as a sequence of `tensordot`s over $R_q$ (batched coefficient convolution).
6. **JL projection engine**: expand $\Pi$ from a seed; compute $M_R(\Pi)\in R_q^{256\times b_0\iota}$ once; per round apply $\sigma_{-1}(\Pi^{(k-r)})\cdot D(s_i^{(k-r-1)})$ — implement efficiently as: reshape the flattened slice into blocks of $b_0\iota$ ring elements, multiply each block by $\sigma_{-1}(M_R(\Pi))$ (a $(256\times b_0\iota)\times(b_0\iota)$ ring matvec per block — batched over blocks), sum blocks. Output $\in R_q^{256}$; the verifier only consumes $\mathrm{ct}(\cdot)$ of it.
7. **Ajtai commit / verify** with expanded keys: $\mathbf A^{(k-r)}=\vec 1^T\otimes\mathbf A$ — never materialize; compute $\mathbf A^{(k-r)}\vec v$ as $\mathbf A\cdot(\text{block-sum of }\vec v\text{ into }b_0\iota\text{-sized blocks})$. Same trick for $\mathbf B^{(k-r)}$ with $\kappa\iota'$-sized blocks.
8. **Outer commitment stack op**: $G^{-1}_{\delta_t,b\kappa}$ over the $b\kappa$ stacked inner commitments, then $\mathbf B^{(k)}$ matvec; verifier-side recomputation per round.
9. **Protocol driver** (Protocol 1) with prover/verifier state machines and FS transcript (domain-separated: `hw:pi`, `hw:round:r:challenge`, seeded by `hw:stmt`).
10. **PCS wrapper** (Protocols 2/3): commit/open/eval for univariate and multilinear, incl. the $\vec a_j$ builders and the $G^T_{\delta,b_0d}$ expansion of $\vec a_0$.
11. **Batching** (Appendix B) on top of `lzk`'s multilinear sumcheck + `eq` polynomials.

### 8.2 Data structures

- Ring elements: `np.int64` arrays of length $d=64$ (values in $[0,q)$; balanced rep. on demand via `v - q*(v>q//2)`), or packed `object`/`int` arrays if $q>2^{63}$ — **for 128-bit $q$ use Python ints or split into limbs** (numpy uint64 overflows: products of two 128-bit values need big-int or 2-limb arithmetic; alternatively represent $R_q$ elements as length-2 uint64 limb pairs and use `np.convolve` on object dtype). *This is the single biggest performance decision: a 128-bit modulus in numpy forces object dtype or limb tricks; consider $q\approx2^{61}$-$2^{62}$ (still $q\equiv5\bmod 8$, $\iota=16$, $\kappa=32$) for a pure-numpy prototype and re-derive the norm ladder — feasibility still holds for $N\le2^{24}$-ish; verify with the estimator before deviating from the paper's 128-bit $q$.*
- $s^{(k)}$: `np.ndarray` shape $(2,)* (k-1) + (2*ι,)` of ring elements → as `(N/d*ι, 64)` flat int array with an index map; slicing along axis 0 = slices $s_i^{(k-1)}$.
- $\Pi$: store the seed; regenerate blocks deterministically (`np.random.Generator(seed).choice([-1,0,1], p=[.25,.5,.25], size=(256, b0*ι*d))`).
- Transcript: append-only list of canonical byte serializations.

### 8.3 Complexity per step (prover, $N=b^kd$, $b=2$)

| step | cost |
|---|---|
| Commit (gadget + inner commits) | $O(N\iota)$ coefficient ops + $O(\kappa\cdot N/d\cdot\iota)$ ring-mults (batched) |
| Round $r$: fold $\mathrm{fold}^{(k-r)}$ | $O(b^{k-r})$ ring scalar-mults (each $O(d^2)$ coeff ops w/o NTT) |
| Round $r$: projections $\vec p_i$ | $O(256\cdot b^{k-r-1}\iota)$ ring scalar-mults |
| Round $r$: next witness fold | $O(b^{k-r}\iota)$ ring mults by challenges |
| Round $r$: next inner commitments | $O(\kappa b^{k-r-1}\iota)$ ring mults |
| total | $O(N\iota d^2)$ coefficient ops — linear, ~$2\times$ the commitment cost |

Verifier per round: $O((257+\kappa)\cdot b)$ ring ops for checks 1–2, $O(\kappa b\iota'd)$ for the gadget+binding check 3, $O(256b)$ for check 4.

### 8.4 Pitfall ledger (critical)

1. **Gadget index-layout transpose (top bug risk).** The paper writes $\vec a_0\leftarrow G^T_{\delta,b_0d}\vec a_0$ then $M_R(\cdot)$, but a *literal* component-major $G^T$ followed by $M_R$'s "group $d$ consecutive integers" rule scrambles digits across positions. The mathematically correct pairing with the component-major decomposition $G^{-1}_{\delta,b^k}$ (last-axis index $t\cdot\iota+e$ = digit $e$ of ring component $t$) is:
   $$\sigma_{-1}(M_R(\vec a_0))\big[t\cdot\iota+e\big]\ =\ \sigma_{-1}\big(\delta^e\cdot M_R(\vec a_0)[t]\big),\qquad M_R(\vec a_0)[t]=\sum_{j=0}^{d-1}a_0[td+j]X^j .$$
   I.e. *tile each of the $b_0$ ring lifts of $\vec a_0$ by $\delta^e$, $e\in[\iota]$, matching the slice's digit layout.* Define one canonical layout constant and unit-test: $\mathrm{ct}(\langle\text{last axis},\sigma_{-1}(\vec a_0^{ext})\rangle)=\langle\text{coeffs},\vec a_0\rangle$ must hold on random data.
2. **$\sigma_{-1}$ omissions.** Protocol 4 round 1 prints $\vec p_i^{(2)}=\Pi D(s_i^{(1)})$ without $\sigma_{-1}$; Protocol 1 and both final checks require $\sigma_{-1}(\Pi^{(k-r)})$ and $\sigma_{-1}(M_R(\vec a_0))$. Always apply the conjugation entrywise to the *matrix/vector of ring elements* before the matvec — otherwise constant terms are convolutions, not integer projections, and both completeness and the JL check silently break.
3. **Flattening order.** $D$ must be row-major with the *outermost* (first) axis slowest. Check 4 (cross-round projection consistency) and Eq. 5/Eq. 6–7 (extraction) depend on "concat of current slices = full flattening = challenge-fold of previous slices". A column-major or axis-permuted reshape breaks soundness arguments, not just completeness.
4. **Norm-check margin.** $\mathbb{E}[\sum_j\mathrm{ct}(p_j)^2]=128\|s\|^2$ exactly at the check threshold $128\beta^2$ when $\|s\|=\beta$. Honest witnesses pass only because gadget digits are $\pm$uniform-like (RMS $\delta/\sqrt{12}$, ~1.73× below the worst-case $\delta/2$ bound). Never construct witnesses with adversarial (all-max) digits; optionally randomize digit choices among balanced representatives. Add a unit test asserting the empirical JL statistic on random honest witnesses stays below $0.6\cdot128\beta^2$.
5. **$\beta$ recursion ambiguity.** Theorem 3 vs §5.2 print different per-round growth ($\sqrt T$ vs $\sqrt{2T}$; the completeness proof's intermediate line suggests $T\sqrt{b_{k-r-1}/b_{k-r-2}}$ in the worst case). Safe engineering: compute the *actual* norms of the honest folded witness at every round (they're data-dependent, typically ≪ worst case) and set the verifier's per-round $\beta^{(k-r-1)}$ from the *proved* ladder with the conservative growth $\sqrt{2T}$ (or re-derive $\beta^{(r)}$ per instance and put it in the statement — the relation allows instance-dependent $\beta$ as long as the MSIS bound $\max(8T\gamma,\beta')$ and $q/125$ constraints hold).
6. **Wrap-around in the JL projection.** All projected quantities must stay below the modulus where Lemma 3's $b\le q/125$ applies; with the 128-bit $q$ and $\beta^{(0)}\approx2^{62}$ there is huge headroom, but if you shrink $q$ for numpy friendliness re-check $\sqrt{128}\,\beta^{(r)}\ll q$ for *every* round $r$.
7. **Non-power-of-two / general $(b_j)$.** The relation supports non-uniform axes; the concrete numbers and the $k=\log N-6$ formulas assume $b=2$. For $N$ not of the form $2^k\cdot64$, pad coefficients with zeros to the next $b^kd$ (evaluation vectors unaffected; zero coefficients don't change $y$).
8. **Univariate exponent overflow.** $\vec a_0=(1,u,\dots,u^{bd-1})$ and $\vec a_i=(1,u^{b^i},\dots)$ — compute by repeated squaring mod $q$; for $k\approx25$ the exponents reach $2^{30}$ — fine mod $q$, but use modpow, never floats.
9. **Multilinear variable-to-axis assignment.** With $b=2$: variables $u_0,\dots,u_{\log(bd)-1}$ go to the innermost axis (via $\vec a_0$), then one variable per outer axis in order. A permutation mistake here yields a *different but consistent* commitment (completeness holds, evaluations wrong) — test against direct multilinear evaluation.
10. **Final-round norm check.** $\|s^{(1)}\|\le\beta^{(0)}$ is over the *ring-element* $\ell_2$ norm ($\sqrt{b\iota d}$ coefficients each $\le\delta/2$ plus fold growth) — the largest bound in the ladder; make sure the constant-time encoding of $s^{(1)}$ (5-bit signed digits) is actually valid, i.e. the folded digits really are $\le\delta/2$-ish; after $\sqrt{2T}$-growth rounds the *worst-case* bound exceeds 5 bits, so **encode $s^{(1)}$ with $\lceil\log_2(2\beta^{(0)})\rceil$-bit signed integers** (or full ring elements) rather than assuming gadget-width digits.
11. **FS + rejection-sampled challenges.** The Labrador-distribution + op-norm rejection must be *deterministic given the digest* (fixed retry policy, fixed PRG) or verifiers diverge. Sample per challenge component with its own counter/domain tag.
12. **Statement update duality.** The verifier updates $\mathrm{cm}^{(k-r-1)}_{\mathrm{out}}$ from the *prover-sent* $c_{\min,i}^{(k-r-1)}$ and challenge: $\mathbf B\,G^{-1}_{\delta_t,\kappa}(\sum_iC_ic_{\min,i})$; the prover *also* holds the next-round commitments $c_{\min,i}^{(k-r-2)}$ whose stack binds to the same value (Eq. 5). Keep both code paths and assert equality in tests (this is the completeness spine).
13. **$t_i$ vs $c_{\min,i}$ naming.** Protocol 1's prover message prints $(\vec p_i^{(k-r)},t_i^{(k-r-1)})$; Theorem 4's $\pi_r$ prints $(\vec p_i^{(k-r)},c_{\min,i}^{(k-r-1)})$ — they are the same objects ($t_i\equiv c_{\min,i}$, sent in the clear, extractor outputs them unmodified).

### 8.5 Edge cases

- $k=2$ (smallest non-trivial): single reduction round $\mathcal{R}_2\to\mathcal{R}_1$; $\Pi^{(2)}=M_R(\Pi)$, $\mathbf A^{(2)}=\mathbf A$; check 4 appears only in the final round's form. $k=1$ degenerates to: commit slices of a 1-D witness and open directly.
- $N=d\cdot2$ ($k=1$): the whole protocol collapses to an Ajtai opening + JL norm check.
- Zero polynomial / zero slices: norm checks trivially pass; fold outputs 0.
- Evaluation at $u=0$: all $\vec a_j=(1,0,\dots,0)$.
- Hiding: append a small random vector to the message before committing (paper treats the randomness as part of the witness — the norm bounds must then cover the randomness too; sample it with $\ell_2$ norm ≤ the slack between the gadget RMS and the worst-case bound).

### 8.6 What can be reused from the shared `lzk` core

| `lzk` facility | use in HyperWolf |
|---|---|
| $\mathbb{Z}_q[x]/(x^n+1)$ ring | direct ($n=64$); the NTT fast path won't apply for $q\equiv5\bmod8$ — keep the schoolbook/Karatsuba path; NTT path reusable if a different modulus family is chosen (then re-justify invertibility via norm vs. factor structure) |
| Ajtai/SIS commitments | the inner/outer commitment exactly (`commit(A, s)`, expanded-key matvec via block-sum trick) |
| gadget decomposition | `g_decompose/g_compose` with configurable base ($\delta$, $\delta_t$) and balanced digits |
| multilinear sumcheck | the Appendix-B batching protocols (cases 2–3) |
| ring-norm sumcheck | not needed — HyperWolf uses the *JL projection* instead of a sumcheck for norms (completely different mechanism; do not confuse) |
| tensor/LDE encodings | the hypercube reshape/flatten utilities and the multilinear `eq`/extension helpers |
| Fiat–Shamir transcripts | round-by-round challenge derivation with domain separation; seeded $\Pi$ |

### 8.7 Test vectors to build first

1. Ring identities: $\mathrm{ct}(\langle\sigma_{-1}(\vec a),\vec b\rangle)=\langle\mathrm{coeffs}(\vec a),\mathrm{coeffs}(\vec b)\rangle$; Lemma-1 invertibility of random small-norm elements; challenge-difference invertibility (10⁴ samples).
2. Gadget round-trip $G\,G^{-1}=\mathrm{id}$ and the §8.4-1 pairing identity.
3. $k=2$ end-to-end on random $f$ ($N=2\cdot64\cdot2=256$ coefficients): commit → eval → verify, all checks green.
4. $k=3$ replica of Protocol 4 against the paper's figure.
5. Attack tests: tamper each prover message component (fold, one $\vec p$ entry, one $c_{\min}$, final $s^{(1)}$) and assert rejection (each maps to a distinct verifier check).
6. JL calibration: empirical distribution of $\sum_j\mathrm{ct}(p_j)^2/(128\beta^2)$ on honest witnesses (target ≤0.6) and on inflated witnesses (target rejection).

### 8.8 Challenge sampler — engineering detail

- **Distribution:** choose a uniform subset of 23 zero positions out of 64; among the remaining 41 choose 31 positions for $\pm1$ and 10 for $\pm2$; signs uniform. $|\mathcal{C}|=\binom{64}{23}\binom{41}{31}2^{41}>2^{128}$.
- **Operator norm:** for $c\in R_q$ with $d=64$, $\|c\|_{\mathrm{op}}$ is the spectral norm of the $64\times64$ negacyclic Toeplitz matrix $T(c)$ ($T(c)_{i,j}=c_{(i-j)\bmod d}$ negated when $i<j$). Compute via `numpy.linalg.svd(T)` ($64\times64$ — microseconds); reject until $\|c\|_{\mathrm{op}}\le15$. Expected retries 5–6 (the paper's number; verify empirically — if the acceptance rate differs, adjust the retry policy *before* freezing the FS derivation).
- **Invertibility:** any two distinct samples differ by an element of norm $\le2\sqrt{71}<\sqrt q$ — invertible by Lemma 1 *provided* $q>2^2\cdot71$; with 128-bit $q$ this is automatic. (If a smaller prototype $q$ is used, keep $q>2^{12}$ at absolute minimum and test.)
- **Determinism under FS:** sample positions/signs from a counter-based PRG (e.g., ChaCha/SHAKE keyed by the round digest); the rejection loop must be implemented identically on both sides; log retry counts into the transcript *hash input* to avoid Grinder-style ambiguities.

### 8.9 Suggested milestone plan (maps to gap-ledger IDs W1–W5)

| ID | deliverable | content | acceptance test |
|---|---|---|---|
| W1 | ring + gadget + challenge core | $R_q$ ($d=64$, $q\equiv5\bmod8$) schoolbook/Karatsuba mult; balanced gadget de/compose ($\delta$, $\delta_t$); Labrador challenge sampler with op-norm rejection; $\sigma_{-1}$, $M_R$, ct-identity | ring identities test; $GG^{-1}=\mathrm{id}$; invertibility stats |
| W2 | witness layer | hypercube container, $D$ flattening, slice views, fold engine (Eq. 4), $\vec a_0$ expansion with the §8.4-1 layout | fold equals direct evaluation on random polys ($k=2,3,4$; uni + multilinear) |
| W3 | commitment layer | Protocol 2 commit/open; expanded-key block-tiling matvecs for $\mathbf A^{(k-r)},\mathbf B^{(k-r)}$; $G^{-1}_{\delta_t,b\kappa}$ stacks | open/commit round-trip; tampered-$f$ rejection |
| W4 | core protocol | Protocol 1 prover/verifier + FS transcript (§5.6 layout) + JL engine; $k=2$ then general $k$ | end-to-end at $N=2^{12}$–$2^{15}$; per-check tamper tests (§8.7-5) |
| W5 | PCS + benchmarks | Protocol 3 wrapper (uni + multilinear), Appendix-B batching, parameter derivation (§7.5), benchmark harness vs. Cini/SLAP/Greyhound modules | proof sizes reproduce Table 2; soundness-error formula check; benchmark report |

---

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
