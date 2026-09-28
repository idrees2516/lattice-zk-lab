# LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems — Deep Analysis & Implementation Spec

## 1. Metadata

| Field | Value |
|---|---|
| Title | LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems |
| Authors | Dan Boneh, Binyi Chen (Stanford University) |
| Venue / eprint | Manuscript dated August 9, 2025; acknowledges CRYPTO reviewers (journal/conference version TBD); predecessor LatticeFold is eprint 2024/257 |
| Date | August 9, 2025 |
| Assumption | Module-SIS with $\ell_\infty$ norms: $\mathrm{MSIS}^{\infty}_{q,\kappa,m,\beta_{\mathrm{SIS}}}$ over $R_q = \mathbb{Z}_q[X]/\langle X^d+1\rangle$ |
| Headline contribution | A very different lattice-based folding protocol vs LatticeFold [BC24]: (1) a purely algebraic range proof (no bit-decomposition commitments) built on a monomial-set check over $R_q$; (2) double commitments (commitments of commitments) that shrink folding proofs to $O_\lambda(\kappa d + \log n)$ bits; (3) a sumcheck-based commitment-transformation protocol $\Pi_{\mathrm{cm}}$ that converts non-homomorphic double-commitment statements into linearly-foldable statements. Prover estimated ~5× faster than LatticeFold; folding L>2 instances at once. |

Positioning relative to prior art:
- **LatticeFold [BC24]**: folds $2d$ instances after norm-reduction; range proof via bit decomposition costing $L\log_2(B)$ commitments to decomposed vectors. LatticeFold+ removes all of these.
- **Lova [FKNP24]**: integer-based Ajtai + $\ell_2$-norm; worse concrete efficiency.
- **Klooß et al. [KLNO24]**: $\ell_2$-norm range proofs with subtractive sets of polynomial size; needs parallel repetition.
- **Neo [NS25]**: small-field embedding into $R_q$; orthogonal and directly compatible (Appendix B of this paper reinterprets it as a tensor-of-rings framework).
- **HyperNova [KS24b]**: Pedersen-based CCS folding with comparable prover time to LatticeFold (per Nethermind benchmarks [Net24]); LatticeFold+ is expected to be significantly faster and post-quantum.

Key quantitative claims (folding $L$ witnesses of dimension $n$, norm $< B$):
- Prover: $\Omega(\log B)$-times faster than LatticeFold; concretely ~5× (estimated from Nethermind's LatticeFold benchmark).
- Proof size: $O_\lambda(\kappa d \log B + d\log n)$ (LatticeFold) → $O_\lambda(\kappa d + \log n)$ (LatticeFold+).
- Concrete parameter set: $L=3$, $q$ 128-bit prime with $q \equiv 1+2^{16} \pmod{4\cdot 16}$ ($R_q$ splits into 16 factors), $d=64$, $n=2^{21}$, $\bar S = \{-1,0,1,2\}^d$, $B=2^{10}$, $k=2$, $\kappa=9$; folding proof < 200 KB (≲100 KB with the Remark 5.3 batching optimization), which hashes to ≲100 $R_q$-hashes in Fiat-Shamir.

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $\lambda$ | Security parameter |
| $d$ | Ring dimension, a power of two; $d' := d/2$ |
| $R$ | $\mathbb{Z}[X]/\langle X^d+1\rangle$, power-of-two cyclotomic ring |
| $R_q$ | $R/qR = \mathbb{Z}_q[X]/\langle X^d+1\rangle$; $\mathbb{Z}_q$ represented as $\{-\lfloor q/2\rfloor,\dots,\lfloor q/2\rfloor\}$ |
| $q$ | Prime modulus, $q>2$; if $q \equiv 1+2e \pmod{4e}$ for $e \mid d$ then $R_q \cong \mathbb{F}_{q^{d/e}}$ via NTT |
| $\kappa$ | Number of rows of the Ajtai/SIS matrix $\mathbf{A} \in R_q^{\kappa\times n}$; commitment output length |
| $n$ | Witness length (number of $R_q$ elements); assumed power of two for tensor notation |
| $\mathrm{cf}(f)$ | Coefficient vector of $f=\sum_{i\in[d]} f_i X^i \in R_q$, i.e. $(f_0,\dots,f_{d-1}) \in \mathbb{Z}_q^d$; for vectors, row-wise concatenation $\mathrm{cf}(\mathbf{f}) \in \mathbb{Z}_q^{n\times d}$ |
| $\mathrm{ct}(f)$ | Constant term $f_0$ of $f$; for vectors the first column of $\mathrm{cf}(\mathbf{f})$ |
| $\mathcal{M}'$ | Monomial set $\{0,1,X,X^2,\dots\} \subseteq \mathbb{Z}_q[X]$ (Eq. 1) |
| $\mathcal{M}$ | Monomial set $\{0,1,X,\dots,X^{d-1}\} \subseteq \mathcal{M}'$ (Eq. 2), embedded in $R_q$ |
| $\mathrm{sgn}(a)$ | Sign of $a \in (-d,d) \subseteq \mathbb{Z}_q$, with $\mathrm{sgn}(0)=0$ |
| $\exp(a)$ | $\mathrm{sgn}(a) X^{a} \in \mathcal{M}$ (for $a<0$: $\exp(a)=X^{a+d}$) |
| $\mathrm{EXP}(a)$ | $\{\exp(a)\}$ if $a\neq 0$; $\{0,1,X^{d/2}\}$ if $a=0$ (Eq. 3) |
| $\mathrm{EXP}(M)$, $\exp(M)$ | Entry-wise extensions to matrices $M \in (-d,d)^{m\times n}$ |
| $\psi$ | Range-check ring element: $\psi := \sum_{i\in[1,d')} i\cdot(X^{-i}+X^i) \in R_q$ (with $X^{-i} \equiv -X^{d-i}$) |
| $\psi_T$ | Lookup-table generalization: $\psi_T := \sum_{i\in[1,d']} (-T_i)X^i + \sum_{i\in[1,d')} T_{i+d'} X^{-i}$ |
| $\|f\|_\infty$ | $\max_{i} |f_i|$ over coefficients (lifted to $\mathbb{Z}$) |
| $\|a\|_{\mathrm{op}}$ | Operator norm $\sup_{y\in R} \|a\cdot y\|_\infty / \|y\|_\infty$; $\|\bar S\|_{\mathrm{op}} := \max_{a\in \bar S}\|a\|_{\mathrm{op}}$ |
| $\mathbf{g}_{b,k}$ | Gadget vector $(1,b,\dots,b^{k-1}) \in \mathbb{Z}^k$ |
| $G_{b,k}$ | Gadget matrix $I_m \otimes \mathbf{g}_{b,k} \in \mathbb{Z}^{mk\times m}$ |
| $G^{-1}_{b,k}(\cdot)$ | Deterministic base-$b$ signed decomposition map: $M \mapsto M'$ with $\|M'\|_\infty < b$, $M' G_{b,k} = M$ |
| $\hat \ell$ | $\lceil \log_B(q) \rceil$ — gadget expansion factor used in the R1CS reduction |
| $\ell$ | $\lceil \log_{d'}(q)\rceil$ — gadget expansion for the double-commitment split map |
| $k$ | Decomposition length so that $B = (d')^k$ |
| $B$ | Norm bound for input witnesses; $B=(d')^k$ |
| $\bar S$ | Folding challenge set: strong sampling set $\subseteq R_q$ with small operator norm; $\|\bar S\|_{\mathrm{op}}$, $|\bar S| \ge 2^\lambda$ |
| $C$ | Sumcheck challenge set (e.g. $\mathbb{Z}_q$ for 128-bit $q$; $\mathbb{F}_{q^2}$ for 64-bit $q$) |
| $\mathcal{M}_C := C\times C$, $\mathcal{M}_q := R_q\times R_q$ | Paired-challenge modules used to halve sumcheck soundness error |
| $\mathrm{com}(\cdot)$ | General linear commitment: $\mathrm{com}(\mathbf{a}) = \mathbf{A}\mathbf{a} \in R_q^\kappa$ for $\mathbf{A}\in R_q^{\kappa\times n}$; for matrices column-wise |
| $\mathrm{dcom}(M)$ | Double commitment $\mathrm{com}(\mathrm{split}(\mathrm{com}(M))) \in R_q^\kappa$ (Eq. 7) |
| $\mathrm{split}(\cdot)$ | Injective map $R_q^{\kappa\times m} \to (-d',d')^n$: gadget-decompose → flatten → coefficient-flatten → zero-pad |
| $\mathrm{pow}(\cdot)$ | Surjective "inverse" of split: power-sums of sub-vectors re-embedded as $R_q^{\kappa\times m}$; $\mathrm{pow}(\mathrm{split}(D))=D$ |
| $\tilde f$ | Multilinear extension of $f:\{0,1\}^{\log n}\to \bar R$; $\tilde f(\mathbf{x}) = \sum_{\mathbf{b}} f(\mathbf{b})\,\mathrm{eq}(\mathbf{b},\mathbf{x})$ |
| $\mathrm{eq}(\mathbf{b},\mathbf{x})$ | $\prod_{i\in[k]} (1-b_i)(1-x_i)+b_i x_i$ |
| $\mathrm{tensor}(\mathbf{r})$ | $\bigotimes_{i\in[k]}(1-r_i, r_i) \in \bar R^{2^k}$; evaluation identity $\tilde f(\mathbf r)=\langle \mathbf f, \mathrm{tensor}(\mathbf r)\rangle$ (Remark 2.3) |
| $\langle \mathbf f,\mathbf g\rangle$ | Inner product; column vectors by default |
| $\mathrm{flat}(M)$ | Vertical concatenation of rows of $M$ |
| $[u_1,\dots,u_k]$ / $(u_1,\dots,u_k)$ | Horizontal / vertical concatenation |
| $\mathrm{ev}_a(\beta)$ | $\sum_{i\in[d]} a_i \beta^i \in \mathbb{F}_{q^u}$ — evaluation of $a(X)$ at $\beta$ |
| $\langle i\rangle$ | Binary representation $\langle i\rangle_{\log n} \in \{0,1\}^{\log n}$; $[\mathbf a]_k = \sum a_i 2^i$ |
| $\mathbf{A}$ | Public randomness $\in R_q^{\kappa\times n}$ defining $\mathrm{com}$ |
| $\epsilon_{\mathrm{bind}}$ | Binding error of $\mathrm{com}$ (from $(b,S)$-relaxed binding, Def. 2.3) |
| $\epsilon_{\mathrm{mon},m}$ | Knowledge error of $\Pi_{\mathrm{mon}}$: $(2d+m+4\log n)/|C| + \epsilon_{\mathrm{bind}}$ |
| $\epsilon'_{\mathrm{rg}}, \epsilon_{\mathrm{rg}}$ | Knowledge errors of warm-up range check / $\Pi_{\mathrm{rgchk}}$ |
| $\epsilon_{\mathrm{sum}}$ | $(2\log n/|C|)^2$ — two-parallel-sumcheck soundness |
| $\epsilon_{\mathrm{cm},k}$ | Knowledge error of $\Pi_{\mathrm{cm}}$ (Lemma 4.10) |
| $\epsilon_{\mathrm{lin},k}$ | Knowledge error of $\Pi_{\mathrm{lin},B}$ = $\epsilon_{\mathrm{cm},k}$ |
| $L$ | Number of simultaneously folded instances ($L-2$ online + 2 accumulated) |
| $n_{\mathrm{lin}}$ | Number of linear checks per $\mathcal{R}_{\mathrm{lin}}$ instance (=4 for R1CS) |
| $\beta$ | Ring-evaluation challenge $\leftarrow C$ used in the monomial-set check |
| $\mathbf r$, $\mathbf r_o$ | Sumcheck / folding-round challenge vectors $\in C^{\log n}$ |
| $\mathbf s \in \bar S^3$, $\mathbf s' \in \bar S^{dk}$ | Folding challenges of $\Pi_{\mathrm{cm}}$ steps 2/3 |
| $D_f$ | $G^{-1}_{d',k}(\mathrm{cf}(\mathbf f)) \in \mathbb{Z}_q^{n\times dk}$ — decomposition matrix of $\mathbf f$ (Eq. 13) |
| $M_f$ | $M_f \in \mathrm{EXP}(D_f) \subseteq \mathcal{M}^{n\times dk}$ — monomial encoding of $D_f$ |
| $\tau_D$ | $\mathrm{split}(\mathrm{com}(M_f)) \in (-d',d')^n$ |
| $\mathbf m_\tau$ | $\mathbf m_\tau \in \mathrm{EXP}(\tau_D) \subseteq \mathcal{M}^n$ (in practice $\exp(\tau_D)$) |
| $\mathbf h$ | $\mathbf h := M_f \mathbf s' \in R_q^n$ — folded matrix witness; $\mathrm{com}(\mathbf h) = \mathrm{com}(M_f)\mathbf s'$ |
| $\mathbf e$, $\mathbf e_o$ | Evaluation vectors produced by sumchecks of $\Pi_{\mathrm{rgchk}}$ / $\Pi_{\mathrm{cm}}$ |
| $\mathbf g$ | Output (folded) witness of $\Pi_{\mathrm{cm}}$: $\mathbf g = s_0\tau_D + s_1\mathbf m_\tau + s_2\mathbf f + \mathbf h$ |
| $R_{\mathrm{open}}$, $R_{\mathrm{dopen},m}$ | Commitment / double-commitment opening relations (Eq. 6, 8) |
| $\mathcal{R}_{\mathrm{lin},B}$ | Generalized committed linear relation (Def. 3.1) |
| $R^{(L)}_{\mathrm{lin},B}$ | $L$-fold product of $\mathcal{R}_{\mathrm{lin},B}$ |
| $\mathcal{R}_{\mathrm{comp}}$, $\mathcal{R}_{\mathrm{acc}}$ | $R^{(L-2)}_{\mathrm{lin},B}$ (online) and $R^{(2)}_{\mathrm{lin},B}$ (accumulated) |
| $\mathbf z$ | In Appendix A: $z = G^\top_{B,\hat\ell}\mathbf f \in R_q^m$, the gadget-recombined R1CS variable vector |
| $\mu$ | $3 + dk$ — folding challenge count used by the extractor of $\Pi_{\mathrm{cm}}$ |

## 3. Algebraic Setting

### 3.1 Rings and fields

- Ring: $R = \mathbb{Z}[X]/\langle X^d + 1\rangle$ with $d$ a power of two; $R_q = R/qR$, $q$ prime $> 2$.
- NTT splitting: if $q \equiv 1 + 2e \pmod{4e}$ with $e \mid d$, then $R_q \cong \mathbb{F}_{q^{d/e}}$. Concrete parameter set uses $e=16$ ($R_q$ splits into 16 factors).
- Signed representation of $\mathbb{Z}_q = \{-\lfloor q/2\rfloor,\dots,\lfloor q/2\rfloor\}$ matters for range semantics: "small" always means small signed integer lift.
- Small-modulus support (Appendix B, "tensor-of-rings" = Neo [NS25]): let $K=\mathbb{F}_{q^t}$; the tensor ring $E := K \otimes_{\mathbb{F}_q} R_q$ is an $\mathbb{F}_q$-space of dimension $t\cdot d$ viewed as $t\times d$ matrices. Two interpretations of products $a(X)\cdot b(Y)$:
  - *Column interpretation*: $a$'s coefficient vector scales $K$-columns: $[a_1 b(Y) \mid \dots \mid a_d b(Y)]$.
  - *Row interpretation*: $b$'s coefficient vector scales $R_q$-rows: $(a(X)b_1,\dots,a(X)b_t)^\top$.
  - Sumchecks run over $K$; folding challenges stay in $\bar S\subseteq R_q$. E.g. $q$ 64-bit → all sumchecks over $\mathbb{F}_{q^2}$ for 128-bit security. A sumcheck over $\mathbb{F}_{q^2}$ of size-$n$ statement is cheaper than one Ajtai commitment over $R_q$ when $d \gg 2$.

### 3.2 Norms

- $\ell_\infty$ on $R$ and matrices (max over coefficient lifts). $R_q$ elements lifted to $R$ first.
- Operator norm $\|a\|_{\mathrm{op}} = \sup_{y\in R} \|ay\|_\infty/\|y\|_\infty$; Lemma 2.5 (Prop. 2 [AL21]): $\|u\|_{\mathrm{op}} \le d\|u\|_\infty$.
- Lemma 2.3: for $a\in\mathcal{M}$, $\|a\cdot b\|_\infty \le \|b\|_\infty$ (monomial multiplication only rotates/flips coefficients).
- Lemma 2.4 (Cor. 1.2 of [LS18]): for $q \equiv 1+2^e \pmod{4e}$, every nonzero $y \in R_q$ with $\|y\|_\infty < q^{1/e}/\sqrt{e}$... (non-zero $y$ with tiny coefficients is invertible; concretely every nonzero $y\in R_q$ with $\|y\|_\infty < \sqrt{q}/\sqrt{e}$-type bound) — used to certify strong sampling sets.

### 3.3 Monomial machinery (the paper's core algebraic device)

- **Lemma 2.1**: over $\mathbb{Z}_q[X]$ ($q>2$ prime), $a(X^2)=a(X)^2 \iff a \in \mathcal{M}'$. Proof by comparing the second-highest-degree term of $a(X)^2$ (degree $d_n + d_{n-1}$, coefficient $2a_na_{n-1}$), which cannot appear in $a(X^2)$ unless one coefficient vanishes. **Caveat (Remark 2.1)**: fails in $R_q$ — e.g. in $\mathbb{Z}_q[X]/\langle X^4+1\rangle$ with $q\equiv1 \pmod 4$, $a(X) = X^3/2 + (i/2)X^2 + (i/2)X + 1/2$ with $i^2=-1$ satisfies $a^2 = a(X^2)$ but $a\notin\mathcal{M}$. Therefore the monomial check is always performed in an extension field $\mathbb{F}_{q^u}$ via $\mathrm{ev}_a(\beta)$, where it *does* hold (Corollary 4.1).
- **Corollary 4.1**: for $a \in \mathcal{M}$, $\beta \in \mathbb{F}_{q^u}$: $\mathrm{ev}_a(\beta)^2 = \mathrm{ev}_a(\beta^2)$; for $a \notin \mathcal{M}$ this holds with probability $< 2d/|\mathbb{F}_{q^u}|$ over random $\beta$.
- **Lemma 2.2 (the range lemma)**: with $d':=d/2$ and $\psi = \sum_{i\in[1,d')} i(X^{-i}+X^i) \in R_q$:
  - If $a \in (-d',d')$ then for all $b\in\mathrm{EXP}(a)$: $\mathrm{ct}(b\cdot\psi) = a$.
  - Conversely, if $b \in \mathcal{M}$ and $\mathrm{ct}(b\cdot\psi) = a$, then $a \in (-d',d')$ and $b\in\mathrm{EXP}(a)$.
  - Intuition: multiplying $\psi$ by a monomial rotates and sign-flips the triangular coefficient pattern so the constant term lands in $(-d',d')$; the map is a bijection $\mathcal{M}\setminus\{0\}\to(-d',d')\setminus\{0\}$ with the only ambiguity at $a=0$ (whence $\mathrm{EXP}(0)=\{0,1,X^{d/2}\}$).
  - **Remark 2.2 (lookup generalization)**: any table $T\subseteq\mathbb{Z}_q$, $|T|\le d$, $0\in T$ gives a lookup argument by replacing $\psi$ with $\psi_T := \sum_{i\in[1,d']}(-T_i)X^i + \sum_{i\in[1,d')} T_{i+d'}X^{-i}$.

### 3.4 Gadget decompositions

- $G_{b,k} = I_m \otimes \mathbf g_{b,k}$; $G^{-1}_{b,k}(M)$: per entry $x\in(-\hat b,\hat b)$ ($\hat b = b^k$), signed base-$b$ digits of $|x|$, sign applied to all digits (footnote 3). Deterministic and injective.
- Instantiations in the paper:
  - $G^{-1}_{d',\ell}$ on $R_q^{\kappa\times m}$ (inside $\mathrm{split}$): digits in $(-d',d')$, $\ell = \lceil\log_{d'} q\rceil$.
  - $G^{-1}_{d',k}$ on $\mathrm{cf}(\mathbf f) \in \mathbb{Z}_q^{n\times d}$ (Eq. 13): $D_f = [D_{f,0},\dots,D_{f,k-1}]$, $D_{f,i}\in\mathbb{Z}_q^{n\times d}$, $\|D_f\|_\infty < d'$, $D_f G_{d',k} = \mathrm{cf}(\mathbf f)$; recombination $f = \sum_i (d')^i \cdot D_{f,i}$ coefficient-wise.
  - $G^\top_{B,\hat\ell}$ in the R1CS reduction: $\mathbf z = G^\top_{B,\hat\ell}\mathbf f \in R_q^m$, $\hat\ell = \lceil\log_B q\rceil$, with $n = m\hat\ell$.

### 3.5 Challenge sets

- $\bar S \subseteq R_q$: folding challenges; strong sampling set (pairwise differences invertible) with small $\|\bar S\|_{\mathrm{op}}$; e.g. $\{-1,0,1,2\}^d$ for $d=64$ (< 2d bits per element vs $d\log q$ for a general $R_q$ element).
- $C$: sumcheck challenges; $\mathbb{Z}_q$ when $q$ is 128-bit; a $\mathbb{Z}_q$-vector space / extension $\mathbb{F}_{q^2}$ when $q$ is 64-bit. $|\bar S| = |C| \ge 2^\lambda$.
- $\mathcal{M}_C := C\times C$, $\mathcal{M}_q := R_q\times R_q$ — encode *two parallel sumcheck executions with independent challenges*, halving soundness error; needed at the union-bound-heavy step of $\Pi_{\mathrm{cm}}$ (Remark 4.9).
- Batching (Remark 2.5): $d$ claims over $\mathbb{Z}_q$ = one claim over $R_q$; $s$ claims over $R_q$ = one over $R_q[Y]/\langle Y^s+1\rangle$. Compression (Remark 2.6): $k$ claims $\{g_i\}$ → one via $\sum_i r^{i-1} g_i$, additive error $k/|\mathbb{F}|$; lift to extension field for small $|\mathbb{F}|$.

### 3.6 Commitments

- $\mathrm{com}(\mathbf a) = \mathbf A \mathbf a \in R_q^\kappa$, $\mathbf A \leftarrow R_q^{\kappa\times n}$; $\mathrm{com}(M) = \mathbf A M \in R_q^{\kappa\times m}$.
- $(b,S)$-valid opening of $\mathrm{cm}_\mathbf a$: $\mathbf a = \mathbf a' s$ with $\|\mathbf a'\|_\infty < b$, $s\in S \subseteq R_q^*$.
- $(b,S)$-relaxed binding (Def. 2.3): hard to find $\mathbf z_1,\mathbf z_2$, $s_1,s_2\in S$ with $0<\|\mathbf z_i\|_\infty<b$, $s_1^{-1}\mathbf z_1 \ne s_2^{-1}\mathbf z_2$ (computed in $R$), and $\mathbf A\mathbf z_1 s_1^{-1} = \mathbf A\mathbf z_2 s_2^{-1}$. Reduction to MSIS: $\mathbf x := s_2\mathbf z_1 - s_1\mathbf z_2 \ne 0$, $\mathbf A\mathbf x = 0$, $\|\mathbf x\|_\infty < 2b\|S\|_{\mathrm{op}} =: B$, so binding follows from $\mathrm{MSIS}^\infty_{q,\kappa,m,B}$.
- Binding is used with $S := \bar S - \bar S$ (difference set, all invertible since $\bar S$ strong sampling).
- Double commitment (Eq. 7): $\mathrm{dcom}(M) := \mathrm{com}(\mathrm{split}(\mathrm{com}(M))) \in R_q^\kappa$, requires $\kappa m d \ell \le n$.
- Lemma 4.1: binding of $\mathrm{com}$ ⟹ binding of $\mathrm{dcom}$ (collision either in $\mathrm{com}(M)$ vs $\mathrm{com}(M')$, in $\tau$ vs $\tau'$, or contradiction via $\mathrm{pow}(\tau)=\mathrm{com}(M)=\mathrm{com}(M')$).

### 3.7 Worked example of the monomial range machinery ($d = 8$, $d' = 4$)

$\psi = \sum_{i=1}^{3} i(X^{-i}+X^i) = 1\cdot(X^7\cdot(-1)+X) + 2\cdot(X^6\cdot(-1)+X^2) + 3\cdot(X^5\cdot(-1)+X^3)$ (using $X^{-i}\equiv -X^{d-i}$), so coefficient-wise: $\psi = [-0, 1, 2, 3, 0, -3, -2, -1]$ (index = power of $X$).
- Take $a = 2$: $\exp(2) = X^2$; $\mathrm{ct}(X^2\cdot\psi) = \psi$-coefficient at index $-2 \bmod 8 = 6$, which is $-2$... careful: $\mathrm{ct}(X^2\psi)$ picks the coefficient of $X^0$ in $X^2\psi$, i.e. the $\psi$-coefficient of $X^{-2} = -X^6 \to$ coefficient $-2$ times $-1$ sign of the wraparound = $2$. ✓ (Implementation must apply the negacyclic wrap: coefficient at wrapped index gets multiplied by $-1$.)
- Take $a = -3$: $\exp(-3) = X^{-3}\cdot\mathrm{sgn} = -X^5 = X^{5}\cdot(-1)$; but also $-X^5 = X^{5+8}/X^8$... the canonical form is $\exp(a) = X^{a+d}$ for $a<0$, so $\exp(-3) = X^{5}$ **with** the sign absorbed: $\exp(-3) := \mathrm{sgn}(-3)X^{-3} = -X^{-3} = -(-X^5) = X^5$. Then $\mathrm{ct}(X^5\psi)$ = wrap-corrected coefficient of $X^{-5}$ in $\psi$, i.e. index 3 with value $3$ and negacyclic sign $-1$ → $-3$. ✓
- Take $a = 0$: $\mathrm{EXP}(0) = \{0, 1, X^{4}\}$; $\mathrm{ct}(0) = 0$; $\mathrm{ct}(\psi) = 0$ (no constant term); $\mathrm{ct}(X^{4}\psi) = \psi$-coefficient at index 4 = 0. ✓ All three options map to $0$.
- Non-example: $a = 5 \notin (-4,4)$. Is there $b\in\mathcal{M}$ with $\mathrm{ct}(b\psi) = 5$? The 8 attainable values are exactly $\{0,\pm1,\pm2,\pm3\}$ — no. This is Lemma 2.2's converse.

### 3.8 Where range proofs sit relative to "cross terms"

In Pedersen-style folding (Nova), folding $\mathbf z' = \mathbf z_1 + r\mathbf z_2$ produces a quadratic cross term $T = (A\mathbf z_1)\circ(B\mathbf z_2)$ that must itself be committed and range-controlled when the commitment is lattice-based. LatticeFold+ restructures the pipeline so that the only quantity needing a range proof is the **folded witness vector** (plus its decomposition helpers $\tau_D, \mathbf m_\tau, M_f$):
- the linearization sumcheck (Fig. 1) absorbs the R1CS quadratic cross terms into *evaluation values* $v_A, v_B, v_C$ (these are $R_q$ values in the instance, not committed vectors);
- the commitment transformation $\Pi_{\mathrm{cm}}$ converts the non-homomorphic double commitment into a single linear commitment whose opening $\mathbf g$ has the norm bound $\|\mathbf g\|_\infty < b/2$, certified *not* by a bit-decomposition argument but by the monomial/ψ machinery of $\Pi_{\mathrm{rgchk}}$;
- consequently there are **no bit-decomposed commitments of cross terms at any point**, and the norm slack introduced per fold is the explicit $\|\bar S\|_{\mathrm{op}}(d'+1+B+dk)$ term, corrected once per fold by $\Pi_{\mathrm{decomp}}$.

## 4. Relations

### 4.1 Generalized committed linear relation $\mathcal{R}_{\mathrm{lin},B}$ (Definition 3.1)

Index $i = (\mathrm{com}(\cdot), (M^{(i)}\in R_q^{n\times n})_{i\in[n_{\mathrm{lin}}]})$; instance $\mathbf x = (\mathrm{cm}_\mathbf f, \mathbf r \in \mathcal{M}_C^{\log n}, \mathbf v \in \mathcal{M}_q^{n_{\mathrm{lin}}})$; witness $\mathbf w = \mathbf f \in R_q^n$. Membership (Eq. 5):

$$(\|\mathbf f\|_\infty < B) \;\wedge\; (\mathrm{cm}_\mathbf f = \mathrm{com}(\mathbf f)) \;\wedge\; \forall i\in[n_{\mathrm{lin}}]:\; \langle M^{(i)}\mathbf f, \mathrm{tensor}(\mathbf r)\rangle = v_i .$$

Each check is a *pair* of multilinear evaluations (at the two points of $\mathbf r \in \mathcal{M}_C^{\log n} = C\times C$). $R_{\mathrm{lin},B}$ (Eq. 31, Appendix A) replaces $\mathcal{M}_C,\mathcal{M}_q$ by $C, R_q$ (single point). The R1CS instantiation uses $n_{\mathrm{lin}}=4$ with

$$M^{(1)} = I_n,\quad M^{(2)} = A G^\top_{B,\hat\ell},\quad M^{(3)} = B G^\top_{B,\hat\ell},\quad M^{(4)} = C G^\top_{B,\hat\ell}.$$

### 4.2 Opening relations

$$R_{\mathrm{open}} := \{(\mathbf x = \mathrm{cm}_\mathbf f \in R_q^\kappa,\ \mathbf w = \mathbf f \in R_q^n) : \mathbf f \text{ is a valid opening of } \mathrm{cm}_\mathbf f\}\quad(\text{Eq. } 6)$$

$$R_{\mathrm{dopen},m} := \{(\mathbf x = C_M \in R_q^\kappa,\ \mathbf w = (\tau \in (-d',d')^n, M \in R_q^{n\times m})) : (\tau, M) \text{ valid opening of } C_M\}\quad(\text{Eq. } 8)$$

where "$( \tau, M)$ valid": (1) $M$ valid opening of $\mathrm{pow}(\tau) = \mathrm{com}(M)$, and (2) $\tau$ valid opening of $C$ viewed as linear commitment. Note $\tau$ need not equal $\mathrm{split}(\mathrm{com}(M))$ since $\mathrm{pow}$ is non-injective (Remark 4.1).

### 4.3 Monomial relations (Section 4.2)

$$R_{m,\mathrm{in}} := \{(\mathbf x = C_M,\ \mathbf w = M \in R_q^{n\times m}) : M_{i,j}\in\mathcal{M}\ \forall(i,j),\ (C_M,(\mathrm{split}(\mathrm{com}(M)), M)) \in R_{\mathrm{dopen},m}\}\quad(\text{Eq. } 9)$$

$$R_{m,\mathrm{out}} := \{(\mathbf x = (C_M, \mathbf r\in C^{\log n}, \mathbf e\in R_q^m),\ \mathbf w = M) : M^\top \mathrm{tensor}(\mathbf r) = \mathbf e \wedge (C_M, (\mathrm{split}(\mathrm{com}(M)), M))\in R_{\mathrm{dopen},m}\}\quad(\text{Eq. } 10)$$

### 4.4 Range-check relations (Section 4.3)

Warm-up $R'_{\mathrm{rg}}$ (single $\mathbb{Z}_q$-vector $\tau$):
- Input: $\mathbf x = (\mathrm{cm}_\tau, \mathrm{cm}_{m_\tau})$, $\mathbf w = (\tau, m_\tau)$ s.t. $\tau\in(-d',d')^n$, $(\mathrm{cm}_{m_\tau}, m_\tau)\in R_{m,\mathrm{in}}$, $m_\tau \in \mathrm{EXP}(\tau)$, $(\mathrm{cm}_\tau,\tau)\in R_{\mathrm{open}}$.
- Output $R'$: $\mathbf x = (\mathrm{cm}_\tau, \mathrm{cm}_{m_\tau}, \mathbf r, (a,b))$, $\mathbf w = (\tau, m_\tau)$ s.t. $[\tau, m_\tau]^\top \mathrm{tensor}(\mathbf r) = (a,b)$ and both openings valid.

Full range relation $R_{\mathrm{rg},B}$ (Eq. 14) for $\mathbf f\in R_q^n$ with $\|\mathbf f\|_\infty < B = (d')^k$:
- $\mathbf x = (\mathrm{cm}_\mathbf f, C_{M_f}, \mathrm{cm}_{m_\tau} \in R_q^{\kappa\times 3})$,
  $\mathbf w = [\tau_D, m_\tau, \mathbf f, M_f] \in \mathbb{Z}_q^n \times R_q^{n\times(2+dk)}$ s.t.
  1. $\mathrm{cf}(\mathbf f)\in(-B,B)^{n\times d}$;
  2. $(C_{M_f}, M_f) \in R_{m,\mathrm{in}}$;
  3. $M_f \in \mathrm{EXP}(D_f)$;
  4. $((C_{M_f}, \mathrm{cm}_{m_\tau}), (\tau_D, m_\tau)) \in R'_{\mathrm{rg}}$;
  5. $(C_{M_f}, (\tau_D, M_f)) \in R_{\mathrm{dopen},dk}$.

Output $R_{\mathrm{dcom}}$ (Eq. 15): $\mathbf x = (\mathrm{cm}_\mathbf f, C_{M_f}, \mathrm{cm}_{m_\tau}, \mathbf r\in C^{\log n}, \mathbf e\in R_q^{3+dk})$, $\mathbf w = [\tau_D, m_\tau, \mathbf f, M_f]$ with

$$[\tau_D, m_\tau, \mathbf f, M_f]^\top \mathrm{tensor}(\mathbf r) = \mathbf e,\quad (\mathrm{cm}_\mathbf f,\mathbf f)\in R_{\mathrm{open}},\ (\mathrm{cm}_{m_\tau},m_\tau)\in R_{\mathrm{open}},\ (C_{M_f},(\tau_D,M_f))\in R_{\mathrm{dopen},dk}.$$

### 4.5 Commitment-transformation output relation $R_{\mathrm{com}}$ (Eq. 17)

$$R_{\mathrm{com}} := \{(\mathbf x = \mathrm{cm}_\mathbf g \in R_q^\kappa,\ \mathbf r_o\in \mathcal{M}_C^{\log n},\ \mathbf v_o\in\mathcal{M}_q,\ \mathbf w = \mathbf g\in R_q^n) : \langle \mathbf g, \mathrm{tensor}(\mathbf r_o)\rangle = v_o \wedge \|\mathbf g\|_\infty < b/2 \wedge (\mathrm{cm}_\mathbf g,\mathbf g)\in R_{\mathrm{open}}\}$$

— a special case of $\mathcal{R}_{\mathrm{lin},b/2}$ with a single evaluation check, with $b \ge 2\|\bar S\|_{\mathrm{op}}(d'+1+B+dk)$.

### 4.6 Committed R1CS (Definition A.1) and folding relations

$$R^{\mathrm{cR1CS}}_B:\quad i = (A,B,C\in R_q^{n\times m}),\ \mathbf x = (\mathrm{cm}\in R_q^\kappa, \mathbf x_{\mathrm{in}}\in R_q^{\ell_{\mathrm{in}}}),\ \mathbf w = \mathbf f\in R_q^n,$$
$$\mathrm{cm} = \mathrm{com}(\mathbf f),\ \|\mathbf f\|_\infty < B,\ \mathbf z := G^\top_{B,\hat\ell}\mathbf f:\ (A\mathbf z)\circ(B\mathbf z)=C\mathbf z,\ \mathbf z[0..\ell_{\mathrm{in}}] = (1,\mathbf x_{\mathrm{in}}).\quad(\text{Eq. } 30)$$

(16 field R1CS constraints pack into one $R_q$ constraint per Remark 4.1 of [BC24].) Folding target: $\mathcal{R}_{\mathrm{comp}} := R^{(L-2)}_{\mathrm{lin},B}$, $\mathcal{R}_{\mathrm{acc}} := R^{(2)}_{\mathrm{lin},B}$; the scheme reduces $\mathcal{R}_{\mathrm{comp}}\times\mathcal{R}_{\mathrm{acc}} \to \mathcal{R}_{\mathrm{acc}}$ via (i) $\Pi_{\mathrm{mlin},L,B}: R^{(L)}_{\mathrm{lin},B} \to R_{\mathrm{lin},B^2}$ and (ii) $\Pi_{\mathrm{decomp},B}: R_{\mathrm{lin},B^2}\to R^{(2)}_{\mathrm{lin},B}$.

## 5. Protocols

### 5.0 The sumcheck layer — exact round-by-round transcription

Every heavy sub-protocol in LatticeFold+ is an instantiation of the **generalized sumcheck over rings** (Lemma 2.7, [CCKP19]). This subsection transcribes the generic protocol once, exactly, and then instantiates it for each concrete claim; the shared core engine's ring-norm sumcheck (`RingSC`) should implement exactly this layer.

**Generic statement.** Given $f \in \bar R_{\le \ell}[X_1,\dots,X_k]$ (individual degree $\le \ell$) over ring $\bar R$ with strong sampling set $C \subset \bar R$, and a value $s\in\bar R$, prove
$$s \stackrel{?}{=} \sum_{\mathbf b\in\{0,1\}^k} f(\mathbf b).$$
Prover time $\tilde O(2^k\ell)$ (for $f$ a sum of products of multilinear polys), verifier time and proof size $O(k\ell)$, soundness error $k\ell/|C|$, perfect completeness. In this paper: $k = \log n$, $\ell\in\{2,3\}$, $\bar R \in \{\mathbb{Z}_q, R_q, C=\mathbb{F}_{q^u}\}$.

**Round messages (prover, round $i = 1..k$):** with partial challenges $\rho_1,\dots,\rho_{i-1}$ fixed, the prover sends the univariate polynomial
$$g_i(X_i) \;:=\; \sum_{\mathbf b\in\{0,1\}^{k-i}} f(\rho_1,\dots,\rho_{i-1},\,X_i,\,\mathbf b)\;\in\; \bar R_{\le \ell}[X_i],$$
encoded as its $\ell+1$ coefficients $(g_i(0),\dots,g_i(\ell))$ (message size $(\ell+1)$ ring elements per round; total $(\ell+1)\log n$ elements).

**Verifier checks (round $i$):**
1. If $i = 1$: check $g_1(0) + g_1(1) = s$ (for $\ell \ge 1$; in general $\sum_{x\in\{0,1\}} g_i(x)$ replaced by the appropriate evaluation at the Boolean cube of the first variable).
2. If $i > 1$: check $g_i(0) + g_i(1) = g_{i-1}(\rho_{i-1})$, where $g_{i-1}(\rho_{i-1})$ was computed by the verifier in the previous round.
3. Sample $\rho_i \leftarrow C$, compute the running claim $c_i := g_i(\rho_i)$ (Horner over the $\ell+1$ coefficients).

**Final round / final opening:** after round $k$, the claimed value is fully determined: $v := g_k(\rho_k)$. The protocol has reduced $\sum_{\mathbf b} f(\mathbf b) = s$ to the single evaluation claim $f(\rho_1,\dots,\rho_k) = v$. The prover then **opens** the committed/structured components of $f$ at $\mathbf r := (\rho_1,\dots,\rho_k)$ — this is where each LatticeFold+ sub-protocol supplies its own opening step ($\{e_j\}$ in $\Pi_{\mathrm{mon}}$, $(\mathbf v, a)$ in $\Pi_{\mathrm{rgchk}}$, the $\mathbf e_o$ values in $\Pi_{\mathrm{cm}}$), and the verifier checks a *local* identity recomputing $v$ from the openings.

**Soundness mechanism:** if at any round the honest relation $g_i(0)+g_i(1) = g_{i-1}(\rho_{i-1})$ fails, then $h(X_i) := g_i(X_i) - \big(\text{true partial sum}\big)$ is a nonzero univariate of degree $\le\ell$, and the verifier's random $\rho_i$ catches it with prob $\ge 1 - \ell/|C|$ (generalized Schwartz-Zippel, Lemma 2.6: $\Pr[f(\mathbf r)=0]\le dk/|C|$ for degree-$d$ $k$-variate). Union over $k$ rounds: $k\ell/|C|$.

**Two-parallel-execution mode ($\mathcal{M}_C = C\times C$):** the claim is duplicated as a pair $(s, s)$, and each round's message is a pair $(g_i^{(0)}, g_i^{(1)})$ with challenges sampled independently $\rho_i^{(0)}, \rho_i^{(1)}\leftarrow C$; final openings are evaluated at the two points $\mathbf r^{(0)}, \mathbf r^{(1)}$. Soundness squares to $(k\ell/|C|)^2$. This mode is *mandatory* in $\Pi_{\mathrm{cm}}$ Step 5 (Remark 4.9).

**Batching mode (Remarks 2.5, 2.6):** $m$ claims $\sum_{\mathbf b} f_j(\mathbf b) = s_j$ (same cube) become one claim with polynomial $f_{\mathrm{comb}} := \sum_j \alpha^{j} f_j$ for a random combiner $\alpha\leftarrow C$ (or a fresh power basis $1, r, r^2, \dots$); the paper's canonical uses:
- $d$ claims over $\mathbb{Z}_q$ → one claim over $R_q$ (batch $\mathbf m_g^{(j)}$ across $j\in[m]$ in $\Pi_{\mathrm{mon}}$);
- 6 claims over $R_q$ in $\Pi_{\mathrm{cm}}$ Step 5 → understood as $6d$ claims over $\mathbb{Z}_q$ → one sumcheck over $C$ (Remark 4.6);
- $L$ executions of $\Pi_{\mathrm{lin},B}$ in $\Pi_{\mathrm{mlin},L,B}$ → one sumcheck (Construction 5.2 Step 1).
Additive soundness cost $m/|C|$ per compression step.

**Instantiation A — the monomial-check sumcheck (Construction 4.2, Eq. 11; degree $\ell = 3$):** the combined polynomial over $\mathbf x\in\{0,1\}^{\log n}$ is
$$f_{\mathrm{mon}}(\mathbf x) := \mathrm{eq}(\mathbf c, \mathbf x)\cdot\Big[\sum_{j\in[m]}\alpha_j\big(\mathbf m_g^{(j)}(\mathbf x)^2 - \mathbf m_g^{\prime(j)}(\mathbf x)\big)\Big],\qquad \sum_{\mathbf x} f_{\mathrm{mon}}(\mathbf x) = 0.$$
- Round $i$ message: $g_i(X) = \sum_{\mathbf b\in\{0,1\}^{\log n - i}} f_{\mathrm{mon}}(\rho_1..\rho_{i-1}, X, \mathbf b)$ — a degree-3 univariate (4 coefficients) because $\mathrm{eq}$ contributes degree 1 per variable and $\mathbf m_g^2$ contributes degree 2 in the round variable.
- Verifier: $g_1(0)+g_1(1) = 0$; then $g_i(0)+g_i(1) = g_{i-1}(\rho_{i-1})$; sample $\rho_i\leftarrow C$.
- Final opening: $\mathbf r = (\rho_1..\rho_{\log n})$, value $v = g_{\log n}(\rho_{\log n})$; the prover sends $\{e_j = \langle M_{*,j}, \mathrm{tensor}(\mathbf r)\rangle\}_{j\in[m]}$ and the verifier recomputes the terminal value via Eq. 12: $\mathrm{eq}(\mathbf c,\mathbf r)\cdot[\sum_j \alpha_j(\mathrm{ev}_{e_j}(\beta)^2 - \mathrm{ev}_{e_j}(\beta^2))] = v$.

**Instantiation B — the linear/folding-consistency sumchecks (Construction 4.5, Eqs. 18 & 20; degree $\ell = 2$):**
- Eq. 18 (four claims, one per vector $\mathbf w \in \{\tau_D, m_\tau, \mathbf f, \mathbf h\}$): $f^{\mathbf w}(\mathbf x) := \mathrm{eq}(\mathbf r, \mathbf x)\cdot \tilde{\mathbf w}(\mathbf x)$ summed $= \langle \mathbf w, \mathrm{tensor}(\mathbf r)\rangle$; the fourth uses target $u$ and includes $\mathbf h$ whose MLE the verifier cannot evaluate — hence the opening at $\mathbf r_o$.
- Eq. 20 (two claims, $z\in[2]$): $f^{(z)}(\mathbf x) := \tau_D(\mathbf x)\cdot t^{(z)}_g(\mathbf x)$ summed $= \langle\mathrm{tensor}(\mathbf c^{(z)}), \mathrm{com}(\mathbf h)\rangle$. Degree 2 since both factors are multilinear. **Key implementation fact** (Remark 4.6): all multiplications are by $\mathbb{Z}_q$-scalars ($\mathrm{tensor}(\mathbf r)\in\mathbb{Z}_q^n$, $\tau_D\in\mathbb{Z}_q^n$), so each $R_q$-valued claim splits into $d$ independent $\mathbb{Z}_q$ claims — the sumcheck prover never does an $R_q$ multiplication.
- Rounds/verifier checks as in the generic protocol with $\ell = 2$ (3 coefficients per message); run as TWO parallel executions with challenges $\mathbf r_o\in(C\times C)^{\log n}$.
- Final opening: the terminal claims are Eq. 22, $[\tau_D, m_\tau, \mathbf f, \mathbf h]^\top\mathrm{tensor}(\mathbf r_o) = \mathbf e_o\in(R_q\times R_q)^4$; $\mathbf e_o$ is precisely the pair-of-points evaluation vector that the *next* folding round consumes, and the verifier can evaluate $\mathrm{eq}(\mathbf r,\cdot)$, $t_g^{(0)}$, $t_g^{(1)}$ at both points of $\mathbf r_o$ by itself.

**Where the "norm check" enters (what RingSC must expose):** the ring-norm sumcheck functionality used end-to-end is the *composition* $\Pi_{\mathrm{rgchk}}$ → $\Pi_{\mathrm{cm}}$: (i) degree-3 monomial sumchecks prove $M_f\in\mathrm{EXP}(D_f)$, $m_\tau\in\mathrm{EXP}(\tau_D)$; (ii) degree-2 tensor sumchecks prove the folded-compatibility of $\mathbf h$ with the double commitment; (iii) the verifier's constant-term checks $\mathrm{ct}(\psi\cdot b) = a$ and Eq. 16 close the loop from monomial structure to coefficient ranges. A `RingSC` API should therefore expose: `prove_sumcheck(poly_spec, claim)` with round messages as above, `open_mle(table, r)`, `eval_tensor(c, r)` and `ct_psi(b)`, plus the paired-challenge wrapper.

### 5.1 Construction 4.1 — the split map (double commitment preprocessing)

On input $\mathrm{com}(M)\in R_q^{\kappa\times m}$ (with $m = dk$ in use, $\kappa m d\ell \le n$):
1. $M' := G^{-1}_{d',\ell}(\mathrm{com}(M)) \in R_q^{\kappa\times m\ell}$, $\|M'\|_\infty < d'$; flatten $M'' := \mathrm{flat}(M') \in R_q^{\kappa m\ell}$.
2. $\tau'_M := \mathrm{flat}(\mathrm{cf}(M''))\in(-d',d')^{\kappa m\ell d}$ (coefficient flattening; each entry $< d'$ in absolute value).
3. Zero-pad $\tau'_M$ to length $n$; output $\mathrm{split}(\mathrm{com}(M)) := \tau_M$.

Properties: injective (gadget decomposition and flattening injective); $\mathrm{pow}(\tau)$ recomputes $D = \mathrm{com}(M)$ by summing $d'$-power combination per group and re-embedding into coefficients of $\kappa\times m$ ring elements; $\mathrm{pow}$ NOT injective. Implementation: `pow(τ)` for $\tau$ reshaped as 4-D array $T\in(-d',d')^{\kappa\times dk\times d\times \ell}$ with index $i(d^2k\ell) + j(d\ell) + o\ell + p$ (Remark 4.5).

### 5.2 Construction 4.2 — monomial set check $\Pi_{\mathrm{mon}}$

**Input** $(\mathbf x = C_M,\ \mathbf w = M\in\mathcal{M}^{n\times m}) \in R_{m,\mathrm{in}}$.

1. **V → P**: challenges $\mathbf c \leftarrow C^{\log n}$ and $\beta \leftarrow C$.
2. **P ↔ V** (degree-3 sumcheck, batched over $j\in[m]$ claims via random combiner $\alpha\leftarrow C$, Remark 2.6). For $j\in[m]$ define
   $$\mathbf m_g^{(j)} := (\mathrm{ev}_{M_{0,j}}(\beta),\dots,\mathrm{ev}_{M_{n-1,j}}(\beta)),\qquad \mathbf m_g^{\prime(j)} := (\mathrm{ev}_{M_{0,j}}(\beta^2),\dots,\mathrm{ev}_{M_{n-1,j}}(\beta^2)),$$
   and the $j$-th claim (Eq. 11):
   $$\sum_{i\in[n]} \mathrm{eq}(\mathbf c,\langle i\rangle)\cdot\left(\mathbf m_g^{(j)}(\langle i\rangle)^2 - \mathbf m_g^{\prime(j)}(\langle i\rangle)\right) = 0 .$$
   The batched claim, with sumcheck challenges $\mathbf r\leftarrow C^{\log n}$, combiner $\alpha$, claimed value $v\in C$:
   $$\mathrm{eq}(\mathbf c,\mathbf r)\cdot\Big[\sum_{j\in[m]}\alpha_j\,\mathbf m_g^{(j)}(\mathbf r)^2 - \mathbf m_g^{\prime(j)}(\mathbf r)\Big] = v .$$
   (Sumcheck round messages are the univariate degree-3 partial sums in each of the $\log n$ rounds; verifier checks per round that $\sum_{x\in\{0,1\}}$ of previous message equals previous claimed total, and final round message is consistent at $\mathbf r$.)
3. **P → V**: openings $\{e_j := M^\top_{*,j}(\mathbf r)\in R_q\}_{j\in[m]}$ (i.e. $\langle M_{*,j},\mathrm{tensor}(\mathbf r)\rangle$).
4. **V**: check (Eq. 12):
   $$\mathrm{eq}(\mathbf c,\mathbf r)\cdot\Big[\sum_{j\in[m]}\alpha_j\big(\mathrm{ev}_{e_j}(\beta)^2 - \mathrm{ev}_{e_j}(\beta^2)\big)\Big] = v .$$
   Abort on failure.
5. **Output**: $(\mathbf x = (C_M, \mathbf r, \mathbf e),\ \mathbf w = M)\in R_{m,\mathrm{out}}$.

**Efficiency (Remark 4.3)**: degree-3 sumcheck over $C$ (plain field arithmetic, no $R_q$ mults). The $\{e_j\}$ openings cost $O(n)$ $\mathbb{Z}_q$-mults (build $\mathrm{tensor}(\mathbf r)$) + $O(nm)$ $\mathbb{Z}_q$-adds: since each $M_{i,j} = X^{m_{i,j}}$, accumulate $v_{m_{i,j}} \mathrel{+}= \mathrm{tensor}(\mathbf r)_i$ into a length-$d$ accumulator. Committing $\mathrm{com}(M)$ = sum of rotated/sign-flipped columns of $\mathbf A$: $n\kappa m$ $R_q$-adds ≈ $n\kappa dm$ parallelizable $\mathbb{Z}_q$-adds — comparable to one arbitrary Ajtai commitment. **Knowledge error**: $\epsilon_{\mathrm{mon},m} = (2d+m+4\log n)/|C| + \epsilon_{\mathrm{bind}}$.

### 5.3 Construction 4.3 — warm-up range check (scalar vector $\tau\in(-d',d')^n$)

**Input** $(\mathbf x = (\mathrm{cm}_\tau, \mathrm{cm}_{m_\tau}),\ \mathbf w = (\tau, m_\tau \in \mathrm{EXP}(\tau)))\in R'_{\mathrm{rg}}$ (in practice $m_\tau := \exp(\tau)$).

1. Run $\Pi_{\mathrm{mon}}$ on $m_\tau$ → output $(\mathrm{cm}_{m_\tau}, \mathbf r, b)\in R_{m,\mathrm{out}}$ with $b = \langle m_\tau, \mathrm{tensor}(\mathbf r)\rangle \in R_q$.
2. **P → V**: $a := \langle \tau, \mathrm{tensor}(\mathbf r)\rangle \in C$.
3. **V**: with $\psi := \sum_{i\in[1,d')} i(X^{-i}+X^i)$, check $\mathrm{ct}(\psi\cdot b) = a$; abort on failure.
4. **Output**: $(\mathrm{cm}_\tau, \mathrm{cm}_{m_\tau}, \mathbf r, (a,b))\in R'$.

**Knowledge error**: $\epsilon'_{\mathrm{rg}} = \epsilon_{\mathrm{mon},1} + \epsilon_{\mathrm{bind}} + \log n/|C|$. Soundness heart: if $m_\tau\in\mathcal{M}^n$ but $\tau\notin(-d',d')^n$ or $m_\tau\notin\mathrm{EXP}(\tau)$, Lemma 2.2 gives $\mathrm{ct}(\psi\cdot m_\tau - \tau)\ne 0$, so $\mathrm{ct}(\psi\cdot b)=a$ with $a=\langle\tau,\mathrm{tensor}(\mathbf r)\rangle$, $b = \langle m_\tau,\mathrm{tensor}(\mathbf r)\rangle$ contradicts Schwartz-Zippel over $\mathbf r\in C^{\log n}$.

### 5.4 Construction 4.4 — range check $\Pi_{\mathrm{rgchk}}$ for $\mathbf f\in R_q^n$, $\|\mathbf f\|_\infty < B$

**Input** $(\mathbf x = (\mathrm{cm}_\mathbf f, C_{M_f}, \mathrm{cm}_{m_\tau})\in R_q^{\kappa\times3},\ \mathbf w = [\tau_D, m_\tau, \mathbf f, M_f])\in R_{\mathrm{rg},B}$.

1. **P ↔ V**: batched $\Pi_{\mathrm{mon}}$ over $M_f = [M_{f,0},\dots,M_{f,k-1}]\in\mathrm{EXP}(D_f)\subseteq\mathcal{M}^{n\times dk}$ AND $m_\tau\in\mathrm{EXP}(\tau_D)\subseteq\mathcal{M}^n$ (single sumcheck, single challenge $\mathbf r$, random combiners). Outputs:
   - $(\mathrm{cm}_{m_\tau}, \mathbf r, b)$ with $b = \langle m_\tau,\mathrm{tensor}(\mathbf r)\rangle$;
   - $(C_{M_f}, \mathbf r, \mathbf e\in R_q^{dk})$ with $\mathbf e = M_f^\top\mathrm{tensor}(\mathbf r)$;
   - per-limb evaluations $\mathbf u_i := (M_{f,i})^\top\mathrm{tensor}(\mathbf r) = \mathbf e[di, d(i+1))\in R_q^d$ for $i\in[k]$.
2. **P → V**: $\mathbf v := \mathrm{cf}(\mathbf f)^\top\mathrm{tensor}(\mathbf r) \in C^d$ and $a := \langle\tau_D,\mathrm{tensor}(\mathbf r)\rangle\in C$.
3. **V**: check
   $$\mathrm{ct}(\psi\cdot b) = a \qquad\text{and}\qquad \mathrm{ct}\big(\psi\cdot(\mathbf u_0 + d'\mathbf u_1 + \cdots + (d')^{k-1}\mathbf u_{k-1})\big) = \mathbf v\quad(\text{Eq. } 16)$$
   (interpretation: $\mathbf v$ is the coefficient-wise evaluation of $\mathbf f$; the second check certifies $\mathrm{cf}(\mathbf f) = \sum_i (d')^i\,\mathrm{ct}(\psi\cdot M_{f,i})$ entry-wise, i.e. $D_f$ really decomposes $\mathbf f$).
4. Assemble $\hat v := \sum_{i\in[d]} v_i X^i\in R_q$; **output** $(\mathbf x_o = (\mathrm{cm}_\mathbf f, C_{M_f}, \mathrm{cm}_{m_\tau}, \mathbf r, (a, b, \hat v, \mathbf u_0,\dots,\mathbf u_{k-1}))$, $\mathbf w_o = [\tau_D, m_\tau, \mathbf f, M_f])\in R_{\mathrm{dcom}}$.

**Knowledge error**: $\epsilon_{\mathrm{rg}} = \epsilon_{\mathrm{mon},dk+1} + \epsilon_{\mathrm{bind}} + \log n/|C|$.

### 5.5 Construction 4.5 — commitment transformation $\Pi_{\mathrm{cm}}$ (THE central protocol)

Assume $n = \kappa d^2 k\ell$ (powers of two; Remark 4.8 handles smaller $n$). **Input** $(\mathbf x, \mathbf w)\in R_{\mathrm{rg},B}$ as in §5.4.

1. **P ↔ V**: run $\Pi_{\mathrm{rgchk}}$ → $(\mathbf r\in C^{\log n}, \mathbf e\in R_q^{3+dk})$. (So $\mathbf e = [\tau_D, m_\tau, \mathbf f, M_f]^\top\mathrm{tensor}(\mathbf r)$: entries $\mathbf e[0]=\langle\tau_D,\mathrm{tensor}(\mathbf r)\rangle$, $\mathbf e[1] = b$, $\mathbf e[2] = \hat v$, $\mathbf e[3,3+dk) = M_f^\top\mathrm{tensor}(\mathbf r)$.)
2. **V → P**: folding challenges $\mathbf s\leftarrow\bar S^3$ and $\mathbf s' \leftarrow \bar S^{dk}$.
3. **P → V**: $\mathrm{com}(\mathbf h) := \mathrm{com}(M_f)\mathbf s' = \mathrm{com}(M_f\mathbf s')\in R_q^\kappa$ (a *folded commitment to the matrix*, sent only after $\mathbf s'$ is known — this is the whole point: $\mathrm{com}(M_f)\in R_q^{\kappa\times dk}$ is too big to send).
4. **V → P**: challenges $(\mathbf c^{(0)}, \mathbf c^{(1)})\leftarrow C^{\log\kappa}\times C^{\log\kappa}$.
5. **P ↔ V**: two parallel sumchecks (independent challenges) over the batch of six claims, compressed via Remarks 2.5/2.6 into a single degree-2 sumcheck per execution (in practice $6d$ claims over $\mathbb{Z}_q$ combined into one over $C$ or its extension — Remark 4.6):
   - **Claim (Eq. 18)**: with $u := \langle \mathbf e[3,3+dk), \mathbf s'\rangle\in R_q$:
     $$[\tau_D, m_\tau, \mathbf f, \mathbf h]^\top\mathrm{tensor}(\mathbf r) = (\mathbf e[0,2), u) .$$
     (Four inner-product claims, one per vector $\tau_D, m_\tau, \mathbf f, \mathbf h$ against $\mathrm{tensor}(\mathbf r)$; note only scalar multiplications occur because $\mathrm{tensor}(\mathbf r)\in C^n = \mathbb{Z}_q^n$.)
   - **Claims (Eq. 20)** for $z\in[2]$: define $\mathbf t^{(z)}\in R_q^n$ as the tensor vector
     $$\mathbf t^{(z)} := \mathrm{tensor}(\mathbf c^{(z)})\otimes \mathbf s'\otimes(1,d',\dots,(d')^{\ell-1})\otimes(1,X,\dots,X^{d-1})\quad(\text{Eq. } 19)$$
     and its multilinear extension $t^{(z)}_g$ (verifier-evaluable in $O(\log\kappa + dk + \ell)$ time by the mixed-product property). Check:
     $$\sum_{i\in[n]} \tau_D(\langle i\rangle)\cdot t_g^{(z)}(\langle i\rangle) = \langle \mathrm{tensor}(\mathbf c^{(z)}), \mathrm{com}(\mathbf h)\rangle\in R_q\qquad z = 0,1.$$
     If $\tau_D\in(-d',d')^n$, this is equivalent (Remark 4.5) to
     $$\langle \mathrm{tensor}(\mathbf c^{(z)}), \mathrm{pow}(\tau_D)\mathbf s'\rangle = \langle\mathrm{tensor}(\mathbf c^{(z)}), \mathrm{com}(\mathbf h)\rangle,\qquad(\text{Eq. } 21)$$
     i.e. $\mathrm{com}(\mathbf h)$ is the correct $\mathbf s'$-fold of $\mathrm{com}(M_f) = \mathrm{pow}(\tau_D)$.
   - Let $\mathbf r_o\leftarrow(C\times C)^{\log n}$ be the final sumcheck challenges. The two executions reduce everything to eight evaluation claims
     $$[\tau_D, m_\tau, \mathbf f, \mathbf h]^\top\mathrm{tensor}(\mathbf r_o) = \mathbf e_o\in(R_q\times R_q)^4\quad(\text{Eq. } 22)$$
     (verifier can evaluate $\mathrm{eq}(\mathbf r,\cdot)$, $t_g^{(0)}$, $t_g^{(1)}$ at both points of $\mathbf r_o$ itself).
6. **V**: compute the folded commitment and value
   $$(\mathrm{cm}_\mathbf g, \mathbf v_o) := s_0\cdot(C_{M_f}, \mathbf e_{o,0}) + s_1\cdot(\mathrm{cm}_{m_\tau}, \mathbf e_{o,1}) + s_2\cdot(\mathrm{cm}_\mathbf f, \mathbf e_{o,2}) + (\mathrm{com}(\mathbf h), \mathbf e_{o,3})\in R_q^{\kappa+2},$$
   treating $\mathbf e_o$ as a matrix $\in R_q^{2\times4}$ with columns $\mathbf e_{o,i}$.
7. **P**: compute the folded witness $\mathbf g := s_0\tau_D + s_1 m_\tau + s_2\mathbf f + \mathbf h\in R_q^n$.
8. **Output**: $(\mathbf x = (\mathrm{cm}_\mathbf g, \mathbf r_o, \mathbf v_o),\ \mathbf w = \mathbf g)\in R_{\mathrm{com}}$.

**Norm budget (Lemma 4.8)**: $\|\mathbf g\|_\infty < d'\|\bar S\|_{\mathrm{op}} + \|\bar S\|_{\mathrm{op}} + B\|\bar S\|_{\mathrm{op}} + dk\|\bar S\|_{\mathrm{op}} = B'/2 \le b/2$ where $B' = 2\|\bar S\|_{\mathrm{op}}(d'+1+B+dk)$. Requires $b \ge B'$.

**Knowledge error (Lemma 4.10)**: with $\mu = 3+dk$ and $\epsilon_{\mathrm{sum}} = (2\log n/|C|)^2$:
$$\epsilon_{\mathrm{cm},k} = \frac{\mu + dk}{|\bar S|} + 3\epsilon_{\mathrm{bind}} + \epsilon'_{\mathrm{rg}} + \epsilon_{\mathrm{rg}} + 2\epsilon_{\mathrm{sum}} + \frac{\mu(\log^2\kappa + (2\log n)^2)}{|C|}.$$

**Communication optimization (Remark 4.7)**: replace $\mathbf e' := \mathbf e[3,3+dk)\in R_q^{dk}$ (the dominant term) by $\tau_e := \mathrm{split}$-like decomposition into $(-d',d')^n$; prover sends $\mathrm{com}(\tau_e)$ and $(v_e, v'_e) := (\mathbf e'[\beta], \mathbf e'[\beta^2])\in C^{dk}$; proves range of $\tau_e$ via $\mathrm{com}(\exp(\tau_e))$ + Construction 4.3; adds sumcheck claims $\langle\mathrm{pow}(\tau_e), \mathbf s'\rangle = u$ and $\mathrm{pow}(\tau_e)[\beta] = v_e$, $\mathrm{pow}(\tau_e)[\beta^2]=v'_e$ (same tensor trick with $(1,\beta,\dots,\beta^{d-1})$ replacing $(1,X,\dots)$); constant-term check of Eq. 16 via extra challenge $\mathbf c'\leftarrow C^{\log d}$, $v' := \langle\mathbf u_0+\dots+(d')^{k-1}\mathbf u_{k-1},\mathrm{tensor}(\mathbf c')\rangle$, $\mathbf z := (1,d',\dots,(d')^{k-1})\otimes\mathrm{tensor}(\mathbf c')$, checking (i) $\mathrm{ct}(\psi\cdot v') = \langle\mathbf v,\mathrm{tensor}(\mathbf c')\rangle$ and (ii) $\langle\mathrm{pow}(\tau_e),\mathbf z\rangle = v'$ (Eq. 23); two more folding challenges $r_1,r_2\in\bar S$ fold $(\mathrm{com}(\tau_e),\mathrm{com}(\exp\tau_e))$ and $(\tau_e,\exp\tau_e)$ into $\mathrm{cm}_\mathbf g$, $\mathbf g$. Net saving factor $\approx dk/(2\kappa)$ in communication.

**Small-$n$ support (Remark 4.8)**: when $n \ll \kappa d^2k\ell$ (e.g. $n = \kappa dk\ell d^*$ with $d = (d^*)^2$): change step 2 of Construction 4.1 to pack the coefficient blocks as $R_q$ elements: $\tau_D = \sum_{i\in[d^*]}\tau_i X^i$ with $\tau_i = \mathrm{flat}(C_i)$; then range-check $\tau_D\in R_q^n$ via a helper $M_\tau\in\mathcal{M}^{n\times d^*}$, $\tau' = \mathrm{split}(\mathrm{com}(M_\tau))$, plus one more folded commitment $\mathrm{com}(\mathbf h') := \mathrm{com}(M_\tau)\mathbf s''$ with $\mathbf s''\leftarrow\bar S^{d^*}$. Trade-off: 2 helper commitments become 4.

### 5.6 Construction 5.1 — single-input folding $\Pi_{\mathrm{lin},B}$ ($\mathcal{R}_{\mathrm{lin},B}\to\mathcal{R}_{\mathrm{lin},B^2/L}$)

**Input** $(i, \mathbf x = (\mathrm{cm}_\mathbf f, \mathbf r\in\mathcal{M}_C^{\log n}, \mathbf v\in\mathcal{M}_q^{n_{\mathrm{lin}}}), \mathbf w = \mathbf f)$.

0. Prover derives helper data: $D_f = G^{-1}_{d',k}(\mathrm{cf}(\mathbf f))$; $M_f\in\mathrm{EXP}(D_f)$; $\tau_D = \mathrm{split}(\mathrm{com}(M_f))$; $m_\tau\in\mathrm{EXP}(\tau_D)$.
1. **P → V**: commitments $C_{M_f} = \mathrm{dcom}(M_f) = \mathrm{com}(\tau_D)\in R_q^\kappa$ and $\mathrm{cm}_{m_\tau} = \mathrm{com}(m_\tau)\in R_q^\kappa$.
2. **P ↔ V**: run $\Pi'_{\mathrm{cm}}$ — $\Pi_{\mathrm{cm}}$ augmented so that Step 5 additionally checks each linear check $\langle M^{(\ell)}\mathbf f, \mathrm{tensor}(\mathbf r)\rangle = v_\ell$ (rewritten as sumcheck claim $\sum_i m(\langle i\rangle)\,\mathrm{eq}(\mathbf r,\langle i\rangle) = v_\ell$, Eq. 29, with $m(\langle i\rangle) = M^{(\ell)}_{i,*}\mathbf f$; reduced to $\langle M^{(\ell)}\mathbf f,\mathrm{tensor}(\mathbf r_o)\rangle = v_{o,\ell}$). In Step 5 the equations are
   $$\big[M^{(\ell)}[\tau_D, m_\tau, \mathbf f, \mathbf h]\big]^\top\mathrm{tensor}(\mathbf r) = \mathbf e^{(\ell)}\quad\text{(pre-challenge)}\quad\Rightarrow\quad \big[M^{(\ell)}[\tau_D, m_\tau, \mathbf f, \mathbf h]\big]^\top\mathrm{tensor}(\mathbf r_o) = \mathbf e^{(\ell)}_o$$
   where the prover supplies the $\mathbf e^{(\ell)}$ values *before* seeing $\mathbf s,\mathbf s'$. Steps 6–8 additionally fold the $\mathbf e^{(\ell)}_o$ values. Also verifies $(\mathbf x' = (\mathrm{cm}_\mathbf f, C_{M_f}, \mathrm{cm}_{m_\tau}), \mathbf w' = (\tau_D, m_\tau, \mathbf f, M_f))\in R_{\mathrm{rg},B}$.
3. **Output**: $(\mathbf x_o = (\mathrm{cm}_\mathbf g, \mathbf r_o, \mathbf v_o),\ \mathbf w_o = \mathbf g)\in R_{\mathrm{lin},B^2/L}$. Knowledge error $\epsilon_{\mathrm{lin},k} = \epsilon_{\mathrm{cm},k}$.

### 5.7 Construction 5.2 — multi-instance folding $\Pi_{\mathrm{mlin},L,B}$ ($R^{(L)}_{\mathrm{lin},B}\to R_{\mathrm{lin},B^2}$)

**Input**: $L$ instances $\mathbf x_i = (\mathrm{cm}_{\mathbf f_i}, \mathbf r_i\in\mathcal{M}_C^{\log n}, \mathbf v^{(i)}\in\mathcal{M}_q^{n_{\mathrm{lin}}})$ with witnesses $\mathbf f_i$.

1. **P ↔ V**: run $L$ parallel executions of $\Pi_{\mathrm{lin},B}$ with ALL sumcheck claims compressed into a single sumcheck via random linear combination (Remark 2.6) — i.e., one Fiat-Shamir transcript, one sumcheck over $\log n$ variables, degree 2 (the combiner multiplies each execution's polynomial by $\alpha^i$-type powers).
2. The $L$ reduced statements $(\mathrm{cm}_{\mathbf g_i}, \mathbf r_o, \mathbf v_o^{(i)}, \mathbf g_i)\in R_{\mathrm{lin},B^2/L}$ are folded *instantaneously* (verifier-side linear combination, no interaction):
   $$\mathbf x_{\mathrm{fold}} = \Big(\sum_{i\in[L]}\mathrm{cm}_{\mathbf g_i},\ \mathbf r_o,\ \sum_{i\in[L]}\mathbf v_o^{(i)}\Big),\qquad \mathbf w_{\mathrm{fold}} = \sum_{i\in[L]}\mathbf g_i\in R_{\mathrm{lin},B^2}.$$

**Theorem 5.2**: knowledge error $\epsilon_{\mathrm{mlin},B,L} \le L\cdot\epsilon_{\mathrm{lin},k}$.

### 5.8 Construction 5.3 — decomposition $\Pi_{\mathrm{decomp},B}$ ($R_{\mathrm{lin},B^2}\to R^{(2)}_{\mathrm{lin},B}$)

**Input**: $(i, \mathbf x = (\mathrm{cm}_\mathbf f, \mathbf r, \mathbf v), \mathbf w = \mathbf f)\in R_{\mathrm{lin},B^2}$.

1. **P → V**: decompose $\mathbf f$ into $F = [F^{(0)}, F^{(1)}]\in R_q^{n\times2}$ (footnote-3 signed gadget style, base $B$): $\|F\|_\infty < B$, $\mathbf f = F\times[1,B]^\top$. Send $C = \mathrm{com}(F)\in R_q^{\kappa\times2}$ and values $\mathbf v^{(0)},\mathbf v^{(1)}\in\mathcal{M}_q^{n_{\mathrm{lin}}}$ defined by $\langle M^{(i)}F^{(j)},\mathrm{tensor}(\mathbf r)\rangle = v^{(j)}_i$.
2. **V**: check $C\times[1,B]^\top = \mathrm{cm}_\mathbf f$ and $\mathbf v^{(0)} + B\mathbf v^{(1)} = \mathbf v$; return ⊥ on failure.
3. **Output**: two statements $(C_{*,i}, \mathbf r, \mathbf v^{(i)})$ with witness halves $F^{(i)}$ — i.e. $R^{(2)}_{\mathrm{lin},B}$, ready to be the next accumulation pair.

**Lemma 5.1**: RoK with **zero** knowledge error (extractor sets $\mathbf f := F\times[1,B]^\top$; verifier check + output validity ⟹ input validity). Remark 5.2: for small $L$ the actual output norm $\bar b \ll B^2$, so decomposition can be delayed or use $\bar b < B$.

### 5.9 Figure 1 — R1CS → $R'_{\mathrm{lin},B}$ reduction (line-by-line)

Parameters: sumcheck challenge set $C$. Input: $i = (A,B,C\in R_q^{n\times m})$, $\mathbf x = (\mathrm{cm}, \mathbf x_{\mathrm{in}})\in R_q^\kappa\times R_q^{\ell_{\mathrm{in}}}$, $\mathbf w = \mathbf f\in R_q^n$ ($n = m\hat\ell$, $\hat\ell = \lceil\log_B q\rceil$).

1. **V → P**: random vector $\mathbf r\leftarrow C^{\log n}$.
2. **P ↔ V**: define the degree-2 polynomial
   $$g(\mathbf x) := \mathrm{eq}(\mathbf r, \mathbf x)\cdot[g_A(\mathbf x)g_B(\mathbf x) - g_C(\mathbf x)],\qquad g_M(\mathbf x) := \sum_{\mathbf b\in\{0,1\}^{\log n}} (\widetilde{M'\mathbf f})(\mathbf x, \mathbf b)\cdot\tilde f(\mathbf b),\quad M' := M G^\top_{B,\hat\ell}.$$
   Run sumcheck for $\sum_{\mathbf b\in\{0,1\}^{\log n}} g(\mathbf b) = 0$. Challenges $\mathbf r_o\leftarrow C^{\log n}$; reduces to $g(\mathbf r_o) = s$ for claimed $s\in R_q$.
3. **P → V**: $(v, v_A, v_B, v_C)\in R_q^4$ where
   $$v := \tilde f(\mathbf r_o) = \langle\mathbf f,\mathrm{tensor}(\mathbf r_o)\rangle,\qquad v_M := \sum_{\mathbf b\in\{0,1\}^{\log n}}(\widetilde{M'\mathbf f})(\mathbf r_o,\mathbf b)\tilde f(\mathbf b) = \langle M'\mathbf f, \mathrm{tensor}(\mathbf r_o)\rangle.$$
4. **V**: compute $e := \mathrm{eq}(\mathbf r, \mathbf r_o)$ and check $e\cdot(v_A v_B - v_C) = s$.
5. Output $i_o := (I_n, A', B', C')$, $\mathbf x_o := (\mathrm{cm}, \mathbf r_o, (v, v_A, v_B, v_C))$, $\mathbf w_o := \mathbf f$ — an $R'_{\mathrm{lin},B}$ triple, expanded to $R_{\mathrm{lin},B}$ by duplicating: $\mathbf r'_o = (\mathbf r_o,\mathbf r_o)\in\mathcal{M}_C^{\log n}$, values $((v,v),(v_A,v_A),(v_B,v_B),(v_C,v_C))\in\mathcal{M}_q^4$.

Remark A.1: the unused $v$ exists to align the reduced instance format with the accumulated instance format of Construction 5.2.

### 5.10 End-to-end folding pipeline (per IVC step)

$$R^{\mathrm{cR1CS}}_B \xrightarrow{\text{Fig. 1 (sumcheck, linearization)}} R_{\mathrm{lin},B}\ (\times L) \xrightarrow{\Pi_{\mathrm{mlin},L,B}\ (\S5.7)} R_{\mathrm{lin},B^2} \xrightarrow{\Pi_{\mathrm{decomp},B}\ (\S5.8)} R^{(2)}_{\mathrm{lin},B} = \mathcal{R}_{\mathrm{acc}}.$$

Each IVC step: the prover folds $(L-2)$ fresh $\mathcal{R}_{\mathrm{comp}}$ instances into the 2-instance accumulator; Theorem 5.1 (composition via Theorem 2.1) gives the RoK from $\mathcal{R}_{\mathrm{comp}}\times\mathcal{R}_{\mathrm{acc}}$ to $\mathcal{R}_{\mathrm{acc}}$ with condition (Eq. 28) $\|\bar S\|_{\mathrm{op}} L(d'+1+B+dk)\le B^2$ and $\mathrm{com}$ $(2B^2, \bar S-\bar S)$-binding.

### 5.11 Exact fold/update equations for the (commitment, witness, cross-term) triple

Collecting the state update in one place. Per input instance $i\in[L]$ with $(\mathrm{cm}_{\mathbf f_i}, \mathbf r_i, \mathbf v_i; \mathbf f_i)$ and its derived helper data $(\tau_{D,i}, \mathbf m_{\tau,i}, M_{f,i}, \mathbf h_i = M_{f,i}\mathbf s')$:

1. **Commitment fold** (verifier-computable, Eq. of Step 6, Constr. 4.5 — this replaces Pedersen-style $\mathrm{cm}' = \mathrm{cm}_1 + r\,\mathrm{cm}_2$ of Nova/HyperNova):
$$\mathrm{cm}_\mathbf g \;=\; s_0\,C_{M_f} + s_1\,\mathrm{cm}_{m_\tau} + s_2\,\mathrm{cm}_\mathbf f + \mathrm{com}(\mathbf h),\qquad \mathrm{com}(\mathbf h) = \mathrm{com}(M_f)\,\mathbf s'.$$
   In the multi-instance case (Constr. 5.2): $\mathrm{cm}_{\mathrm{fold}} = \sum_{i\in[L]}\mathrm{cm}_{\mathbf g_i}$.
2. **Witness fold** (prover-side):
$$\mathbf g \;=\; s_0\,\tau_D + s_1\,\mathbf m_\tau + s_2\,\mathbf f + \mathbf h \;=\; s_0\,\tau_D + s_1\,\mathbf m_\tau + s_2\,\mathbf f + M_f\mathbf s',$$
   and multi-instance: $\mathbf f_{\mathrm{fold}} = \sum_{i\in[L]}\mathbf g_i$.
3. **Value/cross-term fold**: $\mathbf v_o = s_0\,\mathbf e_{o,0} + s_1\,\mathbf e_{o,1} + s_2\,\mathbf e_{o,2} + \mathbf e_{o,3}$ (single instance) — the analog of the R1CS cross term $T = (A\mathbf z_1)\circ(B\mathbf z_2)$: here the "cross term" role is played by the *evaluation vector* $\mathbf e$ whose entries mix the range-proof helpers; multi-instance: $\mathbf v_{\mathrm{fold}} = \sum_i \mathbf v_o^{(i)}$; challenge vectors unify $\mathbf r_i \to \mathbf r_o$ through the sumchecks.
4. **Decomposition update** (Constr. 5.3): $\mathbf f = F^{(0)} + B\,F^{(1)}$, $\mathrm{cm}_\mathbf f = C_{*,0} + B\,C_{*,1}$, $\mathbf v = \mathbf v^{(0)} + B\,\mathbf v^{(1)}$; the two halves become the new accumulator pair. No error/slack term is carried (contrast with relaxed R1CS in Nova: the Ajtai relaxation is the *multiplicative unit* $s\in\bar S-\bar S$ from $(b,S)$-valid openings, which never materializes as a stored cross-term).

### 5.12 IVC/PCD usage pattern (how the folding scheme is driven)

Per step $t$ of an incrementally-verifiable computation (Nova-style, adapted to $L$-ary folding):

1. The step function is expressed as committed R1CS $R^{\mathrm{cR1CS}}_B$ over $R_q$ (with 16× field-constraint packing if the target statement lives over $\mathbb{F}_{q^4}$): witness $\mathbf f_t$ includes $\mathbf z_t = G^\top_{B,\hat\ell}\mathbf f_t$, the previous step's instance digest, and the folding-verifier transcript witness.
2. The prover runs Fig. 1 on $\mathbf f_t$ → a fresh $\mathcal{R}_{\mathrm{lin},B}$ instance $(\mathrm{cm}_{\mathbf f_t}, \mathbf r_t, \mathbf v_t)$. ($L-2$ such instances can be accumulated per fold, e.g. $L=3$: one online + two accumulated.)
3. The prover runs $\Pi_{\mathrm{mlin},L,B}$ over the $L$ instances (one batched Fiat-Shamir transcript) → single $R_{\mathrm{lin},B^2}$ instance, then $\Pi_{\mathrm{decomp},B}$ → the new 2-instance accumulator.
4. The *recursive circuit* verifies only the folding transcript: it re-derives all challenges, recomputes $\mathrm{cm}_\mathbf g, \mathbf v_o$ as linear combinations, and checks the $\approx$ handful of $R_q$-sized identities (Eqs. 12, 16, 21/22) — never any $n$-sized object. Its dominant cost is hashing ≲100 $R_q$-elements (the proof).
5. After $N$ steps, the terminal accumulator instance is wrapped by a lattice-based SNARK for $\mathcal{R}_{\mathrm{lin}}$ (e.g. a LaBRADOR/Greyhound-style argument or a sumcheck+opening pipeline) to produce the final succinct proof. Folding proofs themselves are *recursive witnesses*, not final-proof components.

D-ary tree variant (Mangrove [Ngu+24], [RZ22]): the $L$-ary folding directly supports depth-$\log_L N$ trees instead of chains; the norm budget Eq. 28 is per node and unaffected by tree depth.

### 5.13 Design-decision checklist (for the implementer)

- [ ] Pick $q$ (128-bit) with $q\equiv 1+2^{16}\pmod{64}$ so $R_q$ splits into 16 NTT-friendly factors and Lemma 2.4 invertibility holds for $\bar S$-differences.
- [ ] Pick $d=64$, $d'=32$, $k=2$ ($B=2^{10}$), $\kappa=9$, $L=3$; verify Eq. 28 numerically with the *actual* $\|\bar S\|_{\mathrm{op}}$ (not the $d\cdot\max$ bound).
- [ ] Decide large-$n$ vs Remark 4.8 small-$n$ variant before writing `split` (stride contract differs).
- [ ] Decide whether to implement the Remark 4.7 communication compression (recommended: yes — it is what gets the proof under 100 KB) and the Remark 5.3 shared-helper batching (yes, if $L>2$).
- [ ] Fix the paired-challenge ($\mathcal{M}_C$) sumcheck mode as the default engine mode.
- [ ] Choose the terminal proof system for $\mathcal{R}_{\mathrm{lin}}$ (out of scope of the paper; any RoK-to-SIS argument works).

## 6. Soundness & Security

### 6.1 Framework

- Reduction of knowledge (Def. 2.4, [KP23]): $\mathsf{G},\mathsf{P},\mathsf{V}$ with knowledge soundness (Def. 2.6): extractor $\mathrm{Ext}$ such that $\Pr[\text{accept}] - \Pr[(i,\mathbf x_1,\mathrm{Ext})\in R_1]\le\kappa(\lambda)$. Sequential composition (Theorem 2.1, [KP23] Thm. 5) chains RoKs.
- All protocols have perfect completeness and public reducibility (deterministic $f(i,\mathbf x_1,\mathrm{tr}) = \mathbf x_2$) — the latter is what makes the folding verifier circuit well-defined for Fiat-Shamir.

### 6.2 Theorem statements

| ID | Statement | Content |
|---|---|---|
| Lemma 2.1 | Monomial squaring characterization | $a(X^2)=a(X)^2 \iff a\in\mathcal{M}'$ over $\mathbb{Z}_q[X]$, $q>2$ |
| Lemma 2.2 | Range lemma | $\mathcal{M}\xrightarrow{\mathrm{ct}(\psi\cdot\cdot)}(-d',d')$ with EXP bookkeeping |
| Lemma 2.4 | Invertibility | small-coefficient $R_q$ elements invertible when $q\equiv 1+2e\pmod{4e}$ |
| Lemma 2.6 | Schwartz-Zippel over rings | $\Pr[f(\mathbf r)=0]\le dk/|C|$ on strong sampling sets |
| Lemma 2.7 | Generalized sumcheck | the §5.0 protocol, error $k\ell/|C|$ |
| Lemma 4.1 | dcom binding | com binding ⟹ dcom binding |
| Lemma 4.2/4.3/4.4 | $\Pi_{\mathrm{mon}}$ | RoK $R_{m,\mathrm{in}}\to R_{m,\mathrm{out}}$, error $\epsilon_{\mathrm{mon},m}$ |
| Lemma 4.5 | warm-up range check | RoK $R'_{\mathrm{rg}}\to R'$, error $\epsilon'_{\mathrm{rg}}$ |
| Theorem 4.2 / Lemma 4.6/4.7 | $\Pi_{\mathrm{rgchk}}$ | RoK $R_{\mathrm{rg},B}\to R_{\mathrm{dcom}}$, error $\epsilon_{\mathrm{rg}}$ |
| Theorem 4.3 / Lemma 4.8/4.10 | $\Pi_{\mathrm{cm}}$ | RoK $R_{\mathrm{rg},B}\to R_{\mathrm{com}}$; norm condition $b\ge 2\|\bar S\|_{\mathrm{op}}(d'+1+B+dk)$; error $\epsilon_{\mathrm{cm},k}$ |
| Lemma 4.9 ([FMN24] 7.1) | coordinate-wise special soundness | the extractor engine, $\epsilon_\Psi - \mu/|\bar S|$ |
| Theorem 5.2 | $\Pi_{\mathrm{mlin},L,B}$ | RoK $R^{(L)}_{\mathrm{lin},B}\to R_{\mathrm{lin},B^2}$, error $\le L\,\epsilon_{\mathrm{lin},k}$ |
| Lemma 5.1 | $\Pi_{\mathrm{decomp},B}$ | RoK with **zero** knowledge error |
| Theorem 5.1 | end-to-end folding | $\mathcal{R}_{\mathrm{comp}}\times\mathcal{R}_{\mathrm{acc}}\to\mathcal{R}_{\mathrm{acc}}$ |
| Theorem 5.3 | efficiency | §7.1 numbers |
| Theorem 2.1 ([KP23] Thm 5) | sequential composition | chains the RoK stack |

Soundness dependency graph (what breaks what):

```
MSIS_{q,kappa,n,beta}  ──relaxed binding (Def 2.3)──▶  com binding  ──Lemma 4.1──▶  dcom binding
        │                                                        │
        ▼                                                        ▼
  Lemma 2.4 (invertibility of S̄-S̄)                    Pi_mon soundness (eps_mon)
        │                                                        │
        ▼                                                        ▼
  Lemma 2.6/2.7 (SZ + sumcheck) ──▶ Pi_rgchk (eps_rg) ──▶ Pi_cm (eps_cm,k)
                                                                │
                                          Lemma 4.9 extractor  ▼
                                                    Pi_mlin (L·eps_lin,k) ──▶ Thm 5.1
                                                    Pi_decomp (0)   ────────┘
```

- **Lemma 4.2 / 4.3**: $\Pi_{\mathrm{mon}}$ is an RoK $R_{m,\mathrm{in}}\to R_{m,\mathrm{out}}$; perfectly complete; knowledge error $\epsilon_{\mathrm{mon},m} = (2d+m+4\log n)/|C| + \epsilon_{\mathrm{bind}}$. Bad events: $B_1$ (bad entry passes the $\beta$-test, prob $2d/|C|$ by Cor. 4.1), $B_2$ (batched claim holds though entries bad: $m/|C| + \log n/|C|$), $B_3$ (sumcheck claim false but openings correct: $3\log n/|C|$).
- **Lemma 4.5**: warm-up range check RoK with error $\epsilon'_{\mathrm{rg}} = \epsilon_{\mathrm{mon},1} + \epsilon_{\mathrm{bind}} + \log n/|C|$.
- **Theorem 4.2 / Lemma 4.7**: $\Pi_{\mathrm{rgchk}}$ RoK $R_{\mathrm{rg},B}\to R_{\mathrm{dcom}}$, error $\epsilon_{\mathrm{rg}} = \epsilon_{\mathrm{mon},dk+1} + \epsilon_{\mathrm{bind}} + \log n/|C|$.
- **Theorem 4.3 / Lemmas 4.8, 4.10**: $\Pi_{\mathrm{cm}}$ RoK $R_{\mathrm{rg},B}\to R_{\mathrm{com}}$ with the norm condition $b\ge 2\|\bar S\|_{\mathrm{op}}(d'+1+B+dk)$; error $\epsilon_{\mathrm{cm},k}$ as above.
- **Theorem 5.2**: $\Pi_{\mathrm{mlin},L,B}$ RoK $R^{(L)}_{\mathrm{lin},B}\to R_{\mathrm{lin},B^2}$, error $\le L\,\epsilon_{\mathrm{lin},k}$.
- **Lemma 5.1**: $\Pi_{\mathrm{decomp},B}$ RoK with zero knowledge error.
- **Theorem 5.1**: end-to-end $\mathcal{R}_{\mathrm{comp}}\times\mathcal{R}_{\mathrm{acc}}\to\mathcal{R}_{\mathrm{acc}}$.

### 6.3 Extractor logic for $\Pi_{\mathrm{cm}}$ (the crux of the paper's soundness)

Uses **coordinate-wise special soundness** (Lemma 4.9 = [FMN24] Lemma 7.1): for $U = \bar S^\mu$, predicate $\Psi$, algorithm $\mathcal A: U\to T$ with $\epsilon_\Psi(\mathcal A)$ success, there is an oracle algorithm $E$ that on $(u_0, y_0)$ outputs $\mu+1$ pairs $(u^{(i)}, y^{(i)})$, all with $\Psi = 1$ and $u^{(i+1)}\equiv_i u^{(0)}$ (differ only in coordinate $i$), with probability $\ge \epsilon_\Psi(\mathcal A) - \mu/|\bar S|$, calling $\mathcal A$ expected $1+\mu$ times.

Instantiation: $\mu = 3+dk$ matches the folding challenges $(\mathbf s\in\bar S^3, \mathbf s'\in\bar S^{dk})$; the "adversary" $\mathcal A'$ hardcodes the final sumcheck challenge $\mathbf r_o$ and replays $\mathcal A^*$ with $u$ as the folding challenge. The extractor:
1. Sample $\mathbf r_o$, $u^{(0)}$, $y_0\leftarrow\mathcal A'(u^{(0)})$.
2. Call $E^{\mathcal A'}(u^{(0)},y_0)$ → transcripts with $u^{(i+1)}\equiv_i u^{(0)}$.
3. For each $i\in[\mu]$: $\mathbf w_i := (w_o^{(i+1)} - w_o^{(0)})/(u^{(i+1)}_i - u^{(0)}_i)\in R_q^n$ (Eq. 25; well-defined since $\bar S-\bar S$ invertible).
4. Output $\mathbf w = [\hat\tau_D, \hat m_\tau, \hat{\mathbf f}, \hat M_f] := [\mathbf w_0,\dots,\mathbf w_{\mu-1}]$.

Extracted-witness properties: (1) $\hat\tau_D,\hat m_\tau,\hat{\mathbf f}$ are $(b,S)$-valid openings of $C_{M_f}, \mathrm{cm}_{m_\tau}, \mathrm{cm}_\mathbf f$; (2) $\hat M_f$ valid opening of $\mathrm{com}(\hat M_f)$ (but maybe not of the double commitment); (3) $\mathrm{com}(\mathbf h^{(i)}) = \mathrm{com}(\hat M_f\mathbf s'^{(i)})$ for all transcripts (by linearity + verifier's Step-6 fold); (4) $[\hat\tau_D,\hat m_\tau,\hat{\mathbf f}]^\top\mathrm{tensor}(\mathbf r_o) = \mathbf e^{(0)}_o[0,3)$; (5) $\langle\hat M_f \mathbf s'^{(0)},\mathrm{tensor}(\mathbf r_o)\rangle = \mathbf e^{(0)}_o[3]$.

Bad events and bounds:
- **BAD1** ($\hat\tau_D\notin(-d',d')^n$): $\le\epsilon_1 = \epsilon_{\mathrm{bind}} + \epsilon'_{\mathrm{rg}} + \epsilon_{\mathrm{sum}}$ — mental experiment re-runs extraction with fresh randomness; the first transcript's challenges are uniformly random (no rejection-sampling bias possible), so a repeated $\hat\tau_D$ outside the range yet passing $\mathrm{ct}(\psi\cdot b) = a$ contradicts Lemma 4.5 / Schwartz-Zippel.
- **BAD2** ($(\hat\tau_D, \hat M_f)$ not a valid double-commitment opening, i.e. $\mathrm{pow}(\hat\tau_D)\ne\mathrm{com}(\hat M_f)$): $\le\epsilon_2 = \epsilon_{\mathrm{bind}} + \mu(\log^2\kappa + (2\log n)^2)/|C|$. Union bound over $\mu|\bar S|$ adversary calls of the sumcheck soundness $(\log\kappa/|C|)^2+\epsilon_{\mathrm{sum}}$ each — **this is exactly why TWO parallel sumchecks with independent challenges are needed** (Remark 4.9): a single sumcheck would give squared error $\approx(\log\kappa/|C|)$ only once, and $\mu|\bar S|\cdot\log\kappa/|C|$ would exceed 1.
- **BAD3** (valid double opening but $\notin R_{\mathrm{rg},B}$, e.g. $M_f\notin\mathrm{EXP}(D_f)$ or $\mathrm{cf}(\mathbf f)$ out of range): $\le\epsilon_3 = \epsilon_{\mathrm{bind}} + \epsilon_{\mathrm{rg}} + dk/|\bar S| + \epsilon_{\mathrm{sum}}$.

Total: $\epsilon_{\mathrm{cm},k} = (3+dk)/|\bar S| + \epsilon_1+\epsilon_2+\epsilon_3$ (matches the displayed formula after simplification: $3\epsilon_{\mathrm{bind}}$ from the three BADs, etc.).

### 6.4 Norm growth / slack analysis

- Input witnesses: $\|\mathbf f\|_\infty < B = (d')^k$.
- After $\Pi_{\mathrm{mlin}}$: output $\mathbf g = \sum_{i\in[L]}\mathbf g_i$, each $\|\mathbf g_i\|_\infty < \|\bar S\|_{\mathrm{op}}(d'+1+B+dk) = B^2/L$ by Eq. (28) — so $\|\mathbf g\|_\infty < B^2$ exactly.
- $\Pi_{\mathrm{decomp}}$ splits base-$B$ digits: halves have norm $<B$. **Norm never exceeds $B^2$ and returns to $B$ after decomposition** — unbounded folding.
- The MSIS binding requirement grows with the folded bound: $\mathrm{com}$ must be $(2B^2,\bar S-\bar S)$-binding ⟹ MSIS$_{q,\kappa,n,4B^2\|\bar S\|_{\mathrm{op}}}$-hard (via the $2b\|S\|_{\mathrm{op}}$ reduction in §3.6).
- "Why not decompose-then-fold (as LatticeFold)?" Remark 5.1: that alternative keeps the witness norm $\le B$ always (allowing larger $B$) but costs $2L$ decomposed commitments per step — the paper's fold-then-decompose is faster.

### 6.5 Worked norm-budget arithmetic (concrete table)

With $d = 64$, $d' = 32$, $B = 2^{10}$, $k = 2$, $\bar S = \{-1,0,1,2\}^{64}$, $L = 3$:
- $\|\bar S\|_{\mathrm{op}} \le d\cdot\max|s_i| = 64\cdot 2 = 128$ by Lemma 2.5 (loose bound; actual operator norm of a worst-case $\{-1,0,1,2\}$ element is smaller — recompute numerically, e.g. by maximizing $\|s\cdot y\|_\infty$ over the 256 extreme $y\in\{-1,1\}^{64}$ candidates or via LP).
- Per-instance folded bound: $\|\bar S\|_{\mathrm{op}}(d'+1+B+dk) \approx 128\cdot(32+1+1024+128) \approx 128\cdot 1185 \approx 151{,}680 < 2^{18}$; condition (28) demands $\|\bar S\|_{\mathrm{op}} L(d'+1+B+dk)\le B^2 = 2^{20}$, i.e. $\approx 455{,}040 \le 1{,}048{,}576$ — satisfied with slack ≈ 2.3×. (This is consistent with the paper's claim that the scheme "naturally extends to more flexible choices of B and L" — the slack can be traded.)
- $\Pi_{\mathrm{decomp}}$ then needs base-$B = 2^{10}$ digits: one decomposition round returns two halves of norm $< 2^{10}$.
- MSIS binding requirement: $2B^2 = 2^{21}$-bounded $(\bar S-\bar S)$-relaxed openings ⟹ MSIS$_{q,\kappa=9,n=2^{21},\,\beta\approx 2\cdot 2^{21}\cdot\|\bar S\|_{\mathrm{op}}\approx 2^{29}}$ — well inside the regime where 128-bit Module-SIS hardness estimates hold for a 128-bit $q$ and $\kappa = 9$ rows over $R_q$ (each row a dimension-64 module element).

### 6.6 Knowledge-error budget (concrete)

$\epsilon_{\mathrm{cm},k} = \frac{\mu + dk}{|\bar S|} + 3\epsilon_{\mathrm{bind}} + \epsilon'_{\mathrm{rg}} + \epsilon_{\mathrm{rg}} + 2\epsilon_{\mathrm{sum}} + \frac{\mu(\log^2\kappa + (2\log n)^2)}{|C|}$ with $\mu = 3+dk = 3+128 = 131$:
- $(\mu + dk)/|\bar S| = 259/2^{128}$ — negligible.
- $\epsilon_{\mathrm{sum}} = (2\log n/|C|)^2 = (2\cdot 21/2^{128})^2 = (42/2^{128})^2$.
- $\frac{\mu(\log^2\kappa + (2\log n)^2)}{|C|} = \frac{131\cdot(\log^2 9 + 441)}{2^{128}} \approx 131\cdot 450/2^{128}$ — negligible.
- Dominant terms are the recursive $\epsilon'_{\mathrm{rg}}, \epsilon_{\mathrm{rg}} \approx \epsilon_{\mathrm{mon},dk+1} = (2d + dk + 1 + 4\log n)/|C| + \epsilon_{\mathrm{bind}} \approx (128 + 129 + 1 + 84)/2^{128} + \epsilon_{\mathrm{bind}}$.
Total knowledge error per fold $\ll 2^{-100}$ for the concrete table — comfortable margin for $2^{\lambda=128}$ security after the $\times L$ of Theorem 5.2.

## 7. Parameters & Concrete Efficiency

### 7.1 Theorem 5.3 (asymptotic, with Remarks 4.6/4.7 optimizations; $d \gg \max(\kappa,\log n)$)

| Metric | Cost |
|---|---|
| Prover time | $Ln\kappa$ $R_q$-multiplications + $O(Ln\kappa dk)$ $R_q$-additions |
| Verifier time (excl. hashing) | $O(Ldk)$ $R_q$-multiplications |
| Online instance size | $(L-2)\cdot[(\kappa + 2n_{\mathrm{lin}})\log|R_q| + 2\log n\log|C|]$ bits |
| Accumulated instance size | $2\cdot[(\kappa+2n_{\mathrm{lin}})\log|R_q| + 2\log n\log|C|]$ bits |
| Folding proof size | $L(5\kappa+6)$ $R_q$-elements + $L(dk+5)$ $\bar S$-elements + $L(2dk+d+1)$ $C$-elements |

Breakdown of the per-input proof (Proof of Thm 5.3): 2 commitments $C_{M_f}, \mathrm{cm}_{m_\tau}$ (Step 1 of Constr. 5.1) + $dk+5$ folding challenges $(\mathbf s,\mathbf s')$ + $\mathrm{com}(\mathbf h)$ + 4 $R_q$-elements $\mathbf e[0..2], u$ + $(\mathbf v, a)\in C^{d+1}$ (Step 2 of Constr. 4.4) + Remark-4.7 items (2 commitments, 2 $R_q$-elements, $2dk$ $C$-elements); plus a fixed $8+2=10$ $R_q$-elements of $\mathbf e_o$-values.

### 7.2 Concrete parameter table (Section 5.3)

| $L$ | $q$ | $d$ | $n$ | $\bar S$ | $B$ | $k$ | $\kappa$ | FS hashes |
|---|---|---|---|---|---|---|---|---|
| 3 | 128-bit prime ($R_q$ splits into 16 factors) | 64 | $2^{21}$ | $\{-1,0,1,2\}^d$ | $2^{10}$ | 2 | 9 | ≲100 |

- Security target: 128-bit conjectured Module-SIS hardness (refs [APS15; Esg+19; ADPS16; BDGL16]).
- $n = 2^{21}$ proves R1CS statements over $\mathbb{F}_{q^4}$ of size $16\cdot2^{21} = 2^{25}$ (16 field constraints per $R_q$ constraint, footnote 17 / [BC24] Remark 4.1).
- Folding proof: < 200 KB plain, ≲100 KB with Remark 5.3 optimization (share one batch of helper commitments across the $L$ inputs → 5 commitments instead of $5L$).
- Recursive verifier dominated by Fiat-Shamir: ≲100 $R_q$-hashes; a 2-to-1 hash over $R_q$ costs >100 R1CS constraints over $R_q$ (Remark 4.7's motivation).
- $\bar S$-elements are cheap to represent: $d=64$ with coordinates in $\{-1,0,1,2\}$ → < $2d$ bits vs $d\log q$ (Remark 5.4).

### 7.3 Byte-level proof-size accounting (concrete table, $L=3$)

Sizes per element: $R_q$-element = $d\log q$ bits = $64\cdot128/8$ = 1024 B; $\bar S$-element < $2d$ bits = 16 B; $C$-element = $\log q$ bits = 16 B ($C=\mathbb{Z}_q$).

Per input ($\times L = 3$), with the Remark 4.7 optimization:
- $(5\kappa + 6) = 51$ $R_q$-elements ≈ 52 KB → ×3 ≈ 156 KB (this is the < 200 KB figure).
- $(dk + 5) = 133$ $\bar S$-elements ≈ 2.1 KB → ×3 ≈ 6.4 KB.
- $(2dk + d + 1) = 321$ $C$-elements ≈ 5.1 KB → ×3 ≈ 15.4 KB.
- Sumcheck messages themselves: $(\ell+1)\log n\cdot$(bytes/coeff) ≈ 3·21·16 B ≈ 1 KB per parallel execution — negligible.

With the Remark 5.3 shared-helper optimization, the $5L$ commitments collapse to 5, cutting the $R_q$-element count from $3\cdot 51$ to roughly $51 + 2\cdot 6$-ish → the ≲100 KB figure. The recursive verifier then Fiat-Shamir-hashes ≲100 $R_q$-blocks; at >100 constraints per 2-to-1 $R_q$ hash this is the entire circuit bottleneck (target ~10⁴ constraints).

### 7.4 Comparison vs LatticeFold [BC24]

| Metric | LatticeFold | LatticeFold+ |
|---|---|---|
| Prover | $O(Ln\kappa\log^2 B)$ $R_q$-mults (degree-4 sumcheck over $R_q$ + $L\log_2 B$ bit-decomposed commitments) | $\Omega(\log B)$× faster; ≈ $Ln\kappa$ $R_q$-mults + adds; est. **5×** faster |
| Verifier circuit | hashes $L\log_2 B$ decomposed commitments + $\Omega(\log^2 n)$ $R_q$-elements | ≲100 $R_q$-hashes |
| Proof size | $O_\lambda(\kappa d\log B + d\log n)$ bits | $O_\lambda(\kappa d + \log n)$ bits |
| Range proof | bit decomposition, committed per-bit | purely algebraic (monomial check + $\psi$ constant-term check), no bit commitments |
| vs HyperNova | ≈ equal prover time (Nethermind) | expected significantly faster + PQ |

Supporting datapoints: Ajtai hash ≈ 30× faster than Pedersen for ≈$2^{19}$ field elements [Net24]; LatticeFold+ prover time ≈ cost of committing to input witnesses only.

## 8. Implementation Notes

### 8.1 What to build on the `lzk` core engine

Reuse directly:
- **Ring $R_q$ with NTT** (`lzk` rings): needed for $R_q$-multiplications in $\mathrm{com}(\mathbf f) = \mathbf A\mathbf f$ ($n\kappa$ mults dominate). Choose $q \equiv 1+2e \pmod{4e}$, $e\in\{8,16\}$, with 2e-th root of unity for the incomplete NTT.
- **Ajtai/MSIS commitments**: $\mathrm{com}$, plus the *relaxed binding* semantics (track $(b, S)$-valid openings, differences of folding challenges). Random $\mathbf A\in R_q^{\kappa\times n}$ via seeded XOF (deterministic re-derivation keeps instances small).
- **Multilinear sumcheck over rings** (`lzk` sumcheck): all sumchecks here are degree-2 or degree-3 over the field $C$ (or $\mathbb{F}_{q^2}$), NOT over $R_q$ — implement the *batching* (Remark 2.5/2.6) and *two-parallel-executions* ($\mathcal{M}_C = C\times C$) modes. The ring-flavored part is only the MLE/tensor machinery with $R_q$-valued tables.
- **Tensor/LDE encodings**: $\mathrm{tensor}(\mathbf r)$, $\mathrm{eq}(\cdot,\cdot)$, $\tilde f$ evaluation identity $\tilde f(\mathbf r) = \langle\mathbf f,\mathrm{tensor}(\mathbf r)\rangle$; the 4-D tensor $\mathbf t^{(z)}$ of Eq. 19 must be evaluable lazily (mixed-product property) — implement as a Kronecker-product evaluator, never materialize the length-$n$ vector on the verifier side.
- **Fiat-Shamir transcripts**: strict ordering — every challenge derivation point listed in §5 must map to a domain-separated transcript absorb; the folding verifier circuit *is* the FS verifier, so transcript layout = circuit layout.

### 8.2 New modules required

1. **Monomial set / exp encoding** (`exp`, `EXP`): maps $a\mapsto \mathrm{sgn}(a)X^a$ with $X^{a}$ for negative $a$ realized as $X^{a+d}$ (since $X^d = -1$). Careful: $\mathrm{EXP}(0) = \{0,1,X^{d/2}\}$ — when the prover picks $m_\tau$ it uses $\exp$ ($0\mapsto 0$); soundness tolerates the other two options.
2. **$\psi$ and constant-term checks**: $\psi$ is a fixed public ring element with the triangular pattern; $\mathrm{ct}(\psi\cdot b)$ is $O(d)$ schoolbook (only coefficient $0$ of the product matters: $\mathrm{ct}(\psi\cdot b) = \sum_i \psi_i b_{-i \bmod d}$ with sign twists). Implement `ct_mul(psi, b)`.
3. **Gadget machinery**: signed base-$b$ decomposition $G^{-1}_{b,k}$ (footnote 3: digits of $|x|$, sign flipped for negative $x$); recombination $G_{b,k}$; the special matrix forms $G^\top_{B,\hat\ell}$ (R1CS) and $G_{d',k}$ (range).
4. **split / pow** (Construction 4.1 + Remark 4.5): reshape $\tau\in(-d',d')^n$ as $T\in\mathbb{Z}^{\kappa\times dk\times d\times \ell}$ with the exact stride $i(d^2k\ell) + j(d\ell) + o\ell + p$; `pow` computes $\mathrm{pow}(\tau)_{i,j} = \sum_{o,p} T_{i,j,o,p}(d')^o X^p$ — implement as tensor contraction.
5. **Double commitment** $\mathrm{dcom}$: pipeline gadget-decompose($\mathrm{com}(M)$) → flatten → coefficient-flatten → pad → $\mathrm{com}(\tau)$.
6. **Ring-evaluation maps** $\mathrm{ev}_a(\beta)$: $\sum_i a_i\beta^i$ over $\mathbb{F}_{q^u}$; needed for $\Pi_{\mathrm{mon}}$. For 128-bit $q$: $u=1$ ($\beta\in\mathbb{Z}_q$). For small $q$: extension field arithmetic ($\mathbb{F}_{q^2}$) — reuse `lzk` GF tower code where applicable, else polynomial basis mod an irreducible degree-$u$ poly.

### 8.3 Algorithms & complexity (honest prover, per folding step, per input instance)

- $\mathrm{com}(\mathbf f)$: $n\kappa$ $R_q$-mults → NTT-based, $O(n\kappa d\log d)$ $\mathbb{Z}_q$-ops.
- $\mathrm{com}(M_f)$ ($M_f\in\mathcal{M}^{n\times dk}$): **no multiplications** — column sums of rotated/flipped $\mathbf A$ columns: $n\kappa dk$ $R_q$-adds. Represent monomial columns by exponent vectors; rotate = index shift with sign on wraparound.
- $\mathrm{com}(\tau_D)$: $\tau_D\in\mathbb{Z}_q^n$ small — only scalar mults by small constants; or treat as gadget-style sparse commitment.
- $e_j = \langle M_{*,j},\mathrm{tensor}(\mathbf r)\rangle$: $O(n)$ mults for $\mathrm{tensor}(\mathbf r)$ once + $O(nm)$ adds via the exponent-accumulate trick (Remark 4.3.2).
- Sumchecks: degree-2/3 over field $C$, size $n$; all batched into ONE sumcheck per parallel execution; two parallel executions with independent challenges ($\mathbf r_o\in(C\times C)^{\log n}$). Prover $O(n)$ per round pair with the standard MLE-with-bookkeeping; total $O(n)$ field mults — negligible vs commitments.
- $\mathbf h = M_f\mathbf s'$: $n\cdot dk$ $R_q$-mults?? — no: $\mathbf h_i = \sum_j (M_f)_{i,j}s'_j$ where $(M_f)_{i,j}$ are monomials, so it is again $n\,dk$ monomial-scalar mults (rotation + small scalar), i.e. adds and shifts only. $\mathrm{com}(\mathbf h)$ comes free: $\mathrm{com}(\mathbf h) = \mathrm{com}(M_f)\mathbf s'$ ($\kappa\,dk$ $R_q$-mults on the already-computed commitment).
- $\Pi_{\mathrm{decomp}}$: base-$B$ split of $\mathbf f$ + 2 fresh commitments (the $O(Ln\kappa dk)$ add-term in Thm 5.3 covers "two decomposed commitments").

### 8.4 Data structures

- Ring element: int64/int128 signed-coefficient array of length $d$ (128-bit $q$ needs 128-bit limbs or lazy reduction); NTT form cached for commitments.
- Monomial matrix $M_f$: store as `uint8` exponent array $E\in[0,d)^{n\times dk}$ + sign bits; materialize lazily.
- Transcript: append-only bytes; challenges derived by domain-separated hashing with public labels (`"c"`, `"beta"`, `"r"`, `"s"`, `"s'"`, `"c0"`, `"c1"`, `"r_o"`, `"alpha"`).
- Accumulator state: $(\mathrm{cm}, \mathbf r, \mathbf v)$ pairs ×2 + witness side $(\mathbf f_{\mathrm{acc}}, \tau, \dots)$ kept by prover only.

### 8.5 Pitfalls & edge cases

1. **Monomial lemma only over $\mathbb{Z}_q[X]$/extension fields, never $R_q$** (Remark 2.1): the honest verifier check Eq. 12 uses $\mathrm{ev}_{e_j}(\beta)$ in $\mathbb{F}_{q^u}$. Do NOT implement the squaring test on $R_q$ representatives.
2. **Two parallel sumchecks are load-bearing** (Remark 4.9): union bound over $\mu|\bar S|$ extractor calls; a single execution makes $\epsilon_2$ meaningless. Keep the $(C\times C)$ challenge structure and independent randomness.
3. **Challenge ordering / adaptivity**: $\mathrm{com}(\mathbf h)$ must be sent AFTER $\mathbf s'$ (that's the security trick — $\mathbf A$ 's binding is recovered through the Eq. 20/21 sumcheck tying $\mathrm{com}(\mathbf h)$ to the pre-committed $C_{M_f}$). In Fiat-Shamir this ordering is enforced by transcript position.
4. **Sign conventions in gadgets**: footnote-3 decomposition flips ALL digits' signs for negative $x$; mixing this with two's-complement or balanced representations breaks $M'G = M$.
5. **$\mathrm{pow}\neq\mathrm{split}^{-1}$**: valid openings $(\tau, M)$ only require $\mathrm{pow}(\tau) = \mathrm{com}(M)$; tests must not assume $\tau = \mathrm{split}(\mathrm{com}(M))$.
6. **$\mathrm{EXP}(0)$ ambiguity**: verifier-side Lemma 2.2 argument covers all three elements; prover should use $\exp$ (canonical) but tests for the relation should accept $\{0,1,X^{d/2}\}$ at zero entries.
7. **$n$ padding**: $\mathrm{split}$ zero-pads to $n$; ensure $\kappa m d\ell\le n$ (or implement Remark 4.8's nested-split variant with $d^*=\sqrt d$ and 4 helper commitments).
8. **Eq. 28 norm budget**: $\|\bar S\|_{\mathrm{op}} L(d'+1+B+dk) \le B^2$ must be checked at setup; with the concrete table ($\bar S = \{-1,0,1,2\}^d$: $\|\bar S\|_{\mathrm{op}}\le d\cdot 2$ by Lemma 2.5 — the paper's parameter choice relies on tighter actual operator norms; recompute numerically).
9. **Folding verbatim vs delayed decomposition** (Remark 5.2): for small $L$ the realized folded norm is $\ll B^2$; skipping or weakening $\Pi_{\mathrm{decomp}}$ is legitimate but must track the true bound $\bar b$ into the next step's $b$.
10. **Zero-knowledge**: NOT addressed — the folding transcript leaks $\mathbf g$-correlated data; final SNARK proof must wrap the terminal accumulator instance in a ZK layer (as in Nova-style pipelines); the paper is silent, so treat all folding proofs as public-coins non-ZK.
11. **$R_q$ splits**: with $e=16$, differences of $\bar S$-elements are invertible only under the small-coefficient condition (Lemma 2.4); assert at setup for the actual $\bar S$ chosen.
12. **Verifier's tensor evaluations**: $\mathrm{eq}(\mathbf r,\mathbf r_o)$, $t_g^{(z)}(\mathbf r_o^{(i)})$ must be computed in $O(\mathrm{polylog})$ via mixed-product; a naive length-$n$ expansion blows the "simple verifier circuit" claim.

### 8.6 Small-modulus instantiation (Appendix B) — engineering recipe

When $q$ is 64-bit (or smaller), set $C := \mathbb{F}_{q^2}$ (a $\mathbb{Z}_q$-vector space of dimension 2) and keep $\bar S\subseteq R_q$:

1. **All sumchecks run over $K = \mathbb{F}_{q^t}$** ($t=2$ for 128-bit security):
   - Eq. 11 over $K$: $\mathrm{eq}(\mathbf c,\langle i\rangle)$ and $\mathbf m_g^{(j)}(\langle i\rangle)$ interpreted as $K$-elements via the column interpretation.
   - Eq. 18: inner products between $R_q$-vectors and $K$-vectors → coefficient-wise $\mathbb{Z}_q$/$K$ claims → single $K$-sumcheck by random combiner.
   - Eq. 20: LHS becomes $d$ claims over $K$ → one claim; $\mathbf t^{(z)}\in E^n$ interpreted as an $E$-vector, $E = K\otimes_{\mathbb{F}_q}R_q$.
2. **Folding stays over $R_q$**: after sumchecks, evaluation claims are inner products between committed $R_q$-vectors and a *shared* $K$-vector; by the row interpretation each splits into $t$ claims against identical $\mathbb{Z}_q$-vectors — fold the committed vectors with challenges in $\bar S\subseteq R_q$, then recombine the $t$ claims into one $K$-evaluation (column interpretation).
3. **Data structure**: represent $E$-elements as $t\times d$ matrices over $\mathbb{Z}_q$; implement the two interpretations as `mul_col(a_K, b_R)` and `mul_row(a_R, b_K)` and assert consistency in tests.
4. **Cost implication**: a sumcheck over $\mathbb{F}_{q^2}$ for a size-$n$ statement is cheaper than one module-Ajtai commitment over $R_q$ whenever $d \gg 2$ — the paper's stated regime — so small-$q$ variants are prover-favorable, matching Neo [NS25].

### 8.7 Fiat-Shamir transcript layout (folding step, non-interactive form)

One folding step's non-interactive transcript, in exact absorb order (all challenges derived from a running hash over labeled fields):

1. Absorb public input: $\mathbf A$-seed, $(M^{(i)})$, the $L$ instances $(\mathrm{cm}_{\mathbf f_i}, \mathbf r_i, \mathbf v_i)$.
2. For the linearization sumcheck (Fig. 1, applied to each online instance): absorb prover's claimed $s$ values → derive $\mathbf r$ → absorb round messages $g_1,\dots,g_{\log n}$ (interleaved: absorb $g_i$, derive $\rho_i$) → derive $\mathbf r_o$ → absorb $(v, v_A, v_B, v_C)$.
3. For each input's helper commitments: absorb $C_{M_f}, \mathrm{cm}_{m_\tau}$.
4. $\Pi_{\mathrm{rgchk}}$ internals: derive $\mathbf c, \beta$ (monomial challenges) → absorb batched sumcheck rounds + combiner $\alpha$ → derive $\mathbf r$ → absorb $\mathbf e$ (or the Remark 4.7 compressed $\mathrm{com}(\tau_e), v_e, v'_e$) → absorb $(\mathbf v, a)$.
5. $\Pi_{\mathrm{cm}}$ internals: derive folding challenges $\mathbf s\in\bar S^3, \mathbf s'\in\bar S^{dk}$ → absorb $\mathrm{com}(\mathbf h)$ → derive $(\mathbf c^{(0)},\mathbf c^{(1)})$ → absorb the paired-execution sumcheck rounds → derive $\mathbf r_o\in(C\times C)^{\log n}$ → absorb $\mathbf e_o$.
6. Verifier (circuit) computes $\mathrm{cm}_\mathbf g, \mathbf v_o$; output accumulator instance $(\mathrm{cm}_\mathbf g, \mathbf r_o, \mathbf v_o)$; prover stores $\mathbf g$.
7. $\Pi_{\mathrm{decomp}}$: absorb $C, \mathbf v^{(0)}, \mathbf v^{(1)}$ → output the 2-instance accumulator.

Every "derive" point is a distinct challenge; the ordering of Steps 3–5 encodes the adaptive sequencing ($\mathrm{com}(\mathbf h)$ strictly after $\mathbf s'$). A wrong order silently breaks knowledge soundness (the extractor's mental-experiment uniformity argument).

### 8.8 Relation to the shared `lzk` core engine — module map

| `lzk` module | LatticeFold+ consumer |
|---|---|
| `rings.ZqX` (NTT, $X^d+1$) | $R_q$ arithmetic for $\mathrm{com}$, $\psi$-products, $\mathbf h$-folding |
| `fields.GF tower` | $\mathbb{F}_{q^2}$ sumcheck challenges (small-$q$ variant), $\mathbb{F}_{q^u}$ for $\mathrm{ev}_a(\beta)$ |
| `commit.ajtai` | $\mathrm{com}$, $(b,S)$-relaxed binding bookkeeping |
| `sumcheck.multilinear` | all degree-2/3 sumchecks (batched + paired modes) |
| `sumcheck.ring_norm` (RingSC) | §5.0 layer: monomial-check + tensor-consistency + $\mathrm{ct}(\psi\cdot b)$ closure |
| `encoding.tensor_lde` | $\mathrm{tensor}(\cdot)$, $\mathrm{eq}$, $\tilde f$ identity, 4-D lazy tensor $t^{(z)}_g$ |
| `transcript.fiat_shamir` | §8.7 layout, domain-separated labels |
| new: `gadget.split_pow` | Construction 4.1, Remark 4.5 stride contract |
| new: `monomial.exp` | $\exp$/EXP, $\mathrm{ev}$, monomial-column commitment |

### 8.9 Complexity summary for the honest prover (end-to-end per folding step)

- $L\cdot n\kappa$ $R_q$-mults (dominant; the $L-2$ fresh $\mathrm{com}(\mathbf f_i)$ plus decomposed commitments) — NTT-accelerable.
- $O(Ln\kappa dk)$ $R_q$-adds (monomial-column commitments $\mathrm{com}(M_f)$, rotations of $\mathbf A$) — embarrassingly parallel, SIMD-friendly.
- $O(L\cdot n)$ field mults for all sumchecks combined (batched!) — negligible.
- $O(L\kappa dk)$ $R_q$-mults for $\mathrm{com}(\mathbf h) = \mathrm{com}(M_f)\mathbf s'$.
- Memory: the $\mathbf A$ matrix ($\kappa n$ ring elements = $9\cdot 2^{21}\cdot 1$ KB ≈ 18 GB at 128-bit $q$, 64-bit $d$!) — **stream $\mathbf A$ from a PRG seed**; witness-side storage $O(n\,dk)$ monomial exponents ($n\,dk$ bytes ≈ 32 MB) + $O(n)$ ring elements per instance.

### 8.10 Test vectors to construct

- Lemma 2.2 round trip: for all $a\in(-d',d')$ and all $b\in\mathrm{EXP}(a)$: $\mathrm{ct}(\psi\cdot b) = a$; and for $b\in\mathcal{M}$, $a = \mathrm{ct}(\psi\cdot b)\Rightarrow a\in(-d',d')\wedge b\in\mathrm{EXP}(a)$ (exhaustive over $d=8,16$).
- Corollary 4.1 statistics: random $\beta$, non-monomial $a$ passes with freq $\to 2d/|\mathbb{F}_{q^u}|$.
- Construction 4.1: $\mathrm{pow}(\mathrm{split}(D)) = D$ for random $D\in R_q^{\kappa\times dk}$; injectivity on random pairs.
- End-to-end: R1CS instance (small $n = 2^8$, $d=64$, toy $q$) through Fig. 1 → $\Pi_{\mathrm{mlin}}$ ($L=3$) → $\Pi_{\mathrm{decomp}}$, assert accumulator relation holds and norms track $B \to B^2 \to B$.
- Soundness spot checks: corrupt one coefficient of $\mathbf f$ beyond range → Eq. 16 must fail for random $\mathbf r$; corrupt one monomial in $M_f$ → Eq. 12 fails.
- Aggregate equivalence: the folded claim $\langle M^{(\ell)}\mathbf f_{\mathrm{fold}},\mathrm{tensor}(\mathbf r_o)\rangle = \mathbf v_{\mathrm{fold}}$ must hold with the same $\mathbf r_o$ for all $\ell\in[n_{\mathrm{lin}}]$ — catches sign errors in the $\mathbf e_o$ bookkeeping.

## 9. Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- ✅ The sumcheck layer (§5.0) — the shared RingSC engine implements the
  generic ring sumcheck exactly (coefficient-form round messages,
  g(0)+g(1) checks, Horner running claims, bind recursion, the
  two-parallel-execution and batching modes via explicit combiners).
- ✅ Construction 5.1 folding (fold + linear constraint folding + cross-term
  tracking) and the norm-check composition (Π_rgchk → Π_cm norm path).
- ✅ The range-check instantiation (Construction 4.4 style): base-b digit
  decomposition with recomposition checks + degree-2/3 monomial sumchecks.
- □ Not implemented: the double-commitment split map (Construction 4.1),
  the full EXP(D_f) monomial-set machinery, ZK masking, the R1CS→R_lin
  reduction of Figure 1 (Appendix A chain documented in the spec).

**(replacing the placeholder)**

- DONE: the sumcheck layer (5.0) — the shared RingSC engine implements the generic ring sumcheck exactly (coefficient-form round messages, g(0)+g(1) checks, Horner running claims, bind recursion, the two-parallel-execution and batching modes via explicit combiners).
- DONE: Construction 5.1 folding (fold + linear constraint folding + cross-term tracking) and the norm-check composition (the Pi_rgchk -> Pi_cm norm path).
- DONE: the range-check instantiation (Construction 4.4 style): base-b digit decomposition with recomposition checks + degree-2/3 monomial sumchecks.
- NOT implemented: the double-commitment split map (Construction 4.1), the full EXP(D_f) monomial-set machinery, ZK masking, the R1CS-to-R_lin reduction of Figure 1 (Appendix A chain documented in the spec).
