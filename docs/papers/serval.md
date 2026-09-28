# Serval: Slack-Free ℓ2-Sound Polynomial Commitments from Lattices — Deep Analysis & Implementation Spec

> Source: `papers_txt/serval.txt` (Zhang, Chow, Gao, Xiao; ~2.3k extracted lines, read in full).
> All figure/lemma/theorem/table/equation numbers are cross-referenced to the paper.
> Prototype: gitlab.com/LatticePCSReview/servalPCS (Apple M2 baseline, no LaBRADOR
> compaction integrated). This doc is implementation-grade for the `lzk` engine waves.

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Serval: Slack-Free ℓ2-Sound Polynomial Commitments from Lattices (Serval = **S**lack-free **E**uclidean **R**adius **V**erification for **A**lgebraic **L**attices) |
| **Authors** | Lizhen Zhang¹, Sherman S. M. Chow², Shang Gao¹, Bin Xiao¹ (¹ PolyU HK, ² CUHK) |
| **Group** | Same PolyU HK group as HyperWolf, Quasar |
| **Primitive** | Lattice (module) PCS for univariate and multilinear polynomials over $\mathbb Z_q$, transparent setup |
| **Assumption** | Standard M-SIS$_{\kappa,n,q,\beta}$ (Def. 1) + ROM for Fiat–Shamir; **explicitly not** k-SIS or SIS-with-hints (BASIS) |
| **Headline norm guarantee** | **Slack-free ℓ2 soundness**: extractor outputs $\vec f$ with $\lVert\vec f\rVert_2\le B$ — the *same* bound as the relation, multiplicative slack $\alpha=1$ (vs $\approx2$ for Cini et al./Greyhound, poly$(L)$ for SLAP/Fenzi et al.) |
| **Concrete sizes** (128-bit, optimized) | $L=2^{15}$: 259.16 KB; $2^{16}$: 302.88 KB; $2^{17}$: 337.03 KB; $2^{18}$: 385.22 KB; $2^{19}$: 423.03 KB; $2^{20}$: 436.03 KB; $2^{22}$: 1.97 MB; $2^{24}$: 2.24 MB; $2^{26}$: 2.73 MB; $2^{28}$: 3.15 MB; $2^{30}$: 3.59 MB. At $L=2^{20}$: **8× smaller than Fenzi et al. (JoC '24, 3.4 MB→36.5 MB class) and 85× smaller than SLAP**; larger than Greyhound (46–53 KB) but **faster verifier at large $L$** |
| **Asymptotics** | Proof $O(\lambda^2\log^2N)$ bits (with $\ell=\lceil\log q\rceil$, $t\cdot\log q=O(\lambda)$); prover $O(N\lambda)$ ring ops (linear); verifier $O(\log N\cdot\mathrm{poly}(\lambda))$ ring ops |

**Key contributions:**

1. **Slack-free ℓ2 extraction** under standard M-SIS by the Lyubashevsky–Nguyen–
   Plançon (Crypto '22) norm-proof paradigm: quadratic **self-inner-product** claim
   $\mathrm{ct}\langle\vec f,\sigma^{-1}(\vec f)\rangle=b\bmod q$ **plus** an exact
   coefficient-set (binary) constraint that rules out modular wraparound — the
   integer squared norm equals its residue, so a range check $0\le b\le B^2$ is exact.
2. **One split-and-fold engine for everything**: commitment consistency (leveled
   Ajtai), tensor-structured linear (evaluation) constraints, the quadratic norm
   relation, **and the binarity check itself** (rewritten as an inner-product-shaped
   constraint $\langle\vec\alpha\circ\vec s,\vec s\rangle=\langle\vec\alpha,\vec s\rangle$)
   all share the same $\log N$-round divide-and-conquer recursion with a shared
   per-round challenge.
3. **GSW-style unsigned base-2 decomposition** ($\ell=\lceil\log q\rceil$) of the
   coefficient vector into a binary witness — slightly larger witness than Greyhound's
   larger-base choice, but binarity gives the exact $\ell_\infty$ pin needed for
   slack-freeness and unifies all sub-proofs.
4. **Proof compaction** via Fiat–Shamir + LaBRADOR: encode all verifier checks of the
   $\log N$-round transcript as one LaBRADOR quadratic dot-product relation
   ($O(\log\log M)$ ring elements, $M=O(\lambda\log N)$).
5. Batching: multiple polys @ single point (random linear combination), single poly @
   multiple points (sum-check with $\widetilde{\mathrm{eq}}$), multiple @ multiple.

**What "slack-free ℓ2-sound" means precisely.** A lattice PCS is $\ell_2$-sound with
slack $\alpha\ge1$ if the extractor only guarantees $\lVert\vec f\rVert_2\le\alpha B$
for the committed short object. Serval achieves $\alpha=1$: the extracted witness
satisfies the *prescribed* bound $B$ exactly. Mechanism (Lemma 2):

- binary coefficients ⇒ $\lVert\vec f\rVert_\infty=1$ ⇒ $|\vec f|^2\le N\ell d$;
- $q>2N\ell d$ ⇒ the centered representative of
  $\mathrm{ct}\langle\vec f,\sigma^{-1}(\vec f)\rangle\in\mathbb Z_q$ equals the integer
  $|\vec f|^2$ (no wraparound);
- hence proving $0\le b\le B^2$ *modularly* yields the integer statement
  $|\vec f|^2\le B^2$, i.e. $\lVert\vec f\rVert_2\le B$ — **no approximation, no
  repetition-induced slack, no JL-projection factor**.

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter (128 in the instantiation) |
| $L$ | PCS size parameter: $L=D{+}1$ univariate degree-$D$; $L=2^n$ for $n$-variate multilinear |
| $N$ | number of ring elements in the packed witness; $N\cdot d=L$ |
| $d$ | ring dimension (power of two); concrete 64 |
| $q$ | prime modulus, $q\equiv5\pmod 8$ (invertibility regime of Lemma 1); concrete $\log q\in[84,128]$ bits per $N$ |
| $\mathbb Z_q$, $R$, $R_q$ | $\mathbb Z/q\mathbb Z$ (centered representatives $[-\frac{q-1}2,\frac{q-1}2]$); $\mathbb Z[X]/(X^d{+}1)$; $\mathbb Z_q[X]/(X^d{+}1)$ |
| $[n]$, $[a{:}b]$ | $\{0,\dots,n{-}1\}$, $\{a,\dots,b{-}1\}$ |
| $\mathrm{ct}(f)$, $\mathrm{coef}(f)$ | constant term $f_0$; coefficient vector $(f_0,\dots,f_{d-1})$ |
| $\sigma^{-1}$ | conjugation automorphism $\sigma^{-1}(X)=X^{-1}$ in $R_q$; $\sigma^{-1}(f)=\sum f_iX^{-i}$; multiplicative: $\sigma^{-1}(ab)=\sigma^{-1}(a)\sigma^{-1}(b)$ |
| $\langle\vec a,\vec b\rangle$ | coefficient inner product $=\mathrm{ct}\langle\vec a,\sigma^{-1}(\vec b)\rangle$ over $R_q^n$ (§2.1 identity) |
| $\lVert\cdot\rVert_1,\lVert\cdot\rVert_2,\lVert\cdot\rVert_\infty$ | norms over centered coefficients; $\lVert\vec f\rVert_\infty\le\lVert\vec f\rVert_2\le\sqrt{md}\lVert\vec f\rVert_\infty$ for $\vec f\in R_q^m$; default $\lVert\cdot\rVert=\lVert\cdot\rVert_2$ |
| $\mathcal C\subset R_q$ | challenge space: all distinct $c,c'\in\mathcal C$ have $c-c'$ invertible; $\lVert c\rVert\le\tau$, $\lVert c\rVert_{\mathrm{op},\infty}\le T$ |
| $\lVert c\rVert_{\mathrm{op},\infty}$ | $\sup_{v\ne0}\lVert cv\rVert_\infty/\lVert v\rVert_\infty$; for the concrete alphabet $=\lVert c\rVert_1$ (Young's inequality, negacyclic convolution) |
| $\tau,T$ | challenge $\ell_2$ / operator-norm bounds; concrete $T=48$ (and $T=9$ variant with $\{0,\pm1\}$ challenges + 2× parallel repetition for ≥90-bit) |
| $\vec g_a$, $\iota:=\lceil\log_aq\rceil$ | gadget vector $(1,a,a^2,\dots,a^{\iota-1})$; decomposition length in base $a$ |
| $G_{a,m}$, $G^{-1}_{a,m}(\cdot)$ | gadget matrix $I_m\otimes\vec g_a^T\in\mathbb Z_q^{m\times m\iota}$; base-$a$ gadget decomposition operator (entry-wise over $R_q$) |
| $\sigma,\iota$ / $\sigma_\alpha,\iota_\alpha$ | decomposition base & pieces for inner commitments / for the larger-norm $\vec s_\alpha$; concrete $\iota=5$ (8 at $e=20$) |
| $\ell:=\lceil\log q\rceil$ | base-2 decomposition expansion factor of the witness (GSW-style unsigned) |
| $\kappa$ | height (rank) of commitment matrices $A_i,B_i$; concrete 13 |
| $A_i\in R_q^{\kappa\times2^i\kappa}$, $A_0\in R_q^{\kappa\times2\ell}$ | leveled commitment matrices ($i\in[1,\log N]$) |
| $B_i\in R_q^{\kappa\times2^i\kappa}$, $B_0\in R_q^{\kappa\times2\ell\iota_\alpha}$ | auxiliary (binary-proof) commitment matrices |
| $\vec s\in R_q^{N\ell}$ | the binary PCS witness: $\mathrm{coef}(\vec s)\in\{0,1\}^{N\ell d}$, $\mathrm{Com}(\vec s)=\mathrm{cm}$ |
| $\mathrm{cm}$, $\mathrm{cm}_{\mathrm{min},i}$ | top commitment; intermediate commitments (private prover state), $\mathrm{cm}_{\mathrm{min},i}\in R_q^{2^{i+1}\kappa}$... (level-dependent) |
| $n_i:=N/2^{i+1}$ | witness half-length bookkeeping at level $i$ |
| $F:\mathbb F^m\times\mathbb F^n\to\mathbb F$ | (Quasar-side; not used in Serval) |
| $v,b,\beta$ | linear-constraint output value; quadratic self-IP value; norm bound $\beta$ with statement check $0\le b\le\beta^2$ |
| $\vec a_i\in\mathbb Z_q^{b_i}$, $b_i$ | public tensor factors of the evaluation vector; $b_0=2\ell d$, $b_i=2$ for $i\in[1:\log N]$ |
| $\vec a_0\in R_q^{2\ell}$ | packed base tensor factor (eval weights incl. base-2 powers) |
| $\vec c_i=(c_{i,0},c_{i,1})\in\mathcal C^2$ | per-round folding challenge pair |
| $\vec c_i^{(\mathrm{qua})}$ | quadratic fold vector $(c_{i,0}\sigma^{-1}(c_{i,0}),\,c_{i,1}\sigma^{-1}(c_{i,1}),\,c_{i,0}\sigma^{-1}(c_{i,1}),\,c_{i,1}\sigma^{-1}(c_{i,0}))$ |
| $L_i,M_i^{(1)},M_i^{(2)},R_i$ | quadratic sub-claim quartet: $\langle\vec s_L,\sigma^{-1}(\vec s_L)\rangle$, cross terms, $\langle\vec s_R,\sigma^{-1}(\vec s_R)\rangle$ |
| $\pi_i^{(\mathrm{cm})},\pi_i^{(\mathrm{lin})},\pi_i^{(\mathrm{qua})},\pi_i^{(\mathrm{bin})}$ | per-round sub-proof messages |
| $\alpha\in\mathbb Z_q$, $\vec\alpha$ | binarity randomizer; $\vec\alpha:=(1,\alpha,\dots,\alpha^{N\ell d-1})$ with tensor split $\vec\alpha=\bigotimes_{i=0}^{\log N-1}\vec\alpha_i$, $\vec\alpha_0=(1,\alpha,\dots,\alpha^{2\ell d-1})$, $\vec\alpha_i=(1,\alpha^{2^i\cdot2\ell d})$ |
| $\vec s_\alpha=\vec s\circ\vec\alpha$ | randomized witness (coefficient-wise), embedded into $R_q^{N\ell}$ |
| $\hat s_\alpha\in R_q^{N\ell\iota_\alpha}$ | gadget decomposition of $\vec s_\alpha$ in base $\sigma_\alpha$: $G_{\sigma_\alpha,N\ell}\hat s_\alpha=\vec s_\alpha$ |
| $\mathrm{cm}_\alpha$ | commitment to $\hat s_\alpha$ (with $B$ matrices) |
| $r\in\mathbb Z_q$, $\vec r,\vec r_\alpha$ | well-formedness challenge; $\vec r:=(1,r,\dots,r^{N\ell d-1})$; $\vec r_\alpha:=\vec r\circ\vec\alpha$ (both tensor-decomposed like $\vec\alpha$) |
| $v_\alpha,v_r,v_{r\alpha}$ | $v_\alpha=\langle\vec\alpha,\vec s\rangle$; $v_r=\langle\vec s_\alpha,\vec r\rangle$; $v_{r\alpha}=\langle\vec s,\vec r_\alpha\rangle$; check $v_r=v_{r\alpha}$ |
| $t:=\lambda/\lceil\log q/(2N\ell d)\rceil$ | binary-check repetitions (fresh $\alpha$'s); $t\cdot\log q=O(\lambda)$, $t=\Theta(\lambda\log\lambda/\log^2N)$ |
| $\gamma_{\log N}=(2T)^{\log N-1}$, $\gamma_{\alpha,\log N}=\frac{\sigma_\alpha}{2}(2T)^{\log N-1}$ | final folded $\ell_\infty$ bounds |
| $\gamma=\sqrt{2\ell d}\,\gamma_{\log N}$, $\gamma_\alpha=\sqrt{2\ell\iota_\alpha d}\,\gamma_{\alpha,\log N}$ | final-round $\ell_2$ admissibility bounds |
| $\beta_{\text{M-SIS}}\ge\max\big(\sqrt N\cdot N\ell\gamma_{\log N},\ \sqrt N\cdot N\ell\iota_\alpha\gamma_{\alpha,\log N}\big)$ | M-SIS norm bound required by the reduction (Eq. 4) |
| $\delta$, $b_k$ | root-Hermite factor; BKZ block size $b_k=O(\lambda)$; M-SIS hard iff $\beta_{\text{M-SIS}}\le\min(2^{2\sqrt{d\log q\log\delta}}\ ...,\ q)$ heuristic |
| $w_0,w_1,w_2$ | challenge pool profile: $w_1$ coefficients $\pm1$, $w_2$ coefficients $\pm2$, rest 0; concrete $(w_0,w_1,w_2)=(24,32,8)$, $d=64$ |
| $\mathcal P_{w_0,w_1,w_2}$ | challenge pool; $\lvert\mathcal P_w\rvert=\binom d{w_1}\binom{d-w_1}{w_2}2^{w_1+w_2}$; $|\mathcal C|\approx2^\lambda$ |
| $R_{\mathrm{Lab}}$ | LaBRADOR relation (Eq. 1): quadratic dot products $f=\sum\alpha_{i,j}\langle\vec z_i,\vec z_j\rangle+\sum\langle\vec\varphi_i,\vec z_i\rangle-b$ with $\mathrm{ct}$-only $F'$ part and $\sum\lVert\vec z_i\rVert_2^2\le\beta^2$ |
| $r,n$ (LaBRADOR) | LaBRADOR block count with $r=N^{1/3}$, $n=N^{2/3}$, proof $O(\log\log N)$ |
| $M$ | total ring elements in the compacted LaBRADOR witness: $\Theta((t{+}1)\log N)+\Theta(t\ell\log\gamma_\alpha)+\ell\log\gamma=O(\lambda\log N)$ |
| $\mu_i,\rho_i$ | FS challenge seed hash $H(\mathrm{Com}(\mathrm{tr}_{i-1}))$; PRG expansion |
| $W$ | concatenated witness blocks for LaBRADOR compaction |
| $\epsilon_{\mathrm{se}},\epsilon_{\mathrm{fs}},\epsilon_{\mathrm{La}}$ | soundness error components of the composed scheme (Theorem 7) |
| $\vec u_{\mathrm{uni}},\vec u_{\mathrm{mul}}$ | evaluation vectors: $(1,u,\dots,u^{Nd-1})$; MLE tensor $\bigotimes_j(1,u_j)$ |
| $\vec f\in R_q^N$ | packed polynomial: $\vec f=(\sum_i f_iX^i,\sum_i f_{i+d}X^i,\dots)$ |

## 3. Algebraic Setting

### 3.1 Ring and norms

$R_q=\mathbb Z_q[X]/(X^d+1)$, $d$ a power of two, $q$ prime with $q\equiv5\pmod8$.
Coefficient embeddings: $\mathrm{ct}(f)=f_0$, $\mathrm{coef}(f)=(f_0..f_{d-1})$.
Norms over centered representatives. Ring vectors: concatenation $(\vec f,\vec g)\in
R_q^{2n}$; $\lVert\vec f\rVert_\infty\le\lVert\vec f\rVert_2\le\sqrt{md}\lVert\vec
f\rVert_\infty$.

**Conjugation identity (§2.1):** for $\vec a,\vec b\in R_q^n$ with coefficient
representations,
$\langle\vec a,\vec b\rangle=\mathrm{ct}\langle\vec a,\sigma^{-1}(\vec b)\rangle$ —
this is the bridge that turns *coefficient* inner products into *ring* inner products,
and it is why every constraint (linear, quadratic, binary) can be given the same
$\mathrm{ct}\langle\cdot,\sigma^{-1}(\cdot)\rangle$ shape.

**Invertibility (Lemma 1, Lyubashevsky–Seiler):** $d$ power of two, $q\equiv5\bmod8$ ⇒
any $f\in R_q$ with $0<\lVert f\rVert_2<\sqrt{q/2}$ is invertible. Used to guarantee
$c-c'$ invertible for distinct challenges.

### 3.2 Challenge space

$\mathcal C\subset R_q$ with (i) $c-c'$ invertible for distinct elements, (ii)
$\lVert c\rVert\le\tau$, (iii) $\lVert c\rVert_{\mathrm{op},\infty}\le T$. Concrete pool
$\mathcal P_{w_0,w_1,w_2}$: coefficients in $\{0,\pm1,\pm2\}$ with exactly $w_1$ of
magnitude 1 and $w_2$ of magnitude 2. For distinct $c,c'$:
$0<\lVert c-c'\rVert_2\le\sqrt{4w_1+2w_2}$... (each of the $\le w_1+w_2$ nonzero
coefficients lands in $\{0,\pm1,\pm2,\pm3,\pm4\}$, bound $4\sqrt{2w_1+2w_2}<\sqrt{q/2}$
iff $q>64(w_1+w_2)$). Bounds $\tau=T=\sqrt{w_1+2w_2}$ (also $\lVert c\rVert_1=w_1+2w_2$,
and $\lVert c\rVert_{\mathrm{op},\infty}=\lVert c\rVert_1$ by Young's inequality for
negacyclic convolution). Concrete: 24 zeros / 32 ±1 / 8 ±2 in $d=64$:
$|\mathcal P|=\binom{64}{32}\binom{32}{8}2^{40}\approx2^{128}$, $T=48$.

### 3.3 Gadget decomposition

$\vec g_a=(1,a,\dots,a^{\iota-1})$, $\iota=\lceil\log_aq\rceil$;
$G_{a,m}=I_m\otimes\vec g_a^T$; $G^{-1}_{a,m}(\cdot)$ is the entry-wise base-$a$
decomposition *operator* (not a matrix inverse): for $A\in R_q^{m\times n}$,
$\tilde A:=G^{-1}_{a,m}(A)\in R_q^{m\times n\iota}$ with $G_{a,m}\tilde A=A$.

### 3.4 M-SIS and Ajtai commitments

**M-SIS$_{\kappa,n,q,\beta}$ (Def. 1):** given uniform $A\in R_q^{\kappa\times n}$,
$n>\kappa$, find nonzero $\vec z\in R_q^n$ with $A\vec z=\vec 0$, $\lVert\vec
z\rVert\le\beta$. **Ajtai commitment (Def. 2):** $\mathrm{Setup}:A\leftarrow\$
R_q^{\kappa\times n}$; $\mathrm{Commit}(\vec f):=A\vec f$ for short $\vec f$ ($\lVert
\vec f\rVert\le\beta$). Binding under M-SIS$_{\kappa,n,q,2\beta}$; hiding by appending
small randomness (treated as part of the witness throughout).

**Leveled $\log N$-level Ajtai commitment (Fig. 1, following Bootle–Lyubashevsky–
Nguyen–Seiler [12]):** for $\vec s\in R_q^{N\ell}$ with $N=2^k$, $k=\log N$:

$$
\mathrm{cm}=A_{\log N-1}\cdot G^{-1}_{\sigma,n_{\log N-1}\kappa}\Big(\cdots G^{-1}_{\sigma,n_2\kappa}\big(I_{n_2}\otimes A_1\big)\cdot G^{-1}_{\sigma,n_1\kappa}\big(I_{n_1}\otimes A_0\big)\vec s\Big)
$$

with $A_0\in R_q^{\kappa\times2^{0}\cdot\ell}$-shaped base matrix (paper writes
$A_0\in R_q^{\kappa\times m_0\ell}$, $m_0=2$ at the base since halves of $\vec s$),
$A_i\in R_q^{\kappa\times2^i\kappa}$ for $i\in[1:\log N]$, $n_i:=N/2^{i+1}$... (as
printed: $n_i=\sum_{j=i}^{k-1}m_j$ general, $=N/2^{i+1}$ for the binary tree).
Intermediate commitments (prover's private state):

$$
\mathrm{cm}_{\mathrm{min},i}:=G^{-1}_{\sigma,n_{i+1}\kappa}\Big(I_{n_{i+1}}\otimes A_i\Big)\,G^{-1}_{\sigma,n_i\kappa}\cdots G^{-1}_{\sigma,n_1\kappa}\big(I_{n_1}\otimes A_0\big)\vec s,\qquad i\in[\log N-1]
$$

satisfying the recurrence
$\mathrm{cm}_{\mathrm{min},i+1}=G^{-1}_{\sigma,n_{i+2}\kappa}\big(I_{n_{i+2}}\otimes
A_{i+1}\big)\mathrm{cm}_{\mathrm{min},i}$ for $i\in[0:\log N-3]$ and the top-level
relation $\boxed{A_{\log N-1}\cdot\mathrm{cm}_{\mathrm{min},\log N-2}=\mathrm{cm}}$ (Eq. 3).
Tree reading of Fig. 1: $\vec s\in R_q^{N\ell}$ at the leaves;
$\mathrm{cm}_{\mathrm{min},\log N-2}\in R_q^{2\kappa}$ one level below the root
($=G^{-1}_{\sigma,2\kappa}(I_2\otimes A_{\log N-2})\,\mathrm{cm}_{\mathrm{min},\log N-3}$);
$\mathrm{cm}_{\mathrm{min},i}\in R_q^{2^{\log N-i-1}\kappa}$ in general. Two-level
variants ($k=2$) are used by LaBRADOR/Greyhound; Cini et al. use $\log N$ levels with
identical $A_i$.

### 3.5 LaBRADOR relation (§2.3)

$R_{\mathrm{Lab}}=((F,F',\beta),(\vec z_0..\vec z_{r-1}))$ with (i) $f(\vec z_0..\vec
z_{r-1})=0\ \forall f\in F$, (ii) $\mathrm{ct}(f'(\ldots))=0\ \forall f'\in F'$, (iii)
$\sum_{i=0}^{r-1}\lVert\vec z_i\rVert_2^2\le\beta^2$, where each $f$ is a quadratic dot
product (Eq. 1): $f=\sum_{i,j}\alpha_{i,j}\langle\vec z_i,\vec z_j\rangle+\sum_i
\langle\vec\varphi_i,\vec z_i\rangle-b$. Proof size $O(\log\log N)$ for $N=n\cdot r$
with $r=N^{1/3}$, $n=N^{2/3}$; quasi-linear prover/verifier.

### 3.6 Coordinate-wise special soundness (App. B.2)

$\vec x\equiv_i\vec y$: agree everywhere except coordinate $i$. $\mathrm{SS}(S,\ell,k)$:
$K=\ell(k-1)+1$ vectors with a "central" $\vec x_e$ and, per coordinate $i$, $k-1$
others differing only at $i$. A $(2\mu+1)$-round public-coin protocol is
$\ell$-coordinate-wise $k$-special sound if an extractor, given the corresponding
$K^\mu$-transcript tree, outputs a witness. Lemma 3 (from SLAP [22, Lem 2.31]):
coordinate-wise special soundness with $(\ell(k-1))^\mu=\mathrm{poly}(\lambda)$ ⇒
knowledge soundness with error $\mu\ell(k-1)/|S|$.

## 4. Relations (exact equations)

**(a) The unified main relation (Eq. 2, §3.1).** With $b_0=2\ell d$, $b_i=2$ for
$i\in[1:\log N]$:

$$
R_{\mathrm{main}}=\left\{
\begin{array}{l}
(\mathrm{cm}\in R_q^\kappa,\ \beta\in\mathbb Z_q,\ v,b\in\mathbb Z_q,\ (\vec a_i\in\mathbb Z_q^{b_i})_{i\in[\log N]}),\\
(\vec s\in R_q^{N\ell},\ (\mathrm{cm}_{\mathrm{min},i}\in R_q^{2^{i+1}\kappa})_{i\in[\log N-1]})
\end{array}
:\ \begin{array}{l}
\mathrm{Com}(\vec s)=\mathrm{cm},\\
\langle\mathrm{coef}(\vec s),\bigotimes_{i=0}^{\log N-1}\vec a_i\rangle=v,\\
\mathrm{ct}\langle\vec s,\sigma^{-1}(\vec s)\rangle\bmod q=b\le\beta^2,\\
\mathrm{coef}(\vec s)\in\{0,1\}^{N\ell d}
\end{array}
\right\}
$$

(i) commitment constraint; (ii) tensor-structured linear (evaluation) constraint;
(iii) quadratic self-inner-product + range; (iv) binarity. Lemma 2 ⇒ (iii)+(iv) give
$\lVert\vec s\rVert_2\le\beta$ **exactly** (when $q>2N\ell d$).

**(b) Exact-ℓ2 decomposition (Lemma 2).** Enforcing slack-free
$\lVert\vec f\rVert_2\le B$ on $\vec f\in R_q^{N\ell}$ reduces to:
1. self-IP constraint $\mathrm{ct}\langle\vec f,\sigma^{-1}(\vec f)\rangle=b\bmod q$
   with $0\le b\le B^2$;
2. bit constraint $\mathrm{coef}(\vec f)\in\{0,1\}^{N\ell d}$.
Proof: bit constraint ⇒ $\lVert\vec f\rVert_\infty=1$ ⇒ $|\vec f|^2\le N\ell d$; for
$q>2N\ell d$ the centered representative of the residue equals the integer
$|\vec f|^2$; hence $b\le B^2$ ⇒ $|\vec f|^2\le B^2$. ∎

**(c) Binarity as inner-product constraints (§3.3).** $\vec s\in\{0,1\}^{N\ell d}$
iff $\vec s\circ(\vec s-\vec 1)=\vec 0$. Randomized: for verifier-sampled
$\alpha\leftarrow\$\mathbb Z_q$, $\vec\alpha:=(1,\alpha,\dots,\alpha^{N\ell d-1})$:

$$
\langle\vec\alpha\circ\vec s,\ \vec s-\vec 1\rangle=0
\iff
\langle\vec\alpha\circ\vec s,\vec s\rangle=\langle\vec\alpha,\vec s\rangle\quad(=v_\alpha)
$$

If $\vec s\notin\{0,1\}^{N\ell d}$, $P(\alpha):=\sum_{i=0}^{N\ell d-1}(s_i^2-s_i)\alpha^i$
is a nonzero polynomial of degree $\le N\ell d-1$ ⇒ error $\le N\ell d/q$. Tensor split:
$\vec\alpha=\bigotimes_{i=0}^{\log N-1}\vec\alpha_i$ with $\vec\alpha_0=(1,\alpha,\dots,
\alpha^{2\ell d-1})\in\mathbb Z_q^{2\ell d}$ and $\vec\alpha_i=(1,\alpha^{2^i\cdot2\ell d})\in
\mathbb Z_q^2$ — matching the $b_0=2\ell d$, $b_i=2$ structure of $R_{\mathrm{main}}$.
Embedding into the ring: $\vec s_\alpha\in R_q^{N\ell}$ with
$\mathrm{coef}(\vec s_\alpha)=\vec s\circ\vec\alpha$ so that
$\mathrm{ct}\langle\vec s_\alpha,\sigma^{-1}(\vec s)\rangle=\langle\vec s_\alpha,\vec s\rangle=v_\alpha$.

**Well-formedness of $\vec s_\alpha$:** verifier samples $r\leftarrow\$\mathbb Z_q$
*after* the prover commits to $\hat s_\alpha$; define $\vec r:=(1,r,\dots,r^{N\ell d-1})$,
$\vec r_\alpha:=\vec r\circ\vec\alpha=(1,r\alpha,\dots,(r\alpha)^{N\ell d-1})$; then
$\mathrm{coef}(\vec s_\alpha)=\vec s\circ\vec\alpha$ implies
$\langle\mathrm{coef}(\vec s_\alpha),\vec r\rangle=\langle\mathrm{coef}(\vec s),\vec r_\alpha\rangle$
i.e. $v_r=v_{r\alpha}$ — again tensor-structured, again provable by the same engine.
Decomposition: $\hat s_\alpha=G^{-1}_{\sigma_\alpha,N\ell}(\vec s_\alpha)$,
$\mathrm{cm}_\alpha=\mathrm{Com}(\hat s_\alpha)$ (with $B$-matrices); only a *loose*
norm bound on $\hat s_\alpha$ is needed.

**(d) The five binary-check claims (§3.3 protocol list):**

1. $\mathrm{Com}(\hat s_\alpha)=\mathrm{cm}_\alpha$;
2. $\langle\mathrm{coef}(\vec s),\bigotimes_{i=0}^{\log N-1}\vec\alpha_i\rangle=v_\alpha$;
3. $\langle\mathrm{coef}(\vec s),\vec r_\alpha\rangle=v_{r\alpha}$;
4. $\langle\mathrm{coef}(G_{\sigma_\alpha,N\ell}\hat s_\alpha),\vec r\rangle=v_r$ and $v_r=v_{r\alpha}$;
5. $\mathrm{ct}\langle G_{\sigma_\alpha,N\ell}\hat s_\alpha,\ \sigma^{-1}(\vec s)\rangle=v_\alpha$.

**(e) PCS relations (App. B.3,Defs. 7–10):** syntax
$(\mathrm{Setup},\mathrm{Commit},\mathrm{Open},\mathrm{Eval})$ over
$\mathbb Z_q^{<N d}[X]$; properties: evaluation completeness (Def. 8), binding
(Def. 9: two distinct polynomial openings of one cm), knowledge soundness (Def. 10:
extractor returns $(f,\mathrm{st})$ opening cm with $f(u)=z$).

**(f) Evaluation constraint reductions (§4):**

- *Univariate* $f$ with $\vec f\in\mathbb Z_q^{Nd}$, point $u_{\mathrm{uni}}$:
  $\sum_{i=0}^{Nd-1}f_i u_{\mathrm{uni}}^i=v$ i.e. $\langle\vec f,\vec
  u_{\mathrm{uni}}\rangle=v$ with $\vec u_{\mathrm{uni}}=(1,u_{\mathrm{uni}},\dots,
  u_{\mathrm{uni}}^{Nd-1})$; tensor split $\vec u_{\mathrm{uni}}=\bigotimes_{i=0}^{\log
  N-1}\vec u_{\mathrm{uni},i}$ with $\vec u_{\mathrm{uni},0}=(1,u,\dots,u^{2d-1})\in
  \mathbb Z_q^{2d}$, $\vec u_{\mathrm{uni},i}=(1,u)\in\mathbb Z_q^2$.
- *Multilinear* over $\log(Nd)$ variables: $\vec u_{\mathrm{mul}}=\bigotimes_{j=0}^{\log(Nd)-1}
  (1,u_j)$, regrouped as $\vec u_{\mathrm{mul},0}=\bigotimes_{j=0}^{\log(2d)-1}(1,u_j)\in
  \mathbb Z_q^{2d}$, $\vec u_{\mathrm{mul},i}=(1,u_{\log(2d)+i-1})\in\mathbb Z_q^2$.
- *Large-norm decomposition*: $\ell:=\lceil\log q\rceil$, unsigned base-2 coefficient-wise
  ⇒ $\mathrm{coef}(\vec s)\in\{0,1\}^{N\ell d}$, $\lVert\vec s\rVert_\infty\le1$,
  $\beta:=\sqrt{N\ell d}$; absorb the base-2 weights into the first tensor factor:
  $\vec a_0:=\vec u_{\mathrm{uni},0}\otimes(1,2,2^2,\dots,2^{\ell-1})\in\mathbb Z_q^{2d\ell}$
  (resp. $\vec u_{\mathrm{mul},0}\otimes(\ldots)$), $\vec a_i:=\vec u_{\cdot,i}$ for
  $i\ge1$ ⇒ $b_0=2\ell d$, $b_i=2$.

## 5. Protocols (full step-by-step transcriptions)

### 5.1 Core commitment constraint proof (§3.2 "Commitments")

Witness $\vec s\in R_q^{N\ell}$, private state $\{\mathrm{cm}_{\mathrm{min},i}\}_{i\in[\log N-1]}$.

- **Round 1:** P sends the pair
  $(\mathrm{cm}_{1,L}^{(\mathrm{cm})},\mathrm{cm}_{1,R}^{(\mathrm{cm})}):=
  \mathrm{cm}_{\mathrm{min},\log N-2}\in R_q^{2\kappa}$ (the two halves).
  V checks the top-level relation (Eq. 3): $A_{\log N-1}\cdot\mathrm{cm}_{\mathrm{min},\log N-2}
  \stackrel?= \mathrm{cm}$.
- V samples $\vec c_1=(c_{1,0},c_{1,1})\leftarrow\$\mathcal C^2$. P folds the witness
  $\vec s=(\vec s_L\Vert\vec s_R)$: $\vec s_2:=c_{1,0}\vec s_L+c_{1,1}\vec s_R$, and
  folds each stored intermediate commitment entry-wise the same way.
- **Round $i\ge2$:** P sends the next pair
  $\pi_i^{(\mathrm{cm})}=(\mathrm{cm}_{i,L}^{(\mathrm{cm})},\mathrm{cm}_{i,R}^{(\mathrm{cm})})
  \in R_q^{2\kappa}$ — the folded intermediate commitment one level below. V checks the
  recurrence against the gadget matrix:
  $A_{\log N-i}\cdot\pi_i^{(\mathrm{cm})}\stackrel?=\big[c_{i-1,0}G_{\sigma,\kappa},\ c_{i-1,1}G_{\sigma,\kappa}\big]\cdot\pi_{i-1}^{(\mathrm{cm})}$.
- Recursion for $\log N$ rounds; each round drops one commitment level and halves the
  witness along the $N$ axis. Final witness $\vec s_{\log N}\in R_q^{2\ell}$ is sent
  in the last round; V checks it opens the final folded commitment:
  $A_0\cdot\vec s_{\log N}\stackrel?=[c_{\log N-1,0}G_{\sigma,\kappa},\ c_{\log N-1,1}G_{\sigma,\kappa}]\cdot
  \pi_{\log N-1}^{(\mathrm{cm})}$.
- Transcript: $\pi^{(\mathrm{cm})}=(\pi_1^{(\mathrm{cm})},\dots,\pi_{\log N}^{(\mathrm{cm})})$,
  $\pi_i^{(\mathrm{cm})}\in R_q^{2\kappa}$ for $i<\log N$, $\pi_{\log N}^{(\mathrm{cm})}=
  \vec s_{\log N}\in R_q^{2\ell}$.

### 5.2 Linear (evaluation) constraint proof (§3.2)

Prove $\langle\mathrm{coef}(\vec s),\bigotimes_{i=0}^{\log N-1}\vec a_i\rangle=v$.

- Define the packed base factor $\vec a_0\in R_q^{2\ell}$ as in §4 (weights included),
  and $\vec a^{(\log N-2)}:=\bigotimes_{i=1}^{\log N-1}\vec a_i$; then
  $\langle\mathrm{coef}(\vec s),\bigotimes_{i=0}^{\log N-1}\vec a_i\rangle
  =\mathrm{ct}\langle\vec s,\vec a^{(\log N-2)}\otimes\vec a_0\rangle$.
- **Round 1:** write $\vec s=(\vec s_L\Vert\vec s_R)$; tensor decomposition of the last
  factor gives
  $\langle\vec s,\vec a_{\log N-1}\otimes\vec a^{(\log N-2)}\rangle=\langle\vec a_{\log
  N-1},(\langle\vec s_L,\vec a^{(\log N-2)}\rangle,\langle\vec s_R,\vec a^{(\log
  N-2)}\rangle)\rangle$. P sends $v_{1,L}:=\langle\vec s_L,\vec a^{(\log N-2)}\rangle$
  and $v_{1,R}:=\langle\vec s_R,\vec a^{(\log N-2)}\rangle$ (both $\in R_q$).
  V checks $\mathrm{ct}\langle\vec a_{\log N-1},(v_{1,L},v_{1,R})\rangle\stackrel?=v$.
- V samples $\vec c_1\in\mathcal C^2$ (shared with the other sub-proofs); P folds
  $\vec s_2:=c_{1,0}\vec s_L+c_{1,1}\vec s_R$; V reduces the claim to
  $\langle\vec s_2,\vec a^{(\log N-2)}\rangle\stackrel?=c_{1,0}v_{1,L}+c_{1,1}v_{1,R}$.
- Recursion for $\log N-1$ rounds (halving along $N$). Final round: P sends
  $\vec s_{\log N}\in R_q^{2\ell}$; V computes $\langle\vec s_{\log N},\vec a_0\rangle$
  locally and matches the reduced claim.
- Transcript: $\pi^{(\mathrm{lin})}=(\pi_1^{(\mathrm{lin})},..)$ with
  $\pi_i^{(\mathrm{lin})}=(v_{i,L},v_{i,R})\in R_q^2$ for $i<\log N$,
  $\pi_{\log N}^{(\mathrm{lin})}=\vec s_{\log N}\in R_q^{2\ell}$ (sent once, shared).

### 5.3 Quadratic (self-inner-product) constraint proof (§3.2)

Prove $\mathrm{ct}\langle\vec s,\sigma^{-1}(\vec s)\rangle=b$.

- Write $\vec s=(\vec s_L\Vert\vec s_R)$; then
  $\langle\vec s,\sigma^{-1}(\vec s)\rangle=\langle\vec s_L,\sigma^{-1}(\vec s_L)\rangle
  +\langle\vec s_R,\sigma^{-1}(\vec s_R)\rangle$. P sends
  $L_1:=\langle\vec s_L,\sigma^{-1}(\vec s_L)\rangle$,
  $R_1:=\langle\vec s_R,\sigma^{-1}(\vec s_R)\rangle$; V checks
  $\mathrm{ct}(L_1+R_1)\equiv b\pmod q$.
- $(L_1,R_1)$ alone don't recurse: V samples $\vec c_1\in\mathcal C^2$, P folds
  $\vec s_2:=c_{1,0}\vec s_L+c_{1,1}\vec s_R$, and by multiplicativity of $\sigma^{-1}$:

$$
\langle\vec s_2,\sigma^{-1}(\vec s_2)\rangle
=c_{1,0}\sigma^{-1}(c_{1,0})L_1+c_{1,1}\sigma^{-1}(c_{1,1})R_1
+c_{1,0}\sigma^{-1}(c_{1,1})\underbrace{\langle\vec s_L,\sigma^{-1}(\vec s_R)\rangle}_{M_1^{(1)}}
+c_{1,1}\sigma^{-1}(c_{1,0})\underbrace{\langle\vec s_R,\sigma^{-1}(\vec s_L)\rangle}_{M_1^{(2)}}
$$

  so P additionally sends cross terms $M_1^{(1)},M_1^{(2)}$.
- With $\pi_1^{(\mathrm{qua})}=(L_1,M_1^{(1)},M_1^{(2)},R_1)$ and $\vec c_1$, the
  original constraint reduces to checking
  $\langle\vec s_2,\sigma^{-1}(\vec s_2)\rangle=\langle\vec c_1^{(\mathrm{qua})},
  \pi_1^{(\mathrm{qua})}\rangle$ where
  $\vec c_1^{(\mathrm{qua})}=(c_{1,0}\sigma^{-1}(c_{1,0}),\ c_{1,1}\sigma^{-1}(c_{1,1}),\
  c_{1,0}\sigma^{-1}(c_{1,1}),\ c_{1,1}\sigma^{-1}(c_{1,0}))$.
- Recurse on $\vec s_2$; run $\log N$ rounds (folding only along $N$, not $\log(N\ell)$,
  to align with the other sub-proofs). Transcript:
  $\pi_i^{(\mathrm{qua})}=(L_i,M_i^{(1)},M_i^{(2)},R_i)\in R_q^4$ for $i<\log N$,
  $\pi_{\log N}^{(\mathrm{qua})}=\vec s_{\log N}\in R_q^{2\ell}$; V locally computes
  $\langle\vec s_{\log N},\sigma^{-1}(\vec s_{\log N})\rangle$ and matches.
- **Same per-round challenge $\vec c_i$ across all sub-proofs; final folded witness
  sent only once.**

### 5.4 Binary range proof (§3.3)

For each repetition $j\in[t]$ (fresh $\alpha^{(j)}$):

1. V samples $\alpha^{(j)}\leftarrow\$\mathbb Z_q$ and defines $\vec\alpha^{(j)}$
   (tensor split as above).
2. P constructs $\vec s_\alpha^{(j)}=\vec\alpha^{(j)}\circ\vec s$ (coefficient-wise),
   computes $v_\alpha^{(j)}=\langle\vec\alpha^{(j)},\vec s\rangle$, decomposes
   $\hat s_\alpha^{(j)}=G^{-1}_{\sigma_\alpha,N\ell}(\vec s_\alpha^{(j)})$, commits
   $\mathrm{cm}_\alpha^{(j)}=\mathrm{Com}(\hat s_\alpha^{(j)})$, and sends
   $(\mathrm{cm}_\alpha^{(j)},v_\alpha^{(j)})$.
   *(Commitment BEFORE $r$: mandatory ordering.)*
3. V samples $r^{(j)}\leftarrow\$\mathbb Z_q$; constructs tensor-decomposed
   $\vec r^{(j)}_i,\vec r^{(j)}_{\alpha,i}$ with
   $\bigotimes_{i=0}^{\log N-1}\vec r^{(j)}_i=\vec r^{(j)}$,
   $\bigotimes_i\vec r^{(j)}_{\alpha,i}=\vec r^{(j)}\circ\vec\alpha^{(j)}$.
4. P computes $v_r^{(j)}=\langle\vec s_\alpha^{(j)},\vec r^{(j)}\rangle$ and
   $v_{r\alpha}^{(j)}=\langle\vec s,\vec r^{(j)}_\alpha\rangle$; V checks
   $v_r^{(j)}\stackrel?=v_{r\alpha}^{(j)}$.
5. The parties then prove, via the §5.1–5.3 recursion (quadratic used in *bilinear*
   form — two different witnesses), the five claims (d) above:
   commitment of $\hat s_\alpha$; $\langle\mathrm{coef}(\vec s),\bigotimes\vec\alpha_i\rangle=v_\alpha$;
   $\langle\mathrm{coef}(\vec s),\vec r_\alpha\rangle=v_{r\alpha}$;
   $\langle\mathrm{coef}(G_{\sigma_\alpha,N\ell}\hat s_\alpha),\vec r\rangle=v_r$;
   $\mathrm{ct}\langle G_{\sigma_\alpha,N\ell}\hat s_\alpha,\sigma^{-1}(\vec s)\rangle=v_\alpha$.
6. Per round $i\in[1,\log N]$ the binary sub-proof message is
   $\pi_i^{(\mathrm{bin})}=(\pi_i^{(\mathrm{cm},\alpha)},\pi_i^{(\mathrm{lin}_1,\alpha)},
   \pi_i^{(\mathrm{lin}_2,\alpha)},\pi_i^{(\mathrm{lin}_3,\alpha)},\pi_i^{(\mathrm{qua},\alpha)})
   \in R_q^{2\kappa i+10}$; in the final round P sends
   $\hat s_{\alpha,\log N}\in R_q^{2\ell\iota_\alpha}$ directly.
7. Per-repetition soundness error $\le2N\ell d/q$; repeat $t=\lambda/
   \lceil\log q/(2N\ell d)\rceil$ times for $(2N\ell d/q)^t\le2^{-\lambda}$
   (needs $q>2N\ell d$).

### 5.5 Figure 2 — complete core protocol for $R_{\mathrm{main}}$

**Public inputs:** $\mathrm{cm}=\mathrm{Com}(\vec s)$, $v,b,\beta\in\mathbb Z_q$,
$(\vec a_i\in\mathbb Z_q^{b_i})_{i\in[\log N]}$ with $b_i=2\ (i\ge1)$, $b_0=2\ell d$;
$n_{i+1}=N/2^{i+1}$. **Private inputs:** $\vec s\in R_q^{N\ell}$,
$(\mathrm{cm}_{\mathrm{min},i}\in R_q^{2^{i+1}\kappa})_{i\in[\log N-1]}$.

| | Prover P | Verifier V |
|---|---|---|
| **statement** | | Check $0\le b\le\beta^2$ *(statement-level, transcript-independent)* |
| **pre** | — receives $(\alpha^{(j)})_{j\in[t]}\leftarrow\$\mathbb Z_q$ from V | Sample $(\alpha^{(j)})_{j\in[t]}$; construct $\bigotimes_{i=0}^{\log N-1}\vec\alpha_i^{(j)}=\vec\alpha^{(j)}$ |
| | Construct $\vec s_\alpha^{(j)}=\vec\alpha^{(j)}\circ\vec s$ | |
| | Send $(\mathrm{cm}_\alpha^{(j)},v_\alpha^{(j)})_{j\in[t]}$ where $v_\alpha^{(j)}=\langle\vec\alpha^{(j)},\vec s\rangle$, $\hat s_\alpha^{(j)}=G^{-1}_{\sigma_\alpha,N\ell}(\vec s_\alpha^{(j)})$, $\mathrm{cm}_\alpha^{(j)}=\mathrm{Com}(\hat s_\alpha^{(j)})$ | |
| | — receives $(r^{(j)})_{j\in[t]}$ | Sample $r^{(j)}\leftarrow\$\mathbb Z_q$; construct $\bigotimes_i\vec r^{(j)}_i=\vec r^{(j)}$, $\bigotimes_i\vec r^{(j)}_{\alpha,i}=\vec r^{(j)}\circ\vec\alpha^{(j)}$ |
| | Compute $v_r^{(j)}=\langle\vec s_\alpha^{(j)},\vec r^{(j)}\rangle$, $v_{r\alpha}^{(j)}=\langle\vec s,\vec r_\alpha^{(j)}\rangle$; send $(v_r^{(j)},v_{r\alpha}^{(j)})_{j\in[t]}$ | Check $v_r^{(j)}\stackrel?=v_{r\alpha}^{(j)}$ for all $j$ |
| **round 1** | Compute $\vec\pi_1=(\vec\pi_1^{(\mathrm{cm})},\vec\pi_1^{(\mathrm{lin})},\vec\pi_1^{(\mathrm{qua})},(\vec\pi_1^{(\mathrm{bin},j)})_{j\in[t]})$ | Run $\mathrm{Verify}(\pi_1)$ (Fig. 3 case $i=1$) |
| | — receives $\vec c_1$ | Sample $\vec c_1\leftarrow\$\mathcal C^2$ |
| **round $i$** | Update $\vec s_{i+1}=c_{i,0}\vec s_{i,L}+c_{i,1}\vec s_{i,R}$ and $\hat s^{(j)}_{\alpha,i+1}=c_{i,0}\hat s^{(j)}_{\alpha,i,L}+c_{i,1}\hat s^{(j)}_{\alpha,i,R}$; compute $\vec\pi_{i+1}$ | Run $\mathrm{Verify}(\pi_1..,\pi_{i+1})$; sample $\vec c_{i+1}\leftarrow\$\mathcal C^2$ |
| | ⋮ iterate $\log N-1$ rounds ⋮ | |
| **final** | Send $\vec s_{\log N}$ and $(\hat s^{(j)}_{\alpha,\log N})_{j\in[t]}$ | Run final verification (Fig. 3 case $i=\log N$) |

### 5.6 Figure 3 — verification algorithm $\mathrm{Verify}((\pi_k)_{k\in[1,i+1]})$

**Case $i=1$** (for each binary repetition $j\in[t]$, using the same $\vec c_1$):

- $A_{\log N-1}\cdot\pi_1^{(\mathrm{cm})}\stackrel?=\mathrm{cm}$  and
  $B_{\log N-1}\cdot\pi_1^{(\mathrm{cm},\alpha,j)}\stackrel?=\mathrm{cm}_\alpha^{(j)}$
- $\mathrm{ct}\langle\vec a_{\log N-1},\pi_1^{(\mathrm{lin})}\rangle\stackrel?=v$
- $\mathrm{ct}\langle\vec r_{\log N-1}^{(j)},\pi_1^{(\mathrm{lin}_1,\alpha,j)}\rangle\stackrel?=v_r^{(j)}$
- $\mathrm{ct}\langle\vec r_{\alpha,\log N-1}^{(j)},\pi_1^{(\mathrm{lin}_2,\alpha,j)}\rangle\stackrel?=v_{r\alpha}^{(j)}$
- $\mathrm{ct}\langle\vec\alpha_{\log N-1}^{(j)},\pi_1^{(\mathrm{lin}_3,\alpha,j)}\rangle\stackrel?=v_\alpha^{(j)}$
- $\mathrm{ct}\langle(1,0,0,1),\pi_1^{(\mathrm{qua})}\rangle\stackrel?=b$  and
  $\mathrm{ct}\langle(1,0,0,1),\pi_1^{(\mathrm{qua},\alpha,j)}\rangle\stackrel?=v_\alpha^{(j)}$

**Case $i\in\{2,\dots,\log N-1\}$** (with $\vec c_{i-1}=(c_{i-1,0},c_{i-1,1})$):

- Commitment consistency:
  $A_{\log N-i}\cdot\pi_i^{(\mathrm{cm})}\stackrel?=\big[c_{i-1,0}G_{\sigma,\kappa},\ c_{i-1,1}G_{\sigma,\kappa}\big]\cdot\pi_{i-1}^{(\mathrm{cm})}$
- Linear recursion: $\langle\vec a_{\log N-i},\pi_i^{(\mathrm{lin})}\rangle\stackrel?=\langle\vec c_{i-1},\pi_{i-1}^{(\mathrm{lin})}\rangle$
- Quadratic recursion: with
  $\vec c_{i-1}^{(\mathrm{qua})}=(c_{i-1,0}\sigma^{-1}(c_{i-1,0}),\,c_{i-1,0}\sigma^{-1}(c_{i-1,1}),\,c_{i-1,1}\sigma^{-1}(c_{i-1,0}),\,c_{i-1,1}\sigma^{-1}(c_{i-1,1}))$
  and $\pi_i^{(\mathrm{qua})}=(L_i,M_i^{(1)},M_i^{(2)},R_i)$:
  $(1,0,0,1)\cdot\pi_i^{(\mathrm{qua})}\stackrel?=\langle\vec c_{i-1}^{(\mathrm{qua})},\pi_{i-1}^{(\mathrm{qua})}\rangle$
  (i.e. $L_i+R_i=\langle\vec c_{i-1}^{(\mathrm{qua})},\pi_{i-1}^{(\mathrm{qua})}\rangle$)
- Binary recursion (each $j$), same folding challenge $\vec c_{i-1}$:
  $B_{\log N-i}\cdot\pi_i^{(\mathrm{cm},\alpha,j)}\stackrel?=[c_{i-1,0}G_{\sigma,\kappa},\,c_{i-1,1}G_{\sigma,\kappa}]\cdot\pi_{i-1}^{(\mathrm{cm},\alpha,j)}$;
  $\langle\vec r_{\log N-i}^{(j)},\pi_i^{(\mathrm{lin}_1,\alpha,j)}\rangle\stackrel?=\langle\vec c_{i-1},\pi_{i-1}^{(\mathrm{lin}_1,\alpha,j)}\rangle$;
  $\langle\vec r_{\alpha,\log N-i}^{(j)},\pi_i^{(\mathrm{lin}_2,\alpha,j)}\rangle\stackrel?=\langle\vec c_{i-1},\pi_{i-1}^{(\mathrm{lin}_2,\alpha,j)}\rangle$;
  $\langle\vec\alpha_{\log N-i}^{(j)},\pi_i^{(\mathrm{lin}_3,\alpha,j)}\rangle\stackrel?=\langle\vec c_{i-1},\pi_{i-1}^{(\mathrm{lin}_3,\alpha,j)}\rangle$;
  $(1,0,0,1)\cdot\pi_i^{(\mathrm{qua},\alpha,j)}\stackrel?=\langle\vec c_{i-1}^{(\mathrm{qua})},\pi_{i-1}^{(\mathrm{qua},\alpha,j)}\rangle$

**Case $i=\log N$ (final round; prover sent $\vec s_{\log N}$, $\hat s_{\alpha,\log N}^{(j)}$):**

1. Norm admissibility: $\lVert\vec s_{\log N}\rVert\le\gamma$ and
   $\lVert\hat s^{(j)}_{\alpha,\log N}\rVert\le\gamma_\alpha$ for all $j$.
2. Base commitment opening:
   $A_0\cdot\vec s_{\log N}\stackrel?=[c_{\log N-1,0}G_{\sigma,\kappa},\,c_{\log N-1,1}G_{\sigma,\kappa}]\cdot\pi_{\log N-1}^{(\mathrm{cm})}$.
3. Auxiliary base opening:
   $B_0\cdot\hat s^{(j)}_{\alpha,\log N}\stackrel?=[c_{\log N-1,0}G_{\sigma,\kappa},\,c_{\log N-1,1}G_{\sigma,\kappa}]\cdot\pi_{\log N-1}^{(\mathrm{cm},\alpha,j)}$.
4. Final linear check: $\langle\vec a_0,\vec s_{\log N}\rangle\stackrel?=\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin})}\rangle$.
5. Final binary linear checks (per $j$):
   $\langle\vec r_0^{(j)},\hat s^{(j)}_{\alpha,\log N}\rangle\stackrel?=\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_1,\alpha,j)}\rangle$;
   $\langle\vec r_{\alpha,0}^{(j)},\vec s_{\log N}\rangle\stackrel?=\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_2,\alpha,j)}\rangle$;
   $\langle\vec\alpha_0^{(j)},\vec s_{\log N}\rangle\stackrel?=\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_3,\alpha,j)}\rangle$.
6. Final quadratic check: $\langle\vec s_{\log N},\sigma^{-1}(\vec s_{\log N})\rangle\stackrel?=\langle\vec c_{\log N-1}^{(\mathrm{qua})},\pi_{\log N-1}^{(\mathrm{qua})}\rangle$.
7. Final binary quadratic check (per $j$):
   $\langle G_{\sigma_\alpha,2\ell}\,\hat s^{(j)}_{\alpha,\log N},\ \sigma^{-1}(\vec s_{\log N})\rangle\stackrel?=\langle\vec c_{\log N-1}^{(\mathrm{qua})},\pi_{\log N-1}^{(\mathrm{qua},\alpha,j)}\rangle$.

*(§3.4 text also lists a "final binary linear check"
$\langle\vec r_{\alpha,0},G_{\sigma_\alpha,2\ell}\cdot\hat s_{\alpha,\log N}\rangle=
\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_2,\alpha)}\rangle$ variant —
see pitfalls §8.7 on the lin₁/lin₂ argument ambiguity.)*

### 5.7 Figure 4 — the PCS (Commit / Open / Eval)

**Public parameters:**
$\mathrm{pp}=((A_i,B_i\in R_q^{\kappa\times2^i\kappa})_{i\in[1,\log N]},\
A_0\in R_q^{\kappa\times2\lceil\log q\rceil},\
B_0\in R_q^{\kappa\times2\lceil\log q\rceil\iota_\alpha})$.

- $\mathrm{Commit}(\mathrm{pp},f)\to(\mathrm{cm},\mathrm{st})$:
  represent $f$ as $\vec f=(f_0,\dots,f_{Nd-1})$; pack
  $f_i=\sum_{j=0}^{d-1}f_{id+j}X^j$ for $i\in[N]$ giving $\vec f=(f_0,\dots,f_{N-1})
  \in R_q^N$; unsigned base-2 decompose $\vec f$ (each coefficient mod $q$) to get
  $\vec s\in R_q^{N\ell}$; $(\mathrm{cm},\mathrm{st})=\mathrm{Com}(\vec s)$
  (leveled commitment, storing intermediate states).
- $\mathrm{Open}(\mathrm{pp},\mathrm{cm},f,\mathrm{st})\to\{0,1\}$: recompute $\vec s$
  from $f$; return $\mathrm{Com}(\vec s)=(\mathrm{cm},\mathrm{st})$.
- $\mathrm{Eval}(\mathrm{pp},\mathrm{cm},u\ \text{or}\ \vec u\in\mathbb Z_q^{\log(Nd)},v;\ (f,\mathrm{st}))$:
  compute $\vec s$ from $f$; construct $(\vec u_{\mathrm{uni},i})_{i\in[\log N]}$
  (resp. $(\vec u_{\mathrm{mul},i})$) with base-2 weights folded into factor 0; set
  $\vec a_i=\vec u_{\cdot,i}$; run the Fig. 2 protocol to prove
  $((\mathrm{cm},\beta,v,b,(\vec a_i)_{i\in[\log N]});\vec s)$ with
  $\beta=\sqrt{N\ell d}$ and $b=\lVert\vec s\rVert^2$ (integer, $<q/2$).

Theorem 4: the Fig. 4 PCS satisfies evaluation completeness (Thm 1), weak binding
(Thm 2 / M-SIS), knowledge soundness (Thm 3). ZK: not native — can be added by hiding
the $\ell_2$ norm of the witness and proving it via standard range-proof techniques.

### 5.8 Algorithm 1 — FS folding-challenge generation

Input: transcript prefix commitment $\mathrm{Com}(\mathrm{tr}_{i-1})=
\mathrm{Com}(\mathrm{pp},\mathrm{cm},(\mathrm{cm}_\alpha^{(j)})_{j\in[t]},\pi_1,\dots,\pi_{i-1})$.

1. $\mu_i\leftarrow H(\mathrm{Com}(\mathrm{tr}_{i-1}))$; $\rho_i\leftarrow\mathrm{PRG}(\mu_i)$.
2. For $j\in\{0,1\}$ (the two challenge slots $c_{i,j}$):
   - absolute-value multiset $A:=[\underbrace{0,\dots,0}_{24},\underbrace{1,\dots,1}_{32},\underbrace{2,\dots,2}_{8}]$ (length $d=64$);
   - Fisher–Yates shuffle of $A$ using bits of $\rho_i$: for $k=d-1\to1$:
     $x\leftarrow$ next bits as integer in $[0,k]$; swap $A[k]\leftrightarrow A[x]$;
   - random signs: for $k=0\to d-1$: if $A[k]=0$ then $c_{i,j,k}\leftarrow0$; else
     $s\leftarrow$ next bit; $c_{i,j,k}\leftarrow A[k]\cdot(-1)^s$;
   - $c_{i,j}:=\sum_{k=0}^{d-1}c_{i,j,k}X^k\in R_q$.
3. Return $\vec c_i=(c_{i,0},c_{i,1})$.

Guarantees: all outputs in $\mathcal C$ (24 zeros/32 ±1/8 ±2 profile ⇒
$\lVert c\rVert_1=32+8\cdot2=48=T$; invertibility of differences by $q\equiv5\bmod8$
+ Lemma 1 since $\lVert c-c'\rVert_2\le4\sqrt{2w_1+2w_2}<\sqrt{q/2}$); round index +
domain separator included in the hash input to avoid cross-round collisions; verifier
reconstructs the identical $\vec c_i$ from the committed prefix.

### 5.9 LaBRADOR compaction (§5.1)

- Apply FS to the recursive phase *after* the prover sends $(v_r,v_{r\alpha})$;
  challenges derived from committed transcript prefixes.
- Every round-$i$ verification condition in Fig. 3 is one of:
  (1) a dot product over $R_q$ (linear/quadratic recursion);
  (2) a linear-map consistency $A\cdot x=y$ — expand coordinates against standard
  basis vectors into dot products;
  (3) a final-round norm admissibility check — reduce to dot products via self-IP
  bound + binary decomposition (§3.3 machinery).
- Transcript-seed consistency: $\mathrm{Com}(\mathrm{tr}_i)$ must match the transcript
  blocks used for FS — linear constraints ⇒ dot products.
- Let $W$ = concatenation of all witness blocks (with base decompositions applied to
  large-norm components of $\pi_{\log N}$). Prover produces a LaBRADOR proof $\pi_L$
  for the system $\sum_{i,j}\alpha_{i,j}\langle\vec z_i,\vec z_j\rangle+\sum_i\langle
  \vec\varphi_i,\vec z_i\rangle-b=0$ where blocks $\vec z_i$ are slices of $W$ and
  $(\alpha_{i,j},\vec\varphi_i,b)$ are verifier-computable.
- $M:=|W|$ ring elements $=\Theta((t{+}1)\log N)+\Theta(t\ell\log\gamma_\alpha)+\ell\log
  \gamma=O(\lambda\log N)$; LaBRADOR proof $O(\log\log M)$ ring elements.
- Final compact proof: $\pi=(\pi_{\mathrm{pre}},\pi_L,(\mathrm{Com}(\mathrm{tr}_i))_{i\in[1,\log N]})$.
  Security moves to ROM, preserving M-SIS binding/extraction (Theorem 7:
  $\epsilon_{\mathrm{se}}+\epsilon_{\mathrm{fs}}+\epsilon_{\mathrm{La}}$).

### 5.10 Batching (Appendix E)

- **Multiple polys @ one point:** claims $f_i(u)=v_i$; V samples
  $\vec\alpha\leftarrow\$\mathbb Z_q^n$; P forms $f:=\sum_i\alpha_if_i$; both set
  $y:=\sum_i\alpha_iv_i$; one evaluation proof for $f$ at $u$. KS by rewinding + PCS
  extractor (repeated rewinding recovers each $f_i$).
- **Single poly @ multiple points (multilinear):** P constructs
  $\tilde f(\vec x)=\sum_{\vec b\in\{0,1\}^{\log N}}f(\vec b)\,
  \widetilde{\mathrm{eq}}(\vec b,\vec x)$ with
  $\widetilde{\mathrm{eq}}(\vec b,\vec x)=\prod_i(b[i]x[i]+(1-b[i])(1-x[i]))$;
  since $\tilde f=f$ on the cube and both are multilinear, $\tilde f=f$ everywhere.
  V samples $\vec\alpha\leftarrow\$\mathbb Z_q^n$; P sets
  $g(\vec x)=\sum_{i=0}^{n-1}\alpha_i\,f(\vec x)\,\widetilde{\mathrm{eq}}(\vec x,\vec u_i)$;
  sum-check for $\sum_{i}\alpha_iv_i=\sum_{\vec b}g(\vec b)$ reduces to checking
  $f(\vec r)=v$ (PCS) and $\widetilde{\mathrm{eq}}(\vec r,\vec u_i)=z_i$
  (verifier-computed) at the sum-check point $\vec r$.
- **Univariate @ multiple points:** rewrite $f(X)=\sum f_iX^i$ as multilinear in
  $X_i:=X^{2^i}$: $f(X_0..X_{\ell-1})=f_0+f_1X_0+f_2X_1+\dots+f_{N-1}X_0X_1\cdots
  X_{\ell-1}$; use $\vec u_i=(u_i,u_i^2,\dots,u_i^{2^{\ell-1}})$; reduces to the
  multilinear case.
- **Multiple @ multiple:** $g(\vec x)=\sum_i\alpha_if_i(\vec x)\,
  \widetilde{\mathrm{eq}}(\vec x,\vec u_i)$; sum-check; individual $f_i$ checks
  handled by the first case.

## 6. Soundness & Security

### 6.1 Completeness (Theorem 1)

With $\mathcal C$ bounded by $(\tau,T)$, per-round $\ell_\infty$ bounds
$\gamma_{\log N}:=(2T)^{\log N-1}$ and
$\gamma_{\alpha,\log N}:=\frac{\sigma_\alpha}{2}(2T)^{\log N-1}$; final $\ell_2$
admissibility $\gamma:=\sqrt{2\ell d}\,\gamma_{\log N}$ and
$\gamma_\alpha:=\sqrt{2\ell\iota_\alpha d}\,\gamma_{\alpha,\log N}$.
Proof: folding satisfies
$\lVert\vec s_{i+1}\rVert_\infty\le\lVert c_{i,0}\rVert_{\mathrm{op},\infty}
\lVert\vec s_{i,L}\rVert_\infty+\lVert c_{i,1}\rVert_{\mathrm{op},\infty}
\lVert\vec s_{i,R}\rVert_\infty\le2T\gamma_i$; initial $\gamma_1=1$ (binary) and
$\gamma_{\alpha,1}=\sigma_\alpha/2$ (base-$\sigma_\alpha$ digits); induction over
$\log N-1$ folds; $\vec s_{\log N}\in R_q^{2\ell}$, $\hat s_{\alpha,\log N}\in
R_q^{2\ell\iota_\alpha}$ give the $\sqrt{\cdot d}$ conversions. Fig. 2 is *perfectly*
complete.

### 6.2 Coordinate-wise special soundness (Theorem 2 / Theorem 6, App. C)

Assume M-SIS hard for rank $\kappa$ and norm bound

$$
\beta_{\text{M-SIS}}\ \ge\ \max\Big(\sqrt N\cdot\sqrt{N\ell}\,\gamma_{\log N},\ \sqrt N\cdot\sqrt{N\ell\iota_\alpha}\,\gamma_{\alpha,\log N}\Big)\qquad(\text{Eq. 4})
$$

Then Fig. 2 achieves **2-coordinate-wise 2-special soundness** with additional error

$$
\frac{4\log N}{|\mathcal C|}+\Big(\frac{2N\ell d}{q}\Big)^{t},
\qquad t:=\lambda\big/\Big\lceil\frac{\log q}{2N\ell d}\Big\rceil
$$

**Extraction structure (proof of Thm 6):** tree of $K=3^{\log N-1}$ accepting
transcripts organized per Definition 6 (three challenge vectors per round in
$\mathrm{SS}(\mathcal C,2,2)$ — a central vector plus two others differing in one of
the two coordinates each).

- **Step I — extract the relaxed opening.** Fix $\vec c_1..\vec c_{\log N-2}$, take
  three transcripts at round $\log N-1$ (Eqs. 5):
  $c^{(b)}_{\log N-1,0}\vec s^{(b)}_{\log N-1,L}+c^{(b)}_{\log N-1,1}\vec s^{(b)}_{\log N-1,R}
  =\vec s^{(b)}_{\log N}$ for $b\in\{0,1,2\}$, with
  $c^{(1)}_{\log N-1,1}\ne c^{(0)}_{\log N-1,1}$ and
  $c^{(2)}_{\log N-1,0}\ne c^{(0)}_{\log N-1,0}$. Extractor computes
  $\bar s_{\log N-1}:=\big(\frac{\vec s^{(1)}_{\log N}-\vec s^{(0)}_{\log N}}
  {\bar c_{\log N-1}^{(1)}},\frac{\vec s^{(2)}_{\log N}-\vec s^{(0)}_{\log N}}
  {\bar c_{\log N-1}^{(2)}}\big)$ with
  $\bar c^{(b)}_{\log N-1}=c^{(b)}_{\log N-1,\cdot}-c^{(0)}_{\log N-1,\cdot}$
  (differences of challenges — invertible by construction of $\mathcal C$). By
  linearity of the commitment, Eqs. (6)–(7):
  $\mathrm{Com}(\bar c\cdot\bar s_L)=\bar c\cdot A_0\vec s_L$ etc.; when
  $\bar c^{(1)}=\bar c^{(2)}$ (achievable for $\mathrm{SS}(\mathcal C,2,2)$ samples),
  $\lVert\bar c_{\log N-1}\cdot\bar s_{\log N-1}\rVert_\infty\le2\gamma_{\log N}$.
  Repeat the rewinding one level up (Eqs. for $\bar s_{\log N-2}$ with halves of
  halves; consistency $A_0(\bar c(\bar s_{L})_{L})=\bar c\,A_0(\vec s_L)_L$ etc.;
  $G$-decomposition gives $\mathrm{Com}(\bar c\bar s_{\log N-2,L})=A_1G^{-1}_{2\kappa}
  [\cdots]=\bar c\,\mathrm{Com}(\vec s_{\log N-2,L})$); after $\log N$ levels obtain
  $\bar s=(\frac{\bar s^{(1)}_2-\bar s^{(0)}_2}{\bar c_1},\frac{\bar s^{(2)}_2-
  \bar s^{(0)}_2}{\bar c_2})$ with
  $\mathrm{Com}(\bar c_2\bar s_L)=\bar c_2\mathrm{Com}(\vec s_L)$,
  $\mathrm{Com}(\bar c_2\bar s_R)=\bar c_2\mathrm{Com}(\vec s_R)$, and the norm bound
  $\big\lVert\prod_{i=1}^{\log N-1}\bar c_i\cdot\bar s\big\rVert_\infty\le
  2^{\log N-1}\gamma_{\log N}$, with $\bar c=\prod_i\bar c_i$, $\bar c_i\in\mathcal
  C-\mathcal C$. Identical procedure for $\hat s_\alpha$ (bound
  $2^{\log N-1}\gamma_{\alpha,\log N}$). The relaxed opening
  $(\bar s,\bar s_\alpha)$ satisfies $\mathrm{Com}(\bar c\,\bar s)=\bar c\,\mathrm{cm}$
  — a *scaled* M-SIS-style opening; the $\sqrt N$ factors in Eq. (4) come from
  unrolling this $\prod\bar c_i$ scaling against the $\ell_2/\ell_\infty$ conversion.
- **Step II — linear & quadratic constraints hold for the extracted witness.**
  From the three linear verification equations at the final round:
  $\langle\vec a_0,\vec s^{(b)}_{\log N}-\vec s^{(0)}_{\log N}\rangle=
  \langle\vec c^{(b)}_{\log N-1}-\vec c^{(0)}_{\log N-1},\pi^{(\mathrm{lin})}_{\log N-1}
  \rangle=\bar c^{(b)}\,v_{\log N-1,\cdot}$; dividing by $\bar c$:
  $\langle\vec a_0,\bar s_{\log N-1,L/R}\rangle=v_{\log N-1,L/R}$. Quadratic:
  substituting $\vec s_{\log N}=c_0\bar s_L+c_1\bar s_R$ into the quadratic check
  shows the verifier evaluates a degree-2 polynomial in $\vec c_{\log N-1}$ whose
  coefficients are exactly $(\langle\bar s_L,\sigma^{-1}(\bar s_L)\rangle,
  \langle\bar s_L,\sigma^{-1}(\bar s_R)\rangle,\langle\bar s_R,\sigma^{-1}(\bar
  s_L\rangle,\langle\bar s_R,\sigma^{-1}(\bar s_R)\rangle)$; if the claimed quartet
  differs from the true one, a nonzero degree-2 polynomial vanishes at a random
  challenge — Schwartz–Zippel $\le2/|\mathcal C|$ per round ⇒ overall quadratic
  soundness $\le2\log N/|\mathcal C|$; same for all linear/quadratic constraints.
- **Step III — binarity of the extracted $\bar s$.** The binary constraint
  $\vec s\circ(\vec s-\vec1)=\vec0$ was reduced to the randomized linear constraint
  $\langle\vec\alpha\circ\vec s,\vec s-\vec1\rangle=0$ (error $\le N\ell d/q$) plus
  the well-formedness check $\langle\vec s_\alpha,\vec r\rangle=\langle\vec s,\vec
  r\circ\vec\alpha\rangle$ (error $\le N\ell d/q$); with $t$ independent repetitions,
  $(2N\ell d/q)^t\le2^{-\lambda}$.

### 6.3 Knowledge soundness (Theorem 3)

Fig. 2 is knowledge-sound with total error
$\frac{6\log N}{|\mathcal C|}+\big(\frac{2N\ell d}{q}\big)^{t}$
(by Lemma 3's union-bound conversion of 2-coordinate-wise 2-special soundness with
error $4\log N/|\mathcal C|+(2N\ell d/q)^t$).

### 6.4 Composed scheme (Theorem 7, App. D)

FS + LaBRADOR compaction is knowledge-sound in the ROM under the standard adaptive
security definition with error $\epsilon_{\mathrm{se}}+\epsilon_{\mathrm{fs}}+
\epsilon_{\mathrm{La}}$: LaBRADOR's extractor returns witnesses satisfying the dot
product system ⇒ the NI Serval verification passes; ROM challenges are
indistinguishable from uniform ⇒ rewinding-and-reprogramming extractor obtains
diverging-challenge transcripts ⇒ Theorem 3 extractor applies.

### 6.5 Where slack would creep in (and why it doesn't)

- **No challenge-space shrinkage for tightness**: classical slack comes from bounding
  $\lVert\sum c_i\vec s_i\rVert$ via $\tau$ per folding — Serval *does* accumulate the
  operator-norm factor $(2T)^{\log N-1}$ in $\gamma$ (the *relaxed* opening bound),
  but that only feeds the **M-SIS hardness** side (Eq. 4: choose $d\log q$ big
  enough); it never multiplies the *extracted norm bound* $\beta$ because Step II
  recovers the *unscaled* linear/quadratic claims and Step III pins
  $\lVert\cdot\rVert_\infty=1$ exactly, and Lemma 2's wraparound argument is exact.
- **No JL projection**: LaBRADOR's $\approx2$ slack (modular Johnson–Lindenstrauss)
  is not used for the norm claim — only as an *optional compaction* layer whose
  witness blocks are re-verified by exact dot products.
- The price: $\ell=\lceil\log q\rceil$ witness expansion (base-2 digits) and $t$
  binary repetitions — both $O(\lambda)$-polylog factors, no asymptotic damage
  ($t\log q=O(\lambda)$, $\ell=O(\log q)$).

## 7. Parameters & Concrete Efficiency

### Table 2 — asymptotic parameters (with $N\cdot d=L$)

| Notation | Explanation | Instantiation |
|---|---|---|
| $q$ | prime modulus, $q\equiv5\bmod8$ | $\log q=O(\log^2N/\log\lambda)$ |
| $d$ | ring dimension | $\Theta(\lambda)$ |
| $\kappa$ | height of matrices $A_i$ | $O(1)$ |
| $\tau$ or $T$ | ℓ2 / operator-norm challenge bound | $O(1)$ |
| $\mathcal C$ | challenge space | $|\mathcal C|\approx2^\lambda$ |
| $(\sigma,\sigma_\alpha)$ | decomposition bases | $O(q^{1/O(1)})$ |
| $(\iota,\iota_\alpha)$ | decomposition pieces | $O(1)$ |
| $(\gamma_{\log N},\gamma_{\alpha,\log N})$ | folded ℓ∞ bounds | $O(q^{1/O(1)}\cdot\sqrt N)$ |
| $t$ | binary-check repetitions | $t\cdot\log q=O(\lambda)$ |

M-SIS heuristic (Micciancio–Regev / Becker–Ducas–Gama–Laarhoven): hard when
$\beta_{\text{M-SIS}}\le\min\big(2^{2\sqrt{d\log q\log\delta}},\ q\big)$ with root-Hermite
$\delta=(\frac{b_k(\pi b_k)^{1/b_k}}{2\pi e})^{1/(2(b_k-1))}$, $b_k=O(\lambda)$;
rearranged $d\log q>\log^4\beta_{\text{M-SIS}}/\log^2\delta$; with
$\log\beta_{\text{M-SIS}}=O(\log N+\log\ell)$, $\log\delta=\Theta(\log\lambda/\lambda)$,
$\log\ell=\log\log q$: $d\log q=O(\lambda\log^2N/\log\lambda)$; set $d=\Theta(\lambda)$
⇒ $\log q=O(\log^2N/\log\lambda)$; then
$t=\lambda\log\lambda/\log^2N=\Theta(\lambda/\log\lambda)$ and $t\log q=O(\lambda)$.

### Table 3 — asymptotic efficiency

| Proof size (bits) | Prover cost (ring ops) | Verification cost (ring ops) |
|---|---|---|
| $O((\ell+\log N)\cdot\lambda^2)$ | $O(t\ell N)$ | $O((t+1)\log N+t\ell)$ |

Details: per round $i<\log N$, $|\pi_i|=(2\kappa i+6)+t\cdot(2\kappa i+10)$ ring
elements... — precisely $|\pi_i|=\big((2\kappa i+6)+t\cdot(2\kappa i+10)\big)\cdot d\log q$
bits; final round $|\pi_{\log N}|=(2\ell+2t\ell\iota_\alpha)\cdot d\log q$; total
$\le O(\log N+\ell)\cdot(2\kappa\iota+10)\cdot t\,d\log q=O((\ell+\log N)\lambda^2)$ bits.
Prover: geometric series over rounds of length-$N\ell/2^{i-1}$ (and $N\ell\iota_\alpha/
2^{i-1}$ per repetition) ⇒ $O(\ell N+t\ell N)$. Verifier: $O(t+1)$ ring ops per round
× $\log N-1$ rounds + $O(t\ell)$ final + $O(t(\ell d+\log N))$ field ops for
challenge-vector construction (base vectors $\vec\alpha_0,\vec r_0,\vec r_{\alpha,0}$
of length $2\ell d$ + $\log N$ length-2 vectors by repeated squaring); one ring op ≈
$O(d\log d)$ field ops.

### Table 4 — concrete parameters & proof sizes ($L=2^e$)

| $e$ | 15 | 16 | 17 | 18 | 19 | 20 | 22 | 24 | 26 | 28 | 30 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $\log q$ | 88 | 100 | 108 | 120 | 128 | 128 | 84 | 94 | 104 | 114 | 124 |
| $d$ | 64 | 64 | 64 | 64 | 64 | 64 | 64 | 64 | 64 | 64 | 64 |
| $\kappa$ | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 |
| $\iota$ | 5 | 5 | 5 | 5 | 5 | 8 | 5 | 5 | 5 | 5 | 5 |
| Raw (MB) | 2.01 | 2.40 | 2.73 | 3.17 | 3.54 | 5.45 | 11.27 | 14.14 | 17.22 | 20.72 | 24.43 |
| Opt. | 259.16 KB | 302.88 KB | 337.03 KB | 385.22 KB | 423.03 KB | 436.03 KB | 1.97 MB | 2.24 MB | 2.73 MB | 3.15 MB | 3.59 MB |

(Opt. = analytic LaBRADOR-compacted estimate from [9]'s formulas + $\log q$-bit ring
encoding; not measured. Note $\log q$ *decreases* for $e\ge22$ (fixed 128-bit security
re-partitioned across larger $N$); $\iota=8$ at $e=20$ because $\log q=128$ with
$\sigma$ fixed.) Challenge space: 24 zeros/32 ±1/8 ±2 over $d=64$,
$|\mathcal P|\approx2^{128}$, $T=48$.

### Table 1 — comparison among post-quantum PCSs (128-bit, prover→verifier bytes)

| Work | Basis | Slack | T.S. | $L=2^{15}$ | $2^{20}$ | $2^{25}$ | $2^{30}$ |
|---|---|---|---|---|---|---|---|
| Brakedown [25] | Hash | N/A | ✓ | 5.32 MB | 10.25 MB† | 50.34 MB | 186.31 MB† |
| Basefold [39] | Hash | N/A | ✓ | – | 6.11 MB | – | – |
| Fenzi et al. [22] | BASIS | poly(L) | × | 3.4 MB | – | 8.3 MB | – |
| SLAP [3] | M-SIS | poly(L) | × | – | 36.5 MB | – | 767 MB |
| Greyhound [36] | M-SIS | poly(L) | ✓ | – | – | 46 KB | 53 KB |
| Cini et al. [19] | M-SIS | ≈2 | ✓ | 120 KB | 501 KB | 1.51 MB | 5.17 MB |
| **Serval (ours)** | M-SIS | **1** | ✓ | 259.16 KB | 436.03 KB | 2.56 MB | 3.59 MB |

### Table 5 / Fig. 6 — ring-operation counts vs Greyhound (common $(q,d)$)

| Phase | Greyhound prover | Serval prover | Greyhound verifier | Serval verifier |
|---|---|---|---|---|
| Init. | $\sqrt N+\kappa\sqrt N$ | $N$ | $N$ | $8\ell+\frac{(\iota+1)(\kappa+\ell)}{4\kappa^2\iota+12}$ |
| Mid. (per level) | – | $N$ | $4\ell+\frac{(\iota+1)(\kappa+\ell)}{4}$ | $(8\kappa^2\iota+28)(\log N-2)$ |
| Final | $\sqrt N\,\iota(\kappa+2\sqrt\kappa+4)$ | $2\ell(1+\iota)$ | $N\big(\iota(\kappa+2\sqrt\kappa+4)+\kappa+1+2\kappa\iota\big)+16$ | $\ell(12+2\kappa+4\iota^2\kappa\iota)+16$ |

Reading: for small $N$ Serval's verifier can be modestly more costly (explicit norm
checks, small gap between $\sqrt N$ and $\log N$); as $N$ grows the polylogarithmic
verifier dominates favorably; prover overhead ratio is stable, driven by $\ell$.

### Prototype & benchmarks (§5.2)

- Hardware: Apple Silicon M2, 16 GB unified memory. Code:
  gitlab.com/LatticePCSReview/servalPCS. Covers the *baseline interactive* protocol of
  Fig. 2 only (no LaBRADOR compaction — the reference labrador implementation was not
  stable on their platform).
- Microbenchmarks cover commitment / linear / quadratic sub-proofs; the binary proof
  is treated as a composition of those three and omitted from micro numbers.
- Fixed $q$ of 100 bits across all $N$ (single build); small-coefficient challenges
  $\{0,\pm1\}$ with operator-norm target $T=9$; **full protocol run twice via parallel
  repetition** to target ≥90-bit security in that configuration.
- Implementation: NTT-based ring multiplication; batched matrix-vector multiplication;
  no SIMD, no multi-threaded accumulation (conservative reference numbers).
- Findings: prover time grows linearly in $N$ as expected; verification dominated by
  the *commitment* proof (matrix-vector products); linear/quadratic checks
  lightweight; proof size dominated by the commitment proof (folded intermediate
  commitment state).

## 8. Implementation Notes (for the `lzk` Python core engine)

### 8.1 Data structures

- `RingPoly`: $d$ coefficients over $\mathbb Z_q$ with centered representatives;
  NTT-based negacyclic multiplication ($X^d+1$) — direct reuse of `lzk`'s
  $\mathbb Z_q[x]/(x^n{+}1)$ NTT core.
- `Conjugate` map $\sigma^{-1}$: index reversal $X^i\mapsto X^{d-i}$ (since
  $X^{-i}\equiv X^{d-i}\bmod X^d+1$... careful: $X^{-i}= -X^{d-i}$ for the
  $X^d\equiv-1$ relation — implement as $f_i\mapsto f_{(d-i)\bmod d}$ with sign
  $(-1)$ on the $i=0$↔$i=d$ wrap; unit-test with
  $\mathrm{ct}\langle\vec a,\sigma^{-1}(\vec b)\rangle=\langle\vec a,\vec b\rangle$).
- `LeveledCommitment`: matrices $(A_0..A_{\log N-1},B_0..B_{\log N-1})$, private state
  list $\{\mathrm{cm}_{\mathrm{min},i}\}$; supports `commit`, `fold(c0,c1)` on both
  witness and state, `open_final`.
- `GadgetDecomp(base, levels)`: base-$\sigma$ digit expansion per coefficient
  ($\iota=\lceil\log_\sigma q\rceil$ digits, each $<\sigma$); `G` reconstruction =
  weighted sum with powers $\sigma^j$.
- `TensorEvalVector`: the $\log N$ factors $(\vec a_0\in\mathbb Z_q^{2\ell d},
  \vec a_i\in\mathbb Z_q^2)$; final-round packed $\vec a_0\in R_q^{2\ell}$ built by
  packing $d$ consecutive entries per ring element *with the same packing layout as
  the witness* (see pitfall 8.3).
- `ChallengeSampler`: Fisher–Yates over the multiset $[0^{24},1^{32},2^8]$, signs
  from PRG bits (Algorithm 1); deterministic re-derivation from
  $H(\mathrm{Com}(\mathrm{tr}_{i-1}))$.
- `ServalProof`: rounds $\{\pi_i^{(\mathrm{cm})},\pi_i^{(\mathrm{lin})},
  \pi_i^{(\mathrm{qua})},\{\pi_i^{(\mathrm{bin},j)}\}\}$ + final
  $(\vec s_{\log N},\{\hat s^{(j)}_{\alpha,\log N}\})$.

### 8.2 Algorithms to build (priority order)

1. **Packing + base-2 decomposition** $\vec f\in\mathbb Z_q^{Nd}\to\vec s\in
   R_q^{N\ell}$: pack $d$ coefficients per ring element; each coefficient $\to\ell=
   \lceil\log q\rceil$ bits; reorder so that the $\ell$ digits of one coefficient
   occupy consecutive positions *within one ring element block of length $2\ell$-style
   layout used by $\vec a_0\otimes(1,2,..,2^{\ell-1})$* — the tensor structure
   requires factor-0 length exactly $2\ell d$ (i.e. $2\ell$ ring elements).
2. **Leveled commitment** + intermediate-state maintenance + fold operation.
3. **Linear split-and-fold** with tensor-decomposed public vectors (§5.2): per round,
   split $(\vec s_L\Vert\vec s_R)$, send $(v_{i,L},v_{i,R})$, verify
   $\mathrm{ct}\langle\vec a_{\log N-i},\pi_i\rangle=\langle\vec c_{i-1},\pi_{i-1}\rangle$.
4. **Quadratic split-and-fold** with cross terms + $\vec c^{(\mathrm{qua})}$ fold
   vector (uses $\sigma^{-1}$ multiplicativity).
5. **Binary sub-proof**: $\vec s_\alpha$ construction (coefficient-wise multiply by
   powers of $\alpha$ — compute via Horner/repeated-squaring batches to avoid
   $O((N\ell d)^2)$), $\hat s_\alpha$ decomposition, the 5 claims, $t$ repetitions.
6. **FS + (optional) LaBRADOR compaction**: start without compaction (matches the
   paper's own prototype); add later.
7. **Batching** (App. E): multi-poly@point (trivial RLC), poly@points (sum-check +
   $\widetilde{\mathrm{eq}}$ — reuses `lzk`'s multilinear sumcheck + eq machinery).

### 8.3 Complexity & memory

- Prover $O(t\ell N)$ ring ops: each round halves the active witness; keep only the
  current folded witness + current folded intermediate commitments ⇒ peak memory
  $O(\ell N)$ ring elements + $t$ auxiliary witnesses $\hat s_\alpha^{(j)}$
  ($O(t\ell\iota_\alpha N)$ — dominant for large $t$; consider streaming/f
  rejection-free construction).
- $\vec s_\alpha$ construction: naive coefficient-wise power multiplication is
  $O(N\ell d)$ multiplications of *powers of $\alpha$* — precompute
  $\alpha^{2^i\cdot2\ell d}$ per tensor level and multiply block-wise via the tensor
  structure (each block of length $2\ell d$ shares one geometric progression; use
  prefix products), total $O(N\ell d)$ field ops.
- Verifier: per round constant ring ops (mostly small matrix-vector with $2\times2^i\kappa$
  matrices — precompute nothing; the matrices $A_{\log N-i}$ are public and small);
  final round $O(t\ell)$ ring ops; challenge-vector construction
  $O(t(\ell d+\log N))$ field ops.

### 8.4 Pitfalls (hard-won, from the paper's fine print)

1. **Commitment ordering in the binary proof is a security requirement, not a
   style choice.** $r$ must be sampled *after* the prover commits to $\hat s_\alpha$;
   knowing $(\alpha,r)$ in advance lets a cheating prover fabricate $\tilde s_\alpha$
   matching the required inner products at the single point $r$ while differing
   elsewhere. Under FS, derive $\alpha$ from $(\mathrm{cm},\ldots)$, then $r$ from
   $(\mathrm{cm},\{\mathrm{cm}_\alpha^{(j)}\},\{v_\alpha^{(j)}\})$.
2. **Wraparound regime must actually hold.** Lemma 2 needs $q>2N\ell d$ *for the
   committed witness*; with $\ell=\lceil\log q\rceil$ this ties $\log q$ to $\log N$
   (Table 4's non-monotone $\log q$ column!). Recompute the inequality for every
   parameter set; also the *statement* check $0\le b\le\beta^2$ uses the *centered*
   representative of $b$ — implement `centered(b)`.
3. **Packing layout consistency.** The tensor factor $\vec a_0$ has length $2\ell d$
   scalars = $2\ell$ ring elements; the digits of one coefficient must sit in the
   *same ring element positions* that $\vec a_0$'s base-2 weights multiply. A layout
   mismatch between $\mathrm{Commit}$ (Fig. 4) and $\mathrm{Eval}$'s $\vec a_i$
   construction silently breaks Eq. (2)'s inner product (completeness failure at
   random points).
4. **$\sigma^{-1}$ signs.** $X^{-i}\equiv -X^{d-i}\pmod{X^d+1}$ — the naive index
   flip forgets the sign on the wrapped coefficient; the ct⟨·,·⟩ identity (§2.1) is
   the right unit test.
5. **Shared challenges, sent-once witness.** All sub-proofs (cm/lin/qua/bin, all $t$
   repetitions) fold with the *same* $\vec c_i$ and the final folded witness is sent
   once. Divergent challenges per sub-proof break the extraction (Step I's linear
   unscaling assumes one common $\bar c$ per level).
6. **Quadratic recursion direction.** Note the fold vector ordering:
   $\vec c^{(\mathrm{qua})}=(c_0\sigma^{-1}(c_0),\,c_1\sigma^{-1}(c_1),\,
   c_0\sigma^{-1}(c_1),\,c_1\sigma^{-1}(c_0))$ pairs with
   $\pi^{(\mathrm{qua})}=(L,M^{(1)},M^{(2)},R)$ where $M^{(1)}=\langle\vec s_L,
   \sigma^{-1}(\vec s_R)\rangle$, $M^{(2)}=\langle\vec s_R,\sigma^{-1}(\vec s_L)\rangle$
   — cross-pairing $M^{(1)}\leftrightarrow c_1\sigma^{-1}(c_0)$ is the classic bug;
   verify against the expansion formula in §5.3.
7. **Fig. 2 vs Fig. 3 argument ambiguity in the binary linear checks.** §3.4's prose
   ("Final binary linear check") lists
   $\langle\vec r_{\alpha,0},G_{\sigma_\alpha,2\ell}\cdot\hat s_{\alpha,\log N}\rangle
   =\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_2,\alpha)}\rangle$ and
   $\langle\vec r_0,\vec s_{\log N}\rangle=\langle\vec c_{\log N-1},\pi_{\log N-1}^{(\mathrm{lin}_3,\alpha)}\rangle$,
   while Fig. 3 Step 3 has
   $\langle\vec r^{(j)}_0,\hat s^{(j)}_{\alpha,\log N}\rangle=\langle\vec c,\pi^{(\mathrm{lin}_1,\alpha)}\rangle$,
   $\langle\vec r^{(j)}_{\alpha,0},\vec s_{\log N}\rangle=\langle\vec c,\pi^{(\mathrm{lin}_2,\alpha)}\rangle$,
   $\langle\vec\alpha^{(j)}_0,\vec s_{\log N}\rangle=\langle\vec c,\pi^{(\mathrm{lin}_3,\alpha)}\rangle$.
   The five claims (d) fix the intended semantics: lin₁ =
   $\langle\vec r,\hat s_\alpha\rangle$ (claim 4, on $G$-reconstructed
   $\vec s_\alpha$), lin₂ = $\langle\vec r_\alpha,\vec s\rangle$ (claim 3), lin₃ =
   $\langle\vec\alpha,\vec s\rangle$ (claim 2). Implement the five-claim semantics;
   treat the §3.4 sentence as a garbled variant (the $G_{\sigma_\alpha,2\ell}$ prefix
   belongs to the quadratic claim 5's first argument, and to claim 4's
   $G_{\sigma_\alpha,N\ell}\hat s_\alpha$ reconstruction).
8. **$\gamma$ admissibility vs $\beta$ binding.** The final-round checks use
   $\lVert\vec s_{\log N}\rVert\le\gamma$ (folded-norm bound, completeness side),
   while M-SIS binding of the *leveled* commitment needs Eq. (4)'s
   $\beta_{\text{M-SIS}}$ — two different bookkeeping chains ($\gamma$ from
   $(2T)^{\log N-1}$; $\beta_{\text{M-SIS}}$ from the extractor's scaled witnesses).
   Don't conflate; both must be checked at parameter selection.
9. **Challenge sampler determinism.** The verifier re-derives $\vec c_i$ from the
   *committed* transcript prefix; the Fisher–Yates bit consumption order and the
   sign-bit order must be bit-exact between prover and verifier (specify endianness
   of `next bits`).
10. **$t$ repetitions vs soundness target.** Error $(2N\ell d/q)^t$: with the Table 4
    parameters this is fine, but any custom $q$ must satisfy
    $t=\lambda/\lceil\log q/(2N\ell d)\rceil$ — and if $2N\ell d\ge q$ the per-check
    error is ≥1 and repetition never converges (wraparound regime again).
11. **Univariate @ multiple points needs the $X^{2^i}$ regrouping** (App. E) —
    the evaluation points become $(u,u^2,\dots,u^{2^{\ell-1}})$; do not feed raw $u_j$
    into the multilinear path.
12. **Zero-knowledge is not provided.** The witness norm $b$ is *revealed* in the
    statement; the paper notes ZK can be added by hiding the $\ell_2$ norm and
    range-proving it. For the lab: Serval as-is is an argument of knowledge, not ZK.
13. **LaBRADOR compaction moves to ROM** and its error $\epsilon_{\mathrm{La}}$ adds
    in; the seed-consistency constraints ($\mathrm{Com}(\mathrm{tr}_i)$ matching the
    transcript blocks) are easy to forget in the encoding — they are the glue that
    makes the FS challenges bind to the *actual* messages.

### 8.5 Reuse map from `lzk`

| Serval piece | `lzk` module |
|---|---|
| $R_q=\mathbb Z_q[X]/(X^d+1)$ arithmetic, NTT | ring core (negacyclic NTT) |
| Ajtai / leveled commitment + gadget $G^{-1}$ | Ajtai commitment + gadget decomposition |
| $\sigma^{-1}$ conjugation | new small utility over the ring core |
| tensor-decomposed evaluation vectors / eq powers | tensor/LDE engine |
| multilinear sum-check for batching (App. E) | multilinear sumcheck |
| FS hasher with domain separators | Fiat-Shamir module |
| ring-norm bookkeeping ($\ell_2/\ell_\infty$/op-norm) | ring-norm sumcheck utilities |

## 9. Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- ✅ The split-and-fold IPA engine with the quadratic cross-term quartet
  (L, M1, M2, R per round) and the exact-norm bookkeeping
  (t' = c²L + c·c'·M1 + c'·c·M2 + c'²R — the slack-free ℓ2 semantics).
- □ Not implemented: the leveled commitment with intermediate states, the
  binary sub-proof with the 5 claims, Algorithm 1 sampler, LaBRADOR
  compaction, the wraparound regime q > 2Nℓd.

**(replacing the placeholder)**

- DONE: the split-and-fold IPA engine with the quadratic cross-term quartet (L, M1, M2, R per round) and the exact-norm bookkeeping (t' = c^2 L + c c' M1 + c' c M2 + c'^2 R — the slack-free l2 semantics).
- NOT implemented: the leveled commitment with intermediate states, the binary sub-proof with the 5 claims, Algorithm 1 sampler, LaBRADOR compaction, the wraparound regime q > 2 N l d.
