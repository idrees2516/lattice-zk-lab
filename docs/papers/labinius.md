# LaBinius — Fast Lattice-Based Binary Polynomial Commitment Scheme — Deep Analysis & Implementation Spec

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | LaBinius – Fast Lattice-Based Binary Polynomial Commitment Scheme |
| **Authors** | Michał Osadnik (Aalto University), Gregor Seiler (IBM Research Europe, Zurich) |
| **Local text** | `papers_txt/labinius.txt` (3052 lines; squeezed copy `/tmp/sq/labinius.txt`, 2928 lines) |
| **Code** | `github.com/osdnk/labinius` (Rust + AVX-512 kernels; LaBRADOR recursion via FFI to the C LaZer/Dachshund implementation) |
| **Problem solved** | Lattice SNARKs couple commitment and constraint domains: (a) invertible challenge differences force *partially splitting* moduli (slow NTT); (b) constraint-field characteristic must equal commitment modulus $q$ (30–50-bit primes) ⇒ binary computations (hashes) need lifting + explicit mod-2 reductions + bitness checks. LaBinius **decouples** the two: commitment over a composite NTT-friendly modulus $q$; evaluation/arithmetic in a binary extension field, with **no bitness checks and no overhead over a binary arithmetisation**. |
| **Core technical idea** | Extraction **over the number field** $K=\mathbb{Q}(\zeta_f)$ instead of modulo $q$: challenge differences $\bar c_j$ are always invertible in $K$, so the extracted witness is a *rational* vector; binding of rational openings follows from SIS mod $q$ + shortness (no wrap-around over $R$); reduction mod the inert prime $p=2$ is well-defined because the challenge set is injective modulo 2. |
| **Headline results** | Keccak-256 / SHA-256 / BLAKE3 provers ≤1.2× the hash-based (Binius/Flock) provers, single core; ≥67,000 BLAKE3 compressions/s (≈4.3 MB/s); verification < 40 ms non-recursive; with LaBRADOR recursion prover < 2× and proof **< 100 KiB — smallest quantum-safe proof of a standard hash evaluation to date** (≈5× smaller than Binius/Flock at the largest sizes). |
| **Figures to transcribe** | Fig. 1 (reduction flows); Fig. 2 $\Pi_{\mathrm{sw}}$ (field switch); Fig. 3 $\Pi_{\mathrm{left\mbox{-}exp}}$; Fig. 4 $\Pi_{\mathrm{fold}}$; Fig. 5 (coefficient blocks / block products / carries of the LaBRADOR recursion); Def. 24 packed Ajtai commitment; Appendix A block constraint system, zero-part test, RNS limb constraints, gadget decompositions, no-wraparound lemma |
| **Lab role** | The lab's binary-track commitment: consumes the `lzk` GF(2^k) tower-field core (Binius-style front ends) *and* the Ajtai/NTT core (LaBRADOR-style back end); it is the bridge paper between the two halves of the lab and the natural PQ replacement for the Merkle/BaseFold layer of Binius/Flock |

### 1.1 The Gröbner-attack context (why prove *standard* hashes)

The paper's motivation section is a compact history of algebraic attacks on **arithmetization-oriented (AO) primitives** — the reason binary-native proving of standard hashes matters:

- Jarvis & Friday broken shortly after proposal ([ACG+19]); distinguishers on StarkWare-challenge Poseidon instances ([BCD+20]); attacks on reduced-round Poseidon, Feistel-MiMC, Rescue-Prime ([BBLP22]).
- **Gröbner-basis and resultant attacks** ([BBL+24] FreeLunch, [YZY+24], [BBB+25] improved resultants, [BBHN26]) lowered security estimates for Anemoi, Griffin, Rescue, and the original Arion spec ([RST23]→revised [CRST26] added rounds in response); reduced-round Poseidon/Poseidon2 challenge instances solved ([ZD25], [BBB+26]).
- Conclusion drawn by the authors (echoing Drake's "Goodbye Poseidon" [Dra26]): with efficient *binary* provers one can keep **standard** hashes (Keccak/SHA-2/BLAKE3) instead of selecting a primitive for its algebraic proof cost — removing an entire attack surface (the AO-Gröbner arms race) from the system.
- Ethereum post-quantum transition quantified: stateless-client witnesses ≈10 MB/block over binary hash trees; proofs replace them by a few hundred KB; worst case ≈660,000 branch hashes to prove within seconds of a 12 s slot ⇒ target ≈200,000 hashes/s; aggregating ≈28,000 attestations/slot is the same order.

**Lab implication:** the Gröbber modules the lab builds for the ProtogaLattice/SALSAA tracks (P0-4: ring-Gröbner reduction over $\mathbb{Z}_{2^k}$-tower ideals) are the *attack-side* toolkit; LaBinius is the *defense-side* response — avoid AO primitives entirely by making standard hashes cheap to prove. Both tracks justify each other in the lab's docs.

---

## 2. Notation Table (EVERY symbol)

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter (concrete target: 100 bits) |
| $[n]$ | $\{0,\dots,n-1\}$ (0-indexed, like Cyclo, unlike Symphony) |
| $\mathrm{bin}(i)$ | little-endian binary expansion of $i\in[2^\nu]$; $\{0,1\}^\nu$ identified with $[2^\nu]$ |
| $[\pm q/2]$ | $\{-\lceil q/2\rceil+1,\dots,\lfloor q/2\rfloor\}$ balanced representatives; all reductions return balanced reps |
| $f$ | cyclotomic conductor, **odd**, with $2$ a primitive root mod $f$: $\mathrm{ord}_f(2)=\varphi$ |
| $K$ | $\mathbb{Q}(\zeta_f)$, the $f$-th cyclotomic number field (⚠️ not the extension field — this paper uses $\mathbb{F}$/$\mathbb{T}$ for fields) |
| $R$ | $\mathbb{Z}[\zeta_f]$, ring of integers, power basis $(\zeta_f^i)_{i\in[\varphi]}$ |
| $q$ | commitment modulus, **composite allowed** (product of 2–3 small fully-splitting NTT-friendly primes) |
| $p$ | evaluation prime; the paper uses $p=2$ throughout ("this regime is relevant to the main application") |
| $R_q$, $R_p$ | $R/qR$, $R/pR$ |
| $\varphi=\varphi(f)$ | degree; concrete $f=3^5=243$, $\varphi=2\cdot3^4=162$ |
| $\Phi_f(x)$ | $x^{162}+x^{81}+1$ for $f=3^5$ (general $f=3^\kappa$: $x^\varphi+x^{\varphi/2}+1$) |
| $\mathrm{coeff}(x)$ | coefficient vector over the power basis; $\|x\|=\|\mathrm{coeff}(x)\|_2$; $\|v\|=\sum\|v_i\|$; $\|W\|$ = column-wise max |
| $\|x\|_{\mathrm{op}}$ | $\sup_{y\neq0}\|xy\|/\|y\|$ |
| $\mathbb{F}$ | $R_2=R/2R$ — **binary residue field of degree $\varphi$** (Lemma 1): $\mathbb{F}\cong\mathbb{F}_2[x]/(x^{162}+x^{81}+1)$ |
| $\mathbb{T}$ | source/tower field of degree $2^\iota$ (concrete $\mathbb{F}_{2^{128}}$ in GHASH basis, modulus $x^{128}+x^7+x^2+x+1$) |
| $\iota$ | switch parameter, $\log_2\deg\mathbb{T}$ (concrete 7) |
| $m,r$ | witness matrix dimensions: $W\in R^{m\times r}$, $mr=2^\nu$ ring elements |
| $n$ | commitment width: $F\in R_q^{n\times m}$, $Y\in R_q^{n\times r}$ |
| $N=mr$ | total ring elements in the witness |
| $\nu$ | $\log_2(mr)$ — multilinear variable count |
| $F$ | public random Ajtai matrix (over superring $S$, see below) |
| $W$, $Y$ | witness matrix ($W\in S^{m\times r}$), commitment $Y=FW\bmod q$ with columns $y_i=Fw_i$ |
| $\beta$ | honest norm bound ($\sqrt{\varphi m}$ for binary $W$); $\beta'=r\gamma_C\beta$ folded |
| $\mu$ | slack operator-norm bound |
| $s\in R^r$ | slack vector: $\|s_i\|_{\mathrm{op}}\le\mu$, $s_i\notin2R$ |
| $C\subseteq R$ | folding challenge set, **injective modulo 2**, expansion factor $\gamma_C=\max_{c\in C}\|c\|_{\mathrm{op}}$ |
| $c\leftarrow C^r$ | folding challenge vector |
| $v=Wc$ | amortised (right) opening, $v\in R^m$ |
| $u^T=\alpha^TW$ | left opening / partial evaluation |
| $\alpha,\beta$ (eval) | multilinear interpolation coefficient vectors at the row/column split of the evaluation point (⚠️ $\beta$ overloaded with norm bound) |
| $\mathrm{eq}(x,y)$ | equality polynomial $\prod_i(x_iy_i+(1-x_i)(1-y_i))$ — integer coefficients, defined over any commutative ring |
| $\widetilde{\mathrm{eq}}(r)$ | evaluation vector $(1-r_{\nu-1},r_{\nu-1})\otimes\cdots\otimes(1-r_0,r_0)\in\mathcal{A}^{2^\nu}$ (little-endian tensor order) |
| $\mathrm{MLE}[a]$ | multilinear extension of $a$: $\langle\widetilde{\mathrm{eq}}(r),a\rangle$ (Eq. 1) |
| $\mathrm{vec}(W)$ | column-major vectorisation (row $i$, column $j$ ↦ index $jm+i$) |
| $\rho$ | field-switch randomiser $\in\mathbb{F}^\iota$ |
| $E(r)\in\mathbb{F}_2^{2^\iota\times2^\nu}$ | basis-decomposition matrix of $\widetilde{\mathrm{eq}}(r)$: $\widetilde{\mathrm{eq}}(r)^T=\theta^TE(r)$ over $\mathbb{T}$ |
| $\theta=(\theta_k)_{k\in\{0,1\}^\iota}$ | fixed $\mathbb{F}_2$-basis of $\mathbb{T}$ (concrete: GHASH monomial basis) |
| $\varphi:\mathbb{T}\to V\subseteq\mathbb{F}$ | **field-switch packing**: $\mathbb{F}_2$-linear bijection, $\varphi(\theta_k)=\eta_k$ (⚠️ $\varphi$ also Euler totient — disambiguate!) |
| $V$ | $\mathrm{span}_{\mathbb{F}_2}\{\eta_k\}\subseteq\mathbb{F}$; concrete: first 128 power-basis coordinates of $\mathbb{F}$ |
| $P_V$ | $\mathbb{F}_2$-linear projection $\mathbb{F}\to V$ (keeps $\eta_k$-coordinates, zeroes the rest) |
| $\mathrm{lift}:\mathbb{L}\to R$ | binary lift: coordinates over the fixed $\mathbb{F}_2$-basis ↦ coefficients over the power basis of $R$ |
| $\omega\in\mathbb{T}^{2^\iota}$ | within-word weight vector on the partial evaluations (Binius/Flock integration) |
| $S$ | commitment **superring** $\mathbb{Z}[\zeta_{8f}]\cong\mathbb{Z}[x]/(x^{648}-x^{324}+1)$, conductor $2^3\cdot3^5$; free rank-4 module over $R$ |
| $\Xi^{\mathrm{lin\mbox{-}rel}}$, $\Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}$, $\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}rel}}$, $\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw\mbox{-}rel}}$, $\Xi^{\mathrm{sis}}$, $\Xi^{\mathrm{eval}}$ | relations — Section 4 |
| $\mathrm{par}$ tuples | parameter bookkeeping: $\mathrm{par}_{\mathrm{in}},\mathrm{par}_{\mathrm{out}},\mathrm{par}'_{\mathrm{in}},\ldots$ chain through reductions |
| $\delta,\kappa$ | correctness / knowledge errors |
| $\gamma_C$ | expansion factor of $C$ |
| $B_v,B_{z'}$ | folded-witness / residual norm bounds (bit dropping) |
| $d$ (drop) | number of dropped low bits in bit-dropped commitments (⚠️ also LaBRADOR ring degree) |
| $Q$ | LaBRADOR modulus (prime over $R'_Q$) |
| $R'_Q$ | LaBRADOR ring $\mathbb{Z}[\zeta_{f'}]/Q$, $f'=2^{\mathrm{d}}$, $R'_Q\cong\mathbb{Z}_Q[x]/(x^{\mathrm{d}}+1)$ (power-of-two cyclotomic) |
| $c,p$ (App. A) | chunk length / block length: $c+p-1\le\mathrm{d}$, $p\mid\varphi/2$ |
| $N=\varphi/p$ | #coefficient blocks; $A=[N]$ block indices, $B=[\lceil\varphi/c\rceil]$ chunk indices |
| $y^{\langle a\rangle}$, $x^{[b]}$, $g^{[b,a]}$ | coefficient block of $y$; witness chunk of $x$; public coefficient block of $g$ at $(b,a)$ |
| $\mathrm{Enc}_c,\mathrm{Dec}_c$ | chunk encoding/decoding maps $R_Q\leftrightarrow R'^{|B|}_Q$ |
| $D_a$, $e_a$ | block product sum / carry out of block $a$ |
| $q_\ell$ | the $\ell$-th prime factor of $q$; $\ell_{\max}$ #factors |
| $k_\ell$ | limb quotient: $F_\ell v-Y_\ell c=q_\ell k_\ell$ |
| $w_b,w_e$ | binary quotients: $\mathrm{lift}(B)v-\sum c_j\tilde u_j=2w_b$; $\sum\mathrm{lift}(e_j)\tilde u_j-\mathrm{lift}(t)=2w_e$ |
| $\mathcal{D}_B$, $B$ (gadget) | balanced digit set $[-B/2,\dots,B/2-1]$; base-$B$ gadget decomposition $x=\sum_jB^jx^{(j)}$ |
| $T_Y,T_u,T_R$ | LaBRADOR pre-commitments to residue vectors / left expansion / chunk+gadget vectors |
| $\rho_{\xi,j}^{(h)}$ | zero-test randomisers |

---

## 3. Algebraic Setting

### 3.1 Cyclotomic rings with two inert (the "odd conductor" move)

- **Definition 1**: $f$ odd with $\mathrm{ord}_f(2)=\varphi$; $K=\mathbb{Q}(\zeta_f)$; $R=\mathbb{Z}[\zeta_f]$; balanced identification of $R_q$ elements with short lifts of $R$.
- **Lemma 1 (inertness)**: $2R$ is **prime** and $R/2R=\mathbb{F}$ is the field with $2^\varphi$ elements. (Since $p\nmid f$ factors into $\varphi/d$ prime ideals of residue degree $d=\mathrm{ord}_f(p)$; for $p=2$, $d=\varphi$ forces a single factor.)
- **Remark 1 (powers of three)**: $f=3^\kappa$ works for every $\kappa\ge1$ ($2$ is a primitive root mod $3$ and $2^{3-1}\not\equiv1\bmod9$ lifts by the standard criterion), giving $\mathbb{F}=\mathbb{F}_{2^{2\cdot3^{\kappa-1}}}$. Concrete: $f=3^5=243$, $\varphi=162$, $\mathbb{F}\cong\mathbb{F}_2[x]/(x^{162}+x^{81}+1)=\mathbb{F}_{2^{162}}$.
- **The mod-2 reduction is a ring homomorphism** $R\to\mathbb{F}$; $x\bmod2$ invertible iff $x\notin2R$. Everything "binary" in the scheme is read through this map — **no separate bitness proof is ever needed**: the *extracted* rational witness's reduction mod 2 *defines* the binary coefficients the arithmetised statement refers to.

### 3.2 Norms, SIS, and challenge sets

- SIS (Def. 4–5): $\Xi^{\mathrm{sis}}_{R,q,m,n,\beta}=\{(F,x):F\in R_q^{n\times m},x\in R^m,\|x\|\le\beta,Fx=0\bmod q,x\neq0\}$; hardness at $2^{-\lambda}$.
- **Definition 6 (folding challenge sets)**: $C\subseteq R$ finite, expansion factor $\gamma_C=\max_{c\in C}\|c\|_{\mathrm{op}}$; $C$ **injective modulo 2** iff $c-c'\notin2R$ for distinct $c,c'$ — the *only* invertibility requirement, replacing the usual "differences invertible in $R_q$" that forces partially-splitting $q$.
- **Lemma 2 (signed binary challenges)**: $\mathcal{B}=\{\sum b_i\zeta_f^i:b\in\{0,1\}^\varphi\}$ — every subset is injective mod 2 (reduction maps $\mathcal{B}$ bijectively onto $\mathbb{F}$); sign-flipping via a public hash $s_H(c)=\sum H(c)_ib_i\zeta_f^i$ keeps the mod-2 image while centring the coefficients ($\{-1,0,1\}$ entries) for average-case norm analysis. Concrete instantiation: **fixed Hamming weight, non-zero coefficients in $\{-1,1\}$**, support sampled by partial Fisher–Yates, signs from a keyed hash; operator norm controlled via Fourier-slot energy (§5.1.3).

### 3.3 Coordinate-wise extraction machinery

- **Definition 7 / Lemma 3** ([FMN24] L7.1): CWSS families $\mathrm{SS}(S,\ell,k)$ with central index $e$; the forking extractor outputs $\ell(k-1)+1$ accepting transcripts with challenges differing in single coordinates, success $\ge\epsilon_V(A)-\ell(k-1)/N$, at most $\ell(k-1)+1$ expected oracle calls. LaBinius uses $k=2$ (pairs differing in one coordinate).

### 3.4 Multilinear machinery over arbitrary commutative rings

- Equality polynomial with *integer* coefficients ⇒ defined over $\mathbb{F},\mathbb{T},R,R_q$ alike; $\widetilde{\mathrm{eq}}(r)$ in little-endian tensor order.
- **Lemma 4 (bilinear evaluation)**: for $W\in\mathcal{A}^{m\times r}$ and $r^T=(r_0^T\ r_1^T)$ with $\log m+\log r=\nu$ variables:
  $$\widetilde{\mathrm{eq}}(r)=\widetilde{\mathrm{eq}}(r_1)\otimes\widetilde{\mathrm{eq}}(r_0),\qquad \mathrm{MLE}[\mathrm{vec}(W)](r)=\widetilde{\mathrm{eq}}(r_0)^TW\widetilde{\mathrm{eq}}(r_1).$$
  (Column-major vectorisation + little-endian order make the first block of variables index *rows* and the second *columns* — this single identity powers $\Pi_{\mathrm{left\mbox{-}exp}}$.)
- Sumcheck (Def. 11/Lemma 6): degree-$d$, $\ell$ rounds, soundness $\ell d/|L|$; PIT root bound (Lemma 5, [BCPS18]): $\Pr[f(r)=0]\le D/|S|$.

### 3.5 Field switching: tower field ↔ binary residue field

- No field embedding $\mathbb{T}\to\mathbb{F}$ exists in general (degree mismatch: $2^\iota\nmid\varphi$); the switch uses only the **common $\mathbb{F}_2$-linear structure**:
  - **Definition 12 (field-switch packing)** $\varphi:\mathbb{T}\to V\subseteq\mathbb{F}$ with $\varphi(\theta_k)=\eta_k$ on bases; projection $P_V:\mathbb{F}\to V$.
  - **Definition 13 (binary lift)**: $\mathrm{lift}(\sum b_i\theta_i)=\sum b_i\zeta_f^i$ — coordinates become power-basis coefficients; likewise for $\mathbb{F}$ with the reduced power basis $(\zeta_f^i\bmod2)$.
  - **Definition 14 / Lemma 7**: $E(r)\in\mathbb{F}_2^{2^\iota\times2^\nu}$ holds the $\theta$-coordinates of $\widetilde{\mathrm{eq}}(r)$ column-wise ($\widetilde{\mathrm{eq}}(r)^T=\theta^TE(r)$); **$E(r)$ commutes with every $\mathbb{F}_2$-linear map** ($\varphi,\varphi^{-1},P_V$) — the load-bearing algebraic trick of $\Pi_{\mathrm{sw}}$.
- **Concrete instantiation (§5.1.1)**: $\mathbb{T}=\mathbb{F}_{2^{128}}$ in GHASH basis ($x^{128}+x^7+x^2+x+1$); $\varphi(\sum_{i=0}^{127}a_ix^i)=\sum_{i=0}^{127}a_ix^i\in\mathbb{F}$ — copy the GHASH coefficient vector into the first 128 power-basis coordinates, zero elsewhere; $\iota=7$.

### 3.6 The commitment superring and NTT profile

- **Superring**: $S=\mathbb{Z}[\zeta_{8f}]\cong\mathbb{Z}[x]/(x^{648}-x^{324}+1)$, conductor $2^3\cdot3^5$; free rank-4 $R$-module; embedding $R\to S$, $\zeta_f\mapsto-\zeta_{8f}^4$. **Four consecutive $\mathbb{F}$-elements are packed into one $S$-element** by interleaving bits across the four module components; multiplication by $R$-elements (including every folding challenge) acts identically per component, so commitment and fold process packed elements without separation. Since $2$ *ramifies* in $S$ ($S/2S$ not a field), binary claims are read per component; SIS instances are over $S$.
- **Mixed-radix NTT**: conductor $2^3\cdot3^5$ allows radix-2 *and* radix-3 splittings. Supported primes: fully splitting **3889, 9721, 17497, 19441** (14–15 bits); quadratic-final **2917, 4861, 12637** (14 bits, Karatsuba in the final slots). $q$ = product of 2–3 of these per target security.
- **Signed-lane SIMD**: one residue per signed lane; lazy reduction schedules per modulus; binary-input forward transform via **byte-table lookups** for the top levels (linear in a small group of input bits); hand-scheduled assembly for final levels; Montgomery butterflies elsewhere.

### 3.7 The key extraction lemma (informal, from §1.3.1)

For challenges differing only in coordinate $j$: $\bar v=v-v'=c_jwj$ over $R$ for honest provers, and $F\bar v=\bar c_jy_j\bmod q$. Dividing by $\bar c_j$ **in $K$** (always invertible there) gives a rational candidate $w_j^*=\bar v/\bar c_j$. Then:

1. *Binding of rational openings*: two candidates with short integral multipliers satisfy $F(\bar c'_j\bar v-\bar c_j\bar v')=0\bmod q$ with a **short known** kernel vector ⇒ SIS mod $q$ ⇒ it must be zero **over $R\subset K$** (no wrap-around) ⇒ $\bar c'_j\bar c_j(w_j^*-w_j^{*'})=0$ in $K$ ⇒ $w_j^*=w_j^{*'}$.
2. *Well-definedness mod 2*: $\bar c_j\notin2R$ (injective challenge set) ⇒ $w_j^*$ has non-negative valuation at prime ideals above 2 ⇒ $w_j^*\bmod2$ exists. General principle: high min-entropy modulo a prime ideal ⇒ no negative valuations there; negative valuations only at small-norm primes.
3. *Consistency checks* ($u_j\bar c_j=\alpha^T\bar v$) are verified **mod $p$ over $R_p$**, not over $R_q$ — the arithmetisation never touches $q$.

**Consequence**: $q$ is free to be a product of *fully splitting* small primes (fastest NTT), and no invertibility is demanded of $q$ at all.

### 3.7.1 Worked example — the wrap-around counterexample and why number-field division fixes it

Take the power-of-two ring $\mathbb{Z}_q[x]/(x^\varphi+1)$ (the classical setting). A dishonest prover sets one coefficient $w$ of some $w_i$ to all-$\pm(q-1)/2$ coefficients and picks a challenge $c_i$ with an **even** number of non-zero $\{\pm1\}$ coefficients. Then:

- Over $R_q$: $v=Wc$ wraps around mod $q$; $v$ *looks* short even though $w_i$ is long — so “$v$ short” does **not** imply “all $w_i$ short”. Shortness of the amortised opening is vacuous without a separate range proof (which would itself have to be verified over $R_q$ — exactly what we are trying to avoid).
- Classical fix: require $\bar c_j$ invertible **in $R_q$** and divide there — forces partially-splitting $q$ (LS18-style constraints), i.e. slow NTT.
- LaBinius fix: divide in $K=\mathbb{Q}(\zeta_f)$. The extracted $w_j^*=\bar v/\bar c_j$ is a proper **rational** vector (e.g. twos in denominators when the counterexample above is run through the extractor). It may not even reduce mod $q$ (unknown valuations at primes above $q$) — but it does not need to: binding was already established over $R$ by the SIS argument, and only the reduction mod 2 (well-defined because $\bar c_j\notin2R$) feeds the arithmetisation. The twos-in-denominators case reduces mod 2 to a perfectly good binary witness.

### 3.7.2 Tower fields, GHASH, and why $\mathbb{T}\neq$ tower of $\mathbb{F}$

The lab's `lzk.gf2` core implements binary **towers** $\mathbb{F}_{2^{2^k}}$ (Binius-style, $\sigma:x\mapsto x^2$ squaring automorphisms). LaBinius needs two non-tower-compatible objects:

- $\mathbb{T}=\mathbb{F}_{2^{128}}$ **in the GHASH basis** (modulus $x^{128}+x^7+x^2+x+1$): chosen because the front ends (Binius/Flock) and the comparison PCSs (BaseFold/WHIR/Ligerito) are instantiated there, and because carry-less multiply (`PCLMULQDQ`/`VPCLMULQDQ`) implements GHASH-basis multiplication at hardware speed. $\mathbb{F}_{2^{128}}$ *is* a tower field abstractly, but the **basis matters**: the field switch is only $\mathbb{F}_2$-linear, so all coordinate manipulations (packing $\varphi$, $E(r)$, $\theta$) are basis-relative.
- $\mathbb{F}=\mathbb{F}_{2^{162}}$: degree $162=2\cdot3^4$ is **not** a power of two — there is no tower structure; multiplication is 3-word carry-less Karatsuba + **two** applications of $x^{162}=x^{81}+1$; elements fit exactly 3 machine words. This is the price of the inert-2 power-of-three conductor; the payoff is that $R_2$ is a *field* (2 inert), which the whole extraction strategy needs.

Also note $2^\iota=128\nmid162$: no embedding $\mathbb{T}\hookrightarrow\mathbb{F}$ — hence the $\mathbb{F}_2$-linear-only switch (§3.5).

### 3.8 What changed vs. classical Ajtai amortisation (LaBRADOR / Greyhound / RoKoko pattern)

| Aspect | Classical (LaBRADOR-style amortised opening) | **LaBinius** |
|---|---|---|
| Division of extracted witness | in $R_q$ — needs $\bar c_j$ invertible mod $q$ | in $K=\mathbb{Q}(\zeta_f)$ — always invertible |
| Constraint on $q$ | partially splitting, inert-degree ≥ 2 (LS18) | **any**: composite, fully splitting, small primes |
| Challenge set requirement | $S-S$ invertible mod $q$, short inverses | injective mod 2 only + operator norm |
| Witness norm guarantee | via range proofs / random projections / short-invertible-difference algebra | *none* — extraction yields rational vectors whose mod-2 reductions are the witness; binding handled by the SIS-no-wraparound argument |
| Evaluation/arithmetisation field | $=\mathbb{Z}_q$ (same characteristic) | $\mathbb{F}_{2^\varphi}$ (inert 2), decoupled |
| Binary computations | lift to $\mathbb{Z}$, explicit mod-2 constraints, bitness proofs | native: mod-2 reduction of the extracted witness *defines* the bits |
| Recursion | LaBRADOR over the same ring | ring-bridging block system (Appendix A) |

This table is the paper's thesis in one view; every design decision downstream (odd conductor, superring, composite $q$, CWSS-mod-2) follows from the second column.

---

## 4. Relations (exact equations)

All relations come in **exact** (blue parts removed: slack $s=1$, $\mu$ dropped) and **relaxed** (extraction) variants; an exact witness is relaxed for every $\mu\ge1$.

### 4.1 Relaxed principal relation (Def. 20)

$$\Xi^{\mathrm{lin\mbox{-}rel}}_{R,q,m,n,r,\beta,\mu}:=\Big\{\big((F,Y),(W,s)\big):\ F\in R_q^{n\times m},\ Y\in R_q^{n\times r},\ W\in R^{m\times r},\ s\in R^r,\ \|W\|\le\beta,\ F\,W=Y\,\mathrm{diag}(s)\bmod q,\ \|s_i\|_{\mathrm{op}}\le\mu\wedge s_i\notin2R\ \forall i\Big\}$$

### 4.2 Relaxed relation with binary field claims (Def. 21)

$$\Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}_{R,q,m,n,\bar n,r,\beta,\mu}:=\Big\{\big((F,Y,B,u),(W,s)\big):\ \big((F,Y),(W,s)\big)\in\Xi^{\mathrm{lin\mbox{-}rel}},\ B\in\mathbb{F}^{\bar n\times m},\ u^T\in\mathbb{F}^{\bar n\times r},\ B\,(W\bmod2)=u\,\mathrm{diag}(s\bmod2)\Big\}$$

### 4.3 Relaxed binary evaluation relation (Def. 22)

$$\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}rel}}_{R,q,m,n,r,\beta,\mu}:=\Big\{\big((F,Y,r,t),(W,s)\big):\ \big((F),(W,Y,s)\big)\in\Xi^{\mathrm{lin\mbox{-}rel}},\ r\in\mathbb{F}^{\nu},\ t\in\mathbb{F},\ \widetilde w:=\mathrm{vec}\big((W\bmod2)\,\mathrm{diag}(s\bmod2)^{-1}\big),\ \mathrm{MLE}[\widetilde w](r)=t\Big\}$$

### 4.4 Relaxed binary evaluation relation with field switch (Def. 23)

$$\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw\mbox{-}rel}}_{R,q,m,n,r,\beta,\mu,\varphi}:=\Big\{\big((F,Y,r,t),(W,s)\big):\ \mathrm{lin\mbox{-}rel\ part},\ \widetilde w':=\mathrm{vec}\big((W\bmod2)\mathrm{diag}(s\bmod2)^{-1}\big),\ P_V(\widetilde w')\in V^{mr},\ r\in\mathbb{T}^\nu,\ t\in\mathbb{T},\ \mathrm{MLE}[\varphi^{-1}(P_V(\widetilde w'))](r)=t\Big\}$$

### 4.5 SIS and evaluation relations

- $\Xi^{\mathrm{sis}}_{R,q,m,n,\beta}$ — as §3.2 (the extraction escape hatch).
- $\Xi^{\mathrm{eval}}=\{(\mathrm{pp},(c,r,t),(f,\mathrm{st})):\mathrm{Open}(\mathrm{pp},c,f,\mathrm{st})=1\wedge\mathrm{MLE}[f](r)=t\}$ (Def. 19) — the PCS interface.

### 4.6 Packed Ajtai commitment (Def. 24)

Message space $\mathbb{T}^{2^\nu}$: **Setup** samples $F\leftarrow R_q^{n\times m}$; **Com**$(F,f)$ computes $W\in R^{m\times r}$ with $\mathrm{vec}(W)=\mathrm{lift}(\varphi(f))$ and returns $Y=FW\bmod q$, state $(W,\mathbf{1})$; **Open**$(F,Y,f,(W,s))$ checks $\|W\|\le\beta$, $\|s_j\|_{\mathrm{op}}\le\mu$, $s_j\notin2R$, $FW=Y\,\mathrm{diag}(s)\bmod q$, and $\varphi^{-1}P_V\mathrm{vec}((W\bmod2)\mathrm{diag}(s\bmod2)^{-1})=f$.

### 4.7 LaBRADOR relation (Def. 25, App. A.1) and encoded folded relation (Def. 35)

- LaBRADOR: instance $(a_{i,j}^{(k)},\varphi_i^{(k)},b^{(k)},f'^{(\ell)},I_{\mathrm{bin}},\{\beta_i^2\}_{i\in[r]})$; witness $s=(s_0,\dots,s_{r-1})$, $s_i\in R'^{n_i}_Q$; constraints $f^{(k)}(s)=\sum_{i,j}a_{i,j}^{(k)}\langle s_i,s_j\rangle+\sum_i\langle\varphi_i^{(k)},s_i\rangle-b^{(k)}=0\in R'_Q$ (all $k$), $\mathrm{ct}(f'^{(\ell)}(s))=0\in\mathbb{Z}_Q$ (all $\ell$), binary coefficients for $i\in I_{\mathrm{bin}}$, $\|s_i\|^2\le\beta_i^2$.
- Encoded folded relation $R_{\mathrm{rec}}$ (Def. 35): instance $I_{\mathrm{rec}}=(\{F_\ell\},c,B,\{\mathrm{lift}(e_j)\},t,B,(T_Y,T_u,T_R),\rho_{\xi,j}^{(h)},\{\eta_i,\beta_i\})$; witness = RNS residue vectors $(y_\ell)_{\ell\in[\ell_{\max}]}$, chunk encodings of $v$ and $\tilde u=\mathrm{lift}(u)$, gadget-digit vectors of carries/$k_\ell$/$w_b$/$w_e$; relation = open + block + bit + zero + norm constraints (see §5.6).

### 4.8 Figure 1 — reduction flows (transcribe exactly)

$$
\begin{array}{ccccccccc}
& \Pi_{\mathrm{sw}} & & \Pi_{\mathrm{left\mbox{-}exp}} & & \Pi_{\mathrm{fold}} & \\
\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw}}_r & \longrightarrow & \Xi^{\mathrm{bin\mbox{-}eval}}_r & \longrightarrow & \Xi^{\mathrm{bin\mbox{-}lin}}_r & \longrightarrow & \Xi^{\mathrm{bin\mbox{-}lin}}_1 & (\text{correctness, solid})\\[4pt]
\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw\mbox{-}rel}}_r\ \cup\ \Xi^{\mathrm{sis}} & \longleftarrow & \Xi^{\mathrm{bin\mbox{-}eval\mbox{-}rel}}_r & \longleftarrow & \Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}_r & \longleftarrow & \Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}_1 & (\text{extraction, dashed})
\end{array}
$$

Subscripts count witness columns: $r\to r\to r\to1$. The composition (Corollary 1) chains the parameters:
$$\mathrm{par}_{\mathrm{in}}=(R,q,m,n,r,\beta,\varphi),\quad\mathrm{par}_{\mathrm{out}}=(R,q,m,n,1,1,r\gamma_C\beta),\quad\mathrm{par}'_{\mathrm{in}}=(R,q,m,n,r,2\beta',2\gamma_C,\varphi),\quad\mathrm{par}'_{\mathrm{out}}=(R,q,m,n,1,1,\beta'),\quad\mathrm{par}_{\mathrm{sis}}=(R,q,m,n,8\gamma_C\beta').$$

### 4.9 Worked micro-example (relations on a toy instance)

Let $m=2,r=2$ ($\nu=2$), $\bar n=1$, and suppose (schematic, over the real $\varphi=162$ ring in practice) the honest binary witness matrix is $W=\begin{pmatrix}1&0\\0&1\end{pmatrix}$ lifted to $R$ (each entry a 0/1 ring element), $F=(f_0\ f_1)\in R_q^{1\times2}$, so $Y=FW=(y_0\ y_1)$ with $y_0=f_0,y_1=f_1$.

- **Committed relation**: $FW=Y$ (slack $s=\mathbf 1$), $\|W\|=\sqrt2\le\beta$ — exact member of $\Xi^{\mathrm{lin\mbox{-}rel}}$ with $\mu=1$.
- **Left opening** at $r=(r_0,r_1)$: $u^T=\widetilde{\mathrm{eq}}(r_0)^TW\bmod2=(1-r_0,r_0)$; evaluation $u^T\widetilde{\mathrm{eq}}(r_1)=(1-r_0)(1-r_1)+r_0r_1=\mathrm{eq}(r_0,r_1)=\mathrm{MLE}[\mathrm{vec}(W)](r)$ — Lemma 4 in action.
- **Fold** with $c=(c_0,c_1)$: $v=Wc=(c_0,c_1)^T$; $Fv=Yc$ ✓; $Bv=u^Tc\bmod2$ where $B=(1-r_0,r_0)$ ✓; $\|v\|\le\|c_0\|+\|c_1\|\le2\gamma_C$ — the $r\gamma_C\beta$ bound.
- **Extraction**: fork on coordinate 0: $c^{(0)}=(c_0,c_1)$, $c^{(2)}=(c'_0,c_1)$; $\bar v=v^{(0)}-v^{(2)}=(c_0-c'_0,0)^T$, $\bar c_0=c_0-c'_0$; $w^{(0)}=\bar v/\bar c_0=(1,0)^T$ **over $K$** — recovers column 0 exactly; $s^{(0)}=\bar c_0\notin2R$ by challenge-set injectivity.

---

## 5. Protocols (full numbered transcriptions)

### 5.0 Dependency graph and full pipeline

```
f ∈ T^{2^nu}  (Binius/Flock front end output: bit-level claim, within-word weights ω)
   |
   |  Com: W with vec(W) = lift(φ(f)); Y = F W mod q            [Def. 24]
   v
Ξ^{bin-eval-sw}  ——— Π_sw (Fig. 2) ———> Ξ^{bin-eval}
   |   partial evals t = E(r) φ^{-1}(w'); sumcheck MLE[c]·MLE[w']; z = e^{-1} τ
   v
Ξ^{bin-eval}   ——— Π_left-exp (Fig. 3) ———> Ξ^{bin-lin}
   |   u^T = eq(r_0)^T W mod 2; B = eq(r_0)^T; check u^T eq(r_1) = t
   v
Ξ^{bin-lin}_r  ——— Π_fold (Fig. 4) ———> Ξ^{bin-lin}_1
   |   v = W c; F v = Y c mod q; B v = u^T c mod 2; ||v|| ≤ r γ_C β
   v
(final message)  ——— [non-recursive: send v, check directly] ———> PCS proof
   |
   |  [recursive: pre-commit T_Y (RNS residues), T_u, T_R BEFORE c; then]
   |   block system (Fig. 5) + limbs (Eq. limb) + binary (Eq. bin)
   |   + zero-part (Eq. zero) + gadgets + (nowrap) ———> LaBRADOR proof  [Thm 2]
   v
proof ≈ 80–100 KiB, verifier does ring arithmetic + FS hashes only
```

Extraction flows run right-to-left along the dashed arrows of Figure 1, terminating in $\Xi^{\mathrm{sis}}$ (over the superring $S$) or a relaxed witness.

### 5.1 Figure 2 — $\Pi_{\mathrm{sw}}$: field-switch reduction

**Statement.** $((F,Y,r,t),W)\in\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw}}_{\mathrm{par}_{\mathrm{in}}}$ with $\mathrm{par}_{\mathrm{in}}=(R,q,m,n,r,\beta,\varphi)$ → $((F,Y,r'',z),W)\in\Xi^{\mathrm{bin\mbox{-}eval}}_{\mathrm{par}_{\mathrm{out}}}$, $\mathrm{par}_{\mathrm{out}}=(R,q,m,n,r,\beta)$. Correctness error $\delta=(\nu+\iota)/|\mathbb{F}|$; knowledge soundness $\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw\mbox{-}rel}}_{\mathrm{par}'_{\mathrm{in}}}\cup\Xi^{\mathrm{sis}}_{\mathrm{par}_{\mathrm{sis}}}\leftarrow\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}rel}}_{\mathrm{par}'_{\mathrm{out}}}$ with $\kappa=(2\nu+\iota)/|\mathbb{F}|$, $\mathrm{par}_{\mathrm{sis}}=(R,q,m,n,2\mu\beta')$.

| # | Prover $P((F,Y,r,t),W)$ | Verifier $V((F,Y,r,t))$ |
|---|---|---|
| 1 | $\widetilde w':=\mathrm{vec}(W\bmod2)\in V^{mr}$ | |
| 2 | $\mathbf{t}:=E(r)\,\varphi^{-1}(\widetilde w')\in\mathbb{T}^{2^\iota}$ — the $2^\iota$ **partial evaluations** (send) | checks $\theta^T\mathbf{t}=t$ |
| 3 | | samples $\rho\leftarrow\mathbb{F}^\iota$ |
| 4 | | computes $\mathbf{t}':=\widetilde{\mathrm{eq}}(\rho)^T\varphi(\mathbf{t})$ and $c^T:=\widetilde{\mathrm{eq}}(\rho)^TE(r)\in\mathbb{F}_2^{2^\nu}$ |
| 5 | runs sumcheck over $\mathbb{F}$ for $\sum_{b\in\{0,1\}^\nu}\mathrm{MLE}[c](b)\mathrm{MLE}[\widetilde w'](b)\stackrel?=t'$ | verifies rounds; ends at $r''\in\mathbb{F}^\nu$ with claim $\mathrm{MLE}[c](r'')\mathrm{MLE}[\widetilde w'](r'')\stackrel?=\tau$ |
| 6 | | $e:=\mathrm{MLE}[c](r'')$; **abort if $e=0$**; $z:=e^{-1}\tau$ |
| 7 | outputs $W$ | outputs $((F,Y,r'',z),W)\in\Xi^{\mathrm{bin\mbox{-}eval}}_{\mathrm{par}_{\mathrm{out}}}$ |

**Marked messages** (proof-of-knowledge parts): $\mathbf{t}$ and the sumcheck rounds. The correctness chain: $\theta^T\mathbf{t}=\widetilde{\mathrm{eq}}(r)^T\varphi^{-1}(\widetilde w')=t$; commuting $\varphi$ past $E(r)$ (Lemma 7) gives $\varphi(\mathbf{t})=E(r)\widetilde w'$, hence $t'=\widetilde{\mathrm{eq}}(\rho)^T\varphi(\mathbf{t})=c^T\widetilde w'$ = the sumcheck total. The abort probability: $e=\widetilde{\mathrm{eq}}(\rho)^TE(r)\widetilde{\mathrm{eq}}(r'')=\mathrm{MLE}[\mathrm{vec}(E(r)^T)]((r'',\rho))$, nonzero multilinear in $\nu+\iota$ variables (nonzero because $\theta^TE(r)\mathbf{1}=1$) ⇒ Schwartz–Zippel $(\nu+\iota)/|\mathbb{F}|$.
**Knowledge soundness (Lemma 8)**: run once, rewind once; SIS branch from $F(W\,\mathrm{diag}(\hat s)-\hat W\,\mathrm{diag}(s))=0$ (norm $\le2\mu\beta'$); else $W\,\mathrm{diag}(\hat s)=\hat W\,\mathrm{diag}(s)$ over $R$, reduce mod 2, divide by invertible diagonals ⇒ $\widetilde w'=\hat{\widetilde w}'$. For a *bad* $\widetilde w'$ (violating the switch claim): fixed $\mathbf{t}$ precedes all challenges; $t'=\widetilde{\mathrm{eq}}(\rho)^T(\varphi(\mathbf{t})-E(r)\widetilde w')$ — nonzero fixed vector vanishing at uniform $\rho$ w.p. $\le\iota/|\mathbb{F}|$; if zero then $E(r)\widetilde w'=\varphi(\mathbf{t})$, applying $P_V$ and $\varphi^{-1}$ contradicts badness. Total $(2\nu+\iota)/|\mathbb{F}|$.

### 5.2 Figure 3 — $\Pi_{\mathrm{left\mbox{-}exp}}$: left expansion

**Statement.** $((F,Y,r,t),W)\in\Xi^{\mathrm{bin\mbox{-}eval}}_{\mathrm{par}_{\mathrm{in}}}$, $\mathrm{par}_{\mathrm{in}}=(R,q,m,n,r,\beta)$ → $((F,Y,B,u),W)\in\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}_{\mathrm{out}}}$, $\mathrm{par}_{\mathrm{out}}=(R,q,m,n,1,r,\beta)$ (the $\bar n=1$ slot holds $B$). **Knowledge error $\kappa=0$** (deterministic verifier ⇒ extractor = one run).

| # | Prover | Verifier |
|---|---|---|
| 1 | splits $r^T=(r_0^T\ r_1^T)\in\mathbb{F}^{\log m}\times\mathbb{F}^{\log r}$ | same split |
| 2 | $u^T:=\widetilde{\mathrm{eq}}(r_0)^TW\bmod2\in\mathbb{F}^r$ (send) | checks $u^T\widetilde{\mathrm{eq}}(r_1)=t$ |
| 3 | outputs $W$ | sets $B:=\widetilde{\mathrm{eq}}(r_0)^T\in\mathbb{F}^{1\times m}$; outputs $((F,Y,B,u),W)$ |

Correctness is Lemma 4 over $\mathbb{F}$: $u^T\widetilde{\mathrm{eq}}(r_1)=\widetilde{\mathrm{eq}}(r_0)^T(W\bmod2)\widetilde{\mathrm{eq}}(r_1)=\mathrm{MLE}[\mathrm{vec}(W\bmod2)](r)=t$; the binary claim of $\Xi^{\mathrm{bin\mbox{-}lin}}$ reads $BW=u^T\bmod2$ — true by construction. Soundness: from $B(W\bmod2)=u\,\mathrm{diag}(s\bmod2)$, divide column $j$ by invertible $s_j\bmod2$ and recombine against $\widetilde{\mathrm{eq}}(r_1)$ — $\kappa=0$.

### 5.3 Figure 4 — $\Pi_{\mathrm{fold}}$: folding

**Statement.** $((F,Y,B,u),W)\in\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}_{\mathrm{in}}}$, $\mathrm{par}_{\mathrm{in}}=(R,q,m,n,\bar n,r,\beta)$ → $((F,Yc,B,c^Tu\bmod2),v)\in\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}_{\mathrm{out}}}$, $\mathrm{par}_{\mathrm{out}}=(R,q,m,n,\bar n,1,r\gamma_C\beta)$. Knowledge soundness $\Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}_{\mathrm{par}'_{\mathrm{in}}}\leftarrow\Xi^{\mathrm{bin\mbox{-}lin\mbox{-}rel}}_{\mathrm{par}'_{\mathrm{out}}}$ with $\kappa=r/|C|$, $\mathrm{par}'_{\mathrm{in}}=(R,q,m,n,\bar n,r,2\beta',2\gamma_C)$, $\mathrm{par}'_{\mathrm{out}}=(R,q,m,n,\bar n,1,\beta')$.

| # | Prover | Verifier |
|---|---|---|
| 1 | | samples $c\leftarrow C^r$ |
| 2 | $v:=Wc\in R^m$ (send) | checks $((F,Yc,B,c^Tu\bmod2),v)\in\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}_{\mathrm{out}}}$, i.e. $Fv=Yc\bmod q$, $Bv=u^Tc\bmod2$, $\|v\|\le r\gamma_C\beta$ |

Norm bound: $\|v\|\le\sum_j\|W_{:,j}c_j\|\le\sum_j\|c_j\|_{\mathrm{op}}\|W_{:,j}\|\le r\gamma_C\|W\|$.
**Extractor (Lemma 10)**: CWSS forking (Lemma 3, $k=2$) gives $c^{(0)},\dots,c^{(r)}$ pairwise differing from $c^{(r)}$ in single coordinates with outputs $v^{(j)}$; set $w^{(j)}:=v^{(j)}-v^{(r)}$, $s^{(j)}:=c^{(j)}_j-c^{(r)}_j$; then $Fw^{(j)}=s^{(j)}y_j\bmod q$, $Bw^{(j)}=s^{(j)}u_j\bmod2$, $\|w^{(j)}\|\le2\beta'$, $\|s^{(j)}\|_{\mathrm{op}}\le2\gamma_C$, and $s^{(j)}\notin2R$ by injectivity mod 2. Assemble $W=(w^{(j)})_j$, $s=(s^{(j)})_j$ — a relaxed witness. Loss exactly $r/|C|$.

### 5.4 Composition and the PCS theorem

- **Corollary 1**: $\Pi=\Pi_{\mathrm{sw}}\circ\Pi_{\mathrm{left\mbox{-}exp}}\circ\Pi_{\mathrm{fold}}$ is correct $\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw}}_{\mathrm{par}_{\mathrm{in}}}\to\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}_{\mathrm{out}}}$ with $\delta=(\nu+\iota)/|\mathbb{F}|$ and knowledge-sound for $\Xi^{\mathrm{bin\mbox{-}eval\mbox{-}sw\mbox{-}rel}}_{\mathrm{par}'_{\mathrm{in}}}\cup\Xi^{\mathrm{sis}}_{\mathrm{par}_{\mathrm{sis}}}\leftarrow\Xi^{\mathrm{bin\mbox{-}lin}}_{\mathrm{par}'_{\mathrm{out}}}$ with $\kappa=(2\nu+\iota)/|\mathbb{F}|+r/|C|$; errors add under sequential composition [KLNO24]; SIS bound $8\gamma_C\beta'=2\mu\cdot2\beta'$ with $\mu=2\gamma_C$.
- **Theorem 1 (PCS over $\mathbb{T}$)**: with $\gamma_C\ge1$, $\beta\ge\sqrt{\varphi m}$, $\beta':=r\gamma_C\beta$, SIS$_{\mathrm{par}_{\mathrm{sis}}}$ hard: run $\Pi$ as a PoK where the prover sends the final $v$ and the verifier checks the folded $\Xi^{\mathrm{bin\mbox{-}lin}}$ membership; then the packed Ajtai commitment $(m,n,r,2\beta',2\gamma_C,\varphi)$ + $\Pi$ is a multilinear PCS for $\nu$ variables over $\mathbb{T}$ with binding error $2^{-\lambda}$, correctness $\delta$, knowledge error $\kappa+2^{-\lambda}$. Binding argument: two openings with $f\neq f'$ have distinct $P_V(\widetilde w)$ projections ⇒ some column $j$ of $s'_jW-s_jW'$ is a nonzero SIS solution of norm $\le2\cdot2\gamma_C\cdot2\beta'$.
- **Lemma 11 (efficiency)**, $2^\nu=mr$: prover $O(2^\nu)$ mults in $\mathbb{T}$ and $\mathbb{F}$, $O(2^{\nu+\iota})$ adds in $\mathbb{T}$/$\mathbb{F}$, $O(2^\nu)$ mults of ring elements by challenges; verifier $O(2^\iota)$ $\mathbb{T}$-mults, $O(\nu2^{2\iota}+m+r)$ $\mathbb{F}$-mults, $O(nm)$ $R_q$-mults, $O(nr)$ challenge-mults; **communication**: $2^\iota$ elements of $\mathbb{T}$, $3\nu+r$ elements of $\mathbb{F}_2$ (footnote 2: reducible to $2\nu$ — the verifier knows $g_i(0)+g_i(1)$ from the previous round so two values determine the degree-2 round polynomial), and $m$ elements of $R$ of norm $\le\beta'$; verifier sends $\nu+\iota$ elements of $\mathbb{F}$ and $r$ challenges.
  Verifier's $e=\widetilde{\mathrm{eq}}(\rho)^TE(r)\widetilde{\mathrm{eq}}(r'')$ trick: compute $E(r)\widetilde{\mathrm{eq}}(r''))\in\mathbb{F}^{2^\iota}$ (coordinates over $\theta_k\otimes1$ of $\prod\big((1-r_i)\otimes(1-r''_i)+r_i\otimes r''_i\big)\in\mathbb{T}\otimes_{\mathbb{F}_2}\mathbb{F}$, $\nu$ mults in the $2^\iota$-dimensional $\mathbb{F}$-algebra) then inner product with $\widetilde{\mathrm{eq}}(\rho)$ — avoids materialising $c$.

### 5.5 Within-word / word-crossing claims (Binius & Flock integration, §5.1.5)

Both front ends end their reductions **on the bits of the packed trace**, not on the words: $\nu$ multilinear coordinates over the words, and *within a word* $\iota$ multilinear coordinates (Binius) or a **univariate skip over six of them** (Flock). Instead of first collapsing the within-word part to a word-level claim over $\mathbb{T}$ via the ring switching of [DP25] and then applying Figure 2, LaBinius runs the switch **on the bit-level claim directly**: the within-word part is a public weight vector $\omega\in\mathbb{T}^{2^\iota}$ on the $2^\iota$ partial evaluations $\mathbf{t}$, and the verifier's check becomes $\omega^T\mathbf{t}$ in place of $\theta^T\mathbf{t}$. This saves **one sumcheck of $\nu$ rounds and one message of $2^\iota$ elements of $\mathbb{T}$**. The two integrations share the commitment/opening implementation; statement shapes differ: Binius = one chained hash over a long message (compressions consume previous state); Flock = batch of independent compression calls.

### 5.6 Appendix A — recursion into LaBRADOR: the block constraint system

**Goal**: replace $\Pi_{\mathrm{fold}}$'s final message $(v,Y,u)$ — satisfying $Fv=Yc\bmod q$, $Bv=u^Tc\bmod2$, $\|v\|\le\beta'$ — by Ajtai pre-commitments $T_Y,T_u,T_R$ + one LaBRADOR proof. $Y$ (RNS residues) and $u$ are committed **before** the folding challenge, so the prover cannot tailor them to $c$.

**Bridge between mismatched rings**: $R_Q$ ($\varphi=162$ coefficients, $\Phi_{3^5}=x^{162}+x^{81}+1$) vs. LaBRADOR's $R'_Q\cong\mathbb{Z}_Q[x]/(x^{\mathrm d}+1)$ (power-of-two degree $\mathrm d<\varphi$).

1. **Chunking (Defs. 26–31)**: witness $x\in R_Q$ cut into chunks of $c$ consecutive coefficients, each an $R'_Q$ element ($\mathrm{supp}\subseteq[c]$); public $g$ cut into blocks of $p$ coefficients with $c+p-1\le\mathrm d$, $p\mid\varphi/2$; $N=\varphi/p$ blocks; $g^{[b,a]}:=x^{bc}g$'s $a$-th coefficient block; $\mathrm{Enc}_c/\mathrm{Dec}_c$ encode/decode ($\mathrm{Dec}_c(\mathrm{Enc}_c(x))=x$).
   **Lemma 12 (chunk products)**: $g^{[b,a]}\xi$ (for $\mathrm{supp}(\xi)\subseteq[c]$) is an exact $\mathbb{Z}_Q[x]$ product of degree $\le p+c-2\le\mathrm d-1$ — no reduction mod $x^{\mathrm d}+1$ — and $\sum_a x^{ap}g^{[b,a]}\xi=x^{bc}g\xi$ in $\mathbb{Z}_Q[x]$.
2. **Block equations with carries (Def. 32, Figure 5)**: for the identity $\sum_\nu g_\nu x_\nu=z$ in $R_Q$, define block product sums $D_a:=\sum_{\nu,b}g_\nu^{[b,a]}x_\nu^{[b]}$; the system is, for every $a\in A$:
   $$D_a+e_{a-1}-x^pe_a-\mathbf{1}_{a=0}e_{N-1}-\mathbf{1}_{a=N/2}x^{\varphi/2}e_{N-1}=z^{\langle a\rangle}\in R'_Q\qquad(\text{block})$$
   with $e_{-1}:=0$, supports $\mathrm{supp}(x_\nu^{[b]})\subseteq[c]$, $\mathrm{supp}(e_a)\subseteq[\mathrm d-p]$. **Figure 5 layout**: blocks $a=0,1,\dots,N/2,\dots,N-1$ along the coefficient axis $0,p,2p,\dots,\varphi/2,\dots,\varphi$; products $g^{[b,1]}x^{[b]}$, $g^{[b,N-1]}x^{[b]}$ straddle block boundaries; carries $e_1$ flow right (subtract $x^pe_a$ from block $a$, add $e_a$ to block $a{+}1$); the **last carry $e_{N-1}$ wraps around twice** — subtracted once in block 0 and once (scaled by $x^{\varphi/2}$) in block $N/2$ — exactly implementing reduction by $\Phi_{3^\kappa}(x)$, since $x^\varphi\equiv-x^{\varphi/2}-1$.
   **Lemma 13 (block encoding)**: carries with the stated supports exist iff $\sum_\nu g_\nu\mathrm{Dec}_c((x^{[b]}_\nu)_b)=z$ in $R_Q$. (Proof: sum $x^{ap}\times(\text{block})$; carry telescoping gives $-x^\varphi e_{N-1}$; indicators give $-e_{N-1}-x^{\varphi/2}e_{N-1}$; total $P-\Phi_f(x)e_{N-1}=z$. Converse constructs $e_a$ by downward accumulation with $e_{N-1}=W$ where $P-z=\Phi_fW$.) **Support conditions are necessary** — a stray coefficient at a position in $[c,\mathrm d)$ or $[\mathrm d-p,\mathrm d)$ makes the equation hold only mod $x^{\mathrm d}+1$.
3. **Zero-part test (Eq. zero, Lemma 14)**: for forbidden coefficient positions $\mathcal{Z}=\{(\xi,j)\}$, after chunk commitments are fixed, derive $\lceil\lambda/\log_2Q\rceil$ independent uniform $\rho_{\xi,j}^{(h)}\in\mathbb{Z}_Q$ and impose $\mathrm{ct}\big(\sum_{(\xi,j)\in\mathcal{Z}}\rho_{\xi,j}^{(h)}x^{-j}\xi\big)=0$ for every $h$. One nonzero forbidden coefficient survives with probability $\le Q^{-\lceil\lambda/\log_2Q\rceil}\le2^{-\lambda}$.
4. **RNS limbs (Def. 34, Eq. limb, Lemma 15)**: $q=\prod_{\ell\in[\ell_{\max}]}q_\ell$ distinct odd primes; balanced residues $F_\ell,Y_\ell$; the folded identity $Fv=Yc\bmod q$ ⇔ exists $k_\ell\in R^n$: $F_\ell v-Y_\ell c=q_\ell k_\ell$ **over $R$** for every $\ell$ (coefficients divisible by $q_\ell$; CRT recombination).
5. **Binary constraints (Eq. bin)**: with $\tilde u:=\mathrm{lift}(u)$ and public $e_j=\widetilde{\mathrm{eq}}(r_1)_j$:
   $$\mathrm{lift}(B)v-\sum_{j\in[r]}c_j\tilde u_j=2w_b,\qquad \sum_{j\in[r]}\mathrm{lift}(e_j)\tilde u_j-\mathrm{lift}(t)=2w_e,$$
   — integer identities whose mod-2 reductions are exactly $Bv=u^Tc\bmod2$ and the evaluation check (using $c_j\bmod2$ multiplication and $\tilde u=\mathrm{lift}(u)\bmod2$ from the bit constraint).
6. **Norm caps and gadgets (Def. 33)**: residue vectors used directly with $\|y_\ell\|\le\beta_{Y,\ell}:=\frac{q_\ell-1}{2}\sqrt{n_Y}$ (Eq. norm, no gadget decomposition); carries, limb quotients $k_\ell$, and binary quotients $w_b,w_e$ gadget-decomposed in base $B$: $x=\sum_jB^jx^{(j)}$, digits in $[-B/2,B/2-1]$, per-digit cap $\frac{B-1}{2}\sqrt{n_x}$; level counts chosen so honest quotients/carries decompose.
7. **Pre-commitments (Eq. open)**: $T_Y=\mathrm{Com}_{h_Y}(y)$ (residues), $T_u=\mathrm{Com}_{h_u}(\mathrm{Enc}_c(\tilde u))$, $T_R=\mathrm{Com}_{h_R}(z_R)$ ($z_R$ = chunk encodings of $v$ + all gadget digits).
8. **No-wraparound (Lemma 16)**: every encoded linear constraint must satisfy
   $$\sum_\ell\|C_{\nu,t,\ell}\|_{\mathrm{op}}\tfrac{q_\ell-1}{2}\sqrt{n_Y}+\sum_{i\in U}\|r_{\nu,t,i}\|\beta_i+\sum_{(x,j)\in G}\|r_{\nu,t,x,j}\|\tfrac{B-1}{2}\sqrt{n_x}+|b_{\nu,t}|<Q/2\qquad(\text{nowrap})$$
   ⇒ identities mod $Q$ are integer identities (zero is the only multiple of $Q$ in range).
9. **Lemma 17**: $R_{\mathrm{rec}}$ (Def. 35) is exactly a LaBRADOR relation (open = linear constraints; block = linear since one factor public; bit = binary constraint; zero = constant-term constraints; norms = front-end constraints).
10. **Theorem 2 (security of the recursive opening)**: assuming LaBRADOR knowledge soundness, binding of the Ajtai pre-commitments (SIS), and Theorem 1 hypotheses, with Eq. (nowrap) for every constraint and $\kappa_{\mathrm{Lab}}$ LaBRADOR's error: complete with $\delta=(\nu+\iota)/|\mathbb{F}|$; PoK for $\Xi^{\mathrm{eval}}$ with
    $$\kappa=\frac{2\nu+\iota}{|\mathbb{F}|}+\frac{r}{|C|}+\kappa_{\mathrm{Lab}}+5\cdot2^{-\lambda}.$$
    (Zero-test failure $2^{-\lambda}$; three binding failures; SIS branch; sequential composition adds Corollary 1's error.) Extraction: binding of $T_Y,T_u$ fixes residues and $u$ **before** $c$; binding of $T_R$ fixes chunks before zero masks; Lemma 14 ⇒ supports; Lemma 13 ⇒ limb/binary identities over $R_Q$; Lemma 16 ⇒ over $\mathbb{Z}$; mod-$q_\ell$ + Lemma 15 ⇒ $Fv=Yc\bmod q$; mod-2 ⇒ binary checks + evaluation; with the norm bound these are exactly $\mathrm{Open}$.

### 5.6.1 Worked example of the block system (Figure 5 sanity check)

Toy numbers (not the paper's): take $\varphi=6$ (pretend $f=9$), $\mathrm d=8$, chunk $c=3$, block $p=2$: check $c+p-1=4\le8$ ✓ but $p\mid\varphi/2=3$ fails — so take $p=3$, $c=4$: $c+p-1=6\le8$ ✓, $p\mid3$ ✓, $N=\varphi/p=2$ blocks, $B=\lceil6/4\rceil=2$ chunks.

Encode a single product $g\cdot x=z$ in $R_Q=\mathbb{Z}_Q[x]/(x^6+x^3+1)$ (the $f=9$ cyclotomic):

- Chunks: $x=x^{[0]}+x^3x^{[1]}$ with $\mathrm{supp}(x^{[b]})\subseteq[4]$; blocks: $g=g^{\langle0\rangle}+x^3g^{\langle1\rangle}$, each $\mathrm{supp}\subseteq[3]$.
- Block products: $D_0=g^{[0,0]}x^{[0]}+g^{[1,0]}x^{[1]}$ where $g^{[b,a]}$ = block $a$ of $x^{bc}g$; $D_1=g^{[0,1]}x^{[0]}+g^{[1,1]}x^{[1]}$ — each is an exact $\mathbb{Z}_Q[x]$ product of degree $\le p+c-2=5<\mathrm d$ ✓ (Lemma 12).
- Block equations (Eq. block): $D_0+e_{-1}-x^3e_0-\mathbf 1_{a=0}e_1-\mathbf 1_{a=N/2=1}x^3e_1=z^{\langle0\rangle}$ and $D_1+e_0-x^3e_1-\mathbf 1_{a=1}x^{0}e_1=z^{\langle1\rangle}$ — the second has *both* indicator roles? No: only $a=0$ gets the unscaled $e_{N-1}$ and only $a=N/2=1$ gets $x^{\varphi/2}e_{N-1}$ (here $\varphi/2=3$). Multiply the first by $x^0$, the second by $x^3$, sum: carry telescoping kills $e_0$; the indicators contribute $-e_1-x^6e_1$; total $P-(x^6+x^3+1)e_1=z$, i.e. $P=z\bmod\Phi_9$ ✓ — the wrap-around carry *is* the cyclotomic reduction.
- The lab's unit test should replicate exactly this arithmetic for random $g,x$ and confirm the constructive carry computation of Lemma 13's proof yields $e_{N-1}=W$ (the quotient $P-z=\Phi_fW$).

### 5.6.2 Gadget and norm-cap summary (what LaBRADOR sees)

| Witness object | Encoding | Norm cap |
|---|---|---|
| RNS residue matrices $y_\ell=\mathrm{Enc}_c(Y_\ell)$ | direct (no gadget) | $\beta_{Y,\ell}=\frac{q_\ell-1}{2}\sqrt{n_Y}$ (Eq. norm) |
| Folded witness $v$ | chunk encoding | from $\|v\|\le\beta'$ per chunk |
| Left expansion $\tilde u=\mathrm{lift}(u)$ | chunk encoding | binary ($I_{\mathrm{bin}}$ set) |
| Carries $e_{\delta,a}$ (limb/bin/eval blocks) | base-$B$ gadget digits | $\frac{B-1}{2}\sqrt{n_x}$ per digit (Def. 33) |
| Limb quotients $k_\ell$ | base-$B$ gadget digits | ditto |
| Binary quotients $w_b,w_e$ | base-$B$ gadget digits | ditto |

Public level counts are chosen so every *honest* quotient and carry admits its decomposition; the (nowrap) inequality then certifies that the mod-$Q$ identities are integer identities.

### 5.7 Bit dropping (§5.1.4) — security-level fine-tuning

Products of small primes make $q$ coarse-grained; **bit-dropping** (Dilithium public-key compression / [LNP22] style) gives fine control: drop $d$ low bits of the commitment — prover runs **Garner** (mixed-radix) on the RNS residues, writes $Y=Y_0+2^dY_1$ ($Y_0$ = rounding error), sends $Y_1$ + remaining mixed-radix digits; verifier reconstructs the rounded commitment, computes $z':=Fv-2^dY_1c=Y_0c\bmod q$, transforms only the residual back. The identity $(F\ I)(v,-z')=2^dY_1c\bmod q$ is a **normal-form SIS relation**: extracted preimage bound $\sqrt{B_v^2+B_{z'}^2}$. Trades excess security for smaller commitments without changing the modulus.

---

## 6. Soundness & Security

### 6.1 Statement inventory

| # | Statement | Error |
|---|---|---|
| Lemma 1 | $R/2R=\mathbb{F}_{2^\varphi}$ (2 inert) | exact |
| Lemma 2 | signed binary challenges injective mod 2 | exact |
| Lemma 3 | CWSS forking ([FMN24] L7.1) | $\ell(k{-}1)/|S|$ |
| Lemma 4 | bilinear evaluation over any ring | exact |
| Lemmas 5–6 | PIT root bound / sumcheck soundness | $D/|S|$, $\ell d/|L|$ |
| Lemma 7 | $E(r)$ commutes with $\mathbb{F}_2$-linear maps | exact |
| **Lemma 8** | $\Pi_{\mathrm{sw}}$ RoK | $\delta=(\nu{+}\iota)/|\mathbb{F}|$; $\kappa=(2\nu{+}\iota)/|\mathbb{F}|$ |
| **Lemma 9** | $\Pi_{\mathrm{left\mbox{-}exp}}$ RoK | $\kappa=0$ |
| **Lemma 10** | $\Pi_{\mathrm{fold}}$ RoK | $\kappa=r/|C|$ |
| **Corollary 1** | composition | $\delta=(\nu{+}\iota)/|\mathbb{F}|$; $\kappa=(2\nu{+}\iota)/|\mathbb{F}|+r/|C|$; SIS bound $8\gamma_C\beta'$ |
| **Theorem 1** | PCS over $\mathbb{T}$ | binding $2^{-\lambda}$; correctness $\delta$; knowledge $\kappa+2^{-\lambda}$ |
| Lemmas 12–13 | chunk products / block encoding | exact (supports necessary) |
| Lemma 14 | zero-part test | $2^{-\lambda}$ |
| Lemma 15 | RNS lifting | exact |
| Lemma 16 | no wraparound | exact given (nowrap) |
| Lemma 17 | reduction to LaBRADOR | — |
| **Theorem 2** | recursive opening | $\kappa=(2\nu{+}\iota)/|\mathbb{F}|+r/|C|+\kappa_{\mathrm{Lab}}+5\cdot2^{-\lambda}$ |

### 6.2 The three extraction templates

1. **Rational-field division (unique to LaBinius)**: fork on coordinate $j$; $\bar v/\bar c_j$ computed **in $K$**; binding via SIS-mod-$q$ + shortness ⇒ no wrap-around ⇒ equality over $R$ ⇒ cancel invertible differences in $K$. The extracted witness may be a proper rational vector (e.g. twos in denominators for the all-$\pm(q-1)/2$ counterexample) — and that is fine: its mod-2 reduction exists because $\bar c_j\notin2R$.
2. **CWSS forking with division mod 2** ($\Pi_{\mathrm{fold}}$): differences only need invertibility **modulo 2** — the relaxation that unlocks fully-splitting $q$.
3. **Rewind-once + S-Z** ($\Pi_{\mathrm{sw}}$): fixed pre-challenge message $\mathbf{t}$; bad-$\widetilde w'$ analysis splits error into sumcheck part ($2\nu/|\mathbb{F}|$) and $\rho$-part ($\iota/|\mathbb{F}|$).

### 6.3 Security anchors and parameter selection (§5.1.8)

- **SIS over the superring $S$** (since the commitment lives there), $q$ = product of small primes; conventional lattice attack estimated with LatticeEstimator [APS15] at **λ = 100 bits**; average-case norm estimates in the completeness direction, worst-case extracted bounds in the soundness direction; bit-dropped commitments include both folded witness and residual ($\sqrt{B_v^2+B_{z'}^2}$).
- **Module-BKZ predictions of [DEdP25]**; for conductors $2^a3^b$ the cheapest subfield attack is over $\mathbb{Q}(\zeta_3)$ — the estimator must allow every relevant subfield; coefficient→canonical-embedding conversion via trace-form Gram matrix assuming random direction; block size translated to module-BKZ equivalent.
- **Challenge set**: fixed Hamming weight, $\{-1,1\}$ nonzeros, signed via keyed hash (preserves mod-2 image, centres norms); operator norm monitored via Fourier-slot energy.

### 6.4 Fiat–Shamir transcript layout (implementation contract)

The evaluation proof is compiled non-interactively; the recursive statement is bound to the preceding transcript by a **digest of its absorbed data** (§5.1.7). Order of absorb/derive events for one full recursive evaluation proof:

1. `absorb`: public parameters ($F$ digest, ring profile, $\mathrm{par}$ tuple), commitment $T_Y$ (or $Y$ non-recursively).
2. `derive`: the front-end's own challenges (Binius/Flock sumchecks, until the bit-level claim $(r,t,\omega)$ is fixed).
3. `derive` `sw-rho`: $\rho\in\mathbb{F}^\iota$ (after $\mathbf{t}$, the $2^\iota$ partial evaluations, is absorbed).
4. `derive` `sc-r''[i]`: one $\mathbb{F}$ element per sumcheck round (after each round polynomial — send 2 of 3 coefficients, footnote 2).
5. `absorb`: $u$ (left opening), and — recursive mode — $T_u,T_R$ pre-commitments **all before `fold-c`**.
6. `derive` `fold-c`: $c\leftarrow C^r$ (per-coordinate domain separation for the forking analysis).
7. `absorb`: LaBRADOR proof + instance digest; `derive` LaBRADOR's internal challenges (handled inside the LaZer/Dachshund front end).

**Binding-before-challenge discipline** (Theorem 2): $T_Y,T_u$ must be fixed *before* `fold-c`, and $T_R$ before the zero-test masks $\rho_{\xi,j}^{(h)}$ — any implementation that lets the prover influence these orderings forfeits the extraction argument.

### 6.5 Zero-knowledge gap (stated open problem)

The scheme is **not** zero-knowledge: the folded opening $v$, partial evaluations $\mathbf t$, and left opening $u$ are revealed (non-recursive mode) or committed-and-proved (recursive). The paper sketches a path: hide commitments/openings inside a ZK argument such as LaBRADOS [BBL+26a] and blind the sumcheck messages à la [XZZ+19]; the open problem is ensuring the *composed* protocol hides the witness including the information leaked by the evaluation proof. For the lab: mark LaBinius as a *transparent, non-ZK* PCS; wrap with LaBRADOS-style blinding only if a privacy use-case appears.

---

## 7. Parameters & Concrete Efficiency

### 7.1 Algebraic parameters (concrete)

| Parameter | Value |
|---|---|
| $f$ / $\varphi$ / $\Phi_f$ | $3^5=243$ / $162$ / $x^{162}+x^{81}+1$ |
| $\mathbb{F}$ | $\mathbb{F}_{2^{162}}$ (3 machine words per element) |
| $\mathbb{T}$ | $\mathbb{F}_{2^{128}}$, GHASH basis $x^{128}+x^7+x^2+x+1$; $\iota=7$ |
| $\varphi$ (packing) | copy GHASH vector to first 128 power-basis coordinates |
| Superring $S$ | $\mathbb{Z}[x]/(x^{648}-x^{324}+1)$, conductor $2^33^5$, rank 4 over $R$; 4 $\mathbb{F}$-elements packed per $S$-element |
| $q$ | product of 2–3 of {3889, 9721, 17497, 19441 (fully splitting); 2917, 4861, 12637 (quadratic-final)} |
| $C$ | signed fixed-weight ternary, injective mod 2 |
| Security | 100 bits (SIS over $S$) |
| LaBRADOR ring | $R'_Q=\mathbb{Z}_Q[x]/(x^{\mathrm d}+1)$, separate prime $Q$; chunks $c$, blocks $p$, $c+p-1\le\mathrm d$, $p\mid\varphi/2=81$ |

### 7.2 Table 1 — PCS comparison (times ms; |C|, |π| KiB; 100 bits; LaBinius over $\mathbb{F}_{2^{162}}$ vs. others over $\mathbb{F}_{2^{128}}$ — noted as *to LaBinius's disadvantage*)

| Scheme | $2^{18}$: Comm / P / V / |C| / |π| | $2^{20}$: Comm / P / V / |C| / |π| | $2^{22}$ | $2^{24}$ |
|---|---|---|---|---|
| BaseFold 1/2 | 5.6 / 2.4 / 0.3 / 0.03 / 243.8 | 25.0 / 9.3 / 0.4 / 0.03 / 312.2 | 110.5 / 40.9 / 0.5 / 0.03 / 395.1 | 468.7 / 175.4 / 0.6 / 0.03 / 478.5 |
| BaseFold 1/4 | 11.1 / 3.4 / 0.2 / 0.03 / 184.3 | 49.3 / 13.1 / 0.3 / 0.03 / 235.3 | 213.6 / 55.3 / 0.3 / 0.03 / 285.0 | 907.0 / 243.8 / 0.4 / 0.03 / 345.3 |
| WHIR 1/2 | 7.1 / 8.5 / 2.2 / 0.03 / 190.2 | 31.3 / 48.0 / 1.6 / 0.03 / 239.7 | 133.6 / 127.7 / 1.6 / 0.03 / 294.0 | 649.9 / 909.9 / 2.0 / 0.03 / 352.7 |
| WHIR 1/4 | 11.3 / 5.6 / 0.9 / 0.03 / 154.4 | 61.5 / 30.1 / 0.8 / 0.03 / 202.8 | 261.9 / 143.4 / 1.3 / 0.03 / 243.4 | 1069.4 / 594.5 / 1.1 / 0.03 / 300.9 |
| Ligerito 1/2 | 4.4 / 12.9 / 0.6 / 4.0 / 350.2 | 26.1 / 50.3 / 1.1 / 4.0 / 378.9 | 96.8 / 240.5 / 1.3 / 4.0 / 330.8 | 482.9 / 837.8 / 1.0 / 4.0 / 469.5 |
| Ligerito 1/4 | 9.0 / 16.7 / 0.4 / 2.0 / 176.5 | 53.4 / 55.9 / 0.7 / 2.0 / 191.7 | 199.5 / 284.4 / 0.8 / 2.0 / 183.9 | 963.5 / 917.9 / 0.6 / 2.0 / 249.2 |
| Brakedown 0.704 | 6.5 / 2.9 / 5.6 / 0.03 / 3498.6 | 23.6 / 9.1 / 10.9 / 0.03 / 6158.0 | 120.3 / 27.4 / 20.8 / 0.03 / 11149.9 | 604.7 / 97.0 / 40.2 / 0.03 / 20806.5 |
| Brakedown 0.581 | 6.7 / 2.0 / 3.2 / 0.03 / 1658.5 | 29.8 / 6.8 / 6.2 / 0.03 / 3003.9 | 155.3 / 23.3 / 13.5 / 0.03 / 5602.0 | 978.3 / 86.4 / 27.1 / 0.03 / 10705.6 |
| **LaBinius** | 7.0 / 2.8 / 0.3 / 283.5 / 307.5 | 42.7 / 10.8 / 1.2 / 587.2 / 658.1 | 164.7 / 44.8 / 2.7 / 1174.5 / 1394.9 | 636.0 / 167.3 / 6.7 / 2430.0 / 2927.3 |
| **LaBinius+LaBRADOR** | 9.8 / 121.7 / 76.8 / 4.1 / **75.3** | 48.1 / 300.9 / 192.8 / 4.1 / **72.6** | 174.2 / 603.4 / 370.4 / 4.1 / **86.1** | 642.9 / 1333.8 / 713.1 / 4.5 / **82.9** |

Reading: commitment+prover within 25% of Brakedown/BaseFold and 1.6–2.3× faster than WHIR/Ligerito at the largest size; **recursive proof constant ≈72–87 KiB — smallest in the table at every size, ≈3× smaller than the best competitor at $2^{24}$**; recursive commitment $|C|=4.1$–4.5 KiB; non-recursive proof/verification grow as $\sqrt{\cdot}$; recursive verification not competitive (future: RoKoko-style wrapper).

### 7.2.1 Reading Table 1 (analysis)

- **Commitment column**: LaBinius's linear cost is ≈25% above Brakedown/BaseFold at $2^{24}$ (636 ms vs 604.7/978.3/468.7 — actually *between* the BaseFold rates and below Brakedown 0.581) — but its *commitment is over $\mathbb{F}_{2^{162}}$ with 4-way superring packing*, i.e. the count is per packed element; the comparison PCSs commit $\mathbb{F}_{2^{128}}$ elements.
- **Prover column**: non-recursive LaBinius prover (167 ms at $2^{24}$) is the fastest in the table after Brakedown; recursive (1334 ms) is dominated by the LaBRADOR prover whose share *falls* as the witness grows (its cost ∝ $N^{1/4}$ vs. the linear commitment).
- **Verification**: non-recursive 6.7 ms at $2^{24}$ — competitive with Brakedown's $\sqrt N$ shape, beaten by the polylog schemes (0.6–2 ms) only at large sizes; recursive 713 ms is the scheme's acknowledged weakness (future RoKoko-style wrapper).
- **Proof size, the headline**: non-recursive grows as $\sqrt N$ (307 KiB → 2927 KiB); recursive is **flat ≈72–87 KiB** — smaller than every competitor at every size, ≈3.4× smaller than BaseFold-1/4 (345 KiB) and ≈58× smaller than Brakedown-0.704 (20.8 MiB) at $2^{24}$.
- **Commitment size**: $|C|=4.1$–4.5 KiB recursive (the pre-commitments $T_Y,T_u,T_R$), 283–2430 KiB non-recursive — the RNS residues of $Y$ dominate the non-recursive commitment.

### 7.3 Hash benchmarks under Binius (Tables 2–4; prover excludes witness generation; ms / KiB)

**Keccak-256**: 873 perms — Binius 165.0/95.6/244.1 vs LaBinius 167.3/96.2/584.8 vs +LaBRADOR 275.7/168.9/**89.1**; 3,495 — 667.2/390.6/310.4 vs 716.3/394.6/1286.7 vs 1011.1/595.2/**86.3**; 13,981 — 2671.0/1564.7/390.5 vs 3187.2/1580.4/2564.1 vs 3641.7/1948.3/**100.1**; 55,924 — 10821.3/6250.7/471.3 vs 12166.0/6266.6/5452.5 vs 13828.4/6969.7/**97.6**.

**SHA-256**: 1,134 compr. — 72.3/36.4/244.2 vs 75.0/37.0/591.4 vs 196.2/112.2/**88.9**; 4,539 — 297.2/144.9/310.5 vs 356.2/153.2/1273.4 vs 654.3/359.1/**86.7**; 18,157 — 1214.2/580.2/390.6 vs 1480.5/632.7/2510.7 vs 2069.1/999.4/**100.3**; 72,628 — 4853.6/2315.2/471.4 vs 5753.1/2488.6/5380.1 vs 6923.1/3191.2/**97.7**.

**BLAKE3**: 2,055 compr. — 99.0/50.4/244.2 vs 100.6/51.0/607.3 vs 210.9/127.6/**88.7**; 8,225 — 401.4/201.5/310.5 vs 434.6/209.6/1261.2 vs 685.6/400.1/**86.6**; 32,906 — 1628.3/809.7/390.6 vs 1870.0/862.0/2633.5 vs 2441.8/1223.2/**100.2**; 131,624 — 6544.8/3240.4/471.4 vs 7334.4/3399.9/5417.8 vs 8485.8/4091.2/**97.6**.

Summary ratios (largest sizes, all three hashes): non-recursive prover ≤1.2×, verifier <1.1×; recursive prover <1.5×, verifier <1.4×; recursive proof ≈5× shorter. Succinct-part-only verification 78–132 ms (Binius), 89–142 ms (non-recursive), 793–835 ms (recursive).

### 7.4 Hash benchmarks under Flock (Tables 5–6; prover includes witness generation; ms / KiB)

**BLAKE3**: 2,048 — Flock 55.3/26.2/369.8 vs LaBinius 58.1/27.6/565.2 vs +LaBRADOR 175.8/112.3/**88.5**; 8,192 — 148.2/27.2/398.6 vs 147.4/28.9/1196.3 vs 439.5/223.6/**85.6**; 32,768 — 560.8/27.9/351.0 vs 505.8/31.7/2450.7 vs 1075.3/396.4/**99.2**; 131,072 — 2121.8/27.3/490.0 vs 1953.9/38.6/5130.3 vs 3072.4/729.0/**96.4**.
**SHA-256**: 1,024 — 56.4/27.2/369.9 vs 54.0/27.4/542.0 vs 181.7/111.5/**88.2**; 4,096 — 149.5/28.5/398.7 vs 148.5/29.9/1146.2 vs 442.8/225.2/**85.7**; 16,384 — 575.1/28.2/351.0 vs 527.2/32.5/2322.3 vs 1093.5/392.9/**99.3**; 65,536 — 2184.1/27.8/490.1 vs 2036.8/38.7/4848.6 vs 3172.3/730.7/**96.5**.

Summary: non-recursive prover ≈0.9× (faster than Flock!), verifier ≈1.4×; recursive prover <1.5×; recursive proof ≈5× shorter; recursive verifier 26–27× Flock's (which stays flat at tens of ms). **Best throughput: 4.3 MB/s BLAKE3 (Flock, non-recursive) = >67,000 compressions/s; 2.7 MB/s recursive.** Hardware: single thread, AMD EPYC 9R05, AWS m8azn.metal-12xl, 192 GiB RAM.

### 7.5 Asymptotic shape

- Non-recursive: commitment/prover linear in witness; proof & verification ∝ $\sqrt{N}$ (balancing $m=\sqrt{N}$, $r=\sqrt{N}$ ⇒ commitment+openings contain $O(\sqrt N)$ ring elements).
- Recursive: LaBRADOR dominates ⇒ prover/commitment ∝ $\sqrt{\cdot}$ of the reduced instance ∝ $N^{1/4}$; proof constant ≈80 KB; verification ∝ $\sqrt N$.

### 7.6 Scaling analysis and application sizing

- **Where the crossover sits**: non-recursive LaBinius beats hash-based PCSs on proof size only after recursion; its *niche* is (a) prover throughput parity with linear-time hash commitments, (b) $\sqrt{N}$-shaped proof/verification, (c) the recursive mode's constant ≈80 KiB proofs. Brakedown dominates raw proof *generation* at small sizes but its proofs are 20–60× larger; WHIR/Ligerito have polylog verification but 1.6–2.3× slower provers.
- **Ethereum sizing (from §1.2)**: ≈660,000 branch-node hashes worst case per block, ≈200,000 hashes/s target, 12 s slot. The BLAKE3 numbers (67,000 compressions/s single core non-recursive ⇒ ≈4.3 MB/s) show one core is short of the target by ≈3×; a multi-core prover (kernels are single-thread in the paper — “All kernels use one thread”) closes the gap with 3–4 cores; the recursive mode (2.7 MB/s) needs ≈8–12 cores. Attestation aggregation (≈28,000/slot) is the same order.
- **IVC outlook (§1.4)**: the paper positions LaBinius as the missing piece for lattice IVC — folding schemes give Ajtai-commitment homomorphism (the Pedersen-analogue role), LaBinius gives efficient proofs of the FS hash computations that recursive verification must certify; “realising this integration remains an open direction”. For the lab this is the natural composition experiment: Cyclo/LatticeFold+ folder × LaBinius hash prover as the in-circuit FS check.

### 7.7 Benchmark reproduction notes

- **Hardware**: AMD EPYC 9R05, AWS m8azn.metal-12xl, 192 GiB RAM, single thread pinned per kernel. The lab's Python port should target the *ratios* (commitment:fold ≈ 1:3–4; prover vs. Brakedown within 25%; recursive prover <2× non-recursive) rather than absolute times — expect ~2 orders of magnitude slowdown from numpy vs. AVX-512.
- **Fairness settings already applied by the authors** (§5.1.6): Flock/Ligerito at 100-bit / rate 1/2; hardware SHA-256 Merkle trees for Flock+Ligerito (BLAKE3 default was slower on their machine); BaseFold/WHIR/Brakedown in unique-decoding, no grinding, 100 bits; Ligerito Johnson-bound profiles with 16-bit grinding at rate 1/4; LaBinius at $\mathbb{F}_{2^{162}}$ vs. others' $\mathbb{F}_{2^{128}}$ (to LaBinius's disadvantage, noted).
- **Version pins**: Binius `81cdfff` (2026-09-14); Flock `b684b12` (2026-09-11); WHIR rows from Binius `37e9cd6` (day before WHIR removal). BinarySpartan excluded (code unavailable at writing time).
- **Prover-time conventions**: Binius rows exclude witness generation; Flock rows include it (Flock generates inside the prover); Flock runs its single-table path (commits the full padded witness) — the path where the LaBinius integration replaces the commitment.

### 7.8 Position within the lab's stack

- **Binary track anchor**: LaBinius is the lab's only lattice PCS whose evaluation field is binary — the bridge between `lzk.gf2` (tower fields, Binius-style front ends) and `lzk.ajtai`/`lzk.ring` (lattice back ends). Every other lab lattice paper (Akita, Greyhound-track, RoKoko, LatticeFold+, Cyclo, Symphony, Hachi) fixes characteristic = commitment modulus.
- **Hachi** (`hachi.md`) is the mirror-image trick: embedding $\mathbb{F}_{q^k}$ *slots* into $R_q$ (same characteristic). LaBinius changes characteristic via the inert-2 ring and $\mathbb{F}_2$-linear packing — compare the two when documenting “field switching” patterns in the lab's ARCHITECTURE.md.
- **Salsa/PROV context**: the Gröbner-attack motivation (§1.1 here, `salsa_probe.md` §6) explains why standard-hash proving (LaBinius's niche) is the sound long-term bet vs. AO primitives; the lab's ring-Gröbner module (P0-4) quantifies the attack side.
- **Symphony** uses the same LaBRADOR recursion idea (wrap prover communication in LaBRADOR) but for folding transcripts; the block/carry encoding of Appendix A is reusable for any $R_Q\to R'_Q$ bridging the lab needs later (e.g. ProtogaLattice PGL-Boot if it must land in a power-of-two ring).

---

## 8. Implementation Notes

### 8.1 Data structures

- `FElt162`: 3×`uint64` word-sliced (bits = consecutive powers of $x$; XOR-combining); `TElt128`: 2×`uint64` GHASH. Word-sliced SIMD: first words of several elements in one register, etc.
- $\mathbb{F}_{2^{162}}$ multiply: 3 diagonal + 3 cross products via `VPCLMULQDQ` (Karatsuba over 64-bit words); reduction folds $x^{162}=x^{81}+1$ **twice**; inner products accumulate the 6 unreduced components per summand and reduce once at the end.
- `SElt`: rank-4 interleaved packing of 4 $\mathbb{F}$-elements into one $S$-element (coefficient position mod 4 = component); NTT in centred slot layout; one signed lane per residue.
- Matrices: $F$ stored in transform layout, read once per commitment; witness kept **in the transform domain of a single RNS limb** across commit→fold (only the folded result is transformed back).
- Challenges: support via partial Fisher–Yates over $[\varphi]$, signs via keyed hash; store support+sign, materialise lazily.

### 8.2 Algorithms & reuse from `lzk`

| LaBinius component | `lzk` reuse / new |
|---|---|
| GF(2^k) tower/extension fields ($\mathbb{F}_{2^{162}}$, $\mathbb{F}_{2^{128}}$ GHASH) | `lzk.gf2` tower core; add the degree-162 non-tower field (3-word, carry-less mult + double fold) |
| $\mathbb{F}_2$-linear maps $\varphi,P_V,\mathrm{lift}$, basis bookkeeping | new tiny module (matrix-free: coordinate copies) |
| $\mathrm{eq}/\widetilde{\mathrm{eq}}/\mathrm{MLE}/\mathrm{vec}$, sumcheck over $\mathbb{F}$ | `lzk.sumcheck` + `lzk.tensor` (little-endian order — matches this paper's convention) |
| Ajtai commitment $Y=FW$, RNS over small primes, mixed-radix NTT | `lzk.ajtai` + `lzk.ring` **new profile**: composite $q$, radix-2/3 mixed NTT, primes {3889, 9721, 17497, 19441, 2917, 4861, 12637} |
| Superring packing (4-way interleave, $R\to S$ embedding) | new |
| CWSS forking lemma | `lzk.forking.cwss` (shared with Cyclo/Symphony) |
| $\Pi_{\mathrm{sw}},\Pi_{\mathrm{left\mbox{-}exp}},\Pi_{\mathrm{fold}}$ | new protocol modules (Figs. 2–4) |
| Bit dropping (Garner/mixed-radix, residual SIS) | new |
| LaBRADOR recursion: chunks/blocks/carries, zero-part, limbs, gadgets, (nowrap) checker | new; LaBRADOR itself from the lab's LaBRADOR track (or the C LaZer via FFI, as the paper does) |
| Fiat–Shamir | `lzk.fs` — recursive statement bound to transcript by a digest of absorbed data |

### 8.3 Complexity & what to benchmark first

1. **Commitment** ($nm$ $S$-mults, linear in $N$): the dominant non-recursive cost; benchmark the packed NTT + dot-product kernel (in the lab's Python: numpy int64 with per-prime Montgomery, expect ~100× slower than AVX-512 — record scaling, not absolute).
2. **Fold** ($mr$ challenge-mults): 3–4× faster than commitment in the paper (single RNS limb, retained transform) — verify this ratio holds in Python.
3. **Sumcheck over $\mathbb{F}_{2^{162}}$** (degree-2, $\nu$ rounds): linear in $2^\nu$ with the 6-component deferred-reduction trick.
4. **Recursive encoding construction** (chunks, carries, gadgets): pure bookkeeping; the LaBRADOR prover then dominates.

### 8.4 Pitfalls

1. **$\varphi$ overload**: Euler totient vs. field-switch packing map vs. LaBRADOR's $\varphi_i^{(k)}$ vectors — rename in code (`totient`, `pack_map`, `lab_phi`).
2. **0-indexed $[n]$ and little-endian $\mathrm{bin}$**: matches Cyclo, clashes with Symphony's 1-indexing; the tensor order *is* the vector index order — assert.
3. **Two different cyclotomics**: $R=\mathbb{Z}[\zeta_{243}]$ (odd conductor, $\Phi=x^{162}+x^{81}+1$) for the scheme vs. $R'_Q=\mathbb{Z}_Q[x]/(x^{\mathrm d}+1)$ for LaBRADOR. Never mix their arithmetic; the block system is the *only* sanctioned bridge.
4. **Carry wrap-around signature**: the last carry $e_{N-1}$ appears in block 0 (unscaled) *and* block $N/2$ (scaled $x^{\varphi/2}$) — both indicator terms, no others; getting $N/2$ wrong (e.g. $p\nmid\varphi/2$) silently breaks the $\Phi_f$ reduction.
5. **Support conditions are soundness-critical** (Lemma 13 end): chunks must vanish on $[c,\mathrm d)$, carries on $[\mathrm d-p,\mathrm d)$; the zero-part test is what enforces this — do not skip repetitions ($\lceil\lambda/\log_2Q\rceil$ independent ones).
6. **(nowrap) is a per-constraint inequality**: recompute $\sum_\ell\|C_{\nu,t,\ell}\|_{\mathrm{op}}\frac{q_\ell-1}{2}\sqrt{n_Y}+\dots< Q/2$ whenever any of $q$, $B$, $\mathrm d$, $c$, $p$ changes; a violation means identities hold only mod $Q$ and the integer-lifting proof collapses.
7. **Challenge injectivity is only mod 2**: $C$ needs *no* invertibility mod $q$ — resist the reflex to reuse LaBRADOR's challenge set unchanged (its differences need invertibility mod its own modulus; here only mod-2 injectivity + operator norm matter).
8. **Extraction is over $K=\mathbb{Q}(\zeta_f)$**: implement rational division with common denominators (the extracted witness is $\bar v/\bar c_j$ — coefficients are fractions); only reduce mod 2 at the very end. Do not emulate division in $R_q$.
9. **Packing vs. commitment layout**: $S$-elements interleave *4 $\mathbb{F}$-elements*; binary claims are per-component because $2$ ramifies in $S$ ($S/2S$ is not a field!) — the mod-2 claims must be read per component, and SIS is over $S$.
10. **Sumcheck message count**: $3\nu$ → $2\nu$ optimisation (footnote 2) is not optional at scale — the degree-2 round polynomial is determined by $g_i(0)+g_i(1)$ (known from previous round) + two sent values.
11. **Verifier's $E(r)\widetilde{\mathrm{eq}}(r'')$ trick**: never materialise $c\in\mathbb{F}_2^{2^\nu}$ (that's the whole point — verifier stays polylog); compute in the $2^\iota$-dimensional algebra $\mathbb{T}\otimes_{\mathbb{F}_2}\mathbb{F}$.
12. **Bit-dropping changes the SIS instance**: the extracted preimage is $(v,-z')$ with bound $\sqrt{B_v^2+B_{z'}^2}$ — re-run the estimator after choosing $d$; $Y_0$ (rounding error) must be handled exactly via Garner, not approximated.
13. **Front-end versioning (§5.1.5/5.1.6 footnotes)**: Binius/Flock codebases differ from their publications (Binius absorbed Flock's univariate skip; Flock lacks Keccak); pin commits (Binius `81cdfff`, Flock `b684b12`, WHIR rows from Binius `37e9cd6`) and apply the fairness modifications (Flock at 100-bit/rate 1/2; hardware SHA-256 Merkle trees) when reproducing Tables 1–6.

### 8.5 Proposed lab module layout

```
lzk/protocols/labinius/
  __init__.py        # LaBiniusPCS: setup/commit/open/eval_proof; recursive mode
  fields.py          # F_2^162 (3-word), T = GHASH F_2^128, packing phi, P_V, lift
  ring_s.py          # superring S = Z[x]/(x^648 - x^324 + 1): packing, embedding R->S
  ntt.py             # mixed-radix NTT over small primes; lazy reduction schedules
  relations.py       # Xi^lin-rel, Xi^bin-lin-rel, Xi^bin-eval-rel, Xi^bin-eval-sw-rel, Xi^sis
  challenges.py      # signed fixed-weight set, Fisher-Yates support, keyed signs, op-norm check
  sw.py              # Figure 2 Pi_sw (E(r), partial evals, sumcheck, z = e^-1 tau)
  leftexp.py         # Figure 3 Pi_left-exp
  fold.py            # Figure 4 Pi_fold
  compose.py         # Corollary 1 chaining + Theorem 1 PCS wrapper
  bitdrop.py         # Garner mixed-radix, residual SIS normal form
  recur/
    blocks.py        # chunks/blocks/carries (Defs. 26-33, Figure 5), Lemma 12/13 engines
    limbs.py         # RNS limb constraints (Eq. limb), binary constraints (Eq. bin)
    zeropart.py      # Eq. (zero) randomised tests
    gadgets.py       # base-B digit decompositions + caps
    nowrap.py        # Eq. (nowrap) checker over the constraint inventory
    encode.py        # I_rec assembly (Def. 35) -> LaBRADOR instance
  params.py          # Table 1 profile; estimator hooks incl. subfield/Q(zeta_3) attacks
  bench.py           # Tables 1-6 reproduction (scaled)
tests/test_labinius_*.py
```

### 8.6 Test plan

1. **Field units**: $\mathbb{F}_{2^{162}}$ mult/reduce ($x^{162}=x^{81}+1$ twice), GHASH $\mathbb{F}_{2^{128}}$; packing round-trips $\varphi^{-1}\varphi=\mathrm{id}$, $P_V$ idempotent, Lemma 7 commutation on random $E,\psi$.
2. **Ring units**: $\mathrm{Dec}_c\mathrm{Enc}_c=\mathrm{id}$ (Def. 30); Lemma 12 exactness for random $g,\xi$; **Figure 5 reconstruction**: random $W,c$ → compute carries by the constructive proof of Lemma 13 → check every (block) equation and that $e_{N-1}=W_{\text{quotient}}$.
3. **Relation round-trips**: honest binary $W$ satisfies all four relations exactly; slacked variants satisfy the relaxed forms with the right bounds.
4. **$\Pi_{\mathrm{sw}}$ end-to-end** on a toy ($\nu=4$, $\iota=3$): honest path accepts; malicious $\widetilde w'$ (violating the switch claim) rejected w.p. $\ge1-(2\nu+\iota)/|\mathbb{F}|$; abort-on-$e=0$ frequency matches $(\nu+\iota)/|\mathbb{F}|$.
5. **$\Pi_{\mathrm{fold}}$ forking simulation**: two transcripts differing in coordinate $j$; verify $w^{(j)}=v^{(j)}-v^{(r)}$, $s^{(j)}=c^{(j)}_j-c^{(r)}_j\notin2R$, and the assembled relaxed witness opens $Y$.
6. **Composition**: small Binius-style claim (e.g. 32-word binary MLE) through all three reductions to the folded $v$; final $\Xi^{\mathrm{bin\mbox{-}lin}}_1$ check passes.
7. **Bit dropping**: Garner reconstruction $Y=Y_0+2^dY_1$ exact; verifier's $z'$ path equals the undropped check on the same $v$; SIS bound recomputed with $\sqrt{B_v^2+B_{z'}^2}$.
8. **Recursion encoding**: build $I_{\mathrm{rec}}$ for a folded instance; (nowrap) satisfied; a mock-LaBRADOR (native checker) accepts; corrupt one forbidden coefficient ⇒ zero-part test fails w.p. $1-2^{-\lambda}$.
9. **Benchmark parity**: commitment:fold time ratio ≈1:3–4; linear scaling of commitment in $N$.

### 8.7 Estimated lab (Python) build effort

| Module | LOC est. | Depends on | Notes |
|---|---|---|---|
| `fields.py` | ~200 | `lzk.gf2` | F_2^162 (3-word CLMul via Python ints: `(a*b)` carry-less emulation or bit-slicing), GHASH T, packing |
| `ring_s.py` | ~150 | new | superring packing, embedding, per-component binary reads |
| `ntt.py` | ~250 | `lzk.ring` | mixed radix-2/3, 7 small primes, lazy schedules; RNS limbs; Garner |
| `relations.py` | ~120 | — | 4 relations + checkers (exact/relaxed) |
| `challenges.py` | ~80 | — | Fisher–Yates support, keyed signs, op-norm via Fourier slots |
| `sw.py` | ~150 | `lzk.sumcheck` | Fig. 2 incl. E(r) construction and verifier algebra trick |
| `leftexp.py` | ~60 | — | Fig. 3 |
| `fold.py` | ~60 | — | Fig. 4 |
| `compose.py` | ~80 | all three | Corollary 1 chaining, Theorem 1 wrapper |
| `bitdrop.py` | ~100 | `ntt.py` | Garner mixed-radix, residual path |
| `recur/` | ~600 total | lab's LaBRADOR | blocks, limbs, zeropart, gadgets, nowrap, encode; mock-LaBRADOR first |
| `params.py` | ~100 | — | Table 1 profile, estimator hooks (subfield attacks incl. Q(ζ₃)) |
| tests | ~600 | all | §8.6 plan |

**Staging**: (1) `fields.py` + Lemma 2/7 tests; (2) `relations.py` + toy round-trip (§4.9); (3) `sw.py` on $\nu=4$ toy; (4) `leftexp`+`fold`+`compose` — the non-recursive PCS, benchmarkable end-to-end vs. a Merkle-tree baseline; (5) `bitdrop`; (6) `recur/` with a *native-checker mock* standing in for LaBRADOR (validates the encoding, (nowrap), zero-part); (7) link the lab's LaBRADOR implementation or the C library. Front ends (Binius/Flock reductions) are external: consume their output shape — a bit-level claim $(r,t,\omega)$ — via a small adapter, so the lab can also drive `labinius` with hand-written binary circuits (e.g. a toy Keccak-f permutation over $\mathbb{F}_2$).

### 8.8 What the lab gets out of it (deliverable framing)

1. A **post-quantum binary PCS** the lab can benchmark against BaseFold/WHIR-style Merkle commitments at $2^{16}$–$2^{22}$ element scales, filling the “smallest PQ proof of a standard hash” row in the lab's comparison matrix.
2. The **decoupled-modulus architecture** as a reusable pattern: any lab protocol currently stuck with a partially-splitting $q$ (for challenge invertibility) can adopt number-field extraction + mod-$p$-injective challenges to unlock fully-splitting composites — audit Cyclo/LatticeFold+ specs for this refactor once `labinius` validates the technique.
3. The **block/carry bridge** (Appendix A) for crossing between odd-conductor and power-of-two rings inside one proof — needed again if PGL-Boot or the SALSAA folding applications must compose with LaBRADOR-style compressors.

---

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
