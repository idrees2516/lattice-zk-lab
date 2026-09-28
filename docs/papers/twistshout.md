# Twist and Shout: Faster Memory Checking Arguments via One-Hot Addressing and Increments — Deep Analysis & Implementation Spec

> Source: `papers_txt/twistshout.txt` (Setty–Thaler, ePrint 2025/105, ~6.3k extracted lines).
> All equation/figure/theorem numbers below are cross-referenced to the paper.

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Twist and Shout: Faster memory checking arguments via one-hot addressing and increments |
| **Authors** | Srinath Setty (Microsoft Research), Justin Thaler (a16z crypto research and Georgetown University) |
| **Venue/date** | ePrint 2025/105; cited by Akita as "CRYPTO 2026" |
| **Assumption** | None beyond the polynomial commitment scheme it is composed with (elliptic-curve PCS like HyperKZG/Zeromorph/Dory/Hyrax, or binary-field hashing PCS like Binius/FRI-Binius/Blaze). Pure PIOP + sum-check machinery. |
| **Headline** | A new memory-checking method — **one-hot addressing and increments** — instantiated by two protocol families: **Twist** (read/write memories) and **Shout** (read-only memories / lookup arguments). Both have **logarithmic verifier costs** and, unlike all prior work, **invoke no grand-product or grand-sum arguments**. >10× prover speedup vs state-of-the-art log-proof memory checking; ≥2–4× vs prior work configured for larger proofs. |

Key claims:

- Twist = "Tracking Write Increments via Sum-check Techniques"; Shout = "Sum-check-based
  Handling of Unchanging Tables". Both are families parameterized by integer $d\ge1$:
  prover commits to $d\cdot K^{1/d}$ values in $\{0,1\}$ per memory operation ($d$ ones and
  the rest zeros), instead of $K$ values at $d=1$. Small $d$ ⇒ cheaper operations but bigger
  commitment keys (curve PCS) / slower commitments (hashing PCS).
- With elliptic-curve commitments: committing to 0s is **free** (a committed 0 does not
  alter the MSM), committing to 1 costs one group op; "small" values
  ($\{0,\dots,2^{32}-1\}$) cost 1–2 group ops via Pippenger; random values ~11 group ops.
- Cost profile matches real CPUs: small memories are cheaper than large ones; the Twist
  prover is faster for **local** memory accesses ($2^i$-local access costs $O(i)$ field
  multiplications vs $O(\log K)$ worst case).
- Soundness error only $\log(TK)/|\mathbb{F}|$ (vs $(T+K)/|\mathbb{F}|$ for offline memory
  checking) — relevant for 64-bit-base-field curves with 128-bit subfield challenges
  (offline memory checking drops to 88–98 bits there; one-hot addressing keeps >120 bits).
- Two new SNARKs for non-uniform constraint systems built from Shout:
  **SpeedySpartan** (Plonkish; ~50× fewer field multiplications and ~75× lower commitment
  cost than Plonk; 4× lower commitment cost than BabySpartan) and **Spartan++** (CCS/R1CS;
  ~6× faster prover than Spartan; commits only to multiplication-gate outputs).
- Also yields **Spark++**, a sparse multilinear polynomial commitment scheme (Shout viewed
  as an advance in sparse PCS rather than lookup arguments).

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $K$ | memory size (number of cells/registers/lookup-table entries) |
| $T$ | number of memory operations; read-only: $T$ reads; read/write: $T$ reads + $T$ writes ($2T$ ops, alternating read-then-write, cycles numbered $0..T$ for both reads and writes) |
| $d$ | one-hot dimension parameter ($N=K^{1/d}$); $1\le d\le\log K$ |
| $N$ | $=K^{1/d}$, side length of the $d$-dimensional address cube |
| $\mathbb{F}$ | field of the PIOP (scalar field of the curve group for curve-based PCS) |
| $\mathrm{Val}(k)$ | fixed value of memory cell $k$ (read-only memory / lookup table) |
| $\mathrm{Val}(k,j)$ | value stored in cell $k$ at cycle $j$ (read/write memory) |
| $raf, waf\in\mathbb{F}^T$ | read/write addresses specified by one field element per cycle ("f" = field-element form) |
| $rv, wv\in\mathbb{F}^T$ | values returned by reads / values written by writes |
| $ra, wa\in\{0,1\}^{T\cdot K}$ | one-hot encodings of all $T$ read/write addresses; $ra(k,j)=1$ iff register $k$ read at cycle $j$ |
| $ra_i(\cdot,j)$, $i=1..d$ | $d$-dimensional one-hot encoding components, each of length $K^{1/d}$; $ra_i(k_i,j)=1$ iff $i$-th coordinate of $raf(j)$ equals $k_i$ |
| $\tilde{ra},\tilde{wa},\tilde{rv},\tilde{wv},\tilde{raf},\tilde{waf},\widetilde{Val},\widetilde{Inc}$ | multilinear extensions (MLEs) of the corresponding vectors |
| $\mathrm{Inc}(k,j)$ | increment: $\mathrm{Inc}(k,j):=\mathrm{Val}(k,j{+}1)-\mathrm{Val}(k,j)=wa(k,j)\cdot(wv(k,j)-\mathrm{Val}(k,j))$ (Eq. 9) |
| $\widetilde{eq}(x,e)$ | MLE of equality function: $\prod_{i=1}^{s}(x_ie_i+(1-x_i)(1-e_i))$ (Eq. 15) |
| $\mathrm{LT}(j',j)$ | less-than predicate: 1 iff $\mathrm{int}(j')<\mathrm{int}(j)$; $\widetilde{LT}$ its MLE (evaluable in $O(\log T)$ ops) |
| $\mathrm{int}(j)$ | integer with binary representation $j$: $\sum_{i=1}^{\log T}2^{i-1}j_i$ |
| $r_{cycle}, r', r''$ | verifier-chosen random evaluation points for the cycle variables |
| $r_{address}, r, \tau$ | verifier-chosen random points for address/register variables |
| $r^{(1)}_{address},\dots,r^{(d)}_{address}$ | per-component random points ($d$ blocks of $\log(K)/d$ challenges) |
| $E, E^*, B, C, D, F, G_i, H_i, A_i, I$ | prover arrays in the fast sum-check implementations (see §5.6–5.8) |
| $s_i(c)$ | sum-check round-$i$ univariate polynomial; evaluation points $c\in\{0,\dots,d_i+1\}$ (with $s_i(1)$ free and, via Gruen, $s_i(d_i+1)$ avoidable) |
| $s'_i(c)$ | Gruen's reduced round polynomial (degree $d$ instead of $d+1$; eq-factor stripped) |
| $z$ | batching challenge for parallel sum-check instances (§4.2.1); also selector in Jolt prefix-reduction |
| $c$ (matrix context) | integer with $cK^{1/(cd)}=o(T)$ chunking parameter for sparse-dense sum-check |
| $C$ | integer with $K^{1/C}=o(T)$ (structured tables, $K\approx T^C$) |
| $q_l,q_r,q_o,q_m,q_c\in\mathbb{F}^m$ | Plonkish selector vectors |
| $A,B,C\in\mathbb{F}^{m\times n}$ | sparse matrices whose rows are unit vectors (one-hot address selections) |
| $z=(w,x)$ | witness + public IO vector in Plonkish/R1CS |
| $\tilde z,\tilde z_A,\tilde z_B,\tilde z_C$ | MLEs of witness and of $Az,Bz,Cz$ (the latter two virtual) |
| $m,n,\ell$ | Plonkish bounds: constraints, witness+IO size, public IO size ($\ell<n$) |
| $\mathrm{addr}^M,\mathrm{addr}^M_i$ | preprocessed one-hot address polynomials for matrix $M\in\{A,B,C\}$ |
| $\lambda$ | security parameter |

## 3. Algebraic Setting

- No exotic algebra: everything is over a finite field $\mathbb{F}$ (large prime field for
  curve-based deployments; binary/tower fields when combined with Binius — note that the
  Hamming-weight-one trick via evaluation at $(2^{-1},\dots,2^{-1})$ fails over binary
  fields, replaced there by a direct sum-check, §4.1.2).
- **Multilinear polynomials**: degree ≤ 1 per variable; unique MLE $\tilde f$ extending
  $f:\{0,1\}^\ell\to\mathbb{F}$; Lagrange form $\tilde u(x)=\sum_yu_y\widetilde{eq}(y,x)$;
  Fact 3.1: $p(c,x')=(1-c)p(0,x')+c\,p(1,x')=p(0,x')+c(p(1,x')-p(0,x'))$.
- **Lemma 1 (Vu et al.)**: all Lagrange basis polynomials at $r\in\mathbb{F}^{\log m}$
  computable with $m$ multiplications (array-doubling $A_{i+1}[x,1]=r_iA_i[x]$,
  $A_{i+1}[x,0]=A_i[x]-A_{i+1}[x,1]$); $\tilde u(r)$ with $2m$ multiplications.
- **Sum-check** (§3.3): $\ell$ rounds; round $i$ message has $d_i$ field elements
  ($d_i$ = degree in variable $i$); perfect completeness; soundness error
  $\sum_id_i/|\mathbb{F}|$; verifier $O(\sum_id_i)$ + one final evaluation.
- **Linear-time sum-check prover** (§3.3): for
  $\sum_x\widetilde{eq}(r',x)\prod_{i=1}^{\ell}p_i(x)$ with $N=2^n$... (with arrays
  $A_1..A_\ell$ of $p_i$ evaluations and $B$ of $\widetilde{eq}(r',x)$): naive
  $(\ell^2+3\ell+2)N$ multiplications; with Dao–Thaler [DT24] ($B$-array elimination),
  omission of $c'=1$, and Gruen [Gru24] ($c'=\ell+1$ avoidance): ~$(\ell^2+\ell)N$.
- **Zero-check PIOP** (§3.6): to prove $g(x)=0$ on $\{0,1\}^\ell$, verify
  $\sum_x\widetilde{eq}(r,x)g(x)=0$ for random $r$; soundness $\ell/|\mathbb{F}|$ + sum-check error.
  **Gruen's optimization** (§3.6.1): send $s'_i(c)=A\cdot C(c)$ (strip the degree-1 factor
  $B(c)=r_ic+(1-r_i)(1-c)$ contributed by variable $i$ to $\widetilde{eq}$); then
  $s_i(c)=s'_i(c)B(c)$ recoverable in time depending only on $d$; saves one evaluation
  point per round.
- **One-hot encodings** (§3.7): 1-D: unit vector $e_z\in\mathbb{F}^K$. $d$-dimensional:
  the $d$ unit vectors $v_1..v_d$ of length $K^{1/d}$ with
  $(e_z)_k=\prod_{i=1}^dv_i(k_i)$ for $k=(k_1..k_d)\in[N]^d$; if $z\leftrightarrow(z_1..z_d)$
  under the natural bijection $[K]\leftrightarrow[N]^d$, then $v_i=e_{z_i}$.
- **Commitments** (curve-based, §3.1): Pedersen-style MSM
  $\prod_{x_i}g_i^{y_i}$ over the commitment key; committing to 0 is free; 1 costs one
  group op (sum of $g_i$ over $\{i:y_i=1\}$); small negatives via precomputed inverted key
  $h_i=g_i^{-1}$ (needed for increments!). Evaluation proofs for HyperKZG/Zeromorph
  require MSMs over random vectors of length $n$ (2^ℓ) regardless of sparsity; amortized by
  splitting into $2^{\ell_1}$ commitments to $\ell_2$-variate polynomials (commitment size
  grows $2^{\ell_1}$, verifier does $2^{\ell_1}$ exponentiations) or by folding.
- **Analytic cost model** (§3.1.2): 256-bit field multiplication = 40–80 cycles; group
  operation ≈ 6 field multiplications; small committed value = 1 group op; random value
  ≈ 11 group ops; scalar multiplication ≈ 400 group ops; pairing ≈ 10 scalar
  multiplications (~4000 group ops); field additions ignored.
- **Commitment schemes**: HyperKZG/Zeromorph (1 group element commitment, powers-of-tau
  SRS of size $N=2^\ell$, log-size eval proofs, 2–3 pairings + log MSM to verify);
  Dory (transparent; $\sqrt N$ elements of $G_1$ and $G_2$ key; commitment = $\sqrt N$
  MSMs of length $\sqrt N$ **plus a multi-pairing of size $\sqrt N$** (can be reduced to
  $\sqrt N/t$ with key $t\sqrt N$); eval proofs $6\log N$ target-group elements; target-group
  ops ~6× slower than $G_1$); Hyrax (linear field work eval proofs; sparse: $\sqrt N+O(\sqrt M)$
  mults for $M$ nonzeros; $\sqrt N$ commitment and proof sizes; transparent);
  Bulletproofs/IPA and HyperKZG eval proofs require committing to linear amounts of random
  data — poor fits.
- **Hashing-based over binary fields** (§2.1): commitment key is tiny, but 0s are not free;
  pack 128 values into one GF($2^{128}$) element (Binius/FRI-Binius/Blaze); need
  $dK^{1/d}$ ∈ [a few dozen, a couple hundred] bits per address; Booleanity-checking can be
  omitted because the PCS enforces it (Figure 8 note).

## 4. Relations

### 4.1 The memory-checking problem (§2.2)

- **Read/write**: prover commits to $raf,waf,rv,wv\in\mathbb{F}^T$. Must prove:
  $rv(j)=wv(j')$ where $j'<j$ is the largest cycle with $waf(j')=raf(j)$; if none, $rv(j)=0$
  (all registers initialized to 0; nonzero initial contents can be committed/public).
- **Read-only**: contents public (the *lookup table* $\mathrm{Val}$); each cycle is a single read.
- **One-hot formulation**: internally, addresses are unit vectors
  $ra(j)=e_\ell\in\{0,1\}^K$. The zkVM-facing $raf$/$waf$ polynomials are **virtual**:
  not committed, but query-accessible via sum-check reductions from $\tilde{ra},\tilde{wa}$.
  Likewise $\widetilde{rv}$ may be virtual.

### 4.2 Core one-hot-addressing identities

- **Read validity (read-only, Eq. 3)**: for every cycle $j$:
  $\sum_{k}ra(k,j)\mathrm{Val}(k)=rv(j)$ — a rank-one constraint system of $K\cdot T$
  variables with only ~$T$ non-zeros. (Already explicit in
  [ZBK+22, ZGK+22, STW24, GM24].)
- **Read validity (read/write, Eq. 7)**: $\sum_kra(k,j)\mathrm{Val}(k,j)=rv(j)$.
- **Increments (Eq. 9)**:
  $\mathrm{Inc}(k,j):=\mathrm{Val}(k,j{+}1)-\mathrm{Val}(k,j)=wa(k,j)\cdot(wv(k,j)-\mathrm{Val}(k,j))$.
  Only one register written per cycle ⇒ exactly one non-zero increment per cycle, and it
  is small ($\in\{-2^{32}-1,\dots,2^{32}-1\}$ for 32-bit registers). At $d$-dimensional
  one-hot: $wa$ factor becomes $\prod_{i=1}^d\tilde{wa}_i(k_i,j)$ (Eq. 37).
- **Virtual Val via increments (Eq. 36)**:
  $\widetilde{Val}(k,j)=\sum_{j'}\widetilde{Inc}(k,j')\widetilde{LT}(j',j)$
  (register value at time $j$ = sum of all prior increments).
- **Virtual $raf$ (Eq. 27)**: $\widetilde{raf}(j)=\sum_k(\sum_i2^ik_i)\,ra(k,j)$;
  $d$-dimensional version (§4.2):
  $\widetilde{raf}(r''_{cycle})=\sum_{k,j}\widetilde{eq}(r''_{cycle},j)\big(\sum_{i,\ell}2^{i\cdot\log(K)/d+\ell}k_{i,\ell}\big)\prod_{i=1}^d\tilde{ra}_i(k_i,j)$.
- **Booleanity (Eq. 24)**: $ra(k,j)^2-ra(k,j)=0$ for all $(k,j)$.
- **Hamming-weight-one (Eq. 25)**: $\sum_kra(k,j)=1$ for all $j$;
  over non-binary fields checkable by ONE evaluation query since
  $\sum_k\tilde{ra}(k,r')=K\cdot\tilde{ra}(2^{-1},\dots,2^{-1},r')$ (Eq. 26).
- **Permutation-check fingerprint (Lipton's trick, Eq. 1)** — what prior work uses and
  Twist/Shout *eliminate*: $\prod_i(a_i-r)=\prod_i(b_i-r)$, soundness $\ell/|\mathbb{F}|$,
  implemented via grand-product (Spice/Lasso) or grand-sum-of-inverses (LogUp) arguments.

### 4.3 SpeedySpartan / Spartan++ relations

- **Plonkish** (Def. 9.1): $(q_l)_iz_{a_i}+(q_r)_iz_{b_i}+(q_o)_iz_{c_i}+(q_m)_i(z_{a_i}\cdot z_{b_i})+(q_c)_i=0$;
  as matrices: $q_l\circ Az+q_r\circ Bz+q_o\circ Cz+q_m\circ Az\circ Bz+q_c=0$, with
  $A,B,C$ having one 1 per row (one-hot address selections into the "table" $z$).
- **Spartan sum-check target (Eq. 82/83)**:
  $f(x)=\tilde q_l(x)\tilde z_A(x)+\tilde q_r(x)\tilde z_B(x)+\tilde q_o(x)\tilde z_C(x)+\tilde q_m(x)\tilde z_A(x)\tilde z_B(x)+\tilde q_c(x)$
  (or $(1-\tilde q_m)(\tilde z_A+\tilde z_B)+\tilde q_m\tilde z_A\tilde z_B$ for arithmetic circuits).
- **R1CS (Spartan++)**: $Az\circ Bz=w$ where $w$ = multiplication-gate outputs;
  zero-check (Eq. 85): $\sum_x\widetilde{eq}(r,x)(\tilde a(x)\tilde b(x)-\tilde w(x))=0$;
  $\tilde a(r')=\sum_j\tilde A(r',j)\tilde z(j)$, $\tilde b(r')=\sum_j\tilde B(r',j)\tilde z(j)$.
- **Spark++ sparse commitment** (§9.3.1): commitment to $T$-sparse (0/1-valued) $\ell$-variate
  $p$ = $d$ one-hot polynomials encoding $S=\{x:p(x)\ne0\}$;
  $p(r)=\sum_{k_1..k_d,j}\prod_i\tilde{ra}_i(k_i,j)\cdot\widetilde{eq}(k,r)$ — i.e. Shout
  read-checking into the table $\mathrm{Val}(k)=\widetilde{eq}(k,r)$ (MLE-structured).

## 5. Protocols — full step-by-step transcription

### 5.1 Figure 5 — Core Shout PIOP, $d=1$ (MLE-structured table)

1. P and V agree on size-$K$ table with MLE $\widetilde{Val}$ (evaluable in $O(\log K)$).
   P has committed to $\tilde{ra}:\mathbb{F}^{\log K}\times\mathbb{F}^{\log T}\to\mathbb{F}$.
   P wants to give V query access to the virtual polynomial $\tilde{rv}$ defined by
   $\tilde{rv}(j)=\sum_k\tilde{ra}(k,j)\widetilde{Val}(k)$ for all $j\in\{0,1\}^{\log T}$.
2. V → P: desired evaluation point $r_{cycle}\in\mathbb{F}^{\log T}$.
3. V and P run sum-check to compute
   $\tilde{rv}(r_{cycle})=\sum_{k\in\{0,1\}^{\log K}}\tilde{ra}(k,r_{cycle})\cdot\widetilde{Val}(k)$.
   (RHS is multilinear in $r_{cycle}$ — this is the $d=1$ special case.)
4. Let $r_{address}$ be the sum-check randomness. In the final round V evaluates the
   committed $\tilde{ra}$ at $(r_{address},r_{cycle})$ (via PCS) and evaluates
   $\widetilde{Val}(r_{address})$ itself in $O(\log K)$ time.

**Theorem 1**: perfect completeness; soundness error $(2\log K+\log T)/|\mathbb{F}|$ (assuming
one-hot addresses; one-hot correctness is checked separately).
Prover cost (Thm 5): $3K+T$ field multiplications ($T$ to build $E=\widetilde{eq}(j,r_{cycle})$,
lookups to build $F[k]=\tilde ra(k,r_{cycle})$, then $3K$ standard prover; the $K$ additive term
is removed for structured tables via sparse-dense sum-check).

### 5.2 Figure 6 — one-hot-encoding-checking PIOP, $d=1$

Input: P committed to $\tilde{ra}$, claims each $ra(\cdot,j)$ is the one-hot encoding of some
$raf(j)\in\{0,\dots,K-1\}$, and (optionally) $\tilde{raf}(r_{cycle})=y$.

1. V → P: random $(r,r')\in\mathbb{F}^{\log K}\times\mathbb{F}^{\log T}$.
2. **Booleanity check** — sum-check over $(k,j)\in\{0,1\}^{\log K}\times\{0,1\}^{\log T}$:
   $0=\sum\widetilde{eq}(r,k)\widetilde{eq}(r',j)\big(\tilde{ra}(k,j)^2-\tilde{ra}(k,j)\big)$ (Eq. 29).
3. Let $(r'_{address},r'_{cycle})$ be that sum-check's randomness.
4. **Hamming-weight-1 check**: sum-check to confirm
   $1=\sum_{k\in\{0,1\}^{\log K}}\tilde{ra}(k,r'_{cycle})$ (Eq. 26 form; over non-binary
   fields this can instead be done with one evaluation query at
   $(2^{-1},\dots,2^{-1},r'_{cycle})$).
5. **$\tilde{raf}$-evaluation sum-check** (run in parallel with Line 5):
   $y=\sum_k\big(\sum_{i=0}^{\log K-1}2^ik_i\big)\tilde{ra}(k,r'_{cycle})$;
   randomness $r''_{address}$.
6. Final-round checks: V evaluates $\widetilde{eq}(r,r'_{address})$,
   $\widetilde{eq}(r',r'_{cycle})$ itself; queries $\tilde{ra}$ at
   $(r'_{address},r'_{cycle})$ and $(r''_{address},r'_{cycle})$ (reducible to a single
   evaluation by standard batching).

**Theorem 2**: perfect completeness; soundness $(6\log K+4\log T)/|\mathbb{F}|$.
Prover: Booleanity $O(K)+2T$ mults; Hamming-weight-one $O(K)$; $\tilde{raf}$-evaluation
$O(K)$ given an $E$ array (which itself costs $O(\sqrt{KT})=o(T)$ via the $D''/D'''$ split trick).

### 5.3 Figure 7 — Core Shout PIOP, general $d>1$ (MLE-structured table)

1. P committed to $\tilde{ra}_1,\dots,\tilde{ra}_d:
   \mathbb{F}^{\log(K)/d}\times\mathbb{F}^{\log T}\to\mathbb{F}$. Wants query access to
   virtual $\tilde{rv}$ with
   $\tilde{rv}(j)=\sum_{k=(k_1,..,k_d)}\prod_{i=1}^d\tilde{ra}_i(k_i,j)\widetilde{Val}(k)$.
2. V → P: random $r_{cycle}\in\mathbb{F}^{\log T}$.
3. **Read-checking sum-check**: confirm
   $\tilde{rv}(r_{cycle})=\sum_{k,j}\widetilde{eq}(r_{cycle},j)\prod_{i=1}^d\tilde{ra}_i(k_i,j)\widetilde{Val}(k)$ (Eq. 30).
   (Degrees: 3 in each $k$ variable, $2+d$ in each $j$ variable ⇒ prover $O(K+d^2T)$.)
4. Let $r_{address}=(r^{(1)}_{address},\dots,r^{(d)}_{address})$ be the randomness over the
   first $\log K$ rounds and $r'_{cycle}$ over the final $\log T$ rounds. V queries each
   $\tilde{ra}_i$ at $(r^{(i)}_{address},r'_{cycle})$ and evaluates
   $\widetilde{Val}(r_{address})$ in $O(\log K)$.

**Theorem 3**: Figure 7 soundness $\le((d+2)\log T+2\log K)/|\mathbb{F}|$; Figure 8
soundness $\le(4d\log T+6\log K)/|\mathbb{F}|$; both perfectly complete.

**Batching parallel sum-checks (§4.2.1)**: for $t$ parallel instances, apply one sum-check
to $\sum_\ell z^{\ell-1}\cdot(\text{summand}_\ell)$ (Eq. 32); +$t/|\mathbb{F}|$ soundness;
also prover-time benefits (shared arrays).

### 5.4 Figure 8 — one-hot-encoding-checking PIOP, general $d$

Input: P committed to $\tilde{ra}_1..\tilde{ra}_d$; claims
$(ra_1(\cdot,j),..,ra_d(\cdot,j))$ is the correct $d$-dimensional one-hot encoding of
$raf(j)$ for all $j$, and optionally $\tilde{raf}(r'_{cycle})=y$.

1. V → P: random $(r,r')$ ($r\in\mathbb{F}^{\log(K)/d}$; set $r'=r_{cycle}$ if the core PIOP
   already chose it — shares the $E^*$ table).
2. **Booleanity check** ($d$ parallel sum-checks, batchable): for $i=1..d$,
   $0=\sum_{k,j}\widetilde{eq}(r,k)\widetilde{eq}(r',j)\big(\tilde{ra}_i(k,j)^2-\tilde{ra}_i(k,j)\big)$.
   (Omittable entirely if the PCS enforces Booleanity, e.g. Binius.)
3. **Hamming-weight-1 check**: for each $i$: $1=\sum_{k_i}\tilde{ra}_i(k_i,r''_{cycle})$
   ($r''_{cycle}$ any point chosen after the $\tilde{ra}_i$ were committed).
4. **$\tilde{raf}$-evaluation sum-check** (in parallel with Booleanity and the core
   read-checking sum-check):
   $y=\sum_{k,j}\widetilde{eq}(r'_{cycle},j)\big(\sum_{i=1}^d\sum_{\ell=0}^{\log(K)/d-1}2^{i\cdot\log(K)/d+\ell}k_{i,\ell}\big)\prod_{i=1}^d\tilde{ra}_i(k_i,j)$.
   (Equivalent to read-checking into the "int" table $\mathrm{Val}(k)=\mathrm{int}(k)$;
   batchable with the core read-checking sum-check by replacing
   $\widetilde{Val}\to\widetilde{Val}+z\cdot\widetilde{int}$.)

### 5.5 Figure 9 — Core Twist PIOP, $d\ge1$ (read/write memory)

Input: P has committed to $\tilde{Inc}:\mathbb{F}^{\log K}\times\mathbb{F}^{\log T}\to\mathbb{F}$,
$\tilde{wv}:\mathbb{F}^{\log T}\to\mathbb{F}$, and
$\tilde{ra}_1,\tilde{wa}_1,\dots,\tilde{ra}_d,\tilde{wa}_d:
\mathbb{F}^{\log(K)/d}\times\mathbb{F}^{\log T}\to\mathbb{F}$. $\widetilde{Val}$ is the
virtual polynomial $\widetilde{Val}(k,j)=\sum_{j'}\widetilde{Inc}(k,j')\widetilde{LT}(j',j)$.
P wants query access to virtual $\tilde{rv}$ with
$\tilde{rv}(j)=\sum_k\prod_i\tilde{ra}_i(k_i,j)\widetilde{Val}(k,j)$.

1. V → P: desired evaluation point $r'\in\mathbb{F}^{\log T}$ for $\tilde{rv}$; random
   $r\in\mathbb{F}^{\log K}$. Then two sum-checks run **in parallel**:
2. **Read-checking sum-check** (Eq. 33):
   $\tilde{rv}(r')=\sum_{k,j}\widetilde{eq}(r',j)\prod_{i=1}^d\tilde{ra}_i(k_i,j)\widetilde{Val}(k,j)$.
3. **Write-checking sum-check** (Eq. 34): confirm
   $\tilde{Inc}(r,r')=\sum_{k,j}\widetilde{eq}(r,k)\widetilde{eq}(r',j)\prod_{i=1}^d\tilde{wa}_i(k_i,j)\big(\tilde{wv}(j)-\widetilde{Val}(k,j)\big)$.
4. At the end of both, for random $(r_{address},r_{cycle})$ V must evaluate
   $\tilde{wa}(r_{address},r_{cycle})$, $\tilde{wv}(r_{cycle})$,
   $\tilde{ra}(r_{address},r_{cycle})$ (from commitments) and
   $\widetilde{Val}(r_{address},r_{cycle})$ (from the next sum-check).
5. **$\widetilde{Val}$-evaluation sum-check** (Eq. 11):
   $\widetilde{Val}(r_{address},r_{cycle})=\sum_{j'\in\{0,1\}^{\log T}}\widetilde{Inc}(r_{address},j')\cdot\widetilde{LT}(j',r_{cycle})$.
6. Final round: V evaluates $\widetilde{LT}$ at the random point itself in $O(\log T)$;
   queries the committed $\tilde{Inc}$.

Running read- and write-checking in parallel ensures only ONE $\widetilde{Val}$ evaluation
is needed (one Val-evaluation sum-check serves both). One-hot correctness of both $\tilde{ra}$
and $\tilde{wa}$ is checked by Figure 8 (with $ra\to wa$ substitutions).

**Theorem 4**: perfect completeness; soundness $\le((2d+3)\log T+3\log K)/|\mathbb{F}|$.

### 5.6 Fast Shout provers — small memories (§6)

**Core Shout $d=1$ (Thm 5): $3K+T$ multiplications.** Build
$E^*[j]=\widetilde{eq}(j,r_{cycle})$ ($T$ mults); $F[k]=\tilde{ra}(k,r_{cycle})$ by
additions/lookups into $E^*$; standard prover $3K$.

**Core Shout general $d$ (§6.2, Thm 6): $(d^2+d+1)T+5K+o(T)$; if $K^{1/d}=o(T)$:
$(d^2+1)T+5K+o(T)$.** Bind all $\log K$ address variables FIRST, then $\log T$ cycle variables.
- Precompute $E^*[j]=\widetilde{eq}(r_{cycle},j)$ ($T$ mults).
- **First $\log K$ rounds**: two halving arrays: $A[k]\leftarrow\widetilde{Val}(k)$,
  $C[k]\leftarrow v_k=\sum_{j:ra(k,j)=1}\widetilde{eq}(r_{cycle},j)$ (initialization free).
  Bind per round (Eq. 20). Key fact (Eq. 46): after $m$ rounds, for each $y_{cycle}$ exactly
  one $y_{mem}$ has $\tilde{ra}(r_1..r_m,y_{mem},y_{cycle})\ne0$, equal to
  $\widetilde{eq}((k_1..k_m),(r_1..r_m))$. Round message:
  $s_m(c')=\sum_kA[c',k]C[c',k]$ (Eqs. 50–51) — 4K total.
- **Final $\log T$ rounds** ($d=1$): build $E[j]=\tilde{ra}(\tau,j)=\widetilde{eq}(\tau,k_j)$
  via a size-$K$ eq-table ($K$ mults) + lookups; standard linear-time prover ≈4T, optimized
  to ~2T via [DT24, Gru24]; further "small memory" optimization: when
  $K\cdot2^m\ll T$, binding costs $O(K\cdot2^m)$ instead of $T/2^m$.
- **General $d$**: $d$ arrays for $\tilde{ra}_1..\tilde{ra}_d$; $dT$ binding (falls to
  $o(T)$ if $K^{1/d}=o(T)$); $d^2T$ message computation.

**Booleanity + one-hot checking (§6.3)**: $(5d+2)T+O(K^{1/d}\log K)$ unoptimized →
**$3dT+O(K^{1/d}\log K)$** with: (i) $r'=r_{cycle}$ sharing ($D=E^*$, saves $T$);
(ii) Dao–Thaler $D$-binding reduction to $O(\sqrt T)$; (iii) $K2^m$-distinct-values
binding trick for $H_1..H_d$ (saves $2dT$). Arrays: $B$ (size $K^{1/d}$ eq-table),
$D$ (size $T$), $F$ (size $2^m$, stores $\widetilde{eq}((k_1..k_m),(r_1..r_m))$),
$G_i[k]=\sum_{j:\tilde{ra}_i(k,j)=1}D[j]$ (additions only); round message Eq. 56:
$s_m(c)=\sum_kG_i[k]B[c,k']\big(F[k_1..k_{m-1},c]^2-F[k_1..k_{m-1},c]\big)$,
cost $2^m+2K^{1/d}$ per round. $\tilde{raf}$-evaluation (d=1): $O(\sqrt{KT})=o(T)$ via the
$D''$/$D'''$ split of the eq-table (last $\ell$ coordinates separated;
$T/2^\ell+2^{\ell+1}$ mults, minimized at $\ell=(\log T-\log K)/2$).

**Combined (§6.4)**: for $K=o(T)$, $K^{1/d}\log K=o(T)$: core $(d^2+2)T$ + one-hot
checking $3dT$ ⇒ total $\le(d^2+3d+2)T$ field multiplications.

### 5.7 Fast Shout prover — gigantic structured memories (§7, sparse-dense sum-check)

**Sparse-dense sum-check [STW24 App. G]** (§7.1): for $\sum_i\hat a(i)\hat b(i)$ where
binding variable 1 multiplies each $\hat a$-term in group $H(0)$ by one factor $m_{0,r_1}$
(and $H(1)$ by $m_{1,r_1}$) and each $\hat b$-term by $v_{0,r_1}$/$v_{1,r_1}$: aggregate
terms per group first, then multiply once per group. Canonical cases:
$\hat b=\widetilde{eq}(r',x)$ with $v_{0,r_1}=\widetilde{eq}(r'_1,r_1)/(1-r'_1)$,
$v_{1,r_1}=\widetilde{eq}(r'_1,r_1)/r'_1$ (multiplicative update); or
$\hat b(x)=\sum_i2^{i-1}x_i$ (range-check table) with *additive* updates
$2^{i-1}(r_i-c)$. Runs in $O(CT)$ for $N\le T^C$.

**Booleanity for $K^{1/d}\gg T$ (§7.2)**: with $\hat a=\tilde{ra}_i^2$ (NOT multilinear,
but "ultra-structured": exactly one nonzero $k$ per $j$; binding multiplies by
$(1-r_1)^2$ etc.). Chunk $k$ into $c$ chunks of $\log(K)/(cd)$ bits with
$cK^{1/(cd)}=o(T)$. Build $c+1$ eq-tables of size $K^{1/(cd)}$ ($cK^{1/(cd)}+T$ mults);
partial-sum tree over $K^{1/(cd)}=o(T)$ leaves ($d(c+1)T$ mults to build);
round-$i$ messages = linear combinations of level-$i$ tree nodes with coefficients
$m_kv_k$ where $m_k=\widetilde{eq}(r_1..r_{i-1},2,k)^2$,
$v_k=\widetilde{eq}(k,(r_1..r_i))^{-1}\widetilde{eq}(r_1..r_i,r_1..r_i)$
(batch-inversion: $O(2^i)$ mults + 1 inversion per round);
**tree recomputation** at the end of each chunk of rounds ($3dT+O(dK^{1/(cd)})$ per
rebuild, $c-1$ rebuilds); final $\log T$ rounds: $5dT$.
Total Booleanity: $O(dcK^{1/(dc)})+(4dc+3d+1)T$ (e.g. $c=d=2$: $O(K^{1/4})+23T$).

**Read-checking for structured $K\gg T$ (§7.3)**: sparse-dense applies to the first
$\log K$ rounds because $\prod_i\tilde{ra}_i(k_i,j)$ is multilinear in the $k$ variables
(only $j$-degree exceeds 1); cost $2CT+o(T)$ for the first $\log K$ rounds; then "switch
over" to the standard linear-time prover for the final $\log T$ rounds ($d^2T$).

**$\tilde{raf}$-evaluation & Hamming-weight-one for $K\gg T$ (§7.4)**: batch with
read-checking by $\widetilde{Val}\to\widetilde{Val}+z\cdot\widetilde{int}$
($CT+o(T)$ extra); Hamming-weight-one: $O(dK^{1/d})$ or sparse-dense with
$\hat a=\tilde{ra}_i(\cdot,r''_{cycle})$, $\hat b=1$ ($cT+O(CK^{1/C})$, $C=cd$).

**Total (§7.5)**: $\le(7C+d^2+3d+c+2)T$ field multiplications for $K^{1/C}=o(T)$
(with $4C+3d$ of those from Booleanity). Example $C=4,d=2$: $40T$ (Fig. 3 says $42T$
inclusive of one-hot checks; $65T$ at $d=4$, $112T$ at $d=8$).

**Appendix C variant — linear in $d$**: replace Eq. 30 by
$\tilde{rv}(r_{cycle})=\sum_{k,j_1..j_d}\widetilde{eq}(r_{cycle},j_1,...,j_d)\prod_i\tilde{ra}_i(k_i,j_i)\widetilde{Val}(k)$ (Eq. 95)
with $\widetilde{eq}(j_0,j_1,\dots,j_d)$ the MLE of "$d{+}1$-way equality"
(Eq. 94: $\prod_{i=1}^{\log T}\prod_{k=0}^d((1-j_{k,i})+...)$... specifically
$\prod_{i}[(1-j_{0,i})\prod_{k=1}^d(1-j_{k,i})+j_{0,i}\prod_{k=1}^dj_{k,i}]$).
$\log K+d\log T$ rounds, each degree-2; proof size still
$O(\log K+d\log T)$; soundness $O((\log K+d\log T)/|\mathbb{F}|)$ (Thm 7). Prover: stage
$s$ processes variable $s$ of each $j_1..j_d$ in sequence; round messages collapse because
$\widetilde{eq}$ forces $j_1=\dots=j_d$; $d=2$: $10.5T$ mults (≈$5.5T$ with the
$K^{1/d}=o(\sqrt T)$ lookup-table trick); general $d$: $(8d-7.5)T$ with Gruen in the last
round of each stage; $8d-12.5$ for $K=2^{64},d=16$ with product lookup tables.
Preferable for $d\ge8$ (i.e., hashing-based commitments over gigantic tables).

### 5.8 Fast Twist provers (§8)

**$\widetilde{Val}$-evaluation sum-check (§8.1)**: LT table via the
$\mathrm{LT}_i$ decomposition (Eq. 86–87, App. B.1):
$\widetilde{LT}(x,y)=\sum_{i=2}^{\log T}\mathrm{LT}_i(x,y)$,
$\mathrm{LT}_i=(1-x_i)y_i\widetilde{eq}(x_{>i},y_{>i})$; tables
$E_i[j']=\widetilde{eq}(j'_{>i},r_{>i})$ ($T/2$ mults total) and
$D_i[x]=\sum_{\ell=i}^{\log T}\mathrm{LT}_\ell(x,r_{\ge\ell})$ ($T$ mults total;
recurrence: $x_i=1\Rightarrow D_i=D_{i+1}$; $x_i=0\Rightarrow D_i=D_{i+1}+r_iE_i$).
$3T/2$ for the full LT table; $2K$ for the $\widetilde{Inc}(r_{address},j')$ table;
standard prover $4T$; **total $2K+5.5T$, optimized to $2K+4T$** (App. B.2: maintain
$Q_{i,c}=\sum_{j\le i}Q_{j,i}(c)$ scalars and compute
$s_i(c)=(\sum_{j=1}^{i-1}Q_{j,i}(c))A'(c)+C(c)$, Eq. 93).

**Read/write-checking — two algorithms (§8.2):**

1. **Local algorithm ($d=1$)** — binds the $\log T$ **cycle** variables first
   (low-order bit $j_1$ upward). Data: array $I$ of non-zero
   $\widetilde{Inc}(k,r_1..r_i,j'')$ evaluations (≤$2^i$ non-zeros per row by Fact 8.1);
   per-row Val reconstruction via the chunk identity (Eq. 72):
   $\widetilde{Val}(k,r_1..r_i,j)=\widetilde{Val}(k,j^*)+\sum_{\hat j}\widetilde{Inc}(k,(\hat j,j))\widetilde{LT}(\hat j,r_1..r_i)$
   with $j^*=(0^i,j)$; $\widetilde{LT}(\hat j,b,r_1..r_i)=\widetilde{LT}(\hat j,r_1..r_{i-1})+(1-b)r_i$
   (one multiplication per row). Arrays $E$/$E'$ of size $\sqrt{KT}$ (Dao–Thaler style
   left/right split, Eqs. 75–76) with aggregated values $agg_{j''}$.
   **Worst case**: first $\log K$ rounds $4\log(K)T+o(T)$ ($2T\log K$ write-induced +
   $3\log(K)T$... precisely: $2T\log K$ write-induced; read-induced
   $3\log(K)T+o(T)$... the paper totals $(4\log(K)+6)T$ for the read-checking and
   $(3\log(K)+5)T$ extra for the write-checking); final $\log T$ rounds ~$5T$–$6T$.
   **Locality**: a $2^i$-local write contributes $i$ (vs $\log K$) write-induced
   multiplications; a $2^i$-local read contributes $3i$ (vs $3\log K$) read-induced ones
   (duplicate reads/writes within a $2^i$-cycle chunk coalesce: cost
   $2(2^i-D)$ with $D$ duplicates).
2. **Alternative algorithm (general $d$)** — binds the $\log K$ **address** variables
   first. Arrays $B$ (eq over $j$, size $T$), $C$ (conceptually $KT$ but rows differ in ≤1
   entry: generate row-on-row via Eq. 79–80:
   $C[k',(j)]-C[k',j]=\mathrm{Inc}(k,j)\widetilde{eq}(k'',r_1..r_i)$), $A_1..A_d$ (one
   non-zero per row; store index + shared $2^i$-entry lookup table). Costs:
   read-checking $(3\log(K)+d^2+2d+1)T$; write-checking extra
   $(2\log(K)+d^2+2d+2)T$; **total $(5\log(K)+2d^2+4d+4)T$** ($d=1$:
   $(5\log(K)+10)T$, vs local algorithm's $(5\log(K)+19)T$ worst case). Amenable to a
   $(T/K)$-fold parallel speedup with constant-factor work increase.

**Cost summary (§8.3)**: local $d=1$ core Twist ≤$(7\log(K)+15)T$ (i.e.
$(4\log K+6)T$ read + $(3\log K+5)T$ write + $4T$ Val-eval; $K=32$: $50T$;
$K=2^{20}$: $155T$); one-hot checking adds $6dT+O(dK^{1/d})$.

### 5.9 Figure 10 — SpeedySpartan PIOP (degree-2 Plonkish)

**Preprocessing** (honest party): from sparse $A,B,C\in\mathbb{F}^{m\times n}$ (unit-vector
rows) and $q_l,q_r,q_o,q_m,q_c\in\mathbb{F}^m$ output query-access to
$\tilde q_l,\tilde q_r,\tilde q_o,\tilde q_m,\tilde q_c$ and
$\mathrm{addr}^A,\mathrm{addr}^B,\mathrm{addr}^C$ — the $d$-dimensional one-hot encodings of
the addresses in $M$, sent as $d$ polynomials $\mathrm{addr}_{M,1..d}$ each of size
$m\cdot n^{1/d}$. (No one-hot checking needed — preprocessed by an honest party.)

**Online**:
1. P → V: commitment to purported witness polynomial $\tilde w$ (the ONLY online commitment).
2. V → P: random $\tau\in\mathbb{F}^s$ ($s=\log m$).
3. V ↔ P: **Spartan sum-check**: confirm
   $0=\sum_{x\in\{0,1\}^s}\widetilde{eq}(\tau,x)f(x)$ with $f$ from Eq. 82/83; ends with
   claim $c=\widetilde{eq}(\tau,r)\cdot f(r)$.
4. P → V: $v_A\leftarrow\tilde z_A(r)$, $v_B\leftarrow\tilde z_B(r)$, $v_C\leftarrow\tilde z_C(r)$
   (where $z=(w,x)$, $z_A=Az$ etc.).
5. V: $e=\widetilde{eq}(\tau,r)$; query preprocessed $\tilde q_*$ at $r$; **reject unless**
   $c=e\cdot(v_lv_A+v_rv_B+v_ov_C+v_mv_Av_B+v_c)$.
6. V ↔ P: **core Shout read-checking** (Eq. 81) for each $M\in\{A,B,C\}$:
   $v_M=\sum_{k,j}\widetilde{eq}(r,j)\prod_i\mathrm{addr}_{M,i}(k_i,j)\tilde z(k)$
   — validates the three virtual evaluations via lookups into the "table" $\tilde z$.
   Ends with queries to $\tilde z$ (= one query to $\tilde w$ plus public $x$ handling) and
   to the preprocessed $\mathrm{addr}$ polynomials.

Batching (§4.2.1 + [GLH+24 §5]) collapses the many evaluation proofs into one.
A folding scheme for Plonkish follows from "early stopping" SpeedySpartan (à la
HyperNova), with logarithmic verifier circuit.

**Costs ($m=n=2^{24}$ running example, Hyrax/Dory)**: proving key $m\cdot n^{1/d}$
group elements ($d=2$: $2^{18}$); preprocessing: $dm$ + $5m$ group ops; online: commit
only witness (small values); Spartan sum-check $9m$ mults; Shout read-checking twice:
$(d^2+1)m+4n$ each; **total $25m$ field multiplications at $d=2$**; proof
$O(d\log(n+m))$ field elements + one eval proof; verifier $O(d\log(n+m))$ + eval-proof
check. Dory eval proofs ≤30% of prover time iff $m,n\ge2^{26}$ and $d\ge3$.

### 5.10 Spartan++ / Spark++ (§9.3)

**Spark++ commitment**: commit to $T$-sparse 0/1-valued $p$ via $d$ one-hot polynomials
encoding $S=\{x:p(x)\ne0\}$ (honest-party commitments; no one-hot checking needed).
**Evaluation** at $r$: $p(r)=\sum_{k,j}\prod_i\tilde{ra}_i(k_i,j)\widetilde{eq}(k,r)$
— Shout read-checking into the MLE-structured table $\widetilde{eq}(k,r)$; either via a
sum-check for $\sum_j\tilde{rv}(j)$ or directly $T\cdot\tilde{rv}(2^{-1},..,2^{-1})$.
Prover $O(CT)$ for $K=2^\ell\le T^C$.

**Spartan++** (= SuperSpartan with Spark++ instead of Spark; R1CS case):
1. Preprocessing: honest party commits to $\tilde A,\tilde B$ via Spark++.
2. Online: P commits only to multiplication-gate outputs $w$ ($\tilde w$).
3. Zero-check (Eq. 85): $\sum_x\widetilde{eq}(r,x)(\tilde a(x)\tilde b(x)-\tilde w(x))=0$
   ($5M$ mults); ends needing $\tilde a(r'),\tilde b(r'),\tilde w(r')$.
4. Two parallel sum-checks (batchable):
   $\tilde a(r')=\sum_j\tilde A(r',j)\tilde z(j)$, $\tilde b(r')=\sum_j\tilde B(r',j)\tilde z(j)$
   ($M+5n$ mults); end needing $\tilde A(r',r'')$, $\tilde B(r',r'')$ (via Spark++) and
   $\tilde z(r'')$ (commitment).
5. Shout on $2T$ lookups into the size-$M\cdot n$ table
   $\mathrm{Val}(j,j')=\tilde z$-lookups: $2(d^2+4)T$ mults.

Total: $6M+5n+2(d^2+5)T\approx11M+(2d^2+10)T$ field mults; $d=4$: ~42 per addition gate,
53 per multiplication gate; **~6× faster than Spartan** (Spartan/Spark/Lasso: 2 random
committed values per non-zero ⇒ ~132 field ops/non-zero + 24 Lasso field ops ⇒
~$312T$). Hyrax eval proofs: $T$ mults; Dory: multi-pairings/scalars of size
$\le(Mn)^{1/d}\cdot T$ (concretely OK for $d\ge4$).

### 5.11 Integration into zkVMs (§2.2, App. E context)

- $raf/waf$ virtual: the verifier evaluates $\tilde{raf},\tilde{waf}$ at random points by
  sum-check reductions expressed through $\tilde{ra},\tilde{wa}$ (the $\tilde{raf}$-evaluation
  sum-check); $\tilde{rv}$ virtual likewise.
- **Naive folding with Nova** (§2.9.3): shard execution; Jolt (+Twist) proves each shard
  including commitments to end-of-shard register/memory state (O(M) per shard — Nebula
  avoids this; open for Twist); a Nova step verifies each Jolt proof and checks
  state-consistency via commitment comparison. Optimization: defer polynomial evaluation
  proofs by folding $R_{polyeval}$ instances (HyperNova-style multi-folding:
  rerandomize incoming instances to a shared evaluation point via sum-check, then random
  linear combination); prover pays $O(m)=O(T\cdot K^{1/d})$ per shard in the folding step.
- Alternatives: distill reductions and build folding-centric zkVMs (NeutronNova — Shout
  can be directly turned into a folding scheme this way; Nebula).

## 6. Soundness & Security

| Theorem | Statement |
|---|---|
| **Thm 1** | Core Shout $d{=}1$ (Fig. 5): perfect completeness; soundness $(2\log K+\log T)/|\mathbb{F}|$ (given one-hot $ra$). Proof: both sides of Eq. 22 multilinear in $j$; agree on cube ⟺ polynomial identity; Schwartz–Zippel at $r_{cycle}$; sum-check soundness. |
| **Thm 2** | One-hot checking $d{=}1$ (Fig. 6): completeness; soundness $(6\log K+4\log T)/|\mathbb{F}|$ (union of Booleanity $3(\log K+\log T)$, Hamming-weight $\log T+\log K$, $\tilde{raf}$-eval $2\log K$ terms). |
| **Thm 3** | Figs. 7/8: completeness; soundness $((d{+}2)\log T+2\log K)/|\mathbb{F}|$ (Fig. 7) and $(4d\log T+6\log K)/|\mathbb{F}|$ (Fig. 8). |
| **Thm 4** | Core Twist (Fig. 9): completeness; soundness $((2d{+}3)\log T+3\log K)/|\mathbb{F}|$. |
| **Thm 5** | Core Shout $d{=}1$ prover: $3K+T$ multiplications. |
| **Thm 6** | Core Shout $d>1$ prover: $(d^2+d+1)T+5K+o(T)$; $(d^2+1)T+5K+o(T)$ if $K^{1/d}=o(T)$. |
| **Thm 7** | Appendix-C Shout variant (Eq. 95): completeness; soundness $O((\log K+d\log T)/|\mathbb{F}|)$. |

**Twist soundness logic (Thm 4 proof — the important one):** define the *correct*
polynomials $\widetilde{cInc},\widetilde{crv},\widetilde{cVal}$ implied by the committed
$\tilde{wa},\tilde{wv}$. Three-step structure: (i) read-checking grants access to
$\widetilde{crv}$ assuming $\widetilde{Val}=\widetilde{cVal}$; (ii) write-checking forces
$\widetilde{Inc}=\widetilde{cInc}$ assuming $\widetilde{Val}=\widetilde{cVal}$;
(iii) Val-evaluation forces $\widetilde{Val}=\widetilde{cVal}$ assuming
$\widetilde{Inc}=\widetilde{cInc}$. Steps (ii)/(iii) look circular but are not: for the
Val-evaluation to fail at some $(k,j)$ one only needs $\widetilde{Inc}(k,j')$ wrong for
$j'<j$. Take the *smallest* $j^*$ with $\widetilde{Inc}(k^*,j^*)\ne\widetilde{cInc}(k^*,j^*)$;
then $\widetilde{Val}(k^*,j^*)=\widetilde{cVal}(k^*,j^*)$ (all earlier increments correct),
so the write-checking residual $h(k^*,j^*)$ (Eq. 40) is nonzero; Schwartz–Zippel over
$(r,r')$ + sum-check soundness ⇒ rejection with error
$((d+1)\log T+2\log K)/|\mathbb{F}|$; then Val-evaluation ($+2\log T/|\mathbb{F}|$) and
read-checking ($+(d\log T+\log K)/|\mathbb{F}|$) close the argument. Completeness from
Eqs. 37–39 (Eq. 37 holds only pointwise on the cube — not as formal polynomials — which
is fine because the sum-check only evaluates on the cube).
**Extractor-free**: knowledge soundness is inherited from the sum-check protocol's
special-soundness and the PCS's binding; no grand-product ⇒ no permutation-extraction
argument at all.

**What replaces grand-product / grand-sum arguments**: the read/write correctness is
expressed as (very sparse, rank-1 or rank-$d$) *constraint systems* over the one-hot
variables, checked by the zero-check PIOP; the "most recently written" ordering is handled
by the $\widetilde{LT}$-weighted increment sum instead of timestamp monotonicity + range
checks; permutation/multiset-equality fingerprinting (Lipton's trick) disappears entirely.

**Batching soundness (§4.2.1)**: random linear combination of $t$ parallel instances adds
$t/|\mathbb{F}|$.

**Improved soundness error (§2.7)**: one-hot addressing error $\log(TK)/|\mathbb{F}|$ vs
offline memory checking's $\ge(T+K)/|\mathbb{F}|$ (degree-$(T+K)$ univariate in the
fingerprint challenge). On 64-bit-base-field/128-bit-subfield curves
($r$ drawn from $\mathbb{F}_{2^{128}}$-subfield): $K=2^{30}$ leaves 98 bits; $T=2^{40}$
leaves 88 bits; one-hot addressing keeps >120 bits.

## 7. Parameters & Concrete Efficiency

### 7.1 Headline cost tables (elliptic-curve commitments)

**Figure 1 — read/write memory ($R=T$ reads, $W=T$ writes):**

| Checker | Non-zero committed values | Field multiplications | Proof size |
|---|---|---|---|
| Spice | $5R+6W+2K\approx11T$ | $80T+80K\approx80T$ | $O(\log^2T)$ |
| Twist ($d{=}1$) | $R+3W=4T$ | $(5\log(K)+16)T+O(K\log K)$ | $O(d\log T)$ |
| Twist ($d{=}2$) | $2R+4W=6T$ | $(5\log(K)+32)T+O(K)$ | $O(d\log T)$ |

(d=1 locality: $2^i$-local accesses cost $7i$ instead of $5\log K$; costs include
Booleanity-checking.)

**Figure 2 — read-only memory (small/unstructured tables):**

| Checker | Non-zero committed values | Field multiplications | Proof size |
|---|---|---|---|
| Lasso | $3T+\min\{K,T\}$ | $12T+12K$ | $O(\log^2T)$ |
| LogUpGKR | $2T+\min\{K,T\}$ | $21T+21K$ | $O(\log^2T)$ |
| Shout ($d{=}1$) | $T$ | $4T+O(K\log K)$ | $O(d\log T)$ |
| Shout ($d{=}2$) | $2T$ | $11T+O(K)$ | $O(d\log T)$ |

**Figure 3 — structured read-only memory, $K$ with $K^{1/C}=o(T)$, $C=4$:**

| Checker | Non-zero committed values | Field multiplications | Proof size |
|---|---|---|---|
| Lasso (Jolt-style) | $\ge16T$ | $\ge144T$ | $O(\log^2T)$ |
| Shout ($d{=}2$) | $2T$ | $42T$ | $O(d\log T)$ |
| Shout ($d{=}4$) | $4T$ | $65T$ | $O(d\log T)$ |
| Shout ($d{=}8$) | $8T$ | $112T$ | $O(d\log T)$ |

(Lasso row = optimistic estimate of Jolt's decomposed-subtable configuration: 4–10
subtable lookups of size $2^{16}$, 2 small committed values per subtable address +
range checks.)

**Figure 4 — committed bits (hashing-based / binary-field PCS):**

| Checker | Memory | Bits of committed data | Field mults | Proof size |
|---|---|---|---|---|
| Lasso | $K=2^{64}$ (structured) | ≥928$T$ | ≥194$T$ | $O(\log^2T)$ |
| Shout ($d{=}16$) | $K=2^{64}$ (structured) | 256$T$ | 131$T$ | $O(d\log T)$ |
| Spice | $K=32$ | 421$T$ | 95$T$ | $O(\log^2T)$ |
| Twist ($d{=}1$) | $K=32$ | 128$T$ | 35$T$ | $O(d\log T)$ |

### 7.2 Choosing $d$ (§2.8)

| Application | Setting | HyperKZG | Dory | Hashing (GF(2^128)) |
|---|---|---|---|---|
| 1 | $K=32$, $T=2^{20}$ (RISC-V registers) | $d=1$: SRS $32\cdot2^{21}=2^{26}$ (GBs); or $d=2$: $2^{11}$ | – | $d=1$ (32 bits/address; 4 addresses pack into one GF($2^{128}$)) |
| 2 | $K=2^{20}$, $T=2^{20}$ (L2/L3 cache) | $d=4$: SRS $2^{25}$, 4-el. commitments | $d=1$: key $2\cdot2^{21}$ | $d=4$ ($4\cdot2^5=128$ bits → one GF($2^{128}$)) |
| 3 | $K=2^{30}$, $T=2^{32}$ (4 GB RAM) | infeasible | $d=2$: key $\approx2^{26}$ | – |
| 4 | $K=2^{64}$, $T=2^{20}$ (Jolt instruction tables) | $d=8$: 32-el. address commitments, SRS $2^{26}$ | $d=4$: key $2^{19}$ (even $d=2$: $2^{27}$) | $d=16$: $16\cdot2^4=256$ bits → two GF($2^{128}$) |

Rules of thumb: curve PCS ⇒ $d\in[1,4]$; hashing PCS ⇒ $d\in[1,16]$; key sizes:
HyperKZG $\Theta(K^{1/d}\cdot T)$, Dory $\Theta((K^{1/d}\cdot T)^{1/2})$; key reducible by
factor $k$ at cost of $k$-element commitments; $d=\log K$ = "Spark-naive" regime
(minimal committed bits but ≥$O(T\log K)$ field work and
$O(\log^2K+\log T\log K)$ proofs — not recommended).

### 7.3 SpeedySpartan vs Plonk / BabySpartan (Figure 11; fan-in-2 arithmetic circuits, $m=n$)

| | Plonk (small proof) | Plonk (fast prover) | BabySpartan | SpeedySpartan ($d{=}2$) | SpeedySpartan ($d{=}3$) |
|---|---|---|---|---|---|
| Committed field elements (excl. preprocessing) | 8$m$ random | 6$m$ random + 3$m$ small | 3$m$ + $n$ small | $n$ small | $n$ small |
| Field multiplications | 54$m\log m$ + 546$m$ | 54$m\log m$ + 414$m$ | 51$m$+30$n$ | 19$m$+14$n$ | 29$m$+14$n$ |
| Total (at $m=n=2^{24}$) | 1842·$2^{20}$ | 1710·$2^{24}$ | 81·$2^{24}$ | **33·$2^{24}$** | 43·$2^{24}$ |

SpeedySpartan $d=2$: ~50× fewer field multiplications and ~75× lower commitment cost
than Plonk; 4× lower commitment cost and 2× less field work than BabySpartan.
Translation rules: small committed value = 1 group op; random value = 11 group ops;
group op = 6 field ops.

### 7.4 Other concrete numbers

- Dory: multi-pairing not a bottleneck for $T\ge2^{22}$ (cost
  $4000\sqrt T/pip\ll$ MSMs); proof $6\log N$ target-group elements (~a dozen KB);
  target-group ops ~6× slower than $G_1$.
- Spartan++ ($d=4$): ~42 field mults per addition gate, 53 per multiplication gate; ~6×
  faster than Spartan; commitment costs grow only with multiplication-gate count.
- Proof size / verifier (both families): $O(d(\log T+\log K))$ field elements; with a
  log-size-eval-proof PCS the SNARK proof is $O(d(\log T+\log K))$ field+group elements;
  batching ⇒ single eval-proof verification = constant MSMs of size
  $O(\log T+\log K)$ + constant pairings.
- Context (§2.1): Spice ≈ 20% of Jolt prover time (mostly registers); Lasso ≈ 25%;
  together almost half of Jolt prover time. Shout vs Lasso-in-Jolt: up to 8× commitment
  cost and ~3× field-multiplication improvements; Twist vs Spice (32 registers): ~3×
  commitment and 2× field-multiplication improvements.

## 8. Implementation Notes

### 8.1 Components to build (dependency order)

1. **MLE/eq/LT layer**: eq-table builder (Lemma 1 doubling trick);
   $\widetilde{LT}$ evaluation in $O(\log T)$ (App. B.1 recurrence
   $D_i[x]$/$E_i[x]$ tables); int-MLE $\widetilde{int}$ for the $\tilde{raf}$-evaluation
   sum-check; $d$-way-equality MLE $\widetilde{eq}(j_0,...,j_d)$ (Eq. 94) for the
   Appendix-C variant.
2. **Sum-check engine**: standard linear-time prover with arrays $A_1..A_\ell,B$; round
   messages at points $c\in\{0,2\}$ (omit $c=1$: $s_i(1)=s_{i-1}(r_{i-1})-s_i(0)$; omit
   $c=d+1$ via Gruen's $s'_i$); Dao–Thaler $B$-array elimination; unequal-arity batching
   with $z$-powers; per-instance "bind order" control (address-first vs cycle-first is
   the crucial Twist switch).
3. **One-hot data structures**: for each committed $\tilde{ra}_i$: per-cycle address
   $k_i$, shared per-round lookup table of $\widetilde{eq}$ values over bound prefixes
   (Eq. 46); aggregation arrays $C$/$G_i$ (sums of eq-entries over cycles hitting each
   address — additions only).
4. **Shout prover** (small memories): A/C array algorithm for the first $\log K$ rounds;
   E/$E^*$ arrays for the final $\log T$ rounds; $K2^m$-distinct-values binding
   optimization; Booleanity pipeline ($B,D,F,G_i,H_i$); $\tilde{raf}$-evaluation with the
   $D''$/$D'''$ split ($O(\sqrt{KT})$).
5. **Shout prover** (structured tables): sparse-dense machinery — eq-tables per chunk,
   partial-sum trees, round-message coefficients $c_k=m_kv_k$ with batch inversion, tree
   recomputation every $\log(K)/(cd)$ rounds; int-table batching via
   $\widetilde{Val}+z\widetilde{int}$.
6. **Twist prover**: increments table $I$; per-row Val reconstruction (Eq. 72 with the
   $\widetilde{LT}(\hat j,b,...)=\widetilde{LT}(\hat j,...)+(1-b)r_i$ trick);
   $\sqrt{KT}$-sized $E$/$E'$ arrays with `agg` accumulators (local algorithm); or the
   row-delta $C$-array algorithm (Eq. 79–80) for the alternative algorithm; write-checking
   by the substitution $\widetilde{Val}\to\widetilde{Val}-\tilde{wv}$; one shared
   Val-evaluation sum-check.
7. **Commitments**: sparse MSM over non-zero entries only (0s free); dual key
   $(g_i,h_i=g_i^{-1})$ for negative increments; small-value bucketing (Pippenger);
   batching of evaluation proofs.
8. **SpeedySpartan/Spartan++**: preprocessing (one-hot address polynomials for
   $A,B,C$); Spartan sum-check with the $q_m\in\{0,1\}$ binding optimization; Shout
   read-checking into $\tilde z$; Spark++ commitment/evaluation.

### 8.2 Complexity summary

| Protocol | Prover field mults | Committed non-zeros | Proof size | Verifier |
|---|---|---|---|---|
| Shout $d{=}1$ (small $K$) | $4T+O(K\log K)$ | $T$ | $O(\log T+\log K)$ | $O(\log T+\log K)$ + eval queries |
| Shout general $d$ (small $K$) | $(d^2+3d+2)T+O(K^{1/d}\log K)$ | $dT$ | $O(d(\log T+\log K))$ | ditto |
| Shout structured ($K^{1/C}=o(T)$) | $(7C+d^2+3d+c+2)T$ | $dT$ | $O(d(\log T+\log K))$ | ditto |
| Shout App. C ($d\ge8$) | $(8d-7.5)T$ (or $8d-12.5$) | $dT$ | $O(\log K+d\log T)$ | ditto |
| Twist $d{=}1$ local (worst) | $(7\log K+15)T$ | $4T$ (+1 small per write = increments) | $O(\log T+\log K)$ | ditto |
| Twist general $d$ (alternative alg.) | $(5\log K+2d^2+4d+4)T+6dT$ | $(2d+2)T$-ish (read+write addresses + increments + $wv$) | $O(d(\log T+\log K))$ | ditto |
| SpeedySpartan $d{=}2$ ($m{=}n$) | $25m$ (33·$2^{24}$ at $2^{24}$) | $n$ small | $O(d\log(n+m))$ + 1 eval proof | $O(d\log(n+m))$ |
| Spartan++ $d{=}4$ | $11M+(2d^2+10)T$ | $M$ (mult-gate outputs) | $O(d\log)$ + eval proofs | $O(d\log)$ |

### 8.3 Memory layout / data structures

- Arrays halve per sum-check round (bind in place); keep $E^*$ ($T$), per-$i$ address
  tables ($K^{1/d}$), and — for the Appendix-C trick — product lookup tables of sizes
  $K^{2/d},K^{3/d},\dots$ (a few dozen MBs at $K=2^{64},d=16$).
- Local Twist prover iterates rows of Val in lexicographic cycle order; maintains
  $\le2^i$-sparse increment rows; peak working set $O(T)$, not $O(KT)$.
- Commitment key (HyperKZG): $d$ SRS segments of $K^{1/d}\cdot T$; Dory:
  $\sqrt{K^{1/d}T}$; reducible by $k$× at $k$× commitment size.

### 8.4 Pitfalls & edge cases

1. **Bind order matters**: Shout binds address variables first (aggregation over cycles);
   the Twist local algorithm binds *time* variables first (coalescing locality). The
   alternative Twist algorithm binds address first to generalize to $d>1$ — using the
   local algorithm with $d>1$ degrades concrete costs.
2. **Eq. 37 is only pointwise on the cube** (not a polynomial identity) — sum-check
   applications must be formulated via $\widetilde{eq}$-anchored sums (Eqs. 33/34), never
   by "cancelling" the $\prod_i\tilde{wa}_i$ factors symbolically.
3. **Circularity in Twist soundness** is resolved by the minimal-$j^*$ argument — an
   implementation-independent proof structure, but any protocol variant that lets the
   prover choose $r'$ or the Val-evaluation point *after* seeing other challenges must
   preserve the ordering: commit to $\tilde{ra},\tilde{wa},\tilde{wv},\tilde{Inc}$ BEFORE
   all sum-check randomness.
4. **Binary fields**: no $2^{-1}$ — the Hamming-weight-one check via evaluation at
   $(2^{-1},\dots,2^{-1})$ must be replaced by the sum-check version (which is anyway
   better for batching). Small-characteristic also raises prior-work costs (timestamps
   [DP23 §4.4]).
5. **Booleanity omission** is only valid when the PCS itself enforces Booleanity
   (Binius-style); otherwise the $3dT$ Booleanity cost must be counted.
6. **$d=\log K$ is a trap**: minimal committed bits but superlinear field work and
   $O(\log^2K)$-ish proofs; keep $d$ minimal subject to key/commitment-time constraints.
7. **$K^{1/d}$ vs $T$ regimes switch algorithms**: small-memory optimizations
   ($K2^m$ binding trick) require $K^{1/d}=o(T)$; structured-table path requires
   $K^{1/C}=o(T)$ AND MLE-structured $\widetilde{Val}$; unstructured $K\gg T$ with $d=1$
   pays $O(K)$ — avoid.
8. **Negative increments** need the inverted commitment key $h_i=g_i^{-1}$ (or negate in
   the exponent).
9. **Read values must not be committed before the evaluation point is known** (footnote
   13) — the virtual-$\tilde{rv}$ pattern is load-bearing for soundness accounting.
10. **Evaluation-proof amortization**: HyperKZG/Zeromorph/Bulletproofs eval proofs cost
    random-MSMs of size = committed length ($m\cdot n^{1/d}$ for preprocessed
    polynomials!) — use Hyrax/Dory, folding, or the homomorphic split, else the whole
    point of one-hot sparsity is lost.
11. **Jolt interaction**: Shout avoids Lasso's subtable decomposition overheads (inputs
    no longer need over-fine chunking + range checks); the Akita backend expects exactly
    the one-hot commitment shape this paper prescribes.
12. **Zero increments are free but must still be committed as 0s** when using hashing
    commitments — the packing strategy (bits per GF($2^{128}$) element) is the whole
    cost model there.

### 8.5 Reuse from the shared core engine (`lzk`)

- Multilinear sumcheck (compressed + equality-factored/Gruen variants, batching with
  $z$-powers, bind-order control) is the single heaviest reused component — every
  protocol step here is a sum-check.
- Tensor/LDE encodings: the one-hot/tensor-product structure
  ($e_z=v_1\otimes\dots\otimes v_d$) is exactly the packing machinery; $\widetilde{eq}$
  tables and Lemma-1 builders are shared with every other paper in the lab.
- Ring-norm sumcheck: the Booleanity check $w^2-w=0$ is the same degree-2 vanishing
  predicate family used by Akita's range check (with the $w(w+1)$ symmetry trick
  inapplicable here since the alphabet is $\{0,1\}$ directly).
- GF(2^k) tower fields: direct use when combining with Binius-style commitments
  (packing 128 one-hot bits per GF($2^{128}$) element).
- Ajtai/SIS commitments and Fiat-Shamir transcripts: not needed by the PIOP itself, but
  the transcript layer (challenge derivation, batching challenges) is shared.
- One-hot commitments under the `lzk` commitment layer: the Akita "one-hot shape"
  (identity source map, pay-per-nonzero) is the natural backend for Twist/Shout
  addresses — the two papers are designed to compose (Jolt).

## 9. Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- ✅ Shout core PIOP (d=1): the lookup sumcheck Σ MLE[W]·MLE[A] = v with
  one-hot selectors; the one-hot encoding check (Booleanity + Hamming
  weight via Σ MLE[A]² = 1); non-one-hot rejection tested.
- ✅ Twist read-checking (batched per-step claims with transcript
  combiners in one degree-2 sumcheck over the address hypercube).
- □ Not implemented: the write-checking + increment PIOP (Inc = wa·(wv−Val)),
  the LT-weighted virtual values, the sparse prover optimizations
  (A/C-array aggregation, K2^m binding, partial-sum trees), SpeedySpartan.

**(replacing the placeholder)**

- DONE: Shout core PIOP (d=1): the lookup sumcheck sum MLE[W] MLE[A] = v with one-hot selectors; the one-hot encoding check (Booleanity + Hamming weight via sum MLE[A]^2 = 1); non-one-hot rejection tested.
- DONE: Twist read-checking (batched per-step claims with transcript combiners in one degree-2 sumcheck over the address hypercube).
- NOT implemented: the write-checking + increment PIOP (Inc = wa(wv - Val)), the LT-weighted virtual values, the sparse prover optimizations (A/C-array aggregation, K2^m binding, partial-sum trees), SpeedySpartan.
