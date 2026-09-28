# Quasar: Sublinear Multi-Cast Commitment Mixing in Recursive Accumulation — Deep Analysis & Implementation Spec

> Source: `papers_txt/quasar.txt` (Zheng, Gao, Chow, Guo, Xiao; ~2.7k extracted lines, read in full).
> All figure/lemma/theorem/table/equation numbers are cross-referenced to the paper.
> This doc is implementation-grade: every protocol figure is transcribed step-by-step with
> exact verification equations, ready to be consumed by the `lzk` core-engine waves.

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Quasar: Sublinear Multi-Cast Commitment Mixing in Recursive Accumulation |
| **Authors** | Tianyu Zheng¹, Shang Gao¹, Sherman S. M. Chow², Yu Guo³, Bin Xiao¹ (¹ PolyU HK, ² CUHK, ³ SECBIT Labs) |
| **Group** | Same PolyU HK group as Serval, HyperWolf, Symphony (ePrint 2025/1905) |
| **Primitive** | Multi-instance **accumulation/folding scheme** with $O(1)$ in-circuit commitment random linear combinations (CRCs) per recursive step, arity $\ell$ |
| **Assumptions** | PCS-agnostic IOR layer; instantiations: (i) curve-based — Mercury PCS over BN256 (DL, not PQ); (ii) code-based — FRI + Poseidon-Merkle over RS codes (hash/PQ); (iii) lattice — compatible with extractable lattice PCS (LatticeFold / Symphony style, refs [11,23]) |
| **Soundness** | Perfect completeness + round-by-round (RBR) knowledge soundness in the ROM (Fiat–Shamir of public-coin IORs) |
| **Headline** | Reduces in-circuit CRCs from $\Theta(\ell)$ to $O(1)$ per step; verifier: $O(\log\ell)$ field/RO work; concrete recursion overhead (R1CS, $\ell=32$): HyperNova $1.62\times2^{15}$ vs Quasar $1.01\times2^{14}$ ($3.21\times$ better); code-based (Plonkish, $\ell=32$): Arc $1.34\times2^{19}$ vs Quasar $1.20\times2^{17}$ ($4.49\times$) |

**Key contributions:**

1. **Multi-cast reduction** (new IOR primitive, Sec. 4): compresses $\ell$ input NARK
   instances into a *single derived instance with a constant number of committed oracle
   polynomials*, by committing to *union polynomials* $\tilde x_\cup(\mathbf Y,\mathbf X)$,
   $\tilde w_\cup(\mathbf Y,\mathbf X)$ over the hypercube $\mathbf Y\in\mathbb F^{\log\ell}$
   and verifying a random *partial evaluation* at $\mathbf Y=\boldsymbol\tau$.
2. **Composition theorem** (Main Theorem 1 / Theorem 2): multi-cast ⊕ standard
   2-to-1 folding (Protostar-style SPS accumulation) ⇒ multi-instance accumulation
   scheme whose recursive verifier does $O(\mu)$ CRC operations (independent of $\ell$)
   and $O(\log\ell)$ explicit field work.
3. **Interleaved SPS multi-cast** (Fig. 6): runs the $\ell$ special-sound protocol
   instances *round-by-round batched through union oracles*, so the Fiat–Shamir RO
   absorbs only succinct digests (not $\Theta(\ell\cdot|m_i|)$ raw messages).
4. **Multi-instance IVC** (App. A): each step absorbs $\ell$ predicate instances +
   1 running accumulator; HyperPlonk constraint system + linear-code PCS ⇒
   linear-time, plausibly-PQ IVC with parallelizable per-step accumulation prover.

**What "sublinear / constant-CRC" means precisely:** the unavoidable linear work of
*reading $\ell$ public inputs* is explicitly excluded from the metric; Quasar only
removes the $\ell$-dependence from *in-circuit commitment combinations* (CRC), moving
it to $O(\log\ell)$ sum-check / RO / PCS-evaluation work.

## 2. Notation Table

| Symbol | Meaning |
|---|---|
| $\lambda$ | security parameter (concrete: 128) |
| $\ell$ | accumulation arity = number of predicate instances absorbed per recursive step |
| CRC | one in-circuit random linear combination of two commitments, $C:=r_1C_1+r_2C_2$ |
| RO / $\mathrm{Hash}$ | random oracle / hash query (in-circuit hash work) |
| $G$ | group operation count (in-circuit EC ops for curve instantiations) |
| $\mathbb F$ | finite prime field $\mathbb F_p$ |
| $\mathbf x, \mathbf w$ | bold vectors; $\mathbf x_k\in\mathbb F^m$ instance, $\mathbf w_k\in\mathbb F^n$ witness ($m,n$ powers of two) |
| $[n]$ | $\{1,\dots,n\}$ |
| $x\leftarrow\$S$ | uniform sampling |
| $\tilde f=\mathrm{mle}[f]$ | multilinear extension of $f\in\mathbb F^n$, $n=2^{\log n}$ |
| $\mathrm{Bits}(i)$ | $\log n$-bit binary decomposition of $i\in\{0,\dots,n-1\}$ |
| $\widetilde{\mathrm{eq}}(\mathbf X,\mathbf b)$ | MLE of the equality predicate: $\prod_{j=1}^{m}(b_jX_j+(1-b_j)(1-X_j))$; also $\widetilde{\mathrm{eq}}_i(\mathbf X):=\widetilde{\mathrm{eq}}(\mathbf X,\mathrm{Bits}(i))$ |
| $\mathbb F^{(<d)}[X_1..X_n]$ | $n$-variate polys with individual degree $<d$ |
| $\mathbf Y\in\mathbb F^{\log\ell}, \mathbf X\in\mathbb F^{\log n}$ | instance-index hypercube variables / coefficient variables |
| $\tilde x_\cup(\mathbf Y,\mathbf X),\tilde w_\cup(\mathbf Y,\mathbf X)$ | **union polynomials** $\mathrm{mle}[\{x^{(k)}\}_{k\in[\ell]}]$, $\mathrm{mle}[\{w^{(k)}\}]$ (Step 1, Fig. 4) |
| $[[\tilde p]]$ | polynomial *oracle* (truth table) for $\tilde p$; compiled to a PCS commitment later |
| $\boldsymbol\tau\in\mathbb F^{\log\ell}$ | accumulation point = sum-check challenge vector (also verifier's first challenge $r_y$ in Fig. 4 — see pitfalls) |
| $\mathbf r^x\in\mathbb F^{\log m}, \mathbf r^w\in\mathbb F^{\log n}$ | random evaluation points for partial-evaluation consistency checks |
| $\bar x(\mathbf Y),\bar w(\mathbf Y)$ | selector-based vector polys $\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\,\mathbf x^{(k)}$ (Fig. 4 Step 4) |
| $H(\mathbf Y)$ | $F(\bar x(\mathbf Y),\bar w(\mathbf Y))$ |
| $G(\mathbf Y)$ | $H(\mathbf Y)\cdot\widetilde{\mathrm{eq}}(\mathbf Y,r_y)$, individual degree $\le d+1$ |
| $e$ | accumulated evaluation value: $e:=G_{\log\ell}(\tau_{\log\ell})\cdot\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)^{-1}=F(\mathbf x,\mathbf w)$ |
| $F:\mathbb F^m\times\mathbb F^n\to\mathbb F$ | polynomial map of total degree $\le d$, homogeneous decomposition $F=\sum_{j=0}^d f_j^F$ |
| $R_F$ | evaluation constraint relation $\{(\mathbf x=(\mathbf x,e),\mathbf w): F(\mathbf x,\mathbf w)=e\}$ |
| $R^\ell$, $R_\ell^F$ | product relation: $\ell$ independent instances sharing the index |
| $R_{\mathrm{eval}}$ | oracle relation $\{(\mathbf x=\{(r_j,v_j)\}_j,\,y=[[{\tilde f}]],\,w=\bot):{\tilde f}(r_j)=v_j\ \forall j\}$ |
| $R_{\mathrm{acc}}$ | accumulator relation (conjunction $R_{\mathrm{eval}}^3\times R_F$ for generic; $R_{\mathrm{eval}}\times R_{\mathrm{eval}}^\mu\times R_{\mathrm{eval}}^\mu\times R_F$ for SPS) |
| IOR / NIR | interactive oracle reduction / non-interactive (FS-compiled) reduction |
| $\mathrm{IOR}_{\mathrm{cast}},\mathrm{IOR}_{\mathrm{cast\text{-}SPS}}$ | multi-cast IORs (Fig. 4 / Fig. 6) |
| $\mathrm{IOR}_{\mathrm{fold}},\mathrm{IOR}_{\mathrm{fold\text{-}SPS}}$ | 2-to-1 folding IORs (Fig. 7) |
| $\mathrm{IOR}_{\mathrm{batch}}$ / $\mathrm{NIR}_{\mathrm{batch}}$ | oracle batching protocol (Def. 2 / Fig. 11) |
| $\Pi_{\mathrm{sps}}$ | $(k_1,\dots,k_\mu)$-special-sound protocol, $\mu$ prover messages $m_1..m_\mu$, challenges $r_i\leftarrow\$\mathbb F$ |
| $\mathbf r, \alpha$ | $\mathbf r:=(r_1,\dots,r_{\mu-1})$; final challenge reused as $\alpha:=r_\mu$ |
| $V_{\mathrm{sps}}$ | SPS verifier polynomial, degree $\le d$; homogeneous decomposition Eq. (7) |
| $\nu$ | number of SPS verifier equations (output dimension of $V_{\mathrm{sps}}$) |
| $\boldsymbol\alpha$ | power vector $(\alpha,\alpha^2,\alpha^4,\dots,\alpha^{2^{\log\nu-1}})$ with constraints $\alpha[0]=r_\mu$, $\alpha[i]=(\alpha[i-1])^2$ |
| $\mathrm{pow}_j(\mathbf X)$ | for $j-1=\sum_{k\in S}2^k$: $\prod_{k\in S}X_k$, so $\mathrm{pow}_j(\boldsymbol\alpha)=\alpha^{j-1}$ |
| $F(\mathbf x,\{m_i\},\mathbf r,\boldsymbol\alpha)$ | scalar compressed check $\sum_{j\in[\nu]}\mathrm{pow}_j(\boldsymbol\alpha)\cdot V_{\mathrm{sps}}(\cdot)[j]=0$ (Eq. 8); degree $D:=d+\log\nu$ |
| $\mathrm{CV}[\Pi_{\mathrm{sps}}]$ | check-compressed SPS (Fig. 5); $(k_1,\dots,k_\mu,\nu{+}1)$-special-sound (Lemma 3) |
| $\tilde m_{\cup,i}(\mathbf Y,\mathbf X)$, $\tilde m_i(\mathbf X)$ | union / partially-evaluated prover-message polynomials (SPS multi-cast) |
| $\mathrm{vec}^{(k)}$ | flattened accumulator instance (Fig. 7 Step 1) |
| $Z\in\{0,1\}$ | folding selector variable; folded objects $\tilde p(Z):=\sum_{k=0}^{1}\widetilde{\mathrm{eq}}_k(Z)\,p^{(k)}$ |
| $\gamma\in\mathbb F^{\log(2\mu+2)}$, $r_z\in\mathbb F$, $\sigma\in\mathbb F$ | fold-phase challenges: claim-aggregation seed, eq-anchor point, sum-check point |
| $\eta_x,\eta_i,\eta_{\cup,i},\eta_F$ | per-component evaluation deltas (Fig. 7 Step 7) |
| $\{(y^\alpha,x^\alpha,v^\alpha)\},\{(y^\beta,x^\beta,v^\beta)\},\{(x^\gamma,v^\gamma)\}$ | output claims of the $2\mu+1$ batching instances |
| NARK / ACC / IVC / PCD | non-interactive argument / accumulation scheme (Def. 17) / incrementally verifiable computation / proof-carrying data |
| $\delta^*$, $\Delta_R$ | IOR proximity radius; distance $\Delta_R(i,\mathbf x,\mathbf y):=\min_{c\in O(i,\mathbf x)}\Delta(\mathbf y,c)$ |
| $\mathrm{State}_\delta$ | RBR knowledge-state function (Def. 20) |
| $\rho$ | code rate ($k/n$); concrete RS $k=2^8$, $\rho=1/16$, $n=2^{12}$ |
| $L(C,\delta)$, $\Lambda(C,f,\delta)$ | list size bound / list-decoding set within distance $\delta$ |
| $\mathrm{ZE}$ | zero-evader (Def. 9) |
| $s,t$ | code-batching repetition parameters (out-of-domain samples $s$; proximity queries $t$) |
| $n$ | witness length / poly size (also codeword length in App. D.1 — context-dependent) |

## 3. Algebraic Setting

### 3.1 Fields, MLEs, sum-check

- Base field $\mathbb F$ (prime $\mathbb F_p$); all lengths $m,n,\ell,\mu,\nu$ padded to powers of two.
- Every vector $\mathbf f\in\mathbb F^n$ is identified with its MLE
  $\tilde f(\mathbf X)=\sum_{i=0}^{n-1}f[i{+}1]\cdot\widetilde{\mathrm{eq}}(\mathbf X,\mathrm{Bits}(i))$,
  $\tilde f\in\mathbb F^{(<2)}[\mathbf X]$, $\mathbf X\in\mathbb F^{\log n}$.
- Sum-check (Sec. 3.2): claim $\sum_{\mathbf x\in\{0,1\}^m}\tilde f(\mathbf x)=\mathrm{sum}$;
  round $i$ prover sends $f_i(X)=\sum_{x_{i+1},..,x_m}\tilde f(r_1..r_{i-1},X,x_{i+1}..x_m)$;
  verifier checks $f_{i-1}(r_{i-1})=f_i(0)+f_i(1)$, samples $r_i\leftarrow\$\mathbb F$;
  final check $f_m(r_m)=\tilde f(r_1..r_m)$. Soundness $m\cdot d/|\mathbb F|$ (Def. 12).
- Schwartz–Zippel (Lemma 1): $\Pr[\tilde f(r)=0]\le n(d-1)/|\mathbb F|$ for
  $\tilde f\in\mathbb F_n^{(<d)}$.

### 3.2 Interactive oracle reductions (IOR, Def. 1)

An IOR from oracle relation $R$ to $R'$ is $(I,P,V)$: indexer $I(i)\to(\iota,\mathcal I,i')$;
$\mu$ rounds where the prover sends message $m_i$ **or oracle string** $\pi_i$ and the
verifier replies with public-coin $r_i$ (from $\mathbb F$ or $\{0,1\}^{\rho_i}$); the
verifier may query $\mathcal I,\mathbf y,\boldsymbol\pi$ and outputs a reduced statement
$(\mathbf x',\mathbf y')$; the prover outputs $\mathbf w'$ with
$(i',\mathbf x',\mathbf y',\mathbf w')\in R'$. Soundness is proximity-based (Def. 19,
radius $\delta^*$); Fiat–Shamir is justified via **RBR knowledge soundness** (Defs. 20–21,
à la Bünz–Chiesa–Fenzi–Wang / linear-time accumulation): a state function
$\mathrm{State}_\delta$ that is 1 on the empty transcript iff close to $R$, is monotone
under prover moves, and characterizes full transcripts.

**Compilation (Theorem 5):** replace every oracle with a PCS commitment
$\Rightarrow\mathrm{IOR}^{PCS}$; apply FS $\Rightarrow\mathrm{NIR}:=\mathrm{FS}[\mathrm{IOR}^{PCS}]$.
If IOR is RBR knowledge-sound and the PCS is extractable, NIR is RBR knowledge-sound
in the ROM; costs add up per message/query complexity.

### 3.3 Special-sound protocols (SPS, Sec. 5.1)

Public-coin $\Pi_{\mathrm{sps}}$ for indexed relation $R$: $\mu$ prover messages
$m_1,\dots,m_\mu\in\mathbb F^n$, challenges $r_1..r_\mu\leftarrow\$\mathbb F$; verifier
polynomial $V_{\mathrm{sps}}(\mathbf x,\{m_i\},\mathbf r)\in\mathbb F^\nu$ of degree $\le d$
with homogeneous decomposition (Eq. 7). $(a_1,\dots,a_k)$-special soundness (Def. 23)
⇒ knowledge soundness with error $\sum_i(a_i-1)/|\mathbb F|$ (Lemma 6).

### 3.4 Linear codes (code-based instantiation, App. D.1 / A)

Linear code = injective $\mathbb F$-linear $C:\mathbb F^k\to\mathbb F^n$, rate $\rho:=k/n$;
zero-evaders (Def. 9) and out-of-domain sampling give the batch soundness machinery
(Theorem 4: $|\mathbb F|\ge 2^{\lambda/s-1}\cdot|L(C,\delta)|^{2/s}$ and
$t\ge\lambda/\log(1/(1-\delta))^{-1}$-style bound; see §6.5 below). Systematic codes
lift $\tilde f_i$-evaluation claims to codeword claims
$\tilde u_i(\mathbf 0,\mathbf x)=v_i$ via $u_i=C(f_i)$ viewed as $1/\rho$ blocks of $k$.

### 3.5 Accumulation scheme syntax (Def. 3 / Def. 17)

$\mathrm{ACC}=(G,I,P,V,D)$ for a NARK: $G(1^\lambda)\to\mathrm{pp}$;
$I(\mathrm{pp},i)\to(\mathrm{apk},\mathrm{avk},\mathrm{adk})$;
$P(\mathrm{apk},\{\mathbf x^{(k)}\}_{k\in[\ell]},\pi,\mathrm{acc}^{(0)})\to(\mathrm{acc},\mathrm{pf})$;
$V(\mathrm{avk},\{\mathbf x^{(k)}\},\pi.\mathbf x,\mathrm{acc}^{(0)}.\mathbf x,\mathrm{acc}.\mathbf x,\mathrm{pf})\to b$;
$D(\mathrm{adk},\mathrm{acc})\to b$. Multi-instance = absorbs $\ell$ NARK statements per
step; **sublinear** = verification overhead beyond reading public inputs is $o(n\ell)$.

## 4. Relations (exact equations)

**(a) Generic high-degree relation (Sec. 4.1).** $F:\mathbb F^m\times\mathbb F^n\to\mathbb F$,
total degree $\le d$, $F=\sum_{j=0}^d f_j^F$ homogeneous:

$$R_F(\mathrm{pp}):=\{(\mathbf x=(\mathbf x,e),\mathbf w): F(\mathbf x,\mathbf w)=e\}$$

(NP satisfaction = special case $e=0$.) Product relation
$R^\ell_F:=\{(i,(\mathbf x^{(1)},..,\mathbf x^{(\ell)}),(\mathbf y^{(1)},..),(\mathbf w^{(1)},..)): \forall k,\ (i,\mathbf x^{(k)},\mathbf y^{(k)},\mathbf w^{(k)})\in R_F\}$.

**(b) Accumulator relation after multi-cast (Fig. 4 output).** With
$\mathbf x$ = coefficient vector of $\tilde x$, $v_x:=\tilde x(\mathbf r^x)$,
$v_w:=\tilde w(\mathbf r^w)$:

$$
R_{\mathrm{acc}}(\mathrm{pp}):=\left\{
\begin{array}{l}
i,\ \mathbf x=(\mathbf x,\boldsymbol\tau,\mathbf r^x,\mathbf r^w,e),\\
\mathbf y=([[\tilde x_\cup]],[[\tilde w_\cup]],[[\tilde w]]),\\
\mathbf w=\mathbf w
\end{array}
:\ \begin{array}{l}
F(\mathbf x,\mathbf w)=e\\
\wedge\ \tilde x_\cup(\boldsymbol\tau,\mathbf r^x)=\tilde x(\mathbf r^x)\\
\wedge\ \tilde w_\cup(\boldsymbol\tau,\mathbf r^w)=\tilde w(\mathbf r^w)
\end{array}
\right\}
$$

Equivalently the conjunction $R^3_{\mathrm{eval}}\times R_F$ of Eqs. (3)–(6):

- $(i,\mathbf x=(\boldsymbol\tau,\mathbf r^x,v_x),y=[[\tilde x_\cup]],w=\bot)\in R_{\mathrm{eval}}$  (3)
- $(i,\mathbf x=(\boldsymbol\tau,\mathbf r^w,v_w),y=[[\tilde w_\cup]],w=\bot)\in R_{\mathrm{eval}}$  (4)
- $(i,\mathbf x=(\mathbf r^w,v_w),y=[[\tilde w]],w=\bot)\in R_{\mathrm{eval}}$  (5)
- $(i,\mathbf x=(\mathbf x,e),y=\bot,w=\mathbf w)\in R_F$  (6)

**(c) SPS transcript relation (Sec. 5.2).**

$$
R_{\mathrm{sps}}:=\left\{
\begin{array}{l}
i,\ \mathbf x=(\mathbf x,\mathbf r,\boldsymbol\alpha,\alpha),\\
\mathbf y=\bot,\ \mathbf w=\{m_i\}_{i\in[\mu]}
\end{array}:
\begin{array}{l}
F(\mathbf x,\{m_i\}_{i\in[\mu]},\mathbf r,\boldsymbol\alpha)=0\\
\wedge\ \alpha[0]=\alpha\ \wedge\ \alpha[i]=(\alpha[i-1])^2\ \forall i\in[\log\nu-1]
\end{array}
\right\}
$$

**(d) SPS accumulator relation (Fig. 6 output):**
$R_{\mathrm{acc}}:=R_{\mathrm{eval}}\times R^\mu_{\mathrm{eval}}\times R^\mu_{\mathrm{eval}}\times R_F$ with components (9)–(12):

- $(i,\mathbf x=(\mathbf x,\boldsymbol\tau,\mathbf r^x,v_x),y=[[\tilde x_\cup]],w=\bot)\in R_{\mathrm{eval}}$  (9)
- $(i,\mathbf x=(\boldsymbol\tau,\mathbf r^w,v_t),y=[[\tilde m_{\cup,t}]],w=\bot)\in R_{\mathrm{eval}}\ \forall t\in[\mu]$  (10)
- $(i,\mathbf x=(\mathbf r^w,v_t),y=[[\tilde m_t]],w=\bot)\in R_{\mathrm{eval}}\ \forall t\in[\mu]$  (11)
- $(i,\mathbf x=(\mathbf x,\mathbf r,\boldsymbol\alpha,\alpha,e),y=\bot,w=\{m_t\}_{t\in[\mu]})\in R_F$  (12)

**(e) Oracle batching relations (Def. 2).**

$$
R_0:=\left\{\begin{array}{l}i,\mathbf x=(\mathbf x,v,\mathbf r)\\ \mathbf y=([[\tilde f_0]],[[\tilde f_1]]),\ \mathbf w=(f_0,f_1)\end{array}:\ \sum_{i=0}^1\widetilde{\mathrm{eq}}_i(\mathbf r)\cdot\tilde f_i(\mathbf x)=v\right\},
\qquad
R_1:=\left\{i,\mathbf x=\{(\mathbf x_j,v_j)\}_j,\mathbf y=[[\tilde f]],\mathbf w=\bot:\tilde f(\mathbf x_j)=v_j\right\}
$$

with completeness / soundness(radius $\delta^*$) / **succinctness** ($\pi_{\mathrm{batch}}$ and
$t_{\mathrm{batch}}$ sublinear in $|\tilde f|$). Code-based encoding (App. A):

$$
R'_0:=\left\{\begin{array}{l}i,\mathbf x=(\alpha:=(\mathbf 0,\mathbf x),v,\mathbf r)\\ \mathbf y=([[\tilde u_0]],[[\tilde u_1]]),\ \mathbf w=(u_0,u_1)\end{array}:\ \sum_{j=0}^{1}\widetilde{\mathrm{eq}}_j(\mathbf r)\cdot\tilde u_j(\boldsymbol\alpha)=v\right\},\quad u_j=C(f_j)
$$

**(f) Multilinear Plonkish relation (Def. 7, App. A).** Index $i=(q,\sigma)$ with
permutation $\sigma:\{0,1\}^{\log\mu+\log n}\to\{0,1\}^{\log\mu+\log n}$, selectors
$\tilde q\in\mathbb F^{(<2)}[\log\mu+\log s]$, public inputs
$\tilde p\in\mathbb F^{(<2)}[\log\mu+\log m]$, witness oracle
$\tilde w\in\mathbb F^{(<2)}[\log\mu+\log n]$:

- Gate identity: $\tilde f(\mathbf X):=f(\{\tilde q(\mathrm{Bits}(j),\mathbf X)\}_{j=0}^{s-1},\{\tilde w(\mathrm{Bits}(j),\mathbf X)\}_{j=0}^{n-1})=0$ for all $\mathbf X\in\{0,1\}^{\log\mu}$;
- Wiring identity: $\tilde w(\mathbf x)=\tilde w(\sigma(\mathbf x))$ for all $\mathbf x\in\{0,1\}^{\log\mu+\log n}$;
- Instance consistency: $\tilde p(\mathbf x)=\tilde w(\mathbf 0^{\log\mu+\log n-\log m},\mathbf x)$ for all $\mathbf x\in\{0,1\}^{\log m}$.

## 5. Protocols (full step-by-step transcriptions)

### 5.1 Figure 4 — Multi-cast IOR $\mathrm{IOR}_{\mathrm{cast}}:R^\ell_F\to R_{\mathrm{acc}}$

**Prover inputs:** $i$, $\{\mathbf x^{(i)}\}_{i\in[\ell]}$, $\{\mathbf w^{(i)}\}_{i\in[\ell]}$.
**Verifier inputs:** $\iota,\mathcal I$, $\{\mathbf x^{(i)}\}_{i\in[\ell]}$ (indexer: $I=\bot$, $i'=i$).

*Interaction phase.*

1. **P computes** the union polynomials
   $\tilde x_\cup(\mathbf Y,\mathbf X):=\sum_{i\in[\ell]}\widetilde{\mathrm{eq}}_{i-1}(\mathbf Y)\cdot\tilde x^{(i)}(\mathbf X)$,
   $\tilde w_\cup(\mathbf Y,\mathbf X):=\sum_{i\in[\ell]}\widetilde{\mathrm{eq}}_{i-1}(\mathbf Y)\cdot\tilde w^{(i)}(\mathbf X)$.
2. **P → V:** oracles $[[\tilde x_\cup]]$, $[[\tilde w_\cup]]$  (sizes $\ell m$, $\ell n$).
3. **V → P:** $r_y\leftarrow\$\mathbb F^{\log\ell}$.
4. **P computes** selector-based vectors (multilinear in $\mathbf Y$, coefficient-wise):
   $\bar x(\mathbf Y):=\sum_{i\in[\ell]}\widetilde{\mathrm{eq}}_{i-1}(\mathbf Y)\cdot\mathbf x^{(i)}\in(\mathbb F^{(<2)}[\log\ell])^m$,
   $\bar w(\mathbf Y):=\sum_{i\in[\ell]}\widetilde{\mathrm{eq}}_{i-1}(\mathbf Y)\cdot\mathbf w^{(i)}\in(\mathbb F^{(<2)}[\log\ell])^n$.
5. **P computes** $G(\mathbf Y):=F(\bar x(\mathbf Y),\bar w(\mathbf Y))\cdot\widetilde{\mathrm{eq}}(\mathbf Y,r_y)$.
6. **P and V run a $(\log\ell)$-round sum-check** for $\sum_{\mathbf y\in\{0,1\}^{\log\ell}}G(\mathbf y)=0$:
   prover sends $\log\ell$ univariates $G_j(\mathbf Y)$ (each of degree $\le d+1$ in the
   round variable); verifier replies with challenges $\tau_1,\dots,\tau_{\log\ell}$
   (collected as $\boldsymbol\tau\in\mathbb F^{\log\ell}$).
7. **V checks:** reject if $G_1(0)+G_1(1)\ne0$; reject if
   $G_{i+1}(0)+G_{i+1}(1)\ne G_i(\tau_i)$ for any $i\in[\log\ell-1]$.
8. **P computes** the partial evaluations
   $\tilde x(\mathbf X):=\tilde x_\cup(\boldsymbol\tau,\mathbf X)$,
   $\tilde w(\mathbf X):=\tilde w_\cup(\boldsymbol\tau,\mathbf X)$.
9. **P → V:** explicit message $\tilde x$ (i.e. the coefficient vector $\mathbf x\in\mathbb F^m$)
   and oracle $[[\tilde w]]$ (size $n$).
10. **V samples** $\mathbf r^x\leftarrow\$\mathbb F^{\log m}$, $\mathbf r^w\leftarrow\$\mathbb F^{\log n}$.

*Output phase.*

11. Define $\mathbf x$:=$ coefficient vector of $\tilde x$.
12. Define $e:=G_{\log\ell}(\tau_{\log\ell})\cdot\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)^{-1}$ (reject if $\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)=0$).
13. **V outputs** $\mathbf x:=(\mathbf x,\boldsymbol\tau,\mathbf r^x,\mathbf r^w,e)$,
    $\mathbf y:=([[\tilde x_\cup]],[[\tilde w_\cup]],[[\tilde w]])$; prover outputs $\mathbf w$.

*Costs (Lemma 2):* $\log\ell+2$ rounds; explicit proof $O(d\log\ell)$ field elements
(sum-check) $+\ m$ ($\tilde x$ message); oracle length $\ell(m+n)+n$; verifier makes **no
oracle queries**, non-linear work $O(d\log\ell)$ field ops; $R_{\mathrm{acc}}$ contains
3 polynomial oracles. With an extractable PCS, $\mathrm{FS}[\mathrm{IOR}^{PCS}_{\mathrm{cast}}]$
is a non-interactive reduction of knowledge in the ROM.

**Why it works:** for Boolean $\mathbf y=\mathrm{Bits}(k-1)$,
$\bar x(\mathbf y)=\mathbf x^{(k)}$ and each $\tilde x_\cup(\mathbf y,\cdot)=\tilde x^{(k)}(\cdot)$
(exact selector), so $H(\mathbf y)=F$-values vanish on the cube when all inputs satisfy
$R_F$; $\widetilde{\mathrm{eq}}$-anchored sum-check compresses the $\ell$ checks to one
evaluation $e=H(\boldsymbol\tau)$; partial-evaluation claims (3)–(5) bind the *derived*
instance to the *union* commitments at random points.

### 5.2 Figure 5 — Check-compressed SPS $\mathrm{CV}[\Pi_{\mathrm{sps}}]$

**P inputs:** pp, $\mathbf x$, $\mathbf w$. **V inputs:** pp, $\mathbf x$.

1. For $i\in[\mu]$: $m_i\leftarrow P_{\mathrm{SPS}}(\mathbf x,\mathbf w,\{m_j,r_j\}_{j=1}^{i-1})$; **P → V** $m_i$; **V → P** $r_i\leftarrow\$\mathbb F$.
2. Define $\mathbf r:=(r_1,\dots,r_{\mu-1})$; set $\alpha:=r_\mu$.
3. **P computes** $\boldsymbol\alpha:=(\alpha,\alpha^2,\alpha^4,\dots,\alpha^{2^{\log\nu-1}})$; **P → V** $\boldsymbol\alpha$.
4. **V checks:** (1) $F(\mathbf x,\{m_i\}_{i\in[\mu]},\mathbf r,\boldsymbol\alpha)=0$;
   (2) $\alpha[0]=r_\mu$; (3) $\alpha[i]=(\alpha[i-1])^2\ \forall i\in[\log\nu-1]$.

(The compressed scalar check is Eq. (8):
$F(\mathbf x,\{m_i\},\mathbf r,\boldsymbol\alpha):=\sum_{j\in[\nu]}\mathrm{pow}_j(\boldsymbol\alpha)\cdot V_{\mathrm{sps}}(\mathbf x,\{m_i\},\mathbf r)[j]=0$,
degree $D:=d+\log\nu$; Lemma 3: $\mathrm{CV}[\Pi_{\mathrm{sps}}]$ is
$(k_1,\dots,k_\mu,\nu{+}1)$-special-sound because $F(\cdot,\alpha)$ is univariate of
degree $\le\nu-1$ in $\alpha$ — vanishing at $\nu+1$ points forces all $\nu$
coordinates of $V_{\mathrm{sps}}$ to zero.)

### 5.3 Figure 6 — Multi-cast IOR for SPS $\mathrm{IOR}_{\mathrm{cast\text{-}SPS}}:R^\ell\to R_{\mathrm{acc}\text{-}\mathrm{SPS}}$

**P inputs:** $(i,\{\mathbf x^{(k)},\mathbf w^{(k)}\}_{k\in[\ell]})$.
**V inputs:** $\{i,\mathbf x^{(k)}\}_{k\in[\ell]}$.

*Interaction phase.*

1. For each $k\in[\ell]$: $m_1^{(k)}\leftarrow P_{\mathrm{sps}}(\mathbf x^{(k)},\mathbf w^{(k)})$.
2. **P computes** $\tilde x_\cup(\mathbf Y,\mathbf X):=\sum_{k\in[\ell]}\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde x^{(k)}(\mathbf X)$ and
   $\tilde m_{\cup,1}(\mathbf Y,\mathbf X):=\sum_{k\in[\ell]}\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde m_1^{(k)}(\mathbf X)$.
3. **P → V:** $[[\tilde x_\cup]]$, $[[\tilde m_{\cup,1}]]$.
4. **V → P:** $r_1\leftarrow\$\mathbb F$  *(one challenge binds the whole round-1 batch)*.
5. For $i\in[2,\mu]$:
   - (a) for each $k\in[\ell]$: $m_i^{(k)}\leftarrow P_{\mathrm{sps}}(\mathbf x^{(k)},\mathbf w^{(k)},\{m_j^{(k)},r_j\}_{j=1}^{i-1})$;
   - (b) **P computes** $\tilde m_{\cup,i}(\mathbf Y,\mathbf X):=\sum_{k\in[\ell]}\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde m_i^{(k)}(\mathbf X)$;
   - (c) **P → V:** $[[\tilde m_{\cup,i}]]$;
   - (d) **V → P:** $r_i\leftarrow\$\mathbb F$.
6. Set $\alpha:=r_\mu$.
7. **P computes** $\boldsymbol\alpha:=(\alpha,\alpha^2,\dots,\alpha^{2^{\log\nu-1}})$; **P → V** $\boldsymbol\alpha$.
8. **V checks:** (a) reject if $\alpha[0]\ne r_\mu$; (b) reject if
   $\alpha[i]\ne(\alpha[i-1])^2$ for any $i\in[\log\nu-1]$.
9. **P and V run the remaining process of $\mathrm{IOR}_{\mathrm{cast}}$ (Fig. 4 Steps 4–10)**, i.e.:
   selector vectors $\bar x(\mathbf Y),\{\bar m_i(\mathbf Y)\}_i$ from the union oracles,
   $G(\mathbf Y):=F(\bar x(\mathbf Y),\{\bar m_i(\mathbf Y)\}_{i\in[\mu]},\mathbf r,\boldsymbol\alpha)\cdot\widetilde{\mathrm{eq}}(\mathbf Y,r_y)$,
   the $(\log\ell)$-round sum-check $\sum_{\mathbf y}G(\mathbf y)=0$ with challenges
   $\boldsymbol\tau$, partial evaluations $\tilde x(\mathbf X):=\tilde x_\cup(\boldsymbol\tau,\mathbf X)$
   and $\tilde m_i(\mathbf X):=\tilde m_{\cup,i}(\boldsymbol\tau,\mathbf X)\ \forall i$, message
   $\tilde x$, oracles $\{[[\tilde m_i]]\}_i$, and challenges $\mathbf r^x,\mathbf r^w$.

*Output phase.*

10. Define $\mathbf x$ = coefficient vector of $\tilde x$; $\mathbf r:=(r_1,\dots,r_{\mu-1})$;
11. $e:=G_{\log\ell}(\tau_{\log\ell})\cdot\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)^{-1}$;
12. **V outputs** $\mathbf x:=(\mathbf x,\mathbf r,\boldsymbol\alpha,\alpha,\boldsymbol\tau,\mathbf r^x,\mathbf r^w,e)$,
    $\mathbf y:=([[\tilde x_\cup]],\{[[\tilde m_{\cup,i}]]\}_{i\in[\mu]},\{[[\tilde m_i]]\}_{i\in[\mu]})$.

*Costs (Lemma 4):* explicit proof = $m$ field elements ($\tilde x$) + $O(d\log\ell)$
(sum-check); oracles: $[[\tilde x_\cup]]$ of size $\ell m$, $\mu$ oracles
$\{[[\tilde m_{\cup,i}]]\}$ of size $\ell n$, $\mu$ oracles $\{[[\tilde m_i]]\}$ of size $n$;
RO queried $O(\mu+\log\ell)$ times on constant-size inputs (after PCS compilation);
verifier non-linear work $O(d\log\ell)$; $R_{\mathrm{acc}}$ contains $2\mu+1$ oracles.

### 5.4 Figure 7 — 2-to-1 folding IOR $\mathrm{IOR}_{\mathrm{fold\text{-}SPS}}:(R_{\mathrm{acc}})^2\to R_{\mathrm{acc}}$

**P inputs:** $(i_{\mathrm{acc}},\{\mathbf x^{(k)}_{\mathrm{acc}},\mathbf w^{(k)}_{\mathrm{acc}}\}_{k=0}^1)$.
**V inputs:** $(i_{\mathrm{acc}},\{\mathbf x^{(k)}_{\mathrm{acc}}\}_{k=0}^1)$.

*Interaction phase.*

1. For each $k\in\{0,1\}$ define the flattened instance
   $\mathrm{vec}^{(k)}:=(\mathbf x^{(k)}\Vert\mathbf r^{(k)}\Vert\boldsymbol\alpha^{(k)}\Vert\boldsymbol\tau^{(k)}\Vert\mathbf r^{x(k)}\Vert\mathbf r^{w(k)}\Vert(e^{(k)},v_x^{(k)},v_1^{(k)},\dots,v_\mu^{(k)})\Vert m_1^{(k)}\Vert\cdots\Vert m_\mu^{(k)})$.
2. **P computes the folded (virtual) objects:**
   $\widetilde{\mathrm{vec}}(Z):=\sum_{k=0}^{1}\widetilde{\mathrm{eq}}_k(Z)\,\mathrm{vec}^{(k)}$;
   $\tilde x_\cup(Z,\mathbf Y,\mathbf X):=\sum_{k=0}^1\widetilde{\mathrm{eq}}_k(Z)\,\tilde x_\cup^{(k)}(\mathbf Y,\mathbf X)$;
   $\tilde m_i(Z,\mathbf X):=\sum_{k=0}^{1}\widetilde{\mathrm{eq}}_k(Z)\,\tilde m_i^{(k)}(\mathbf X)\ \forall i\in[\mu]$;
   $\tilde m_{\cup,i}(Z,\mathbf Y,\mathbf X):=\sum_{k=0}^{1}\widetilde{\mathrm{eq}}_k(Z)\,\tilde m_{\cup,i}^{(k)}(\mathbf Y,\mathbf X)\ \forall i\in[\mu]$.
3. **P parses** $\widetilde{\mathrm{vec}}(Z)$ as
   $\tilde x(Z),\tilde r(Z),\tilde\alpha(Z),\tilde{\boldsymbol\tau}(Z),\tilde r^x(Z),\tilde r^w(Z),\tilde e(Z),\tilde v_x(Z),\tilde v_1(Z),\dots,\tilde v_\mu(Z),\tilde m_1(Z),\dots,\tilde m_\mu(Z)$.
4. **V → P:** $\gamma\leftarrow\$\mathbb F^{\log(2\mu+2)}$, $r_z\leftarrow\$\mathbb F$.
5. **P computes** $G(Z):=\widetilde{\mathrm{eq}}(r_z,Z)\cdot(p_1(Z)+p_2(Z)+p_3(Z)+p_4(Z))$, where
   - $p_1(Z):=\tilde x_\cup\big(Z,\tilde{\boldsymbol\tau}(Z),\tilde r^x(Z)\big)-\tilde v_x(Z)$
   - $p_2(Z):=\sum_{i\in[\mu]}\mathrm{pow}_i(\gamma)\cdot\big(\tilde m_i(Z,\tilde r^w(Z))-\tilde v_i(Z)\big)$
   - $p_3(Z):=\sum_{i\in[\mu]}\mathrm{pow}_{\mu+i}(\gamma)\cdot\big(\tilde m_{\cup,i}(Z,\tilde{\boldsymbol\tau}(Z),\tilde r^w(Z))-\tilde v_i(Z)\big)$
   - $p_4(Z):=\mathrm{pow}_{2\mu+1}(\gamma)\cdot\big(F(\tilde x(Z),\{\tilde m_i(Z)\}_{i\in[\mu]},\tilde r(Z),\tilde\alpha(Z))-\tilde e(Z)\big)$
6. **1-round sum-check** over $Z\in\{0,1\}$ for $\sum_{z\in\{0,1\}}G(z)=0$: prover sends
   univariate $G(Z)$; verifier samples $\sigma\leftarrow\$\mathbb F$; claim $G(\sigma)$.
7. **P → V:** $\eta_x,\{\eta_i,\eta_{\cup,i}\}_{i\in[\mu]},\eta_F$ where
   $\eta_x:=\tilde x_\cup(\sigma,\tilde{\boldsymbol\tau}(\sigma),\tilde r^x(\sigma))-\tilde v_x(\sigma)$;
   $\eta_i:=\tilde m_i(\sigma,\tilde r^w(\sigma))-\tilde v_i(\sigma)\ \forall i$;
   $\eta_{\cup,i}:=\tilde m_{\cup,i}(\sigma,\tilde{\boldsymbol\tau}(\sigma),\tilde r^w(\sigma))-\tilde v_i(\sigma)\ \forall i$;
   $\eta_F:=F(\tilde x(\sigma),\{\tilde m_i(\sigma)\}_{i\in[\mu]},\tilde r(\sigma),\tilde\alpha(\sigma))-\tilde e(\sigma)$.
8. **V checks** that $G(\sigma)$ equals
   $\widetilde{\mathrm{eq}}(r_z,\sigma)\cdot\Big(\eta_x+\sum_{i\in[\mu]}\mathrm{pow}_i(\gamma)\eta_i+\sum_{i\in[\mu]}\mathrm{pow}_{\mu+i}(\gamma)\eta_{\cup,i}+\mathrm{pow}_{2\mu+1}(\gamma)\eta_F\Big)$.
9. **P and V engage $2\mu+1$ oracle batching protocols $\mathrm{IOR}_{\mathrm{batch}}$ in parallel**
   (one per paired oracle: $[[\tilde x_\cup]]$, $\{[[\tilde m_{\cup,i}]]\}$, $\{[[\tilde m_i]]\}$),
   with fold inputs derived from $\tilde{\boldsymbol\tau}(\sigma),\tilde r^w(\sigma),\tilde r^x(\sigma)$.

*Output phase.*

10. Define $\{(y^\alpha,x^\alpha,v^\alpha)\}_\alpha,\{(y^\beta,x^\beta,v^\beta)\}_\beta,\{(x^\gamma,v^\gamma)\}_\gamma$ as the outputs of $\mathrm{IOR}_{\mathrm{batch}}$.
11. Define $\mathbf x:=\tilde x(\sigma)$, $\mathbf r:=\tilde r(\sigma)$, $\alpha:=\tilde\alpha(\sigma)$, $e:=\tilde e(\sigma)$.
12. **V outputs** $\mathbf x=(\{(y^\alpha,x^\alpha,v^\alpha)\}_\alpha,\{(y^\beta,x^\beta,v^\beta)\}_\beta,\{(x^\gamma,v^\gamma)\}_\gamma,\mathbf x,\mathbf r,\alpha,e)$,
    $\mathbf y=([[\tilde x_\cup]],\{[[\tilde m_{\cup,i}]]\}_{i\in[\mu]},\{[[\tilde m_i]]\}_{i\in[\mu]})$.

*Remark 1:* the batching step may output a *list* of evaluation claims per invocation
(indexed $\alpha,\beta,\gamma$); this is resolved by adding a constant number of auxiliary
evaluation claims at a fixed point (e.g. $\mathbf 0$), as in Arc/WARP.

*Costs (Lemma 5):* explicit proof $O(d+\mu\cdot\delta)$ field elements ($\delta$ = max
claims per $\mathrm{IOR}_{\mathrm{batch}}$ invocation); oracle proof length
$O(\mu\ell n)$; verifier time $(2\mu+1)\cdot t_{\mathrm{batch}}$; **each batching
invocation combines exactly two committed oracles ⇒ $O(1)$ CRC, $\ell$-independent.**

### 5.5 Figures 8–10 — SPS protocols for HyperPlonk (App. A)

- **Fig. 8 $\Pi_{\mathrm{gate}}$** (P: $f,\tilde q,\tilde w$; V: $f,\tilde q$): 1. P → V: $\tilde w(\mathbf X)$. 2. V checks
  $f(\{\tilde q(\mathrm{Bits}(j),\mathbf X)\}_{j=0}^{s-1},\{\tilde w(\mathrm{Bits}(j),\mathbf X)\}_{j=0}^{n-1})=0$.
- **Fig. 9 $\Pi_{\mathrm{wire}}$** (P: $\sigma,\tilde w$; V: $\sigma$): 1. P → V: $\tilde w(\mathbf X)$. 2. V checks
  $\tilde w(\mathbf x)-\tilde w(\sigma(\mathbf x))=0$ for all $\mathbf x\in\{0,1\}^{\log\mu}$.
- **Fig. 10 $\Pi_{\mathrm{pi}}$** (P: $\tilde p,\tilde w$; V: $\tilde p$): 1. P → V: $\tilde w(\mathbf X)$. 2. V checks
  $\tilde p(\mathbf x)=\tilde w(\mathbf 0^{\log\mu+\log n-\log m},\mathbf x)$ for all $\mathbf x\in\{0,1\}^{\log m}$.

### 5.6 Figure 11 — Code-based oracle batching $\mathrm{NIR}_{\mathrm{batch}}$

**P inputs:** pp, $i,\mathbf x,\mathbf y$; $\mathbf w=(u_0,u_1)$. **V inputs:** pp, $i,\mathbf x,\mathbf y$.

1. Parse $\mathbf x=(\boldsymbol\alpha,\mathbf v,\mathbf r)$ (with $\boldsymbol\alpha:=(\mathbf 0,\mathbf x)$) and $\mathbf y=([[\tilde u_0]],[[\tilde u_1]])$.
2. **P computes** $u:=\sum_{i=0}^{1}\widetilde{\mathrm{eq}}_i(\mathbf r)\cdot u_i$ and its oracle $[[\tilde u]]$.
3. **P → V:** $[[\tilde u]]$.
4. **V → P:** $\alpha_1,\dots,\alpha_s\leftarrow\$\mathbb F^{\log(1/\rho)+\log n}$ *(out-of-domain samples)*.
5. **P computes** $\mu_1,\dots,\mu_s\in\mathbb F$ with $\mu_j:=\tilde u(\alpha_j)$; **P → V** $\mu_1,\dots,\mu_s$.
6. **V samples** $b_1,\dots,b_t\leftarrow\$\{0,1\}^{\log(1/\rho)+\log n}$.
7. **V queries** $\tilde u(b_j),\tilde u_0(b_j),\tilde u_1(b_j)$ for all $j\in[t]$.
8. **V checks** $\tilde u(b_j)=\sum_{i=0}^{1}\widetilde{\mathrm{eq}}_i(\mathbf r)\cdot\tilde u_i(b_j)$ for all $j\in[t]$.

*Output:* $\mathbf x':=(\{(\alpha_j,\mu_j)\}_{j\in[s]},\{(b_j,\tilde u(b_j))\}_{j\in[t]})$, $\mathbf y':=[[{\tilde u}]]$.

Security (Theorem 4): RBR knowledge-soundness error $\le2^{-\lambda}$ for every
$\delta\in(0,1)$ if $|\mathbb F|\ge 2^{\lambda/s-1}\cdot|L(C,\delta)|^{2/s}$ and
$t\ge\lambda/\log\frac1{1-\delta}$.

### 5.7 Figure 13 — Non-interactive prover $\mathrm{NIR}_{\mathrm{cast\text{-}SPS}}.P$

**Inputs:** $(\mathrm{pk},\{\mathbf x^{(k)},\mathbf w^{(k)}\}_{k\in[\ell]})$.

1. For each $k\in[\ell]$: $m_1^{(k)}\leftarrow P_{\mathrm{sps}}(\mathbf x^{(k)},\mathbf w^{(k)})$.
2. Compute $\tilde x_\cup(\mathbf Y,\mathbf X):=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde x^{(k)}(\mathbf X)$.
3. Compute $\tilde m_{\cup,1}(\mathbf Y,\mathbf X):=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde m_1^{(k)}(\mathbf X)$.
4. Set $C_\cup:=\mathrm{Commit}(\mathrm{ck},\tilde x_\cup)$, $C_{\cup,1}:=\mathrm{Commit}(\mathrm{ck},\tilde m_{\cup,1})$.
5. $r_1\leftarrow\mathrm{Hash}(C_\cup,C_{\cup,1})$.
6. For $i\in[2,\mu]$: (a) $m_i^{(k)}\leftarrow P_{\mathrm{sps}}(\mathbf x^{(k)},\mathbf w^{(k)},\{m_j^{(k)},r_j\}_{j=1}^{i-1})$;
   (b) $\tilde m_{\cup,i}:=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\tilde m_i^{(k)}(\mathbf X)$;
   (c) $C_{\cup,i}:=\mathrm{Commit}(\mathrm{ck},\tilde m_{\cup,i})$; (d) $r_i\leftarrow\mathrm{Hash}(r_{i-1},C_{\cup,i})$.
7. $\alpha:=r_\mu$; $\boldsymbol\alpha:=(\alpha,\alpha^2,\dots,\alpha^{2^{\log m}})$ — *(paper text: powers up to $2^{\log m}$; $\nu$-dependent in general; keep consistent with $F$'s $\mathrm{pow}$ indexing)*.
8. $r^{\mathrm{sc}}\leftarrow\mathrm{Hash}(\boldsymbol\alpha)$.
9. **NI sum-check over $\mathbf Y$** with:
10. $\bar x(\mathbf Y):=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)\mathbf x^{(k)}$;
11. $\bar m_i(\mathbf Y):=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf Y)m_i^{(k)}\ \forall i\in[\mu]$;
12. $G(\mathbf Y):=F(\bar x(\mathbf Y),\{\bar m_i(\mathbf Y)\}_{i\in[\mu]},\mathbf r^{F})\cdot\widetilde{\mathrm{eq}}(\mathbf Y,r^{\mathrm{sc}})$  *(where $\mathbf r^F:=(\mathbf r\Vert\alpha)$, App. E.1)*;
13. run a $(\log\ell)$-round non-interactive sum-check for $\sum_{\mathbf y\in\{0,1\}^{\log\ell}}G(\mathbf y)=0$, obtaining polynomials $\{G_j(\mathbf Y)\}_{j\in[\log\ell]}$ and challenges $\boldsymbol\tau\in\mathbb F^{\log\ell}$;
14. set $e:=G_{\log\ell}(\tau_{\log\ell})$;
15. set $\tilde x(\mathbf X):=\tilde x_\cup(\boldsymbol\tau,\mathbf X)$;
16. for all $i\in[\mu]$: $\tilde m_i(\mathbf X):=\tilde m_{\cup,i}(\boldsymbol\tau,\mathbf X)$, $C_i:=\mathrm{Commit}(\mathrm{ck},\tilde m_i)$;
17. $(\mathbf r^x,\mathbf r^w)\leftarrow\mathrm{Hash}(r^{\mathrm{sc}},\{C_i\}_{i\in[\mu]})$;
18. **Output proof $\pi$:** message $\tilde x$; commitments $C_\cup,\{C_{\cup,i}\}_{i\in[\mu]},\{C_i\}_{i\in[\mu]}$; challenges $\boldsymbol\alpha,\boldsymbol\tau,r^{\mathrm{sc}},\mathbf r^x,\mathbf r^w$; sum-check $\{G_j(\mathbf Y)\}_{j\in[\log\ell]}$, $e$.

### 5.8 Figure 14 — Non-interactive verifier $\mathrm{NIR}_{\mathrm{cast\text{-}SPS}}.V$

**Inputs:** $(\mathrm{vk},\{\mathbf x^{(k)}\}_{k\in[\ell]},\pi)$.

1. Parse $\pi$ as $\tilde x,C_\cup,\{C_{\cup,i}\},\{C_i\},\boldsymbol\alpha,\boldsymbol\tau,r^{\mathrm{sc}},\mathbf r^x,\mathbf r^w,\{G_j\},e$.
2. Recompute SPS challenges: $r_1\leftarrow\mathrm{Hash}(C_\cup,C_{\cup,1})$; $r_i\leftarrow\mathrm{Hash}(r_{i-1},C_{\cup,i})$ for $i\in[2,\mu]$.
3. Recompute sum-check challenges: $r^{\mathrm{sc}\prime}\leftarrow\mathrm{Hash}(\boldsymbol\alpha)$; reject if $\ne r^{\mathrm{sc}}$; $\tau_j'\leftarrow\mathrm{Hash}(G_j(\mathbf Y))$ for all $j\in[\log\ell]$; reject if $\boldsymbol\tau'\ne\boldsymbol\tau$.
4. Check sum-check consistency: reject if $G_1(0)+G_1(1)\ne0$; reject if $G_{j+1}(0)+G_{j+1}(1)\ne G_j(\tau_j)$ for any $j\in[\log\ell-1]$.
5. Check final value: reject if $e\ne G_{\log\ell}(\tau_{\log\ell})$.
6. $(\mathbf r^{x\prime},\mathbf r^{w\prime})\leftarrow\mathrm{Hash}(r^{\mathrm{sc}},\{C_i\}_{i\in[\mu]})$; reject if mismatch.
7. $\mathbf x$ := coefficient vector of $\tilde x(\mathbf X)$.
8. **Output** $\mathbf x_{\mathrm{acc}}:=(\mathbf x,\{C_{\cup,i}\}_{i\in[\mu]},C_\cup,\{C_i\}_{i\in[\mu]},\{r_i\}_{i\in[\mu]},\boldsymbol\alpha,\boldsymbol\tau,\mathbf r^x,\mathbf r^w,e)$.

### 5.9 Figures 15–16 — Non-interactive 2-to-1 fold $\mathrm{NIR}_{\mathrm{fold}}$

**P (Fig. 15), inputs $(\mathrm{pk},\{(\mathbf x_{\mathrm{acc}}^{(k)},\mathbf w_{\mathrm{acc}}^{(k)})\}_{k\in\{0,1\}})$:**

1. For each $k\in\{0,1\}$: $\mathrm{vec}^{(k)}:=(\mathbf x^{(k)}\Vert\mathbf r^{(k)}\Vert\boldsymbol\alpha^{(k)}\Vert\boldsymbol\tau^{(k)}\Vert\mathbf r^{x(k)}\Vert\mathbf r^{w(k)}\Vert(e^{(k)},v_x^{(k)},v_1^{(k)},\dots,v_\mu^{(k)})\Vert m_1^{(k)}\Vert\cdots\Vert m_\mu^{(k)})$.
2. Compute $\widetilde{\mathrm{vec}}(Z):=\sum_{k=0}^1\widetilde{\mathrm{eq}}_k(Z)\mathrm{vec}^{(k)}$, $\tilde x_\cup(Z,\mathbf X):=\sum_{k=0}^1\widetilde{\mathrm{eq}}_k(Z)\tilde x_\cup^{(k)}$; for all $i\in[\mu]$: $\tilde m_i(Z,\mathbf X):=\sum_{k=0}^1\widetilde{\mathrm{eq}}_k(Z)\tilde m_i^{(k)}$, $\tilde m_{\cup,i}(Z,\mathbf Y,\mathbf X):=\sum_{k=0}^1\widetilde{\mathrm{eq}}_k(Z)\tilde m_{\cup,i}^{(k)}$.
3. Parse $\widetilde{\mathrm{vec}}(Z)$ into $\tilde x(Z),\tilde r(Z),\tilde\alpha(Z),\tilde{\boldsymbol\tau}(Z),\tilde r^x(Z),\tilde r^w(Z),\tilde e(Z),\tilde v_x(Z),\tilde v_1(Z),\dots,\tilde v_\mu(Z),\tilde m_1(Z),\dots,\tilde m_\mu(Z)$.
4. $\gamma,r_z\leftarrow\mathrm{Hash}(\{\mathbf x_{\mathrm{acc}}^{(k)}\}_{k\in\{0,1\}})$.
5. Define $p_1(Z):=\tilde x_\cup(Z,\tilde r^x(Z))-\tilde v_x(Z)$ *(paper: $p_1(Z):=\tilde x_\cup(Z,\tilde r^x(Z))-\tilde v_x(Z)$; note Fig. 7 uses $(Z,\tilde{\boldsymbol\tau}(Z),\tilde r^x(Z))$ — see pitfalls §8)*;
   $p_2(Z):=\sum_{i\in[\mu]}\mathrm{pow}_i(\gamma)(\tilde m_i(Z,\tilde r^w(Z))-\tilde v_i(Z))$;
   $p_3(Z):=\sum_{i\in[\mu]}\mathrm{pow}_{\mu+i}(\gamma)(\tilde m_{\cup,i}(Z,\tilde{\boldsymbol\tau}(Z),\tilde r^w(Z))-\tilde v_i(Z))$;
   $p_4(Z):=\mathrm{pow}_{2\mu+1}(\gamma)(F(\tilde x(Z),\{\tilde m_i(Z)\},\tilde r(Z),\tilde\alpha(Z))-\tilde e(Z))$.
6. $G(Z):=\widetilde{\mathrm{eq}}(r_z,Z)\cdot(p_1+p_2+p_3+p_4)(Z)$.
7. 1-round NI sum-check over $Z\in\{0,1\}$: run for $\sum_z G(z)=0$, obtaining $G_1(Z)$, $\sigma\in\mathbb F$, claim $v_G:=G(\sigma)$.
8. Set $\eta_x:=p_1(\sigma)$, $\eta_i:=\tilde m_i(\sigma,\tilde r^w(\sigma))-\tilde v_i(\sigma)$, $\eta_{\cup,i}:=\tilde m_{\cup,i}(\sigma,\tilde{\boldsymbol\tau}(\sigma),\tilde r^w(\sigma))-\tilde v_i(\sigma)\ \forall i$.
9. Run $2\mu+1$ instances of $\mathrm{IOR}_{\mathrm{batch}}.P$ in parallel; obtain $\{y^\alpha,x^\alpha,v^\alpha\}_\alpha,\{y^\beta,x^\beta,v^\beta\}_\beta,\{x^\gamma,v^\gamma\}_\gamma$.
10. Output $\mathbf x:=(\{y^\alpha,x^\alpha,v^\alpha\}_\alpha,\{y^\beta,x^\beta,v^\beta\}_\beta,\{x^\gamma,v^\gamma\}_\gamma,\mathbf x,\mathbf r,\alpha,e)$, $\mathbf y:=([[\tilde x_\cup]],\{[[\tilde m_{\cup,i}]]\},\{[[\tilde m_i]]\})$, and $\pi$ containing $(G_1,\sigma,v_G)$ and batching transcripts.

**V (Fig. 16), inputs $(\mathrm{vk},\{\mathbf x_{\mathrm{acc}}^{(k)}\}_{k\in\{0,1\}},\pi)$:**

1. Parse $\pi$ → $(G_1(Z),\sigma,v_G)$ + batching transcripts.
2. $(\gamma,r_z)\leftarrow\mathrm{Hash}(\{\mathbf x_{\mathrm{acc}}^{(k)}\}_{k\in\{0,1\}})$.
3. Check 1-round sum-check: reject if $G_1(0)+G_1(1)\ne0$; $\sigma'\leftarrow\mathrm{Hash}(G_1(Z))$, reject if $\sigma'\ne\sigma$; reject if $v_G\ne G(\sigma)$.
4. Check aggregated identity: reject if
   $v_G\ne\widetilde{\mathrm{eq}}(r_z,\sigma)\cdot\big(\eta_x+\sum_{i\in[\mu]}\mathrm{pow}_i(\gamma)\eta_i+\sum_{i\in[\mu]}\mathrm{pow}_{\mu+i}(\gamma)\eta_{\cup,i}+\mathrm{pow}_{2\mu+1}(\gamma)\eta_F\big)$.
5. Run $2\mu+1$ instances of $\mathrm{IOR}_{\mathrm{batch}}.V$ in parallel; verify $\{y^\alpha,x^\alpha,v^\alpha\},\{y^\beta,x^\beta,v^\beta\},\{x^\gamma,v^\gamma\}$.
6. Compute $\mathbf x:=\tilde x(\sigma)$, $\mathbf r:=\tilde r(\sigma)$, $\alpha:=\tilde\alpha(\sigma)$, $e:=\tilde e(\sigma)$.
7. Output $\mathbf x,\mathbf y$ as in Fig. 15.

### 5.10 NARK and accumulation scheme (Sec. 6.2)

**NARK = wrapper of $\mathrm{NIR}_{\mathrm{cast\text{-}SPS}}$:**
$G:=\mathrm{NIR}_{\mathrm{cast}}.G$;
$I$: $(\mathrm{pk}_{\mathrm{cast}},\mathrm{vk}_{\mathrm{cast}},i')\leftarrow\mathrm{NIR}_{\mathrm{cast}}.I(\mathrm{pp},i)$, output $(\mathrm{pk},\mathrm{vk})=(\mathrm{pk}_{\mathrm{cast}},(\mathrm{vk}_{\mathrm{cast}},i',\mathrm{pp}))$;
$P$: run $\mathrm{NIR}_{\mathrm{cast}}.P$ → $(\pi_{\mathrm{cast}},\mathbf w_{\mathrm{acc}})$, output $\pi=(\pi.\mathbf x,\pi.\mathbf w):=(\pi_{\mathrm{cast}},\mathbf w_{\mathrm{acc}})$;
$V$: parse, compute $\mathbf x_{\mathrm{acc}}\leftarrow\mathrm{NIR}_{\mathrm{cast}}.V(\mathrm{vk}_{\mathrm{cast}},\{\mathbf x^{(k)}\},\pi_{\mathrm{cast}})$, accept iff $(i',\mathbf x_{\mathrm{acc}},\mathbf w_{\mathrm{acc}})\in R^{PCS}_{\mathrm{acc}}(\mathrm{pp})$.

**ACC (multi-instance):** $G:=\mathrm{NIR}_{\mathrm{cast}}.G$;
$I$: sequentially $(\mathrm{pk}_{\mathrm{cast}},\mathrm{vk}_{\mathrm{cast}},i')\leftarrow\mathrm{NIR}_{\mathrm{cast}}.I$, $(\mathrm{pk}_{\mathrm{fold}},\mathrm{vk}_{\mathrm{fold}},i')\leftarrow\mathrm{NIR}_{\mathrm{fold}}.I$, output
$\mathrm{apk}=(\mathrm{vk}_{\mathrm{cast}},\mathrm{pk}_{\mathrm{fold}},\mathrm{vk}_{\mathrm{fold}})$, $\mathrm{avk}=(\mathrm{vk}_{\mathrm{cast}},\mathrm{vk}_{\mathrm{fold}})$, $\mathrm{adk}=(i',\mathrm{pp})$;
$P(\mathrm{apk},\{\mathbf x^{(k)}\},\pi,\mathrm{acc}^{(0)})$: parse $\pi=(\pi_{\mathrm{cast}},\mathbf w_{\mathrm{acc}})$;
  - $\mathrm{acc}^{(1)}.\mathbf x\leftarrow\mathrm{NIR}_{\mathrm{cast}}.V(\mathrm{vk}_{\mathrm{cast}},\{\mathbf x^{(k)}\},\pi_{\mathrm{cast}})$;
  - $\mathrm{acc}^{(1)}.\mathbf w:=\mathbf w_{\mathrm{acc}}$;
  - $(\mathrm{pf},\mathrm{acc}.\mathbf w)\leftarrow\mathrm{NIR}_{\mathrm{fold}}.P(\mathrm{pk}_{\mathrm{fold}},\{\mathrm{acc}^{(0)},\mathrm{acc}^{(1)}\})$;
  - $\mathrm{acc}.\mathbf x\leftarrow\mathrm{NIR}_{\mathrm{fold}}.V(\mathrm{vk}_{\mathrm{fold}},\{\mathrm{acc}^{(0)}.\mathbf x,\mathrm{acc}^{(1)}.\mathbf x\},\mathrm{pf})$; output $(\mathrm{acc},\mathrm{pf})$;
$V$: recompute $\mathrm{acc}^{(1)}.\mathbf x$ via $\mathrm{NIR}_{\mathrm{cast}}.V$ and check
$\mathrm{acc}.\mathbf x=\mathrm{NIR}_{\mathrm{fold}}.V(\mathrm{vk}_{\mathrm{fold}},\{\mathrm{acc}^{(0)}.\mathbf x,\mathrm{acc}^{(1)}.\mathbf x\},\mathrm{pf})$;
$D(\mathrm{adk},\mathrm{acc})$: accept iff $(i',\mathrm{acc}.\mathbf x,\mathrm{acc}.\mathbf w)\in R^{PCS}_{\mathrm{acc}}(\mathrm{pp})$.

**Multi-instance IVC (Def. 4, App. A):** $\mathrm{IVC}=(G,I,P,V)$ where
$P(\mathrm{ipk},i,\{z_i^{(k)},w_i^{(k)},z_{i+1}^{(k)}\}_k,\Pi_i)\to\Pi_{i+1}$ absorbs $\ell$
transitions per step; the recursive circuit computes $\varphi_i$ on the $k$-th transition
*and* embeds the accumulation verification for $(\pi.\mathbf x,\mathrm{acc}.\mathbf x)$ →
$\mathrm{acc}'.\mathbf x$ (one circuit carries the verification, others use dummy wiring);
the prover invokes the multi-cast reduction to produce the reduced recursive proof;
final verifier runs the decider on $\mathrm{acc}'$.

## 6. Soundness & Security

### 6.1 Multi-cast RBR soundness (Lemma 2 proof, Sec. 4.2)

Three stages, adversarial prover $P^*$:

- **Stage 1 (sum-check):** if $\sum_{\mathbf y}G(\mathbf y)\ne0$, the $\log\ell$-round
  sum-check accepts with $\epsilon_{\mathrm{sc}}\le\log\ell\cdot(d{+}1)/|\mathbb F|$
  (individual degree $d+1$). Conditioned on acceptance the transcript defines
  $(\boldsymbol\tau,G(\boldsymbol\tau))$ with
  $G(\boldsymbol\tau)=H(\boldsymbol\tau)\cdot\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)$.
- **Stage 2 (division):** if $\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)=0$ the verifier
  rejects; since it is non-zero of total degree $\log\ell$ in $r_y$,
  $\epsilon_{\mathrm{div}}\le\log\ell/|\mathbb F|$ (Schwartz–Zippel). Otherwise
  $e=H(\boldsymbol\tau)$ is transcript-consistent.
- **Stage 3 (partial evaluation):** if either identity
  $\tilde x_\cup(\boldsymbol\tau,\mathbf r^x)=\tilde x(\mathbf r^x)$ or
  $\tilde w_\cup(\boldsymbol\tau,\mathbf r^w)=\tilde w(\mathbf r^w)$ fails as a polynomial
  identity in $\mathbf X$, it fails at random points with
  $\epsilon_{\mathrm{pe}}\le(\log m+\log n)/|\mathbb F|$.
- **Extraction:** conditioned on the complement, the reduced statement is consistent
  with the oracle strings; the extractor reads $\mathbf w$ from $[[\tilde w]]$ on the
  Boolean hypercube ($\mathbf w[j{+}1]:=\tilde w(\mathrm{Bits}(j))$), recovering per-instance
  witnesses from $[[\tilde w_\cup]]$ if needed; runtime polynomial in oracle lengths.

$$\epsilon\ \le\ \epsilon_{\mathrm{sc}}+\epsilon_{\mathrm{div}}+\epsilon_{\mathrm{pe}}\ \le\ \frac{\log\ell\,(d+1)}{|\mathbb F|}+\frac{\log\ell}{|\mathbb F|}+\frac{\log m+\log n}{|\mathbb F|}$$

Also used: **Corollary 1** (equality-polynomial facts):
$\widetilde{\mathrm{eq}}_i(\mathbf b)^d=\widetilde{\mathrm{eq}}_i(\mathbf b)$ for $d\ge1$;
$\widetilde{\mathrm{eq}}_i(\mathbf b)\cdot\widetilde{\mathrm{eq}}_j(\mathbf b)=0$ for $i\ne j$
(on-cube selector orthogonality — the algebraic heart of multi-cast mixing).

### 6.2 Special-soundness ladder

- **Lemma 3:** $\Pi_{\mathrm{sps}}$ $(k_1..k_\mu)$-special-sound ⇒
  $\mathrm{CV}[\Pi_{\mathrm{sps}}]$ $(k_1,\dots,k_\mu,\nu{+}1)$-special-sound
  (univariate degree $\le\nu-1$ in $\alpha$; $\nu{+}1$ points force all $\nu$
  coordinates of $V_{\mathrm{sps}}$ to vanish).
- **Lemma 6:** $(a_1,\dots,a_k)$-special-sound $(2k{+}1)$-move public-coin protocol ⇒
  knowledge soundness with $\kappa\le\sum_{i=1}^k(a_i-1)/|\mathbb F|$.
- **Lemma 4:** $\mathrm{IOR}_{\mathrm{cast\text{-}SPS}}$ = IOR $R^\ell\to R_{\mathrm{acc}}$,
  perfect completeness + RBR knowledge soundness; FS + extractable PCS ⇒
  $\mathrm{NIR}_{\mathrm{cast\text{-}SPS}}$ in the ROM.

### 6.3 Folding soundness (Lemma 5 / App. F.1)

$\mathrm{IOR}_{\mathrm{fold}}$ has soundness errors
$\epsilon_{\mathrm{zc}},\epsilon_{\mathrm{sc}},\epsilon_{\mathrm{batch}}$ (extraction time
$O(\ell^2n^2)$):

$$\epsilon_{\mathrm{zc}}=(\mu+1)/|\mathbb F|,\quad
\epsilon_{\mathrm{sc}}=\max(d{+}1,\log(\ell n))/|\mathbb F|,\quad
\epsilon_{\mathrm{eval}}=\mu/|\mathbb F|,\quad
\epsilon_{\mathrm{batch}}=2\mu\cdot\epsilon_0$$

with $\epsilon_0$ the $\mathrm{IOR}_{\mathrm{batch}}$ soundness error. State-function
structure (per stage):

- **Empty transcript:** $\mathrm{State}(i,\mathbf x,\mathbf y,\varnothing)=1$ iff
  $(\mathbf x^{(k)},\mathbf y^{(k)})\in L(R_F)$ for all $k\in[\ell]$.
- **Bounding $\epsilon_{\mathrm{zc}}$ (challenges $\gamma,r_z$):** state = 1 iff
  $\sum_{z\in\{0,1\}}G(z)=0$ where (Eq. 14, per input $k$)
  $G^{(k)}(Z^\gamma,Z^r)=\widetilde{\mathrm{eq}}(Z^r,k)\cdot(F(\tilde x^{(k)},\{m_i^{(k)}\},\mathbf r_F^{(k)})-e^{(k)})+\sum_{i\in[\mu]}\mathrm{pow}_i(Z^\gamma)(\tilde m_i^{(k)}(\mathbf r^{x(k)})-v_i^{(k)})+\sum_{i\in[\mu]}\mathrm{pow}_{i+\mu}(Z^\gamma)(\tilde m_{\cup,i}^{(k)}(\boldsymbol\tau^{(k)},\mathbf r^{x(k)})-v_i^{(k)})$;
  total degree $\le\mu+1$ ⇒ union over $k$ vanishes with prob $\le(\mu{+}1)/|\mathbb F|$.
  Extractor outputs $\mathbf w=(\{m_{\cup,i}^{(k)}\},\{m_i^{(k)}\})$ in $O(\mu n^2)$ by
  querying the oracles on the cube ($m_{\cup,i}^{(k)}[j]=\tilde m_{\cup,i}(\mathrm{Bits}(j))$).
- **Bounding $\epsilon_{\mathrm{sc}}$ (sum-check):** state after $\mathrm{tr}=(\gamma,r_z,G(Z))$:
  $G(\sigma)=\widetilde{\mathrm{eq}}(r_z,\sigma)\cdot(F(\tilde x(\sigma),\{m_i(\sigma)\},\mathbf r_F(\sigma))-e(\sigma))+\sum_i\mathrm{pow}_i(\gamma)(\tilde m_i(Z,\mathbf r^x(Z))-v_i(Z))+\sum_i\mathrm{pow}_{\mu+i}(\gamma)(\tilde m_{\cup,i}(Z,\boldsymbol\tau(Z),\mathbf r^x(Z))-v_i(Z))$ (Eq. 15);
  a cheating univariate $G'\ne G$ of degree $\max(d{+}1,\log(\ell n))$ matching at
  random $\sigma$ costs $\max(d{+}1,\log(\ell n))/|\mathbb F|$.
- **Bounding $\epsilon_{\mathrm{eval}}$ ($\eta$ message):** state = 1 iff
  $\eta=F(\tilde x(\sigma),\{m_i(\sigma)\},\mathbf r_F(\sigma))-e(\sigma)$,
  $\eta_i=\tilde m_i(\sigma,\mathbf r^x(\sigma))-v_i(\sigma)$,
  $\eta_{\cup,i}=\tilde m_{\cup,i}(\sigma,\boldsymbol\tau(\sigma),\mathbf r^x(\sigma))-v_i(\sigma)$;
  forging $\boldsymbol\eta'$ satisfying Eq. (16)
  $G(\sigma)=\widetilde{\mathrm{eq}}(r_z,\sigma)\cdot[\eta'+\sum_i\mathrm{pow}_i(\gamma)\eta'_i+\sum_i\mathrm{pow}_{i+\mu}(\gamma)\eta'_{\cup,i}]$
  costs $\le\mu/|\mathbb F|$ for random $\gamma$.
- **Bounding $\epsilon_{\mathrm{batch}}$:** union bound over $2\mu$ batching
  invocations: $2\mu\cdot\epsilon_0$.

### 6.4 Composition theorems

- **Main Theorem 1 / Theorem 2 (SPS instantiation):** given
  $\mathrm{NIR}_{\mathrm{cast\text{-}SPS}}$ ($R^{PCS\,\ell}\to R^{PCS}_{\mathrm{acc}}$) and
  $\mathrm{NIR}_{\mathrm{fold\text{-}SPS}}$ ($(R^{PCS}_{\mathrm{acc}})^2\to R^{PCS}_{\mathrm{acc}}$,
  same generator), the transformation $T$ outputs (NARK, ACC) with perfect completeness
  and RBR knowledge soundness in the ROM. Each fold level invokes the batching verifier
  a **constant** number of times (independent of $\ell$); $O(\log\ell)$ fold levels
  contribute only explicit field work. Accumulation prover:
  $O(\ell m+\ell\mu n)$ field ops + $\mu+\log\ell$ RO queries + $2\mu+1$
  $\mathrm{NIR}_{\mathrm{batch}}.P$ runs. Accumulation verifier: $O(\log\ell)$ field ops +
  $\mu+\log\ell$ RO queries + $2\mu+1$ $\mathrm{NIR}_{\mathrm{batch}}.V$ runs =
  $O(\mu)$ CRC total. Decider: $O(\mu)$ PCS.Verify on the evaluation claims.
- **Theorem 3 (multi-instance IVC, from [BCLMS21]):** NARK + multi-instance ACC ⇒
  multi-instance IVC for constant-depth compliance predicates, assuming the
  accumulation-verifier circuit complexity is sublinear in its input; PQ/ZK are
  inherited.
- **Theorem 4 (code-based batching):** $\mathrm{NIR}_{\mathrm{batch}}$ RBR knowledge
  soundness error $\le2^{-\lambda}$ for every $\delta\in(0,1)$ iff
  $|\mathbb F|\ge 2^{\lambda/s-1}\cdot|L(C,\delta)|^{2/s}$ and $t\ge\lambda/\log\frac1{1-\delta}$
  (with zero-evader error folded in).
- **Theorem 5 (IOR→NIR compilation):** oracle→PCS commitment, then FS; RBR KS +
  extractable PCS ⇒ RBR KS in the ROM.

### 6.5 Where the PCS matters (slack-free notes for the lattice lab)

The PCS choice *only* affects (i) the $\mathrm{IOR}_{\mathrm{batch}}$ instantiation and
(ii) PCS.Open / PCS.Verify costs for the induced evaluation claims. Requirements:
extractability (Def. 16-style knowledge soundness of Eval) and *succinct batching*
(proof/verification sublinear in $|\tilde f|$). Homomorphic PCS ⇒ direct group
combination; non-homomorphic (code/lattice) ⇒ use Arc-style codeword batching or
lattice folding-based batching (Symphony / LatticeFold). For an `lzk`-style lattice
backend, the CRC "combination" of two Ajtai commitments
$C=c_{1,0}A_0+c_{1,1}A_1\cdot G$-style gadget combination is *linear* — the batching
relation $R_0$ maps onto $A\mathbf f_0,A\mathbf f_1$ claims with
$\widetilde{\mathrm{eq}}_i(\mathbf r)$ weights, so the two commitments can be folded
into one with $O(1)$ in-circuit ring operations (this is the interface Quasar
preserves).

## 7. Parameters & Concrete Efficiency

### Table 1 — asymptotic multi-accumulation comparison

| Scheme | Constraints | PCS type | PQ | Verifier cost |
|---|---|---|---|---|
| ProtoGalaxy | Plonkish | EC | No | $O(1)$ Hash, $O(\ell\cdot d)$ $G$ |
| HyperNova | CCS | EC | No | $O(\log n)$ Hash, $O(\ell)$ $G$ |
| **Quasar (curve)** | Plonkish | EC | No | $O(\log\ell)$ Hash, $O(1)$ $G$ |
| Arc | R1CS | RS codes | Yes | $O(\ell\cdot\log(1/\rho)\cdot\log n)$ Hash |
| WARP | PESAT | linear codes | Yes | $O(\ell\cdot\log(1/\rho)\cdot\log n)$ Hash |
| **Quasar (code)** | Plonkish | linear codes | Yes | $O(\log(1/\rho)\cdot(\log n+\log\ell))$ Hash |

($\ell$ = arity, $d$ = max relation degree, $n$ = witness length, $\rho$ = code rate.)

### Table 2 — concrete recursion overhead (constraint counts, Nova toolchain)

| Arity | HyperNova (R1CS) | Quasar (R1CS) | Ratio | Arc (Plonkish) | Quasar (Plonkish) | Ratio |
|---|---|---|---|---|---|---|
| 2 | $1.48\times2^{13}$ | $2\times1.48\times2^{13}\approx2\times1.48\cdot2^{13}$ → 1.01× | 1.01× | $1.13\times2^{18}$ | $1.13\times2^{17}$ | 1.91×* |
| 4 | $1.91\times2^{13}$ | $1.61\times2^{13}$ | 1.09× | $1.09\times2^{18}$ | $1.14\times2^{17}$ | 1.91× |
| 8 | $1.32\times2^{14}$ | $1.75\times2^{13}$ | 1.51× | $1.62\times2^{18}$ | $1.16\times2^{17}$ | 2.79× |
| 16 | $1.98\times2^{14}$ | $1.88\times2^{13}$ | 2.10× | $1.08\times2^{19}$ | $1.18\times2^{17}$ | 3.66× |
| 32 | $1.62\times2^{15}$ | $1.01\times2^{14}$ | 3.21× | $1.34\times2^{19}$ | $1.20\times2^{17}$ | 4.49× |

(*Row $\ell=2$ R1CS as printed: "2 1.48×10^13 2 1.48×10^13 1.01×" — the R1CS baseline
parity at arity 2; ratios = baseline/Quasar.)

### Table 3 — batching instantiations ($n$: polynomial size)

| Scheme | Assumption | Prover | Proof size | Batch proof size |
|---|---|---|---|---|
| IPA | DL | $O(n\log n)$ | $O(\log n)$ | $O(\log n)$ |
| Mercury | DL | $O(n\log n)$ | $O(1)$ | $O(1)$ |
| RS codes | Hash | $O(n\log n)$ | $O(\log n)$ | $O(\lambda\log(1/\rho)\log n)$ |
| Linear codes | Hash | $O(n)$ | $O(\log n)$ | $O(\lambda\log(1/\rho)\log n)$ |

### Table 4 — circuit size vs arity and degree (constraints)

| Arity $\ell$ | HyperNova $d{=}2/4/8$ | Quasar $d{=}2/4/8$ |
|---|---|---|
| 2 | 12,533 / 12,539 / 12,552 | 12,143 / 12,149 / 12,161 |
| 4 | 15,667 / 15,677 / 15,697 | 13,229 / 13,239 / 13,259 |
| 8 | 21,629 / 21,643 / 21,671 | 14,315 / 14,329 / 14,357 |
| 16 | 32,467 / 32,485 / 32,521 | 15,401 / 15,419 / 15,455 |
| 32 | 53,057 / 53,079 / 53,123 | 16,487 / 16,509 / 16,553 |
| 64 | 93,151 / 93,177 / 93,229 | 17,573 / 17,599 / 17,651 |

Quasar's growth is $\approx+1087$ constraints per arity doubling (vs HyperNova
$\approx+1.69\times$ per doubling); degree sensitivity is tiny (tens of constraints).

### Experimental setup (App. C)

- Hardware: MacBook Air 2025, Apple M4 (8 cores), 16 GB RAM; macOS Sequoia 15.6;
  rustc 1.92.0 `--release`. Circuit synthesis: `bellpepper` crate.
- Curve-based: Mercury PCS over BN256. Code-based: FRI with Poseidon-Merkle;
  future drop-in Brakedown-style linear-time PCS.
- Parameters: $\lambda=128$, $d=2$ default, $\ell\in\{2,4,8,16,32,64\}$; RS code
  message length $k=2^8$, rate $\rho=1/16$, codeword length $n=k/\rho=2^{12}$.
- Workload: synthetic predicate incrementally computing a hash chain.
- Fig. 12a (curve): across all arities Quasar has lower constraints, lower prover
  time, lower peak memory; for $\ell\ge16$, CRC is > half of HyperNova's
  accumulation-verification constraints but < one quarter in Quasar. Constraint axis
  spans ~$2^{13}$–$2^{17}$; time axis 12–18 s; memory 50–300 MB.
- Fig. 12b (code): Arc incurs 3–5× higher prover cost; constraint axis ~$2^{17}$–$2^{19.5}$;
  time up to ~3.5 ks; memory up to ~55 MB region per plot (Arc dominates).
- Scope caveat: **no end-to-end IVC prototype** — no recursive wrapper + no in-circuit
  FRI verifier yet; measurements are circuit-footprint sanity checks of the
  $\ell$-dependence model only.

## 8. Implementation Notes (for the `lzk` Python core engine)

### 8.1 Data structures

- `UnionPoly`: multilinear-in-$(\mathbf Y,\mathbf X)$ table of shape
  $(\ell, m)$ / $(\ell, n)$ stored as an $\ell\times n$ matrix (row $k$ =
  $\mathbf w^{(k)}$); its MLE is *implicit* — evaluation at $(\mathbf y,\mathbf x)$ =
  $\sum_k\widetilde{\mathrm{eq}}_{k-1}(\mathbf y)\,\tilde w^{(k)}(\mathbf x)$.
  Reuse `lzk`'s `mle_eval` (tensor/LDE engine) + precomputed
  `eq(Y, y)` factors.
- `FoldedState`: per-round accumulator of
  $(\tilde x_\cup,\{\tilde m_{\cup,i}\},\{\tilde m_i\})$ *folded views* — after the
  $\mathrm{IOR}_{\mathrm{fold}}$ rounds, these are only ever accessed at
  $Z=\sigma$-derived points, so store lazy closures, not materialized tables.
- `SPSTranscript`: $\{(m_i, r_i)\}_{i\le\mu}$ + $\boldsymbol\alpha$ power ladder
  (length $\log\nu$, squares chain — verify $\alpha[i]=(\alpha[i-1])^2$).
- `AccInstance`: $(\mathbf x,\mathbf r,\boldsymbol\alpha,\alpha,\boldsymbol\tau,\mathbf r^x,\mathbf r^w,e)$
  + commitments $(C_\cup,\{C_{\cup,i}\},\{C_i\})$ + values $(v_x,\{v_i\})$.

### 8.2 Algorithms to build (priority order)

1. **eq-selector utilities**: $\widetilde{\mathrm{eq}}_i(\mathbf Y)$, on-cube
   orthogonality (Corollary 1) — already essentially `lzk`'s tensor/LDE module.
2. **Multilinear sum-check with $\widetilde{\mathrm{eq}}$ anchor** (the
   $G(\mathbf Y)=H(\mathbf Y)\widetilde{\mathrm{eq}}(\mathbf Y,r_y)$, individual degree
   $d+1$, $\log\ell$ rounds) — extend `lzk`'s sumcheck to accept the *product with eq*
   and the final division $e:=G_{\log\ell}(\tau_{\log\ell})\cdot\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)^{-1}$
   (compute $\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)$ by the product formula;
   reject on zero — do NOT silently resample inside FS).
3. **Union polynomial commitment + partial-evaluation opening** — for a lattice
   backend this is the core new PCS-facing piece: commit to $\tilde w_\cup$ as
   $\ell n$ coefficients (Ajtai/`lzk` commitment over $R_q$ with packing), open at
   $(\boldsymbol\tau,\mathbf r^w)$ *and* the derived $\tilde w$ at $\mathbf r^w$; the
   opening proof should batch the two points (Serval-style batching or one
   sumcheck-style inner-product reduction).
4. **$\mathrm{CV}[\Pi_{\mathrm{sps}}]$ compressor**: build $F$ from
   $V_{\mathrm{sps}}$'s homogeneous components + $\mathrm{pow}_j$ ladder.
5. **$\mathrm{IOR}_{\mathrm{fold}}$ 1-round $Z$-sumcheck**: folded-parse
   $\widetilde{\mathrm{vec}}(Z)$; $p_1..p_4$ assembly; $\eta$ splitting; this is the
   exact in-circuit verifier body — keep it field-only.
6. **Batching $\mathrm{IOR}_{\mathrm{batch}}$** for the chosen backend: lattice =
   Ajtai gadget-combination fold (two commitments, $O(1)$ ring ops); code = Fig. 11
   (out-of-domain samples + $t$ proximity queries).
7. **FS transcript hasher** with strict ordering (see pitfalls).

### 8.3 Complexity summary (what the recursive circuit pays)

- Per fold level: 1 hash-anchored 1-round sumcheck over $Z$ + $2\mu+1$ batching
  verifications ⇒ $O(\mu)$ CRC; levels = $O(\log\ell)$ ⇒ total explicit field work
  $O(\log\ell)$, CRC $O(1)$ per level, $\ell$-independent CRC overall per step.
- Multi-cast verifier: $O(d\log\ell)$ field ops (sumcheck bookkeeping) + linear
  public-input pass for $\mathbf x$ (excluded from the metric but real: computing
  $\mathbf x=\sum_k\widetilde{\mathrm{eq}}_{k-1}(\boldsymbol\tau)\mathbf x^{(k)}$
  costs $O(\ell m)$).
- Accumulation prover: $O(\ell m+\ell\mu n)$ field ops + $2\mu+1$ batching provers
  (each linear in the oracle length for code/lattice backends) ⇒ linear-time
  accumulation prover with linear-code or Ajtai backends.

### 8.4 Pitfalls (hard-won, from the paper's fine print)

1. **$\widetilde{\mathrm{eq}}(\boldsymbol\tau,r_y)=0$ division event.** In the
   *interactive* protocol the verifier may re-sample $r_y$; under Fiat–Shamir this
   must become an explicit reject (probability $\le\log\ell/|\mathbb F|$), never a
   resample loop (state-restoration attacks). Fig. 13/14 sidestep by defining
   $e:=G_{\log\ell}(\tau_{\log\ell})$ directly — note the *inconsistency* between
   Fig. 4 Step 12 (divides by eq) and Fig. 13 Step 14 (no division, absorbing the eq
   factor into the sumcheck claim $G$'s definition with anchor $r^{\mathrm{sc}}$).
   Implementation must pick ONE convention and match prover/verifier; recommended:
   the Fig. 13 convention (no inversion, $r^{\mathrm{sc}}$ anchor).
2. **Challenge-order dependency.** In Fig. 6/13, $r_y$/$r^{\mathrm{sc}}$ is derived
   *after* $\boldsymbol\alpha$ and binds the whole SPS transcript; $\mathbf r^x,\mathbf r^w$
   are derived *after* the partial-evaluation commitments $\{C_i\}$ (Step 17). Any
   reordering breaks the Schwartz–Zippel independence underlying Stages 2–3.
3. **Interleaving is load-bearing.** Sending $\Theta(\ell)$ raw SPS messages per round
   would blow up RO inputs to $\Theta(\ell|m_i|)$; the union-oracle batching (Step 5 of
   Fig. 6) is what keeps FS digests succinct. In-circuit, verify commitments to union
   oracles, not the oracles.
4. **Interface preservation.** The entire point is that $R_{\mathrm{acc}}$ contains
   exactly $2\mu+1$ oracles *both* after multi-cast *and* after each fold. Any "convenience"
   refactor that adds a per-instance commitment to the accumulator reintroduces
   $\Theta(\ell)$ CRC.
5. **$\mathrm{pow}_j$ indexing.** $j{-}1=\sum_{k\in S}2^k$, $\mathrm{pow}_j=\prod_{k\in S}X_k$;
   off-by-one here silently corrupts the $\nu$-equation compression (Eq. 8) and the
   $p_2/p_3/p_4$ weight ladders (powers $\mathrm{pow}_i,\mathrm{pow}_{\mu+i},\mathrm{pow}_{2\mu+1}$
   of the *same* $\gamma$).
6. **Fig. 7 vs Fig. 15 mismatch on $p_1$.** Fig. 7 defines
   $p_1(Z)=\tilde x_\cup(Z,\tilde{\boldsymbol\tau}(Z),\tilde r^x(Z))-\tilde v_x(Z)$
   (three arguments: folded union poly evaluated at folded $\boldsymbol\tau$), while
   Fig. 15 Step 6 writes $p_1(Z):=\tilde x_\cup(Z,\tilde r^x(Z))-\tilde v_x(Z)$
   (two arguments). The Fig. 7 form is the consistent one (matches relation (9) with
   folded $\boldsymbol\tau$); implement the 3-argument form and treat Fig. 15's as a
   typo. Similarly Fig. 7's final checks evaluate
   $\tilde m_i(Z,\tilde r^w(Z))$ but relation (11) uses $\mathbf r^w$ — the folded
   point $\tilde r^w(\sigma)$ is what the batched claims must use.
7. **Zero-indexed vs one-indexed $\widetilde{\mathrm{eq}}$.** Fig. 4 uses
   $\widetilde{\mathrm{eq}}_{i-1}$ (instances $i\in[\ell]$ one-indexed); fold uses
   $\widetilde{\mathrm{eq}}_k$, $k\in\{0,1\}$. Keep a single convention in code.
8. **Code-based details.** Systematic code assumption is required for lifting
   $\tilde f_i(\mathbf x)=v_i$ to $\tilde u_i(\mathbf 0,\mathbf x)=v_i$; $1/\rho$ must
   be a power of two; out-of-domain samples $\alpha_j$ are sampled from
   $\mathbb F^{\log(1/\rho)+\log n}$ (i.e. the full codeword domain), and $b_j$ from
   the Boolean subcube of the same dimension.
9. **Theorem 4's $t$ bound:** $t\ge\lambda/\log\frac1{1-\delta}$ — as printed in the
   paper ("$\lambda/(-\log(1-\delta))$"); with small $\delta$ this is $\approx
   \lambda/\delta$, so proximity radius choice directly drives in-circuit Merkle depth.
10. **Zero-knowledge is out of scope.** Quasar inherits none; per-step ZK for
    intermediate witnesses requires an additional layer (cf. Nova-style blinds — do
    not bolt on naively, the union-polynomial structure leaks cross-instance
    linearity unless blinded per instance).
11. **Promise/proximity relations.** The paper focuses on distance-preserving
    accumulation; promise-relation extensions follow Bünz et al. — if the lab targets
    code-based backends with $\delta^*>0$, the decider must check proximity claims,
    not just evaluations.
12. **Public-input processing is linear and NOT the enemy.** Do not attempt to
    sublinearize $\mathbf x$-processing with the same machinery — the security
    argument explicitly excludes it, and mixing it into the sumcheck changes the
    statement being proven.

### 8.5 Reuse map from `lzk`

| Quasar piece | `lzk` module |
|---|---|
| $\widetilde{\mathrm{eq}}$, MLE evaluation, tensor decomposition | tensor/LDE engine |
| $(\log\ell)$-round sumcheck with eq anchor | multilinear sumcheck (extend for $d{+}1$ degree + anchor) |
| Union polynomial storage/commitment | Ajtai commitment over $R_q$ (pack $\ell n$ coefficients; NTT for linearity) |
| $\mathrm{IOR}_{\mathrm{batch}}$ (lattice flavor) | ring-norm sumcheck / gadget folding modules |
| FS challenge derivation | Fiat-Shamir hasher with domain separators + transcript hashing |
| SPS check compression $F$, $\mathrm{pow}$ | small utility on top of field arithmetic |

## 9. Implementation Status (Gap Ledger)

## 9. Implementation Status (Gap Ledger)

- ✅ The multi-cast union-polynomial commitment (union_commit: the arity
  hypercube mixing) and the recursive accumulation fold with the
  γ-ladder keeping the accumulator interface constant
  (accumulate_fold chained across steps).
- □ Not implemented: the eq-anchored partial-evaluation sumcheck with the
  division event, the CV compression ladder, the 2μ+1-oracle interface
  preservation checks, the SPS interleaving.

**(replacing the placeholder)**

- DONE: the multi-cast union-polynomial commitment (union_commit: the arity hypercube mixing) and the recursive accumulation fold with the gamma-ladder keeping the accumulator interface constant (accumulate_fold chained across steps).
- NOT implemented: the eq-anchored partial-evaluation sumcheck with the division event, the CV compression ladder, the (2 mu + 1)-oracle interface preservation checks, the SPS interleaving.
