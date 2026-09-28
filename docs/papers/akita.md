# Akita: A High-Performance Lattice-Based Polynomial Commitment Scheme — Deep Analysis & Implementation Spec

> Source: `papers_txt/akita.txt` (paper PDF, ~11k extracted lines). This document is an
> implementation-oriented specification and deep analysis. All equation numbers, figure
> numbers, lemma/theorem numbers, and table values are cross-referenced to the paper.

## 1. Metadata

| Field | Value |
|---|---|
| **Title** | Akita: A High-Performance Lattice-Based Polynomial Commitment Scheme |
| **Authors** | Quang Dao¹,³, Omid Bodaghi¹, Amirhossein Khajehpour¹, Giuseppe Vitto¹, Mohammadtaghi Badakhshan¹, Markos Georghiades², Fengrun Liu³, Jiapeng Zhang⁴, Justin Thaler²,⁵ |
| **Affiliations** | ¹ LayerZero Labs, ² a16z crypto research, ³ Carnegie Mellon University, ⁴ University of Southern California, ⁵ Georgetown University |
| **Venue/date** | ePrint 2026 (preprint; direct successor to Hachi ePrint 2026 and Greyhound). Twist and Shout is cited as "CRYPTO 2026" |
| **Assumption** | Module-SIS (MSIS) over cyclotomic rings $\mathbb{Z}_q[X]/(X^d+1)$, with both $\ell_\infty$ (coefficient) and $\ell_2$ (Euclidean) variants per Def. 3.6. Fiat–Shamir security proven in the **classical random oracle model (ROM)**; QROM left as future work. |
| **Headline** | A lattice multilinear PCS with **all three** deployment properties: (i) small proofs — $\tilde{O}_{\kappa_{root},\lambda}(\log N)$, concretely **61–72 KB**; (ii) fast verification — $\tilde{O}_{\kappa_{root},\lambda}(N^{1/\kappa_{root}})$ for any fixed $\kappa_{root}\ge 2$, concretely < 20 ms single-threaded at $N=2^{30}$; (iii) standard Module-SIS soundness. Prover $\tilde{O}(N)$, pay-per-bit (sparse) commitment. |

**Key results (from abstract & §1.1):**

- **Setup offloading**: public setup matrices are committed ahead of time; the verifier's
  matrix processing is *deferred and proved against these commitments*. For any fixed
  $K \ge 2$: verifier time $\tilde{O}_{K,\lambda}(N^{1/K})$, proof size $\tilde{O}_{K,\lambda}(\log N)$,
  prover $\tilde{O}_{K,\lambda}(N)$, Module-SIS soundness (Theorem 1.1).
- "Optimize every fold from root to tail and iterate the fold to completion": optimized
  digit range check (prover $O(b^2L)\to O(bL)$, round communication
  $2(\log_2 b-1)\lceil\log_2 L\rceil + O(1)$ field elements), relation-specific ring
  dimensions, subring challenges, two opening representations (direct coefficient packing
  vs evaluation trace), commitment compression to **128 bytes**, exact Euclidean
  ($\ell_2$) norm checks.
- Deployment capabilities: batched openings of separately-committed polynomials,
  low-communication distributed proving (response chunking), offline planner for secure
  parameters under configurable cost objectives.
- Benchmarks (§13): proofs of 61–72 KB; vs Greyhound calibrated to same lattice-security
  target: **19.2×–89.7× faster verification**. Least memory of all compared schemes
  (overhead sublinear in $N$). Jolt integration: **1.3–2.2× prover speedup** and
  **2.2–7.4× verifier speedup** over Jolt-with-Dory, every proof < 100 KB.
- Motivating application: Twist & Shout (CRYPTO 2026) memory-checking arguments inside
  the Jolt zkVM commit to *one-hot* polynomials — concatenations of standard basis
  vectors $e_j$ — that are almost entirely zero, so commitment time must be
  pay-per-nonzero-entry.

**Comparison table (paper Table 1)** — concretely-oriented lattice PCSs, all with $\tilde{O}(N)$ provers:

| PCS | Binding assumption | Proof size | Verifier | Artifact |
|---|---|---|---|---|
| Greyhound [78] | M-SIS | $\tilde{O}_\lambda(\log N)$; 46–53 KB for $N=2^{26}$–$2^{30}$ | $\tilde{O}_\lambda(N^{1/2})$ | End-to-end C, AVX-512 only |
| Hachi [76] | M-SIS | $\tilde{O}_\lambda(\log N)$; 55 KB (estimate) $N=2^{30}$ | $\tilde{O}_\lambda(N^{1/2})$ | Partial Rust, single fold |
| Jindo [51] | M-SIS | $\tilde{O}_\lambda(N^{1/3})$; 315–1207 KB, $N=2^{14}$–$2^{20}$ | $\tilde{O}_\lambda(N^{1/3})$ | End-to-end Go |
| RoKoKo [58] | vSIS | $\tilde{O}_\lambda(\log N)$; 115 KB, $N=2^{26}$–$2^{30}$ | $\tilde{O}_\lambda(\log N)$ | End-to-end Rust |
| Grand Danois [53] | vSIS | $O_\lambda(\log N)$; 80–90 KB (est.) $N=2^{32}$ | $O_\lambda(\log N)$ | No implementation |
| **Akita** | **M-SIS** | $\tilde{O}_{\kappa_{root},\lambda}(\log N)$; **61.3–67.3 KB**, $N=2^{22}$–$2^{30}$ | $\tilde{O}_{\kappa_{root},\lambda}(N^{1/\kappa_{root}})$ | Production-feature-complete Rust |

Context: prior art trilemma — Greyhound/Hachi give small proofs from Module-SIS but
square-root verifiers; RoKoKo/Grand Danois get polylog verification only under the
stronger/less-studied vanishing-SIS assumption; polylog-from-Module-SIS works
(Fenzi–Moghaddas–Nguyen, SLAP, Cini et al.) have MB-scale proofs (8.3 MB, 767 MB, 5.17 MB
at degree $2^{30}$). Akita's position: keep Greyhound-family concrete compactness,
improve the verifier both concretely and asymptotically, staying on plain Module-SIS.

## 2. Notation Table

Index sets are zero-based: $[n] := \{0,\dots,n-1\}$. $\log$ is base 2.

| Symbol | Meaning |
|---|---|
| $N = 2^\ell$ | number of Boolean evaluations of the committed multilinear polynomial $\tilde f$ (input size) |
| $\tilde f, f$ | multilinear polynomial over base field; $f(x)=\tilde f(x)$ for $x\in\{0,1\}^\ell$ |
| $\mathbb{K}=\mathbb{F}_q$, $\mathbb{E}=\mathbb{F}_{q^k}$ | base (coefficient) field; opening/challenge/evaluation field, $k\in\{1,2,4\}$ |
| $q$ | odd prime modulus |
| $\lambda$ | security parameter (128-bit target) |
| $R_{q,d}$, $R_q$ | cyclotomic ring $\mathbb{Z}_q[X]/(X^d+1)$; $R_q$ when $d$ is clear |
| $d$, $d_A,d_B,d_D$ | ring dimension (power of two); per-matrix ring dimensions for the inner-fold ($A$), outer-commitment ($B$), partial-evaluation ($D$) matrices |
| $d_{F,i}, d_{H,i}$ | per-layer ring dimensions of the two compression chains $F_1,F_2$ (outer) and $H_1,H_2$ (opening) |
| $d_{max,j}$ | largest native ring dimension among active ring-valued rows of fold $j$ |
| $s_{split}$ | number of irreducible factors of $X^d+1$ mod $q$ (power of two, $1<s_{split}\le d$); $q\equiv 2^{s_{split}}+1 \pmod {2^{s_{split}+1}}$ |
| $H \le \mathrm{Aut}(R_q)$ | Galois subgroup fixing the embedded field $\mathbb{E}$; minimal splitting: $H=\langle\sigma_{-1},\sigma_{4^{k}+1}\rangle$, $\sigma_i:X\mapsto X^i$ |
| $\sigma_{-1}$ | automorphism $X\mapsto X^{-1}$ |
| $\mathrm{Tr}_H$ | $=\sum_{\sigma\in H}\sigma$ (automorphism trace) |
| $\psi$ | packing map $\mathbb{E}^{d/k}\to R_q$ (Hachi trace construction); $(\mathbb{F}_{q^k})^{d/k}\!\to R_q$ with $\mathrm{Tr}_H(\psi(a)\sigma_{-1}(\psi(b)))=(d/k)\langle a,b\rangle$ |
| $e_j = X^{jm}+X^{-jm}$ | ring-subfield basis elements, $j\in[1,k)$, $m:=d/(2k)$; basis $\{1,e_1,\dots,e_{k-1}\}$ of the fixed subfield over $\mathbb{F}_q$ |
| $\mathrm{cf}(w)$ | coefficient vector $(w_0,\dots,w_{d-1})\in\mathbb{Z}_q^d$ of $w\in R_q$ |
| $\|w\|_\infty,\|w\|_1,\|w\|_2$ | centered-representative norms over the concatenated coefficient vector (for vectors of ring elements too) |
| $M_a\in\mathbb{Z}^{d\times d}$ | negacyclic-convolution matrix of centered lift of $a\in R_q$ |
| $\|v\|_{\mathrm{mul},2}:=\|M_v\|_{2\to2}$ | spectral norm of $a\mapsto av$; $\|a\|_{\mathrm{mul},2}=\max_k |a(\zeta_k)|$, $\zeta_k=e^{(2k+1)\pi i/d}$ |
| $S, S_E, \iota$ | challenge subring $S=\mathbb{F}_q[Y]/(Y^{d_{car}}+1)$, carrier ring $S_E=\mathbb{E}[Y]/(Y^{d_{car}}+1)$, embedding $\iota:S\hookrightarrow R$, $Y\mapsto X^{kh}$ |
| $d_{car}, h$ | retained coefficient axis dimension and stride with $d_A = k h d_{car}$ ($d=k h d_{car}$ generally) |
| $b, b_1, b_z, b^\star$ | gadget bases: source/commitment base $b=2^\ell$, opening base $b_1$, response base $b_z$, common certified range base $b^\star$ |
| $\delta, \delta_{com}, \delta_{open}, \delta_f, \delta_r$ | digit depths: generic $\delta=\lceil\log_b q\rceil$, commitment, opening-partial, folded-response, quotient |
| $\mathcal{D}_b=\{-b/2,\dots,b/2-1\}$ | balanced digit alphabet (half-open) |
| $\mathcal{A}_b$ | same set as $\mathcal{D}_b$ in usage; paper uses $\mathcal{A}_b$ for the range-check alphabet |
| $T_k, M_k$ | largest positive / negative magnitude representable with $k$ balanced base-$b$ digits: $T_k=\frac b2\left(\frac{b^k-1}{b-1}\right)$, $M_k=\frac b2\cdot\frac{b^k-1}{b-1}$... (exact: $M_k = \frac{b}{2}\cdot\frac{b^k-1}{b-1}$) — see §3 below |
| $G_{b,n}$, $G^{-1}_{b,n}$ | gadget matrix $I_n\otimes(1\ b\ \cdots\ b^{\delta-1})\in R_q^{n\times n\delta}$; balanced decomposition right-inverse |
| $G_z$ | response recomposition $I_{M\delta}\otimes(1,b_z,\dots,b_z^{\tau-1})$, $z=G_z\hat z$ |
| $\mathcal{C}\subset R_q$ | folding-challenge family: sparse support, fixed magnitudes $(n_a)_{a\in\mathcal{A}}$, random signs |
| $\mathcal{A}, \mathcal{A}^+$, $s$, $\omega$, $c_{max}$ | allowed magnitudes set; active set ($n_a>0$); support size $s=\sum n_a$; $\omega=\sum_a a\,n_a$ ($\|c\|_1$); $c_{max}=\max\mathcal{A}^+$ ($\|c\|_\infty$) |
| $|\mathcal{C}|=2^s\binom{d}{s}\binom{s}{n_a:a\in\mathcal{A}}$ | raw cardinality of one challenge coordinate |
| $\mathcal{C}^{acc}$, $\mathcal{C}^{acc}_\Gamma$ | verifier-sampled (filtered) family; operator-norm-filtered family $\{c\in\mathcal{C}_0:\mathrm{OpNormAccept}_\Gamma(c)=1\}$ |
| $\Gamma, \kappa_1, \kappa_2$ | accepted folding-challenge bounds: operator-norm ($\|cz\|_2\le\Gamma\|z\|_2$), coefficient $\ell_1$, $\ell_2$ |
| $B, M, N_R$ | block count $B=\lceil N/M\rceil$; ring elements per block $M=2^{r_{pos}}$; packed vector length $N_R = BM$ |
| $r_{blk}=\lceil\log_2 B\rceil$, $r_{pos}$ | block-index bits; position bits |
| $s_i$, $t_i$, $\hat t_i$ | gadget decomposition of block $i$; inner image $t_i=As_i$; digitized inner image $\hat t_i = G^{-1}_{b_1,n_A}(t_i)$ |
| $\hat s$ | concatenated digit decomposition $G^{-1}_{b,M}(f)$ (commitment openings) |
| $u$, $u_s$, $x_{B,s}$ | outer commitment image $u=B\hat t$; sliced outer images $u_s = Bx_{B,s}\in R_{q,d_B}^{n_B}$; padded input vector of slice $s$ |
| $v$, $\hat e$, $\hat e_i$ | opening image $v=D\hat e$, $\hat e=(\hat e_i)_{i\in[B]}$; $\hat e_i=G^{-1}_{b_1,1}(e_i)$ digitization of partial |
| $u_{pub}, v_{pub}$ | transmitted payloads (raw or compressed) |
| $C$, $C_{S,h}$ | public commitment payload; preprocessed setup-prefix commitment for offloaded edge $h$ |
| $\hat u_j,\hat v_j$ | digits in outer ($F$) / opening ($H$) compression chains |
| $e_i$, $\bar e_i$, $v_R$ | partial opening evaluations per block (carrier-ring or $A$-ring element); $\bar e_i=\langle a,f_i\rangle$; $v_R=\sum_i\tilde\chi_{blk}(i)\bar e_i$ with $\mathrm{Tr}_{pack}(v_R)=v$ |
| $\mathrm{Tr}_{pack}$, $T(Z)$ | public linear functional $R_q\to\mathbb{E}$ from the trace identity; $T(Z)=m^{-1}\mathrm{Tr}_H(Z\sigma_{-1}(\check\chi))$ |
| $a\in R_q^M$ | within-block opening weights |
| $\check\chi = \psi((\widetilde{eq}(\rho_{pack},u))_u)$ | packed equality weights for packed-coordinate axes |
| $\tau_\nu$ | trace digit weights $\frac1m\mathrm{Tr}_H(X^\nu\sigma_{-1}(\check\chi))$ |
| $\omega_{Tr}(i,\ell,\nu)$ | trace weight $\theta\,\widetilde{eq}(\rho_{blk},i)\,b^\ell_{op}\tau_\nu$ |
| $z$, $\hat z$ | folded response $z=\sum_i c_i s_i$; digitized response carried to the next level |
| $w_0=(\hat z,\hat e,\hat t)$, $w_{next}=(\hat z,\hat e,\hat t,\hat r)$ | private relation witness; with quotient digits $\hat r$ |
| $\alpha\in\mathbb{E}$ | ring-reduction evaluation challenge (shared by quotient lifting and quotient-free routes) |
| $\alpha^{(d)}$ | multilinear extension of $(1,\alpha,\dots,\alpha^{d-1})$ on $\log d$ coefficient variables: $\prod_j (1+y_j(\alpha^2-1))$ (Eq. 52) |
| $\tilde\alpha^{(d_b)}$ | truncated weight prefix per block dimension $d_b$ |
| $Q$ (quotient) | prover-supplied polynomial s.t. $\sum_c A_c(X)W_c(X)-Y(X)=(X^d+1)Q(X)$ |
| $\kappa_{A,\alpha}^{(d)}(j)$ | quotient-free weight $:=(A(X)X^j \bmod (X^d+1))(\alpha)$ (transpose-convolution) |
| $Q_{\mathcal{A}}(w)=\prod_{a\in\mathcal{A}}(w-a)$ | range polynomial over digit alphabet $\mathcal{A}$ |
| $Q^{sq}(s)=\prod_{k=0}^{b/2-1}(s-k(k+1))$ | symmetry-reduced range polynomial in $s=w(w+1)$ |
| $\tilde s$, $s_{claim}$, $r_{virt}$ | transformed polynomial $\tilde s(x)=\tilde w(x)(\tilde w(x)+1)$ on Booleans; its sum-check claim; anchor point |
| $\tau_0$, $\tau_1$ | range-anchor challenge point; row-batching challenge point |
| $m_{\tau_1}$ | relation polynomial combined by row-batching point $\tau_1$ |
| $\sigma_S$ | setup contribution to $m_{\tau_1}(r_2)=m_{local}(r_2)+\sigma_S$ |
| $S=(S_0,S_1,\dots)$, $S^\flat$, $N_{setup}$, $N_{active}$ | shared flat setup vector; canonical zero-padded vector for offloading; provisioned stream length $2^{\lceil\log_2 N_{view}\rceil}$; longest active prefix |
| $N_{view}$ | max over admitted matrix instances of $n_I m_I d_I$ |
| $\omega_{setup}(p)$ | combined public weight of all uses of $S_p$: $\sigma_S=\sum_{p<N_{active}} S_p\,\omega_{setup}(p)$ |
| $\widetilde S^\flat, \widetilde\omega_{setup}$ | multilinear polynomials with Boolean evaluations of the padded setup prefix / weights; $\nu_S$ = padded variable count |
| $\rho_S$, $s_{\rho_S}$, $\mathcal{S}_h=(C_{S,h},\rho_S,s_{\rho_S})$ | setup opening point, claimed value, setup-prefix opening group carried to fold $h+1$ |
| $\mathcal{O}_{h+1}=(\mathcal{S}_h,\mathcal{W}_{h+1})$ | opening shape passed across an offloaded edge |
| $\kappa_{root}$, $N^\star$ | constant-root exponent; target scale $N^\star:=N^{1/\kappa_{root}}$ (Eq. 17) |
| $\kappa_{FS}$, $Q_{max}$ | Fiat–Shamir target and max classical RO query count (counting nonce probes) |
| $\kappa_h$, $\epsilon_{cw,h}$ | tensor-reduction head arity at receiver $h$; its coordinate-wise fold error |
| $\epsilon_{h,r}^{enc}, \epsilon_{h,r}^2$ | encoding / energy failure allocations for marginal response bounds |
| $\rho_{model,h}$ | multiplicative envelope relating modeled response moment to completeness premise |
| $\mathcal{M}_h$ | typed recursive moment state $(d_{pack};(\mu_\chi,v_\chi^{full},v_\chi^{local})_{\chi\in RespPart})$ |
| $\vartheta_{j,c}$ | public weight combining claim $c$ of source group $j$ in a multi-instance fold |
| $\zeta_{batch}$ | fresh challenge whose powers derive root-batching weights |
| $N_{clm,h}$, $N_{chunk,h}$ | total claims entering receiver $h$; response chunks retained by fold $h$ |
| $\Delta f,j^{cert}, \Delta rsp,h,g,a^{cert}, \Delta_{\Sigma,h,g}^{cert}$ | certified difference envelopes (group response / retained chunk / aggregate) |
| $p_h^{acc}, p_{h,r}^{rsp}, N_{try,h}$ | admission targets; verifier-enforced nonce allowance |
| $\alpha_{h,u}$, $a_h$ | certified accepted fraction per challenge coordinate; lower bound on construction success |
| $\delta_{h,r}^{brsp}, \delta_{h}^{btot}$ | response-admission and complete nonce-failure bounds |
| $E_{int}(\hat z)$, $E_{resp}$, $S_{max}$ | squared norm of reconstructed integer response; transmitted integer value; schedule bound |
| $p^h_{r}box, p^h_{r}ball, p^G_{r}$ | Gaussian-surrogate box / ball / correlated joint response scores |
| $\beta_{fold}^{cert}$ | coefficient envelope implied by the enforced response-digit alphabet |
| $[-M_f, T_f]$ | exact interval representable by honest canonical response digits |
| $G$ | number of opening groups in a batch |
| $n_{clm,j}$, $B_j$ | claims in group $j$; its input blocks per claim |
| $c^A_{j,c,i}$, $z_j$ | per-group folding challenges; per-group response $z_j=\sum_{c,i}c^A_{j,c,i}s_{j,c,i}$ |
| $N_{chunk}$, $I_j$, $z^{(j)}$ | number of contiguous response chunks; chunk index sets; local responses $z^{(j)}=\sum_{i\in I_j}c_i s_i$ |
| $L_B$, $m_B$, $m_D$ | total outer input length; $B$-slice width; full unsliced $D$ width |
| $S_B$, $I_{B,s}$, $\Pi_B(B,S_B)$ | frozen $B$-slice count; canonical block range of slice $s$; shorthand $(I_{B,s})_{s\in[S_B]}$ |
| $n_\bullet, m_\bullet$ | row count (module rank) / column count for matrix $\bullet$ |
| $L_F, L_H\in\{0,2\}$ | number of compression stages (both or none) |
| $P$ | number of polynomial vectors bound by one commitment handle |
| $\mathrm{Src}$, $\mathrm{shape}_{com}$ | frozen source layout; commitment shape $(\mathrm{Src}; M,b,b_1; (d_A,n_A);(d_B,n_B,S_B);\mathcal{F})$ |
| $\mathrm{cfg}_j=(\mathrm{Open}_j,\mathrm{RingCheck}_j,\mathrm{Comp}_j,\mathrm{Norm}_j)$ | fold configuration (opening method, ring-reduction route, compression profile, norm certificate) |
| $\mathrm{edge}_j$ | outgoing edge tag ∈ {Direct, OffloadedSetup, TerminalInnerState} |
| $\mathcal{O}_j$, $\mathcal{A}_{0,j}$, $\mathcal{W}_j$ | opening shape at fold $j$; root source groups; recursive-witness group |
| $\mathcal{H}_{FS}, \mathcal{H}_{setup}$ | RO restrictions to Fiat–Shamir / setup-expansion namespaces |
| $\mathrm{OpNormAccept}_\Gamma$ | deterministic fixed-point predicate certifying $\|c\|_{\mathrm{mul},2}\le\Gamma$ |
| $\mathrm{Rel}_{com}, \mathrm{Rel}_{eval}$ | decommitment relation; evaluation relation (Eq. 57) |
| $Q_A, Q_b$ | product range polynomials over alphabet $\mathcal{A}$ / $\mathcal{A}_b$ |
| $\widetilde{eq}(\cdot,\cdot)$ | multilinear equality polynomial |
| $\mathrm{MSIS}_{q,d}(n,m,\beta)$ | Module-SIS: given uniform $M\in R_q^{n\times m}$ find $0\ne z\in R_q^m$, $Mz=0$, $\|z\|_{p,coef}\le\beta$ |
| $N_{tensor}$ | number of claims in a shared tensor-reduction batch |
| $\eta$, $\zeta_{a,i}$ | row-batching point; normalized claim-batching tensor coefficients |
| $\theta_a$ | transparent tensor factor $\prod_{t=m_a}^{m_{max}-1}(1-\rho_t)^{-1} A_{\eta,a}(\rho_a)$ |
| $\kappa$ | tensor-reduction extension half-degree; $\mathbb{E}=\mathbb{F}_{q^{2\kappa}}$ in §3.7 |
| $m_a:=\ell_a-\kappa$, $m_{max}$ | tail arity per group; max over groups |
| NSS | $\prod_i(\ell_i(k_i-1)+1)$ — special-soundness tree size |

## 3. Algebraic Setting

### 3.1 Rings, fields, modulus

- Base field $\mathbb{K}=\mathbb{F}_q$, $q$ an odd prime. Opening/evaluation field
  $\mathbb{E}=\mathbb{F}_{q^k}$ with $k\in\{1,2,4\}$ (paper's concrete profiles use
  $\mathbb{F}_{q}$ with $q$ of 32, 64, or 128 bits, and $k=4$ extension for the
  evaluation claims; commitment always uses base-field coefficients — "the $P=1$
  interface").
- Cyclotomic ring $R_q := \mathbb{Z}_q[X]/(X^d+1)$, $d$ a power of two.
- **Partial splitting** (Eq. 42): if $s_{split}$ is a power of two with
  $1<s_{split}\le d$ and $q\equiv 2^{s_{split}}+1 \pmod{2^{s_{split}+1}}$, then
  $X^d+1\equiv\prod_{j=1}^{s_{split}}(X^{d/s_{split}}-r_j)\pmod q$ for distinct
  $r_j\in\mathbb{Z}_q^\times$; $R_q\simeq\prod_j \mathbb{F}_{q^{d/s_{split}}}$.
  Minimal splitting $s_{split}=2$ (i.e. $q\equiv 5\bmod 8$) is what most prior work
  (LaBRADOR, Greyhound, Hachi) uses; larger $s_{split}$ permits faster NTT arithmetic
  at the cost of a tighter invertibility threshold.
- **Invertibility (LS18)**: when $X^d+1$ splits into $s_{split}$ factors, every nonzero
  $c\in R_q$ with $\|c\|_\infty < q^{1/s_{split}}/\sqrt{s_{split}}$ is invertible; for
  $s_{split}=2$: $\|c\|_\infty<q^{1/2}/\sqrt2$.
- **Extension-field embedding**: for $k\mid d/s_{split}$, $\mathbb{F}_{q^k}$ embeds in
  $R_q$ as the subring fixed by a Galois subgroup $H$. Minimal splitting:
  $H=\langle\sigma_{-1},\sigma_{4^k+1}\rangle$; explicit bijection
  $\psi:(\mathbb{F}_{q^k})^{d/k}\to R_q$ with
  $\mathrm{Tr}_H(\psi(a)\cdot\sigma_{-1}(\psi(b)))=(d/k)\langle a,b\rangle$
  (Hachi Theorem 2; generalizes LNP22).
- **Ring-subfield coordinates** ($s_{split}=2$): $m:=d/(2k)$;
  $e_j := X^{jm}+X^{-jm} = X^{jm}-X^{d-jm}$, $j\in[1,k)$; $\{1,e_1,\dots,e_{k-1}\}$
  is an $\mathbb{F}_q$-basis of the fixed subfield. The packing map (Eq. 45):
  $\psi(a,b)=\sum_{t=0}^{m-1}X^t(a_t+X^{d/2}b_t)$ with
  $a_t=\sum_{j=0}^{k-1}a_{t,j}e_j$; packed coefficients (Eq. 46):
  $c_t=a_{t,0}$, $c_{t+d/2}=b_{t,0}$,
  $c_{t+jm}=a_{t,j}+b_{t,k-j}$, $c_{t+d-jm}=-a_{t,j}+b_{t,k-j}$ ($1\le j<k$).
  Two banks overlap: $\ell_\infty$ norm grows by $\le\sqrt2$... (paper: coefficient
  $\ell_\infty$ can increase by factor $\sqrt 2$; $\ell_1$ by $\le 2$; $\ell_2$ by
  $\le\sqrt2$ since $(A+B)^2+(-A+B)^2=2(A^2+B^2)$). These are *logical-to-ring
  conversion factors* applied only when a bound is stated before $\psi$.
- **$k=1$ degeneration**: $\psi$ is ordinary coefficient packing
  $\psi(a_0,\dots,a_{d-1})=\sum a_iX^i$; trace identity is scaled constant-term
  extraction: constant coefficient of $A\sigma_{-1}(B)$ is $\sum_i a_ib_i$.
- **Norms**: centered representatives in $(-q/2,q/2]$; for
  $v\in R_q^m$ norms concatenate all $md$ coefficients. $\|\cdot\|_{\mathrm{mul},2}$
  spectral norms via unitary diagonalization at $\zeta_k=e^{(2k+1)\pi i/d}$:
  $\|a\|_{\mathrm{mul},2}=\max_k|a(\zeta_k)|$,
  $\|v\|_{\mathrm{mul},2}=\max_k(\sum_j|v_j(\zeta_k)|^2)^{1/2}$.
- **Lemma 3.1 (coefficient-product inequalities)**: for $a\in R_q$, $v\in R_q^m$:
  $\|av\|_\infty\le\|a\|_1\|v\|_\infty$;
  $\|av\|_2\le\min\{\|a\|_1\|v\|_2,\ \|a\|_{\mathrm{mul},2}\|v\|_2,\ \|a\|_2\|v\|_{\mathrm{mul},2}\}$.
  These are the only three valid challenge-response pairings for Module-SIS binding.

### 3.2 Challenge subrings and sparse challenges

- **Direct coefficient packing rings** (§3.1 end): with $d=khd_{car}$:
  $S=\mathbb{F}_q[Y]/(Y^{d_{car}}+1)$ (challenge subring),
  $S_E=\mathbb{E}[Y]/(Y^{d_{car}}+1)$ (carrier ring), $R=\mathbb{F}_q[X]/(X^d+1)$ ($A$ ring).
  Canonical embedding $\iota:S\hookrightarrow R$, $Y\mapsto X^{kh}$ (Eq. 47); $R$ is a free
  $S$-module of rank $kh$: $R=\bigoplus_{a=0}^{kh-1}X^a\iota(S)$ (Eq. 48).
- **Lemma 3.2**: $\iota$ preserves units, all coefficient norms
  ($\|\iota(c)\|_p=\|c\|_p$, $p\in\{1,2,\infty\}$) and the multiplication operator norm
  ($\|\iota(c)\|_{\mathrm{mul},2,R}=\|c\|_{\mathrm{mul},2,S}$). Also holds after scalar
  extension $S\to S_E$.
- **Sparse folding challenges** (§3.2): family $\mathcal{C}\subset R_q$ fixed by $(d,(n_a)_{a\in\mathcal{A}})$:
  1. uniform $s$-subset $S\subseteq\{0,\dots,d-1\}$;
  2. uniform partition into blocks $S_a$ with $|S_a|=n_a$;
  3. $c_j=\varepsilon_j a$ for $j\in S_a$, $\varepsilon_j\in\{\pm1\}$; else $c_j=0$.
  Every member: $\|c\|_\infty=c_{max}$, $\|c\|_1=\omega$.
  $|\mathcal{C}|=2^s\binom ds\binom{s}{n_a:a\in\mathcal{A}}$ (multinomial; $=2^s\binom ds$ when $|\mathcal{A}|=1$).
  Differences: $\|\bar c\|_1\le2\omega$; invertible when $2c_{max}<q^{1/s_{split}}/\sqrt{s_{split}}$.
- CWSS error of a fold with $W$ coordinates is $W/|\mathcal{C}^{acc}|$; Fiat–Shamir
  multiplies total interactive error by $(Q+1)$ (§3.8). A raw 128-bit family does not
  by itself give a 128-bit schedule.
- **Operator-norm filtered family** (Eq. 49): $\mathcal{C}^{acc}_\Gamma=\{c\in\mathcal{C}_0:\mathrm{OpNormAccept}_\Gamma(c)=1\}$,
  deterministic, witness-independent, certified sandwich between a smaller true-norm ball
  and $\{c:\|c\|_{\mathrm{mul},2}\le\Gamma\}$ (Theorem D.1). Soundness charged against
  certified lower bound on $|\mathcal{C}^{acc}_\Gamma|$; replaces
  $\|c\|_{\mathrm{mul},2}\le\|c\|_1$ by $\Gamma$.
- **Sampling**: partial Fisher–Yates shuffles + rejection sampling for uniform integers,
  $s$ sign bits; in the noninteractive protocol draws come from a domain-separated XOF
  stream (variable bit count; byte-level procedure in the "Akita Book" [61]).

### 3.3 Gadget decomposition and Module-SIS

- Base $b=2^\ell>1$; $\delta:=\lceil\log_b q\rceil$;
  $G_{b,n}:=I_n\otimes(1\ b\ \cdots\ b^{\delta-1})\in R_q^{n\times n\delta}$;
  $G_{b,n}\cdot s=\sum_{i=0}^{\delta-1}b^is_i$. $G^{-1}_{b,n}:R_q^n\to R_q^{n\delta}$
  is a chosen right inverse producing **balanced** digits in
  $\mathcal{D}_b=\{-b/2,\dots,b/2-1\}$.
- Balanced digits reduce the digit $\ell_\infty$ bound from $b-1$ to $b/2$ and worst-case
  squared $\ell_2$ from $k(b-1)^2$ to $k(b/2)^2$.
- Exact representable range with $k$ digits:
  $T_k=\frac b2\left(\frac{b^k-1}{b-1}\right)$ (largest positive),
  $M_k=\frac b2\cdot\frac{b^k-1}{b-1}$ (largest negative magnitude);
  $[-M_k,T_k]$ contains exactly $b^k$ integers.
- Canonical residue lift for full-field decomposition: with
  $T:=\min(T_k,\lfloor q/2\rfloor)$, $\tilde x=x$ if $x\le T$ else $x-q$; guarantees
  $\tilde x\in[-M_k,T_k]$ (no extra digit).
- Different components may use different bases: $b$ = commitment base,
  $b_1$ = opening base; $\delta_{com}=\lceil\log_b q\rceil$,
  $\delta_{open}=\lceil\log_{b_1} q\rceil$. Negative-binary digits
  $\{-1,0\}$ (base 2) are used for compression chains.
- **Definition 3.6 (Module-SIS)**: for $p\in\{2,\infty\}$ and bound $\beta>0$,
  $\mathrm{MSIS}^{(p)}_{q,d}(n,m,\beta)$: given uniform $M\in R_q^{n\times m}$, find
  nonzero $z\in R_q^m$ with $Mz=0$ and $\|z\|_{p,coef}\le\beta$. Unadorned
  $\mathrm{MSIS}_{q,d}$ = coefficient-$\ell_\infty$ problem. Akita uses the
  $\ell_\infty$ problem for digit-alphabet collisions; the Euclidean problem may price
  inner-commitment collisions when the verifier certifies the response norm.

### 3.4 Multilinear extensions, sum-check, equality-factored sum-check

- MLE: $\tilde f(X)=\sum_{i\in\{0,1\}^\mu}f(i)\widetilde{eq}(i,X)$;
  $\widetilde{eq}(i,X)=\prod_j((1-i_j)(1-X_j)+i_jX_j)$.
- **Theorem 3.7 (sum-check soundness)**: interactive soundness $\mu\ell/|\mathbb{F}|$;
  $(\ell+1)$-special soundness per round (interpolation identifies the round polynomial).
- **Compressed sum-check (Figure 2)**: round message omits the *linear* coefficient;
  verifier recovers $s_{j,1}=T_j-2s_{j,0}-\sum_{i\ge2}s_{j,i}$ from running claim
  $T_j=s_j(0)+s_j(1)$. Final check $g(r_1,\dots,r_\mu)=T_{\mu+1}$.
- **Batching unequal arities**: order-preserving injections
  $\pi_i:\{1..\mu_i\}\hookrightarrow\{1..M\}$, $\mu_t=M$; extend
  $\hat g_i(x)=g_i(x_{\pi_i(1)},\dots)$; $\sum_{x\in\{0,1\}^M}\hat g_i=2^{M-\mu_i}T^{(i)}$;
  batched claim $\sum_i\gamma_i2^{M-\mu_i}T^{(i)}=\sum_x\sum_i\gamma_i\hat g_i(x)$.
  Inactive rounds contribute constant round polynomial $s_j^{(i)}(X)=C_j^{(i)}/2$.
  The implementation uses the **suffix embedding** $\pi_i(k)=M-\mu_i+k$.
- **Equality-factored sum-check (§3.5, [46,33])**: for
  $T=\sum_x\widetilde{eq}(\tau,x)p(x)$ with $\deg p\le\ell-1$ per variable: normalize the
  running claim by stripping equality factors; round message omits the *constant*
  coefficient $q_{j,0}=T_j-\tau_j\sum_{i\ge1}q_{j,i}$ — inversion-free, one fewer
  coefficient than the linear-omission format. Prover caches equality weights for the
  two halves of $\tau$ (~$2\mu/2$ values/half). Only applies when the whole round
  message shares one common equality factor (range-tree stages without fused norm term;
  NOT the fused relation sum-check).

### 3.5 Quotient-lift ring switching (HMZ / Hachi)

- **Lemma 3.8 (ring-switch lift)**: $Mw=h$ in $R_q^{n}$ ⟺ exists unique
  $r\in(\mathbb{Z}_q^{<d-1}[X])^n$ with $\tilde M\tilde w=\tilde h+(X^d+1)r$ in
  $\mathbb{Z}_q[X]^n$; $\deg r\le d-2$ (since $\deg(\tilde M\tilde w-\tilde h)\le 2d-2$).
- Evaluate at random $\alpha\in\mathbb{F}_{q^k}$ (Eq. 51):
  $M(\alpha)w(\alpha)=h(\alpha)+(\alpha^d+1)r(\alpha)$. Soundness (Schwartz–Zippel):
  false relation passes at probability $\le(2d-1)/q^k$.
- **Partial-evaluation view**: $w(x,y)$ = MLE of coefficient layout ($x$ selects ring
  coordinate, $y\in\{0,1\}^{\log d}$ selects coefficient);
  $\tilde\alpha(y)=\prod_{j=0}^{\log d-1}(1+y_j(\alpha^2-1))$ (Eq. 52);
  $w_x(\alpha)=\sum_y w(x,y)\tilde\alpha(y)$ (Eq. 53) — "evaluate at $X=\alpha$" is a
  partial evaluation against fixed weight $\tilde\alpha$, coefficient variables unbound.
- **Lemma 3.9 (mixed-dimension ring switch)**: row blocks $b=1..K$ with dimensions
  $d_b$; per-block identity (Eq. 54)
  $M^{(b)}(\alpha)w^{(b)}(\alpha)=h^{(b)}(\alpha)+(\alpha^{d_b}+1)r^{(b)}(\alpha)$.
  Completeness for every $\alpha$; soundness: fail ⇒ holds for $\le 2d_{max}-1$ values
  of $\alpha$, i.e. $2d_{max}$-special sound in $\alpha$, error $\le(2d_{max}-1)/q^k$.
  All truncated weights are prefixes of one tensor — verifier computes a single power
  ladder $\{\alpha^{2^j}\}_{j<\log d_{max}}$ and each block uses its length-$\log d_b$
  prefix.
- **One sum-check for all ring dimensions**: append all quotient coefficients to the
  committed coefficient vector before sampling $\alpha$; per block use augmented matrix
  $[M^{(b)}(\alpha)\mid-(\alpha^{d_b}+1)I]$ placed in prescribed witness/quotient slices
  with zeros elsewhere; random-coefficient batching → one sum-check over the common
  augmented MLE.
- **Remark 3.10**: ring dimension is a *per-row-block choice*; $d_b$ enters only through
  a public weight and degree bound; the commitment to the flat $\mathbb{Z}_q$ coefficient
  vector is unchanged.

### 3.6 Tensor reduction to the extension field (Diamond–Posen, §3.7)

- Purpose: reduce an evaluation claim on a base-field multilinear polynomial at an
  extension-field point to a single evaluation claim on a packed extension-field
  polynomial with $\kappa$ fewer variables. Extension degree $2\kappa$; deterministic
  $\mathbb{F}_q$-basis $(\beta_y)_{y\in\{0,1\}^\kappa}$ of $\mathbb{F}_{q^{2\kappa}}$;
  split $\ell$ variables into $\kappa$ head + $\ell-\kappa$ tail;
  $g(X_{tail}):=\sum_y f(y,X_{tail})\beta_y$.
- **Column partials**: $S_y=f(y,r_{tail})$; verifier checks
  $v=\sum_y\widetilde{eq}(y,r_{head})S_y$ (multilinear recombination over head — this is
  what prevents the insecure shortcut $\sum_y\beta_yS_y$).
- **Row partials** in tensor algebra $\mathbb{F}_{q^{2\kappa}}\otimes_{\mathbb{F}_q}\mathbb{F}_{q^{2\kappa}}$
  ($2^\kappa\times2^\kappa$ matrices over $\mathbb{F}_q$):
  $S_y=\sum_uS_{u,y}\beta_u$; $\mathrm{row}_u=\sum_yS_{u,y}\beta_y$;
  honest: $\mathrm{row}_u=\sum_wA_u(w)g(w)$ where $A_u(w)$ are coordinates of the tail
  equality factor $\widetilde{eq}(r_{tail},w)$.
- **Tensor-reduction sum-check**: batch rows with $\eta\in\mathbb{F}_{q^{2\kappa}}^\kappa$,
  $\eta_u=\widetilde{eq}(u,\eta)$: $c_\eta=\sum_u\eta_u\mathrm{row}_u$,
  $A_\eta(w)=\sum_u\eta_uA_u(w)$; run degree-2 sum-check on $A_\eta(w)g(w)$ over
  $\ell-\kappa$ variables → point $\rho$, value $\mathrm{final}=A_\eta(\rho)g(\rho)$.
  $A_\eta(\rho)$ transparent: rows of $\widetilde{eq}:=\widetilde{eq}(\phi_0(r_{tail}),\phi_1(\rho))$
  in the tensor algebra with $\phi_0(\alpha)=\alpha\otimes1$, $\phi_1(\alpha)=1\otimes\alpha$;
  $A_\eta(\rho)=\sum_u\eta_ue_u$ in $O(\ell-\kappa)$ tensor ops. **Verifier rejects if
  $A_\eta(\rho)=0$** (necessary; schedule charges honest abort probability, no resample).
- Honest abort $\le\ell/|\mathbb{F}_{q^{2\kappa}}|$; soundness for false input
  $\le(\kappa+2(\ell-\kappa))/|\mathbb{F}_{q^{2\kappa}}|$.
- **Batching across groups** (different points/arities): cylindrical extensions
  $\bar g_{a,i}(w,z)=g_{a,i}(w)$, $\bar A_{\eta,a}(w,z)=A_{\eta,a}(w)\widetilde{eq}(0,z)$;
  shared row-batching $\eta$ + normalized claim-batching coefficients
  $(\zeta_{a,i})$ (first is 1, rest uniform); one $m_{max}$-round degree-2 sum-check of
  $\sum_{a,i}\zeta_{a,i}\bar g_{a,i}(x)\bar A_{\eta,a}(x)$ (Eq. 55);
  $\theta_a:=A_{\eta,a}(\rho_a)\prod_{t=m_a}^{m_{max}-1}(1-\rho_t)^{-1}$; prover sends
  $h_{a,i}:=\theta_ag_{a,i}(\rho_a)$ per claim; verifier checks final value equals
  $\sum\zeta_{a,i}h_{a,i}$ and rejects if any $\theta_a=0$.
- **Theorem 3.11 (shared tensor-reduction soundness)**: if ≥1 input claim false,
  all checks pass + all forwarded packed claims correct with probability
  $\le(\kappa+\mathbf{1}_{N_{tensor}>1}+2m_{max})/|\mathbb{E}|$. Extraction: nested
  binary tree in the $\kappa$ coordinates of $\eta$ (factor $2^\kappa$); claim batching
  factor $(N_{tensor}-1)/|\mathbb{E}|$ (Eq. 56). Honest abort (some $\theta_a=0$):
  $\le G(\kappa+m_{max})/|\mathbb{E}|$. Identity reduction (k=1): all challenges and
  errors vanish.

### 3.7 Coordinate-wise special soundness (CWSS) — §3.8

- PCS interface (Def. 3.12): Setup, Commit(pp, shape, f)→(cm,st) with
  cm=(shape, C), Eval.P, Eval.V; decommitment relation $\mathrm{Rel}_{com}$;
  evaluation relation $\mathrm{Rel}_{eval}$ (Eq. 57):
  $\mathrm{Rel}_{eval}=1\iff\mathrm{Rel}_{com}=1\wedge\tilde f(r)=v$.
- Def. 3.13/3.14/3.15: completeness error, binding, knowledge soundness with
  resettable black-box extractor (adaptive, same-execution knowledge experiment).
- Def. 3.16/3.17 (special-sound structure / CWSS protocol):
  $NSS=\prod_i(\ell_i(k_i-1)+1)$ trees of accepting transcripts; deterministic
  poly-time extractor from any prefix-consistent member tree.
- Def. 3.18 nested interpolation tree (branch on coordinates in order; $2^a$ leaves for
  binary arities); Lemma 3.19: multilinear residual vanishing on all leaves ⇒ zero.
- **Theorem 3.20 (CWSS→knowledge; classical FS)**: $\ell$-coordinate-wise $k$-special
  sound ⟹ knowledge error $\kappa_{CWSS}=\mu\ell(k-1)/|X|$; extractor runs prover
  $(\ell(k-1)+1)^\mu$ times in expectation. Fiat–Shamir: knowledge error
  $\kappa_{FS\text{-}CWSS}(Q)=(Q+1)\cdot\mu\ell(k-1)/|X|$ vs classical $Q$-query RO
  adversary. **Not a QROM theorem.**
- Corollary 3.21 (heterogeneous coordinates): error
  $\sum_i\sum_{u\in U_i}(k_{i,u}-1)/|X_{i,u}|$, tree size
  $\prod_i(1+\sum_u(k_{i,u}-1))$; FS multiplies error by $Q+1$.
- Lemma 3.22 (mixed transcript trees): flat stages contribute
  $e_r=\sum_u(k_{r,u}-1)/|S_{r,u}|$, branching $b_r=1+\sum_u(k_{r,u}-1)$; nested stages
  $e_r=\sum_u(k_{r,u}-1)/|S_{r,u}|$, $b_r=\prod_uk_{r,u}$; interactive error
  $\le\sum_re_r$; RO error $\le(Q+1)\sum_re_r$ provided conditional-prefix sampling is
  expected poly-time; FS input includes injective encoding of stage + complete
  preceding transcript. Cost polynomial in $Q$ and $\prod_rb_r$.

*(Sections 4–9 of the paper: setup, commitments, the fold, norm checks, ring checks,
verifier offloading — transcribed below.)*

## 4. Relations (exact definitions)

Akita's fold checks are expressed as one *common relation* over the recursive witness. The
paper gives the canonical relation in **Figure 6**; each family is listed below in the
canonical order (families 1–6; within a family: increasing group, slice, matrix-row index;
$\sum c,i$ abbreviates $\sum_{c\in[n_{clm,g}]}\sum_{i\in[B_g]}$):

1. **Fold evaluation** (one row per group).
   - Coefficient packing (carrier ring, Eq. 138):
     $\sum_{c,i} c_{g,c,i}(Y)\,e_{g,c,i}(Y) = \mathcal{L}_g(G_{b_g,M_g}z_g)(Y)$ in $\mathbb{E}[Y]/(Y^{d_{car,g}}+1)$.
   - Evaluation trace (full ring, Eq. 139):
     $\sum_{c,i} c_{g,c,i}(X)\,e_{g,c,i}(X) = a_g^\top G_{b_g,M_g}z_g(X)$ in $R_{q,d_{A,g}}$.
   A carrier row has $k$ base-field coordinate planes; native modulus stays $Y^{d_{car,g}}+1$.
2. **Inner consistency** ($n_{A,g}$ rows per group, Eq. 140):
   $\sum_{c,i} c^A_{g,c,i}\,t_{g,c,i} = A_g z_g$ in $R_{q,d_{A,g}}$,
   where $c^A_{g,c,i}=\iota_g(c_{g,c,i})$ (packing) or $c_{g,c,i}$ (trace).
3. **Outer consistency** (one matrix equation per group and slice, Eq. 141):
   $B_g x_{B,g,s} = u_{g,s}$, $g\in[G]$, $s\in[S_{B,g}]$; complete image
   $u_g=\|_s u_{g,s}$ is raw payload or recomposition of $\hat u_{g,1}$. Every slice reuses the same matrix $B_g$.
4. **Shared opening consistency** (one matrix equation, Eq. 142):
   $D\,\mathrm{concat}(\hat e_0,\dots,\hat e_{G-1}) = v$ (raw payload or recomposition of $\hat v_1$; unsliced, exact summed width).
5. **Compression chains** (increasing depth): rows of Eq. (76):
   $M\hat x = G_{\mathcal{A}_1,\cdot}\hat\xi_1$; $K_j\hat\xi_j = G_{\mathcal{A}_{j+1},\cdot}\hat\xi_{j+1}$ ($1\le j<L$);
   $K_L\hat\xi_L = p$, with $L=2$, $\mathcal{A}_1=\mathcal{A}_2=\{-1,0\}$. At $L=0$: $M\hat x=p$ (Eq. 77).
   - $F$-chain substitution: $(M,K_j,\hat x,\hat\xi_j,p) = (B\Pi_B(B,S_B), F_j, \hat t, \hat u_j, u_{pub})$.
   - $H$-chain substitution: $(M,K_j,\hat x,\hat\xi_j,p) = (D, H_j, \hat e, \hat v_j, v_{pub})$.
   Families 3–4 supply the first row of each chain; at each remaining depth all group-local $F$
   rows precede shared $H$ rows. Final rows have public targets $u_{pub,g}, v_{pub}$.
6. **One scalar opening row** (E-linear, no quotient): Eq. (136) (packing) or Eq. (137) (trace).

**Common normal form for ring rows (§7.3).** Let $\mathrm{Rows}_{ring}$ be the ordered active
ring-valued rows; row $r$ has native dimension $d_r$, coefficient field $\mathbb{K}_r\subseteq\mathbb{E}$
($\mathbb{K}_r=\mathbb{K}$ for ordinary A/B/D/F/H rows; $\mathbb{E}$ for the carrier row,
represented by its fixed $\mathbb{F}_q$-basis planes), ring $R_r=\mathbb{K}_r[X]/(X^{d_r}+1)$,
$d_{max}:=\max_{r}d_r$ (Eq. 143). With $N_w=|w'|$ the outgoing witness, occurrence set
$\mathrm{Occ}_r$, address map $\mathrm{addr}_{r,c}:[d_r]\to[N_w]$ (Eq. 144) and public
multiplier $A_{r,c}(X)\in R_r$ (gadget powers, folding challenges, row signs, projection
weights; $\beta_t$ basis elements for the carrier row):

- witness polynomial: $W_{r,c}(X):=\sum_{j=0}^{d_r-1}w_{\mathrm{addr}_{r,c}(j)}X^j\in R_r$ (Eq. 145);
- ring residual: $Z_r(X):=\sum_{c\in\mathrm{Occ}_r}A_{r,c}(X)\circledast^{d_r}W_{r,c}(X)-Y_r(X)=0$ in $R_r$ (Eq. 146),
  where $\circledast^d$ is negacyclic multiplication mod $X^d+1$ and $Y_r$ is public.

**Row dimensions by family:** fold-evaluation: $d_{car,g}$ (packing) / $d_{A,g}$ (trace);
inner consistency: $d_{A,g}$; sliced outer: $d_{B,g}$; opening consistency: $d_D$; compression
rows: dimension of their own $F_j$ or $H_j$ map.

**Digit range relation** (per Boolean point $x$, common alphabet
$\mathcal{A}_{b^\star}=\{-b^\star/2,\dots,b^\star/2-1\}$):
$Q_{b^\star}(w(x))=\prod_{a\in\mathcal{A}_{b^\star}}(w(x)-a)=0$; halved:
$Q_{b^\star}(w)=Q^{sq}(w(w+1))$ with $Q^{sq}(s)=\prod_{k=0}^{b^\star/2-1}(s-k(k+1))$ (Eq. 114);
anchored identity $\sum_{x\in\{0,1\}^{\mu'}}\widetilde{eq}(\tau_0,x)\,Q^{sq}(s(x))=0$ (Eq. 115).

**Response norm relations** (Euclidean route, Eqs. 117–118):
$E_{int}(\hat z):=\sum_{u=0}^{N_A-1}(z^{\mathbb{Z}}_u)^2$ where
$z^{\mathbb{Z}}_u=\sum_{h=0}^{\delta_f-1}b^h\,w^{(j+1)}(\pi(u,h))$ (Eq. 116);
statement $E_{int}(\hat z)=E_{resp}$ and $E_{resp}\le S_{max}$. Direct route admissible only when
$\max\{U^{dir},S_{max}\}<q$ with $U^{dir}:=N_A(\sum_{h}b^hB_{dig,h})^2$ (Eq. 119).

**Setup-product relation** (Eq. 167/168): $\sigma_S=\sum_{p<2^{\nu_S}}S^\flat(p)\,\omega_{setup}(p)$,
checked by a degree-2 sum-check over $\{0,1\}^{\nu_S}$.

**PCS relations** (Def. 3.12/3.15): $\mathrm{Rel}_{com}$ (decommitment) and
$\mathrm{Rel}_{eval}$: $\mathrm{Rel}_{eval}(\mathrm{pp},\mathrm{cm},r,v;f,st)=1\iff
\mathrm{Rel}_{com}(\mathrm{pp},\mathrm{cm},f,st)=1\wedge\tilde f(r)=v$.

## 5. Protocols — full step-by-step transcription

### 5.1 Setup (§4.3) and matrix layout

1. Fix an admissible schedule (Def. 9.2) for $(1^\lambda,\mu_{max})$.
2. Choose $N_{view}:=\max\{n_I m_I d_I : I$ a matrix instance in an admitted schedule with
   $\mu\le\mu_{max}\}$; provision $N_{setup}:=2^{\lceil\log_2 N_{view}\rceil}$ (Eq. 65).
3. Expand the public 256-bit seed via domain-separated XOF:
   $S_i:=\mathrm{XOF}_q(\mathrm{seed};\text{setup},i)$ (Eq. 67). Prefix-consistent; each
   coefficient within statistical distance $q2^{-w}$ of uniform, draw width
   $w\ge\lceil\log_2N_{setup}+\log_2 q+\log_2(1/\delta_{setup})\rceil$ (exact rejection sampling has zero bias).
4. Matrix instance $M\in R_{q,d}^{n\times m}$ (Eq. 66):
   $M[i,j]:=\sum_{\ell=0}^{d-1}S_{(im+j)d+\ell}X^\ell$ — first $nmd$ entries of $S$, row-major,
   ring coefficients consecutive. $A^{(j)},B^{(j)},D^{(j)},F_i^{(j)},H_i^{(j)}$ are all
   overlapping prefix views of $S$ at their own $(n,m,d)$ (Figure 3).
5. Populate the verifier's setup-prefix registry with the exact commitment $C_{S,h}$ for every
   scheduled offloaded edge (each is a commitment to the canonical padded prefix vector
   $S^\flat$, fixed by the schedule's registry slot).

**Matrix cost formulas** (Eq. 68): with $L_I$ input coefficients, output $T_I=n_Id_I$:
$m_I=L_I/d_I$, setup size $n_Im_Id_I=L_IT_I/d_I$, ring products $n_Im_I=L_IT_I/d_I^2$. Larger
rings shrink storage and product count. Rank-one ($n_I=1$): matrix contains exactly as many
field coefficients as its padded input.

**Ring-dimension compatibility:** packing candidate selects $d_{car}$ + audited challenge
family; then $d_A$ with $kd_{car}\mid d_A$, $h=d_A/(kd_{car})$. $B$/$D$ dimensions free of
challenge floor: $d_B\mid d_A$ required (B source $\hat t$ is a flat $A$-ring coefficient
vector); $d_D\mid d_A$ (trace) or $d_D\mid kd_{car}$ (packing); no condition $d_D\mid d_B$.

### 5.2 Commitment algorithm (§4.5, Figure 4 — "commitment pipeline")

Input: shape $\mathrm{shape}_{com}=(\mathrm{Src};M,b,b_1;(d_A,n_A);(d_B,n_B,S_B);\mathcal{F})$
and ordered vectors $(f_p)_{p\in[P]}$ ($P=1$ for the base PCS interface):

1. **Embed into $R_{q,d_A}$**: pack each run of $d_A$ consecutive base-field coefficients
   (ring-subfield basis of §3.1) into one ring element → ring-packed vector
   $f\in R_{q,d_A}^N$, $N=\lceil\text{len}/d_A\rceil$.
2. **Reshape to blocks**: $B=\lceil N/M\rceil$ blocks of $M=2^{r_{pos}}$ ring elements;
   $f_i[x]=f[iM+x]$ if $iM+x<N$ else $0$ (Eq. 70; canonical zero extension). Block index uses
   $r_{blk}=\lceil\log_2B\rceil$ MLE variables; equality factor splits:
   $\widetilde{eq}(r,iM+x)=\widetilde{eq}(r_{pos},x)\widetilde{eq}(r_{blk},i)$ (Eq. 71).
3. **Decompose**: full-field source: $s_i:=G^{-1}_{b,M}(f_i)$ (balanced base-$b$ digits,
   depth $\delta_{com}=\lceil\log_bq\rceil$). Bounded source (recursive digits or one-hot):
   identity source map $s_i:=f_i$, $\delta_{com}=1$, $G_{b,M}=I_M$; packed-coefficient bound
   = envelope of packed ring coefficients (may exceed the logical alphabet due to Eq. 46).
   In both cases $G_{b,M}s_i=f_i$.
4. **Inner commitment** (A at $d_A$): $t_i:=As_i\in R_{q,d_A}^{n_A}$;
   $\hat t_i:=G^{-1}_{b_1,n_A}(t_i)$ (balanced base-$b_1$, depth $\delta_{open}=\lceil\log_{b_1}q\rceil$).
5. **Slice + outer commitment** (B at $d_B$): frozen power-of-two slice count $S_B\le B$,
   canonical ranges $I_{B,s}:=[\lfloor sB/S_B\rfloor,\lfloor(s+1)B/S_B\rfloor)$ (Eq. 72).
   Per block of one polynomial: $g_B:=\frac{n_A\delta_{open}d_A}{dB}$ elements of $R_{q,d_B}$.
   Reindex $\hat t_{p,i}$ into the $R_{q,d_B}$ view (address change
   $(a\delta+u)d_A+yd_B+k\mapsto((as+y)\delta+u)dB+k$, $a$=A row, $y\in[d_A/d_B]$ subcolumn,
   $u\in[\delta]$ digit, $k\in[d_B]$ coefficient).
   $L_B^{blk}:=B/S_B$, $m_B:=PL_B^{blk}g_B$;
   slice input $x_{B,s}:=(\hat t_{p,i}\ \| \ 0^{(L_B^{blk}-|I_{B,s}|)g_B})_{p\in[P],i\in I_{B,s}}\in R_{q,d_B}^{m_B}$ (Eq. 73;
   padding inside each polynomial segment).
   Compute $u_s:=Bx_{B,s}\in R_{q,d_B}^{n_B}$ for each $s$; complete outer image
   $u:=(u_0\|\cdots\|u_{S_B-1}) =: B\Pi_B(B,S_B)\hat t$ (Eq. 74; logical block-diagonal map, NOT
   $S_B$ independent matrices). Coordinate order: slice, B row, ring coefficient (coefficient first).
6. **Optional F-chain compression** ($L_F\in\{0,2\}$): both stages use negative-binary alphabet
   $\{-1,0\}$; $\delta=\lceil\log_2q\rceil$ digits per coefficient (decompose $-x\bmod q$'s
   binary expansion and negate digits). Digit plane layout: digit $u$ of coefficient $v$ at
   position $v+su$ (least-significant digits of all coefficients first). Stage $j$:
   $\hat u_j:=G^{-1}_{\mathcal{A}_{F,j},\cdot}(\tilde u_{j-1})$, $\tilde u_j:=F_j\hat u_j$
   (Eq. 75 area); only the second image is transmitted; both digit vectors enter the next fold's witness.
7. **Payload**: $u_{pub}:=u$ if $L_F=0$ else $\tilde u_{L_F}$ (Eq. 75). At depth 0: a vector of
   $S_Bn_Bd_B$ field elements (slice/matrix-row/coefficient order); at positive depth:
   $n_{F,L_F}d_{F,L_F}$ field elements. Fixed-width canonical encoding; no shape/length header
   (schedule determines both). **Public commitment** $C:=u_{pub}$; $cm=(\mathrm{shape}_{com},u_{pub})$.

**Compression sizing (Table 5)** — two-stage binary compression for input images ≤ 8 KiB
(module rank 1, coefficient collision bound 1, quantum ADPS16 Core-SVP ≥ 147 bits):

| Modulus $q$ | $d_1$ | $m_1$ (max) | $d_2$ | $m_2$ | intermediate | output |
|---|---|---|---|---|---|---|
| $2^{32}-99$ | 64 | 1024 | 32 | 64 | 256 B | **128 B** |
| $2^{64}-59$ | 32 | 2048 | 16 | 128 | 256 B | **128 B** |
| $2^{128}-2^{33}+2^{2537}$... | 16 | 4096 | 8 | 256 | 256 B | **128 B** |

Input widths: $m_1=\lceil\delta s_0/d_1\rceil$, $m_2=\lceil\delta n_1d_1/d_2\rceil$; choose both
shapes so $\mathrm{MSIS}_{q,d_i}(n_i,m_i,1)$ meets the target; output $n_2d_2\lceil\delta/8\rceil$ bytes.

**Sparse/one-hot commitment**: pay-per-nonzero follows from the identity source map and from
Ajtai linearity — the implementation commits to one-hot inputs with sparse matrix-vector
products (§13); the one-hot shape only sharpens the *honest* response bound (Remark 4.1/4.2:
the guarantee is validated externally by booleanity/hamming-weight sum-checks in the surrounding
proof system, e.g. Jolt; the extractor recovers a polynomial regardless).

### 5.3 One fold for an opening batch (§5, Figure 5 — canonical interaction)

Public input: ordered groups $\mathcal{O}_h$ (commitment handles, points, projections, claimed
values); setup identity + schedule digest fixing source/successor shapes, fold record, edge.

**Step 0 — reduce incoming claims (evaluation-trace folds with $k>1$ only).**
Absorb all tensor column partials $S_y=f(y,r_{tail})$; draw shared row-batching $\eta$ and
claim-batching $(\zeta_{a,i})$ challenges; run the one shared tensor reduction (Theorem 3.11,
absorbing each message before its challenge); bind every $h_{g,c}=\theta_gg_{g,c}(\rho_g)$ and
check every $\theta_g\ne0$. Packing/identity reductions omit this step.

**Step 1 — bind all partial opening evaluations.** Prover forms mode-specific $e_{g,c,i}$:
- *Coefficient packing* (contraction $\mathcal{L}$, Eq. 87):
  $e_i(Y):=\sum_{x\in[M]}\sum_{a\in[kh_{car}]}\sum_{j\in[d_{car}]}\widetilde{eq}(\hat r_{pos},x)\widetilde{eq}(\hat r_{pack},a)\,f_{i,x,a,j}Y^j\in S_E$,
  i.e. $e_i=\mathcal{L}(f_i)$; written $e_i(Y)=\sum_j(\sum_t\beta_te_{i,t,j})Y^j$ (Eq. 88) —
  one partial = exactly $kd_{car}$ committed base-field coordinates (Eq. 82 for the padded claim).
- *Evaluation trace* (Eq. 96): $a_x:=\widetilde{eq}(\rho_{pos},x)\in\mathbb{E}$, $a:=(a_x)$;
  $e_i:=\langle a,f_i\rangle\in R_{q,d_A}$ with $d_A$ base-field coordinates ($d_{op}=d_A$;
  Eq. 97: $d_{op}=kd_{car}$ for packing).
Then decompose base-field coordinates in base $b_1$, concatenate group intervals
$\hat e:=\mathrm{concat}(\hat e_0,\dots,\hat e_{G-1})$, and send the raw shared $D$ image
$v=D\hat e$ or the final H payload $v_{pub}$. **Absorb before any scalar-batching or fold challenge.**

**Step 2 — combine the scalar claims and fold each group.**
- Derive weights $\vartheta$: packing root with $\Lambda=\sum_gn_{clm,g}>1$: sample
  $\zeta_{batch}\leftarrow\mathbb{E}$, $\vartheta_{g(a),c(a)}:=\zeta_{batch}^a$ (Eq. 102);
  offloaded boundary (2 groups): weights $(1,\vartheta_{grp})$, $\vartheta_{grp}\leftarrow\mathbb{E}$;
  singleton direct edge: weight 1. Packing target: $v_{root}:=\sum_{g,c}\vartheta_{g,c}\phi^{\mathrm{pad}}_{g,c}v_{g,c}$ (Eq. 103).
  Trace: first scalar coefficient = 1, other $\Lambda-1$ sampled from $\mathbb{E}$;
  $\bar v_{root}:=\sum\vartheta_{g,c}h_{g,c}$.
- Draw the fold challenges: use a candidate nonce to derive the complete mode-specific tuple
  $(c_{g,c,i})_{g,c,i}$ (each query separately indexed under fixed round root and nonce);
  form every group response $z_g:=\sum_c\sum_ic^A_{g,c,i}s_{g,c,i}$ (Eq. 104; $c^A=\iota(c)$
  for packing, $c$ itself for trace). **Reject the nonce** if a bounded fixed-filter sampler
  fails or a response does not fit its scheduled certificate; a retry resamples the whole tuple;
  verifier enforces the common nonce budget $N_{try,h}$.
- Decompose responses: $\hat z_g:=G^{-1}_{b_{z,g},m_{A,g}}(z_g)$, $z_g=G_{b_{z,g},m_{A,g}}\hat z_g$
  (Eq. 105; requires $b_{z,g}\le b^\star$).

**Step 3 — bind the successor witness.** Assemble Eq. (109):
$w^{(h+1)}:=w^{(h)}_{main}\|Q̂_{main}[\hat c_a|Q̂_a]_{a=1}^{L_{comp}}$ with
$w^{(h)}_{main}:=[\hat z_g|\hat e_g|\hat t_g]_{g\in[G]}$ (Eq. 106) and
$\hat c_a:=\left(\binom{\hat u_{g,a}}{g\in[G]}\right)\|\hat v_a$.
Digit plane addresses: $\mathrm{pos}(j,y,u,k):=(js+y)\delta+ud+k$ (Eq. 107; coefficient first,
then digit, then native block); response digits:
$\mathrm{pos}_{\hat z}(x,u_{com},u_{fold},k):=\delta_f(\delta_{com}x+u_{com})+u_{fold}d_A+k$
(Eq. 108); quotient digits: $\mathrm{pos}_{Q̂_r}(u,t,k):=(up_r+t)d_r+k$ (Eq. 110).
Commit using the successor's frozen shape; absorb payload. At the final nonterminal fold bind
the canonical terminal inner state instead.

**Step 4 — bind any squared-norm claims** (eligible singleton Euclidean route): send and absorb
canonical fixed-width unsigned integer encoding of $E_{resp}$ (verifier rejects noncanonical
encodings / out-of-range values) and, if required, the digit-inner-product claims
$p_{t,h,k}=\sum_{u\in I_t}z_h(u)z_k(u)$ (Eq. 121; segment condition Eq. 122:
$|I_t|B_{dig,h}B_{dig,k}<q/2$). Batching challenges follow these claims and the successor binding.

**Step 5 — check the ranges and relations.** Draw $\alpha$ and later batching challenges in
the order of §6.1/§6.2/§7.4; use the selected ring check on the rows of Figure 6; run one
range pipeline on the complete witness; fuse the optional norm proof into its final stage.
The fused relation sum-check (Eq. 160) authenticates those outputs against the same witness
and leaves one claim $\tilde w^{(h+1)}(r^{(h+1)})=v^{(h+1)}$.

**Step 6 — pass the remaining claims to the next level.** Direct edge → witness opening
$\mathcal{W}_{h+1}$. Offloaded edge → run Stage 3 (setup-product sum-check) then produce
$(\mathcal{S}_h,\mathcal{W}_{h+1})$. Final edge → TerminalInnerState, no setup claim.

### 5.4 Digit range check protocol (§6.1)

Level $j{+}1$ commitment binds $w':=w^{(j+1)}$ indexed by $\{0,1\}^{\mu'}$; certify every
Boolean evaluation in $\mathcal{A}_{b^\star}$, $b^\star\in\{4,8,16,32,64\}$ (schedule-chosen;
contains every balanced digit alphabet used by the witness entries; positional bases are
recomposition-only and separately recorded):

1. **Halve the predicate degree**: pair factors $(w-k)(w+k+1)=w(w+1)-k(k+1)$, $k\in U_{b^\star}=\{0,\dots,b^\star/2-1\}$;
   derived value $s(x):=w(x)(w(x)+1)$; check $Q^{sq}(s(x))=0$ with
   $Q^{sq}(s)=\prod_{k\in U_{b^\star}}(s-k(k+1))$ (degree $b^\star/2$).
2. **Anchored identity** (Eq. 115): $\sum_x\widetilde{eq}(\tau_0,x)Q^{sq}(s(x))=0$ with
   range-anchor challenge $\tau_0$; reduces to claim $s_{claim}=\tilde s(r_{virt})$ where
   $\tilde s(r)=\sum_x\widetilde{eq}(r,x)w(x)(w(x)+1)$ — *multiply at each Boolean index then
   interpolate* (NOT $\tilde w(r)(\tilde w(r)+1)$, which differs off the cube).
3. **Product tree** (only when $b^\star>8$): leaves = $b^\star/2$ factors $s(x)-k(k+1)$;
   internal nodes = products; degree per node 2 or 4 (root may have 2 children, others 4):
   | $b^\star$ | degrees $(d_0..d_{S_{tree}})$ | nodes $(n_0..n_{S_{tree}})$ |
   |---|---|---|
   | 4 | (2, 0) | (1, 2) |
   | 8 | (4, 0) | (1, 4) |
   | 16 | (2, 4, 0) | (1, 2, 8) |
   | 32 | (4, 4, 0) | (1, 4, 16) |
   | 64 | (2, 4, 4, 0) | (1, 2, 8, 32) |
   $S_{tree}$ sequential range sum-checks (one per product level $i=0..S_{tree}-1$), each
   equality-factored (§3.5) unless a norm term is fused (then standard compressed). Leaf level:
   values $s(x)-k(k+1)$ are affine in $s$ → all leaf claims collapse to
   $s_{claim}=\tilde s(r_{virt})$ — the only claim that leaves the range pipeline.
   For $b^\star\le8$: a single sum-check (degree ≤ 4).
4. **Binariness of compression digits** (Remark 6.2): positions $I_{bin}$ (schedule-known
   spans of compression digits) additionally satisfy $w(w+1)=0$ — same quadratic, fused into
   the final sum-check (Eq. 160) with coefficient $\zeta_{bin}$ and restricted equality weight
   $\widetilde{eq}_{I_{bin}}(r_{virt},X)$ := MLE in $X$ of $x\mapsto1_{I_{bin}}(x)\widetilde{eq}(r_{virt},x)$.

**Prover optimizations**: Gruen's equality-factored message format removes the common public
equality factor from the round polynomial (one fewer coefficient per round; only when no norm
term is fused); small-value techniques of [33] reuse computations for repeated $w(w+1)$ values
(only $b^\star/2$ possible values initially).

### 5.5 Euclidean norm-check protocols (§6.2)

**Direct route** (when $\max\{U^{dir},S_{max}\}<q$): prover sends canonical encoding of
$E_{resp}$ and proves field identity $\sum_{x\in\{0,1\}^{\mu'}}z_{int}(x)^2=E_{resp}$ (Eq. 120);
Lemma 6.3: accepted identity ⇒ integer equality (both sides in $[0,q)$).

**Digit-expanded route** (when the complete squared norm can exceed $q$):
1. Partition $[N_A]$ into public consecutive segments $I_t$ with $|I_t|B_{dig,h}B_{dig,k}<q/2$ (Eq. 122).
2. Prover supplies claims $p_{t,h,k}:=\sum_{u\in I_t}z_h(u)z_k(u)\in\mathbb{F}_q$ for all $0\le h\le k<\delta_f$ (Eq. 121).
3. Verifier takes unique centered lift $\bar p_{t,h,k}\in(-q/2,q/2)$ and reconstructs
   $E_{resp}=\sum_t(\sum_hb^{2h}\bar p_{t,h,h}+2\sum_{h<k}b^{h+k}\bar p_{t,h,k})$ (Eq. 123);
   rejects on mismatch, negative, or $>S_{max}$. (Lemmas 6.4, 6.5.)
4. **Fusion**: after digit-inner-product claims fixed, sample $\zeta_{pair}\leftarrow\mathbb{E}$;
   $N_{pair}:=|\{I_t\}|\delta_f(\delta_f+1)/2$ (Eq. 124);
   $P_{norm}(x):=\sum_{t,h\le k}\zeta_{pair}^{\mathrm{idx}(t,h,k)}1_{I_t}(x)z_h(x)z_k(x)$,
   $C_{norm}:=\sum\zeta_{pair}^{\mathrm{idx}}p_{t,h,k}$; then fresh $\zeta_{norm}\leftarrow\mathbb{E}$
   and one sum-check $\sum_x(P_{rng}(x)+\zeta_{norm}P_{norm}(x))=C_{rng}+\zeta_{norm}C_{norm}$
   (Eq. 125). Direct norm term degree 2; digit-pair terms degree 3 (segment indicator included);
   fused stage uses standard compressed format; adds **no rounds**, one extra element per round.
5. **Binding to the committed witness** (Eqs. 126–128): after final range-tree point $r$,
   sample $\eta_{norm}\leftarrow\mathbb{E}$; randomized identities
   $\eta_{norm}\tilde z^{int}_f(r)=\eta_{norm}\sum_u\widetilde{eq}(r,u)\sum_hb^hw^{(j+1)}(\pi(u,h))$
   (direct) or $\eta_{norm}\tilde z^f_h(r)=\eta_{norm}\sum_u\widetilde{eq}(r,u)\sum_{h'}b^{h'}w^{(j+1)}(\pi(u,h'))$ (digit-expanded);
   combined sum-check $\sum_x(P_{base}(x)+P_{bind}(x))=C_{base}+C_{bind}$ (Eq. 128). The
   ordinary relation is independent of $\eta_{norm}$, so a false norm identity cannot cancel a
   false relation identically.

### 5.6 Ring-relation checking — both routes (§7.3)

**Quotient lifting (HMZ)**: prover supplies $Q_r\in\mathbb{K}_r[X]$, $\deg Q_r<d_r$, with
$\sum_cA_{r,c}(X)W_{r,c}(X)-Y_r(X)=(X^{d_r}+1)Q_r(X)$ (Eq. 147); evaluated at $\alpha\leftarrow\mathbb{E}$:
$\sum_c\sum_jA_{r,c}(\alpha)\alpha^jw_{\mathrm{addr}_{r,c}(j)}-Y_r(\alpha)-(\alpha^{d_r}+1)Q_r(\alpha)=0$ (Eq. 148).
- Packing fold-evaluation row (carrier, Eq. 149): $\sum_ic_i(\alpha)e_i(\alpha)-\mathcal{L}(G_{b,M}z)(\alpha)-(\alpha^{d_{car}}+1)Q_{car}(\alpha)=0$
  where $Q_{car}(Y)=\sum_{t,j}\beta_tq_{t,j}Y^j$ (k base-field planes = one polynomial over $\mathbb{E}$).
- Packing inner-consistency rows (Eq. 150): $[A(\alpha)z(\alpha)]_r-\sum_ic_i(\alpha^{kh})[t_i]_r(\alpha)-(\alpha^{d_A}+1)Q_{A,r}(\alpha)=0$
  — note the **two evaluations of the same challenge**: $c_i(\alpha)$ in the carrier equation
  and $c_i(\alpha^{kh})$ in the A-ring equations (coincide iff $kh=1$).
- Evaluation-trace fold-evaluation row (Eq. 151): $\sum_ic_i(\alpha)e_i(\alpha)-a(\alpha)^\top G_{b,M}z(\alpha)-(\alpha^{d_A}+1)Q_{eval}(\alpha)=0$.
- B/D/F/H families: ordinary lift at their scheduled dimensions with modulus factor $\alpha^d+1$.
- Error: false lifted relation passes with probability $\le(2d_{max}-1)/|\mathbb{E}|$
  (packing subring identity contributes $\le(2d_{car}-1)/|\mathbb{E}|$; not multiplied by $k$).

**Quotient-free (transpose convolution)**: residue kernel
$\kappa^{(d)}_{A,\alpha}(j):=(A(X)X^j\bmod(X^d+1))(\alpha)$ (Eq. 152); explicit
$\kappa^{(d)}_{A,\alpha}(j)=\sum_{k+j<d}a_k\alpha^{k+j}-\sum_{k+j\ge d}a_k\alpha^{k+j-d}$ (Eq. 153;
minus sign = negacyclic wraparound; e.g. $d=4$, $A=X^3$, $j=1$ gives $-1$). Lemma 7.1
(transpose-convolution identity): $(A W\bmod(X^d+1))(\alpha)=\sum_jw_j\kappa^{(d)}_{A,\alpha}(j)$
(Eq. 154). Field residual (Eq. 155):
$z_r(\alpha):=\sum_c\sum_{j=0}^{d_r-1}\kappa^{(d_r)}_{A_{r,c},\alpha}(j)w_{\mathrm{addr}_{r,c}(j)}-Y_r(\alpha)$; check $z_r(\alpha)=0$.
All kernels computable in $O(d)$ extension-field ops by a wraparound recurrence (Appendix B.1).
- **Theorem 7.2** (mixed-dimension quotient-free): completeness for all $\alpha,\tau_1$;
  soundness $\le(d_{max}-1)/|\mathbb{E}|$ (α) $+\ s_{rel}/|\mathbb{E}|$ (row batching,
  $s_{rel}=\lceil\log_2n_{rel}\rceil$); $d_{max}$-special sound in α. No division by
  $\alpha^{d_r}+1$ — roots of cyclotomic moduli need no rejection.
- **Ordering is load-bearing**: the outgoing commitment must be bound before α; the
  row-combination challenge $\tau_1$ sampled after the outgoing witness is bound (else the
  prover could choose a nonzero residual in the linear kernel — the flaw in the first public
  Grand Danois version; Appendix F.1).

### 5.7 The fused sum-check (§7.4, Figure 7)

Row-batching combines all relation rows (ring rows reduced by the selected route + scalar
opening row) with $\tau_1\in\mathbb{E}^{s_{rel}}$:
- quotient-lift: $m_{\tau_1}(x):=\sum_i\widetilde{eq}(\tau_1,i)M(\alpha)(i,\cdot)$ evaluated on
  witness columns; $V_{\alpha,\tau_1}:=\sum_i\widetilde{eq}(\tau_1,i)[y(\alpha)]_i$ (Eq. 158),
  where $M(\alpha)$ includes quotient columns;
- quotient-free: $m_{\tau_1}(x):=m^{qf}_{\alpha,\tau_1}(x)$ (sum of native row occurrences),
  $V_{\alpha,\tau_1}:=V^{qf}_{\alpha,\tau_1}$ (Eq. 159).

Verifier samples $\gamma\leftarrow\mathbb{E}$ and, when $I_{bin}\ne\emptyset$, a distinct
$\zeta_{bin}\leftarrow\mathbb{E}$ (else $\zeta_{bin}=0$, $\widetilde{eq}_\emptyset=0$). One
sum-check for (Eq. 160):

$$\sum_{x\in\{0,1\}^{\mu'}}\Big[\tilde w(x)m_{\tau_1}(x)+\gamma\big(\widetilde{eq}(r_{virt},x)+\zeta_{bin}\widetilde{eq}_{I_{bin}}(r_{virt},x)\big)\cdot\tilde w(x)(\tilde w(x)+1)\Big]=V_{\alpha,\tau_1}+\gamma s_{claim}.$$

Simultaneously (i) verifies every relation row (incl. the evaluation claim) and (ii) binds the
range claim $\tilde s$ to the committed witness. Standard compressed format (relation term has
no common equality factor). Final point $r_2$; claimed witness value $v'$ there. Remaining
private claim: the opening $\tilde w^{(j+1)}(r_2)=v'$ passed to the next level.

### 5.8 Verifier evaluation of the batched row (§7.5, Table 6)

At $r_x=r_2$ the verifier evaluates $m_{\tau_1}(r_2)=m_{local}(r_2)+\sigma_S$ (Eq. 166/12):
- $m_{local}$: structured gadget/challenge/opening-row/norm/quotient contributions + directly
  evaluated F/H compression relations, computed via the finite-state/tensor-factor evaluator
  (Appendix A) in $O(\log|w'|+\text{depths}+d)$ work;
- $\sigma_S=\sum_{p<N_{active}}S_p\bar\omega(p)$ (Eq. 161): the setup scan —
  $N_{active}=\max_{I\in\mathcal{M}_{setup}}n_Im_Id_I$; overlapping views (incl. B slices) add
  their weights; $N_{active}$ base-field × extension-field multiply-adds.

**Sum-check round-message accounting (Table 6):**

| Stage | Rounds | Degree | Format | Elements/round |
|---|---|---|---|---|
| Nonidentity shared tensor reduction | $m_{max}$ | 2 | standard | 2 |
| Single-claim nonidentity tensor reduction | $\ell-\kappa$ | 2 | standard | 2 |
| Identity tensor reduction (incl. $k=1$) | 0 | – | none | 0 |
| Range product stage $i$, w/o norm fusion | $\mu'$ | $d_i+1$ | equality-factored | $d_i$ |
| Final range stage, either norm route | $\mu'$ | $d_i+1$ | standard | $d_i+1$ |
| Fused relation + range binding + binary support (+ norm-claim binding) | $\mu'$ | 3 | standard | 3 |
| Setup-product sum-check | $\nu_S$ | 2 | standard | 2 |

### 5.9 Terminal protocol (§8.2)

State bound by the preceding fold: the canonical inner state $t_i=A_{term}s_i$ for every block
$i\in[B_{term}]$ of the one incoming recursive-witness group (final edge = TerminalInnerState;
terminal accepts ONE recursive-witness group, NO pending setup opening).

1. Predecessor absorbs terminal $t$ state as its outgoing binding; terminal reabsorbs it.
2. Tensor-reduction prefix (if $k>1$): produces packed claim $g_{term}(\rho_{term})=\bar v_{term}$
   and final pair $(\theta_{term},v_{tensor})$, $v_{tensor}=\theta_{term}\bar v_{term}$;
   requires $\theta_{term}\ne0$; rejects without resampling (separate from response grinding).
   Split $\rho_{term}=(\rho_{blk,term},\rho_{pos,term},\rho_{pack,term})$; define
   $a_{term,x}:=\widetilde{eq}(\rho_{pos,term},x)$, $\chi_{blk,term}(i):=\widetilde{eq}(\rho_{blk,term},i)$,
   $T_{\rho_{pack,term}$ = specialization of Eq. 133.
3. Form partials $e_i:=\langle a_{term},f_i\rangle\in R_{term}$ and absorb the **clear** (uncommitted)
   partial opening evaluations $(e_i)_i$.
4. Response grind: each candidate nonce absorbed before deriving the complete fold-challenge
   tuple $(c_i)_i$; nonce admissible only when every bounded fixed-filter sampler produces an
   accepted challenge and the clear response $z:=\sum_ic_is_i\in R_{term}$ satisfies its
   scheduled encoding and norm checks; ≤ $N_{try,term}$ nonces; final transcript contains the
   selected nonce and absorbs $z$ before the terminal checks:
   - Eq. 163: $A_{term}z=\sum_ic_it_i$ in $R_{term}$;
   - Eq. 164: $\sum_ic_i(X)e_i(X)=a_{term}(X)^\top G_{b_{term},M_{term}}z(X)$ in $R_{term}$;
   - Eq. 165: $\sum_i\theta_{term}\chi_{blk,term}(i)T_{\rho_{pack,term}}(e_i)=v_{tensor}$ in $\mathbb{E}$.
5. Response bound checked directly (coefficient-wise or squared-norm); no digit-range
   sum-check; no outer B relation, D/H path, quotient witness, relation sum-check, or next
   commitment. Signed Rice encoding with a byte budget $\sum_i|z_i|\le N_z\sqrt S$ permitted.

### 5.10 Setup offloading — Stage 3 (§9.1–9.2)

After Stage 2 (fused sum-check) fixes $r_x$ (so $\omega_{setup}$ is fully determined):

1. Prover supplies claimed $\sigma_S$ for the final check of Stage 2.
2. Stage 3 proves the claimed setup inner product by degree-2 sum-check
   $\sigma_S=\sum_{p\in\{0,1\}^{\nu_S}}\tilde S^\flat(p)\widetilde\omega_{setup}(p)$ (Eq. 168;
   padded source $S^\flat(p)=S_p$ for $p<N_{active}$, else 0; $\omega_{setup}(p)=0$ on padding;
   standard compressed format).
3. Output: point $\rho_S$; sum-check output $=\tilde S^\flat(\rho_S)\cdot\widetilde\omega_{setup}(\rho_S)$
   (Eq. 169). Verifier computes the second factor from public description (Appendix B.4) without
   scanning the setup prefix; the value $s_{\rho_S}$ is carried to the next fold.
4. Successor receives $\mathcal{O}_{h+1}=(\mathcal{S}_h,\mathcal{W}_{h+1})$ (Eq. 170) with
   $\mathcal{S}_h=(C_{S,h},\rho_S,s_{\rho_S})$, $\mathcal{W}_{h+1}=(C_{W,h+1},r_2,v_W)$,
   $v_W:=\hat w^{(h+1)}(r_2)$. Receiver binds both groups' shared opening payload before
   sampling $\vartheta_{grp}\leftarrow\mathbb{E}$. Boundary targets: packing
   $v_{boundary}:=\phi_Ss_{\rho_S}+\vartheta_{grp}\phi_Wv_W$ (Eq. 171); trace
   $\bar v_{boundary}:=h_S+\vartheta_{grp}h_W$ (Eq. 172).
5. Only ONE setup opening pending at any boundary; final nonterminal fold must check any
   incoming setup group and produce none; the terminal cannot check one.
6. **Lemma 9.1**: conditioned on Stage-3 sum-check soundness and binding of the successor's
   opening of $C_{S,h}$, the used $\sigma_S$ equals the verifier's direct fused setup scan.
   Binding by the source-comparison class $C^{cmp}_{S,h}$ (contains protocol occurrence and
   canonical reference occurrence $u^0_{S,h}$ of Eq. 192), radius from Eqs. 195/196.
7. Carried-setup size: rank-one profile $N_{active}=\max_Id_Im_I\le|w'|_\mathbb{K}$ (Eq. 173);
   $N_{prefix}:=2^{\lceil\log_2N_{active}\rceil}<2N_{active}\le2|w'|_\mathbb{K}$ (Eq. 174).

### 5.11 The assembled protocol (§9.5, Figure 8)

- **Setup($1^\lambda,\mu_{max}$)**: fix admissible schedule; expand seed into $S$ (Eq. 67) with
  stacked prefix views (Fig. 3); prepare setup data for every scheduled direct edge; populate
  verifier's setup-prefix registry with exact commitments $C_{S,h}$ for every scheduled
  offloaded edge.
- **Commit(pp, shape, $(f_p)_{p\in[P]}$)**: run the commitment pipeline (Fig. 4); output
  $cm=(\mathrm{shape}_{com},u_{pub})$. Commitments entering one root batch remain
  independently formed with their own shapes.
- **Eval(pp, $\mathcal{O}_0$)**: absorb seed identity, schedule digest (incl. $(\lambda_{FS},Q_{max})$),
  every root commitment/point/claimed value; then (1) run Figure 5 at each scheduled
  nonterminal level (after the root use the source list of Eq. 61; offloaded edges also run
  Stage 3 and pass the setup opening to the immediate successor); (2) the final fold produces
  the canonical terminal inner state — apply the tensor prefix when required and the direct
  checks of §8.2; reject any pending setup opening.
- **V accepts** iff every sum-check verifies, every payload and shape check passes, grinding
  nonces respect their scheduled ranges, and the terminal checks hold.

**Opening-mode policy (Eq. 162)**: $\mathrm{method}(j,\mathrm{kind})=$ SubringCoefficientPacking
for nonterminal levels 0,1; EvaluationTrace otherwise (incl. terminal). Ring-check policy:
quotient lifting forms a prefix; optional quotient-free suffix only from level 2, evaluation
trace, neither receiving nor producing a setup opening. Compression: root + setup-prefix
commitments compressed; along the recursion compression may stop once and not resume.

### 5.12 Schedule topology (§4.2)

- Root source: ordered nonempty list of application-supplied groups
  $\mathcal{O}_0=(\mathcal{A}_{0,0},\dots,\mathcal{A}_{0,G_0-1})$ (Eq. 60);
  $G_0=1$ = ordinary single-opening interface. After the root:
  $\mathcal{O}_j=(\mathcal{W}_j)$ if edge$_{j-1}$=Direct; $(\mathcal{S}_{j-1},\mathcal{W}_j)$
  if OffloadedSetup (Eq. 61).
- Fold configuration: $\mathrm{cfg}_j=(\mathrm{Open}_j,\mathrm{RingCheck}_j,\mathrm{Comp}_j,\mathrm{Norm}_j)$ (Eq. 62);
  fold record (Eq. 83): $\mathrm{Fold}:=(\mathrm{OpeningMethod};\mathrm{RingCheck};(\mathrm{Chal}_g,b_{z,g},\delta_{f,g})_{g\in[G]};(d_D,n_D);\mathcal{H};\mathrm{Norm};\delta_{quot})$.
- Edge tags: $\mathrm{edge}_j\in\{\mathrm{Direct},\mathrm{OffloadedSetup},\mathrm{TerminalInnerState}\}$ (Eq. 63).
- Schedule: finite composable sequence (Eq. 64)
  $\mathcal{O}_0\xrightarrow{\mathrm{Fold}_0[\mathrm{cfg}_0;\mathrm{edge}_0]}\mathcal{O}_1\to\cdots\xrightarrow{\mathrm{Fold}_{t-1}[\ldots;\mathrm{TerminalInnerState}]}\mathcal{T}_t\xrightarrow{\mathrm{Terminal}}\mathrm{accept}$.
- Fiat–Shamir profile: every schedule records target $\lambda_{FS}$, max classical query count
  $Q_{max}$ (counting every nonce probe to $\mathcal{H}_{FS}$; setup-expansion queries don't
  count), raw challenge shells, filters, certified $|\mathcal{C}^{acc}|$ lower bounds,
  pairwise-difference certificates, raw-draw allowances, nonce sets $\{N_{try,j}\}$ and joint
  retry rules. Schedule digest absorbed before the first protocol challenge.
- Within a fold each challenge coordinate is derived from a separately indexed query under a
  fixed round root and candidate nonce (deriving one coordinate does not absorb another's answer).

### 5.13 Constant-root verifier schedule (§9.4)

Fix $\kappa_{root}\ge2$, $N^\star:=N^{1/\kappa_{root}}$ (Eq. 17). First $\kappa_{root}-1$ folds:
$B_j=\tilde O_{\kappa_{root},\lambda}(N^\star)$ blocks, $M_j=\lceil N_j/B_j\rceil$; verifier
processes the $B_j$ challenge evaluations; offloading removes the $M_j$ setup scan; direct F/H
evaluations remain. Witness recurrence $N_{j+1}=\tilde O_{\kappa_{root},\lambda}(N_j/N^\star+N^\star)$
(Eq. 177/18); after $\kappa_{root}-1$ folds the claim has size $\tilde O(N^\star)$; then
balanced direct folds with $N_{j+1}\le N_j^\beta$ ($\beta<1$, e.g. $3/4$ above a poly-in-$L$
threshold). Costs (Eq. 19): prover $\tilde O_{\kappa_{root},\lambda}(N)$; proof
$\tilde O_{\kappa_{root},\lambda}(\log N)$; verifier $\tilde O_{\kappa_{root},\lambda}(N^{1/\kappa_{root}})$;
expanded A/B/D verifier setup $\tilde O_{\kappa_{root},\lambda}(N^{1/\kappa_{root}})$ (plus
seed and offloading commitments).

**Regularity conditions** (constant-root regular family): (1) counts of groups, claims/slice
groups, logical B slices, relation-row families, quotient families, active F/H maps are
$\tilde O(1)$; (2) all ring dims, ranks, digit depths, challenge descriptions, finite-state
address spaces $\tilde O(1)$ in $N$; (3) successor segments other than the folded response
have total length $\tilde O(B_j)$; (4) $N_{prefix,j}=\tilde O(|w_{j+1}|)$; (5) exact
finite-state evaluations of remaining factored rows and $\widetilde\omega_{setup}(\rho_S)$
take $\tilde O(N^\star)$ field ops (factors over $M_j$ positions evaluated through equality
structure, no enumeration).

**Theorem 9.3** states the costs above under these conditions. **Lemma 9.4** (existence):
under a parameter-growth assumption (module-rank-one MSIS: for each constant $C$ choose
power-of-two $d\ge CL$, $d=L^{O(1)}$, prime $q\equiv5\bmod8$ with $\log_2q=\Theta_C(L^2)$,
such that degree-$d$ rank-1 width $\le2^{CL}$ collision-bound $\le2^{CL}$ instances are
$2^{-CL}$-hard for $2^{CL}$-time algorithms; $L:=\lambda+\lceil\log_2(N+2)\rceil+\lceil\log_2(Q_{max}+2)\rceil$),
there exist admissible constant-root schedules using: one common ring degree, rank one, one B
slice, $\mathbb{E}=\mathbb{F}_q$, entire ring as challenge subring at the first two levels,
quotient lifting through the offloaded prefix, $b=b_1=4$ digits, no Euclidean/operator
filtering/grinding, two-stage binary compression on root/setup-prefix commitments then raw,
challenges = all sign vectors with exactly $d/2$ nonzero entries (count
$\binom{d/2}^{d/2}$... i.e. $\binom d{d/2}2^{d/2}=2^{\Omega(d)}$, $\|c\|_1=d/2$, differences
bounded by 2), sampled by unranking a uniform index into the shell (binary rejection;
$\ge1/2$ success/trial, $CL$ trials → failure $\le2^{-CL}$). Response planes: deterministic
coefficient bound $O(B_jd)$ → $O(\log B_j+\log d)$ base-4 planes.

**Hardness discussion**: a fixed positive power in the hardness exponent
($h(D)=\Omega(D^\alpha)$, incl. $2^{\Omega(\sqrt D)}$) suffices with $D=L^{O(1/\alpha)}$;
only quasipolynomial $2^{\Omega((\log D)^c)}$ gives $N^{1+o(1)}$ prover, $N^{1/\kappa_{root}+o(1)}$
verifier, $N^{o(1)}$ proofs instead of polylog.

## 6. Soundness & Security

### 6.1 Completeness (§10.1)

- **Response admission** (Def. 10.5): $\mathrm{HAdm}_{h,r}(z) := \mathrm{Enc}_{h,r}(z)\wedge[\|z\|_{2,coef}^2\le S_{max,h,r}$ if $p_{h,r}=2]$, where the encoding domain at a nonterminal fold is exactly the balanced interval $[-M_{h,r},T_{h,r}]$ of Eq. 180 with $M_{h,r}=\frac{b_{h,r}}2\frac{b_{h,r}^{\delta_{f,h,r}}-1}{b_{h,r}-1}$, $T_{h,r}=\frac{b_{h,r}}2(\frac{b_{h,r}^{\delta_{f,h,r}}-1}{b_{h,r}-1})-1$ (canonical decomposition fits in $\delta_f$ planes).
- **Conditional nonce failure** (Def. 10.6): $a_h:=\prod_{u\in U_h}(1-(1-\alpha_{h,u})^{L_{h,u}})$;
  $\hat q_h^{rsp}(\tau):=\Pr[\neg\mathrm{HAdm}_{h,r}(z_{h,r}(\tau,c_h))\ \forall r\mid c_h\ne\bot]$;
  $q_h(\tau):=1-a_h(1-\hat q_h^{rsp}(\tau))$.
- **Lemma 10.7**: with $N_{try,h}$ independent nonce trials, failure prob $q_h(\tau)^{N_{try,h}}$ (power taken *before* averaging over $\tau$ — retries reuse fixed sources).
- **Theorem 10.9** (scheduled completeness): accepted with probability ≥
  $1-\varepsilon_{comp}(\mathrm{sch})$ where
  $\varepsilon_{comp}=\sum_{h\in\mathrm{RespLev}}\xi_h+\sum_{h\in\mathrm{EvalRecv}^+}\frac{G_h(\kappa_h+m_{max,h})}{|\mathbb{E}_h|}+\varepsilon^{pow}(\mathrm{sch})$;
  with $\varepsilon^{pow}=\sum_{g_i>0}(1-2^{-g_i})^{M_i}$ ($M_i=2^{g_i+7}$, each ≤ $e^{-128}$; PoW rule $g=\max\{0,128+\lceil\log_2L\rceil-C\}$ makes $2^{-g}L2^{-C}\le2^{-128}$).
- **Corollary 10.10**: uniform $\delta_h$ ⇒ $\xi_h=\delta_h^{N_{try,h}}$. Rare-exception histories: $\xi_h=\eta_h+\delta_h^{N_{try,h}}$.
- Certified response bounds: deterministic envelopes (Corollary G.6:
  $U_{h,r}=\sum_aK_{1,h,a}B_{h,r,a}$ with $T_{h,r}\ge U_{h,r}$, $S_{max}\ge D_{h,r}=(\sum_a\sqrt{\Gamma_{h,a}E_{h,a}})^2$ ⇒ $q^{rsp}=0$)
  or marginal tails (Corollary G.7 with allocations satisfying Eq. 322).
  Modeled (Gaussian-surrogate) bounds retain the conditional premise Eq. 351.

### 6.2 Knowledge soundness (§10.2) — backward extraction

**Module-SIS inventory.** $\mathrm{Occ}(\mathrm{sch})$ = every scheduled source-group occurrence at a
nonterminal fold + the single terminal occurrence. Each occurrence $u$ records the verified
bounds $(K_{1,u},B_{\infty,u},K_{mul,2,u},B_{2,u},K_{2,u},B_{mul,2,u})$ (Euclidean entries optional).
Registered setup commitments add canonical reference occurrences $u^0_{S,h}$ with weak
certificate $\bar c^0_{S,h,c,i}=1$, $r^0_{S,h,c,i}=s^0_{S,h,c,i}$ (Eq. 191) and envelopes (Eq. 192).
Two occurrences are **source-compatible** iff same commitment shape (incl. B/F source path) and
same $A$ matrix view; this partitions occurrences into **source-comparison classes**.
Class collision radii (Eqs. 193–196):
- $E_\infty(u,u'):=K_{1,u'}B_{\infty,u}+K_{1,u}B_{\infty,u'}$;
- $E_{2,1}=K_{1,u'}B_{2,u}+K_{1,u}B'_{2,u}$; $E_{2,2}=K_{mul,2,u'}B_{2,u}+K_{mul,2,u}B'_{2,u}$; $E_{2,3}=K_{2,u'}B_{mul,2,u}+K_{2,u}B'_{mul,2,u}$;
- $\eta_{A,C}:=\max_{u,u'}E_\infty(u,u')$ ($p_C=\infty$) or $\max_{u,u'}\min_{r\in P(u,u')}E_{2,r}(u,u')$ ($p_C=2$; requires $P(u,u')\ne\emptyset$);
- $\eta_{K,C}:=\max_{u,u'}\max_{x\in D_{K,u},y\in D_{K,u'}}\|x-y\|_{\infty,coef}$ (cross-profile alphabet diameter for B/F views; D/H occurrence-local).

**Table 7 — MSIS instance inventory** (per schedule):

| Instance $I$ | Description | $d_I$ | $n_I$ | $m_I$ | $p_I$ | Collision bound $\eta_I$ |
|---|---|---|---|---|---|---|
| $A^{(C)}$ | Nonterminal source-class inner commitment | $d_A$ | $n_A$ | $m_A$ | $p_C$ | $\eta_{A,C}$ (Eq. 195) |
| $A_{term}$ | Terminal inner commitment | $d_A$ | $n_A$ | $m_A$ | $\infty$ or 2 | Eq. 209/210 |
| $B^{(C)}$ | Source-class sliced outer commitment | $d_B$ | $n_B$ | $m_B$ (one slice width) | $\infty$ | $\eta_{B,C}$ |
| $D^{(j)}$ | Unsliced opening commitment | $d_D$ | $n_D$ | $m_D$ (full width) | $\infty$ | $\eta_{D,j}=b_{range}-1$ |
| $F_\ell^{(C)}$ | Source-class outer chain map $\ell\in\{1,..,L_F\}$ | $d_{F,\ell}$ | $n_{F,\ell}$ | $m_{F,\ell}$ | $\infty$ | **1** |
| $H_\ell^{(j)}$ | Opening-local chain map $\ell\in\{1,..,L_H\}$ | $d_{H,\ell}$ | $n_{H,\ell}$ | $m_{H,\ell}$ | $\infty$ | **1** |

Terminal radii: $\eta_{A,term,\infty}=8\kappa_{1,term}Z_{\infty,term}$ (Eq. 209);
$\eta_{A,term,2}=64\Gamma_{term}^2S_{max,term}$ (Eq. 210).

- **Lemma 10.11** (shared-prefix → ordinary MSIS): any adversary outputting a short kernel
  vector for a matrix *view* of a uniform flat setup $S\leftarrow\mathbb{Z}_q^{N_{setup}}$ reduces to ordinary
  MSIS adversaries: $\mathrm{Adv}^{sch}_{sp}\le\sum_{I\in I(sch)}\mathrm{Adv}^{\mathrm{MSIS}^{(p_I)}}_{q,d_I}(n_I,m_I,\eta_I)(B_I)$ (Eq. 197). Simulation: embed the ordinary MSIS challenge as the $I$-view of $S$, fill the rest uniformly.
- **Corollary 10.12**: same for an adaptive schedule chosen from a public family $\mathcal{S}_P$ (union $I_P=\bigcup I(sch)$, Eq. 198) — no conditioning on the schedule choice.
- **Definition 10.13 (Akita algebraic decommitment)**: commitment-side part of the
  construction: $f^\star_{j,c}=\mathrm{Dec}_{shape}((s_{j,c,i})_i)$, $A_js_{j,c,i}=G_{b_1,n_A}\hat t_{j,c,i}$,
  slice map + F chain rows (76)/(77) terminate at $u_{pub,j}$; digits in the contracted
  alphabets; no zero condition on algebraic-padding cells; no canonicality of the gadget
  decomposition. $\mathrm{Rel}^{Akita}_{com}$ (Eq. 200); batch relation $\mathrm{Rel}^{Akita}_{batch}$
  (Eq. 202): all groups' $\mathrm{Rel}^{Akita}_{com}$ ∧ all $\tilde f^\star_{j,c}(r_j)=\phi_{j,c}v_{j,c}$.
- **Definition 10.14 (weak opening)**: source blocks, $\hat t$/$\hat e$, compression openings,
  units $\bar c_{j,c,i}\in S_j$ with
  $\|\iota_j(\bar c)\|_1\le\bar\kappa_{1,j}$, $\|\iota_j(\bar c)s\|_{\infty,coef}\le\bar\beta_{\infty,j}$
  (+ Euclidean variants); all Figure-6 rows on these (recomposed) values; source projection
  $\mathrm{Src}(\omega)$ discards challenges/partials/D-H.
- **Lemma 10.15 (weak binding, one fold)**: two weak openings for the same instance/payloads
  that differ ⇒ short nonzero kernel vector for $A_j$, $B_j$, $D$, or a compression map.
  Cross-multiplication (both denominators cleared):
  $z_A:=\iota_j(\bar c_i')(\iota_j(\bar c_i)s_i)-\iota_j(\bar c_i)(\iota_j(\bar c_i')s_i')$, $A_jz_A=0$;
  bounds Eqs. 203–206: $\|z_A\|_{\infty}\le2\bar\kappa_1\bar\beta_\infty$;
  $\|z_A\|_2\le2\min\{\bar\kappa_1\bar\beta_2,\bar\kappa_{mul,2}\bar\beta_2,\bar\kappa_2\bar\beta_{mul,2}\}$.
- **Remark 10.16**: collisions are priced at the *enforced* alphabet ($b^\star-1$ for B/D;
  1 for F/H since $w(w+1)=0$; response planes by Eq. 112), not the honest alphabet
  ($b_1-1$ would under-price when $b_1<b^\star$).
- **Corollary 10.17**: source-extractor uniqueness across opening profiles (same comparison
  class + same commitment ⇒ same $\mathrm{Src}$, else collision); holds with one side being a
  canonical setup reference occurrence.
- **Corollary 10.21** (radius-to-collision): with raw bounds
  $\|c\|_1\le\kappa_1$, $\|c\|_{mul,2}\le\Gamma$, $\|c\|_2\le\kappa_2$, $\|z\|_2\le Z_2$,
  $\|z\|_{mul}\le Z_{mul}$: $\|z_A\|_2^2\le64\min\{\kappa_1^2Z_2^2,\Gamma^2Z_2^2,\kappa_2^2Z_{mul}^2\}$
  (form differences over $\mathbb{Z}$ *before* reduction mod $q$).
- **Lemma 10.24** (public batching): false padded claim passes $\zeta_{batch}$ recombination
  with prob ≤ $(\Lambda-1)/|\mathbb{E}|$ (degree-$\Lambda-1$ polynomial).
- **Lemma 10.25** (Euclidean response check soundness): implies
  $E_{int}(\hat z)=E_{resp}\le S_{max}$, $\|z\|_2^2\le E_{resp}$; extra RLC error ≤
  $2/|\mathbb{E}|$ (direct) or $(N_{pair}+\delta_f)/|\mathbb{E}|$ (digit-expanded).
- **Corollary 10.26**: coefficient route radius $\eta_{A,\infty}=8\kappa_1Z_\infty$;
  Euclidean route $\eta_{A,2}=64\Gamma^2S_{max}$ (requires no-wrap premise on challenge
  differences); $\ell_1$-ball challenge of mass $\omega_j$: $\eta_{A,j}=4\omega_j\Delta^{cert}_{f,j}$.
- **Theorem 10.27**: ring reduction is $\xi_{ring}$-special sound with $\xi_{ring}=2d_{max}$
  (QuotientLift) or $d_{max}$ (QuotientFree); fused relation sum-check has $\mu'$ degree-3 rounds.
- **Lemma 10.28** (range tree CWSS): $\varepsilon_{tree}=\sum_{j=1}^S\frac{\mu'(d_j+1)}{|\mathbb{F}_{q^k}|}+\sum_{j=1}^{S-1}\frac{m_j-1}{|\mathbb{F}_{q^k}|}$.
- **Theorem 10.23 (one-fold backward extraction)**: from a descendant-certified nested
  coordinate-wise fold family (Def. 10.22: one prefix + $|Q|+1$ folding-challenge children
  forming a CWSS structure, complete accepting mixed subtrees below each), a deterministic
  extractor returns (i) a weak opening of every incoming source group
  ($\bar\beta_{\infty,j}=\Delta^{cert}_{f,j}$), or (ii) a short kernel vector for a matrix view.
  Later challenges need not agree across folding children.
- **Theorem 10.31 (interactive extraction, fixed schedule)**: from a complete accepting
  transcript tree, extractor returns an Akita batch witness satisfying
  $\mathrm{Rel}^{Akita}_{batch}$ or a short kernel vector (norm ≤ $\eta_I$); knowledge error
  $\le\varepsilon_{int}(\mathrm{sch})$ (Eq. 223); repeated commitment occurrences agree.
- **Theorem 10.33 (Fiat–Shamir knowledge soundness, classical ROM)**: for
  $Q\le Q_{max}$ queries to $\mathcal{H}_{FS}$:
  $\Pr[\text{accept}\wedge\text{extract fails}]\le(Q+1)\varepsilon_{int}(\mathrm{sch})+\Delta_{setup}+\sum_{I\in I(sch)}\mathrm{Adv}^{\mathrm{MSIS}^{(p_I)}}_{q,d_I}(n_I,m_I,\eta_I)(B_I)$ (Eq. 229)
  ≤ $2^{-\lambda_{FS}}+\Delta_{setup}+\sum\mathrm{Adv}^{MSIS}$. Proof: (1) idealize setup
  (statistical distance $N_{setup}q2^{-w}$); (2) FS→transcript tree (Lemma 3.22 + Lemma 10.2
  conditional tapes); (3) extract fixed schedule; (4) shared-view collisions → ordinary MSIS.
- **Corollary 10.34**: effective FS strength
  $\lambda^{eff}_{FS}=-\log_2((Q_{max}+1)\varepsilon_{int})$; claim only
  $\lambda_{FS}\le\lambda^{eff}_{FS}$; ceiling $\log_2|\mathbb{E}|-\log_2c-\log_2(Q_{max}+1)$ if error contains $c/|\mathbb{E}|$.
- **Theorem 10.37 (size-adaptive knowledge soundness)**: public policy $\mathcal{P}$ with
  finite accepted family $\mathcal{S}_P$, transcript binds $(\vec N,sch)$ before the first
  challenge; error ≤ $(Q+1)\max_{sch}\varepsilon_{int}+\Delta_{setup}+\sum_{I\in I_P}\mathrm{Adv}^{MSIS}$.
- **Remark 10.32**: extraction does NOT recover the canonical commitment state (division by
  a unit need not preserve norm) — hence the decommitment-relation formulation of Def. 3.15.
- **Per-level interactive error** (Eq. 218):
  $\varepsilon_j=\varepsilon_{cw,j}+\frac{\xi_{ring,j}+\lceil\log n_j\rceil+\mu'_j+\beta_j\mu'_j}{|\mathbb{F}_{q^k}|}+\frac{\sum_s\mu'_j(d_{j,s}+1)+\sum_s(m_{j,s}-1)}{|\mathbb{F}_{q^k}|}+\frac{1+\beta_j+\nu_j+3\mu'_j}{|\mathbb{E}|}$;
  $\varepsilon^{sch}_j=\varepsilon_j+o_j\frac{2\log_2N_{setup,j}}{|\mathbb{F}_{q^k}|}$ (Eq. 219);
  $\varepsilon_{int}=\sum_j\varepsilon^{sch}_j+\varepsilon_{tensor}+\varepsilon_{grp}+\varepsilon_{term}+\varepsilon_{batch}$ (Eq. 223);
  FS budget $\varepsilon_{FS}(\mathrm{sch};Q_{max})=(Q_{max}+1)\varepsilon_{int}\le2^{-\lambda_{FS}}$ (Eq. 224).
  Tree size (Eq. 225): flat fold factor $1+\sum_gW_{j,g}$; claim combinations factor $\Lambda$;
  tensor row batching $2^\kappa$; range anchor $2^{\mu'}$; row batching $2^{\lceil\log_2n_{rel}\rceil}$;
  scalar degree-$D$ sum-check stage $D+1$; admissibility requires $\mathrm{Tree}(sch)\le T_{poly}(\lambda,N_{exp,max})$ (Eq. 176).
- **Extraction tree cost** (Eq. 227):
  $T_{FS}\le(Q+1)\mathrm{poly}(\lambda,|sch|,\mathrm{Tree}(sch),T_A,T_{ver},T_{filter})$;
  $T_{filter}=\max\sum_uL_{r,u}/a_{r,u}$ (Eq. 226).
- **Security model caveat**: classical ROM only; the Module-SIS inventory is sized against a
  quantum lattice-attack cost model, but that does not upgrade the FS reduction to QROM.
  Every prover-controlled nonce probe counts toward $Q$; setup-expansion queries don't.

### 6.3 Distributed proving security (§11)

- **Proposition 11.1**: chunked completeness — one-shot failure
  $\delta_{chunk}\le\sum_{j\in J_+}2n_z\exp(-t_j^2/(2V_j))$ with $V_j=C_j\kappa_2^2\sigma_\infty^2$
  (Eq. 254/255); nonce exhaustion ≤ $(1-a_h(1-\delta_{chunk}))^{N_{try}}$ (Eq. 256).
- **Theorem 11.2**: extraction of a response-chunked fold — weak opening with
  $\bar\beta_\infty=\Delta^{cert}_\Sigma=\sum_j\Delta^{cert}_{rsp,j}$ (Eq. 258/259);
  A-collision radius $\eta_{A,chunk}=2\bar\kappa_1\Delta^{cert}_\Sigma=4\omega\Delta^{cert}_\Sigma$
  (Eqs. 260/261). The factor $N_{chunk}$ appears because aggregate rows don't identify which
  chunk changed. All other radii unchanged.
- **Corollary 11.3**: substituting chunked completeness/radius/sum-check parameters into
  Theorems 10.9/10.33 — no additional error term. Workers+aggregator treated as one prover
  (no privacy/fairness/robustness vs. malicious workers).
- Chunk limits: $N_{chunk}=1$ or powers of two ≤ 64; used only at leading packing folds;
  one fold-challenge vector and one nonce shared by all chunks.

### 6.4 Comparison with Greyhound / LaBinius / prior art (§1–2, App. F)

- vs **Greyhound**: same family (LaBRADOR two-tier Ajtai + norm reset + recursion), Akita adds:
  setup offloading (constant-root verifier), optimized digit range check, per-matrix ring
  dimensions + subring challenges, quotient-free tail, 128-byte commitments, exact $\ell_2$
  norm checks. Greyhound = square-root verifier, 46–53 KB proofs, truncated-output Ring-SIS
  in its implementation (App. F.2 — extension-ring packing $T=S[Z]/(Z^p-Y)$ with output
  truncated to $\kappa<p$ coordinates: *not* covered by its Module-SIS theorem).
- vs **LaBinius**: Akita works over arbitrary prime fields with a cyclotomic ring + Ajtai
  commitments instead of binary towers + sumcheck; shares the small-field packing ideas
  (tensor reduction of Diamond–Posen), uses LaBRADOR-style folding rather than
  recursive snapping; concrete proofs ~61–72 KB vs LaBinius's asymptotics.
- vs **Hachi** (direct predecessor): Akita fixes Hachi's base-field shortcut (§3.2 of Hachi is
  *unsound* for $k>2$: the two E-linear checks (Eqs. 310/311 here) leave a joint kernel;
  Akita's fix = tensor reduction of Diamond–Posen); replaces the single Hachi fold with
  folding-to-completion; adds setup offloading; removes the transmitted trace ring element
  (4096 bytes at Hachi's parameters); two opening representations; smaller commitments.
- Trilemma positioning: Jindo (cube-root, 315–1207 KB), RoKoKo/Grand Danois (polylog verify,
  but vSIS), SLAP/FMNV/CMNW (polylog from Module-SIS but 8.3 MB–767 MB proofs).

## 7. Parameters & Concrete Efficiency

### 7.1 Running example schedule (§2.4, Table 2) — $2^{30}$ fp32 coefficients, 4 GiB input, $\mathbb{E}/\mathbb{K}$ degree 4

Six committed folds (0–5) + terminal T:

| level | $N_j$ | $M_j$ | $B_j$ | $d_A$ | $d_D$ | opening | $d_{op}$ | ring check | L2 check |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 524,288 | 512 | 1,024 | 2,048 | 256 | direct | 256 | quotient | – |
| 1 | 56,192 | 512 | 110 | 1,024 | 256 | direct | 256 | quotient | – |
| 1 (setup) | 8,192 | 128 | 64 | 1,024 | 256 | direct | 256 | quotient | – |
| 2 | 54,408 | 1,024 | 54 | 128 | 128 | trace | 128 | quotient | – |
| 3 | 7,236 | 512 | 15 | 128 | 128 | trace | 128 | transpose | – |
| 4 | 2,776 | 256 | 11 | 128 | 128 | trace | 128 | transpose | ✓ |
| 5 | 1,134 | 128 | 9 | 128 | 128 | trace | 128 | transpose | ✓ |
| T | 634 | 128 | 5 | 128 | – | trace | 128 | clear | ✓ |

Root detail: $2^{30}$ coefficients → $2^{19}$ $A$-ring elements at $d_A=2048$, $B=2^{10}$
blocks of $M=2^9$; coordinate split $30=10+9+11$ (block/position/$A$-ring coefficient); $k=4$,
$d_{car}=64$, $h=8$; 11 = 5 (index $a$) + 6 (index $j$); partial = 256 base-field coordinates
(1 MiB across 1024 blocks vs 8 MiB for trace). Offloading example: root scan of $5\cdot2^{20}$
coefficients, precommitted prefix padded to $2^{23}$; largest remaining direct scan $2^{20}$
coefficients; expanded verifier matrix storage 20 → 4 MiB; prover stores 32 vs 20 MiB;
planner proof estimate 66,571 → 69,289 bytes; verification 32.5 → 15.9 ms; opening +14.5%;
proof +4.2%.

### 7.2 Concrete field profiles (App. H/I)

$p_{32}=2^{32}-99$, $p_{64}=2^{64}-59$, and a 128-bit prime the extracted text renders as
"$2^{128}-2^{32}+2^{2537}$" (superscript run is mangled in pdftotext — a Goldilocks-style
$2^{128}-2^{32}+\text{small}$ correction term; consult the artifact for the exact value). Extension degrees for openings: 4 (p32),
2 (p64), 1 (p128) — each opening-field element ≈ 128 bits. $N=2^{b-5},2^{b-6},2^{b-7}$ for
nominal $B=2^b$ bits. Commitment payload: 128 bytes (+ ~214–215 B of profile/shape metadata
counted as excluded verifier context).

### 7.3 Lattice-PCS benchmarks (Table 8; AMD Ryzen 9 9950X, AVX-512, 121 GiB RAM, 1 thread for lattice provers; medians of 10 runs)

| Bits committed | Scheme | Commit (s) | Open (s) | Verify (ms) | Proof (KB) | Peak RAM (GiB) |
|---|---|---|---|---|---|---|
| $2^{27}$ | Akita direct | 0.097 | 0.999 | 7.5 | 61.3 | 0.128 |
| $2^{27}$ | Akita offloaded | – | – | – | – | – |
| $2^{27}$ | Greyhound | 0.110 | 0.183 | 75.0 | 60.1 | 0.33 |
| $2^{27}$ | RoKoKo | 0.037 | 0.158 | 4.0 | 109.3 | 0.852 |
| $2^{29}$ | Akita direct | 0.333 | 1.53 | 9.3 | 61.8 | 0.254 |
| $2^{29}$ | Akita offloaded | 0.329 | 2.04 | 8.1 | 66.2 | 0.253 |
| $2^{29}$ | Greyhound | 0.444 | 0.396 | 155 | 60.6 | 1.08 |
| $2^{29}$ | RoKoKo | 0.122 | 0.275 | 4.3 | 109.4 | 1.72 |
| $2^{31}$ | Akita direct | 1.25 | 2.70 | 12.7 | 63.1 | 0.696 |
| $2^{31}$ | Akita offloaded | 1.24 | 3.32 | 12.1 | 66.3 | 0.699 |
| $2^{31}$ | Greyhound | 2.10 | 1.06 | 334 | 63.3 | 3.93 |
| $2^{31}$ | RoKoKo | 0.437 | 0.726 | 5.0 | 114.8 | 4.47 |
| $2^{33}$ | Akita direct | 6.02 | 6.59 | 20.8 | 64.5 | 1.38 |
| $2^{33}$ | Akita offloaded | 6.02 | 7.78 | 14.4 | 66.9 | 1.42 |
| $2^{33}$ | Greyhound | 11.5 | 4.50 | 676 | 64.9 | 20.7 |
| $2^{33}$ | RoKoKo | 1.69 | 1.48 | 4.9 | 114.9 | 12.3 |
| $2^{35}$ | Akita direct | 24.3 | 16.1 | 32.5 | 64.6 | 4.69 |
| $2^{35}$ | Akita offloaded | 24.4 | 18.4 | **15.9** | 67.3 | 4.71 |
| $2^{35}$ | Greyhound | 52.3 | 19.2 | 1423 | 67.2 | 92.6 |
| $2^{35}$ | RoKoKo | 8.27 | 4.43 | 7.2 | 115.0 | 36.9 |

Offloaded profile supported from $2^{29}$ bits ($2^{24}$ coefficients) up. Offloading at
$2^{35}$: verify 32.5→15.9 ms, open 16.1→18.4 s, proof 64.6→67.3 KB. Verification speedup vs
calibrated Greyhound: 19.2× (at $2^{29}$) to 89.7× (at $2^{35}$). RoKoKo verifies faster
(4.0–7.2 ms) but targets 100-bit statistical soundness with ~109–115 KB proofs.

### 7.4 Hash-PCS comparison (Table 9/16/17/18; 8-thread provers, 1-thread verify)

Selected rows at $2^{35}$ bits committed (full 3-size table in paper Table 9):

| Scheme | Commit (s) | Open (s) | Verify (ms) | Proof (KB) | Peak RAM (GiB) |
|---|---|---|---|---|---|
| Akita (p32) | 3.46 | 2.71 | 32.6 | 64.6 | 4.71 |
| Akita offload (p32) | 3.46 | 3.01 | 15.9 | 67.3 | 4.74 |
| Akita (p64) | 3.77 | 1.78 | 21.1 | 68.5 | 4.90 |
| Akita offload (p64) | 3.77 | 2.03 | 14.7 | 71.8 | 4.95 |
| Akita (p128) | 2.89 | 1.87 | 24.1 | 69.1 | 5.05 |
| Akita offload (p128) | 2.88 | 2.01 | 12.2 | 72.0 | 5.15 |
| Plonky2 FRI | OOM | OOM | OOM | OOM | OOM |
| Plonky3 FRI(1) | 5.89 | 1.24 | 10.2 | 570.2 | 12.2 |
| Plonky3 STIR(1) | 5.89 | 1.60 | 4.3 | 233.5 | 12.2 |
| WHIR (Plonky3)(2) | 5.53 | 8.38 | 11.4 | 690.9 | 17.1 |
| Binius64 BaseFold | 5.01 | 1.41 | 1.1 | 666.7 | 22.7 |
| Flock Ligerito | 2.38 | 5.21 | 1.7 | 570.5 | 21.7 |
| WHIR (WorldFnd) | 24.7 | 117 | 1.4 | 317.4 | 43.4 |
| BaseFold (SP1) | 67.7 | 5.51 | 32.0 | 1440.6 | 21.3 |

(1) = batched univariate (128 polys at $2^{35}$); (2) = unique decoding. Tradeoff: Akita
proofs 64.6–72.0 KB vs 233.5–1440.6 KB hash-based; hash baselines (except SP1) verify faster
and most open faster 1-thread. Akita uses least memory at large sizes among non-Binius/Flock rows
in its own profiles; one-thread Akita commit 18.6–26.3 s at $2^{35}$. Communication totals
(Table 17): Akita total = 61.5–72.1 KB (incl. 128 B commitment + evaluation); commitment
sizes of baselines: Plonky2 520 B, Plonky3/SP1 32 B, STIR 34 B, WHIR 32–56 B, Flock 4136 B.
Prep state (Table 18): Akita 0.002–0.0625 GiB; offloaded adds ~0.44–0.82 s preprocessing.

### 7.5 Jolt end-to-end (Table 10; Apple M4 Max, 16 cores, 64 GiB, macOS; SHA-256 chains; medians of 3 runs)

| Trace length | Backend | Prove (s) | Verify (ms) | Proof (KB) | Peak RAM (GiB) |
|---|---|---|---|---|---|
| $2^{17}$ | Akita | 0.50 | 9.96 | 85.9 | 0.33 |
| $2^{17}$ | Dory | 1.08 | 69.38 | 81.9 | 0.32 |
| $2^{19}$ | Akita | 1.12 | 14.49 | 88.5 | 0.55 |
| $2^{19}$ | Dory | 2.21 | 73.93 | 86.2 | 0.61 |
| $2^{21}$ | Akita | 3.30 | 11.66 | 92.8 | 1.26 |
| $2^{21}$ | Dory | 5.63 | 77.80 | 90.6 | 1.85 |
| $2^{23}$ | Akita | 11.22 | 15.57 | 94.0 | 2.93 |
| $2^{23}$ | Dory | 16.35 | 83.10 | 94.9 | 3.45 |
| $2^{25}$ | Akita | 29.45 | 28.17 | 94.2 | 11.17 |
| $2^{25}$ | Dory | 54.07 | 85.78 | 91.8 | 13.26 |
| $2^{27}$ | Akita | 90.85 | 39.82 | 98.1 | 35.47 |
| $2^{27}$ | Dory | 175.18 | 88.29 | 95.9 | 34.76 |

Prover speedup 1.3–2.2×; verifier speedup 2.2–7.4×; proofs within [−0.9%, +8.9%] of Dory,
all < 100 KB. At $T=2^{27}$: throughput 0.766→1.477 MHz. Configuration transitions: setup
offloading first at $T=2^{21}$ (verify 15.44→11.66 ms despite larger trace; proof
89.6→92.8 KB); at $T=2^{25}$ Jolt switches 4-bit→8-bit one-hot chunks and 16-bit→32-bit
read-address chunks (Akita proof 96.1→94.2 KB; verify 16.88→28.17 ms).

### 7.6 Security parameters (App. C, D)

- Per-instance floor: quantum ADPS16 ≥ $2^{128}$ (Core-SVP: quantum $2^{0.2650\beta}$,
  classical $2^{0.2920\beta}$). Family-wide (union over $\mathcal{I}_P$):
  $\lambda_{fam}=-\log_2\sum2^{-c_I}>125$ bits (every fixed schedule > 127).
- Estimator: LGSA basis shape + quantum ADPS16; $\ell_\infty$ instances use direct
  infinity-norm attack equations; Euclidean instances keyed by $C^2$ (e.g. $64\Gamma^2S_{max}$),
  scalarized $n_{sc}=rd$, $m_{sc}=m_Ad$, $L_{sc}=\sqrt{C^2}$ (Eq. 298). Rust estimator ~3 orders
  of magnitude faster than Python/Sage; corrections documented (centered Gaussian mass,
  active dimension, tall q-ary domain, ZGSA determinant preservation).
- Compression maps (Table 5 params): first stage 147.34 bits (block size 556), second 153.17
  bits (578); ≥ 147 bits for all supported widths.
- Operator-norm filter certificates (Table 12): $d=64$, shell $(a,b)=(31,11)$, $T=18$,
  $\log_2(N_{raw}p_0)=128.06$; $d=128$, shell $(31,0)$, $T=13$,
  $\log_2(N_{raw}p_0)=128.56$. Precision $\nu=48$, error $\epsilon=4$; Bernstein/Sturm
  certificates for the degree-30 tail polynomial.
- Model comparisons at $\beta=500$, $d=1024$: quantum ADPS16 132.5, classical ADPS16 146.0,
  classical MATZOV 169.7, classical BDGL16 175.4 bits.
- Greyhound recalibration for benchmarks (App. I): ranks recalibrated to 128-bit quantum
  ADPS16 Euclidean-SIS; JL norm check corrected (sparse-ternary projection, slack
  $\sqrt{128/29}$); transcript-bound challenge grinding added at all folding levels.

## 8. Implementation Notes

### 8.1 What an implementer must build (ordered by dependency)

1. **Field/ring layer** (`lzk` reuse): $\mathbb{F}_q$ for $q\in\{2^{32}-99, 2^{64}-59,
   128\text{-bit prime}\}$; negacyclic ring $R_{q,d}$ with $d\in\{16..4096\}$ powers of two;
   NTT for partial splitting $s_{split}\in\{2,4,\dots\}$ ($q\equiv5\bmod8$ minimal splitting);
   negacyclic convolution via CRT/NTT butterflies; automorphisms $\sigma_i:X\mapsto X^i$
   ($i\in\mathbb{Z}_{2d}^\times$) and $\sigma_{-1}$ for the trace map; the subfield basis
   $\{1,e_j=X^{jm}+X^{-jm}\}$ arithmetic for $k\in\{2,4\}$; extension field $\mathbb{E}=\mathbb{F}_{q^k}$
   with basis $(\beta_t)$; tensor algebra $\mathbb{E}\otimes_{\mathbb{F}_q}\mathbb{E}$ for
   the Diamond–Posen reduction ($2^\kappa\times2^\kappa$ matrices over $\mathbb{F}_q$).
2. **Challenge machinery**: sparse fixed-magnitude families $(n_a)_{a\in\mathcal{A}}$ with
   partial Fisher–Yates + bitmask rejection sampling (variable bit consumption; count
   completed *shell draws* $L_{r,u}$, not bit words); operator-norm filter
   $\mathrm{OpNormAccept}_\Gamma$ with fixed-point trig tables ($\nu=48$, $\epsilon=4$,
   Machin/Taylor interval enclosures); invertibility certificates ($2c_{max}<q^{1/s_{split}}/\sqrt{s_{split}}$).
3. **Gadget decomposition**: balanced base-$b$ digits ($b\in\{4,8,16,32,64\}$; paper default
   3-bit = base 8 for prover efficiency — digits $\{-4..3\}$); negative-binary $\{-1,0\}$
   for compression; canonical lift threshold $T=\min(T_k,\lfloor q/2\rfloor)$; exact
   representable intervals $[-M_k,T_k]$.
4. **Commitment pipeline** (§4.5/Fig. 4): embed → block reshape → decompose → inner A →
   slice/reindex into $R_{q,d_B}$ view (address permutation
   $(a\delta+u)d_A+yd_B+k\mapsto((as+y)\delta+u)d_B+k$) → outer B (per-slice, shared matrix) →
   F-chain (2 stages, negative-binary, digit-plane layout: digit $u$ of coefficient $v$ at
   $v+su$) → 128-byte payload. Sparse path: identity source map + sparse matrix-vector
   product over nonzero blocks only (pay-per-nonzero; one-hot shapes need no decomposition).
5. **Opening constructions**:
   - *Direct coefficient packing*: contraction $\mathcal{L}$ (Eq. 87) evaluating position and
     low-coefficient axes; carrier ring $S_E$; subring challenges via $\iota:Y\mapsto X^{kh}$;
     two evaluations $c(\alpha)$ vs $c(\alpha^{kh})$.
   - *Evaluation trace*: Diamond–Posen tensor reduction (column partials $S_y$, row partials
     in tensor algebra, batched degree-2 sum-check, transparent factor $A_\eta(\rho)$ with
     nonzero check); partials $e_i=\langle a,f_i\rangle$; trace functional
     $T(Z)=\frac{k}{d_A}\mathrm{Tr}_H(Z\sigma_{-1}(\check\chi))$; trace digit weights
     $\tau_\nu$, $\omega_{Tr}$ (Eqs. 24, 135).
6. **The fold driver** (Fig. 5): steps 0–6 with transcript binding (schedule digest first);
   nonce grinding loop with joint retry rule; per-coordinate domain-separated challenge
   queries (coordinate-fork friendly); successor witness assembly (Eq. 109) with exact digit
   plane addresses (Eqs. 107/108/110); optional norm claims.
7. **Range pipeline** (§6.1): $s(x)=w(x)(w+1)$ transform; product trees with branching
   (2,4,4)/(4,4) etc.; equality-factored sum-check format (omit constant coefficient;
   cache equality weights for two halves of $\tau_0$); fused binariness term
   $\widetilde{eq}_{I_{bin}}$; small-value precomputation for the $b^\star/2$ possible
   $w(w+1)$ values.
8. **Norm proofs** (§6.2): direct identity or digit-inner-product claims with segment
   partition (Eq. 122), centered lifting, integer reconstruction (Eq. 123), $\zeta_{pair}$
   power batching, fused final stage, $\eta_{norm}$ binding identities.
9. **Relation machinery** (§7): quotient-lift (private $Q_r$, weight factorization
   $A_{r,c}(\alpha)\alpha^j$) AND/OR quotient-free (residue kernels via the O(d) recurrence
   Eqs. 277/278 — no division by $\alpha^d+1$); transposed kernels for verifier evaluation
   (Eqs. 287–290); row batching with $\tau_1$; the single fused sum-check (Eq. 160).
10. **Setup offloading** (§9): registry of precommitted padded prefixes $C_{S,h}$;
    Stage-3 degree-2 setup-product sum-check; boundary combination with $(1,\vartheta_{grp})$
    weights; successor check of the setup group.
11. **Terminal**: clear partials, response grind, direct checks (Eqs. 163–165), direct norm
    bound, optional Rice encoding.
12. **Verifier evaluator** (App. A/B): the finite-state/weighted-transducer contraction
    (Def. A.1, recurrence Eq. 269) for structured public weights; carry buckets for
    shifted/tight digit windows (Prop. A.4: $O(\delta(Q+\lceil L/Q\rceil))$); paired
    two-address contractions (Eq. 267); shared-view setup weight combination (Eqs. 294/295);
    geometric digit weights via prefix sums $P(v)=\sum_{z<v}\gamma^zE[z]$ (constant-work
    windows); interval-offset equality evaluator (merge count
    $\sum_j(\lfloor hi/2^{j+1}\rfloor-\lfloor lo/2^{j+1}\rfloor+1)$).
13. **Planner + validator** (§12): dynamic programming over schedule space with cost tuple
    $(C_{pf},C_V,C_P,C_{setup},C_{comm})$ (Eq. 263); response-moment model (App. G.3:
    states $\mathcal{M}=(d_{pack};(\mu_\chi,v_\chi^{full},v_\chi^{local})_{\chi\in\{z,e,t,r,cmp\}})$,
    peak-column functional Eq. 334, Gaussian digit transition Eqs. 338/339, packing update
    Eq. 341, Gaussian correlation inequality scores Eqs. 346–350); independent validator
    rederiving every successor and checking Def. 9.2.
14. **SIS estimator**: LGSA + quantum ADPS16; table generation
    $(\text{modulus},\eta,n_{sc})\mapsto\max m_{sc}$; Euclidean buckets keyed by $C^2$.

### 8.2 Complexity summary

| Component | Prover | Verifier | Communication |
|---|---|---|---|
| Commit (dense, $N$ coeffs) | $\tilde O(N)$ | – | 128 B |
| Commit (sparse, $\nu$ nonzeros) | $\tilde O(\nu)$ | – | 128 B |
| One fold (witness $N_j$, blocks $B_j$) | $\tilde O(N_j)$ | $\tilde O(B_j+M_j)$ (direct) or $\tilde O(B_j)$ (offloaded) | $O(\log N_j)$ field elts + payloads |
| Range check ($b^\star$, $\mu'$ vars) | $O(b^\star\mu')$ (down from $O(b^{\star2}\mu')$) | – | $2(\log_2b^\star-1)\lceil\log_2\mu'\rceil+O(1)$ elements |
| Fused relation sum-check | $\tilde O(|w'|)$ | $\mu'$ rounds × 3 elements | $3\mu'$ field elements |
| Setup-product sum-check | $O(2^{\nu_S})$ | $\nu_S$ rounds × 2 elements | $2\nu_S$ field elements |
| Tensor reduction (per receiver) | $O(2^{\ell-\kappa})$ | $O(\ell)$ | $2m_{max}$ elements + column partials |
| Full opening ($\kappa_{root}$ folds) | $\tilde O_{\kappa_{root},\lambda}(N)$ | $\tilde O_{\kappa_{root},\lambda}(N^{1/\kappa_{root}})$ | $\tilde O_{\kappa_{root},\lambda}(\log N)$ |

### 8.3 Data structures & memory layout

- Flat base-field witness vector with segment offsets; digit-plane order: coefficient → digit
  → native block (Eq. 107); response planes interleave commitment digits and fold digits
  (Eq. 108). Zero alignment: compression suffix on common relation-coefficient block boundary;
  each stage on its largest-ring-dimension boundary; ends on largest group $d_A$ boundary.
- Shared setup: one seed-expanded vector; matrices are prefix views (Eq. 66, row-major,
  coefficients consecutive); $N_{setup}=2^{\lceil\log_2N_{view}\rceil}$.
- Peak RAM (full process, incl. polynomial): 4.69–5.15 GiB at $2^{35}$ bits (vs Greyhound
  92.6, RoKoKo 36.9); overhead beyond the polynomial is sublinear.
- Rust implementation: 16 crates, ~248,000 lines; scalar/NEON/AVX2/AVX-512 backends;
  field profiles p32/p64/p128.

### 8.4 Pitfalls, edge cases, and soundness traps

1. **Hachi base-field shortcut is unsound** for $k>2$ (App. F.1): the two checks
   $v=\sum\chi_yS_y$ and $g=\sum\beta_yS_y$ leave a nontrivial joint kernel; a false
   $\Delta$ with $\Delta_a=\beta_b,\Delta_b=-\beta_a$ passes both while changing the claimed
   value. Always use the full tensor reduction (row partials + tensor-algebra batching).
2. **Challenge-ordering**: the outgoing witness commitment MUST be bound before $\alpha$;
   the row-batching challenge $\tau_1$ must be sampled after the outgoing witness is bound
   (the first Grand Danois version sampled it earlier — soundness break, App. F.1).
3. **Certified vs honest alphabets** (Remark 10.16): price every collision at the enforced
   $b^\star-1$ (B/D), 1 (F/H), Eq. 112 (response), never at the honest $b_1-1$; completeness
   requires $b_1\le b^\star$ and $b_z\le b^\star$.
4. **Two challenge evaluations under packing**: $c_i(\alpha)$ in the carrier equation vs
   $c_i(\alpha^{kh})$ in A-ring equations (Eq. 150); they coincide only when $kh=1$.
5. **$\tilde s$ is not $\tilde w(\tilde w+1)$ off the Boolean cube** (§6.1): the range claim
   must be bound via the sum $\sum_x\widetilde{eq}(r_{virt},x)w(x)(w(x)+1)$, then joined to
   the relation sum-check.
6. **No division by $\alpha^d+1$** anywhere (quotient-free route and kernels); roots of
   cyclotomic moduli are legal challenge values (no rejection needed) — unlike the
   $\theta$ factors of tensor reduction, which MUST be checked nonzero.
7. **Compressed images ≥ 8 KiB input break the 128-byte output** (Table 5 cutoffs): size
   the two maps again; a rank-one map cannot securely absorb arbitrary source lengths
   (Orthus's pre-fix bug: 32 outputs over width-68,608 binary inputs = 27.4 ADPS16 bits).
8. **Response bounds and completeness**: model-derived (Gaussian surrogate) bounds are
   heuristic; power must be taken before averaging over prefixes; filtered families may
   destroy the independent-sign premises of Lemma G.1/Theorem G.2 (use Lemmas G.4/G.5).
9. **Query accounting**: every nonce probe to $\mathcal{H}_{FS}$ counts toward $Q_{max}$;
   do not both shrink $|\mathcal{C}^{acc}|$ for a grind and charge the same probes via $Q_{max}$;
   setup-expansion queries are free (separate namespace).
10. **Sampler encoding matters** (Lemma 10.2): the conditional tape must resample the full
    bit encoding of a shell draw (rejected words + accepted value), not just the decoded
    element; variable-length rejection decoding means the outer search bounds completed
    shell draws (4096 in the implementation), not bytes.
11. **Padding semantics**: extraction returns decoded full-grid vectors; natural-domain
    claims need either a separate padding-image predicate or the prefix-reduction trick
    (Lemma E.1: selector $\zeta$ over packed slots, error $s/|\mathbb{F}|$, no zero-padding
    predicate needed). Admissible padding must have a nonzero public factor $\phi$ (reject
    $\phi=0$ claims rather than treating them as negligible).
12. **Slicing**: $u=B\Pi_B(B,S_B)\hat t$ is a logical block-diagonal map with ONE matrix;
    shorter slices pad inside each polynomial segment; slice/instance dims may reuse the
    same setup coefficients — combine weights before reading (Eq. 296).
13. **Distributed**: carries prevent summing local digit decompositions; chunks share one
    nonce (all must pass); ownership boundaries align to ring elements
    ($O(Jd_{A,next})$ move cost); no privacy/robustness between machines.
14. **Response digit depth vs envelope**: honest threshold must fit the canonical interval
    (Eq. 111); the security envelope (Eq. 112) is wider when $b<b^\star$ and must drive
    Module-SIS sizing.
15. **Terminal must not receive a pending setup opening**; final committed fold checks any
    incoming setup group and produces none.

### 8.5 Reuse from the shared core engine (`lzk`)

- `Z_q[x]/(x^n+1)` NTT rings → Akita's $R_{q,d}$ with partial splitting; automorphisms for
  the trace/subfield machinery; negacyclic convolution = response folding.
- GF(2^k) tower fields → not directly used (Akita is prime-field), but the tensor-algebra
  row/column dual view in the Diamond–Posen reduction mirrors the packed-sumcheck reuse.
- Ajtai/SIS commitments → the two-tier A/B/D commitment + F/H compression chains; shared
  prefix-view setup; MSIS estimator integration.
- Multilinear sumcheck → compressed format (linear-omission), equality-factored format
  (constant-omission), unequal-arity batching with suffix embedding, and the fused
  relation/range/norm sum-checks; small-value techniques.
- Ring-norm sumcheck → range trees, $\ell_2$ certificates, digit-expanded norm reconstruction.
- Tensor/LDE encodings → $\psi$ packing, $\widetilde\alpha$ power ladders, the
  finite-state evaluator (weighted read-once branching programs; related to Jagged's
  carry-state width-4 programs).
- Fiat–Shamir transcripts → domain-separated namespaces ($\mathcal{H}_{FS}$ vs
  $\mathcal{H}_{setup}$), coordinate-indexed queries, PoW predicate sites, schedule digests.

## 9. Implementation Status (Gap Ledger)

*(to be filled by implementer)*
