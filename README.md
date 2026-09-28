# lzk — Lattice-ZK Protocol Lab

Reference implementations of **15 lattice-based zero-knowledge / folding /
polynomial-commitment protocols** from the 2024–2026 literature, with deep
per-paper analysis docs, an exact-protocol test suite, and a benchmark
harness.  Everything runs end-to-end: honest prover → verifier → attack
rejection, at reduced (lab) parameters with the papers' exact protocol logic.

```
python -m pytest tests/ -q          # full test suite
python benchmarks/run_benchmarks.py # wall-clock + paper proof-size models
```

## The papers

| # | paper | module | status |
|---|---|---|---|
| 1 | **HyperWolf** (ePrint 2025/922) — hypercube-wise lattice PCS, k-round recursive folding, O(log N) proofs | `lzk.protocols.hyperwolf` | **full** (7.12) |
| 2 | **RoKoko** — committed refinement: recursive COM, fold-split, sumcheckify, linearisation | `lzk.protocols.rokoko` | **full** (7.13) |
| 3 | **SALSAA** (2025/2124) — sumcheck-aided RoKs: Π_norm+, Π_bin, staircase, VDF, AIR folding | `lzk.protocols.salsaa` | **full** (7.11 A1–A5) |
| 4 | **ProtogaLattice** — algebraic folding via ring Gröbner reduction: PGL-Fold, PGL-Boot | `lzk.protocols.protogalattice` + `lzk.core.groebner` | **full** (7.4 P0-1..P0-5) |
| 5 | LatticeFold+ (Boneh–Chen) — folding + range checks + ring-norm sumcheck | `lzk.protocols.latticefold_plus` | core |
| 6 | LaBinius (Osadnik–Seiler) — binary tower PCS, field-switch reductions | `lzk.protocols.labinius` | core |
| 7 | Akita (Dao et al.) — high-performance tensor-commit PCS | `lzk.protocols.akita` | core |
| 8 | Twist & Shout (Setty–Thaler) — one-hot memory checking PIOPs | `lzk.protocols.twistshout` | core |
| 9 | Cyclo (Garreta et al.) — partial range checks / pay-per-bit folding | `lzk.protocols.cyclo` | core |
| 10 | PikkuFold (Osadnik) — layered random projections folding | `lzk.protocols.pikkufold` | core |
| 11 | Quasar (Zheng et al.) — multi-cast union-polynomial accumulation | `lzk.protocols.quasar` | core |
| 12 | Serval (Zhang et al.) — slack-free ℓ2 split-and-fold IPA | `lzk.protocols.serval` | core |
| 13 | Symphony (B. Chen) — high-arity ROM folding | `lzk.protocols.symphony` | core |
| 14 | Hachi (Nguyen et al.) — extension-field PCS, HMZ ring switch | `lzk.protocols.hachi` | core |
| 15 | PROV attack (Ferreira–Perret) — Gröbner key recovery on UOV | `docs/papers/salsa_probe.md` | analysis |

"full" = every protocol figure transcribed + implemented + tamper-tested;
"core" = the paper's characteristic mechanism end-to-end (the remaining
machinery is documented in the paper's gap ledger).

## The core engine (`lzk.core`)

- **`ring.py`** — `R_q = Z_q[X]/(X^n+1)`: negacyclic NTT (Goldilocks) or exact
  Kronecker bigint convolution; the conjugation involution `X↦X^{-1}` with the
  Hermitian trace identity `Tr(a†b) = n·⟨a,b⟩`; balanced integer norms.
- **`sumcheck.py`** — product-of-MLEs sumcheck engine (bind recursion,
  coefficient-form round messages), `eq`/MLE utilities (MSB-first hypercube).
- **`ringsc.py`** — **RingSC** (lab item 7.8): the generalized ring sumcheck
  with explicit protocol combiners; **Π_norm** (conjugate inner product, the
  O(m) trick, balanced-trace check), **Π_batch** (power-ladder row folding).
- **`groebner.py`** — **P0-4**: the staircase ideal
  `I = ⟨Y_iY_j − Y_i⟩` with Proposition 1's reduced Gröbner basis, the
  deterministic division algorithm with quotient extraction
  (`P = Σ K_rs Z_rs + R`, deg K ≤ d−2), the L-basis of Lemma 4.
- **`transcript.py`** — Fiat-Shamir duplex with domain separation + forks.
- **`commitment.py`** — seeded (transparent) Ajtai/Module-SIS commitments,
  gadget decompositions.
- **`field.py`** — GF(2^k) tower fields for the binary-field protocols.
- **`serialization.py`** — canonical proof encodings + size models.

## Documentation

- **`docs/ARCHITECTURE.md`** — the in-depth system architecture: every
  module, every protocol's internal mechanics, the shared-engine mapping,
  and the full data-flow of each proof system.
- **`docs/papers/<name>.md`** (15 files, ~12,000 lines) — per-paper deep
  analyses: notation tables, algebraic settings, full protocol-figure
  transcriptions, soundness sketches, parameter tables, implementation
  notes, and the **gap ledger** (exactly what is implemented vs simplified).
- **`docs/BENCHMARKS.md`** — wall-clock + the HyperWolf Table-2 size-model
  reproduction.
- **`docs/GAP_LEDGER.md`** — the consolidated Wave-7/8 item status.

## Layout

```
src/lzk/core/         the shared engine (ring, sumcheck, RingSC, Groebner, ...)
src/lzk/protocols/    14 protocol modules
tests/                pytest suite (8 modules — core + every protocol)
benchmarks/           wall-clock harness + paper size models
docs/papers/          15 deep paper analyses with gap ledgers
scripts/              bring-up scripts (the originals the tests were migrated from)
```

Python ≥ 3.10, only dependency `numpy` (SVD for challenge op-norm rejection).

**Not audited. Not constant-time. Reduced security parameters.** This is a
research lab for studying protocol mechanics — see each paper's gap ledger
before relying on any of it.
