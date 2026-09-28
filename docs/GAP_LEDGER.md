# Consolidated Gap Ledger — Wave 7 + Wave 8

The per-paper ledgers live in `docs/papers/<name>.md` §9. This file
consolidates the milestone status from the prior plan (Wave 7 = protocol
completion; Wave 8 = performance alignment + productionization).

## Wave 7 items (protocol completion)

| item | paper(s) | status |
|---|---|---|
| 7.4 P0-1..P0-3 | ProtogaLattice setting/relations/backbone | ✅ |
| **7.4 P0-4** | **ring-Gröbner reduction module** (`lzk.core.groebner`) | ✅ **full** |
| **7.4 P0-5** | **PGL-Fold + PGL-Boot end-to-end** (e\*-bookkeeping) | ✅ **full** |
| 7.8 | RingSC engine (ring-norm sumcheck) | ✅ shared core |
| **7.11 A1–A5** | **SALSAA**: Π_sum/Π_batch, Π_norm+, Π_bin+staircase, VDF, AIR folding | ✅ **full** |
| **7.12 W1–W5** | **HyperWolf**: core→witness→commitment→protocol→PCS+size model | ✅ **full** |
| **7.13 R1–R5** | **RoKoko**: Ξ^lin, COM, fold-split, sumcheckify, Π^lin, round driver | ✅ (R1 partial: no Π^proj-f) |
| 7.x others | LaBinius, LF+, Akita, Twist&Shout, Cyclo, PikkuFold, Quasar, Serval, Symphony, Hachi | ✅ core mechanisms |
| — | PROV attack (salsa_probe) | ✅ analysis |

## Wave 8 items (performance + productionization)

| item | deliverable | status |
|---|---|---|
| 8.1 | benchmark harness (`benchmarks/run_benchmarks.py`) + `docs/BENCHMARKS.md` | ✅ |
| 8.2 | proof serialization & size models (`lzk.core.serialization`, HyperWolf Table-2 reproduction within 1%) | ✅ |
| 8.3 | Fiat-Shamir transcripts, domain separation + forks (`lzk.core.transcript`) | ✅ |
| 8.4 | NTT fast path (Goldilocks) + Kronecker exact fallback; benchmarked | ✅ |
| 8.5 | pytest suite (8 modules, all green) + attack/tamper tests per protocol | ✅ |
| 8.6 | CI workflow (`.github/workflows/ci.yml`, py3.10/3.12 matrix + quick bench) | ✅ |
| 8.7 | coverage config (pyproject) | ✅ |
| 8.8 | README + usage docs | ✅ |
| 8.9 | packaging (`pyproject.toml`, `lzk` on the src layout) | ✅ |
| 8.10 | LICENSE (MIT) + reproducible bring-up scripts in `scripts/` | ✅ |

## Known lab simplifications (all documented in the per-paper §9)
- CRT-slot / subfield Φ-batching → full-ring challenges (SALSAA, RoKoko).
- Row-tensor H/F factorisations → flat row tables (verifier-side optimisation).
- ZK masking, hiding randomness — out of scope (no masking anywhere).
- Reduced security parameters (32/61-bit q, n = 8..16 rings).
