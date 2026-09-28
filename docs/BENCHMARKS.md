# Benchmark Results (Wave 8)

Lab scale: Goldilocks q = 2^64−2^32+1 (NTT) and q = 12289 for the small-ring
protocols; ring dimensions n ∈ {8, 16}; witness lengths m ≤ 64; single-threaded
Python 3.12 (pure-int arithmetic; the papers' AVX2/NTT-optimised C+assembly
implementations are 10^3–10^4x faster — the lab measures protocol LOGIC cost).

## Wall-clock (full suite, this container)

| protocol | op | time | instance |
|---|---|---|---|
| RingSC (7.8) ring-norm sumcheck | prove | 0.010 s | m=32, n=8, degree 2 |
| | verify | 0.001 s | |
| HyperWolf (7.12) PCS | commit | 0.034 s | N=64 coeffs, k=3 |
| | prove | 0.477 s | proof = 11,200 B |
| | verify | 0.460 s | all checks accept |
| RoKoko (7.13) fold-split round | prove | 0.232 s | m_w=8, r=2 |
| | verify | 0.062 s | |
| SALSAA (7.11) A2 Π_norm+ | prove | 0.009 s | m=8 + 2 rows |
| | verify | 0.002 s | |
| SALSAA A4 VDF (T=4) | prove | 0.128 s | binary staircase + Π_bin |
| | verify | 0.005 s | |
| ProtogaLattice (7.4) PGL-Fold | prove | 0.001 s | k=2, degree-2 f |
| LatticeFold+ fold | prove | 0.001 s | m=8 |
| Akita tensor round | prove | 0.002 s | 4×4 tensor |
| Serval split-fold IPA | prove | 0.008 s | m=32 (5 rounds) |
| Symphony arity-4 folding | prove | 0.004 s | 3 batches |

## Proof-size model — HyperWolf paper parameters (Table 2 reproduction)

Per round: b·(1 + jl_rows + κ) ring elements with the paper's 128-bit q,
ι=32, κ=64, jl_rows=256, b=2, d=64:

| N | rounds k−1 | model | paper Table 2 |
|---|---|---|---|
| 2^15 | 8 | 81.2 KB | 80.28 KB |
| 2^25 | 18 | 181.6 KB | 180.59 KB |

(The ~1% residual is the final s^(1) message at 5-bit digits plus the
log-q rounding — matches the paper's derivation; see
docs/papers/hyperwolf.md §7.5.)

## Reproducing

```bash
python benchmarks/run_benchmarks.py          # full suite
python benchmarks/run_benchmarks.py --quick  # CI smoke test
python -m pytest tests/ -q                   # 8 test modules, all green
```
