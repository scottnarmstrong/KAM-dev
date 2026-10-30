# SJS-FEAS kernel probes: cost of the certificate checker in the Lean kernel vs Fourier support

Worktree `sjs-feas` (commit 5c2d5939, Lean v4.35.0), `nice -n 5 lake env lean .drafts/<probe>.lean`, one process
at a time, machine load 12-14 on 16 cores (every timing +-30 %). Kernel time = profiler "type checking took" of the
probe's single `theorem … := by decide +kernel`; RSS = `/usr/bin/time` peak of the whole process (Mathlib import
baseline 3.1 GB, 0.8 GB without Mathlib). No `maxHeartbeats`/`maxRecDepth` override anywhere.
Raw records: `kernel_probes_raw.jsonl`; fits and extrapolation: `kernel_probes.json`
(`kernel_probe_summary.py`); generators: `kernel_probe_gen.py`, runner `kernel_probe_run.py`, jet counts
`jet_counts.py` → `jet_counts.json`.

**Scope caveat.** This worktree has the *landed, pre-D34* packing (`Poly/Packed.lean`: linear-accumulator
`packShift`, linear Int slot peel `intSlotsBound`). The D34 fix (SO-PACKFIX: sparse term-driven blocks, offset-Nat
mask/shift decode) lives on the farm branch `inp-sopackfixl` and is not here. The `F*` probes below are my own
prototypes of the same ideas (measurement devices, no soundness proof) and stand in for it.

## 1. Packed product

### 1a. Landed `checkPackedProduct adv da db = true` (2-D box, B = 200 bits, `blockRows` 1, scale = B)

Synthetic random factors, exact design-B advice (nearest rounding per shard window, target = whole product
window), `da = (layA.dense tA).getD []`. Negative control (one advice slot +2) is rejected.

| S | denseLen | prodLen | shards | window | advice slots | w | kernel s | RSS GB |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 225 | 421 | 841 | 29 | 57 | 1 653 | 412 | 4.1 | 3.8 |
| 441 | 841 | 1 681 | 41 | 81 | 3 321 | 413 | 9.6 | 4.75 |
| 961 | 1 861 | 3 721 | 61 | 121 | 7 381 | 414 | 61.6 | 7.5 |

Fit: time ≈ 1.3e-4 · S^(1.9 ± 0.3) s; extra RSS ≈ 6.8e-4 · S^1.28 GB. Variations at S = 441: B = 100 / 200 / 300 →
13.9 / 9.6 / 14.5 s (no measurable bit dependence: interpretive overhead dominates). S = 961 with `blockRows` 4
(window 487): 150 s. 3-D box S = 343: 15.3 s. One landed shard (`checkShard`, S = 10 201, `blockRows` 4,
window 1 607): 188 s, 9.9 GB.

Parts at S = 961 (each alone): `dense` 0.8 s, block packing 0.9, all shard products 2.6, `shapeOK` 1.6, length /
`shardFits` / `reconFits` guards 25.9 (`shardFits` alone 14.8, 5.8 GB: it re-flattens `A.take (s+1)` per shard),
decode (`intSlotsBound` with `shardLogs`) 34.1 (≈ 4.3 ms per window slot), full 61.6; `packedRealProduct` (adds
`targetTerms`, `remainderBound`: per-slot keys and weight powers) 83.3 s, 8.9 GB.

Micro (in-kernel data, w = 2B + log n + 3): landed decode of one window of 2n−1 slots: n = 1000 → 1.3 s,
n = 2000 → ≈ 3 s, **n = 3000 → 403 s, 7.6 GB** (a cliff, reproducible cause not isolated). Landed packing memory is
quadratic (n = 6000: +2.3 GB for one 2.5 Mbit integer).

### 1b. Prototype fixed route (D34 stand-in)

`Fpack` term-driven sparse block packing (pairwise shift rounds); `Fadv` offset shift-tree packing of the advice
windows; `Fmul` all block products; `Fdec` full check with a divide-and-conquer mask/shift decode; `Fmask` the same
with a mask-and-compare test (O(1) big-integer ops per window).

| shape | S | blockRows | shards | advice slots | Fpack | Fadv | Fdec | Fmask | RSS (Fdec) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2-D box | 961 | 1 | 61 | 7 381 | 2.8 | 4.5 | 9.3 | 7.3 | 4.1 |
| 2-D box | 3 025 | 8 | 13 | 22 659 | 7.6 | 21.6 | 37.2 | 21.9 | 6.5 |
| 2-D box | 3 025 | 1 | 109 | 23 653 | | | 34.4 | | 6.5 |
| 2-D box | 3 025 | 55 (1 shard) | 1 | 11 989 | | | 34.4 | 21.3 | 5.8 |
| 3-D box | 729 | 1 | 17 | 9 809 | | | 5.1 | | 4.2 |
| 2-D diamond | 925 | 1 | 85 | 14 365 | | | 9.3 | | 4.8 |
| 3-D diamond | 377 | 1 | 25 | 31 225 | | | 19.1 | | 5.9 |

Per-unit constants: factor packing 1.25-1.48 ms per term; advice packing 0.61-0.95 ms per advice slot; D&C decode
0.20-0.34 ms per slot (micro `Pdec − Pmul`, n = 1e3..1e4); mask test ≈ 0; block products negligible
(0.2-0.4 s of 3 s). Shard size does not matter (per-slot overhead, not GMP). Memory: ≈ 82 kB per advice slot +
≈ 260 kB per factor term (2-parameter fit, 7 points, residual 0.12 GB). One prototype shard at S = 10 201
(`Fshard`, window 3 215): 29.9 s, 6.9 GB, almost all of it re-packing the 2·10⁴ factor terms (each shard
declaration re-packs unless packed blocks are certificate data tied once).

Advice slots per factor term ν (layout inflation of the landed row-major box layout): 2-D box 7.7, 3-D box 13.5,
2-D diamond 15.5, 3-D diamond 83 at K = 6 (asymptotically 2·2^d·d! = 96), 4-D box ≈ 32, 4-D diamond ≈ 768.

### 1c. GMP in the kernel (no caps up to 1e8-bit shifts; 8e8-bit products pass)

| op | 1e8 bits | 4e8 bits |
|---|---:|---:|
| mul (net) | 0.58 s | 2.6 s (6.6 ns/bit) |
| add / land / shift / divide by 2^600−1 | 4-17 ms | 40-110 ms |

## 2. Per-coefficient model passes (`CertFixed P`, production weight w = 1.0939…, keys of a 2-D box)

| pass | S = 961 | 3 025 | 10 201 | ms / term |
|---|---:|---:|---:|---:|
| `CertPoly.weightedNormUp` (`supBound`; `foldr`) | 0.41 | 1.63 | **fails** ("decide failed to reduce", deep recursion) | 0.43-0.54 |
| `CertPoly.supNormUp` (balanced `sumUp`) | 0.52 | 1.94 | 6.75 | 0.54-0.66 |
| C1 `cornerLeq` (4 vertices; `foldr`) | 2.18 | 8.07 | **fails** (same) | 0.57-0.67 per vertex |
| `CertModel.add` (two S-term models, all keys equal) | 0.83 | 2.68 | 16.0 (6.1 GB) | 0.87-1.57 |
| `CertModel.toDeg` (scale + error radius) | 1.37 | 3.90 | 16.6 | 1.3-1.6 |
| `CertPoly.toMants` (mantCheck per coefficient) | 1.68 | 19.7 | > 600 (timeout) | **superlinear** 1.7 → 6.5 → > 59 |

P = 170 vs 300 at S = 3 025: supNorm 1.69 / 1.94, add 2.89 / 2.68, toDeg 3.81 / 3.90, toMants 16.5 / 19.7 s:
precision is nearly irrelevant. The weight power `w^{|k|₁}` is recomputed per term (no cache hit across keys);
at these |k|₁ ≤ 100 it is not the dominant per-term cost (weightedNormUp with w = 11/10 also fails at 10 201).
Floor: walking a literal list costs 190 µs/element and 21 kB/element (sum: 177 µs; forced sum over
`List.range`: 65 µs) — every kernel pass over data costs ≥ 0.1 ms and ≥ 20 kB per element.

## 3. Composition

**Jet counts** (Python mirror `scripts/spin_orbit/adv_jet.py` of the landed jet compiler; model ops = add/mul with
a Fourier-model operand; MM = genuine model × model packed products):

| program | ops | model ops (whole) | invariance d1 | energy v0 | shared v0::d1 | torsion d1+d2 | MM (whole / shared) |
|---|---:|---:|---:|---:|---:|---:|---:|
| lunar `soRotHamExprScaled` (n = 2) | 887 | 658 | 98 | 43 | 140 | 273 | 1 / 1 |
| planetary-type toy n = 4, 16 modes | 2 860 | 2 357 | 400 | 147 | 461 | 1 026 | 171 / 49 |
| planetary-type toy n = 4, 64 modes | 20 068 | 17 051 | 1 784 | 531 | 1 989 | 5 750 | 1 236 / 204 |

**Kernel experiment** (synthetic program of `const`/`action`/`mul`(scalar route)/`add` on S-term models: a
shared chain of 6 model ops, branches E and I of 4 ops each, a dead branch of 8 ops; `Slp.compose` landed, C7
`composePruned` copied verbatim into the probe):

| S | E alone | I alone | E + I separate decls | E && I one decl | one compose [e, i] | composePruned | all slots forced |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 441 | 5.5 | 5.7 | 11.2 | 7.8 | 8.5 | 8.0 | 11.7 |
| 961 | 15.9 | 15.3 | 31.2 | 24.5 | 24.5 | 24.0 | 34.2 |

Per model op: 0.9-1.26 ms per term; memory ≈ 220 kB per live term-op (6.1 GB at S = 961, 14 live ops).
In one declaration the whnf cache shares the common prefix and laziness skips dead `mul`/`add` at every size
measured — pruning/sharing gives nothing there (this is size-independent: it depends only on which slots are
demanded). Separate declarations pay the shared prefix twice (+27 %). Pruning cost itself: C7 `liveSet`+`pruneOk`
on the lunar program (887 ops) 17.5 s, 5.9 GB; on the 2 860-op planetary toy it fails (kernel deep recursion).

## 4. Extrapolation (model, not measured)

Constants: c_slot ≈ 1.0 ms and 82 kB per advice slot, c_term ≈ 1.4 ms per factor term, 1.26 ms and 220 kB per
term per model op, GMP 6.6 ns/bit per product. w ≈ 2B + 40.

Per REAL packed product, prototype route (= D34-like, per-slot kernel work):

| S | 2-D box | 3-D box | 4-D box | 3-D diamond | min. declarations at 29 GB (2-D box / 3-D box) |
|---|---:|---:|---:|---:|---:|
| 1e7 | 29 CPU-h | 45 | 97 | 274 | 218 / 383 |
| 1e8 | 292 | 453 | 967 | 2 744 | 2 180 / 3 821 |

(identical at B = 300 and B = 170: bits do not enter.) Per model op on an S-term model: 3.5 CPU-h at 1e7,
35 at 1e8, ≈ 2.2 TB / 22 TB of kernel memory if done in one declaration. Lunar-type shared invariance + energy
(140 model ops): 490 / 4 900 CPU-h; planetary toy with 64 modes (1 989 model ops + 204 MM products): ≈ 7 000 CPU-h
of model ops + 204 × (29-97) CPU-h of products at 1e7.

Landed checker extrapolated by its fit: ≈ 1 CPU-h and 90 GB at S = 1e4 in one declaration; 10⁵-10⁶ CPU-h at 1e7.

GMP-only floor (packed representation, O(1) big-integer ops per product, no per-term kernel steps): one
2-D-box product at S = 1e7, B = 300 (factor 1.2e10 bits): ≈ 7 min and ≈ 6-12 GB; 3-D box ≈ 12 min, 11-22 GB.
Largest single product in a 32 GB slice under that design ≈ 3-6e10 bits per factor (≈ 5-9e7 slots at w = 640).
Under the current per-slot design: ≈ 2-3e5 advice slots per 29 GB declaration (landed: ≈ 4e3 terms in 2-D).

## 5. Uncertainties

- Single runs on a loaded machine (±30 %). Fits use 3-7 points; the landed exponents are rough (p = 1.9 ± 0.3).
- The prototype is not the D34 code; SO-PACKFIX reported one lunar `blockRows`-32 shard (8 192-slot blocks,
  w = 896) at +45 s and 4.55 GB, the same order per slot (≈ 2-3 ms/slot) as my prototype.
- Memory per element assumes the whnf/infer caches retain everything for the whole declaration (observed linear).
- The `toMants` superlinearity and the landed-decode cliff at ≈ 6 000-slot windows are measured, not explained.
- The planetary jet is a polynomial-amplitude toy (no inv/exp/sqrt nodes), so its op counts are lower bounds.
- GMP-only floor: measured mul throughput only; the packed rounding/norm/truncation algebra it presumes does not
  exist and its kernel cost is an estimate.
