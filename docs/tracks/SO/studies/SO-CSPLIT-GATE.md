# SO-CSPLIT gates CAL-1 and CAL-2: measured on the lower N = 65 torus

Status: done (2026-10-30). Design `docs/tracks/SO/design/SO-CSPLIT.md` §4.5. The gates ran on branch
`inp-socsplit2` after merging the audited branches:
- `inp-csegl2` (`d64aa6f5`, SO-CSEG-L2 `Stage`, which already contains SO-CSEG-L3 `ProductSplit`);
- `inp-sokdepth2-land` (`2dad8824`, the log-depth jet compiler).

The data are SO-DATA3's real lower torus (g2: L = 20, CertFixed 96, cutoffs 100000 / 160): its data modules
from `inp-sodata3`, copied **untracked** into the worktree and built through the compile gate.

**Verdict.**
- **All 15 probes pass.** Each forces a complete literal equality or a forced Bool. There was no OOM and no
  heartbeat or depth option.
- **The plan holds with room to spare.** Every theorem measured ≤ 4.05 GB of cgroup memory against the 10 GiB cap.
- **The per-call cost is 2–4× below the design's calibration.** The budget therefore rises from B = 75 k to
  **B = 200 k** census calls per theorem.
- **The cost falls from 3.0–4.3 to about 1.6–2.5 CPU-h per torus.**
- **The mirror is bit-exact on every probed object.**

## 1. Method

**Data (untracked, not landed).** These were built through the compile gate:
- SO-DATA3's `KAM/SpinOrbit/Data/{Format,Lower/*}`, `LunarConstsR2`, `LunarAssemblyV2` and `Graph/CertV2`;
- 56 generated gate modules, `KAM/SpinOrbit/Data/Lower/Gate/*` and `GateW` (one definition per module).

The gate modules are written by `kam-data/so-csplit/gate/gen_gate.py` and `gen_g5.py`, which run SO-DATA3's
mirror. They hold:
- the literal jet;
- ledger pairs (model and cached norm), metas and the plan for the two probed segments;
- operands and decoded terms of three packed products;
- the torsion `[4,8]` inputs, products and entry;
- the character-witness values.

**Probes** (`kam-data/so-csplit/gate/G*.lean`, `.out`, `summary.txt`):
- one heavy theorem per file;
- the production import closure: the gate index, plus `Kernel.{SegBridges, SegOne, ProductSplit, Stage}`;
- explicit instantiation in every rewrite (the L2 audit's R5);
- each run by `run_probe.sh`: alone under `flock …/.kernel-probe.lock systemd-run --user --scope -p
  MemoryMax=10G -p MemorySwapMax=0`, `LEAN_NUM_THREADS=1`, `/usr/bin/time -v`. The cgroup's `memory.peak` and
  `memory.events` are read inside the scope.

**Two memory figures.**
- **`memory.peak`** is the cgroup charge, which is what the cap enforces.
- **Max RSS** also counts the mmapped `.olean` pages already in the page cache, which are not charged to the probe.
- The import base differs by about 2.95 GB between the two (G1). A cold page cache would charge those pages to the
  first probe, so the plan budgets against the RSS-based worst case as well.

## 2. Measurements

| probe | statement (forced) | wall | user | sys | max RSS | **cgroup peak** |
|---|---|---:|---:|---:|---:|---:|
| G1 | import-only control (`True`) | 5.1 s | 2.0 s | 2.4 s | 3.55 GB | **0.60 GB** |
| G0 | jet bridge `base.ham.jet.segBeq jetLit = true` | 8.8 s | 5.4 s | 3.4 s | 4.16 GB | **1.08 GB** |
| G2 | `segOk` of cfgFull segment 22 `[529,545)`: 74.5 k calls, 4 imports, 4 exports | 19.0 s | 11.3 s | 5.7 s | 4.55 GB | **1.48 GB** |
| G3 | `segOk` of cfgFull segment 16 `[772,818)`: 147.6 k calls, 10 imports | 30.7 s | 21.3 s | 8.5 s | 5.82 GB | **2.79 GB** |
| G4a | `[0,10]` (503×503): all 7 shards of every part (`packedRealProduct … .isSome`) | 41.8 s | 29.6 s | 11.2 s | 6.84 GB | **3.84 GB** |
| G4b | `[0,10]` decode `dyadicTerms … rr.targetTerms` = literal (847 terms; 8,536 target slots) | 13.8 s | 9.0 s | 4.5 s | 4.50 GB | **1.43 GB** |
| G4c | `mulN … [0,10] … = slot10` with the product memoized (truncation, errRadius, cross terms) | 4.8 s | 2.6 s | 2.1 s | 3.70 GB | **0.61 GB** |
| G5a | the character residual `[1,0]` (484×498): all shards | 42.4 s | 30.4 s | 11.4 s | 7.05 GB | **4.05 GB** |
| G5b | its decode (`ir`, 942 terms) = literal | 15.0 s | 9.9 s | 5.1 s | 4.54 GB | **1.47 GB** |
| G5d | `expResidualUp … 0` = literal, with its product memoized | 9.7 s | 5.4 s | 3.5 s | 3.90 GB | **0.80 GB** |
| G5c | `expWitnessRadius … = some r` from the two memoized residuals (pin, `expm1Up`, combination) | 7.8 s | 4.8 s | 2.8 s | 3.68 GB | **0.59 GB** |
| G6ca | a cfgLow product `[4,8,0,0,0]` (254×522, `ii`): shards | 23.4 s | 16.5 s | 6.8 s | 5.57 GB | **2.53 GB** |
| G6cb | its decode = literal (419 terms) | 9.1 s | 5.6 s | 3.5 s | 4.14 GB | **1.06 GB** |
| G6a | torsion `[4,8]` entry (0,0) from its 4 memoized products (`matMulEntry_eq_of_products`) | 9.0 s | 4.4 s | 3.4 s | 3.76 GB | **0.66 GB** |
| G7 | `checkEnergy base = true` by `checkEnergy_of_ckpt`, chain facts as hypotheses, residual decided | 5.5 s | 3.0 s | 2.5 s | 3.72 GB | **0.63 GB** |

**Literal elaboration** (a ledger module alone, `lake env lean`):
- `Slot869` (26 KB, 270 terms): 5.1 s wall, 0.48 GB;
- `St48ARow0` (46 KB): 6.1 s, 0.48 GB.

That is ≈ 0.05 s per KB on top of a fixed ≈ 4–5 s. The ≈ 20 s per module seen in the gated build was parallel
contention.

**Bit-exactness (R1).** Every probe asserts `= true`, so equality to the mirror's literal holds for:
- two whole cfgFull segments, with their exports, cached norms and output metadata;
- slot 10;
- three decoded packed products (cfgFull, witness, cfgLow);
- a torsion entry;
- the witness residual and radius.

## 3. The memory law and the budget

**Rate.** The increment over the G1 base, against user time beyond G1's 2.0 s:

| probe | GB per user-second |
|---|---:|
| G2 | 0.095 |
| G3 | 0.113 |
| G4a | 0.117 |
| G5a | 0.121 |
| G6ca | 0.134 |

So the rate is 0.10–0.13 GB per user-second, consistent with the design's fitted 0.04–0.13.

**Per census call** (G2, G3):

| | G2 | G3 | design §4.2 |
|---|---:|---:|---:|
| time per call | 0.125 ms | 0.131 ms | 0.3–0.6 ms |
| memory per call | 11.8 KB | 14.8 KB | 25–42 KB |

That is 2–4× cheaper than the design's calibration.

**Packed products.**
- **Shards:** about 3.9 s and 0.46 GB per shard ([0,10]: 7 shards, +3.24 GB; this matches SO-DATA3's RR). cfgLow
  shards are smaller, about 2.9 s each.
- **Decode:** **≈ 0.1 MB and 0.8 ms per target slot** ([0,10]: +0.83 GB). The design's projection by subtraction
  (P1 − RR = 3.1 GB) was too high by about 4×. P1's RSS-based figure included the products' other work and mapped
  imports.
- **Remainders:** each is ≤ 0.2 GB over base (G4c, G5c, G5d).

**Budget.** The largest B with a predicted peak ≤ 7 GB:
- warm cache: 0.60 GB + 15 KB × B gives B ≈ 425 k;
- **cold cache** (RSS base 3.55 GB): 3.55 + 15 KB × B gives B ≈ 230 k.

**B = 200 k** is predicted at ≈ 3.6 GB charged warm and ≈ 6.6 GB in the cold worst case.

| | B = 75 k (design) | **B = 200 k** | B = 250 k |
|---|---:|---:|---:|
| cfgFull segments (one-op cuts 10, 28) | 38 | **15** | 13 |
| cfgLow segments (cut 28) | 70 | **25** | 21 |
| ledger models / bytes (cfgFull + cfgLow) | 479 / 8.1 MB | **307 / 5.4 MB** | 266 / 4.5 MB |
| total literal volume (estimate, §5 of the design) | 10.4 MB | **7.6 MB** | 6.7 MB |
| Gram / torsion stage theorems | 9 / 75 | **7 / 57** | 7 / 57 |

(The B = 200 k and 250 k plans were emitted by `csplit_plan.py`: `kam-data/so-csplit/plan_lower_{200000,250000}.json`.)

**Products.** Keep one shard-group theorem and one decode theorem per evaluated product (128 per torus). Merging
them would be ≈ 4.9 GB warm and ≈ 7.9 GB cold for the residual product, too close to the cold bound.

## 4. Does the plan hold?

**Memory: yes.** The heaviest measured theorem is G5a at 4.05 GB charged (7.05 GB RSS). At B = 200 k no planned
theorem is predicted above about 3.6 GB charged or 6.6 GB in the cold worst case. The 10 GiB cap (10.74 GB) leaves
at least 4 GB of margin.

**Cost per torus, at B = 200 k** (user time ≈ CPU; the builds are serial, so wall ≈ CPU × 1.5 with system time):

| item | estimate |
|---|---:|
| segment work: 6.9 M calls × 0.13 ms | 0.25 h |
| Gram and torsion entry work: 3.4 M calls × 0.13 ms | 0.12 h |
| packed shards: 667 × 3–4 s | 0.55–0.75 h |
| decodes: 351 k slots × 0.8 ms | 0.08 h |
| fixed per theorem (≈ 5 s wall each) × ≈ 380 theorems (40 segments, 256 product, 64 stage, ≈ 20 tails, frames, jet, assembly) | 0.5 h |
| literal modules: ≈ 7.6 MB × 0.05 s/KB + ≈ 150 modules × 4.5 s | 0.3 h |
| **total** | **≈ 1.6–2.5 CPU-h per torus; 3.2–5 for both** |

This is against the design's 3.0–4.3 CPU-h per torus, so the plan holds.

**Not measured here:**
- the frame corners (FrameL/N/T, 33–69 k census calls each; predicted ≤ 1.5 GB);
- the invariance rows (≤ 60 k calls);
- `checkSoGraph`, which is out of scope (design R8).

## 5. Notes for SO-CSEG-GEN (the ledger emitter)

- **B:** use 200 k census calls per theorem. Forced one-op cuts: cfgFull 10, 28; cfgLow 28 (cfgLow slot 10 is dead).
- **Products:** one shard theorem plus one decode theorem per evaluated product. The remainder (truncation,
  `errRadius`) stays in the consuming segment or entry.
- **Literal module size:** one or a few models per module; ≤ 1,400 lines is fine, since elaboration is about
  0.05 s per KB.
- **Proof form (from the probes):**
  - the jet stated through `segBeq` (G0);
  - every `rw` with explicitly instantiated lemma arguments (G4c, G5c, G6a, G7);
  - `CertModel.eq_of_segBeq (by decide +kernel)` for model equalities;
  - a local `DecidableEq (CC SoBackendV2)` for the pin ball (G5c).
- **Reference implementation:** `kam-data/so-csplit/gate/gen_gate.py` formats the literals (`tm` rows, pairs,
  cache entries, metas, `SegSpec` rows) as the probes consume them.

## 6. Deviations and limits

- **Merges.** `inp-csegl3` was not merged separately: `inp-csegl2` already contains it. No edits were made.
- **SO-DATA3 data modules.** Copied untracked into the worktree and built there; not committed. The gate data
  modules are likewise untracked, with their sources in `kam-data/so-csplit/gate`.
- **Residual G5.** It was measured in its split form (shards, decode, residual remainder, radius remainder).
  The one-op segment `[28,29)` itself, `segOk_one_of` with its `hop`, was not run. Its rewriting cost is that of
  G4c and G7 (≈ 0.6 GB); its check is a 498-term shift.
- **Single torus.** Only the lower torus was run. The upper torus has the same program and model sizes (census).
- **Cold cache.** Not reproduced. The cold-cache bound uses the RSS-based base (3.55 GB) as the worst case.
