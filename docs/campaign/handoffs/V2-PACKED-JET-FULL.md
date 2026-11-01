# V2-PACKED-JET-FULL handoff: the whole cfgFull jet chain of LG00, packed and measured block by block

Task: the orchestrator's decisions after V2-PACKED-JET-LOW, on `v2-packed-jet`:
1. **Full first,** measured end to end against the landed Full stage (10.2 CPU-h).
2. Then the rounding leaf conversion (a new module; keep `CertFixed 128` and the landed embedding) and the
   `P = 64` measurement on the whole Low chain.
3. Then the production pieces: the shared data module, one theorem over all blocks with their order, and the link
   to the consumers.

Rules: new modules only under `KAM/CertificateSharp/Packed`, additive; at most 4 GB per Lean process; at most one
Lean process of mine at a time. From the orchestrator's later rule: heavy Python under an 8 GiB cap (below).

## Result

**Every one of the 169 blocks of LG00's whole cfgFull chain passes in the kernel**, each as a separate theorem
over a probe-local copy of the program, the embedding, the weight and the π enclosure. The chain itself is not
yet one theorem; see "What is not proved" below.
- **Data.** `lg00-cert` `fd82fef5`; 1,837 live slots (463 constants, 120 characters, 20 actions, 2 `inv`, 2
  `sqrt`, the rest products and sums), ending at the 5 wanted slots 7731 (`J.v0`) and 7732–7735 (`J.d1`).
- **The box.** cfgFull (cutoff 48) on the packed box `H = 48`: 97 × 97 coefficients, the product window
  193 × 193, slots of 400 bits (book `lb = 140`, `P = 128`). That is 3.6× the coefficients of Low's 51 × 51.
- **169 blocks, one process each, every one under the 4 GiB cap:**
  - 88 segments (at most 8 heavy steps and at most 15 imports + exports each), holding 1,693 steps: 463
    constants, 78 box-by-box products and 487 reduces in place;
  - 5 action blocks (20 action slots, 4 each);
  - 4 staged exponentials `exp(±i 2π angleAt_j)`, Taylor degrees 17 (`j = 0`) and 22 (`j = 1`): 4 `tstart`,
    28 `tstep` (at most 3 Taylor steps each, 78 in all: 24 blocks of 3, 2 of 2 and 2 of 1) and 4 `texp`
    blocks;
  - 12 power blocks (`m = 2..6`, at most 2 powers each, each from the previous power: 8 blocks export 2
    powers and 4 export 1, 20 in all);
  - 24 character blocks (2 keys each: 48 keys, 120 character slots);
  - 2 `inv` and 2 `sqrt` blocks.
- **No given blocks.** The chain theorem `jChainT_slot` has no hypotheses beyond the block checks, the block
  order, the book, weight and π checks, and `hng` (no block is given). Its LG00 instance is not built (below).

| | landed Full stage (run20e) | packed Full chain |
|---|---:|---:|
| processes | the `KAM.LG00Cert.Full.*` modules | 169 |
| CPU (user + sys) | **36,734.5 s (10.20 h)** | **4,382.8 s (1.22 h)** |
| kernel | — | 945.7 s |
| largest charge | — | 4.08 GB (`FullSeg_37`) |
| serial wall | — | 3,482.0 s |

**That is 8.4× on the whole Full stage, with three items unmeasured:**
- the shared data module (it would remove most of the fixed part below);
- one theorem over the 169 blocks with its order proof (the LG00 instance of `jChainT_slot`, below);
- the link from the `JEnc` exports to the consumers (§12.2).

Notes on the figures:
- The landed figure counts each module's last, successful run. With the ledger's failed earlier attempts
  (8.7 s), it is 36,743.3 s, still 8.4×.
- The landed figure includes its 2,113.1 CPU-s of literal modules. The packed figure includes, in every
  process, the elaboration of that process's own data.
- Single runs on a shared machine (LG00's kernel run alongside); no block was repeated.

## What is not proved (as for Low; AUDIT-V2-PACKED-JET-1 M1)

- **The LG00 instance of `jChainT_slot` is not built.** Its hypotheses are not discharged in Lean for LG00:
  - `hfirst` (the block order) and `hng` (no given block). Both hold as data, not as a Lean proof. The audit
    (AUDIT-V2-PACKED-JET-FULL-1) checked `hfirst` as data: all 892 imports equal an earlier export, key and
    literal node alike, in plan order; no key is exported twice; no block is given.
  - **The block order is load-bearing.** The per-block theorems do not check the degree or power labels of
    their imports: a `texp` fed the partial sum of degree 2 under the key `sum 3`, or a `pows` fed the square
    as the power 3, passes its own check (audit probe). Only `hfirst`, through the ledger keys, ties the
    labels. So the 169 per-block theorems alone establish no slot enclosure; they do so within
    `jChainT_slot`, as at Low.
  - `jBookOk`: checked inside each segment only.
  - `checkWeight gW` and `checkPiEnclosure lgPe`: they appear in no probe.
- **The probe program is a prefix.** `lgProg` is the first 7,736 of the 7,816 operations of `lg00Jet.prog`
  (slots `[0, 7736)`, ending at the wanted slot 7735). A prefix lemma (`Slp.val_append`) is needed unless the
  data module names `lg00Jet.prog` itself.
- **`hfirst` cannot be decided as stated.** `JNode`, `PC` and `CertFixed` have no `DecidableEq`. With a shared
  data module it can be shown by name; alternatively, derive `DecidableEq` or index the ledger by key.

## Where the CPU goes, and why the ratio is lower than Low's 35.6×

**The fixed part per process dominates at Full.** The kernel is 945.7 s, 22% of the total. The other 3,437.1
CPU-s is 20.3 s per process. Two baselines split it (`full/base/`):
- the imports alone: 2.2 CPU-s (`FullBaseImports`: the probe header and a trivial theorem);
- the imports plus the probe's copy of the program (7,736 operations), the book and the embedding: 11.8 CPU-s
  (`FullBaseData`).
- So per process: 2.2 s of imports, 9.6 s of shared data, about 8.5 s of the block's own node literals on
  average, then the kernel.
- The shared data is 169 × 9.6 ≈ 1,620 CPU-s, 37% of the total. **Estimate, unmeasured:** with a shared data
  module the chain would cost about 2,760 CPU-s, about 13× the landed Full stage. Sharing the node literals too
  (each node elaborated once, not in both its exporting and its importing block) would go further.

**The kernel per heavy step is 5.8× Low's**: 1.04 s in the segments (0.18 s at Low), for 3.7× the bits per
step; the products of the larger numbers cost more than linearly.

**More processes per heavy step.** At most 8 heavy steps and 15 nodes per segment (Low: 34 heavy steps), so
169 processes for 849 heavy steps (Low: 60 for 1,624), each paying the fixed part.

**The packed side grows faster than the landed one.** The packed nodes keep the dense 97 × 97 box. Per live slot
the packed cost grows 6.3× from Low to Full (0.38 to 2.39 CPU-s); the landed cost grows 1.5× (13.5 to 20.0 CPU-s).

**By kind.** The landed cost of a module is split evenly over its pieces, so this split is approximate.

| kind | landed CPU | packed blocks | packed CPU | kernel | heavy steps | largest charge | ratio |
|---|---:|---|---:|---:|---:|---:|---:|
| regular + product + literals | 25,253.9 s | 88 segments + 5 actions | 2,878.3 s | 637.2 s | 565 | 4.08 GB | 8.8× |
| characters (`X`) | 11,054.8 s | 4 tstart + 28 tstep + 4 texp + 12 pow + 24 char | 1,440.2 s | 297.6 s | 276 | 3.21 GB | 7.7× |
| `inv` (`I`) + `sqrt` (`Q`) | 425.8 s | 2 inv + 2 sqrt | 64.4 s | 10.9 s | 8 | 2.35 GB | 6.6× |

## Memory calibration (`calib-h8/`)

**First plan: segments of at most 8 heavy steps, no cap on nodes** (72 segments, up to 25 imports + exports).
The largest block of each kind was probed first:
- **`FullSeg_49` (8 heavy steps, 24 nodes) was OOM-killed at 4 GiB.**
- `FullSeg_47` (8 heavy steps, 21 nodes): 4.10 GB. `FullSeg_27` (8, 17): 3.60 GB. `FullSeg_33` (3, 14):
  2.71 GB. `FullSeg_34` (4, 6): 1.84 GB.
- These four fit about 0.57 GB + 0.125 GB per node held (import or export) + 0.13 GB per heavy step. At Full
  the nodes a process holds dominate its memory, not the heavy steps.
- The other kinds stayed far below the cap: action 2.08, character (2 keys) 3.06, power 1.93, Taylor (3
  steps) 2.54, `texp` 0.90, `tstart` 1.80, `inv` 1.90, `sqrt` 2.31 GB.

**Re-planned with `--seg-io=15`** (and `--heavy=8`): 88 segments, at most 15 nodes each.
- The segments were charged 1.62–4.08 GB. Two were above 3.6 GB: `FullSeg_14` (3.80 GB) and `FullSeg_37`
  (4.08 GB, 14 nodes, 8 heavy steps).
- The fit does not explain these two; other segments with 15 nodes and 8 heavy steps took 3.2–3.6 GB.
- A tighter cap (say 13 nodes) would give a margin, at the price of more processes.
- The calibration runs and the failed attempt are not counted in the totals. The final plan's 169 blocks were
  each run once.

**Python.** Both generator runs started before the orchestrator's Python rule:
- the first run (the mirror and the emission) took 65.7 CPU-min and 73 min of wall. Its RSS was 1.7 GB when
  sampled at 15 min; the peak was not recorded;
- the re-plan from the mirror cache took 30.3 CPU-min, at 0.8 GB at its end.
- The summary and the radius comparison ran under `py_capped.sh` (8 GiB, no swap, `nice -n 10`).

## Controls

Each new block kind was checked once with one exported radius lowered by one ulp (`full/ctl/`;
`scripts/packed/jet_low_ctl.py`):
- a `tstart` export (`FullTw_0_n`, `w`);
- a `tstep` export (`FullTay_1_n_3`, the partial sum at `m = 6`);
- a `texp` export (`FullTexp_1_n`, the exponential);
- a `pows` export from a power above 1 (`FullPow_1_n_3`, the power 5 from the power 3).

All four decide `= false`. The segment, action, character, `inv` and `sqrt` checks are those of M1, MEM and LOW,
which have their controls.

## Accuracy: the packed configuration against the landed configuration (not method against method)

The 5 wanted slots, both sides at degree 0 (`scripts/packed/jet_low_cmp.py --stage=Full`,
`full/FullRadii.{txt,json}`):

| slot | packed radius | landed radius | ratio |
|---:|---:|---:|---:|
| 7731 (`v0`) | 5.77e-23 | 3.04e-21 | 0.019 |
| 7732 | 3.48e-22 | 1.51e-20 | 0.023 |
| 7733 | 3.40e-22 | 3.22e-20 | 0.011 |
| 7734 | 2.87e-22 | 1.20e-20 | 0.024 |
| 7735 | 1.17e-21 | 4.13e-20 | 0.028 |

- **Radii.** The packed configuration's radii are 1.1–2.8% of the landed configuration's. At Full the landed
  radii are already small (the gap at Low was 12–15 orders).
- **Norm bounds.** The packed norm bounds agree with the landed weighted sup norms to at most 6e-8 relative.
- **Configurations.** The packed side is the dense 97 × 97 box (`|k|∞ ≤ 48`); the landed side is the trimmed
  cfgFull models. Only the tails beyond the box and the rounding reach the packed radius.
- **For the consumers.** The packed radii are below the landed ones on every wanted slot. The margin that
  matters is the downstream check, which cannot be measured until the consumer exists; the packed enclosures are
  box nodes, so a consumer needs the §12.2 bridge (unbuilt).

## The staged chain (Lean; `KAM/CertificateSharp/Packed/JetStage.lean`, M0 `cd937459`)

At cfgFull a whole Taylor sum in one process would hold 35–45 heavy steps of the 97 × 97 box, far above 4 GiB
(the Low exponentials of 45 heavy steps already took 3.07 GB on the 51 × 51 box). So the exponential is staged:
- **`TKey`**, the ledger keys of a staged exponential: `w = σ i 2π angleAt_j`, the Taylor term `w^m / m!` and the
  partial sum `Σ_{i ≤ m} w^i / i!` (`tkeyFn`). The chain's keys are `JKeyT = JKey ⊕ TKey`.
- **`jTStep`, `jTSteps`**: Taylor steps from any `(term, partial sum)` at `m` (the steps of `jTaylor`).
- **`jExpFin`**: the partial sum of degree `N` plus the remainder `jExpRem` (as `jExpNode`).
- **`JBlockT`** adds to `JBlockW` the blocks:
  - `tstart`: `w` and the constant `1` (the term and the partial sum at `m = 0`);
  - `tstep`: `k` Taylor steps from `m`;
  - `texp`: the exponential node from the partial sum of degree `N`;
  - `pows`: powers `m + 1 .. m + k` from the power `m` (the Low block started at `m = 1` only).
- **Soundness:** `jTStep_sound`, `jTSteps_sound`, `jExpFin_sound`, `JBlockT.sound`, `jChainT_sound` and
  `jChainT_slot` (every exported `(Sum.inl (Sum.inl j), nd)` encloses slot `j` of the program at the embedding).
- **Tests** (`JetStageTests.lean`): three staged steps from `m = 0` give exactly `jTaylor`'s nodes; so does a
  resumed run (one step, then two from `m = 1`); a wrong staging decides `false`.

The action block, the character blocks and the witnesses are those of Low (`JBlockT.lift`). The action slots
are split into blocks of 4 (`jActionsOk` on each part).

## Changes since `990dd97b`, all on `v2-packed-jet`

**Lean:** none since M0 (`cd937459`: `JetStage.lean`, `JetStageTests.lean`, the generated root).

**Scripts:**
- **`jet_low_gen.py`:**
  - `--seg-io=K`: at most `K` imports + exports per segment (the cut is decided slot by slot; a segment's exports
    are the slots read after it, or wanted);
  - a statement longer than 100 columns is wrapped after `.ok`.
- **`run_plan.sh`** (new): every block of a plan in order, one process at a time through `run_probe.sh`;
  resumable (a block whose `.cost` records `exit 0` is skipped).
- **`py_capped.sh`** (new): the orchestrator's rule for heavy Python (8 GiB cap, no swap, `nice -n 10`, wait while
  the user's anonymous memory is above 20 GB).

**Docs:** design §12.12 and this handoff.

**Receipts:** `docs/campaign/studies/V2-PACKED-JET-FULL/`:
- `full/`: the `.out`/`.cost` of the 169 blocks, `FullPlan.json`, `FullSummary.json`, `FullRadii.{txt,json}` and
  `axioms.txt`;
- `full/ctl/` (the 4 controls) and `full/base/` (the 2 baselines);
- `calib-h8/`: the first plan (`FullPlan-h8.json`) and its 13 calibration runs, with the OOM-killed `FullSeg_49`.

**Reproduce** (generation is untrusted Python and is not counted on either side):
```
python3 -I scripts/packed/jet_extract_low.py .lake/v2-packed-jet/lg00-gen-L20/state.pkl \
  .lake/v2-packed-jet/full.json --stage=Full
scripts/packed/py_capped.sh scripts/packed/jet_low_gen.py .lake/v2-packed-jet/full.json --stage=Full \
  --heavy=8 --seg-io=15 --char-keys=2 --char-io=12 --act=4 --taylor=3 --pows=2 \
  --cache=.lake/v2-packed-jet/full_mirror.pkl
bash scripts/packed/run_plan.sh 4G .lake/v2-packed-jet/full/FullPlan.json .lake/v2-packed-jet/full <logs>
scripts/packed/py_capped.sh scripts/packed/jet_low_sum.py FullPlan.json <logs> <run20e.tsv> \
  <lg00-cert>/KAM/LG00Cert/Full <plans.json>
scripts/packed/py_capped.sh scripts/packed/jet_low_cmp.py <state.pkl> FullPlan.json --stage=Full
```
(`jet_low_sum.py` names its landed total `landed_low_cpu_s` for either stage.)

## Checks

- **Targeted build** `lake build KAM.CertificateSharp.Packed.JetStageTests` (it builds `JetStage`):
  `Build completed successfully (3283 jobs)`. Its only warnings are in landed `KAM/Certificate/` modules, none in
  `Packed/`. All toy tests pass.
- **`#print axioms`:** `[propext, Classical.choice, Quot.sound]` for `jTStep_sound`, `jTSteps_sound`,
  `jExpFin_sound`, `JBlockT.sound`, `jChainT_sound` and `jChainT_slot`. `chain_sound` uses no axioms
  (`full/axioms.txt`).
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (4171 Lean files, 0 comparator configurations)` and
  `FROZEN-ANCHOR GUARD OK`. The ABI step fails as before: a frozen module's `.olean` is not built in this
  worktree (pre-existing). `gen_root_imports.py --check` exits 0.
- **Source limits:** `JetStage.lean` 418 lines, `JetStageTests.lean` 54; no line over 100 characters; no
  forbidden token; no `KAM/` change since `990dd97b`.

## Uncertainties

1. **The production assembly is unmeasured** (data module, one theorem, the consumer link), as for Low. At Full
   the data module matters more: the fixed part is 78% of the CPU.
2. **Memory margin.** Two segments took 3.80 and 4.08 GB under the 4 GiB cap, and the node-and-step fit does not
   explain them. A rerun on a busier machine could fail one of them; `run_plan.sh` resumes, and a tighter
   `--seg-io` gives a margin.
3. **Single runs** on a shared machine; run-to-run noise unmeasured.
4. **The by-kind landed split** assigns a module's cost evenly over its pieces, so it is approximate.
5. **The Taylor degree** (17, 22) comes from a float estimate in the generator; the kernel check holds for any
   degree. Not tuned.

## Errata and deviations

- **Errata:** no suspected defect in a pinned source.
- **Deviations:**
  - **The exponential is staged** (`JBlockT.tstart`/`tstep`/`texp`) rather than one `expo` block, for memory;
    powers are computed from any power (`JBlockT.pows`).
  - **The action slots are split** into blocks of 4.
  - **Python rule:** the two generator runs started before the rule and ran without the 8 GiB cap (above).

## Next (orchestrator's order)

1. **The rounding leaf conversion** (a new module; keep `CertFixed 128` and the landed embedding) and the
   `P = 64` measurement on the whole Low chain. At `P = 64` the digits and the literals narrow, which helps the
   fixed part as well as the kernel.
2. **The production pieces:** the shared data module (the largest single saving at Full: about 37% of the CPU
   is the per-process copy of the program, book and embedding), one theorem over all blocks with their order,
   and the link to the consumers.

## Owner questions (overnight mode: none blocked work)

1. **Memory margin at Full.** Keep `--seg-io=15` (169 blocks; largest 4.08 GB under the 4 GiB cap), or tighten it
   for margin at the price of more processes?
