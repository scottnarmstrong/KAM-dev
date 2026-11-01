# V2-PACKED-JET handoff: the first gate of the packed jet evaluator

Task: the orchestrator's overnight decision of 2026-11-01. "Design accepted: compute reduced values in the kernel
with boxOk (literals only as fallback); accept the larger Full box; the jet ledger shares the production data
module. ... start V2-PACKED-JET with the first gate (one Low segment of ~50 products at LG00 size, end to end,
measured against the landed segment), on branch v2-packed-jet from v2-packed-b3; new modules only."

The branch is `v2-packed-jet`, from `v2-packed-b3` at `475c7311`. It is local and was never pushed. The frames
work (V2-PACKED-FRAMES) is on its own branch `v2-packed-frames`.

## Result

- **The Lean is complete and sound for a packed jet segment**, on the standard axioms.
  `jSegOk_sound`: if the segment check passes and every imported node encloses its slot function
  `θ ↦ p.val n (z θ) j`, then every exported node encloses its slot function. Here `p` is the jet program, `z`
  any point map, and the slot semantics is the landed `Slp.val`.
  - **No literal inside a segment.** A box-by-box product is computed exactly on the window, then reduced to the
    box in the kernel: the candidate is computed (`zPC`), validated by one mask check (`boxOk`, with the new digit
    lemma `boxOk_sound`), and given its radius by the packed norm of the residual (`PEnc.reduceZ`).
  - **Fails closed.** Nothing about how the candidate was computed is assumed, so a wrong candidate fails the check.
- **The gate passes on LG00's data** (`lg00-cert` `fd82fef5`, its L = 20 generator state). It covers cfgLow slots
  [7099, 7292), measured against the landed modules of the same 83 segments:

  | | landed (run20e) | packed |
  |---|---:|---:|
  | live steps | 114 (54 product segments, 29 regular segments) | 114: 55 box-by-box products, 13 products by constants (reduced in place), 46 sums |
  | processes | 228 theorem modules | 23 sub-segments |
  | CPU (user + system) | **4,815.2 s** | **511.9 s** (279.1 s kernel, 449 s wall) |
  | largest charge | 5.27 GB | 4.29 GB (at the 4 GiB cap, `JSeg_5`) |

  - That is **9.4× less CPU on the range**.
  - **Production assembly is unmeasured.** The packed column counts the probes only. Each carries its own copy of
    the data (book, program, its ledger memos); a shared data module and the chain theorem over the
    sub-segments are not built.
  - **Per-process overhead.** About 7–10 s per process is start-up and data (control `JData_0`: 10.1 CPU-s,
    0.71 GB), roughly 200 s of the 512.
  - **What the landed column leaves out.** It counts the theorem modules only. The Low stage's literal modules
    (ledger `L` 2,197 s, product data `D` 119 s, ...) are not attributed to the range.
- **The design's cost model (§12.6) was optimistic. Recorded as §12.9:**
  - **Kernel time:** about 4.1 s per heavy step (product or reduce) inside a run, against 0.5 s estimated.
  - **Kernel memory:** about 0.5 GB per heavy step inside a run, against 30 MB estimated. The kernel keeps every
    intermediate of a declaration.
  - **Sub-segment size.** A process under 4 GB therefore holds at most 4 heavy steps, and fewer when it carries
    many ledger memos; the gate needed 23 sub-segments where the design assumed one.
  - **One process fails.** The whole 55-product segment in one process is OOM-killed (`profile/OneProcess_*`).
  - **Standalone costs.**
    - A product with its reduce: 0.65 s and about 100 MB (`profile/M6`);
    - each of its two packed norms: about 0.8 s and 40 MB (`M4`, `M5`).
    - So the run keeps far more than the sum of its operations (`M9`: the run of 4 products without radii holds
      1.9 GB). This is the next engineering target.

## Files (all new except the generated root)

- **`KAM/CertificateSharp/Packed/Box.lean`** (293 lines).
  - `boxDigits`, and `boxPat`, the closed form: a row `periodic w D₁ v` repeated `D₀` times with period `w S`
    (`natPack_boxDigits`);
  - `natPack_land` (`AND` of packings), `packSum_zipWith_sub`;
  - `boxOk` and `boxOk_sound` (`∃ d, SRep L (2^l) Z d`), `inBox_of_mod`, `boxLen_eq_denseLen`.
- **`KAM/CertificateSharp/Packed/StageZ.lean`** (128 lines).
  - The candidate: `zPart`/`zPC` (offset digits, `digitShift`, box mask and move, offset removed), and the
    residual `zRes`;
  - `PEnc.stageRep`: the residual stage for any candidate with a `PCRep`, with the radius `r + pnorm(residual)`
    and the norm bound `pnorm(candidate)` computed;
  - `PCRep.ofBoxOk`, `PEnc.reduceZ`, `PEnc.weaken`.
- **`KAM/CertificateSharp/Packed/JetNode.lean`** (338 lines).
  - The book `JBook`, its guards `jBookOk` (once per segment) and `JBookFacts`;
  - nodes `JNode` and `JEnc`;
  - the operations `jUp`, `jAdd`, `jRedW`, `jRed`, `jMul`, each with its soundness;
  - `normOk_mono`, `mulLoad_mono`.
- **`KAM/CertificateSharp/Packed/JetSeg.lean`** (248 lines).
  - The slot semantics: `slpVal_eq_step`, `slpVals_take_getD`, `slpVal_add`, `slpVal_mul`;
  - the run: `jOp`, `jPost`, `jRun`;
  - the check `jExportOk`, `jSegOk`;
  - the soundness: `jOp_sound`, `jRun_sound`, `jSegOk_sound`.
- **`KAM/CertificateSharp/Packed/JetIngest.lean`** (45 lines): `respaceLin`, `respace`, `jIngest`.
  - A ledger node is written as its 2,601 box digits at a narrow width, and the kernel spreads them to the
    352-bit layout.
  - This is data ingestion, not a check: the export check compares the computed value with the ingested one
    exactly.
- **`KAM/CertificateSharp/Packed/JetTests.lean`** (85 lines). A toy segment (`n = 2`, box of half-width 1):
  - an import sum, and a box-by-box product reduced in the kernel: passes;
  - a digit off by one, or a rounding shift above `smax`: fails;
  - a `jIngest` example.
- **`KAM/Root/CertificateSharp.lean`**: regenerated (six imports).
- **Scripts (new):**
  - `scripts/packed/jet_extract.py`: the slot range from LG00's generator state (unpickled with lg00-cert's
    tooling, written to JSON);
  - `scripts/packed/jet_gate_gen.py`: the bit-exact mirror of the run, the book (two passes), the probes and their
    cut into sub-segments (`--heavy`, `--split`);
  - `scripts/packed/jet_landed.py`: the landed modules of the range and their run20e cost;
  - `scripts/packed/jet_gate_sum.py`: the totals.
- **Docs:** this handoff; design §12.8 (decisions recorded) and §12.9 (the gate).
- **Receipts:** `docs/campaign/studies/V2-PACKED-JET-GATE/`.
  - `segments/` (23 sub-segments), `controls/`, `profile/`;
  - `JetGate.json` (book and plan), `Landed.json`, `Summary.json`.

## Design as built (against §12)

- **Nodes.**
  - Box nodes live on `Lb` (half-width 25: 51 × 51, row stride 101, 352-bit slots); constants live on the
    one-slot `LU0`.
  - Each node carries its load and its scale `2^e`.
  - Sums bring both operands to the larger scale by exact unit shifts. A product by a constant stays on the box and
    is reduced in place to `2^128`. A box-by-box product goes to the window (101 × 101) and is reduced at once.
- **The book is checked once per segment.** `jBookOk` checks the layouts, the windows, the zero slots, and three
  norm guards at the largest load and shift. Each operation then only compares its load and shift with the book.
- **Steps and exports.**
  - The steps carry only untrusted target scales.
  - An export must equal its ledger entry (value, layout, load, scale) with a radius and a norm bound below the
    entry's.
- **The gate's imports.** They are LG00's landed cfgLow models, rounded to scale `2^128` on the box: radius =
  landed radius × `(2π)^deg` (upper) + the exact rounding. They are the **hypotheses** of `jSegOk_sound` and are
  not checked; in a full packed chain they are the exports of earlier packed segments.
- **Chaining.** Each sub-segment's imports are earlier memos and its exports the next ones' imports (the same
  literals). So the 23 checks chain by `jSegOk_sound`, in slot order.
- **Not built yet (§12.7 items 2–5):**
  - constants with `(2π)^deg`, actions, characters, `inv`/`sqrt`/`exp`;
  - the chain theorem over a plan;
  - the consumers;
  - the `Full` chain.

## Checks and their output

- **Targeted builds** (`nice -n 5 systemd-run … MemoryMax=4G lake build KAM.CertificateSharp.Packed.<M>`) of
  `Box`, `StageZ`, `JetNode`, `JetSeg`, `JetIngest` and `JetTests`: `Build completed successfully` each, with
  0 errors and 0 warnings in `Packed/`.
- **Toy tests pass.** The opposite claim fails in the kernel: a scratch file outside the repo, a kernel error.
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of `boxOk_sound`,
  `PEnc.reduceZ`, `jMul_sound`, `jRed_sound`, `jSegOk_sound` and `slpVal_mul`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (3686 Lean files, 0 comparator configurations)` and
  `FROZEN-ANCHOR GUARD OK`.
  - Only the pre-existing ABI step fails (`FixedSunPlanetaryKAM.olean`), as in B3b.
  - `gen_root_imports.py --check` exits 0.
- **Source limits.** No forbidden token and no `set_option` in the modules; no line over 100 characters; the
  largest file has 338 lines.
- **Additivity.** Against the merge base with `main`, the only changes under `KAM/` are the six added
  `Packed/*.lean` and the generated `KAM/Root/CertificateSharp.lean`.

## Gate on LG00's data

**Method.**
- **Generation.** `python3 -I scripts/packed/jet_extract.py <state.pkl> <plans.json> 7099 7292 <seg.json>`, then
  `V2P_GATE_DIR=… python3 -I scripts/packed/jet_gate_gen.py <seg.json> --heavy=4 "--split=1,3,6;4,9;10"`. The
  state is lg00-cert's `gen_L20/state.pkl`, copied to `.lake/v2-packed-jet/lg00-gen-L20/`.
- **Running.** `run_probe.sh 4G`, one process at a time, `LEAN_NUM_THREADS=1`. Every probe proves its statement
  by `decide +kernel`.
- **Mirror.** The Python mirror runs the whole range in about 70 s. It asserts every `boxOk` and the ingestion of
  every literal.

**Book.**
- `P = 128`, `q = 24`, slot width 352;
- reduced digits ≤ `2^140`; product loads `< 2^277`, in-place loads `< 2^268`; rounding shift 128;
- window numbers 3.6 Mbit.

**Cut.** Sub-segments of at most 4 heavy steps. Those carrying the most memos were halved again (by heavy steps,
or by steps when they had at most one heavy step).

**Totals** (`Summary.json`):
- 23 processes, all pass;
- 511.9 CPU-s, 279.1 s kernel, 449.4 s wall;
- 68 heavy steps (4.1 s kernel and 7.5 CPU-s each);
- the largest charge 4.29 GB (`JSeg_5`, 23 memos); the others 2.1–4.1 GB.

**Controls:**
- `JSegMutR_22` (the last export's radius one ulp, 2⁻¹²⁸, lower) decides `= false`;
- `JSegMutX_22` (its lowest box digit off by one) decides `= false`;
- `JData_0` is data only.

**Values.** Export radii are ≤ 3.5·10⁻¹⁰ and norm bounds ≤ 1.9·10⁻⁴.

## Uncertainties

1. **Production assembly** (a shared data module, the chain theorem over sub-segments and plan) is unmeasured.
   The per-process data overhead (about 200 s here) is where it would save.
2. **Memory is the binding constraint.** Inside a run the kernel keeps about 0.5 GB per heavy step, against
   about 0.15 GB standalone. Until that is understood, segments are 4 heavy steps, the ledger grows with the
   cuts, and three pieces sit at the cap.
3. **Ledger volume.** Box nodes keep 2,601 modes (h = 25), more than cfgLow's diamond: about 515 landed terms per
   entry. So a packed memo is about 5× a landed one.
4. **Imports are hypotheses.** The import radii come from the landed models; they are not checked here.

## Errata and deviations

- **Suspected errata in pinned sources:** none.
- **Deviations:** none from §12's soundness design.
- **Measured against the cost model.** It is worse: time about 8×, memory about 15× per heavy step. Recorded in
  design §12.9.

## Owner questions (overnight mode: none blocked work)

1. **Next step.** Either memory engineering of the run first (aim: about 0.15 GB per heavy step, i.e. 15–20
   steps per process), or the chain theorem and the remaining operations at today's 4-step cut (9.4× on this
   range).
2. **The shape of exported memos.** Keep the box, or add an export-shaping reduce to cfgLow's diamond (about 2×
   less ledger)?
3. **Precision of the Low chain.** Is `P = 128` needed for Low, given the torsion tolerance? `P = 64` would halve
   the numbers and the memos.

V2-PACKED-JET GATE DONE
