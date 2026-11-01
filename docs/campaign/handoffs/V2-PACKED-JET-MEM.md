# V2-PACKED-JET-MEM handoff: the kernel memory of a packed jet run

Task: the orchestrator's overnight decisions after V2-PACKED-JET GATE, on `v2-packed-jet`:
1. Engineer the kernel memory first. Target 15–20 heavy steps per process. Find what holds the ~0.5 GB per
   product: retained terms, sharing, cached reductions, the Nat literal hashing.
2. Memo shaping to the cfgLow mode set: after (1), if cheap.
3. `P = 128` for Low: decide by measurement only.

## Result

- **Target exceeded.** The whole LG00 range of the first gate passes in one process: 68 heavy steps, 29.0 CPU-s,
  3.90 GB.
- **Chosen setting: 34 heavy steps per process.** The range takes 2 processes, 54.9 CPU-s (8.4 s kernel), at most
  2.65 GB.
- **Against the first gate.** That gate needed 23 processes, 512 CPU-s and 4.29 GB for the same 68 heavy steps;
  the chosen cut is ≈ 9.3× less CPU.
- **Against the landed range** (228 modules, 4,815 CPU-s), this is ≈ 88×.
  - The landed column counts theorem modules only; each packed process also elaborates its own ledger data.
  - Production assembly is unmeasured.
- **All runs are on LG00's data** (`lg00-cert` `fd82fef5`, cfgLow slots [7099, 7292), the same 53 imports and 35
  exports):

  | cut | processes | heavy steps per process | CPU (user + sys) | kernel | largest charge |
  |---|---:|---:|---:|---:|---:|
  | first gate (before) | 23 | ≤ 4 | 511.9 s | 279.1 s | 4.29 GB |
  | one process | 1 | 68 | 29.0 s | 6.0 s | 3.90 GB |
  | **≤ 34 (chosen)** | 2 | 34 | **54.9 s** | 8.4 s | **2.65 GB** |
  | ≤ 20 | 4 | 20, 20, 20, 8 | 71.3 s | 11.1 s | 2.22 GB |

- **The kernel now spends 0.09–0.16 s per heavy step.** The rest of the CPU is the elaborator reading the
  data: the data-only controls take 19.1 CPU-s at 0.95 GB (cut 34) and 25.2 CPU-s at 1.07 GB (whole range).
- **Controls** (the radius one ulp lower; the lowest box digit off by one) decide `= false`, both on the
  one-process segment and on the last sub-segment of the 34-step cut.

## What held the memory (all measured; `docs/campaign/studies/V2-PACKED-JET-MEM/profile/`)

The packed arithmetic was never the problem.
- A product with its reduce and both norms, standalone and forced (`XSF1`, `XSF2`): about 0.6 s and 0.1–0.2 GB
  with ingestion included. Without ingestion, about 5–20 MB.
- The run kept far more for two reasons.

1. **The program read: about 0.4 GB per step.**
   - **Alone** (`XP`: `lgProg.ops.getD 7291`): 4.5 s and 1.1 GB of kernel. `XPA` (`drop 7291`) and `XPL`
     (`length`) are the same order.
   - **Narrowed down.**
     - A 91-step walk inside one 200-op chunk is negligible (`XPB`), and so is a 399-step walk across one append
       (`XPC`).
     - The generator wrote `ops_0 ++ ops_1 ++ … ++ ops_36`, which Lean parses left-nested (`++` is `infixl`).
       So every cell of the first chunk passes through 36 appends: quadratic in the chunk count, and every
       intermediate is cached.
     - And `jRun` read `p.ops.getD i` from slot `0` at every step.
   - **Fix:**
     - the generator now right-nests the appends;
     - `jSegOk` takes the segment's `start` and runs on `p.ops.drop start` (computed once, shared), reading
       `getD (i - start)` under `start ≤ i` (`getD_drop_sub`, `jOp_sound`);
     - the drop costs 0.16 s (`O_K0`).
2. **Literal ingestion: 73 MB and 0.44 s per imported node** (`I5`/`I20`).
   - **The cause is the spreading, not the literals.** Forcing the narrow literals themselves is negligible
     (`L5`/`L20`). The cost is `respace`, one kernel operation per digit (about 15k per part).
   - **Fix: `jSpread`.** It works in about 18 whole-number steps, first the digits, then the rows. Each step
     moves the upper half of every block by one closed-form mask, one multiplication and one addition.
   - **Shared masks.** Literal widths are rounded up to multiples of 8, so the masks are shared (6 width classes
     here), and identically zero parts (most imaginary parts) are written `0`.
   - **Cost now** (`J5`/`J20`, before the zero-part change): 27 MB and 0.04 s per node.

**What remains.**
- In the run without radii (`Q_K10`/`Q_K30`), a heavy step now costs about 33 MB and 0.08 s, the ingestion of its
  operands included.
- In the whole range with radii, the kernel adds 2.7 GB over the 1.2 GB data plateau: about 1.2 GB for the 88
  ingested memos and about 1.5 GB for everything else.
- **The Nat literal hashing was not a factor.** Once the program walk and the per-digit spreading were removed,
  the kernel time per heavy step fell to 0.09 s. So the hash degradation, if present, is not material here, and
  it was not investigated further.

## Changes (all on `v2-packed-jet`, in modules new on this branch)

- **`KAM/CertificateSharp/Packed/JetSeg.lean`.** `jOp`, `jRun` and `jSegOk` take the segment's start and read
  from `p.ops.drop start`. Added `getD_drop_sub`; `jOp_sound`, `jRun_sound` and `jSegOk_sound` are restated
  accordingly.
- **`KAM/CertificateSharp/Packed/JetIngest.lean`.** `respace`/`jIngest` are replaced by `spreadStep`,
  `spreadAux` and `jSpread`.
- **`KAM/CertificateSharp/Packed/JetTests.lean`.** Updated: the segment tests pass the start, and the `jSpread`
  example.
- **`scripts/packed/jet_gate_gen.py`.**
  - It emits right-nested appends, the `jSpread` literals (width classes, zero parts `0`) and the segment
    start.
  - Default `--heavy=34`; `--split` takes rounds.
  - Its mirror asserts every ingested literal.
- **`scripts/packed/run_probe_trace.sh`** (new): `run_probe.sh` plus a memory trace every 0.1 s.
- **`scripts/packed/jet_gate_sum.py`:** the data control is optional.
- **Docs:** design §12.10; this handoff.
- **Receipts:** `docs/campaign/studies/V2-PACKED-JET-MEM/`.
  - `profile/`: the isolating probes, with traces;
  - `cuts/one`, `cuts/h34`, `cuts/h20`: each sub-segment's `.out`/`.cost`/`.trace`, the controls,
    `JetGate.json` and `Summary.json`.

## Checks

- **Targeted builds** of `JetSeg`, `JetIngest` and `JetTests`: `Build completed successfully`, 0 errors, 0
  warnings in `Packed/`. The toy tests pass (segment, its two failing controls, and `jSpread`).
- **`#print axioms jSegOk_sound`:** `[propext, Classical.choice, Quot.sound]`; likewise `boxOk_sound`,
  `PEnc.reduceZ`, `jMul_sound`, `jRed_sound` and `slpVal_mul`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (3692 Lean files)` and `FROZEN-ANCHOR GUARD OK`; the
  ABI step fails as before (pre-existing). `gen_root_imports.py --check` exits 0.
- **Source limits:** no forbidden token, no line over 100 characters, files at most 338 lines. Additivity is
  unchanged: only new `Packed/*.lean` and the generated root.

## Decisions 2 and 3

- **(2) Memo shaping to the cfgLow set: not cheap with the dense spreading, deferred.**
  - Ingestion is now cheap, so shaping would save mostly elaboration: the literal source, now the dominant CPU.
  - The literal is dense in the 51 × 51 box, and the cfgLow diamond (ℓ¹ ≤ 24) has 1,201 of its 2,601 keys. So
    shaping needs two new pieces:
    - an export reduce to the diamond, with a residual norm;
    - a diamond-dense literal with its own spreading (rows of varying length).
  - Estimated gain: about 2× on the ledger source.
- **(3) `P = 128` for Low: not decided.**
  - This gate cannot decide it. A lower precision must pass the same downstream checks: the packed torsion
    (B3b) on the chain's `DX_H ∘ K`/`DH ∘ K` boundary, which needs the whole Low chain.
  - It is measurable once the chain theorem and the remaining operations exist (§12.7).
  - A `P = 64` run of this segment would measure only the cost side: fewer bits, about half the literals.
    Owner question 2.

## Owner questions (overnight mode: none blocked work)

1. **Next.** Either the production data module (now the dominant CPU), or the chain theorem and the remaining
   operations (constants with `(2π)^deg`, actions, characters, `inv`/`sqrt`/`exp`) toward the whole Low chain.
2. **Precision.** Run the cost side of `P = 64` on this segment now, or wait for the whole chain, where the
   torsion check decides it?

V2-PACKED-JET-MEM DONE
