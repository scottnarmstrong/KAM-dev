# Gate A receipts (V2-PACKED-SHARP): notes

- **Run:** `run_tree.sh TP gate` equivalent, log directory `runA` of the worker's scratchpad, 2026-11-01
  14:35:22 (first build) to 15:03:35 UTC (last ledger row); 353 modules, all exit 0, cap `4G`.
- **Harness version.** The run was started three times (the ledger keeps every passed module, so restarts only
  resume). The last start (14:41:55 UTC) ran `scripts/packed/run_packed.py` as committed in `7ca5dc0a` but
  WITHOUT that commit's own-section kernel parser, which was added to the working tree at about 14:50, after the
  process had loaded the script. The earlier starts ran the `228747b5` version. Every version wrote the same
  ledger columns except the kernel time.
- **Kernel column corrected (AUDIT-V2-PACKED-SHARP-1 F1).** The old parser summed every `type checking took`
  line of a module's Lake output, and Lake replays the logs of the module's imports. For `LG00Packed.TP.GateA` it
  therefore recorded 19.82 s, the sum of `FrameL`, `FrameN` and `FrameT`. GateA's own section has no such line
  (it proves a conjunction by term), so its kernel time is 0. `ledger.tsv` here is the run's ledger with the kernel
  column recomputed from the raw logs by the committed parser (`run_packed.row`). Only that row changed
  (19.82 → 0.00), and the kernel total is 88.93 s, as in `summary.txt`. The raw, uncorrected ledger is the run's
  `runA/ledger.tsv` (worker's scratchpad).
- **What the gate shows** (AUDIT-V2-PACKED-SHARP-1 F3). The gate's own modules pass. Gate A does not establish
  `refinedTestPackedS … lg00Cert lg00RW = true` or T′'s `FrameMajorants`. It decides the final frame sums on memos
  it does not verify, and `refinedCoreS`. The memos' verification (the stage conjuncts shared with
  `checkTorsionR`), `checkHamClaim` and `checkFrameOmega` belong to the B3b route.
- `GateA.lean.txt` is the module as rebuilt after the F3 docstring change (the statement and proof are
  unchanged).
