# SO-KPERF: where one packed shard check spends kernel time and memory

Track SO, study (measurement only; no landed Lean module changed). Probes and generator: `.drafts/kperf/`
(`gen.py` builds every probe from SO-DATA-2's literal shard `PSR<R>.lean`; `run.sh` runs one probe alone under
`systemd-run -p MemoryMax=10G -p MemorySwapMax=0`, later also under the shared kernel-probe `flock`).
Stopped early on the orchestrator's instruction (SO-PACKFIX implements decision D34 with its own profiling).

## Method
- Shard: the middle shard of `[0,10]` A0·A0 (rr part), the same as SO-DATA-2. blockRows 4: L = 708, 90 pairs,
  s = 89. blockRows 8: L = 1416, 45 pairs, s = 44. w = 658, scale = 330.
- Every probe has the same single light import, `KAM.Certificate.Poly.Advice`, and the same data defs. Each
  probe states `decide +kernel` of one part. Results are forced against literals: packed integers are compared
  through their residues mod 2^521−1 computed by a Python replica, and the window sums through exact literals.
- Cost of a part = probe minus its baseline, which elaborates the same data with `True := trivial`.
- Peak = cgroup `anon`, sampled every 1 s. Wall time includes elaboration (the baseline).

## Per-part table, blockRows 4 (baseline `none`: 87 s, 0.68 GB)

| part (probe) | wall | peak | part cost (Δ wall / Δ peak) |
|---|---:|---:|---|
| whole `checkShard` (`full`) | 149 s | 6.35 GB | **+62 s / +5.7 GB** |
| block lengths `packLenEq` ×181 (`len`) | 95 s | 1.63 GB | +8 s / +0.95 GB |
| `packShift` of all 180 factor blocks (`pack`) | 102 s | 2.99 GB | +15 s / +2.3 GB |
| `packShift` of the advice window (`packw`) | 86 s | 0.72 GB | ≈ 0 |
| 90 big multiplications + sum, literal packed inputs (`mul` vs its own literal baseline `lits` 386 s / 0.75 GB) | 384 s | 0.75 GB | **≈ 0 s / 0 GB** |
| `shardFits` (`fits`) | 110 s | 3.49 GB | **+23 s / +2.8 GB** |
| `reconFitsAux` with `shardLogs` (`recon`) | 89 s | 0.72 GB | +2 s / ≈0 |
| `shardLogs` (`inBox`) on all 1,415 slots (`logs`) | 89 s | 0.77 GB | +2 s / +0.1 GB |
| `intSlotsBound` with constant logs (`dec0`) | 109 s | 0.87 GB | +22 s / +0.2 GB |
| `intSlotsBound` with `shardLogs` (`dec`) | 110 s | 0.98 GB | **+23 s / +0.3 GB** |
| prototype balanced-tree pack `packD` (`packD`) | 119 s | 3.97 GB | +31 s / +3.3 GB (worse) |
| prototype divide-and-conquer decode `slotsD` (`decD`) | 101 s | 0.87 GB | **+13.5 s** / +0.2 GB |
| `full` with `slotsD` + `packD` (`fullD`) | 149 s | 7.28 GB | +62 s / +6.6 GB |

The `len`, `pack` and `fits` rows each force the block lists from scratch, so their memory overlaps; they
do not simply add.

## blockRows 8 (baseline `none`: 118 s, 0.71 GB; the run was stopped after three parts)

| part | wall | peak | part cost |
|---|---:|---:|---|
| whole `checkShard` | 184 s | 9.95 GB | +66 s / +9.2 GB (no margin; SO-DATA-2 saw the same) |
| `packShift` of the 90 blocks | 144 s | 5.27 GB | +26 s / +4.6 GB |
| `shardFits` | 155 s | 4.01 GB | +37 s / +3.3 GB |

## Sparse-block prototype, blockRows 4 (baseline `snone`, the same data plus sparse `(slot, c)` blocks: 209 s, 1.29 GB)

The prototype blocks list only the nonzero slots: 9,001 of 63,720 slots per factor are nonzero (14 %). The
pack is `packSp` (shifts by `w·slot` on positive and negative parts). The fit guard is `fitsSp` (sorted, in
range, sparse max).

| probe | wall | peak | part cost |
|---|---:|---:|---|
| force every dense element (`foldl natAbs` over A, Bq) | 221 s | 2.29 GB | +12 s / +1.0 GB |
| sparse pack of all 180 blocks | 218 s | 1.80 GB | +9 s / +0.5 GB |
| sparse fit guard | 218 s | 1.55 GB | +9 s / +0.26 GB |
| **sparse shard check, landed `intSlotsBound`** | 254 s | 2.56 GB | **+45 s / +1.27 GB** |
| **sparse shard check, `slotsD` decode** | 235 s | 2.52 GB | **+26 s / +1.23 GB** |

## Diagnosis
1. **Memory comes from walking the dense, run-length-coded factor blocks, not from arithmetic.**
   - The packed multiplications cost nothing measurable (`mul` ≈ `lits`).
   - Each walk over the 127k dense elements of A and Bq (`unzero`, `List.replicate`, `++`, then
     `packLenEq`, `packShift`, and the `flatten` and `packMaxAbsAux` of `shardFits`) costs 1–3 GB at
     blockRows 4. A dense element is mostly a zero produced by `replicate`.
   - The kernel keeps every intermediate list term (about 10–20 KB retained per element). So the peak
     scales with the block size: 4.6 GB for the pack alone at blockRows 8. This is why a 12-pair shard at
     blockRows 32 exceeds 13.6 GB.
2. **Time comes from the slot decode.** `intSlotsBound` peels one slot at a time with `Int` `%`, `/` and
   `slotRep` on the whole remainder: n steps on an O(n)-bit integer, which is quadratic. It took 22 s for
   1,415 slots (about 16 ms per slot). The per-slot `shardLogs`/`inBox` adds little (+1 s).
3. **Comparison with SO-REPLAY2.** It measured a different implementation:
   - Its prototype `KAM/Certificate/Prototype/Packed.lean` (branch `inp-soreplay`) packed by **balanced
     shift trees** (`soShLoop`/`soPackRows`) over rows of zigzag `Nat` literals with no RLE.
   - It bounded slots with a **divide-and-conquer mask/shift** on an offset `Nat`
     (`soSlotsBoundSh`: `&&&`, `>>>`), at about 2.5 s per 16,384-slot window (about 0.15 ms per slot,
     roughly 100× cheaper per slot than our `intSlotsBound`).
   - It had none of the guards added since: `shardFits`, `reconFits`, `shardLogs`, `packLenEq`.
   - It timed only the kernel (profiler), with data in an imported module.

   The ~50× gap is therefore mainly:
   - (a) the linear `Int` peel decode in place of the balanced `Nat` mask/shift tree;
   - (b) the RLE dense list representation with several full walks (length, fit, pack), which drives
     memory;
   - (c) SO-DATA-2's per-pair figure including the elaboration of the literal data (58–87 s of the 149 s).

   The added guards themselves are cheap *except* `shardFits`, because it re-walks and flattens the dense
   blocks. A balanced *pack* tree does not help here (`packD` is worse): packing is not limited by
   carry-chain arithmetic but by the element walk.

## Candidate fix and measured gain
- **(F1) Sparse factor blocks.**
  - Pack and bound the factors directly from `(slot, c)` terms. The real factor is a `CertPoly` term list, so
    the dense `dense`/`cut` lists need never be built.
  - Measured: shard memory 5.7 → 1.2 GB (×4.6 less) and time 62 → 45 s at blockRows 4.
  - Memory no longer grows with the number of zero slots, so larger blocks become feasible again (not
    measured).
- **(F2) Divide-and-conquer decode.** Split the remainder at the balanced residue mod 2^(w·k). This is my
  `Int` prototype `slotsD`, measured 23 → 13.5 s. Better would be REPLAY2's offset-`Nat` mask/shift form,
  which on its numbers should be ≈ 0.2–0.5 s per window (not measured here).
- **Together (measured F1 + `slotsD`): +26 s and 1.2 GB per 90-pair blockRows-4 shard**, against +62 s and
  5.7 GB.
- **Proof impact.** The signed statements (`checkShard_sound`, `checkPackedProduct_*`, the frozen
  theorems) do not change.
  - **F2** needs one new soundness lemma, `slotsD_sound`, with the same conclusion as
    `intSlotsBound_sound`. It follows by induction from `intSlotsBoundAux_sound` and `packSum_append`, since
    any split is sound and no completeness is needed.
  - **F1** needs a sparse pack lemma: `packSp` of the terms equals `packSum` of the dense block. It also
    needs a sparse `shardFits` equivalence, or the guard rephrased on terms, and a tie between `PackedAdvice.cut`
    of the dense factor and the term blocks. These touch `Poly/Packed.lean` and `Poly/Advice.lean`
    (`shard_reconstruct` premises), and the place in `checkPackedProduct` where `cut (dense …)` is formed.

## Projection (lunar, both tori)
- At blockRows 4, with F1 and the `Int` D&C decode: about 26 s of kernel time per full 90-pair shard. The
  9,149 + 9,402 shards include many edge shards with fewer pairs, so this gives **≈ 25–65 CPU-h kernel for
  both tori**, down from SO-DATA-2's 100–170 CPU-h, under 2.6 GB per shard.
- The remaining time is dominated by the per-slot decode. With REPLAY2's `Nat` mask/shift decode (F2′) and
  sparse blocks at larger blockRows (fewer shards, which the memory now allows), the estimate is
  **≈ 5–15 CPU-h**. That is a model estimate, not measured.
- Elaboration of the data is extra (SO-DATA-2: 395 s per torus for the modules, plus literal blocks).

## Recommendation
Implement F1 (sparse/term-driven packing and fit guard) and F2′ (balanced `Nat` mask/shift slot decode),
keeping the signed statements. Re-measure blockRows 8–32 under the cap before fixing the layout. Drop
`packD`: balanced packing of dense lists gives no gain.

## Uncertainties
- Single runs on a shared machine; peaks are sampled.
- The blockRows-8 decode and sparse probes were not run (stopped on instruction).
- The 5–15 CPU-h figure is extrapolated from REPLAY2's per-slot decode rate.
