# SO-PACKFIX handoff (owner ruling D34; track SO)

Branch `inp-sopackfix`. Status: **done**. A blockRows-32 shard (the current data) now fits under the 10 GB cap
with margin: **4.55 GB peak, 235 s wall, +45 s and +3.5 GB of kernel work over the data-only baseline**. Before the
fix it was OOM above 13.6 GB.

Signed statements are unchanged and the advice DATA format is unchanged. Two deviations from the corrected brief are
reported below: a fallback route, and the restored balanced packing of the dense window, which is backed by
measurement.

## Files (lines)
- `KAM/Certificate/Poly/Sparse.lean` (new, 477): the F1 sparse route and its bridge to the dense check.
- `KAM/Certificate/Poly/Packed.lean` (624): balanced `packShift` and the F2′ decode.
- `KAM/Certificate/Poly/Advice.lean` (711): `shardFits` without `take`/`flatten` copies.
- `KAM/Certificate/Poly/MulPacked.lean` (535): `packedRealProduct` takes the sparse route first.
- `KAM/Certificate/Tests/Packed.lean` (417): sparse tests, positive and negative.
- `.drafts/packfix/`: probe generators (`gen.py`, `gensp.py`, `reblock.py`), the capped runner (`run.sh`, which
  takes the shared probe lock) and logs. The generated multi-MB probe `.lean` files are not committed; regenerate
  them with `python3 reblock.py 32` (3.5 min), then `gen.py R` / `gensp.py R`.
- `KAM.lean` must be regenerated for the new module (`scripts/gen_root_imports.py`). I did not touch it (rule 10),
  so lint reports "KAM.lean is out of date".

## Bodies changed, lemmas re-proved (all signed statements unchanged)
- **F1 (sparse, term-driven).** `Poly/Sparse.lean`:
  - `spBlocks` cuts strictly increasing global `(slot, value)` terms into blocks in one `takeWhile`/`dropWhile` pass.
  - `spPack` packs a block by a balanced join of nodes `(lowest slot, pos, neg)`. Each intermediate is only as
    wide as its slot range.
  - `spMax` is the term maximum, used by the fit guard.
  - `checkShardSp` is the window length, fit `2(s+1)·L·mA·mB < 2^w`, `reconFitsAux`, and `intSlotsBound` on the
    sparse shard sum. `checkPackedSp` checks shape, ascending slots below `denseLen`, the advice count, and every
    shard.
  - **Bridge `checkPackedSp_dense`:** a passing sparse check ⇒ `checkPackedProduct adv (packFill la.denseLen 0 ea)
    (packFill lb.denseLen 0 eb) = true`. Supporting lemmas:
    - `packSum_cut_packFill`: dense block `i` of the cut fill packs to `spPack` of sparse block `i`.
    - `spBlocks_getD` (block = filter of its slot range), `sum_packSlotTotal_window`, `getD_getD_of_flatten`.
    - `packCutAux_length_eq`, `PackedAdvice.cut_length_eq` (⌈N/L⌉ blocks).
    - `natAbs_packSlotTotal_le`, `maxAbs_take_cut_packFill_le` (the fit guard).
    - `checkShardSp_dense`.
  - **Wiring.** `packedRealProduct` (body only) runs `checkPackedSp` on `PackLayout.slotTerms` (the same slots
    `dense` fills) when every key is slotted (`allSlots`). It falls back to the old dense route otherwise.
    `packedRealProduct_sound` is re-proved: the old argument is now `packedRealProduct_core`, and the sparse branch
    reaches it through `PackLayout.dense_eq_packFill` and `checkPackedSp_dense`. `CertPoly.mulPacked(_sound)` and
    everything downstream are untouched.
  - **Data.** The data format is unchanged: F1 derives the sparse blocks from the factor terms the checker already
    has. The advice windows stay RLE dense lists.
- **F2′ (decode).** `intSlotsBound` (body):
  - `0 < w`, `0 ≤ X + slotOffset`, then `natSlotsSh` on the offset `Nat`: mask (`&&& (2^k - 1)`) and shift
    (`>>> k`) halves, with leaves of 16 digits (`natSlotsAux`) and a fuel-64 digit-by-digit fallback, so the value
    is exact regardless.
  - `slotOffset w len = 2^(w-1)·(2^(w·len)-1)/(2^w-1)` (`slotOffset_eq` via `Nat.geomSum_eq`).
  - `intSlotsBound_sound` is re-proved with the identical conclusion, via `natSlotsAux_sound`, `natSlotsSh_sound`,
    `packSum_map_sub` and `packSum_replicate`.
- **`packShift` (body), balanced.** 16-slot leaf chunks as `Nat` pairs (`packLeavesAux`), then pairwise merge levels
  with doubled width (`packMerge`, `packTree`), with a linear fallback (`packFold`). `packShift_eq` is re-proved (via
  `pairVal`).
- **`shardFits` (body).** `packLenLeBlocks` / `packMaxBlocks` replace `take`/`flatten`/`all`. Re-proved:
  `slotsBounded_shardConv`, via `packLenLeBlocks_eq` and `packMaxBlocks_eq`.

## Deviations (please review)
1. **Balanced packing of the dense advice window, against the correction's point (1).** SO-KPERF measured `packD`
   only at blockRows 4, where a block is 0.47 Mbit. At blockRows 32 the window has 11,327 slots × 658 bits =
   7.4 Mbit. The linear accumulator keeps every intermediate literal, which is quadratic in bits.
   - Measured, same harness and same data (`K32_packw`, `packShift w win % P`): old linear code **8.4 GB peak**;
     balanced **1.1 GB**.
   - The sparse blockRows-32 shard with balanced `spPack` but the linear window `packShift` was **OOM at 9.8 GB**.
     With the balanced window it **passes at 4.55 GB**.
   - The same quadratic effect is why `spPack` is a balanced node join and not a linear `packSpAux`.
2. **The dense route is kept as a fallback** inside `packedRealProduct` (unsorted or unslotted terms). It is
   evaluated only if the sparse check fails, so completeness is unchanged and soundness covers both branches.

## Measurements
Each probe ran alone under the shared lock: `flock .kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G
-p MemorySwapMax=0`. Peak is the sampled cgroup anon peak. Each probe is one middle shard of `[0,10]` A0·A0 (rr), with
forced equality.
- "Dense" is `checkShard adv A Bq s` on SO-DATA-2's literal RLE blocks (`K<R>_full`).
- "Sparse" is `checkShardSp` on the same factor as global ascending terms (`S<R>_full`, 8,475 terms per factor).

| blockRows (L, pairs) | before: dense, old code | dense, new code | **after: sparse** | sparse data-only baseline | **sparse kernel increment** |
|---|---|---|---|---|---|
| 32 (5,664; 12) | **OOM > 13.6 GB** (SO-DATA-2, 14 GB cap) | OOM at 10 GB¹ | **235 s, 4.55 GB** | 190 s, 1.03 GB | **+45 s, +3.5 GB** |
| 8 (1,416; 45) | 185 s, 9.9 GB (SO-DATA-2; no margin) | — | **210 s, 2.97 GB** | ≈1.0 GB² | ≈ +25 s, +2.0 GB |
| 4 (708; 90) | 149 s, 6.35 GB (data-only 87 s, 0.68 GB → +62 s, +5.7 GB) | 123 s, 5.25 GB¹ | **202 s, 2.71 GB** | 183 s, 0.97 GB | **+19 s, +1.7 GB** |

¹ Measured with the first iteration (balanced dense `packShift`, `Int` D&C decode, without F1). The dense route is
not the production route any more.
² Not run; the blockRows 4 and 32 baselines bracket it at 0.97–1.03 GB.

The sparse data-only baselines (≈ 190 s) are elaboration of the literal term lists; they are not kernel work.

Part probes at blockRows 32 (first iteration, dense data, new code):

| part | wall | peak |
|---|---|---|
| lengths | 178 s | 2.8 GB |
| pack | 171 s | 3.3 GB |
| window pack | 148 s | 1.1 GB |
| fits | 180 s | 3.7 GB |
| decode | 1,390 s | 2.2 GB |
| recon | 155 s | 1.6 GB |

The decode wall is almost entirely the elaboration of the 7-Mbit literal `X`. A separate test showed that parsing
alone is 81 s at blockRows-8 size, and it grows quadratically.

## Projection (kernel, both tori)
- At **blockRows 32**: 1,157 + 1,157 = 2,314 shard theorems (SO-DATA-2 counts) × ≤ 45 s, since the middle shard
  is the largest, gives **≤ 29 CPU-h; edge shards are cheaper, so ≈ 15–29 CPU-h**. Each shard is ≤ 4.6 GB and
  there are no block-tie theorems (the sparse route needs no dense factor).
- For comparison:
  - blockRows 4: 18,551 shards × ≤ 19 s ≈ ≤ 98 CPU-h.
  - Before the fix: 100–170 CPU-h at blockRows 4, and infeasible at 32.
- Composition, Gram and torsion work is extra and was not measured here.
- SO-REPLAY2's original kernel projection was ~0.75–1.5 CPU-h for 30 real products, ≈ 6.5–13 CPU-h scaled to
  2 × 129 real products. The figure above is **about 2–3× over that**.
- Likely remaining per-shard costs, not separately profiled with the final code:
  - the dense RLE advice window walks (`packLenEq`, `reconFitsAux` with per-slot `shardLogs`/`inBox`, and the
    leaf walk of `packShift`) over 11,327 slots;
  - the 11,327-slot decode leaves.
- **Recommendation:** keep blockRows 32.

## Checks
- **Gate builds (all success):**
  - `KAM.Certificate.Poly.{Packed,Advice,OverlapAdd,Sparse}`, `KAM.Certificate.Soundness`.
  - `KAM.Certificate.Tests.{Packed, Negative, Model}`.
  - Toys one at a time: `Tests.Toy2` (20 s), `Tests.Toy2d` (70 s), `Tests.Toy3` (26 s), `Tests.Rat` (11 s).
  - All with default heartbeats and no `set_option`.
- **`scripts/lint_sources.sh`:** check_lean_modules PASS (1456 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144).
  The only message is "KAM.lean is out of date" (new module; regeneration is the orchestrator's job).
- **`main_shortname_check.py`** (Sparse, Packed, Advice, MulPacked): OK.
- Lines ≤ 100 columns; all files ≤ 1500 lines.
- **New tests in `Tests/Packed`:**
  - `packedTest_sparse2`: slot terms and sparse pass.
  - `packedTest_sparse2_dense`: the bridge applied.
  - `packedTest_sparse2_rejects`: one changed advice slot rejected; descending slots rejected.
  - The existing P2–P5 positive and negative tests, including the `reconFits` anti-carry negative and the
    `intSlotsBound` kernel examples, still pass.
- **`#print axioms`:** `checkPackedProduct_sound`, `checkPackedSp_dense`, `CertPoly.mulPacked_sound`,
  `intSlotsBound_sound` and `checkTorusCertificate_sound` each depend only on [propext, Classical.choice,
  Quot.sound].

## Uncertainties
- Single runs on a shared machine; peaks are sampled once per second.
- The sparse probe takes the factor terms as literal slotted lists. In production, `slotTerms` computes the slots
  with `packSlotAux` from the `CertPoly` keys: 8,475 terms per factor, per shard theorem, unless hoisted. That cost
  is not in the table.
- The assembly of separately decided shard theorems now has `checkShardSp` as its per-shard unit, with `spBlocks`
  and `spMax` shared. A `checkPackedSp_eq_true_iff`-style decomposition was not added; it is straightforward if the
  assembly needs it.
- The projection assumes edge shards cost at most a middle shard.

## Errata
None in pinned sources. One factual correction to SO-KPERF's diagnosis ("balanced packing does not help"): it holds
at blockRows 4 but not at 32. See deviation 1.

Landing branch note (orchestrator): this branch (inp-sopackfixl) is inp plus the four SO-PACKFIX commits cherry-picked from inp-sopackfix (648d07da, 58d13990, 2e077f9e, b4e286bb) and SO-KPERF's report (7668ece2), without SO-DATA-2's unlanded data modules; it builds cleanly (Poly.Sparse, MulPacked, Soundness, Tests.Packed, Tests.Negative). The measurements above were taken on inp-sopackfix with the data.

AUDIT FOCUS (owner ruling D34: implementation change, statements unchanged): (1) NO signed statement changed: compare every public declaration of KAM/Certificate/Poly/{Packed,Advice,MulPacked}.lean present on inp with this branch (names, binders, types identical; only bodies and private/helper lemmas may differ); in particular checkPackedProduct, checkPackedProduct_sound, PackedAdvice and its cut/layout, shard_reconstruct, checkShard and its contract, intSlotsBound and intSlotsBound_sound, packShift and packShift_eq, shardFits and slotsBounded_shardConv, packedRealProduct and packedRealProduct_sound, CertPoly.mulPacked and CertPoly.mulPacked_sound; (2) the soundness of the new sparse route: checkPackedSp_dense really implies the DENSE check on exactly the factors the old route used (packFill la.denseLen 0 ea / eb), via packSum_cut_packFill and the fit-guard lemmas; spBlocks' takeWhile/dropWhile cut is correct for every input (unsorted, duplicate or out-of-range slots must make the sparse check fail or fall back, never pass wrongly); (3) the fallback branch of packedRealProduct is sound and the sparse branch cannot skip a guard the dense route had (F12-F14 anti-carry guards: reconFits, shardFits, intSlotsBound bound, the raw-length check); (4) F2' decode: natSlotsSh / natSlotsAux / the fuel-64 fallback give the exact value for every input, slotOffset_eq, and intSlotsBound_sound's identical conclusion; (5) the balanced packShift (packTree/packMerge with fallback) equals the old linear one (packShift_eq); (6) tests: the new sparse tests (positive, bridge, rejects) and the existing P2-P5 negatives still pass; (7) kernel replay of the touched modules, axioms (standard three) of checkPackedProduct_sound, CertPoly.mulPacked_sound and checkTorusCertificate_sound, lint, 1500/100 limits.

## Round 2 (after audit 1, F1)
Fix commit 2b01c348 (orchestrator): the two removed public helpers `packShiftAux` and `packShiftAux_eq` are
restored verbatim from inp (same names, binders, types and proof), as compatibility exports beside the balanced
`packShift`; `spPack`'s docstring now states its `base ≤ e.1` precondition (N1). Builds: Poly.Packed, Sparse,
MulPacked, Soundness, Tests.Packed all succeed; short-name check OK.
ROUND 2 FOCUS (delta): F1 resolved (both exports resolve with the exact inp headers); the restoration changed
nothing else; all 130 public declarations of Poly/{Packed,Advice,MulPacked} present on inp now present with
identical headers.
