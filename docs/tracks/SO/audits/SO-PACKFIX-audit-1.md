# SO-PACKFIX independent audit 1

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-sopackfixl`.
Audited HEAD: `88696cfe32d70f1e4c5e6e44aa0f25556470ede7`.
Baseline `inp` and merge base: `c2a97537297a510507b081cc3a2089a6d239906e`.
Comparison: `git diff inp...HEAD` (seven files, 1,135 insertions, 72 deletions).

## Verdict

**FAIL on the literal public-interface preservation requirement (focus 1); soundness checks PASS,
subject to the validation receipts below.** Two existing public exports disappeared:
`KAM.Certificate.packShiftAux` and `KAM.Certificate.packShiftAux_eq`.
The other 128 existing public declarations in `Poly/{Packed,Advice,MulPacked}.lean` retain
identical names, binders and source types. This finding does not refute packed-product soundness.

| Anchor / contract | Verdict | Reason |
|---|---|---|
| Public interface of `Poly.Packed` | FAIL | Two exports removed; see F1. |
| `packShift_eq`, `intSlotsBound_sound` | PASS | Unchanged statements; balanced packing and offset decode proved. |
| `PackedAdvice`, `cut`, `shard_reconstruct`, `checkShard(_sound)` | PASS | Unchanged record, contracts, and guard attachment. |
| `checkPackedProduct(_sound)` | PASS | Dense checker and theorem statements unchanged; sparse bridge reaches exactly these factors. |
| `packedRealProduct(_sound)`, `CertPoly.mulPacked(_sound)` | PASS | Same signatures; both execution branches reach the dense soundness core. |
| `checkPackedSp_dense` | PASS | Unconditional implication from sparse success to the full dense check. |
| `checkTorusCertificate_sound` | PASS | Unchanged downstream theorem; standard axioms only. |
| New frozen anchors / provider sealing | N/A | None added or changed by this package. |

I followed the user-specified report destination in this worktree, overriding the generic brief's
main-worktree output instruction. Repository edits are limited to this report; temporary probes
and logs were kept under `.lake/abi-scratch/` and removed after recording the evidence.
No state-changing git command, generated-root repair, or source repair was performed.

## Scope and controlling evidence

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package-audit brief,
`docs/tracks/SO/audits/SO-PACKFIX-handoff.md` (especially line 156), the entire package diff,
and `docs/tracks/SO/studies/SO-KPERF.md`. SO's controlling statement surface here is
`docs/tracks/SO/design/SO-LEAN-DESIGN.md` §B′ (lines 1031–1339), especially F12/F13/F14 at
1147–1306, and the P2–P5 test specifications at 763–775.
There is no `docs/tracks/SO/statement.md` in this checkout. This is infrastructure under D34,
not a new I/N/P theorem package. New helper lemmas are checked against their explicit local
specifications and the preserved dense contracts, rather than attributed to nonexistent
blueprint theorem labels.

For downstream context I also inspected `docs/tracks/I/statement.md`,
`blueprint-I/parts/p2-iso-iteration.tex` (`bpI:p2:g1`), `KAM/Iso/Apost/G1.lean`, the sealed
`KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean` and its three Iso definition-closure files.
The manifest marks `KAM.Iso.isoenergetic_kam` SEALED (lines 1607–1650).
None of the four audited polynomial modules imports a provider or a frozen theorem directly.
No new source premise, instance, analytic estimate, norm, or carrier is introduced into an
existing signed theorem. No provider=frozen-type or fresh seal-body probe applies to this diff.

## Findings

### F1 — existing public declarations removed (blocking under focus 1)

`git show inp:KAM/Certificate/Poly/Packed.lean` has, inside its public section:

```lean
-- inp:75
 def packShiftAux (w : ℕ) : ℕ → List ℤ → ℕ → ℕ → ℤ
-- inp:85–86
 theorem packShiftAux_eq (w : ℕ) (cs : List ℤ) :
   ∀ (s p n : ℕ), packShiftAux w s cs p n = (p : ℤ) - n + 2 ^ s * packSum w cs
```

The replacement implementation at current `Packed.lean:74–192` removes both names.
A fresh importing client cannot resolve either export (negative probe receipt below).
They were public implementation helpers, not private declarations. Focus 1 explicitly says
“compare every public declaration … present on inp” and “names, binders, types identical”.
The accompanying allowance for helper-lemma changes does not establish that a public definition
may disappear. I therefore retain the literal compatibility failure instead of silently
narrowing the requirement to a selected list of main theorems.

Remedy: retain the original helper definition and theorem as compatibility exports, leaving
`packShift` on its balanced implementation, or obtain an explicit scope ruling permitting their
removal. No implementation change was made during this audit. All 128 retained declarations
passed source-header comparison; the 127 non-structure declarations also have elaboration
probes against the exact `inp` headers. `PackedAdvice` and its six fields are unchanged.

### N1 — sparse helpers have guarded domains; no unchecked use found

`spBlocks_getD` (`Sparse.lean:194`) correctly requires strict slot order and a lower block
bound. `spPack_eq` (140) requires `base ≤ e.1` for every term. Neither claims its idealized
block specification for arbitrary malformed input. In particular,
`spPack 1 1 [(0,1),(1,1)] = 3`, while the naively documented sum using truncated natural
subtraction is 2. Its docstring at 69–71 should mention the lower-slot precondition.
The bridge proves that precondition from the block-range filter before using `spPack_eq`.
This is a documentation qualification, not a soundness failure.

`checkShardSp` on arbitrary user-supplied blocks and arbitrary `mA,mB` is likewise only a
Boolean computation. Its sound bridge requires blocks produced by `spBlocks`, actual `spMax`
bounds, ascending slots and raw-range bounds. No unconditional claim of shard soundness from
an arbitrary `checkShardSp = true` is made. Production uses precisely the guarded bridge.

### N2 — decoder acceptance is not promised equivalent to the old Boolean

`intSlotsBound` now rejects width zero; the old `intSlotsBoundAux` accepts length zero and
integer zero at width zero. A kernel probe confirms this difference. Both the old and current
`intSlotsBound_sound` assert only that success yields a bounded list of the requested length
with exactly the given packed value. No equality with the old Boolean or completeness theorem
was signed. `shapeOK` enforces positive width, so the example is outside production guards.
The new fuel-zero fallback and every balanced split preserve exact numeric reconstruction;
no claim that the new Boolean accepts every witness of the existential spec is needed.

The phrases “64 levels suffice for any list/length” in `Packed.lean:117–118,520–521` should be
read as practical size expectations, not theorems about unbounded Lean naturals. The proved
fuel-independent fallbacks cover arbitrary finite inputs, so correctness does not rely on
that wording.

### N3 — performance evidence remains a worker measurement

The 4.55 GB / 235 s blockRows-32 result was measured on `inp-sopackfix`, which included
SO-DATA-2 data absent here (handoff:154). The `.drafts/packfix/` generators and measurement logs
listed at handoff:16–18 are also absent from this seven-file landing diff and this worktree.
I did not independently reproduce that benchmark or certify the 15–29 CPU-h projection.
Production `slotTerms` computation, shard-assembly work, and edge-shard cost assumptions remain
exactly the handoff's stated uncertainties. These do not affect the kernel-checked implications.
The balanced dense-window implementation and dense fallback are disclosed deviations; no signed
contract requires the earlier linear implementation or prohibits a sound dense fallback.

## Soundness and guard trace

1. `checkPackedSp` (`Sparse.lean:394–402`) requires `shapeOK`, positive canonical dense lengths,
   strict ascending slots on BOTH inputs, slots below the corresponding dense lengths,
   exactly the required number of advice windows, and every sparse shard check. Strict order
   rejects duplicates as well as descending input. Out-of-range slots cannot pass the range
   check. Malformed keys are additionally excluded by `allSlots` in the consumer.
2. `takeWhile_lt_eq_filter` and `spBlocks_getD` prove that the one-pass cut is exactly the
   slot-range filter under these guards, including empty and padded terminal blocks.
   `packCutAux_length_eq` and `PackedAdvice.cut_length_eq` identify the block counts.
3. `packSum_cut_packFill` (321–347) equates the packed value of EVERY dense cut block, including
   out-of-count indices, to its corresponding sparse pack. `spJoin` handles either ordering
   of node bases exactly; its all-fuel fold/tree specifications include the fallback.
4. `natAbs_packSlotTotal_le` needs strict order so duplicates cannot defeat the maximum-term
   bound. `maxAbs_take_cut_packFill_le` bounds dense prefix maxima by the global sparse maxima.
   `checkShardSp_dense` (421–452) derives all dense block-length checks and its `shardFits`
   inequality from these facts. Global maxima can make the sparse check stricter, which only
   sends more inputs to the dense fallback.
5. The sparse shard explicitly retains the advice-window length, `reconFitsAux` with the SAME
   `shardLogs`, the fit inequality, and `intSlotsBound` of the identical residual after packing
   equality. Thus F12's advice-side and exact-side anti-carry checks are both present.
6. `checkPackedSp_dense` (456–475) concludes exactly
   `checkPackedProduct adv (packFill adv.la.denseLen 0 ea)
      (packFill adv.lb.denseLen 0 eb) = true`.
   `packFill_length` gives the RAW lengths required by F14, with no appeal merely to padded
   blocks. `shapeOK` retains F13's `1 ≤ scale`, compatibility, widths, target bounds, and
   zero-advice guards. The proof goes through `checkPackedProduct_eq_true_iff`, not a weaker
   surrogate checker.
7. `PackLayout.dense_eq_packFill` (`MulPacked.lean:252`) identifies these fills with the old
   `dense` results when `allSlots` and strict order pass. Therefore sparse success reaches
   `packedRealProduct_core` (312), the previous dense soundness argument. Sparse failure runs
   the old dense match and full check. The existing empty-factor exact-zero branch remains.
   `packedRealProduct_sound` handles all three cases; `CertPoly.mulPacked` and its proof are
   otherwise unchanged.
8. `natSlotsAux_sound` uses mask=modulo and shift=division, retaining the final zero remainder.
   `natSlotsSh_sound` joins the two EXACT packs, with the high half starting at `i + len/2`.
   Both fuel zero and `len ≤ 16` use the digit-by-digit reader. `slotOffset_eq` requires `w>0`
   before geometric division; the Boolean supplies this and offset nonnegativity before
   converting to Nat. Subtracting the replicated offset yields the original integer and
   the original per-slot error bound in `intSlotsBound_sound`.
9. `pairVal_packMerge`, `packFold_eq`, `packTree_eq`, `packLeavesAux_eq` prove the balanced
   `packShift` equals `packSum` for all widths and lists, including empty lists, negative
   entries, zero width and exhausted tree fuel. The leaf-width invariant and `k>0` are proved
   at the fixed `k=16` call, not assumed as an external arithmetic fact.

## Declaration-by-declaration review

All declarations below are in `KAM.Certificate` unless already qualified. P/A/M/S abbreviate
`KAM/Certificate/Poly/{Packed,Advice,MulPacked,Sparse}.lean`.
“Same” means identical source header and a successful exact-old-type elaboration probe (except
`PackedAdvice`, whose entire record is textually unchanged). Added helpers implement the stated
local object or invariant; none substitutes for a source theorem or assumes the hard conclusion.

| Node / location | Declaration | Verdict | Reason / classification |
|---|---|---|---|
| P:29 | `packSum` | PASS | Same. |
| P:32 | `packSum_nil` | PASS | Same. |
| P:34 | `sum_map_range_eq` | PASS | Same. |
| P:42 | `packSum_cons` | PASS | Same. |
| P:54 | `packSum_append` | PASS | Same. |
| P:64 | `packSum_eq_sum` | PASS | Same. |
| P:inp:75 | `packShiftAux` | FAIL | Public export removed (F1). |
| P:119 | `packShift` | PASS | Same. |
| P:inp:85 | `packShiftAux_eq` | FAIL | Public export removed (F1). |
| P:190 | `packShift_eq` | PASS | Same. |
| P:195 | `SlotsBounded` | PASS | Same. |
| P:198 | `packSum_injective` | PASS | Same. |
| P:226 | `listConv` | PASS | Same. |
| P:233 | `sum_mul_sum_range_cauchy` | PASS | Same. |
| P:292 | `packSum_listConv` | PASS | Same. |
| P:318 | `maxAbs` | PASS | Same. |
| P:320 | `natAbs_le_maxAbs` | PASS | Same. |
| P:329 | `abs_getD_le` | PASS | Same. |
| P:339 | `convFits` | PASS | Same. |
| P:343 | `abs_conv_entry_le` | PASS | Same. |
| P:391 | `slotsBounded_listConv` | PASS | Same. |
| P:408 | `packSum_flatten` | PASS | Same. |
| P:424 | `packSum_flatten_mul_shards` | PASS | Same. |
| P:438 | `slotRep` | PASS | Same. |
| P:441 | `intSlotsBoundAux` | PASS | Same. |
| P:522 | `intSlotsBound` | PASS | Same. |
| P:449 | `intSlotsBoundAux_sound` | PASS | Same. |
| P:604 | `intSlotsBound_sound` | PASS | Same. |
| P:85 | `pairVal` | PASS | Total weighted signed value of chunk pairs. |
| P:91 | `packLeavesAux` | PASS | Total chunk loop; intended leaf invariant requires k>0 and s+w*j=w*k; fixed k=16 consumer proves both. |
| P:101 | `packMerge` | PASS | Total adjacent-pair shift merge; value preserved for every width. |
| P:106 | `packFold` | PASS | Total linear fallback; exact signed value, including empty input. |
| P:111 | `packTree` | PASS | Total balanced tree; all-fuel value theorem includes fallback. |
| P:123 | `pairVal_packMerge` | PASS | Exact merge identity for arbitrary width and chunk list. |
| P:134 | `packFold_eq` | PASS | Exact fallback identity for arbitrary width and chunk list. |
| P:144 | `packTree_eq` | PASS | Exact all-fuel identity, no size premise. |
| P:152 | `packLeavesAux_eq` | PASS | Exact chunk value under actual loop invariant and positive leaf size. |
| P:500 | `natSlotsAux` | PASS | Total Boolean digit reader; zero residual required at length zero. |
| P:508 | `natSlotsSh` | PASS | Total split decoder; exact high/low reconstruction and fuel-zero reader. |
| P:516 | `slotOffset` | PASS WITH NOTES | Total closed form; geometric-series specification restricted to positive width, checked before use. |
| P:527 | `NatSlotsSpec` | PASS | Explicit existential reconstruction predicate, not a new assumption or instance. |
| P:532 | `natSlotsAux_sound` | PASS | Bounded-digit exact numeric reconstruction after passing leaf reader. |
| P:557 | `natSlotsSh_sound` | PASS | Same exact reconstruction after every fuel/split case. |
| P:581 | `packSum_replicate` | PASS | Exact geometric sum, all widths and lengths. |
| P:588 | `slotOffset_eq` | PASS | Correct geometric offset under w>0, supplied by decoder. |
| P:596 | `packSum_map_sub` | PASS | Exact subtraction of replicated per-digit offset. |
| A:32 | `PackedAdvice` | PASS | Same; record fields unchanged. |
| A:43 | `reconSlots` | PASS | Same. |
| A:46 | `packSum_reconSlots` | PASS | Same. |
| A:63 | `reconFits` | PASS | Same. |
| A:68 | `reconFitsAux` | PASS | Same. |
| A:73 | `reconFitsAux_eq_all` | PASS | Same. |
| A:90 | `reconFitsAux_eq` | PASS | Same. |
| A:95 | `slotsBounded_reconSlots` | PASS | Same. |
| A:120 | `shardConv` | PASS | Same. |
| A:126 | `shardConv_length` | PASS | Same. |
| A:130 | `shardConv_getD` | PASS | Same. |
| A:137 | `packSum_eq_sum_of_length_le` | PASS | Same. |
| A:145 | `packSum_shardConv` | PASS | Same. |
| A:183 | `packLenEq` | PASS | Same. |
| A:188 | `packLenEq_iff` | PASS | Same. |
| A:194 | `packLenLe` | PASS | Same. |
| A:199 | `packLenLe_iff` | PASS | Same. |
| A:205 | `packLengthAux` | PASS | Same. |
| A:209 | `packLengthAux_eq` | PASS | Same. |
| A:217 | `packMaxAbsAux` | PASS | Same. |
| A:221 | `packMaxAbsAux_eq` | PASS | Same. |
| A:265 | `shardFits` | PASS | Same. |
| A:269 | `maxAbs_le_of_forall` | PASS | Same. |
| A:278 | `maxAbs_getD_le_take` | PASS | Same. |
| A:289 | `length_getD_le_take` | PASS | Same. |
| A:300 | `slotsBounded_shardConv` | PASS | Same. |
| A:339 | `shard_reconstruct` | PASS | Same. |
| A:368 | `PackedAdvice.blockLen` | PASS | Same. |
| A:371 | `packTakePad` | PASS | Same. |
| A:376 | `packTakePad_eq` | PASS | Same. |
| A:387 | `packCutAux` | PASS | Same. |
| A:392 | `PackedAdvice.cut` | PASS | Same. |
| A:395 | `packCutAux_length` | PASS | Same. |
| A:407 | `PackedAdvice.cut_length` | PASS | Same. |
| A:411 | `packCutAux_nil` | PASS | Same. |
| A:415 | `packCutAux_flatten` | PASS | Same. |
| A:436 | `PackedAdvice.cut_flatten` | PASS | Same. |
| A:441 | `listConv_length` | PASS | Same. |
| A:449 | `PackedAdvice.prodLen` | PASS | Same. |
| A:453 | `packDigitsIn` | PASS | Same. |
| A:459 | `PackedAdvice.boxLow` | PASS | Same. |
| A:464 | `PackedAdvice.boxHigh` | PASS | Same. |
| A:473 | `PackedAdvice.inBox` | PASS | Same. |
| A:478 | `PackedAdvice.shardLogs` | PASS | Same. |
| A:482 | `packAddZ` | PASS | Same. |
| A:488 | `packOverlapAdd` | PASS | Same. |
| A:496 | `PackedAdvice.combined` | PASS | Same. |
| A:499 | `PackedAdvice.combined_length` | PASS | Same. |
| A:503 | `packDigitsIn_iff` | PASS | Same. |
| A:524 | `PackedAdvice.inBox_eq` | PASS | Same. |
| A:573 | `PackedAdvice.windowZeroOK` | PASS | Same. |
| A:579 | `PackedAdvice.adviceZeroOK` | PASS | Same. |
| A:585 | `PackedAdvice.targetSubBox` | PASS | Same. |
| A:599 | `PackedAdvice.shapeOK` | PASS | Same. |
| A:607 | `shardPacked` | PASS | Same. |
| A:616 | `checkShard` | PASS | Same. |
| A:625 | `shardPacked_eq` | PASS | Same. |
| A:632 | `checkShard_sound` | PASS | Same. |
| A:649 | `checkPackedProduct` | PASS | Same. |
| A:658 | `checkPackedProduct_eq_true_iff` | PASS | Same. |
| A:670 | `PackedAdvice.shapeOK_scale` | PASS | Same. |
| A:676 | `checkPackedProduct_guards` | PASS | Same. |
| A:688 | `checkPackedProduct_scale_zero` | PASS | Same. |
| A:696 | `checkPackedProduct_raw_length` | PASS | Same. |
| A:707 | `packSum_audit5_cancel` | PASS | Same. |
| A:709 | `reconFits_audit5_rejects` | PASS | Same. |
| A:230 | `packLenLeBlocks` | PASS | Exact all-test on take n, including n beyond available blocks. |
| A:235 | `packLenLeBlocks_eq` | PASS | Whole-carrier equality to old take/all test. |
| A:242 | `packMaxBlocks` | PASS | Exact max of initial accumulator and flattened take n; no copied prefix. |
| A:247 | `maxAbs_append` | PASS | Whole-carrier maximum identity. |
| A:254 | `packMaxBlocks_eq` | PASS | Whole-carrier equality to old prefix/flatten maximum. |
| M:36 | `certMantPair` | PASS | Same. |
| M:43 | `mantSel` | PASS | Same. |
| M:46 | `certMantPart` | PASS | Same. |
| M:55 | `CertPoly.toMants` | PASS | Same. |
| M:62 | `intEval_nil` | PASS | Same. |
| M:64 | `intEval_cons` | PASS | Same. |
| M:68 | `intEval_append` | PASS | Same. |
| M:72 | `intEval_map_neg` | PASS | Same. |
| M:81 | `certMantPair_sound` | PASS | Same. |
| M:96 | `intEval_filterMap_certMantPart` | PASS | Same. |
| M:113 | `CertPoly.toMants_sound` | PASS | Same. |
| M:137 | `packRangeSum` | PASS | Same. |
| M:144 | `packRangeSum_eq` | PASS | Same. |
| M:158 | `packRangeMax` | PASS | Same. |
| M:165 | `le_foldr_max_of_mem` | PASS | Same. |
| M:174 | `le_packRangeMax` | PASS | Same. |
| M:194 | `PackedAdvice.slotDeg` | PASS | Same. |
| M:199 | `PackedAdvice.slotErr` | PASS | Same. |
| M:203 | `PackedAdvice.maxSlotDeg` | PASS | Same. |
| M:209 | `PackedAdvice.remainderBound` | PASS | Same. |
| M:215 | `PackedAdvice.targetEntry` | PASS | Same. |
| M:221 | `PackedAdvice.targetTerms` | PASS | Same. |
| M:238 | `packedRealProduct` | PASS | Same. |
| M:259 | `intEval_targetEntry` | PASS | Same. |
| M:275 | `intEval_targetTerms` | PASS | Same. |
| M:282 | `PackedAdvice.shapeOK_compat` | PASS | Same. |
| M:287 | `remainderBound_mul` | PASS | Same. |
| M:356 | `packedRealProduct_sound` | PASS | Same. |
| M:388 | `ofDyadicScaled` | PASS | Same. |
| M:391 | `ofDyadicScaled_sound` | PASS | Same. |
| M:407 | `dyadicTerms` | PASS | Same. |
| M:413 | `dyadicTerms_sound` | PASS | Same. |
| M:438 | `CertPoly.mulPacked` | PASS | Same. |
| M:453 | `CertPoly.mulPacked_sound` | PASS | Same. |
| M:531 | `ProductKey` | PASS | Same. |
| M:533 | `AdviceBook` | PASS | Same. |
| M:226 | `PackLayout.slotTerms` | PASS WITH NOTES | Total slot projection; default 0 off layout is quarantined by allSlots. |
| M:230 | `PackLayout.allSlots` | PASS | Actual isSome test on every key; empty list vacuously true. |
| M:252 | `PackLayout.dense_eq_packFill` | PASS | Actual old dense result; requires verified slot existence and ascending order. |
| M:312 | `packedRealProduct_core` | PASS | Extracted old proof with source data and a dense-check success premise; distinctly named helper. |
| S:33 | `spBlocks` | PASS | Total cut loop; range-filter meaning on sorted, lower-bounded input; guard established by bridge. |
| S:39 | `spNodeVal` | PASS | Total signed node value at its natural slot. |
| S:42 | `spLeaf` | PASS | Exact signed term split into natural positive/negative parts. |
| S:46 | `spJoin` | PASS | Total join at smaller base; both branch orders preserve signed value. |
| S:52 | `spLevel` | PASS | Total adjacent-node merge. |
| S:57 | `spFold` | PASS | Total exact fallback; empty value is zero. |
| S:63 | `spTree` | PASS | Total all-fuel tree with exact fallback. |
| S:72 | `spPack` | PASS WITH NOTES | Guarded block-relative sum; base <= all slots is proved before use (N1). |
| S:77 | `spMax` | PASS | Actual maximum absolute term value; empty maximum is zero. |
| S:80 | `shardPackedSp` | PASS | Actual sum of relative block products; missing blocks are zero. |
| S:84 | `spNodeVal_spJoin` | PASS | Exact value identity on the whole node carrier. |
| S:97 | `spJoin_fst_ge` | PASS | Lower bound preserved by minimum-base join. |
| S:102 | `spListVal` | PASS | Actual sum of signed node values. |
| S:104 | `spLevel_spec` | PASS | Value and lower-bound invariants for one level. |
| S:119 | `spFold_spec` | PASS | Exact fallback value; lower bound only for nonempty nodes. |
| S:129 | `spTree_spec` | PASS | Exact value for every fuel; lower bound only for nonempty nodes. |
| S:140 | `spPack_eq` | PASS | Exact relative sum under explicit lower-slot guard. |
| S:173 | `takeWhile_lt_eq_filter` | PASS | Sorted-list take/drop equivalence; strict order premise explicit. |
| S:189 | `spBlocks_length` | PASS | Unconditional block count, including empty data. |
| S:194 | `spBlocks_getD` | PASS | Correct slot-range block under sortedness/lower-bound guards. |
| S:225 | `sum_packSlotTotal_window` | PASS | Exact window sum for arbitrary term lists, allowing duplicates. |
| S:256 | `getD_getD_of_flatten` | PASS | Correct two-level lookup for uniformly sized blocks. |
| S:274 | `packCutAux_length_eq` | PASS | Ceiling count under positive length and sufficient cut fuel. |
| S:297 | `PackedAdvice.cut_length_eq` | PASS | Ceiling count; actual cut has enough fuel. |
| S:303 | `packFill_getD` | PASS | Correct full-range slot total under sortedness and upper-range bound. |
| S:311 | `packFill_length` | PASS | Unconditional raw length, arbitrary terms and starting slot. |
| S:321 | `packSum_cut_packFill` | PASS | Exact dense block/sparse block packed identity; no omitted tail case. |
| S:350 | `natAbs_packSlotTotal_le` | PASS | Strict order prevents duplicate accumulation from exceeding spMax. |
| S:376 | `PackedAdvice.spCount` | PASS | Total ceiling formula; meaningful positive block length supplied by shapeOK. |
| S:382 | `checkShardSp` | PASS WITH NOTES | Guarded Boolean shard computation; bound arguments trusted only after bridge ties them to spMax (N1). |
| S:394 | `checkPackedSp` | PASS | Full sparse validation; no success without order, range, shape, count and all-shard guards. |
| S:404 | `maxAbs_take_cut_packFill_le` | PASS | Dense prefix maximum bounded by sparse term maximum, with padding zeros. |
| S:421 | `checkShardSp_dense` | PASS | Derives every old shard guard on exact cut fills. |
| S:456 | `checkPackedSp_dense` | PASS | Unconditional sparse-success implication to full dense checker on exact fills. |
| OverlapAdd (unchanged) | `checkPackedProduct_sound` | PASS | Original dense contract and proof; standard axioms. |
| Tests/Packed:95 | `packedTest_sparse2` | PASS | Exact slot terms and positive sparse check by kernel decision. |
| Tests/Packed:101 | `packedTest_sparse2_dense` | PASS | Instantiates the exact-fill bridge. |
| Tests/Packed:108 | `packedTest_sparse2_rejects` | PASS | Changed advice and descending slots rejected by kernel decision. |
| Soundness (unchanged) | `checkTorusCertificate_sound` | PASS | Downstream theorem; standard axioms. |

The table classifies every added `def` (27 total) individually. No new `abbrev`, `structure`,
instance or bundled hypothesis is introduced. Defaults are computational and either exact zero
values (missing blocks/empty sums), or protected by established guards (`slotTerms`, ceiling
count at positive block size, and block-relative packing). Fuel exhaustion invokes exact
algorithms, never a fabricated success value. The only removed definition is F1's public helper.

## Independent validation receipts

Every Lean/Lake invocation below inherited `LEAN_NUM_THREADS=1` and was run sequentially.
Each build went through the prescribed gate, which invokes `nice -n 5 lake build <Module>`.
`lake env lean` and `leanchecker` were explicitly prefixed with `nice -n 5`.
The lint process was also niced and ran only after replay completed (its ABI script invokes Lean).
No heartbeat, recursion, or synthesis-budget override was used.

### Targeted builds — all exit 0

Command template (run once per module, one at a time):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-sopackfixl <Module>
```

| Module | Exact success output |
|---|---|
| `KAM.Certificate.Tests.Packed` | `Build completed successfully (2915 jobs).` |
| `KAM.Certificate.Poly.Packed` | `Build completed successfully (2903 jobs).` |
| `KAM.Certificate.Poly.Advice` | `Build completed successfully (2905 jobs).` |
| `KAM.Certificate.Poly.Sparse` | `Build completed successfully (2907 jobs).` |
| `KAM.Certificate.Poly.MulPacked` | `Build completed successfully (2911 jobs).` |
| `KAM.Certificate.Tests.Negative` | `Build completed successfully (3251 jobs).` |
| `KAM.Certificate.Soundness` | `Build completed successfully (3318 jobs).` |

These are targeted Lake gates against the existing overlay, not clean library rebuilds; job totals
include cached dependencies. Existing warnings are in `Arith/PiHigh.lean:218` (unused simp argument),
`Expr/Basic.lean:85` (unused variable), `Sound/Static.lean:99,152` and `Sound/Ham.lean:68`
(unused section variables); none is in a changed proof. No warning-suppression option was set.

### Public signatures and negative compatibility test

A scratch inventory compared all public `def/theorem/abbrev/structure` headers against
`git show inp:<file>`; equation-clause bodies and comments were excluded from the headers.
Results: Packed 28 old / 44 current (two removed); Advice 66 / 71; MulPacked 36 / 40.
Exactly 128 old declarations remain and all 128 headers are identical. The full `PackedAdvice`
record text, including its six fields, is byte-identical.

For every retained non-structure declaration, I elaborated a scratch example with the EXACT old
binders and result type, assigning `@<current export>` (127 examples in total):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Signatures.lean
```

Final exit **0**; no errors (only scratch binder-unused warnings). The probe imports
`KAM.Certificate.Poly.MulPacked`, opens `KAM CertArith`, and works in `KAM.Certificate`.
An initial probe omitted `open CertArith` and consequently could not resolve `val`; after fixing
that probe context all examples passed. This was an audit-probe issue, not a package failure.

The separate removed-export probe was:

```lean
import KAM.Certificate.Poly.Packed
#check KAM.Certificate.packShiftAux
#check KAM.Certificate.packShiftAux_eq
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Removed.lean
```

Expected negative exit **1**, exact output:

```text
.lake/abi-scratch/Removed.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `KAM.Certificate.packShiftAux`
.lake/abi-scratch/Removed.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `KAM.Certificate.packShiftAux_eq`
```

### Adversarial kernel probes and regression coverage

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Adversarial.lean
```

Final exit **0**. Seventeen extra examples verified: duplicate sparse slots rejected;
a slot equal to `denseLen` rejected; reversed keys accepted through the actual dense fallback;
repeated keys accumulated and accepted through that fallback; out-of-layout keys rejected;
empty sparse terms on a nonempty zero layout accepted; F12 carry-cancelling advice rejected;
F13 scale-zero advice rejected; 33-digit decode accepted for zero and rejected for an unconsumed
high digit; both fuel-zero and one-level `natSlotsSh` fallback accepted the same exact offset;
width-zero old/new acceptance difference; zero-width balanced packing; fuel-zero `packTree`
identity; and the two exact values demonstrating N1's guarded-domain qualification.
An initial scratch example had a malformed pipeline expression; it was corrected and the entire
17-example probe was rerun successfully.

The landed test module includes the three new sparse tests plus all existing tests, including
P2 carry cancellation (`Tests/Packed.lean:334–349`), P3 attained overlap bound (360–373),
P4 rejection of scale zero despite passing individual shards (383–394), and P5 raw-length
padding alias (403–415). These passed the targeted gate and the replay below. The new examples
were scratch probes only; no production or test module was edited.

### Axioms — all allowed

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Axioms.lean
```

Exit **0**. This imports Soundness, Sparse, and Tests.Packed, and issues `#print axioms` for
all 34 newly added public infrastructure theorems and nine main soundness exports. The three
new public test theorems were additionally printed by the adversarial probe. Full output:

```text
'KAM.Certificate.pairVal_packMerge' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packFold_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packTree_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packLeavesAux_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.natSlotsAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.natSlotsSh_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_replicate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotOffset_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_map_sub' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packLenLeBlocks_eq' depends on axioms: [propext]
'KAM.Certificate.maxAbs_append' depends on axioms: [propext]
'KAM.Certificate.packMaxBlocks_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackLayout.dense_eq_packFill' depends on axioms: [propext]
'KAM.Certificate.packedRealProduct_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.spNodeVal_spJoin' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.spJoin_fst_ge' does not depend on any axioms
'KAM.Certificate.spLevel_spec' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.spFold_spec' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.spTree_spec' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.spPack_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.takeWhile_lt_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.spBlocks_length' depends on axioms: [propext]
'KAM.Certificate.spBlocks_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_packSlotTotal_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.getD_getD_of_flatten' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packCutAux_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.cut_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packFill_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packFill_length' depends on axioms: [propext]
'KAM.Certificate.packSum_cut_packFill' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.natAbs_packSlotTotal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.maxAbs_take_cut_packFill_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkShardSp_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedSp_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotsBounded_shardConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.shard_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkShard_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_sparse2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_sparse2_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_sparse2_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular `checkPackedProduct_sound`, `CertPoly.mulPacked_sound`, and
`checkTorusCertificate_sound` depend on exactly `[propext, Classical.choice, Quot.sound]`.
All other printed sets are subsets of these three; no `sorryAx` or nonstandard axiom appeared.

### Kernel replay

One invocation, exit **0**, elapsed 135.97 s:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Certificate.Poly.Packed KAM.Certificate.Poly.Advice \
  KAM.Certificate.Poly.Sparse KAM.Certificate.Poly.MulPacked \
  KAM.Certificate.Tests.Packed KAM.Certificate.Tests.Negative \
  KAM.Certificate.Soundness
```

Exact output:

```text
replaying KAM.Certificate.Soundness
replaying KAM.Certificate.Tests.Negative
replaying KAM.Certificate.Tests.Packed
replaying KAM.Certificate.Poly.MulPacked
replaying KAM.Certificate.Poly.Sparse
replaying KAM.Certificate.Poly.Advice
replaying KAM.Certificate.Poly.Packed
```

### Lint, protected paths and size checks

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with only the brief's explicitly permitted generated-root exception:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1394 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus lint is **PASS WITH NOTES**, not an unconditional exit-zero pass. This landing worktree
has 1394 checked Lean files, rather than the original handoff's 1456-file data-bearing worktree.
The generated `KAM.lean` was left untouched as required.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, empty output. Changed Lean files have respectively 624/711/535/477/417 lines
(Packed/Advice/MulPacked/Sparse/Tests.Packed), with maximum Unicode line lengths
99/100/98/99/100. All meet 1500/100 limits. Each has copyright, `module`, public interface imports,
module docstring, and public section; executable definitions are in exposed public sections.
A code-masked scan of all five changed Lean files found zero forbidden escape/resource tokens.
No introduced `EuclideanSpace`, provider import, or DRAFT_SORRY use was found.


## Source defects, deviations and limits

No suspected defect in a pinned mathematical source or frozen statement was found by this
implementation audit. F1 is a package interface deviation, not an erratum in HL19.
N1 and N2 identify local documentation/domain qualifications. I found no contradiction of the
SO design's F12–F14 conclusions and no conclusion-shaped assumption in a new public theorem.
The performance qualification N3 is retained; small kernel tests do not establish the large-data
runtime projection. Nothing in this audit claims a new lunar certificate or a newly sealed
I/N/P theorem.
