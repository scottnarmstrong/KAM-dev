# SO-POLY-B prover handoff (branch inp-sopolyb, 590a7afd; track SO package run by the main orchestrator)


Branch `inp-sopolyb`, HEAD `590a7afd` (12 commits on top of `da24255d`). Worktree `/root/code/KAM-inp-sopolyb`.
Everything is committed. Every signed declaration of the SO-POLY-B part of
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` is proved with the signed type, verbatim. No `sorry`, no
axiom, no `native_decide`. There is no heartbeat, recursion-depth or synthesis override. Every module builds at the
default budgets.

## Files (all new; landed SO-POLY-A `Poly/Packed.lean` and `Arith/Mantissa.lean` untouched)

| File | Lines | Content |
|---|---|---|
| `KAM/Certificate/Poly/Layout.lean` | 779 | `PackLayout`, `slot`, `denseLen`, `dense` (scatter and linear fill), `prodKey`, `compat`, `intEval`, `dense_length`, `PackLayout.intEval_mul`, and `intEval_mul_of_compat` (any evaluation dimension). Also the mixed-radix decoding lemma `packDigits_packDot`. |
| `KAM/Certificate/Poly/Advice.lean` | 680 | `PackedAdvice`, `reconSlots`, `packSum_reconSlots`, `reconFits` (signed body), `slotsBounded_reconSlots`, `shardConv(_length)`, `packSum_shardConv`, `shardFits`, `slotsBounded_shardConv`, `shard_reconstruct`. Then `blockLen`, `cut(_length)`, `listConv_length`, `prodLen`, `inBox` (with `inBox_eq`), `shardLogs`, `combined(_length)`, `shapeOK`, `checkShard(_sound)`, `checkPackedProduct`, `_guards`, `_scale_zero`, `_raw_length`, `packSum_audit5_cancel`, `reconFits_audit5_rejects`. Kernel-safe list walks. |
| `KAM/Certificate/Poly/OverlapAdd.lean` | 344 | The overlap-add glue, `checkPackedProduct_slots` (stronger internal form) and `checkPackedProduct_sound`. |
| `KAM/Certificate/Poly/MulPacked.lean` | 494 | `CertPoly.toMants(_sound)`, `packedRealProduct(_sound)`, `remainderBound`, `targetTerms`, `ofDyadicScaled`, `dyadicTerms`, `CertPoly.mulPacked(_sound)`, `ProductAdvice`, `ProductKey`, `AdviceBook`. |
| `KAM/Certificate/Poly/Ops.lean` | 68 | `CertPoly.shift`, `eval_shift`, `conjReflect`, `eval_conjReflect`. This is the facade: it publicly imports the packed modules, so Model/Ops (SO-MALG) imports `Poly/Ops` alone, per design §7. |
| `KAM/Certificate/Tests/Packed.lean` | 340 | The §8 `Tests/Packed`: positive tests, negative tests, and P2–P5. |

The design's risk row ("split `Poly/Packed` into layout and glue modules") is taken. The SO-POLY-B declarations live in
the five new modules, and every file is under 800 lines. `KAM.lean` is generated (rule 10) and was not edited.
`gen_root_imports.py` would add exactly my six modules. I checked this and restored the file.

## Approach

- **Layout.** A key's slot is `Σ_j (k_j − lo_j)·stride_j` when the key has exactly `dims.length` entries and lies in
  the box. The exact-length requirement makes `mulPacked_sound` hold at every evaluation dimension `n`.
  - `compat n` asks for `n` axes, equal strides and widths, and no wrap: `stride_j ≥ stride_{j+1}·(dA_{j+1}+dB_{j+1}−1)`
    and last stride `≥ 1`.
  - Greedy digits are then exact (`packDigits_packDot`), so the sum of two in-box slots decodes to the key sum
    (`prodKey_slot_add`).
  - `intEval_mul` regroups the double sum fiberwise. `sum_range_cauchy_weighted` is a Cauchy reindexing with a weight
    `H(p+q)`.
- **Shard (F12).** `shard_reconstruct` is `intSlotsBound_sound` plus both slot bounds (`shardFits` on the exact side,
  `reconFits` on `2^scale·r + e`) plus `packSum_injective`. `checkShard_sound` takes the check as its only premise.
- **Whole product (F13, F14).** `checkPackedProduct_guards` exports `1 ≤ scale`, `shapeOK`, `0 < blockLen`, the raw
  lengths, positivity, the window count and every shard.
  - **Overlap-add.** The exact convolution equals the overlap-add of the exact shard windows. Both sides pack to the
    same integer at every width, so they agree by injectivity at a width above all their slots
    (`eq_of_packSum_forall`, `listConv_getD_eq_overlapAdd`).
  - **Two-window bound.** By induction, a slot is covered by at most two windows. This gives `2·2^(scale−1) = 2^scale`
    on the target box and `2^(outLog+1)` off it; the advice is zero there by `shapeOK`.
  - The length conjunct comes from `combined_length`, `prodLen` and `listConv_length`.
- **`mulPacked`.** It makes four real products.
  - **Zero parts.** `toMants` drops zero mantissas, so an all-zero part is `[]`. `packedRealProduct` returns the
    exact zero product for an empty factor and never looks at that advice (SO-ADVCOUNT lever 2).
  - **Coefficients.** The target coefficients are the nonzero `combined` entries. They are made exact by
    `ofDyadic (2P − scale) (r·2^(scale−2P))`, failing closed.
  - **Radius.** The radius is `ofRatUp(Σ_products Σ_slots b_i·w^{|k_i|₁}/2^{2P})`, summed over every product slot.
    It is computed in naturals as `(Σ b_i num^{d_i} den^{D−d_i})/(den^D·2^{2P})`, with balanced sums.
- **Kernel engineering (no signature change).** A production-size replay (below) showed the following.
  - **`inBox`.** The first body (key decode plus `target.slot`) cost about 2 ms per call, three times per slot. It is
    now a natural-number digit-window test, proved equal to the key reading by `PackedAdvice.inBox_eq`.
  - **`dense`.** It uses a list-walking slot (`packSlotAux_eq`), a linear fill for strictly increasing slots
    (`packFill_eq`), and the binary scatter otherwise.
  - **Deep recursion.** The kernel's deep-recursion guard fired at 8192-slot blocks on the landed `maxAbs` (`foldr`).
    Every walk over a long list in my bodies now counts a literal down or forces its accumulator: `packLenEq`,
    `packLenLe`, `packLengthAux`, `packMaxAbsAux`, `packTakePad`. Each is proved equal to the plain reading.
  - **Non-tail recursions.** The non-tail `match` recursions (mantissas, dyadic terms) became all-check-then-map.
  - **Target terms.** These index through `List.range`, whose elements are literals.

## Checks (exact)

- Gate build `inp_lake_build.sh … KAM.Certificate.Poly.{Layout,Advice,OverlapAdd,MulPacked,Ops}
  KAM.Certificate.Tests.Packed` printed `Build completed successfully (2912 jobs).` It gives no warning in my
  files; the only warning shown is the pre-existing one in `Arith/PiHigh.lean`.
- `sh scripts/lint_sources.sh` passes every check except `KAM.lean is out of date; run scripts/gen_root_imports.py`.
  That one is expected (the generated root; rule 10). The others print `check_lean_modules: PASS`,
  `FROZEN-ANCHOR GUARD OK` and `ABI HASHES OK (144 frozen declarations)`. Every line is at most 100 columns.
- `main_shortname_check.py /root/code/KAM-inp-sopolyb <the six modules>` printed
  `short-name check OK (no reused public short name)`.
- **Signature check.** The script is `.drafts/SO-POLY-B-replay/sigcheck.py`. It compares all 50 signed SO-POLY-B
  declarations whitespace-normalized: statements up to `:=` for `sorry` bodies, the full text for signed concrete
  bodies (`reconSlots`, `reconFits`, `intEval`, `prodLen`, the audit-5 controls, the structures, the inductive and
  the abbrevs). It printed `checked 50 bad 0`.
- `#print axioms`: `PackLayout.intEval_mul`, `PackLayout.dense_length`, `shard_reconstruct`, `checkShard_sound`,
  `checkPackedProduct_{guards,scale_zero,raw_length,sound}`, `combined_length`, `PackedAdvice.inBox_eq`,
  `CertPoly.toMants_sound`, `CertPoly.mulPacked_sound`, `CertPoly.eval_shift`, `CertPoly.eval_conjReflect` and the
  test theorems all give `[propext, Classical.choice, Quot.sound]`. `cut_length` and `listConv_length` give
  `[propext, Quot.sound]`. `packSum_audit5_cancel` and `reconFits_audit5_rejects` give `[propext]`.

## Tests (`Tests/Packed`, all `decide +kernel`; per-theorem elaboration + kernel time, s, `Elab.async false`)

| Test | s | What it shows |
|---|---|---|
| `packedTest_dense2` / `_scatter` / `_badKey` | 0.028 / 0.020 / 0.004 | Linear fill; scatter (unsorted, a repeated key adds); a wrong-length key is rejected |
| `packedTest_pass2`, `_sound2` | 0.051, 0.028 | `n = 2`, two blocks per factor, passes; slot contract at an overlapped slot |
| `packedTest_mulPacked2`, `_encloses`, `_reIm` | 0.109, 0.018, 0.149 | `CertFixed 4`, production decoder, `some`. The three zero-part products carry bogus scale-0 advice and are skipped. Enclosure via `mulPacked_sound` with `checkWeight ⟨1/100, 11/10⟩ 0 6` (0.011). `re·im` route |
| `packedTest_pass3`, `_mulPacked3` | 0.103, 0.158 | `n = 3`, target a proper sub-box (`outLog = 6`) |
| `packedTest_cutM`, `_passM`, `_mulPackedM` | 0.015, 0.056, 0.089 | Three blocks per factor, five overlapping windows |
| `packedTest_offByTwo` | 0.029 | One advice slot `+2`: rejected |
| `packedTest_alias_packs`, `_alias_rejected` | 0.020, 0.036 | `+2^24`/`−1` alias: same `packSum 24`, rejected (slot range) |
| `packedTest_wrap_compat`, `_wrap_rejected` | 0.003, 0.009 | Row stride 4 < 3+3−1: `compat = false`, rejected |
| `packedTest_wrongDecoder`, `_keyOutside` | 0.008, 0.021 | Wrong mantissa: `mantCheck` rejects, so `none`; key outside the box, so `none` |
| **P2** `_P2_shape`, `_P2_decodes`, `_P2_reconFits`, `_P2_rejected` | 0.008, 0.024, 0.008, 0.021 | Audit 5: `shapeOK` holds and the residual decodes (the carry cancels). `reconFits` is false, so `checkShard` and `checkPackedProduct` are false |
| **P3** `_P3_passes`, `_P3_attained`, `_P3_bound` | 0.025, 0.018, 0.024 | Audit 6 overlap: passes; slot 2 error is exactly `2 = 2^scale`; the contract instance |
| **P4** `_P4_shards`, `_P4_rejected`, `_P4_error` | 0.022, 0.004, 0.014 | Audit 5 at scale 0: every shard passes; the whole product is rejected (`checkPackedProduct_scale_zero rfl`); combined error `2 > 2^0` |
| **P5** `_P5_sameBlocks`, `_P5_long`, `_P5_short`, `_P5_short_kernel` | 0.010, 0.023, 0.005, 0.007 | Audit 6 alias: same cut blocks. `[0,0]` passes (`combined = [0,0,0]`, convolution length 3). `[0]` is rejected (`checkPackedProduct_raw_length`, and by kernel) |

The whole test file elaborates in about 8 s wall.

## Replay measurements (scratch, not committed; generators in `.drafts/SO-POLY-B-replay/`)

`gen_replay2.py` builds a 2-D real product: data by kernel formula, dense factors and advice as one big numeral
each. These are the design's "end-to-end design-B shard with the rounding glue" and complex-product items, at
`w = 32`, 8-bit mantissas, on a loaded shared machine (±30 %).

- **256-slot blocks** (8×32 factor, stride 64, 3 shards):

  | Check | Final | First draft |
  |---|---|---|
  | `dense` | 0.42 s | 1.66 s |
  | `checkShard` (each) | 1.3–2.3 s | 2.6–3.3 s |
  | `shapeOK` | 0.80 s | 3.0 s |
  | `checkPackedProduct` (whole) | 5.6 s | 12.8 s |
  | `mulPacked` end-to-end (`isSome`) | 8.9 s | 17.4 s |

  In the first draft `inBox` was about 85 % of the shard cost.
- **8192-slot blocks** (64×128 factor, stride 256, the production shard size):
  - `dense` of 8192 terms into 16256 slots: 17.8–19.6 s.
  - `checkShard`, before the kernel-safe walks: `(kernel) deep recursion detected`. The landed `maxAbs`
    (`foldr`, called by `shardFits`) does it on its own at 16k elements.
  - After the refactor, both the 8192-slot and the 2048-slot runs were SIGTERM-ed externally. The 8192-slot run was
    killed at 11.6 GB RSS after 7 min. The 2048-slot run was killed at 73 s while about 5 GB was free on the machine.
    Neither kill was my watchdog; it looks like a machine memory guard. So the full shard at production size is NOT
    measured.
  - Components at 16k elements:

    | Component | Time |
    |---|---|
    | `List.length` | 2.4 s |
    | `cut` | 3.4 s |
    | landed `packShift` | 7.6 s |
    | `reconFitsAux` (constant logs) | 5.8 s |
    | landed `intSlotsBound` on a 16383-slot window, with its packing inputs | 67 s |

## Design signals and uncertainties

1. **The landed SO-POLY-A decoder `intSlotsBound` is the shard bottleneck at production size.** It costs about
   1.5 ms per slot at 511 slots and about 3–4 ms per slot at 16k slots in my runs. SO-REPLAY2 reports about 2.5 s for
   its own `soIntSlotsBound` on 16384 slots (data in a compiled module). The landed body, with Int `%`/`/`,
   `slotRep` and instance chains, appears much slower.
   - Memory: the kernel caches every intermediate residual `X_k`, so it grows like `slots × |X|`.
   - Lever (SO-POLY-A, no signature change for consumers): a Nat/shift-based or divide-and-conquer decoder, proved
     to imply `intSlotsBound`.
   - The landed `packShift` builds lazy `p + …` accumulators, which form a 16k-deep chain at the end. It passed at
     16k but may trip the deep-recursion guard at 32k+ (the "128-row middle size").
   - SO-DATA should give the factor blocks as data constants tied once (SO-REPLAY2's literal route), not recompute
     `dense`/`cut` inside every shard declaration.
2. **Representability.** `ofDyadic` exactness on `CertFixed P` needs `scale ≥ P` (or advice divisible accordingly).
   Otherwise `mulPacked` returns `none` (fail closed). My first replay hit exactly this. SO-DATA's scale rule (the
   largest scale within budget) gives `scale ≫ P` on the lunar data, but the generator should assert it.
3. **Radius.** The remainder is summed over EVERY product slot, gaps included: `b_i = 2^scale` on the target,
   `2^(outLog+1)` elsewhere. The radius is ε-larger than a box-only sum when strides exceed the extents. SO-DATA's
   layouts use tight strides, so they have no gaps.
4. **Kernel speed.** About 10–60 µs per elementary kernel step makes every per-slot operation count. My per-slot
   paths are now about 0.3 ms per `inBox` (digit test). Further constant factors would come from a per-window logs
   table, which needs a different `intSlotsBound` interface.
5. **Not done here (SO-MALG scope).** `CertModel.Encloses.mul` on the packed route and on the fallback is a §8
   model-level test of `Model/Ops`. It is not in this package.

## Divergences from the SO-DATA-PY mirror (`scripts/spin_orbit/sodata_packed.py`, report §1.1 on `inp`)

My Lean bodies are authoritative.

- **`compat`.**

  | Point | Mine | The mirror |
  |---|---|---|
  | No-wrap | `stride_j ≥ stride_{j+1}·(dA_{j+1}+dB_{j+1}−1)` | the exact lower-part bound `stride_j > Σ_{j'>j}(dA+dB−2)·stride_{j'}` |
  | Last stride | `≥ 1` | `= 1` |
  | Extents | not required `≥ 1` (an empty box is rejected later by raw-length positivity) | `≥ 1` |
  | `lo` length | not checked (`getD` default 0) | checked |

  The two no-wrap conditions agree for `n = 2` (row stride `≥ colsA+colsB−1`), the lunar case, and for canonical
  strides. Mine is stricter for padded strides in `n ≥ 3`.
- **`shardFits`.** The maxima are taken over the blocks `0..s` only (`A.take (s+1)`), not all of `A.flatten`. This is
  a looser test (still sound). Every block among them must also have length `≤ L`. The mirror's widths pass mine.
- **`inBox`.** Digit-window test, equal to "`prodKey i` in the target box" (`inBox_eq`); it has no `i < prodLen`
  conjunct. `shapeOK`'s zero check uses `inBox ∧ i < prodLen`, so advice zero-ness is the same as the mirror's.
  `shardLogs` agrees with the mirror whenever the target is a sub-box and the last stride is 1. Then no slot
  `≥ prodLen` decodes into the box.
- **`shapeOK`.** It does not require `lb.blockRows = la.blockRows`; `lb.blockRows` and the target's stride and
  `blockRows` are unused.
- **Zero parts (their §3).** I chose their option 3 and also the zero-dropping half of option 2. `toMants` drops zero
  mantissas, and an empty part is skipped in `packedRealProduct`. **The emitter should emit no advice and no shard
  theorems for all-zero parts.** Any `PackedAdvice` can be passed there; it is never read. For nonzero parts the
  mirror's `support` layouts remain valid, since dropping zero entries changes neither the box nor the dense list.
- `dense`, `slot`, `prodKey`, `blockLen`, `cut`, `shardConv`, `shardLogs`, `combined`, `checkShard` (guard order)
  and `checkPackedProduct` match their readings.

## Errata and deviations

No suspected erratum in a pinned source. Deviations I introduced:

- Several signed `sorry`-body docstrings are extended to describe the implementation. Their statements are unchanged;
  the affected declarations are `compat`, `shardFits`, `blockLen`, `inBox`, `shapeOK`, `checkShard`, `toMants`,
  `mulPacked` and `dense`.
- `intEval` is `noncomputable def` because it is defined outside the signature file's `noncomputable section`.
- In `eval_shift`, the signed premise `hm` is not needed, since keys are added with zero extension. It is consumed by
  `subst`.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §1.16, §5, §8 (P2-P5) and Appendix A-E; design audits 5, 6, 7 (docs/tracks/SO/audits/SO-DESIGN-audit-{5,6,7}.md on main): F12 carry cancellation, F13 scale 0, F14 raw factor lengths are the traps this checker must close. Signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean, SO-POLY-B part.

AUDIT FOCUS (refute-first, this is the trust core of the packed product): (1) every signed declaration matches verbatim; (2) checkPackedProduct_sound's ONLY premise is the checker's success, and its conclusion is the enclosure of the EXACT product for every advice (no trust in the advice): try to build advice that passes every guard yet decodes to a wrong coefficient, at any scale >= 1, with overlapping shards, raw lengths and padding, empty factors; (3) mulPacked_sound at every evaluation dimension; (4) the tests P2-P5 really reduce by decide +kernel and the negative ones are rejected for the stated reason; (5) hygiene. Audit ONLY the five new Poly modules and Tests/Packed.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
