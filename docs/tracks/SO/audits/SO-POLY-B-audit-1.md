# SO-POLY-B independent audit 1

2026-10-29. **Overall: PASS WITH NOTES.** All 50 signed SO-POLY-B declarations are present with the signed statements and concrete bodies. The exact-product slot and strip contracts pass independent type probes, axiom inspection, targeted build and kernel replay. No blocking mathematical or implementation defect was found. The notes concern the permitted stale generated root, documented implementation policies and unmeasured production replay. There is no frozen anchor/provider in this package; this verdict establishes package acceptance, not a frozen seal, model-layer closure or lunar theorem.

## Scope and authority

Report destination is `/root/code/KAM-inp-sopolyb/docs/tracks/SO/audits/SO-POLY-B-audit-1.md`, as explicitly required by the user, overriding the generic brief's main-worktree destination. Only this report is changed. Temporary probes were confined to `.lake/abi-scratch/` and removed after validation. No state-changing git was used.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external `inp-audit-package.md`, the complete package handoff and AUDIT FOCUS, Revision 7 of `/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, the controlling signatures, and design audits 5–7, especially F12–F14 and §8 P2–P5. There is no SO statement file in this worktree. This infrastructure slice has no I/N/P frozen theorem to seal; provider/frozen seal probes are therefore inapplicable. Its authority is the exact SO signature/design surface. No draft signature module was imported by the production code or probes.

Audited HEAD `b339e88f44efb2e5b0fa342c12afad0850a6cd51`; `inp` at comparison `9ce9e8482be9e2a6cc40e532d7b1dd767572da1b`; merge base `da24255de56d349062678b5bcfbb629aed5f8c98`. The handoff's `590a7afd` is the preceding implementation commit; HEAD adds the audit request. Full `git diff inp...HEAD` contains only the six new Lean files and the handoff: 2,911 insertions. No inherited protected-path changes.

Authority SHA256:

- `SOSignatures.lean`: `9a4652019186e914a0ccfdba6e01c903e458b679d0c057ac4cf7b7d353a4c1cc`.
- Revision 7 design: `4576b12f60f8eec34eac5bd93f14870aa0c1c90dd74c303546b0b06ff1617d8f`.

## Refutation review

**F12, closed in implementation.** `Advice.lean:308` reconstructs the exact shard using the decoded residual, exact packing identity, equal lengths and injectivity. Crucially, `shardFits` bounds the exact convolution and `reconFits` bounds the reconstructed advice-plus-residual, rather than trusting either the advice or the decoder to imply this second bound. `reconFitsAux_eq` identifies the executable Nat guard with the signed Int guard. Prefix maxima in `shardFits` are sufficient because every contributing block index is at most `s`. `checkShard_sound` at line 601 has only checker success as its proof premise. P2 checks shape success, successful carry-cancelled residual decoding, failed reconstruction guard and rejection by both checkers. The independent probe additionally reduces the executable reconstruction guard to false.

**F13, closed in implementation.** `shapeOK` at `Advice.lean:568` enforces `1 ≤ scale` and positive block length. `OverlapAdd.lean:96` proves the two-window bound with the stronger first-block bound needed for induction. Windows are exactly `2L-1` long and spaced by `L`; there is no hidden assumption about the number of blocks. The identity `2 * 2^(scale-1) = 2^scale` is paid using the exported scale guard. P3 accepts and attains the bound two. P4 shows every local shard accepts at zero scale while the whole check rejects; its error is two. Although the committed P4 rejection uses the general negative contract, the auditor independently repeated that rejection by `decide +kernel`.

**F14, closed in implementation.** Raw lengths and positivity are checked before the success theorem is applied (`Advice.lean:618,645`). Cutting preserves the raw data up to a zero tail (`cut_flatten`), and exact convolution equals exact-shard overlap-add at every slot (`OverlapAdd.lean:178`). The proof equates packings at every width, then chooses a sufficiently large width for injectivity; it does not assume injectivity at an insufficient runtime width. `combined` zero-extends before cropping to `prodLen`. Its length is exactly the canonical raw convolution length. P5 explicitly accepts `[0,0]`, rejects `[0]`, and proves their cut blocks coincide. Both empty raw-factor positions were independently reduced to rejection. No accepted malformed shape was found.

**Whole-product contract.** `checkPackedProduct_sound` at `OverlapAdd.lean:331` has only success as its premise, with arbitrary advice/data implicitly quantified. It bounds the exact `listConv`, gives the exact output length, and bounds the exact off-target coefficient itself. The stronger helper `checkPackedProduct_slots` first bounds exact convolution minus scaled combined advice and proves combined advice is zero off target. Shape tests forbid nonzero advice outside the target or beyond the product window; cropping cannot silently hide unchecked nonzero advice. Attempted failure routes were carry aliases, zero scale, padding aliases, empty inputs, wrapping layouts, wrong mantissas and wrong-length/out-of-box keys. No counterexample to the advertised enclosure was established. Rounded coefficients need not equal the exact coefficients: the promised result is the explicit bounded error.

**Every evaluation dimension.** Exact key lengths are checked by `slot`; compatible factor keys have equal lengths, and their sum is decoded exactly by `prodKey_slot_add`. `certKeyFun_zipWith_add` then works for every evaluation dimension, including truncation and zero extension. The stronger `Layout.lean:673` theorem `intEval_mul_of_compat` separates layout dimension `m` from evaluation dimension `n`. `packedRealProduct_sound` uses that stronger theorem. `mulPacked_sound` at `MulPacked.lean:412` has no dimension/layout equality premise. A fresh probe constructs an accepted production-backend example with its enclosure quantified over **all** `n`, not just the sample layout's dimension two.

**Strip and backend attachment.** The untrusted decoder's outputs are rechecked by `mantCheck`. Zero dropping preserves integer evaluation; an empty real part is exact zero and legitimately bypasses advice. Four real products are combined with the correct real subtraction and imaginary factors. `ofDyadicScaled_sound` handles both orders of scale and `2P`; exact representability fails closed. Radius bounds sum over every product slot, including gaps/off-target slots, use full-key absolute degree as an upper bound at any evaluation dimension, divide by `2^(2P)`, and round upwards through backend laws. `LawfulCertArith` and `checkWeight` are standing arithmetic/weight premises, not conclusion-shaped product hypotheses. No hard step is supplied as bundled certificate data.

## Notes, definition semantics and remaining scope

- `compat` uses the sufficient adjacent-stride condition `s_j ≥ s_(j+1) * e_(j+1)` and permits a last stride greater than one. It is sound but stricter than the Python mirror for some padded layouts in dimension at least three. The signed docstring's phrase “each stride at least the sum of the two factor extents minus one” omits the next-stride multiplier outside the two-dimensional/canonical setting (`SOSignatures.lean:241`; implementation `Layout.lean:277`). The implementation docstring states the actual condition. This is a documentation ambiguity, not a weakened soundness conclusion or a pinned-source erratum.
- Layout lists use literal zero defaults for missing origins and strides. `compat` requires exact dimension/stride lengths and common factor strides; missing origins mean zero coordinates consistently. Empty extent boxes have dense length zero; whole raw checks reject them. Dimension-zero layouts have the singleton constant slot. Target strides/blockRows and `lb.blockRows` are unused by the intended slot/window interpretation. They are untrusted metadata, not unchecked mathematical facts.
- `cut` at block length zero is a total fuel-limited operation producing zero-length blocks; successful whole checks require positive block length, so this totalization is not used to prove preservation. Similar helper truncations (`zipWith`, fuel-limited fill/walks, digit defaults) have their needed length/range premises stated and discharged. `packFill` only implements the scatter meaning under its increasing-slot/start premises; `dense` checks these. Neither fallback is used as an unconditional identity.
- `inBox` checks decoded keys, without a product-length conjunct; `windowZeroOK` separately checks product length. `inBox_eq` proves equivalence with the target slot-presence test under the stride-length condition exported by compatibility. `shapeOK` does not impose arbitrary equality of target strides or factor blockRows because these do not enter its slot/product proof.
- Computational definitions are exposed. `intEval` is explicitly `noncomputable` outside the signature file's noncomputable section; its concrete body is unchanged. Extended algorithm docstrings and the unused signed `eval_shift` length premise are disclosed by the handoff. Zero extension makes the latter mathematically unnecessary; its signed type remains unchanged.
- No production-size performance claim was independently rerun. The handoff explicitly leaves the 8192-slot full-shard replay unmeasured after external terminations. Tiny/small kernel tests and successful proof replay do not establish that SO-DATA's production data fit memory/time. SO-MALG's model enclosure/fallback tests, advice emitter alignment, literal lunar data and final theorem remain outside this package.

Definition classification below: **DATA** means untrusted carrier/configuration; **DEN** means a literal denotation or exact transformation; **ALG** means a checked/total computational algorithm; **TEST** means concrete test data. Every one of the 96 new non-theorem declarations is covered. None is a conclusion-shaped proposition masquerading as input data. All 136 public theorems and all helpers are also listed. PASS in the table concerns this package's declaration; global qualification remains PASS WITH NOTES.

## Declaration inventory

All names have prefix `KAM.Certificate.`. S means signed; H means additional helper; T means test. Each locator is relative to the worktree.

| Node | Declaration | Verdict / classification | Locator / assessment |
|---|---|---|---|
| H | `packDot` | PASS / DEN | `KAM/Certificate/Poly/Layout.lean:34`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDot_cons` | PASS | `KAM/Certificate/Poly/Layout.lean:36`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDot_nil_left` | PASS | `KAM/Certificate/Poly/Layout.lean:40`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDot_add` | PASS | `KAM/Certificate/Poly/Layout.lean:42`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDot_le_packDot` | PASS | `KAM/Certificate/Poly/Layout.lean:60`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDigits` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:81`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packNoWrap` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:87`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDigits_packDot` | PASS | `KAM/Certificate/Poly/Layout.lean:96`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackLayout` | PASS / DATA | `KAM/Certificate/Poly/Layout.lean:162`. Signed type/body matches. |
| H | `PackLayout.keyOffsets` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:170`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.keyInBox` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:175`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackLayout.slot` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:181`. Signed type/body matches. |
| S | `PackLayout.denseLen` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:187`. Signed type/body matches. |
| H | `packSlotTotal` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:191`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packScatter` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:197`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packScatter_eq` | PASS | `KAM/Certificate/Poly/Layout.lean:206`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSlotAux` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:238`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packStrictAsc` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:248`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packFill` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:253`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackLayout.dense` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:262`. Signed type/body matches. |
| S | `PackLayout.prodKey` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:273`. Signed type/body matches. |
| S | `PackLayout.compat` | PASS / ALG | `KAM/Certificate/Poly/Layout.lean:281`. Signed type/body matches. |
| S | `intEval` | PASS / DEN | `KAM/Certificate/Poly/Layout.lean:287`. Signed type/body matches. |
| H | `PackLayout.slot_eq_some` | PASS | `KAM/Certificate/Poly/Layout.lean:292`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.keyOffsets_toNat_getD` | PASS | `KAM/Certificate/Poly/Layout.lean:304`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.slot_lt_denseLen` | PASS | `KAM/Certificate/Poly/Layout.lean:313`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `getD_succ_eq_tail_getD` | PASS | `KAM/Certificate/Poly/Layout.lean:339`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packDot_cons_left` | PASS | `KAM/Certificate/Poly/Layout.lean:342`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSlotAux_eq` | PASS | `KAM/Certificate/Poly/Layout.lean:347`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packStrictAsc_pairwise` | PASS | `KAM/Certificate/Poly/Layout.lean:401`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSlotTotal_eq_zero` | PASS | `KAM/Certificate/Poly/Layout.lean:413`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packFill_eq` | PASS | `KAM/Certificate/Poly/Layout.lean:420`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.dense_spec` | PASS | `KAM/Certificate/Poly/Layout.lean:464`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackLayout.dense_length` | PASS | `KAM/Certificate/Poly/Layout.lean:491`. Signed type/body matches. |
| H | `certKeyFun_zipWith_add` | PASS | `KAM/Certificate/Poly/Layout.lean:498`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.prodKey_slot_add` | PASS | `KAM/Certificate/Poly/Layout.lean:509`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `list_sum_map_range_eq` | PASS | `KAM/Certificate/Poly/Layout.lean:572`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `sum_range_list_fiber` | PASS | `KAM/Certificate/Poly/Layout.lean:581`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `sum_range_fiber_mul` | PASS | `KAM/Certificate/Poly/Layout.lean:600`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `sum_range_cauchy_weighted` | PASS | `KAM/Certificate/Poly/Layout.lean:610`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.dense_getD_cast` | PASS | `KAM/Certificate/Poly/Layout.lean:649`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackLayout.intEval_mul_of_compat` | PASS | `KAM/Certificate/Poly/Layout.lean:673`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackLayout.intEval_mul` | PASS | `KAM/Certificate/Poly/Layout.lean:771`. Signed type/body matches. |
| S | `PackedAdvice` | PASS / DATA | `KAM/Certificate/Poly/Advice.lean:32`. Signed type/body matches. |
| S | `reconSlots` | PASS / DEN | `KAM/Certificate/Poly/Advice.lean:43`. Signed type/body matches. |
| S | `packSum_reconSlots` | PASS | `KAM/Certificate/Poly/Advice.lean:46`. Signed type/body matches. |
| S | `reconFits` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:63`. Signed type/body matches. |
| H | `reconFitsAux` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:68`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `reconFitsAux_eq_all` | PASS | `KAM/Certificate/Poly/Advice.lean:73`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `reconFitsAux_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:90`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `slotsBounded_reconSlots` | PASS | `KAM/Certificate/Poly/Advice.lean:95`. Signed type/body matches. |
| S | `shardConv` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:120`. Signed type/body matches. |
| S | `shardConv_length` | PASS | `KAM/Certificate/Poly/Advice.lean:126`. Signed type/body matches. |
| H | `shardConv_getD` | PASS | `KAM/Certificate/Poly/Advice.lean:130`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSum_eq_sum_of_length_le` | PASS | `KAM/Certificate/Poly/Advice.lean:137`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `packSum_shardConv` | PASS | `KAM/Certificate/Poly/Advice.lean:145`. Signed type/body matches. |
| H | `packLenEq` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:183`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packLenEq_iff` | PASS | `KAM/Certificate/Poly/Advice.lean:188`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packLenLe` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:194`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packLenLe_iff` | PASS | `KAM/Certificate/Poly/Advice.lean:199`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packLengthAux` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:205`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packLengthAux_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:209`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packMaxAbsAux` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:217`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packMaxAbsAux_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:221`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `shardFits` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:232`. Signed type/body matches. |
| H | `maxAbs_le_of_forall` | PASS | `KAM/Certificate/Poly/Advice.lean:238`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `maxAbs_getD_le_take` | PASS | `KAM/Certificate/Poly/Advice.lean:247`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `length_getD_le_take` | PASS | `KAM/Certificate/Poly/Advice.lean:258`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `slotsBounded_shardConv` | PASS | `KAM/Certificate/Poly/Advice.lean:269`. Signed type/body matches. |
| S | `shard_reconstruct` | PASS | `KAM/Certificate/Poly/Advice.lean:308`. Signed type/body matches. |
| S | `PackedAdvice.blockLen` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:337`. Signed type/body matches. |
| H | `packTakePad` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:340`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packTakePad_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:345`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packCutAux` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:356`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackedAdvice.cut` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:361`. Signed type/body matches. |
| H | `packCutAux_length` | PASS | `KAM/Certificate/Poly/Advice.lean:364`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackedAdvice.cut_length` | PASS | `KAM/Certificate/Poly/Advice.lean:376`. Signed type/body matches. |
| H | `packCutAux_nil` | PASS | `KAM/Certificate/Poly/Advice.lean:380`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packCutAux_flatten` | PASS | `KAM/Certificate/Poly/Advice.lean:384`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.cut_flatten` | PASS | `KAM/Certificate/Poly/Advice.lean:405`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `listConv_length` | PASS | `KAM/Certificate/Poly/Advice.lean:410`. Signed type/body matches. |
| S | `PackedAdvice.prodLen` | PASS / DEN | `KAM/Certificate/Poly/Advice.lean:418`. Signed type/body matches. |
| H | `packDigitsIn` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:422`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.boxLow` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:428`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.boxHigh` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:433`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackedAdvice.inBox` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:442`. Signed type/body matches. |
| S | `PackedAdvice.shardLogs` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:447`. Signed type/body matches. |
| H | `packAddZ` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:451`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packOverlapAdd` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:457`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackedAdvice.combined` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:465`. Signed type/body matches. |
| S | `PackedAdvice.combined_length` | PASS | `KAM/Certificate/Poly/Advice.lean:468`. Signed type/body matches. |
| H | `packDigitsIn_iff` | PASS | `KAM/Certificate/Poly/Advice.lean:472`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.inBox_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:493`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.windowZeroOK` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:542`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.adviceZeroOK` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:548`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.targetSubBox` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:554`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `PackedAdvice.shapeOK` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:568`. Signed type/body matches. |
| H | `shardPacked` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:576`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `checkShard` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:585`. Signed type/body matches. |
| H | `shardPacked_eq` | PASS | `KAM/Certificate/Poly/Advice.lean:594`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `checkShard_sound` | PASS | `KAM/Certificate/Poly/Advice.lean:601`. Signed type/body matches. |
| S | `checkPackedProduct` | PASS / ALG | `KAM/Certificate/Poly/Advice.lean:618`. Signed type/body matches. |
| H | `checkPackedProduct_eq_true_iff` | PASS | `KAM/Certificate/Poly/Advice.lean:627`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.shapeOK_scale` | PASS | `KAM/Certificate/Poly/Advice.lean:639`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `checkPackedProduct_guards` | PASS | `KAM/Certificate/Poly/Advice.lean:645`. Signed type/body matches. |
| S | `checkPackedProduct_scale_zero` | PASS | `KAM/Certificate/Poly/Advice.lean:657`. Signed type/body matches. |
| S | `checkPackedProduct_raw_length` | PASS | `KAM/Certificate/Poly/Advice.lean:665`. Signed type/body matches. |
| S | `packSum_audit5_cancel` | PASS | `KAM/Certificate/Poly/Advice.lean:676`. Signed type/body matches. |
| S | `reconFits_audit5_rejects` | PASS | `KAM/Certificate/Poly/Advice.lean:678`. Signed type/body matches. |
| H | `packSum_replicate_zero` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:29`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSum_append_replicate_zero` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:34`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `getD_append_replicate_zero` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:38`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `getD_replicate_zero_append` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:47`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packAddZ_getD` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:55`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSum_packAddZ` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:64`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packOverlapAdd_cons_getD` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:72`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packSum_packOverlapAdd` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:78`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packOverlapAdd_sub_abs_le` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:96`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packOverlapAdd_getD_eq_zero` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:145`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `eq_of_packSum_forall` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:163`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `listConv_getD_eq_overlapAdd` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:178`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.windowZeroOK_spec` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:205`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.adviceZeroOK_spec` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:224`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.combined_getD_eq_zero` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:239`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `checkPackedProduct_slots` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:266`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `checkPackedProduct_sound` | PASS | `KAM/Certificate/Poly/OverlapAdd.lean:331`. Signed type/body matches. |
| H | `certMantPair` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:36`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `mantSel` | PASS / DEN | `KAM/Certificate/Poly/MulPacked.lean:43`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `certMantPart` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:46`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `CertPoly.toMants` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:55`. Signed type/body matches. |
| H | `intEval_nil` | PASS | `KAM/Certificate/Poly/MulPacked.lean:62`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_cons` | PASS | `KAM/Certificate/Poly/MulPacked.lean:64`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_append` | PASS | `KAM/Certificate/Poly/MulPacked.lean:68`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_map_neg` | PASS | `KAM/Certificate/Poly/MulPacked.lean:72`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `certMantPair_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:81`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_filterMap_certMantPart` | PASS | `KAM/Certificate/Poly/MulPacked.lean:96`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `CertPoly.toMants_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:113`. Signed type/body matches. |
| H | `packRangeSum` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:137`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packRangeSum_eq` | PASS | `KAM/Certificate/Poly/MulPacked.lean:144`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packRangeMax` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:158`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `le_foldr_max_of_mem` | PASS | `KAM/Certificate/Poly/MulPacked.lean:165`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `le_packRangeMax` | PASS | `KAM/Certificate/Poly/MulPacked.lean:174`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.slotDeg` | PASS / DEN | `KAM/Certificate/Poly/MulPacked.lean:194`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.slotErr` | PASS / DEN | `KAM/Certificate/Poly/MulPacked.lean:199`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.maxSlotDeg` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:203`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.remainderBound` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:209`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.targetEntry` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:215`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.targetTerms` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:221`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packedRealProduct` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:227`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_targetEntry` | PASS | `KAM/Certificate/Poly/MulPacked.lean:236`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `intEval_targetTerms` | PASS | `KAM/Certificate/Poly/MulPacked.lean:252`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `PackedAdvice.shapeOK_compat` | PASS | `KAM/Certificate/Poly/MulPacked.lean:259`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `remainderBound_mul` | PASS | `KAM/Certificate/Poly/MulPacked.lean:264`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `packedRealProduct_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:290`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `ofDyadicScaled` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:347`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `ofDyadicScaled_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:350`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `dyadicTerms` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:366`. Proof/helper semantics reviewed; explicit premises preserved. |
| H | `dyadicTerms_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:372`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `CertPoly.mulPacked` | PASS / ALG | `KAM/Certificate/Poly/MulPacked.lean:397`. Signed type/body matches. |
| S | `CertPoly.mulPacked_sound` | PASS | `KAM/Certificate/Poly/MulPacked.lean:412`. Signed type/body matches. |
| S | `ProductAdvice` | PASS / DATA | `KAM/Certificate/Poly/MulPacked.lean:483`. Signed type/body matches. |
| S | `ProductKey` | PASS / DATA | `KAM/Certificate/Poly/MulPacked.lean:490`. Signed type/body matches. |
| S | `AdviceBook` | PASS / DATA | `KAM/Certificate/Poly/MulPacked.lean:492`. Signed type/body matches. |
| S | `CertPoly.shift` | PASS / DEN | `KAM/Certificate/Poly/Ops.lean:28`. Signed type/body matches. |
| H | `certKeyFun_packAddZ` | PASS | `KAM/Certificate/Poly/Ops.lean:31`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `CertPoly.eval_shift` | PASS | `KAM/Certificate/Poly/Ops.lean:36`. Signed type/body matches. |
| S | `CertPoly.conjReflect` | PASS / DEN | `KAM/Certificate/Poly/Ops.lean:48`. Signed type/body matches. |
| H | `character_neg_eq_conj` | PASS | `KAM/Certificate/Poly/Ops.lean:51`. Proof/helper semantics reviewed; explicit premises preserved. |
| S | `CertPoly.eval_conjReflect` | PASS | `KAM/Certificate/Poly/Ops.lean:60`. Signed type/body matches. |
| T | `packedTestLay2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:45`. Concrete control / derived contract. |
| T | `packedTestTarget2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:48`. Concrete control / derived contract. |
| T | `packedTestA2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:50`. Concrete control / derived contract. |
| T | `packedTestB2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:53`. Concrete control / derived contract. |
| T | `packedTestAdv2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:57`. Concrete control / derived contract. |
| T | `packedTest_dense2` | PASS | `KAM/Certificate/Tests/Packed.lean:62`. Concrete control / derived contract. |
| T | `packedTest_dense2_scatter` | PASS | `KAM/Certificate/Tests/Packed.lean:68`. Concrete control / derived contract. |
| T | `packedTest_dense2_badKey` | PASS | `KAM/Certificate/Tests/Packed.lean:74`. Concrete control / derived contract. |
| T | `packedTest_pass2` | PASS | `KAM/Certificate/Tests/Packed.lean:77`. Concrete control / derived contract. |
| T | `packedTest_sound2` | PASS | `KAM/Certificate/Tests/Packed.lean:83`. Concrete control / derived contract. |
| T | `packedTestRe` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:89`. Concrete control / derived contract. |
| T | `packedTestIm` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:93`. Concrete control / derived contract. |
| T | `packedTestW` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:97`. Concrete control / derived contract. |
| T | `packedTest_weight` | PASS | `KAM/Certificate/Tests/Packed.lean:99`. Concrete control / derived contract. |
| T | `packedTestBogus` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:103`. Concrete control / derived contract. |
| T | `packedTest_mulPacked2` | PASS | `KAM/Certificate/Tests/Packed.lean:105`. Concrete control / derived contract. |
| T | `packedTest_mulPacked2_encloses` | PASS | `KAM/Certificate/Tests/Packed.lean:112`. Concrete control / derived contract. |
| T | `packedTest_mulPacked2_reIm` | PASS | `KAM/Certificate/Tests/Packed.lean:122`. Concrete control / derived contract. |
| T | `packedTestLay3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:131`. Concrete control / derived contract. |
| T | `packedTestTarget3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:134`. Concrete control / derived contract. |
| T | `packedTestA3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:136`. Concrete control / derived contract. |
| T | `packedTestB3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:139`. Concrete control / derived contract. |
| T | `packedTestAdv3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:142`. Concrete control / derived contract. |
| T | `packedTest_pass3` | PASS | `KAM/Certificate/Tests/Packed.lean:148`. Concrete control / derived contract. |
| T | `packedTest_mulPacked3` | PASS | `KAM/Certificate/Tests/Packed.lean:153`. Concrete control / derived contract. |
| T | `packedTestLayM` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:162`. Concrete control / derived contract. |
| T | `packedTestTargetM` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:164`. Concrete control / derived contract. |
| T | `packedTestAM` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:166`. Concrete control / derived contract. |
| T | `packedTestBM` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:169`. Concrete control / derived contract. |
| T | `packedTestAdvM` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:172`. Concrete control / derived contract. |
| T | `packedTest_cutM` | PASS | `KAM/Certificate/Tests/Packed.lean:177`. Concrete control / derived contract. |
| T | `packedTest_passM` | PASS | `KAM/Certificate/Tests/Packed.lean:181`. Concrete control / derived contract. |
| T | `packedTest_mulPackedM` | PASS | `KAM/Certificate/Tests/Packed.lean:186`. Concrete control / derived contract. |
| T | `packedTestAdv2Off` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:195`. Concrete control / derived contract. |
| T | `packedTest_offByTwo` | PASS | `KAM/Certificate/Tests/Packed.lean:200`. Concrete control / derived contract. |
| T | `packedTestAdv2Alias` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:207`. Concrete control / derived contract. |
| T | `packedTest_alias_packs` | PASS | `KAM/Certificate/Tests/Packed.lean:212`. Concrete control / derived contract. |
| T | `packedTest_alias_rejected` | PASS | `KAM/Certificate/Tests/Packed.lean:217`. Concrete control / derived contract. |
| T | `packedTestLayWrap` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:223`. Concrete control / derived contract. |
| T | `packedTest_wrap_compat` | PASS | `KAM/Certificate/Tests/Packed.lean:225`. Concrete control / derived contract. |
| T | `packedTest_wrap_rejected` | PASS | `KAM/Certificate/Tests/Packed.lean:229`. Concrete control / derived contract. |
| T | `packedTest_wrongDecoder` | PASS | `KAM/Certificate/Tests/Packed.lean:235`. Concrete control / derived contract. |
| T | `packedTest_keyOutside` | PASS | `KAM/Certificate/Tests/Packed.lean:242`. Concrete control / derived contract. |
| T | `packedTestLayP2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:251`. Concrete control / derived contract. |
| T | `packedTestAdvP2` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:254`. Concrete control / derived contract. |
| T | `packedTest_P2_shape` | PASS | `KAM/Certificate/Tests/Packed.lean:257`. Concrete control / derived contract. |
| T | `packedTest_P2_decodes` | PASS | `KAM/Certificate/Tests/Packed.lean:260`. Concrete control / derived contract. |
| T | `packedTest_P2_reconFits` | PASS | `KAM/Certificate/Tests/Packed.lean:265`. Concrete control / derived contract. |
| T | `packedTest_P2_rejected` | PASS | `KAM/Certificate/Tests/Packed.lean:269`. Concrete control / derived contract. |
| T | `packedTestLayP3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:277`. Concrete control / derived contract. |
| T | `packedTestAdvP3` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:279`. Concrete control / derived contract. |
| T | `packedTest_P3_passes` | PASS | `KAM/Certificate/Tests/Packed.lean:283`. Concrete control / derived contract. |
| T | `packedTest_P3_attained` | PASS | `KAM/Certificate/Tests/Packed.lean:288`. Concrete control / derived contract. |
| T | `packedTest_P3_bound` | PASS | `KAM/Certificate/Tests/Packed.lean:292`. Concrete control / derived contract. |
| T | `packedTestAdvP4` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:301`. Concrete control / derived contract. |
| T | `packedTest_P4_shards` | PASS | `KAM/Certificate/Tests/Packed.lean:306`. Concrete control / derived contract. |
| T | `packedTest_P4_rejected` | PASS | `KAM/Certificate/Tests/Packed.lean:310`. Concrete control / derived contract. |
| T | `packedTest_P4_error` | PASS | `KAM/Certificate/Tests/Packed.lean:315`. Concrete control / derived contract. |
| T | `packedTestAdvP5` | PASS / TEST | `KAM/Certificate/Tests/Packed.lean:323`. Concrete control / derived contract. |
| T | `packedTest_P5_sameBlocks` | PASS | `KAM/Certificate/Tests/Packed.lean:326`. Concrete control / derived contract. |
| T | `packedTest_P5_long` | PASS | `KAM/Certificate/Tests/Packed.lean:330`. Concrete control / derived contract. |
| T | `packedTest_P5_short` | PASS | `KAM/Certificate/Tests/Packed.lean:334`. Concrete control / derived contract. |
| T | `packedTest_P5_short_kernel` | PASS | `KAM/Certificate/Tests/Packed.lean:337`. Concrete control / derived contract. |

## Independent validation receipts

Every Lean/Lake invocation was serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. Lint was run only after the axiom/type probe finished because it invokes Lean for ABI hashes. No budget overrides, clean/update/cache operation, generated-root regeneration or package edits were performed.

1. Full comparison: `git diff inp...HEAD`; protected comparison `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. `git diff --check inp...HEAD` produced no output, exit 0.
2. Targeted build, exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sopolyb KAM.Certificate.Poly.Layout KAM.Certificate.Poly.Advice KAM.Certificate.Poly.OverlapAdd KAM.Certificate.Poly.MulPacked KAM.Certificate.Poly.Ops KAM.Certificate.Tests.Packed
```

Output: `[inp-gate] slot 1 acquired 17:35:20 ...`; `Build completed successfully (2912 jobs).` Only the pre-existing `KAM/Certificate/Arith/PiHigh.lean:218:8` unused `Nat.succ_eq_add_one` simp-argument warning was replayed. No package warning.

3. Signature comparison: `python3 .drafts/SO-POLY-B-replay/sigcheck.py`, exit 0, output `checked 50 bad 0`. Independently tightened its concrete-body comparison to equality (not prefix matching): all concrete bodies, structures, inductive and abbrevs match after whitespace normalization; only the documented `noncomputable` modifier is normalized. The 46-entry contiguous PackLayout-through-AdviceBook slice and four Ops declarations account for all 50 signed declarations. Namespace review confirms every full name is `KAM.Certificate.<signed name>`; there are no intervening namespaces or local semantic replacements.

4. Fresh scratch probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-sopolyb-1.lean
```

Exit 0. Probe imported only `KAM.Certificate.Tests.Packed`, copied all 20 placeholder-bodied signed theorem headers verbatim as fresh examples using the actual exports (`by apply KAM.Certificate.<name> <;> assumption`), queried axioms of all 136 new public theorems, and added five examples: direct kernel rejection of P4, both empty raw-factor positions, the executable P2 reconstruction guard, and the all-evaluation-dimensions strip enclosure. The two signed concrete theorem bodies were checked by exact source equality and axiom/kernel checks. Probe-only redundant-tactic linter warnings occurred in the generic application bodies; no error or production change. Probe removed afterward.

5. Kernel replay, one invocation, exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Poly.Layout KAM.Certificate.Poly.Advice KAM.Certificate.Poly.OverlapAdd KAM.Certificate.Poly.MulPacked KAM.Certificate.Poly.Ops KAM.Certificate.Tests.Packed
```

Exact output:

```text
replaying KAM.Certificate.Tests.Packed
replaying KAM.Certificate.Poly.Ops
replaying KAM.Certificate.Poly.MulPacked
replaying KAM.Certificate.Poly.OverlapAdd
replaying KAM.Certificate.Poly.Advice
replaying KAM.Certificate.Poly.Layout
```

6. Short names, exit 0:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sopolyb KAM.Certificate.Poly.Layout KAM.Certificate.Poly.Advice KAM.Certificate.Poly.OverlapAdd KAM.Certificate.Poly.MulPacked KAM.Certificate.Poly.Ops KAM.Certificate.Tests.Packed
```

Output: `short-name check OK (no reused public short name)`. The checker scans undotted/dotted helper short names against KAM/Mathlib and other unmerged branches, with design-signed names exempt by the naming policy. Approved namespaced API suffixes such as `shift`/`dense` are therefore not newly invented helper collisions. All code lives under `KAM.Certificate`; no harmful root shadow found. An initial invocation mistakenly supplied file paths rather than module names; it was discarded and rerun with the correct module arguments above.

7. Hygiene: no forbidden proof escapes, `native_decide`, resource overrides or `EuclideanSpace` in scoped code. All six files have copyright, `module`, public imports, module documentation and public sections. Line counts/max columns: Layout 779/100; Advice 680/100; OverlapAdd 344/99; MulPacked 494/98; Ops 68/95; Tests/Packed 340/100. The facade publicly reexports the packed chain. Direct imports contain no provider or draft anchor; full exported-theorem axiom results exclude inherited `sorryAx` as well.

8. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the permitted generated-root staleness. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1343 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure was printed. Frozen-anchor guard and all 144 ABI hashes passed.

## Exact theorem axiom output

136 public theorem queries: 95 use `[propext, Classical.choice, Quot.sound]`, 17 use `[propext, Quot.sound]`, 22 use `[propext]`, and two use no axioms. No `sorryAx`, custom axiom or native evaluator axiom. Exact output follows; each queried name also appears in the inventory above.

```text
'KAM.Certificate.packDot_cons' depends on axioms: [propext]
'KAM.Certificate.packDot_nil_left' depends on axioms: [propext]
'KAM.Certificate.packDot_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packDot_le_packDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packDigits_packDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packScatter_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackLayout.slot_eq_some' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackLayout.keyOffsets_toNat_getD' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackLayout.slot_lt_denseLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.getD_succ_eq_tail_getD' depends on axioms: [propext]
'KAM.Certificate.packDot_cons_left' depends on axioms: [propext]
'KAM.Certificate.packSlotAux_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packStrictAsc_pairwise' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSlotTotal_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packFill_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackLayout.dense_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackLayout.dense_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certKeyFun_zipWith_add' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackLayout.prodKey_slot_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.list_sum_map_range_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_range_list_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_range_fiber_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_range_cauchy_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackLayout.dense_getD_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackLayout.intEval_mul_of_compat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackLayout.intEval_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_reconSlots' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.reconFitsAux_eq_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.reconFitsAux_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotsBounded_reconSlots' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.shardConv_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.shardConv_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_eq_sum_of_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_shardConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packLenEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packLenLe_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packLengthAux_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packMaxAbsAux_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.maxAbs_le_of_forall' depends on axioms: [propext]
'KAM.Certificate.maxAbs_getD_le_take' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.length_getD_le_take' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotsBounded_shardConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.shard_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packTakePad_eq' depends on axioms: [propext]
'KAM.Certificate.packCutAux_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackedAdvice.cut_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packCutAux_nil' depends on axioms: [propext]
'KAM.Certificate.packCutAux_flatten' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackedAdvice.cut_flatten' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.listConv_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.PackedAdvice.combined_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packDigitsIn_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.inBox_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.shardPacked_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkShard_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.shapeOK_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_guards' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_scale_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_raw_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_audit5_cancel' depends on axioms: [propext]
'KAM.Certificate.reconFits_audit5_rejects' depends on axioms: [propext]
'KAM.Certificate.packSum_replicate_zero' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSum_append_replicate_zero' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.getD_append_replicate_zero' depends on axioms: [propext]
'KAM.Certificate.getD_replicate_zero_append' depends on axioms: [propext]
'KAM.Certificate.packAddZ_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_packAddZ' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packOverlapAdd_cons_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_packOverlapAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packOverlapAdd_sub_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packOverlapAdd_getD_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.eq_of_packSum_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.listConv_getD_eq_overlapAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.windowZeroOK_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.adviceZeroOK_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.combined_getD_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_map_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certMantPair_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_filterMap_certMantPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.toMants_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packRangeSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.le_foldr_max_of_mem' depends on axioms: [propext]
'KAM.Certificate.le_packRangeMax' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.intEval_targetEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intEval_targetTerms' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.shapeOK_compat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.remainderBound_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ofDyadicScaled_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dyadicTerms_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certKeyFun_packAddZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_neg_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_conjReflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_dense2' depends on axioms: [propext]
'KAM.Certificate.packedTest_dense2_scatter' depends on axioms: [propext]
'KAM.Certificate.packedTest_dense2_badKey' depends on axioms: [propext]
'KAM.Certificate.packedTest_pass2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_sound2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_mulPacked2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_mulPacked2_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_mulPacked2_reIm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_pass3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_mulPacked3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_cutM' does not depend on any axioms
'KAM.Certificate.packedTest_passM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_mulPackedM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_offByTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_alias_packs' depends on axioms: [propext]
'KAM.Certificate.packedTest_alias_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_wrap_compat' depends on axioms: [propext]
'KAM.Certificate.packedTest_wrap_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_wrongDecoder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_keyOutside' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P2_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P2_decodes' depends on axioms: [propext]
'KAM.Certificate.packedTest_P2_reconFits' depends on axioms: [propext]
'KAM.Certificate.packedTest_P2_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P3_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P3_attained' depends on axioms: [propext]
'KAM.Certificate.packedTest_P3_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P4_shards' depends on axioms: [propext]
'KAM.Certificate.packedTest_P4_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P4_error' depends on axioms: [propext]
'KAM.Certificate.packedTest_P5_sameBlocks' does not depend on any axioms
'KAM.Certificate.packedTest_P5_long' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P5_short' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_P5_short_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Errata, deviations and handoff

No new suspected defect in a pinned mathematical source or frozen theorem was established. The compatibility docstring ambiguity and conservative/unused metadata policies are recorded above with locations; the implementation supplies sound checked objects and preserves every signed contract. Auditor introduced no mathematical deviation. The generated-root exception is explicitly authorized by the audit brief and was left untouched. This audit closes the scoped F12/F13/F14 implementation obligations and P2–P5 controls, while retaining production replay and downstream model/data obligations.

Files written: this report only. Approach: full three-dot source review, declaration-by-declaration signature/definition/premise review, guard refutation controls, exhaustive public theorem axioms, targeted compile gate, kernel replay, naming and source hygiene checks. No frozen anchor was sealed and no campaign theorem closure is claimed.
