# SO-CSEG-L3 handoff (audit request): the product split

Branch `inp-csegl3` off `c2a38f5b`. Design: `docs/tracks/SO/design/SO-CSPLIT.md` §3.5 (M3), §8 row SO-CSEG-L3;
signatures `.drafts/design/SOCsplitSignatures.lean` §(D).

## Files
- `KAM/CertificateSharp/Kernel/ProductSplit.lean` (new, 163 lines; imports `KAM.Certificate.Expr.Compose` only).
- `KAM/CertificateSharp/Tests/ProductSplit.lean` (new, 167 lines; toy tests).
- This handoff.

No landed definition or statement changed. No file of SO-CSEG-A/B touched.

## Signatures against the audited design
The module body from `CertModel.mulN_eq_of_polyProduct` to `expResidualProduct_eq_of_polyProduct` is a
verbatim copy of the signatures file §(D) up to (excluding) `shadowStep_of_live`/`segOk_one_of` which belong to §(C):
`diff` of the two extracted blocks is empty (`IDENTICAL`). Items, all proved, statements unchanged:
`CertModel.mulN_eq_of_polyProduct`, `polyProduct_eq_of_mulPacked` (F2), `CertPoly.mulPacked_eq_of_parts` (F2),
`packedRealProduct_eq_nil_left`, `packedRealProduct_eq_nil_right`, `packedRealProduct_eq_of_sparse` (F3),
defs `checkPackedSpPrefix`, `PackedAdvice.shardRange`, `checkShardAt`, `checkPackedSp_of_groups` (F3),
`charResolve_eq_of_radius`, `expWitnessRadius_eq_of_pin`, `expWitnessRadiusOf_eq_of_residuals`,
`expResidualProduct_eq_of_polyProduct`.

**Not delivered (blocked on SO-CSEG-A):** the row's second module `Kernel/SegOne.lean` (`ComposeCkpt.segOk_one_of`,
`seed_slot_of_mem`, `shadowStep_of_live`, the `composeStep` arm equations). They are stated over `SegSpec`,
`ComposeCkpt`, `ComposeState.seed`, `shadowStep`, `segOk` from `Kernel/SegDefs.lean`, which is not in this tree
(being written on `inp-socsplit2`). I did not duplicate those definitions. SegOne should be a follow-up once A lands.

## Tests (`Tests/ProductSplit.lean`, all `decide +kernel` on small data)
Data are copies of `KAM.Certificate.Tests.Packed` (that module's defs are not `@[expose]`d, so the kernel cannot
unfold them from another module).
- `splitTest_agree`: `checkPackedSp = checkPackedSpPrefix && shardRange.all checkShardAt` on the n=2 product, the
  five-window product, the off-by-two advice (both `false`) and descending slots.
- `splitTest_groupsM`: `checkPackedSp_of_groups` with groups `[[0,1,2],[3,4]]`, each group decided apart.
- `splitTest_realM` (via `_eq_of_sparse` from the grouped check) and `splitTest_realM_whole` (whole kernel run):
  same value. `splitTest_nil`: empty lemmas with bogus advice.
- `splitTest_mulPackedM`: the whole `mulPacked` equals the value assembled by `mulPacked_eq_of_parts` from the
  separately proved real part, three empty parts and the separately proved decode (`splitTest_decodeM`).
  (No whole-vs-whole kernel comparison: `CertFixed` has no landed `DecidableEq`; the theorem itself is the equality.)

## Checks
- `inp_lake_build.sh … KAM.CertificateSharp.Kernel.ProductSplit KAM.CertificateSharp.Tests.ProductSplit`:
  `Build completed successfully (2965 jobs)`; zero warnings in the new files (warnings shown are in landed
  `Expr/Basic.lean`).
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (1686 Lean files)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (158 frozen declarations)`; it also prints `KAM.lean is out of date; run scripts/gen_root_imports.py
  (KAM/Root/CertificateSharp.lean)` because of the two new modules: the generated root is left to the orchestrator
  (rule 10).
- `main_shortname_check.py` on both modules: `short-name check OK`.
- Lines ≤ 100 columns; no heartbeat/recursion overrides, no sorry.
- Axioms:
```
'KAM.Certificate.CertModel.mulN_eq_of_polyProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.polyProduct_eq_of_mulPacked' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_eq_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_nil_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_nil_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_of_sparse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedSp_of_groups' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charResolve_eq_of_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadius_eq_of_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadiusOf_eq_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expResidualProduct_eq_of_polyProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_groupsM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_realM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_mulPackedM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Uncertainties / notes
- Kernel test runs are tiny (each module builds in ≈ 3 s), so they were not run under the kernel-probe lock.
- An explicit-argument detail: applying `mulPacked_eq_of_parts` with `pRR`… left implicit hit the default
  heartbeat limit in unification (`?pRR.2 =?= remainderBound …` unfolds); giving the parts explicitly fixes it.
  Consumers (SO-CSEG-GEN emitted modules) should pass `pRR … tIR` as named arguments.
- Errata: none suspected. Deviations: none in statements; SegOne deferred as above.
