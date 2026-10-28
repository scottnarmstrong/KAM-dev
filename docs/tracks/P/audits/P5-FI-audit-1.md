# Independent audit 1: P5-FI

Overall package verdict: **PASS WITH NOTES**. The two requested results, `KAM.Planetary.schur_inverse_blocks` and `KAM.Planetary.freq_inj`, pass their exact design signatures and proof review. Notes concern the explicitly declared alternative inverse proof and the inherited comparison/root hygiene discussed below. No blocking mathematical defect found in the six assigned modules.

Frozen-anchor verdict: **P-G remains DRAFT_SORRY; no seal is delivered by this infrastructure package**. Neither result is a provider for `KAM.Planetary.properlyDegenerateKAM`. Provider/frozen-type equality and a P-G seal-body probe are therefore not applicable. Successful infrastructure checks do not certify the frozen KAM theorem.

## Scope and authority

Audited `/root/code/KAM-inp-p5fi`, HEAD `439541a66c17f2ecf1e4c9c3dc4d41f48539beae` (observed inp ref `9400863e51e5f140a497a3774d3dff7b479e0d04`), using the requested `git diff inp...HEAD`. Git warns: `multiple merge bases, using 29c1447c330f69985b055f759e35ce8654e57c3e`. The resulting 64-file diff includes inherited packages and root regeneration. As the handoff explicitly requires, proof review is limited to the following six new files, all under `KAM/Planetary/PGAssembly/`:

| File | Lines |
|---|---:|
| `FrequencySchur.lean` | 42 |
| `FrequencyInvLinear.lean` | 106 |
| `FrequencyInvDeriv.lean` | 222 |
| `FrequencyInvJac.lean` | 126 |
| `FrequencyInvBounds.lean` | 214 |
| `FrequencyInverse.lean` | 171 |

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief, the P5-FI handoff, design P45-LEAN-DESIGN.md (including Revision 4 and Appendix A), design audits 1–4, the shared signatures `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, blueprint-P p5 lines 104–133, and track-P statement P-G. Inspected the frozen P-G telescope and relevant frozen definitions, PGData, FrequencyDefs and the produced FrequencyBounds specification. User instruction controls the report destination: this report is in the package worktree, overriding the generic brief's main-worktree destination.

## Exact interfaces and proof review

The shared signature file at lines 751 (`freq_inj`) and 826 (`schur_inverse_blocks`) has exactly the same declaration text after whitespace normalization. A fresh scratch probe copied both telescopes under `audit_` names and supplied the bodies `by exact freq_inj d` and `by exact schur_inverse_blocks hA hS`. Each also passed `example : type_of% @audit_<name> := @<name>`. Thus the original implicit binders, explicit binder order, parameter range, carriers, constants and conclusions elaborate against the implementation. No draft signature containing `sorry` was imported.

`freq_injOn` consumes the actual selected `pgAnalytic_spec d`. Fast lower Lipschitz and the proved block formula give
`c0 X ≤ mu LN (X + Y)`; equality of the slow components and the beta inverse bound give `Y ≤ LB LN X`. The specification supplies `mu LN ≤ c0/2` and `2 mu LN² LB < c0`, forcing both differences to vanish. This does not assume convexity of the tube or a local-injectivity-to-global-injectivity shortcut.

For the derivative, the code proves the full complex-frequency splitting and differentiates it on an open neighbourhood. It derives the slow affine gradient and beta Hessian block using the produced complex symmetry theorem, rather than treating arbitrary total frozen beta values outside V as an analytic extension. Hessian operator bounds imply row bounds in the Pi max norm without a missing dimension factor.

The inverse proof establishes the vector inequalities directly. From
`c0 X ≤ Wf + mu AN X + mu AN Y` and `mu Y ≤ LB (Ws + mu AN X)`, the two smallness inequalities leave `c0 X/4 ≤ (1 + AN LB) max Wf Ws`. The subsequent bounds are dominated by the exact second and third terms of pgCU. Finite-dimensional injective implies surjective produces the continuous linear equivalence. The final operator bounds, fast inverse-row bound O(1), and slow forward-row bound O(mu) follow from these estimates. The slow inverse-row bound O(1/mu) is also implied by the full inverse bound and projection contraction. All constants are selected from d before mu; `muStar ≤ mu0` keeps every use in the source parameter interval.

## Declaration table

All names below have prefix `KAM.Planetary.`. Helper premises are either typing/differentiability data or distinct conditional inequalities proved at their call sites; none is an added premise of freq_inj. New helpers with more general carriers or fewer assumptions are legitimate stronger support statements.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| stepP:p5:fi-inv | `schur_inverse_blocks` (FrequencySchur:25) | PASS | Exact design type; nonsingular inverses converted to invertible instances and Mathlib block identity. |
| fi-blk helper | `lower_of_hasFDerivAt` (FrequencyInvLinear:26) | PASS | Stronger generic normed-space lemma; open-domain lower Lipschitz bound differentiated along real lines. |
| fi-inv helper | `inv_apriori` (FrequencyInvLinear:52) | PASS | Pure real block inequalities, proved here; hypotheses are supplied by jacobian_bounds, not assumed at the package boundary. |
| fi-blk coordinates | `bfCLM` (FrequencyInvDeriv:31) | PASS | Actual fast coordinate projection as a continuous linear map, on the whole carrier. |
| fi-blk coordinates | `bsCLM` (FrequencyInvDeriv:35) | PASS | Actual slow coordinate projection as a continuous linear map, on the whole carrier. |
| fi-blk coordinate/norm helper | `bfCLM_apply` (FrequencyInvDeriv:38) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `bsCLM_apply` (FrequencyInvDeriv:40) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockFast_embFast` (FrequencyInvDeriv:42) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockSlow_embFast` (FrequencyInvDeriv:45) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockFast_embSlow` (FrequencyInvDeriv:48) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockSlow_embSlow` (FrequencyInvDeriv:51) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `eq_embFast_add_embSlow` (FrequencyInvDeriv:54) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `single_castAdd` (FrequencyInvDeriv:59) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `single_natAdd` (FrequencyInvDeriv:67) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk | `hasFDerivAt_complexIntegrable` (FrequencyInvDeriv:75) | PASS | Chain rule on the delta/2 fast tube, for the source parameter interval. |
| fi-inj / fi-blk | `complexFrequency_eq` (FrequencyInvDeriv:89) | PASS | Exact splitting into embedded fast frequency plus mu times polynomial gradient. |
| fi-blk | `hasFDerivAt_complexFrequency` (FrequencyInvDeriv:106) | PASS | Differentiates a neighbourhood equality, not merely a pointwise equality. |
| fi-blk helper | `hasFDerivAt_append_slow` (FrequencyInvDeriv:129) | PASS | Global affine embedding derivative; no domain premise needed. |
| fi-blk | `fderiv_jp_embSlow` (FrequencyInvDeriv:137) | PASS | Slow gradient is Omega + beta xi; uses proved complex symmetry jetBeta_isSymm. |
| fi-blk | `hessian_embSlow` (FrequencyInvDeriv:188) | PASS | Slow-slow Hessian is exactly beta, proved by differentiating the affine slow gradient. |
| fi-blk coordinate/norm helper | `norm_blockFast_le_norm` (FrequencyInvJac:31) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_blockSlow_le_norm` (FrequencyInvJac:35) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_le_max_blocks` (FrequencyInvJac:39) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_partialsCLM_apply_le` (FrequencyInvJac:45) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockFast_partialsCLM` (FrequencyInvJac:50) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `blockSlow_partialsCLM` (FrequencyInvJac:55) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-inj | `blockFast_complexFrequency` (FrequencyInvJac:60) | PASS | Actual fast component complexFast + mu jpGrad. |
| fi-inj | `blockSlow_complexFrequency` (FrequencyInvJac:74) | PASS | Actual slow component mu jpTheta. |
| fi-blk | `jac_fast_eq` (FrequencyInvJac:89) | PASS | Fast derivative row from uniqueness of the proved derivative. |
| fi-blk | `jac_slow_eq` (FrequencyInvJac:101) | PASS | Slow derivative row with its mu factor retained. |
| fi-blk | `jac_slow_slow` (FrequencyInvJac:112) | PASS | Coordinate form of the proved slow-slow Hessian formula. |
| fi-blk coordinate/norm helper | `norm_row_le` (FrequencyInvBounds:30) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_embFast_single` (FrequencyInvBounds:41) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_embSlow_single` (FrequencyInvBounds:44) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-blk coordinate/norm helper | `norm_real_smul_le` (FrequencyInvBounds:47) | PASS | Exact coordinate identity or max-norm estimate; valid on the stated whole carrier, no extra source premise. |
| fi-inv constants | `pgCU_ge` (FrequencyInvBounds:51) | PASS | Exact three printed summands bounded by their nested maximum. |
| fi-inv | `jacobian_bounds` (FrequencyInvBounds:58) | PASS | All four vector bounds with exact pgCU; consumes pgAnalytic_spec and derives the block inequalities. |
| stepP:p5:fi-inj | `freq_injOn` (FrequencyInverse:31) | PASS | Complex injectivity on the full radius-1 slow domain; strict smallness excludes nonzero fast differences. |
| bpP:p5:freq-inj | `freq_inj` (FrequencyInverse:115) | PASS | Exact design type; injectivity and continuous linear equivalence with all bounds; no new premises. |

## Definitions, imports and names

Exactly two new definitions: `bfCLM` and `bsCLM` (FrequencyInvDeriv:31,35). Both are continuous linear maps built from coordinate projections with the specified Fin embeddings. They represent the intended projections everywhere, including zero-dimensional carriers; there are no junk branches, fallback values, new structures, abbreviations or norm instances. They are exposed by the section attribute. pgAnalytic, pgCU and PGAnalyticSpec are upstream P5-FD objects, not new assumptions or definitions in this package.

Recursive import inspection found 85 KAM modules and 20 manifest-bound frozen declarations, all SEALED definitions. No frozen theorem module, DRAFT_SORRY anchor or provider is imported. In particular the pending P-G anchor is not in this import closure. `freq_data d` proves existence before pgAnalytic chooses the witness; the inverse specification is not inserted as a field of PGData.

Checked every new declaration basename against the other KAM source files. The only additional hit was `freq_inj` in TwoScale/StepInj.lean:99; that file is inside namespace `KAM.Planetary.KamHyp` (line 48), so its full name is different. No full-name collision found. FrequencyInvDeriv uses the renamed `blockFast_append_complex` / `blockSlow_append_complex` upstream API.

## Notes, deviations and source defects

1. **Declared proof-route deviation, nonblocking.** Design lines 285–287 and package row 498 prescribe “Neumann inversion of the fast block and its Schur complement”; blueprint p5:128–129 says “Schur complement” and “Block inversion”. The delivered inverse proof instead uses `inv_apriori` and finite-dimensional bijectivity. The standalone Schur formula genuinely uses `Matrix.fromBlocks₁₁Invertible` and `Matrix.invOf_fromBlocks₁₁_eq`, but is not consumed by freq_inj. Exact final statements and constants are preserved. Do not describe the Neumann/Schur intermediate estimates or the transpose block identity as independently exported Lean results; record the bypassed proof steps when synchronizing graph evidence. This is a proof deviation, not a false blueprint statement.
2. **Previously recorded blueprint parameter omission.** Blueprint p5:116 says “mu in (0,muStar]” with muStar bounded by 1 and the smallness conditions, without explicitly restricting muStar by mu0; supporting coefficient estimates are only on [0,mu0]. Design lines 635–639 already identify this. The implementation consumes the repaired proved output `muStar ≤ d.mu0`; it does not silently add a provider premise. This existing blueprint imprecision remains a source-document correction, not a fresh mathematical gap in P5-FI.
3. **Inherited comparison hygiene.** The mandated `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is not empty: it contains 22 added root imports in KAM.lean. Frozen files, manifest and README have no differences. Root differences are inherited before the first P5-FI proof commit (history includes root regenerations 722ad4a, 20c6eb0, c8ccbea, 686d56c); `git diff d04aeac..HEAD -- KAM.lean` is empty. Thus the generic whole-branch empty-diff check is explicitly not satisfied, while the six-file package obeys the restricted scope. No generated file was changed by this audit.
4. Revision 4's existing extension-agreement correction is upstream: no new exterior agreement claim is introduced here. No new suspected pinned-paper erratum, frozen-statement defect or undeclared mathematical deviation was found. No paper claim beyond the local blueprint was independently re-audited.

## Independent validation

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion or synthesis overrides, clean/update/cache retrieval, generated-root edits or state-changing git commands were used.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5fi KAM.Planetary.PGAssembly.FrequencyInverse
[inp-gate] slot 1 acquired 14:20:43 for KAM.Planetary.PGAssembly.FrequencyInverse
Build completed successfully (9131 jobs).
exit 0
```

This target includes all six modules. Replayed upstream warnings concern CompactLipschitz unused hW, JetsPoly unused simp arguments, and Jets unused mu/I. No scoped-module failure or heartbeat failure occurred.

Fresh exact-signature and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5FIAudit.lean
exit 0
```

Complete #print axioms output, covering every new public theorem:

```text
'KAM.Planetary.schur_inverse_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lower_of_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inv_apriori' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bfCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bsCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_embFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockSlow_embFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_embSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockSlow_embSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eq_embFast_add_embSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.single_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.single_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_complexIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexFrequency_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_complexFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_append_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_jp_embSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hessian_embSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_blockFast_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_blockSlow_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_max_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_partialsCLM_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_partialsCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockSlow_partialsCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_complexFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockSlow_complexFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jac_fast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jac_slow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jac_slow_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_row_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_embFast_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_embSlow_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_real_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgCU_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jacobian_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.freq_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.freq_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (single invocation, all six modules):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.FrequencyInverse KAM.Planetary.PGAssembly.FrequencySchur KAM.Planetary.PGAssembly.FrequencyInvLinear KAM.Planetary.PGAssembly.FrequencyInvDeriv KAM.Planetary.PGAssembly.FrequencyInvJac KAM.Planetary.PGAssembly.FrequencyInvBounds
replaying KAM.Planetary.PGAssembly.FrequencyInvBounds
replaying KAM.Planetary.PGAssembly.FrequencyInvJac
replaying KAM.Planetary.PGAssembly.FrequencyInvDeriv
replaying KAM.Planetary.PGAssembly.FrequencyInvLinear
replaying KAM.Planetary.PGAssembly.FrequencySchur
replaying KAM.Planetary.PGAssembly.FrequencyInverse
exit 0
```

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (665 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the explicitly permitted stale generated-root warning. Module conventions, frozen-anchor guard and all 144 elaborated ABI hashes pass. Forbidden-token/resource-override/EuclideanSpace checks and file/line limits emit no failures. The six scoped modules have copyright headers, module declarations, public imports, module docstrings and public sections; maximum length is 222 lines. The stale root was not regenerated.

Final integrity: `git diff --check` exits 0. The tracked working tree has no edits; the only new audit artifact is this report, alongside the pre-existing untracked handoff. All audit-created scratch probe, diff and log files were removed after copying the complete validation receipts into this report. No proof source, frozen file, manifest, generated root, README or handoff was edited. Remaining uncertainties are confined to the stated upstream/source and frozen-theorem scope limits; no required P5-FI check is outstanding.
