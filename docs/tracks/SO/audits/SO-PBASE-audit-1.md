# SO-PBASE independent audit 1

Verdict: **PASS WITH NOTES** for the complete Poly/Basic and Model/Basic slice. All 25 signed declarations match the signed API (fully qualified namespace, binder order, carriers, premises and conclusions); all 44 new public declarations were reviewed. No proof or statement defect found. No frozen theorem anchor or provider is supplied by this infrastructure package, so provider/frozen-type and proposed seal-body probes are not applicable. This verdict does not close `g1_explicit`, the numerical certificate checker, or lunar confinement.

Audited worktree: `/root/code/KAM-inp-sopbase`; HEAD `cc2ed0470cd7151ea238a6f916f8017665cafcbc`; comparison ref `inp` at `1c8cbfd1dad1fca3fb7260162646d619ac2a5a50`. Date: 2026-10-29. The explicit user destination overrides the generic brief's main-worktree destination. Only this report was added; temporary probes/logs were placed in this worktree's `.lake/abi-scratch/` and removed afterwards. The initially untracked handoff was left untouched.

The notes are the permitted stale generated root, one pre-existing PiHigh warning, and a minor design-prose inconsistency described below. There is no unpaid mathematical obligation within this slice.

## Authority, scope and fidelity

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-PBASE-handoff.md`. The handoff's AUDIT FOCUS limits this audit to the following complete diff:

```text
 KAM/Certificate/Model/Basic.lean | 217 +++++++++++++++++++++++++++++++++
 KAM/Certificate/Poly/Basic.lean  | 255 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 472 insertions(+)
```

The external design advanced to Revision 4 during this audit; a final comparison confirmed all 21 non-structure signed types and all four structure field lists unchanged from the successfully checked slice. Locators below use the final snapshot. The controlling signatures are `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §B:317–387 (through `CertPoly.eval_add`) and §C:402–438 (through `CertModel.norm_le_supBound`). The design context is `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, especially §2:202–220, the module map:396–401, and SO-PBASE row:447; the project plan is `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`. Generic I/N/P blueprint and theorem-anchor checks are superseded here by the expressly named SO slice; no I/N/P source theorem is claimed.

A scratch probe copied the 21 non-structure signed declaration types literally into quantified `example` types, then supplied the fully qualified `@KAM.Certificate.<name>` term. The four structures were compared field by field: `CertPoly`, `CertRealPoly`, `CertWeight`, `CertModel`, with no extra field or premise. Eight signed definitions/aliases with explicit signature bodies were additionally checked by `rfl` against separately copied definitions. The two signature implementation holes (`toPoly`, `supBound`) retain their exact types and were reviewed semantically. Production `variable` sections account for textual relocation of implicit binders without changing the API. Every signed name resolves under `KAM.Certificate`; no root shadow was introduced.

The complete slice contains 25 signed declarations and 19 implementation helpers. `shift`, `conjReflect` and their lemmas belong to Poly/Ops; `ModelConfig`, arithmetic/model-operation enclosure lemmas and averaging belong to Model/Ops; witnesses belong to later packages. Their absence is not an omission from this slice.

## Declaration audit

Locators below are in the two audited files; all names are fully qualified. PASS means faithful signed API or sound implementation helper, as indicated.

| Node / locator | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| §B, Poly/Basic:27 | `KAM.Certificate.CertKey` | PASS | Signed alias `List ℤ`; arbitrary lengths are intentional. |
| §B, Poly/Basic:30 | `KAM.Certificate.certKeyFun` | PASS | Signed zero-padding/truncation of the index to `Fin n`; total on every list. |
| §B, Poly/Basic:34 | `KAM.Certificate.CertPoly` | PASS | Signed data structure: exactly `terms : List (CertKey × CC α)`. |
| §B, Poly/Basic:38 | `KAM.Certificate.CertPoly.eval` | PASS | Signed direct finite sum; every stored term participates. |
| §B, Poly/Basic:42 | `KAM.Certificate.CertPoly.coeff` | PASS | Signed filter-and-sum; repeated denoted indices aggregate. |
| §B, Poly/Basic:50 | `KAM.Certificate.CertPoly.coeff_eq_sum` | PASS | Helper: exact coefficient indicator sum, no extra hypothesis. |
| §B, Poly/Basic:60 | `KAM.Certificate.hasSum_list_coeff_mul_character` | PASS | Helper: finite-support HasSum, including duplicate indices. |
| §B, Poly/Basic:79 | `KAM.Certificate.CertPoly.eval_eq_fourierSum` | PASS | Signed exact Fourier-series bridge at every complex point. |
| §B, Poly/Basic:83 | `KAM.Certificate.character_add_int` | PASS | Helper: period-one character identity via integer exponential. |
| §B, Poly/Basic:95 | `KAM.Certificate.differentiable_list_sum` | PASS | Helper: finite sum of differentiable functions; typing premises only. |
| §B, Poly/Basic:103 | `KAM.Certificate.CertPoly.differentiable_eval` | PASS | Signed entire complex differentiability, law-free. |
| §B, Poly/Basic:108 | `KAM.Certificate.CertPoly.eval_add_int` | PASS | Signed unconditional period-one identity, law-free. |
| §B, Poly/Basic:115 | `KAM.Certificate.CertRealPoly` | PASS | Signed data structure: exactly `zero : α` and `half : List (CertKey × CC α)`. |
| §B, Poly/Basic:120 | `KAM.Certificate.CertRealPoly.eval` | PASS | Signed mathematical conjugation and real constant; law-free. |
| §B, Poly/Basic:129 | `KAM.Certificate.character_neg_ofReal` | PASS | Helper: conjugation identity on the real slice. |
| §B, Poly/Basic:138 | `KAM.Certificate.im_list_sum_eq_zero` | PASS | Helper: zero imaginary parts preserved by finite summation. |
| §B, Poly/Basic:147 | `KAM.Certificate.CertRealPoly.eval_real` | PASS | Signed law-free reality, including arbitrary backend denotations. |
| §B, Poly/Basic:156 | `KAM.Certificate.CertRealPoly.differentiable_eval` | PASS | Signed law-free entire differentiability. |
| §B, Poly/Basic:166 | `KAM.Certificate.CertRealPoly.eval_add_int` | PASS | Signed law-free periodicity. |
| §B, Poly/Basic:177 | `KAM.Certificate.certPair` | PASS | Helper definition: original term and reflected/conjugated backend term. |
| §B, Poly/Basic:182 | `KAM.Certificate.CertRealPoly.toPoly` | PASS | Signed type; allowed implementation hole filled by zero term and all pairs. |
| §B, Poly/Basic:185 | `KAM.Certificate.certKeyFun_map_neg` | PASS | Helper: zero-padding commutes with negation for every list. |
| §B, Poly/Basic:191 | `KAM.Certificate.certKeyFun_nil` | PASS | Helper: empty key denotes the zero index. |
| §B, Poly/Basic:194 | `KAM.Certificate.list_sum_flatMap_pair` | PASS | Helper: generic finite flattening identity; no pairing restriction needed. |
| §B, Poly/Basic:201 | `KAM.Certificate.CertRealPoly.eval_toPoly` | PASS | Signed exact equality under exactly the arithmetic laws in the signature. |
| §B, Poly/Basic:215 | `KAM.Certificate.pair_coeff_symm` | PASS | Helper: coefficient-pair identity for any decidable additive commutative group. |
| §B, Poly/Basic:221 | `KAM.Certificate.CertRealPoly.conjugateSymmetric` | PASS | Signed coefficient symmetry under the specified laws. |
| §B, Poly/Basic:247 | `KAM.Certificate.CertPoly.add` | PASS | Signed exact concatenation, independent of arithmetic instances. |
| §B, Poly/Basic:249 | `KAM.Certificate.CertPoly.eval_add` | PASS | Signed exact law-free addition identity. |
| §C, Model/Basic:28 | `KAM.Certificate.CertWeight` | PASS | Signed data structure: exactly rational `rho` and `w`. |
| §C, Model/Basic:34 | `KAM.Certificate.checkWeight` | PASS | Signed positive-width test and rational exponential upper-bound test. |
| §C, Model/Basic:37 | `KAM.Certificate.CertWeight.rho_pos` | PASS | Helper: accepted weight has positive geometric strip width. |
| §C, Model/Basic:42 | `KAM.Certificate.CertWeight.exp_le_w` | PASS | Helper: rational pi upper bound and exponential upper bound give the true weight. |
| §C, Model/Basic:59 | `KAM.Certificate.CertWeight.one_le_w` | PASS | Helper: positivity of width gives `1 ≤ w`. |
| §C, Model/Basic:67 | `KAM.Certificate.norm_character_le_weight` | PASS | Signed character estimate, exact premises and exponent. |
| §C, Model/Basic:78 | `KAM.Certificate.CertModel` | PASS | Signed data structure: exactly integer `deg`, polynomial `poly`, radius `rad`. |
| §C, Model/Basic:84 | `KAM.Certificate.CertModel.Encloses` | PASS | Signed sup-error relation on the open strip with exact integer degree factor. |
| §C, Model/Basic:94 | `KAM.Certificate.CertPoly.weightedNormUp` | PASS | Helper definition: upward fold over all terms using stored-key absolute sum. |
| §C, Model/Basic:99 | `KAM.Certificate.degFactorUp` | PASS | Helper definition: rational pi upper bound for nonnegative degree, lower bound for negative degree. |
| §C, Model/Basic:103 | `KAM.Certificate.CertModel.supBound` | PASS | Signed type; sound implementation for every accepted weight and every integer degree. |
| §C, Model/Basic:106 | `KAM.Certificate.sum_natAbs_certKeyFun_le` | PASS | Helper: truncating/padding a key cannot increase its absolute-index sum. |
| §C, Model/Basic:120 | `KAM.Certificate.two_pi_zpow_le` | PASS | Helper: upper bound for every integer power; inversion reverses the bound for negative degrees. |
| §C, Model/Basic:133 | `KAM.Certificate.weightedNormUp_bound` | PASS | Helper: nonnegative upward sum and polynomial bound under lawful arithmetic. |
| §C, Model/Basic:172 | `KAM.Certificate.CertModel.norm_le_supBound` | PASS | Signed full bound with no radius-sign or degree-sign premise added. |

## Definition classification and refutation attempts

Every new definition/alias/structure is classified below. None hides a proof premise or relies on junk data outside an intended subcarrier.

| Object | Classification and whole-carrier behavior |
|---|---|
| `CertKey` | Exact alias for all integer lists; not a length-restricted subtype. |
| `certKeyFun` | Exact index denotation: read the first `n` entries, use mathematical integer zero for missing entries. Longer keys intentionally denote the same index as their prefix. |
| `CertPoly` | Plain finite data, including duplicate keys and arbitrary key lengths. |
| `CertPoly.eval` | Exact finite sum using every term and its denoted index; no term is pruned. |
| `CertPoly.coeff` | Exact sum over equal denoted indices, including collisions from padding/truncation; zero only when the filtered list sums to zero. |
| `CertRealPoly` | Plain constant plus unrestricted list of paired data; “half lattice” is a storage description, not an assumed uniqueness/sign predicate. |
| `CertRealPoly.eval` | Exact direct denotation using mathematical conjugation, not backend conjugation, and real cast of `val zero`. Reality works even for an unlawful backend. |
| `certPair` | Computed backend pair `(k,c),(-k,c.conj)`; no semantic claim without the appropriate laws. |
| `CertRealPoly.toPoly` | Computed full list with constant at `[]` and every conjugate pair. Exact interpretation and coefficient symmetry properly require lawful arithmetic. |
| `CertPoly.add` | Exact list concatenation, no coefficient rounding. |
| `CertWeight` | Rational input data, not a bundled certificate. |
| `checkWeight` | Computable rational validation; positive width prevents vacuity in the radius argument. Soundness is proved rather than bundled. |
| `CertModel` | Plain integer degree, polynomial, backend radius; no conclusion-shaped field. |
| `CertModel.Encloses` | Exact signed uniform error relation, defined at all radii; it can be vacuous for empty strips, but the bounding theorem separately requires a passing positive-width check. |
| `CertPoly.weightedNormUp` | Total upward accumulation, counting the absolute sum of every stored key; a conservative rather than understated bound. Only passing weights/lawful backends receive the soundness guarantee. |
| `degFactorUp` | Total rational integer-power expression. Uses `piLoQ > 0` when degree is negative, reversing the bound correctly under inversion. |
| `CertModel.supBound` | Total backend expression multiplying the upward degree bound by the upward sum of polynomial bound and radius. No claim for invalid weights/unlawful backends. |

Specific attempted failure modes:

- **Duplicate, padded, empty and overlong keys; `n = 0`.** Both evaluation and coefficients use the same `certKeyFun n`; finite-list `HasSum` induction proves exact equality with the Fourier sum on all complex points. Only the index is truncated, as signed; no stored Fourier term is discarded. For the weighted bound, Model/Basic:106–118 proves the denoted absolute-index sum is at most the stored sum. Since accepted weights satisfy `w ≥ 1`, overlong keys only overestimate the norm. Empty-dimensional strips still contain zero.
- **Unlawful arithmetic and reality (F2).** Poly/Basic:120–124 uses `(starRingEnd ℂ)` directly and a real constant. Backend `ofInt 0` and `CC.conj` enter only `toPoly`; both corresponding correctness theorems carry `[LawfulCertArith α]`. Exact concatenation needs no arithmetic law. No backend-zero fallback enters the direct denotation.
- **Negative degree.** Model/Basic:120–131 splits on the integer sign and bounds inverse powers using `piLoQ`, not `piUpQ`. Zero degree yields factor one. The universal theorem is not restricted to natural degrees.
- **Negative stored radius.** Model/Basic:178–183 derives `0 ≤ val m.rad` by applying enclosure at zero in the positive-width strip and dividing by the positive `(2π)^deg`; this remains valid for negative degrees. There is no added radius hypothesis. The final multiplication uses only established nonnegative quantities, as required by `upMul_ge`.
- **Hidden conclusion assumptions.** The helper assumptions are finite-sum differentiability/reality inputs, arithmetic soundness laws, accepted weights, strip membership, or enclosure itself. No Fourier bridge, bound or radius sign is silently assumed in place of its proof.

## Independent checks

All audit Lean/Lake invocations were serialized, used `LEAN_NUM_THREADS=1`, and ran at nice level 5. No resource-budget override, clean, update, cache replacement, source edit or state-changing Git operation was used. The lint's ABI Lean subprocess inherited this environment and nice level. Other agents' processes were not managed by this audit.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sopbase KAM.Certificate.Poly.Basic KAM.Certificate.Model.Basic
```

The gate runs `nice -n 5 lake build` with those targets. Exit **0**; output:

```text
[inp-gate] slot 1 acquired 12:28:04 for KAM.Certificate.Poly.Basic KAM.Certificate.Model.Basic
⚠ [2898/2902] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
Build completed successfully (2902 jobs).
```

The warning is in an unchanged upstream module. Neither audited file emitted a warning.

### Signed-type, explicit-body and axiom probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOPBaseAudit.lean
```

Final exit **0**: all 21 signed type checks and eight copied-definition `rfl` checks succeeded. Scratch-only unused-binder warnings appeared. An initial scratch run exited 1 because copied real/complex definitions lacked a `noncomputable section`; adding the same section used by the production modules fixed the probe. No package change was made and no signature mismatch occurred.

Exact `#print axioms` output for all 27 new theorems:

```text
'KAM.Certificate.CertPoly.coeff_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hasSum_list_coeff_mul_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_eq_fourierSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.differentiable_list_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.differentiable_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_neg_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.im_list_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.differentiable_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certKeyFun_map_neg' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.certKeyFun_nil' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.list_sum_flatMap_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_toPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pair_coeff_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.conjugateSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertWeight.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertWeight.exp_le_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertWeight.one_le_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_character_le_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_natAbs_certKeyFun_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.two_pi_zpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.weightedNormUp_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.norm_le_supBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Poly.Basic KAM.Certificate.Model.Basic
```

Exit **0**, output:

```text
replaying KAM.Certificate.Model.Basic
replaying KAM.Certificate.Poly.Basic
```

### Lint and integrity

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1296 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module-system check, frozen-anchor guard and all 144 ABI hashes passed. The auditor did not regenerate `KAM.lean`. The handoff's reported lint exit 0 does not match this independent run; the substantive results agree.

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sopbase KAM.Certificate.Poly.Basic KAM.Certificate.Model.Basic
```

Exit **0**:

```text
short-name check OK (no reused public short name)
```

This checker also inspects competing unmerged branches for new public helper short-name collisions. Its documented exclusions for signed names and dotted API names are appropriate here. All helper names remain in `KAM.Certificate`, with no `_root_` escape or harmful root shadow.

Manual/source-script checks: Poly/Basic has 255 lines, Model/Basic has 217; each has maximum Unicode line width 99. Both have copyright, `module`, public imports, module docstring, exposed public section. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace` or `set_option` occurs in either audited source. An import-closure scan found 18 project modules, no provider and no DRAFT_SORRY module. Its only frozen import is `KAM.Frozen.Defs.ComplexStrip`, state **SEALED** in the current manifest; the frozen body was read and matches the open geometric strip used by the proofs.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, no output. Generated files and all frozen/manifest paths were untouched. Initial status contained only the untracked handoff; final status additionally contains this report.

Audited input SHA-256 values:

```text
82e39b8fc417677387e70e7e1ade9edc578afadd3dedb326adc66643ec031836  KAM/Certificate/Poly/Basic.lean
583f95640c2066caddd5742b139e281e396b0987cb4a34c0d4274cf7cc1bdbec  KAM/Certificate/Model/Basic.lean
95a45623f1cd75be9e406f32f2da407035b6663a7a8e98658541fbe4ff38a887  /root/code/KAM-inp/.drafts/design/SOSignatures.lean
```

## Source/design notes, uncertainties and deviations

No suspected mathematical source erratum or incorrect signed statement was found in the audited slice. The arbitrary stored-list exponent in `weightedNormUp` is an allowed implementation choice and is justified by `sum_natAbs_certKeyFun_le`; it changes tightness, not soundness.

One editorial inconsistency in the external design is worth recording: `SO-LEAN-DESIGN.md:83` lists “`eval_add`” among theorems requiring `[LawfulCertArith α]`. The same document at line 72 explicitly says “`CertPoly.add` is **exact list concatenation** (law-free, no error term) with `eval_add` an equality”; its §B and the controlling signatures at SOSignatures:385–387 give `eval_add` without the laws. The implementation correctly follows the specific signed statement. The broad F2 prose list should omit this exact-concatenation theorem; there is no proof obligation to add a premise.

The module dependency table at design:398 is schematic: this implementation additionally imports Arith.Roots for `CC.normUp`, while no Strip/Averages import is needed until the later averaging operation. These imports introduce neither a provider nor an unproved frozen theorem. No deviation to a signed signature was introduced.

The audit is scoped to the current two modules and their imported proof support. Model/Poly operations and the later certificate-consumer assembly were not asserted complete. Frozen sealing remains inapplicable to this package.
