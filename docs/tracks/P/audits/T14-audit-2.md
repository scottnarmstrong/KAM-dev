# T14 independent package audit 2 — delta audit

**Overall verdict: PASS WITH NOTES. Round-1 F1 is closed.** The concrete inverse
rotation lift is now proved equal to Part 9's lift on its physical analytic domain,
and its chart, injectivity, fast-action preservation and translation covariance are
exported. The signed declarations and their existing proofs are unchanged. T14
implements no frozen theorem anchor; provider/type and seal-body probes are N/A.
This is package acceptance, not a seal of P-PLANAR or the full Birkhoff theorem.

## Scope and evidence

Date: 2026-10-28. Worktree and report destination:
`/root/code/KAM-inp-p11c-t14`. The user's exact worktree destination overrides the
external brief's generic main-worktree destination. Production scope is only
`KAM/Planetary/PlanarTorsion/Frame*.lean`; Frame.lean is the sole matching file.
HEAD: `e6abda49d1b2c76c9647ce1479b68cf03d6a37a3`.
Observed inp at initial comparison: `4a5b757e944936d0ae6e9269a1170dc7098e4240`.
Delta baseline: `ebd16fe7`, containing the round-1 report.

Read AGENTS.md, PLAN.md, DECISIONS.md, the external package-audit brief, T14 handoff
and AUDIT FOCUS, audit 1, `.drafts/handoff-T14b.md`, P11C design and design audit 1,
the authoritative external signatures, track P statement, Part-11b rotation and
consumer text, inherited spectral adapter, and the actual Part-9 lift, derivative,
transport and Hamiltonian chart interfaces and frozen phase/coordinate definitions.

`git diff inp...HEAD` selects merge base
`48e9326d764f4bb7e1704209fddf71863ec4eb9e` with the diagnostic
`warning: inp...HEAD: multiple merge bases, using ...`. It contains seven added
files, 1575 insertions: Frame.lean, inherited SpectralAdapter.lean, three T12
reports, and the T14 first audit/handoff. These inherited files are distinguished
from the round-2 production delta. `git diff ebd16fe7..HEAD` changes only Frame.lean:
104 insertions, one deletion. The only pre-existing text replaced is the module
docstring sentence; imports are added and the seven declarations below are appended,
with their section heading and local `open scoped Matrix.Norms.Elementwise`.
Thus the precise delta also includes that necessary scope opening, beyond the
user's abbreviated list of imports/docstring/declarations. No existing declaration
or proof was changed. This scope opening follows the signed declarations.

A byte comparison of the entire original declaration region, from
`def p11c_rotateSlow` through the end of `p11c_rotationLift`, against `ebd16fe7`
passes, including helper proofs. Whitespace-normalized signed definitions and the
`global_planar_frame` header also match the authority file exactly. Fresh Lean
probes copy the three signed definitions under new names and prove equality by
`rfl`; the copied signed theorem statement is proved by
`exact global_planar_frame p hp`.

| Input | SHA-256 |
|---|---|
| Frame.lean | `7ba6dfab02bc2b312ecd7c8db80bb80983c99fab3e6d11b6b078f02708adcc93` |
| /root/code/KAM-inp/.drafts/design/P11CSignatures.lean | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |

## F1 closeout and consumer applicability

Design U9 at line 54 requires: “Identify `p11c_Q`, `p11c_sigma`, projector and
inverse rotation lift with upstream spectral objects; prove equalities, never
assume them.” T14 and the composition ownership are at lines 215 and 245.
Frame.lean:230 now proves precisely the previously missing equality with
`SecularSpectrum.liftInv (fun I => p11c_frame p (p.axes I))`, for valid p and
`fast w.2 ∈ p11c_frameActionDomain p`. Unfolding the domain gives exactly
`p.axes (fast w.2) ∈ p11c_axes`. There is no assumed equality or assumed derivative.

The axis map is the actual quadratic-over-constant formula, analytic for valid
masses and kappa. Composition with the existing frame regularity proves analyticity
of the matrix-valued family, hence differentiability. `fderiv_entry` then identifies
matrix derivative entries with the scalar derivatives in the signed lift formula.
The remaining finite sums are expanded and closed by `ring`. Signs, transpose
order, and the assembled slow-block order agree with Part 9's inverse lift.

Frame.lean:247 exports the four required rotation properties on
`D = SecularSpectrum.liftDomain (p11c_frameActionDomain p)`:

- `IsChart 1 (p11c_rotationLift p) D`, using the existing definition of chart:
  real analyticity on a neighbourhood and the frozen symplectic form with factor 1.
- `InjOn (p11c_rotationLift p) D`.
- Preservation of the fast momentum/action block, in the literal
  `Fin.castAdd 2` form required by the consumer.
- Covariance under every real fast translation `(Fin.append c 0, 0)`.

The equality holds throughout the open D, so the proof obtains neighbourhood
equality before transferring `fderiv`. Pointwise equality alone is not used to
transfer derivatives. Injectivity follows from Part 9's inverse identities and
SO frame. Translation stays inside D because fast actions do not change.

The signed `PlanarBirkhoffResult` at signature lines 594–630 retains the same
`T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval`. The rotation interface above
supplies exactly its rotation-side chart/injectivity/action/translation obligations,
on a domain unrestricted in angles or slow variables. For valid p and
`a ∈ p11c_axes`, the actual dictionary gives `p.axes (p.actions a) = a` (also
independently proved in the scratch probe). Since `O' ⊆ closure O' ⊆ p.actions '' Oa`
and `Oa ⊆ p11c_axes`, the consumer's actions lie in the frame action domain.
The tube condition explicitly includes its fast actions in O'.

The inner lift preserves fast actions directly from its signed `assemble` formula;
therefore its image of the tube lies in D. Together with T11's chart, injectivity
and covariance, `IsChart.comp`, function injectivity on the mapped domain, and
substitution give the four properties of T in the signature. There is no missing
rotation-side radius or range condition. The chart's factor composes as 1 * 1.
The scratch probe also checks literal restriction of all four rotation conclusions
to any subset of D.

T11's signed `lift_map` does not itself state action preservation as a conjunct;
that fact comes from `p11c_liftFlow`'s explicit definition. This clarifies the
handoff's informal phrase “which T11's lift_map supplies”; it is not a failure of
the new rotation export. This audit does not assert that T11/T16 or their physical
range, normal-form, integrability and remainder obligations are already proved.

## Declaration inventory

All declarations are in `KAM.Planetary`. Old proof rows are retained through the
byte-identical delta check and freshly checked axioms/kernel replay.

| Node / role | Declaration (Frame.lean line) | Verdict | Reason |
|---|---|---|---|
| Shared slow rotation | `p11c_rotateSlow` (34) | PASS WITH NOTE | Exact signed definition; existing T13 ownership note retained. |
| Global frame | `p11c_frame` (38) | PASS | Exact signed normalized eigenvector. |
| U9 positivity | `p11c_Q_off_pos` (47) | PASS | Unchanged source-guarded proof. |
| Nonvanishing | `p11c_frame_norm_pos` (58) | PASS | Unchanged positive denominator. |
| Eigenvector | `p11c_frame_eigen` (65) | PASS | Unchanged spectral algebra. |
| Axis topology | `p11c_axes_isOpen` (79) | PASS | Unchanged open cone. |
| Matrix analyticity | `p11c_Q_analyticAt` (84) | PASS | Unchanged physical identification. |
| Eigenvalue analyticity | `p11c_sigma0_analyticAt` (92) | PASS | Unchanged positive discriminant. |
| Frame analyticity | `p11c_frame_analyticAt` (106) | PASS | Unchanged positive normalization. |
| bt-rot / frame replacement | `global_planar_frame` (130) | PASS | Exact signed type/proof unchanged. |
| Concrete inverse lift | `p11c_rotationLift` (176) | PASS | Exact signed formula; attachment now proved below. |
| Frame action domain | `p11c_frameActionDomain` (191) | PASS | Actual preimage of the axis cone. |
| Domain topology | `p11c_frameActionDomain_isOpen` (194) | PASS | Continuous actual axis map, for all p. |
| Axis regularity | `p11c_axes_map_analyticAt` (201) | PASS | Derived from valid physical constants, all I. |
| Family regularity | `p11c_frameFamily_analyticOnNhd` (212) | PASS | Matrix-valued composition, source domain only. |
| Family SO | `p11c_frameFamily_isSO` (220) | PASS | Projection of proved global frame theorem. |
| U9 inverse-lift identification | `p11c_rotationLift_eq_liftInv` (230) | PASS | Derived entry derivatives and finite algebra; F1 equality paid. |
| Part-9 chart interface | `p11c_rotationLift_chart` (247) | PASS | All four consumer properties, no chart/injectivity premise. |

The T14 share of bt-rot/bt-rot#lift is now delivered under the design's authorized
global matrix-frame replacement. The jointly assigned bt-K/bt-nf/bt-avg/bt-frozen
conclusions remain T15/T16 consumer work. No unsigned declaration named after a
graph node falsely advertises an analytic angle theorem.

## Definitions and hypotheses

The only new definition in round 2 is `p11c_frameActionDomain`: a genuine preimage
set on its whole carrier, with no fallback or hidden proof field. No new structure,
abbreviation, instance, constant-selection scheme or substitute physical object is
introduced. Existing definitions retain round-1 classification: `p11c_rotateSlow`
is genuine linear matrix application; the frame and lift are total formulas whose
SO/analytic/chart claims are confined to the valid axis locus. Their invalid-data
extensions are not used as physical frames or charts.

New premises are physical validity (standing positive G, m0, masses), typing data,
and membership in the source axis domain. Openness, analyticity, SO membership,
derivative identification, injectivity and symplecticity are proved, not supplied
as conclusion-shaped hypotheses. No constants or wider parameter dependence arise.
The domain includes some negative-action components because axes uses squares;
this is harmless stronger coverage, while the physical consumer uses the positive
action image. No unproved inverse identity for arbitrary negative actions is used.

## Independent validation

All auditor Lean/Lake invocations were serialized and used `LEAN_NUM_THREADS=1`.
The build gate runs `nice -n 5 lake build`; the probe, checker and lint were also
run with `nice -n 5`. No override, clean, update, root regeneration or extra agent
was used. These are independent reruns, not the prover's receipts.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t14 KAM.Planetary.PlanarTorsion.Frame
   [inp-gate] slot 3 acquired 21:49:12 for KAM.Planetary.PlanarTorsion.Frame
   Build completed successfully (9201 jobs).
   exit 0
   ```

   Cached dependencies replayed unused-variable/deprecation/style warnings;
   no warning or error was attributed to Frame.lean.

2. Signature, consumer adapter and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T14Audit2.lean
   ROOT_SHADOW_CHECK PASS
   exit 0
   ```

   The successful final run had no errors or warnings. The initial scratch-only
   draft needed `noncomputable section` for copied definitions and explicit
   transitivity for positivity of a1; these probe setup errors were corrected,
   without changing any production code or resource setting.

   Exact axiom output (all declarations, including all new public theorems):

   ```text
   'KAM.Planetary.p11c_rotateSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_Q_off_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_axes_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_Q_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_sigma0_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.global_planar_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_rotationLift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frameActionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frameActionDomain_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_axes_map_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frameFamily_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frameFamily_isSO' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_rotationLift_eq_liftInv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_rotationLift_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Frame
   replaying KAM.Planetary.PlanarTorsion.Frame
   exit 0
   ```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (940 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole lint failure is the generated-root staleness expressly excepted by
   the audit brief. Module hygiene, frozen-anchor guard and all 144 ABI hashes
   pass; no substantive lint failure remains. The generated root was untouched.

5. Static/import/protected-path checks:

   - Frame.lean has 286 lines; maximum width 100 Unicode characters. All module
     headers/public imports, docstring, and exposed public noncomputable section
     are present. Comment/string-masked scan finds no forbidden token,
     `EuclideanSpace`, or `set_option`.
   - Declaration-site scan across KAM finds exactly one owner for each of the
     18 public short names. The Lean environment probe finds no corresponding
     root declaration (no harmful root shadow).
   - Recursive import closure reaches 155 local modules and 57 manifest anchors,
     all definition-kind and SEALED. No provider or DRAFT_SORRY theorem is reached.
     The three new imports use actual upstream implementations.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty,
     apart from the multiple-merge-base diagnostic recorded above.
   - `git diff --check` and the report-specific
     `git diff --no-index --check /dev/null docs/tracks/P/audits/T14-audit-2.md`
     pass. Final git status contains only the new report. Audit scratch files
     are deleted after their output is incorporated here.


## Notes, uncertainties, errata and deviations

No new pinned-source, blueprint, or frozen-statement defect was found. The existing
Part-11b line-217 analytic-angle SOURCE_GAP is preserved: its text says the unit
vector “lifts analytically to the angle” by covering, whereas this package proves
the design's explicit global SO(2) matrix replacement. No analytic angle or graph
SOURCE_GAP closure is inferred. The rotation attachment itself is no longer unpaid.

The pre-existing ownership deviation remains: `p11c_rotateSlow` is signed in T13's
block but owned here; T13 must import its definition instead of redeclaring it.
The small handoff discrepancy is numerical: the current file has 286 lines, not
284. Width is at most 100. The permitted stale generated root is recorded above;
it was not regenerated. No production edit or state-changing git action was made
by this auditor. Only this report and temporary scratch probes/logs were written;
all audit-created scratch files were removed after validation.
