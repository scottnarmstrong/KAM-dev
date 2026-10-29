# B16 independent package audit 1

**Overall: PASS WITH NOTES for B16 `limit_torus`.** All seven assigned graph nodes are established, all three signed declarations match exactly, and the proof uses the frozen real Hamiltonian vector field and symplectic form. This is an infrastructure-package verdict. B16 defines no provider and seals no frozen theorem; the provider/frozen-type and frozen seal-body tests are therefore not applicable. It does not prove the physical P-G/P-PLANAR/P-FIXED anchors.

Audit snapshot: 2026-10-29 UTC, worktree `/root/code/KAM-inp-p11b-b16`, HEAD `77aeaaedefb8c519763a10dda787e95a8499c402`, compared `inp` `4484aa01a46740b1c038f5995574426aa073a812`. The requested report path overrides the generic brief's main-worktree destination.

Canonical signature SHA256: `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`; design: `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1`; blueprint: `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b`.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the exact package audit brief, B16-handoff.md, P11B-LEAN-DESIGN.md (node table, B16 row, proof instructions and revision-2 gates), both P11B design audits, canonical `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`, p11a4-limit-family.tex, and the relevant Track P statement conventions/physical consumers. Inspected frozen Phase, real/complex Hamiltonian fields, RealHamiltonian, SymplecticForm, ComplexStrip, ActionNbhd, IsDiophantine, IsPhysicalTorus, IsCylinderTorus, and the P-G anchor. Re-audit is restricted to the six new `KAM/Planetary/WeakKAM/Tori*.lean` files; B15 and other imported packages are dependencies, not independently re-audited here.

`git diff inp...HEAD` reports multiple merge bases and selects `7042a93113c7bbf885cace84f7804d2795e6c929`. Its full inventory is 35 files, 4355 insertions, 192 deletions; all six scoped files are additions (1083 diff lines including headers). The comparison includes inherited preparation, budget, graph and audit changes. Protected-path comparison is **not empty**: generated `KAM.lean` has 15 inserted imports. Frozen files, manifest and README are unchanged. `git diff 3af86cbf^..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty across the six B16 commits. Thus the generated-root deviation is inherited, not a B16 modification. Do not describe the entire branch as satisfying the brief's empty protected-path check.

Initial working-tree status contained only the untracked B16-handoff.md. This audit changes only this report and temporary `.lake/abi-scratch/` artifacts. No git mutation or generated-root repair.

## Graph coverage and signed interface

Every name below is in `KAM.Planetary` unless qualified.

| Node / signed declaration | Lean declaration / locator | Verdict | Reason |
|---|---|---|---|
| signed Hamiltonian | `selectionHamiltonian`, Tori:27 | PASS | Definition byte-identical to canonical signature; unfolds to `realHamiltonian d.h f`. |
| signed output | `SelectionTori`, Tori:30 | PASS | Entire structure, parent and all six new fields byte-identical. |
| bpP:p11a:limit-torus | `limit_torus`, Tori:49 | PASS | Statement byte-identical; one constructed record from raw signed inputs. |
| stepP:p11a:lt-field | `tori_stage_cov`, `tori_jet_bound`, `tori_jet_small` | PASS | Computes the first jet and proves its difference from (omega_nu,0) tends to zero. |
| stepP:p11a:lt-cov | `tori_field_cov`, `tori_stage_cov` | PASS | Direct complex covariance; symplecticity and surjectivity derived, not supplied as new source premises. |
| stepP:p11a:lt-lim | `tori_invariance_C`, `tori_H0_field`, `tori_invariance_real` | PASS | Original-domain containment, field continuity, derivative/frequency limits, and exact frozen real-field identification. |
| stepP:p11a:lt-lag | `tori_lagrangian_C`, `tori_lagrangian` | PASS | Zero-section pullbacks converge; final equality uses frozen real symplecticForm. |
| stepP:p11a:lt-emb | `tori_immersion`, `tori_embedding` | PASS | Exact lower bounds in max norms, on all real angles/vectors. |
| stepP:p11a:lt-dio | inherited `SelectionOutput.diophantine` | PASS | IsDiophantine on Hinf for the same omega_star and schedule; H_subset embeds into Kinf. |

The primary affine-winding clause is inherited through `SelectionLimit.periodic` and the literal `selectionEvaluation` body. The orbit field is proved by chain rule at every real time, not merely at time zero. Positivity of 1 - 2^(-11) makes the two lower bounds imply immersion and injectivity. Together with winding, this supplies the expected injectivity modulo the lattice. No physical Cartesian periodicity is claimed for this affine-winding intermediate map; physical chart transport remains downstream.

The same record is extended from the `limit_map` witness; no unrelated existential choices are combined. Conditional helpers take already constructed records under distinct names. Only the signed source-facing `limit_torus` constructs the result, with no added premise, conclusion-shaped instance or bundled field replacing a proof.

## Every new public theorem

These helper exports are implementation results for the mapped parent nodes, rather than unsigned substitutes named after graph nodes. Local analytic hypotheses in the generic bridges are discharged at use sites. No widening of source constant dependence or carrier change was found.

| Node / locator | Lean declaration | Verdict | Reason |
|---|---|---|---|
| helper / Tori:49 | `limit_torus` | PASS | Raw data and perturbation only; constructs one shared SelectionTori witness. |
| helper / ToriBridge:34 | `tori_cauchy_dir` | PASS | Directional Cauchy estimate with positive closed-circle radius; local analytic premises. |
| helper / ToriBridge:67 | `tori_symplFormC_nondeg` | PASS | Tests coordinate basis vectors; no inverse assumed. |
| helper / ToriBridge:75 | `tori_clm_apply` | PASS | Coordinate expansion of an arbitrary continuous linear functional. |
| helper / ToriBridge:90 | `tori_fderiv_eq_symplFormC` | PASS | Correct minus sign for the frozen action-first symplectic form. |
| helper / ToriBridge:99 | `tori_symplFormC_sub` | PASS | Bilinear subtraction identity. |
| helper / ToriBridge:106 | `tori_surjective_of_near_id` | PASS | Proves injectivity from norm < 1, then finite-dimensional surjectivity. |
| helper / ToriBridge:123 | `tori_field_cov` | PASS | Conditional generic bridge; differentiability, symplecticity and surjectivity proved at its consumer. |
| helper / ToriBridge:148 | `tori_phaseToC_eq` | PASS | Existing real inclusions agree on the entire carrier. |
| helper / ToriField:29 | `toriH0_eq` | PASS | Shift and constant subtraction agree globally. |
| helper / ToriField:37 | `tori_H0_field` | PASS | Constant subtraction and action translation preserve the field globally, including totalized fderiv. |
| helper / ToriField:51 | `tori_eval_C` | PASS | Correct action translation by b after real inclusion. |
| helper / ToriField:58 | `tori_invariance_real` | PASS | Frozen realHamiltonian and frozen real hamiltonianVectorField, with domain/reality proved. |
| helper / ToriLimit:29 | `tori_h_deriv_real` | PASS | Reality of h derivative from a real segment inside its open collar. |
| helper / ToriLimit:79 | `tori_real_of_im` | PASS | Coordinatewise real reconstruction. |
| helper / ToriLimit:86 | `tori_mem_K` | PASS | Intersection membership at every finite stage. |
| helper / ToriLimit:90 | `tori_mem_d` | PASS | Stage-zero retained set is the original K. |
| helper / ToriLimit:95 | `tori_freq_real` | PASS | Reality of initial gradient plus all finite increments. |
| helper / ToriLimit:112 | `tori_freq_tendsto` | PASS | Real-part frequency convergence upgraded to complex convergence using proven reality. |
| helper / ToriLimit:124 | `tori_jet_small` | PASS | Both conservative Cauchy bounds decay geometrically; no division by zero. |
| helper / ToriLimit:166 | `tori_limit_mem` | PASS | Limit has real angle and action strictly inside theta collar. |
| helper / ToriLimit:186 | `tori_H0_cont` | PASS | Holomorphic H0 on an open domain gives continuity of its field at the limit. |
| helper / ToriLimit:205 | `tori_invariance_C` | PASS | Finite covariance, derivative/frequency convergence and vanishing jet yield complex invariance. |
| helper / ToriReal:32 | `tori_isReal` | PASS | Uses inherited limit_real for every real angle. |
| helper / ToriReal:35 | `tori_rr_eq` | PASS | Real restriction is the same limit evaluation before translating actions. |
| helper / ToriReal:41 | `tori_eval_eq` | PASS | Real evaluation is real restriction plus (0,b). |
| helper / ToriReal:47 | `tori_strip_pos` | PASS | Positive quarter strip. |
| helper / ToriReal:49 | `tori_analytic` | PASS | Real analyticity on all real angles via holomorphic restriction. |
| helper / ToriReal:57 | `tori_fderiv_eval` | PASS | Constant action translation has zero derivative. |
| helper / ToriReal:64 | `tori_fderiv_real` | PASS | Real derivative is the complex derivative applied to real directions. |
| helper / ToriReal:71 | `tori_diffAt_eval` | PASS | Actual differentiability, not reliance on totalized derivative. |
| helper / ToriReal:80 | `tori_immersion` | PASS | Exact signed lower bound 1 - 2^(-11). |
| helper / ToriReal:118 | `tori_embedding` | PASS | Exact signed covering-space lower bound 1 - 2^(-11). |
| helper / ToriReal:142 | `tori_lagrangian_C` | PASS | Continuous limit of canonical pullbacks on the zero section. |
| helper / ToriReal:185 | `tori_lagrangian` | PASS | Explicit restriction of Canonical.symplFormC to frozen symplecticForm. |
| helper / ToriStage:31 | `tori_single_norm` | PASS | Coordinate direction bound in the Pi max norm. |
| helper / ToriStage:37 | `toriH0_diffAt` | PASS | H0 holomorphic on the shifted original action collar. |
| helper / ToriStage:70 | `tori_mem_dom` | PASS | Zero section belongs to every finite composition domain. |
| helper / ToriStage:86 | `tori_s0_le_theta` | PASS | Radius containment derived from admissibility, not an extra input. |
| helper / ToriStage:97 | `tori_dom_mem` | PASS | Closed smaller test discs remain strictly inside each stage domain. |
| helper / ToriStage:113 | `tori_rem_diffAt` | PASS | Remainder holomorphy restricted to fixed parameter. |
| helper / ToriStage:121 | `tori_stage_cov` | PASS | Normal form differentiated locally, covariance hypotheses derived from composition output. |
| helper / ToriStage:184 | `tori_jet_bound` | PASS | Bounds with half action radius and quarter strip; sufficient for the literal zero-limit node. |

## Definition classification

| Declaration | Classification | Whole-carrier assessment |
|---|---|---|
| `selectionHamiltonian` | Exact alias | Frozen `realHamiltonian d.h f` for every real phase point. |
| `SelectionTori` | Output record | Extends the entire SelectionLimit witness with the exact six signed clauses; never an input to the source-facing theorem. |
| `toriH0` | Shifted initial Hamiltonian | Literal selectionInitial at fixed real parameter, including subtraction h(b), everywhere. |
| `toriRem` | Function restriction | Literal chain remainder at fixed parameter, everywhere. |
| `toriJet` | Explicit first jet | Frequency plus action derivative, negative angle derivative, everywhere. fderiv is Mathlib's totalized derivative; differentiability is proved at every substantive use. |
| `toriF` | Original complex Hamiltonian | h(I)+f(theta,I), everywhere. |

No new abbrev, norm instance, junk extension, or fallback is introduced. Exposed noncomputable public sections permit needed unfolding. Whole-carrier algebraic field identities remain valid even outside differentiability domains; analytic/limiting uses prove open-domain differentiability explicitly.

## Notes, design deviations and consumer limits

1. **Covariance route substitution.** Design P11B-LEAN-DESIGN.md:336 says: “Land and build that package through its owner before B16; use its actual factor-one type after proving the real restriction bridge.” Audit 2:84 retains this as N1. The delivered proof does not use chart_field: ToriBridge:123 proves complex covariance directly, ToriStage:121 discharges its premises, and ToriField:58 restricts to the frozen real field. This is a complete mathematical replacement for the covariance obligation, rather than evidence that the literal prescribed chart_field application was performed. Chart.lean and Chart.olean now exist in both this worktree and shared inp; this audit does not rerun the unrelated PP1-4 package or certify its historical release. Record the route reconciliation in campaign/design bookkeeping; no claim that N1 was discharged by a signature/build alone. The direct route agrees with the design's general B16 proof instructions at line 303 and avoids any extra small-flow premise.
2. **Conservative intermediate Cauchy constants.** Blueprint p11a4:135 gives epsilon_nu/s_nu and 2 epsilon_nu/strip. ToriStage:184 actually proves 2 epsilon_nu/s_nu plus 4 epsilon_nu/strip, using strictly interior closed circles. ToriLimit:124 proves this larger bound tends to zero. This changes an intermediate estimate, not the literal node conclusion (vanishing field remainder), any signed field, or any consumer constant. No claim is made that the sharper displayed intermediate inequalities were exported. The Stage module docstring states the sharper scale informally; the actual theorem is authoritative.
3. **Generated root and inherited whitespace.** The full protected-path diff contains KAM.lean as described above. Full `git diff --check inp...HEAD` exits 2 for inherited blank EOF lines at GAP-B-audit-1.md:286 and P11A-P2f-audit-1.md:317. Scoped `git diff --check inp...HEAD -- KAM/Planetary/WeakKAM/Tori*.lean` passes. No unrelated file was repaired.
4. No off-section normal form on a fixed positive action radius is asserted. Downstream displacement, parameter Lipschitz, measure, physical torus transport and frozen campaign anchors remain separate obligations.

No suspected new defect in a pinned mathematical source or frozen statement was identified. No external source lookup was required: this audit checks the pinned local blueprint/signature contract rather than independently re-transcribing Rus01. The deviations above are reported explicitly, not silently repaired.

## Independent verification

All auditor-initiated Lean/Lake commands use `LEAN_NUM_THREADS=1` and `nice -n 5`, sequentially. No heartbeat, recursion-depth or synthesis override; no clean, cache fetch, update, library-wide build or `.lake/packages` mutation.

Targeted compile gate (exit 0):

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b16 KAM.Planetary.WeakKAM.Tori
[inp-gate] slot 1 acquired 00:03:07 for KAM.Planetary.WeakKAM.Tori
Build completed successfully (9213 jobs).
```

Warnings are replayed from upstream dependencies (unused variables, deprecated names and style); no diagnostic names a scoped Tori file.

Signed probe in `.lake/abi-scratch/B16Probe.lean` uses a fresh copy of the exact signed `limit_torus` statement with `by exact limit_torus d epsilon he hsmall f hf` (actual Unicode binder names preserved), followed by:

```lean
example : type_of% @KAM.Planetary.limit_torus := @audit_limit_torus
example (d : SelectionData n) (f : SelectionPhaseC n → ℂ) :
    selectionHamiltonian d f = realHamiltonian d.h f := rfl
```

The probe also prints axioms of every one of the 43 new public theorems. Exact complete output:

```text
'KAM.Planetary.limit_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_cauchy_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_symplFormC_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_clm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_fderiv_eq_symplFormC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_symplFormC_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_surjective_of_near_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_field_cov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_phaseToC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.toriH0_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_H0_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_eval_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_invariance_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_h_deriv_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_real_of_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_mem_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_mem_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_freq_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_freq_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_jet_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_limit_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_H0_cont' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_invariance_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_isReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_rr_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_strip_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_fderiv_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_fderiv_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_diffAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_immersion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_lagrangian_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_lagrangian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_single_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.toriH0_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_mem_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_s0_le_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_dom_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_rem_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_stage_cov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tori_jet_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B16Probe.lean` (exit 0). The final repeat also exits 0; exactly 43 axiom lines, no errors or warnings. The repeated probe was for a directly captured completion status; it introduced no source change.

Kernel replay (exit 0), one invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Tori KAM.Planetary.WeakKAM.ToriField KAM.Planetary.WeakKAM.ToriLimit KAM.Planetary.WeakKAM.ToriReal KAM.Planetary.WeakKAM.ToriStage KAM.Planetary.WeakKAM.ToriBridge
replaying KAM.Planetary.WeakKAM.ToriBridge
replaying KAM.Planetary.WeakKAM.ToriStage
replaying KAM.Planetary.WeakKAM.ToriReal
replaying KAM.Planetary.WeakKAM.ToriLimit
replaying KAM.Planetary.WeakKAM.ToriField
replaying KAM.Planetary.WeakKAM.Tori
```

Lint command (exit 1 solely for the permitted stale generated root):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1115 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint diagnostic occurred. The root was left untouched as required.

Mechanical source checks: all six files have copyright, module declaration, public imports, module docstring and exposed public section. No forbidden token/resource override/EuclideanSpace appears in scoped files. All explicit public declarations live in KAM.Planetary; repository-wide explicit declaration scan finds no reused short name and no harmful root shadow. All 167 transitive local KAM modules were traversed: no Provider import and no frozen theorem import, hence no imported DRAFT_SORRY anchor. Frozen definitions only; no theorem manifest-state exception is needed.

| File | Lines | Maximum Unicode line width |
|---|---:|---:|
| Tori.lean | 77 | 98 |
| ToriBridge.lean | 155 | 98 |
| ToriField.lean | 101 | 99 |
| ToriLimit.lean | 268 | 100 |
| ToriReal.lean | 204 | 96 |
| ToriStage.lean | 242 | 97 |

Final integrity: signed source text, frozen files, manifest, generated root and canonical signatures were not modified. Temporary audit probes/logs/diff inventory were removed. Final status contains exactly the new untracked B16-audit-1.md and the pre-existing untracked B16-handoff.md. Report whitespace and the scoped branch diff pass `git diff --check`; the inherited whole-branch whitespace findings above remain disclosed. No unresolved audit check remains.
