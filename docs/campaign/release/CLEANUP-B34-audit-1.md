# CLEANUP-B34 independent audit 1

Verdict: **PASS WITH NOTES** for this release-cleanup batch, No batch correctness defect found. No anchor is being sealed by this audit: all 144 frozen declarations retain their recorded ABI. Provider/frozen signature and seal-body replacement probes are inapplicable because neither surface changes.

Audited `/root/code/KAM-inp-b34` at `59ded5010141b7c521f96740700832f9bf7a6db9`, against `inp` = `0319427f9030707d7d39672fb464a2954dfc1afa`, using the full `git diff inp...HEAD`, the package audit brief, AGENTS.md, PLAN.md, DECISIONS.md and the handoff's AUDIT FOCUS. This report's destination follows the user's explicit worktree path, overriding the brief's generic main-worktree destination. Scope: 23 modified Lean modules; no module addition/deletion, no new definitions or altered theorem statements. Only the report is a repository edit; probes were confined to `.lake/abi-scratch/` and removed after use.

## Deleted unused helpers

PASS means unused in the audited repository, not a promise of compatibility for external clients of deleted public helpers. For each name, `git grep -n -w NAME inp -- KAM scripts docs/graph manifest blueprint blueprint-I blueprint-N blueprint-P` finds exactly its original declaration. The KAM search includes Certificate, SpinOrbit, Frozen and Provider. Fresh `rg --pcre2 -n '(?<![\w])NAME(?![\w\x27])'` searches across KAM, scripts, docs, manifest and every present blueprint directory find no executable/source-graph consumer. Remaining documentation mentions belong to cleanup plans/handoffs or historical audits. No deleted helper was a simp lemma or had a registration that would make the textual non-use argument inadequate.

| Deleted declaration | Base locator | Verdict | Reason |
|---|---|---|---|
| `KAM.Apost.mSize_le_Theta` | `KAM/Apost/Constants.lean:175` | PASS | Declaration-only source occurrence. |
| `nnfF_zero` | `KAM/Nekhoroshev/Partial/NormalFormInduction.lean:398` | PASS | Declaration-only source occurrence. |
| `nnfF_succ` | `KAM/Nekhoroshev/Partial/NormalFormInduction.lean:404` | PASS | Declaration-only source occurrence. |
| `p11cTimeScale_one` | `KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean:57` | PASS | Declaration-only source occurrence. |
| `qbc_tflat_le_one` | `KAM/Planetary/Quantitative/BudgetPositivity.lean:163` | PASS | Declaration-only source occurrence. |
| `KAM.Head.frameL0_mulVec` | `KAM/Head/MatrixNorms.lean:60` | PASS | Declaration-only source occurrence. |
| `KAM.Head.frameN0_mulVec` | `KAM/Head/MatrixNorms.lean:65` | PASS | Declaration-only source occurrence. |
| `directionalCoeff_eq_sum` | `KAM/Diophantine/Cohomological.lean:67` | PASS | Declaration-only source occurrence. |

The other four candidate helpers were retained; no finding requires deleting them. The handoff's “No hits” should be read as no live source use: the cleanup plan and handoff themselves mention the deleted names.

## Duplicate groups and statement fidelity

All 14 removed duplicate declarations were checked against the ten retained lemmas. The probe extracts each old explicit binder list and proposition from `git show inp:PATH`, restores its namespace and its implicit dimension binder where applicable, then elaborates `example : ∀ <old binders>, <old conclusion> := @<retained lemma>`. There is no rewriting, simplification, extra hypothesis, or conversion theorem in these assignments. This checks the entire dependent function type, including binder order. A comments-masked comparison separately finds **zero retained declaration header changes** across all 23 touched modules. The complete diff contains only deletions, visibility promotions, imports and reference substitutions; no other proof transformation changes meaning.

| Group | Removed declaration (base module) | Retained declaration | Verdict |
|---|---|---|---|
| 1 | `KAM.Apost.sqMat_apply_eq` (`Apost/Hamiltonian`) | `KAM.Head.sqMat_apply_entry` | PASS |
| 2 | `KAM.Iso.Linear.Energy.apply_prod_decomp` (`Iso/Linear/Energy`) | `KAM.Head.clm_prod_apply_eq_sum` | PASS WITH NOTES: import closure grows. |
| 3 | private `bj_sf_eq` (`Planetary/Poincare/Bijective`) | `KAM.Kepler.sf_eq` | PASS |
| 4 | `KAM.omegaZero_omegaZero` (`Strip/RealRestriction`) | `KAM.omegaZero_omegaZero` (`Matrix/Norms`) | PASS: same public proposition survives; no rewritten consumer needed. |
| 5 | private `differentiable_update'` (`Planetary/TwoScale/StepSchwarz`) | `KAM.differentiable_update` | PASS |
| 6 | private `inClass_mono'` (`Nekhoroshev/NormalForm/IterativeRemainder`) | `KAM.Weighted.inClass_mono` | PASS |
| 6 | private `inClass_mono''` (`Nekhoroshev/NormalForm/StepsOut`) | `KAM.Weighted.inClass_mono` | PASS |
| 7 | private `wsum_nonneg'` (`Nekhoroshev/NormalForm/BracketDecomp`) | `KAM.Weighted.wsum_nonneg` | PASS |
| 8 | private `continuous_slice` (`Nekhoroshev/NormalForm/BracketDecomp`) | `KAM.Weighted.continuous_real_slice` | PASS |
| 9 | private `realInclusion_single` (`Weighted/Coefficients`) | `KAM.realInclusion_single` | PASS |
| 9 | `KAM.Planetary.realInclusion_single` (`Planetary/PGAssembly/FastComplex`) | `KAM.realInclusion_single` | PASS |
| 10 | private `planeSq_smul_MK` (`Kepler/Mass`) | `KAM.Kepler.planeSq_smul` | PASS |
| 10 | `KAM.Planetary.planeSq_smul` (`Planetary/Newtonian/Reduction`) | `KAM.Kepler.planeSq_smul` | PASS |
| 10 | private `sy_planeSq_smul` (`Planetary/Poincare/Symplectic`) | `KAM.Kepler.planeSq_smul` | PASS |

All rewritten occurrences in the full diff cite the retained lemma, qualified where necessary. Surviving short-name hits such as `continuous_slice` and `wsum_nonneg'` in Nekhoroshev/Partial/Bracket are separate private declarations, not missed uses of the removed helpers. No removed declaration is named by a frozen file, provider or manifest.

## Definitions and new public API

Definition classification: **no added or changed `def`, `abbrev`, `structure` or `class`**. Existing objects and totalization/domain conventions are untouched. No new premise, instance, bundle field, ambient type, normalizer or conclusion-shaped assumption is introduced.

The five promotions are genuine new public exports, so this audit prints their axioms even though their proofs predate the batch. Source declaration scans cover all KAM and the installed Mathlib sources, not just imported files.

| New public export | HEAD locator | Collision/API assessment |
|---|---|---|
| `KAM.Kepler.sf_eq` | `KAM/Kepler/DelaunaySymplectic.lean:203` | No competing declaration with this short name. Correct export; `sf_eq` is cryptic for a public name, so rename later to describe the dimension-two symplectic-form expansion. Nonblocking naming note under D33 / cleanup-plan D1. |
| `KAM.Kepler.planeSq_smul` | `KAM/Kepler/Energy.lean:123` | Unique surviving exact short name; descriptive and acceptable in Kepler namespace. |
| `KAM.Weighted.inClass_mono` | `KAM/Weighted/Bracket.lean:38` | No competing public short name. Two unrelated private homonyms in Canonical/VectorField:46 and Planetary/Averaging/FiniteGen:30; their local resolution is unchanged. Acceptable namespaced API. |
| `KAM.Weighted.wsum_nonneg` | `KAM/Weighted/Bracket.lean:43` | No competing exact short name; acceptable API for the existing `wsum`. |
| `KAM.Weighted.continuous_real_slice` | `KAM/Weighted/Bracket.lean:48` | No competing exact short name; descriptive API. |

Pre-existing rename candidates, **not findings of this batch**: `planeDot_comm`, `realInclusion_single`, `solve`, `solve_unique`. Their reuse elsewhere in KAM/Mathlib predates this change. In the touched modules the declaration counts are respectively 1→1, 3→1, 1→1, 1→1. Across KAM, `realInclusion_single` decreases from four declarations to two (the unchanged `KAM.Head.realInclusion_single` and retained `KAM.realInclusion_single`). No reuse is made worse. Defer renames under DECISIONS.md D33 and CLEANUP-PLAN.md D1, as explicitly directed by the owner.

## Graph, frozen and import integrity

`git diff inp...HEAD -- KAM/Frozen KAM/Provider manifest KAM.lean README.md docs/graph` is empty. None of the deleted/merged helper names occurs in any of `docs/graph/{K,I,N,P}/DEPGRAPH.md`; therefore no LEAN_REF is broken by these deletions. Every surviving graph-referenced declaration keeps its statement, and no graph node is newly claimed proved by this cleanup. This is a change-scoped reference audit, not a fresh global validation of every historical graph edge.

The new imports point to existing theorem modules: Apost/Hamiltonian → Head/TorsionRegularGeneral; Iso/Linear/Energy → Head/Lagrangian; Planetary/TwoScale/StepSchwarz → Strip/Periodic; Weighted/Coefficients → Strip/RealRestriction. No provider or draft anchor import is added. Lint and builds independently check the relevant import discipline and absence of cycles. Group 2 keeps the Head copy despite its larger closure: reasonable layering, with a modest dependency-cost tradeoff. No correctness blocker; moving common algebra into a lighter module can wait for a separately scoped refactor.

## Independent verification receipts

All Lean/Lake/kernel invocations used `LEAN_NUM_THREADS=1` and `nice -n 5`, serially. Lint (including its ABI Lean probe) finished before the module build loop; builds finished before signature/axiom probes and kernel replay. No full-library build, cache operation, clean, package edit, or resource-limit override was used.

### Lint and invariants

Command: `LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh` → exit 0. Exact output:

```text
check_lean_modules: PASS (1383 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

`git diff --check inp...HEAD` → exit 0, no output. The protected-path diff quoted above → exit 0, no output. The maximum touched file length is 940 lines (`KAM/Apost/Constants.lean`), below 1500. Lint checks module structure, forbidden proof escapes, resource overrides and import quarantine; no exception for a stale generated root was needed.

### Targeted builds

For each module below, sequentially:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b34 "$mod"
```

The gate invokes `nice -n 5 lake build "$mod"`. Each invocation returned exit 0. These are snapshot-backed targeted builds, not a fresh independent rebuild of all library dependencies. Exact terminal success lines:

| Module | Output |
|---|---|
| `KAM.Apost.Constants` | `Build completed successfully (2871 jobs).` |
| `KAM.Apost.Frame` | `Build completed successfully (3187 jobs).` |
| `KAM.Apost.Hamiltonian` | `Build completed successfully (2906 jobs).` |
| `KAM.Diophantine.Cohomological` | `Build completed successfully (2076 jobs).` |
| `KAM.Head.MatrixNorms` | `Build completed successfully (2857 jobs).` |
| `KAM.Iso.Linear.Energy` | `Build completed successfully (3209 jobs).` |
| `KAM.Kepler.DelaunaySymplectic` | `Build completed successfully (9096 jobs).` |
| `KAM.Kepler.Energy` | `Build completed successfully (9087 jobs).` |
| `KAM.Kepler.Mass` | `Build completed successfully (9099 jobs).` |
| `KAM.Nekhoroshev.NormalForm.BracketDecomp` | `Build completed successfully (3167 jobs).` |
| `KAM.Nekhoroshev.NormalForm.IterativeRemainder` | `Build completed successfully (3226 jobs).` |
| `KAM.Nekhoroshev.NormalForm.StepsOut` | `Build completed successfully (3236 jobs).` |
| `KAM.Nekhoroshev.Partial.NormalFormInduction` | `Build completed successfully (3286 jobs).` |
| `KAM.Planetary.Newtonian.Reduction` | `Build completed successfully (9092 jobs).` |
| `KAM.Planetary.PGAssembly.FastComplex` | `Build completed successfully (9098 jobs).` |
| `KAM.Planetary.PlanarTorsion.RealFlow.PicardOp` | `Build completed successfully (9057 jobs).` |
| `KAM.Planetary.Poincare.Bijective` | `Build completed successfully (9102 jobs).` |
| `KAM.Planetary.Poincare.Symplectic` | `Build completed successfully (9101 jobs).` |
| `KAM.Planetary.Quantitative.BudgetPositivity` | `Build completed successfully (9087 jobs).` |
| `KAM.Planetary.TwoScale.StepSchwarz` | `Build completed successfully (2857 jobs).` |
| `KAM.Strip.RealRestriction` | `Build completed successfully (2852 jobs).` |
| `KAM.Weighted.Bracket` | `Build completed successfully (3165 jobs).` |
| `KAM.Weighted.Coefficients` | `Build completed successfully (3160 jobs).` |

### Signature and axiom probes

`LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B34Probe.lean` → exit 0, all 14 direct-assignment examples accepted. The first scratch attempt omitted the original `KAM.Torus` / `KAM.Planetary` opens and failed with unknown identifiers; restoring those opens resolved the probe setup error. The successful probe sets `autoImplicit false` so an unresolved identifier cannot become an implicit premise. Warnings only flag intentionally unused hypothesis binder names in the copied forall signatures. No resource or linter override was introduced.

Exact `#print axioms` output for all ten retained lemmas (including all five newly public exports):

```text
'KAM.Head.sqMat_apply_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Head.clm_prod_apply_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.sf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.omegaZero_omegaZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.differentiable_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.inClass_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.wsum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.continuous_real_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.realInclusion_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.planeSq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

<details>
<summary>Reproducible signature probe (accepted final version)</summary>

```lean
/- Audit scratch: old explicit signatures checked by direct term assignment. -/
module
import KAM.Apost.Hamiltonian
import KAM.Iso.Linear.Energy
import KAM.Planetary.Poincare.Bijective
import KAM.Strip.RealRestriction
import KAM.Planetary.TwoScale.StepSchwarz
import KAM.Nekhoroshev.NormalForm.IterativeRemainder
import KAM.Nekhoroshev.NormalForm.StepsOut
import KAM.Nekhoroshev.NormalForm.BracketDecomp
import KAM.Weighted.Coefficients
import KAM.Planetary.PGAssembly.FastComplex
import KAM.Kepler.Mass
import KAM.Planetary.Newtonian.Reduction
import KAM.Planetary.Poincare.Symplectic
import KAM.Matrix.Norms
import KAM.Weighted.Bracket
import KAM.Head.TorsionRegularGeneral
import KAM.Head.Lagrangian

/-! CLEANUP-B34 audit probes. -/
public section
set_option autoImplicit false
open Set Metric KAM KAM.Kepler KAM.Planetary KAM.Torus KAM.Weighted KAM.Canonical

namespace KAM.Apost
-- KAM/Apost/Hamiltonian.lean: sqMat_apply_eq
example : ∀ {n : ℕ}  (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ))
    (s t : Fin n ⊕ Fin n) ,
    sqMat U s t = sumVec n (U ((sumVec n).symm (Pi.single t 1))) s  := @KAM.Head.sqMat_apply_entry
end KAM.Apost

namespace KAM.Iso.Linear.Energy
-- KAM/Iso/Linear/Energy.lean: apply_prod_decomp
example : ∀ {n : ℕ}  (ℓ : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ)
    (u : (Fin n → ℂ) × (Fin n → ℂ)) ,
    ℓ u = ∑ i, u.1 i * ℓ (Pi.single i 1, 0) + ∑ i, u.2 i * ℓ (0, Pi.single i 1)  := @KAM.Head.clm_prod_apply_eq_sum
end KAM.Iso.Linear.Energy

namespace KAM.Planetary
-- KAM/Planetary/Poincare/Bijective.lean: bj_sf_eq
example : ∀  (a b : Phase 2) ,  symplecticForm a b =
    (a.2 0 * b.1 0 + a.2 1 * b.1 1) - (a.1 0 * b.2 0 + a.1 1 * b.2 1)  := @KAM.Kepler.sf_eq
end KAM.Planetary

namespace KAM
-- KAM/Strip/RealRestriction.lean: omegaZero_omegaZero
example : ∀ {n : ℕ}  (u : (Fin n → ℂ) × (Fin n → ℂ)) ,  omegaZero (omegaZero u) = -u  := @KAM.omegaZero_omegaZero
end KAM

namespace KAM.Planetary
-- KAM/Planetary/TwoScale/StepSchwarz.lean: differentiable_update'
example : ∀ {n : ℕ}  (θ : Fin n → ℂ) (j : Fin n) ,
    Differentiable ℂ (fun ζ : ℂ => Function.update θ j ζ)  := @KAM.differentiable_update
end KAM.Planetary

namespace KAM.NormalForm
-- KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean: inClass_mono'
example : ∀ {n : ℕ}  {D : Set (Fin n → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) ,
    InClass D r s u  := @KAM.Weighted.inClass_mono
end KAM.NormalForm

namespace KAM.NormalForm
-- KAM/Nekhoroshev/NormalForm/StepsOut.lean: inClass_mono''
example : ∀ {n : ℕ}  {D : Set (Fin n → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) ,
    InClass D r s u  := @KAM.Weighted.inClass_mono
end KAM.NormalForm

namespace KAM.NormalForm
-- KAM/Nekhoroshev/NormalForm/BracketDecomp.lean: wsum_nonneg'
example : ∀ {n : ℕ}  (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (s : ℝ) (I : Fin n → ℂ) ,
    0 ≤ wsum f s I  := @KAM.Weighted.wsum_nonneg
end KAM.NormalForm

namespace KAM.NormalForm
-- KAM/Nekhoroshev/NormalForm/BracketDecomp.lean: continuous_slice
example : ∀ {n : ℕ}  {D : Set (Fin n → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hu : InClass D r s u) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) ,  Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I)  := @KAM.Weighted.continuous_real_slice
end KAM.NormalForm

namespace KAM.Weighted
-- KAM/Weighted/Coefficients.lean: realInclusion_single
example : ∀ {n : ℕ}  (i : Fin n) ,
    KAM.realInclusion n (Pi.single i 1) = Pi.single i 1  := @KAM.realInclusion_single
end KAM.Weighted

namespace KAM.Planetary
-- KAM/Planetary/PGAssembly/FastComplex.lean: realInclusion_single
example : ∀ {n : ℕ}  (i : Fin n) ,
    KAM.realInclusion n (Pi.single i 1) = Pi.single i 1  := @KAM.realInclusion_single
end KAM.Planetary

namespace KAM.Kepler
-- KAM/Kepler/Mass.lean: planeSq_smul_MK
example : ∀  (c : ℝ) (v : Fin 2 → ℝ) ,  planeSq (c • v) = c ^ 2 * planeSq v  := @KAM.Kepler.planeSq_smul
end KAM.Kepler

namespace KAM.Planetary
-- KAM/Planetary/Newtonian/Reduction.lean: planeSq_smul
example : ∀  (c : ℝ) (v : Fin 2 → ℝ) ,  planeSq (c • v) = c ^ 2 * planeSq v  := @KAM.Kepler.planeSq_smul
end KAM.Planetary

namespace KAM.Planetary
-- KAM/Planetary/Poincare/Symplectic.lean: sy_planeSq_smul
example : ∀  (c : ℝ) (v : Fin 2 → ℝ) ,  planeSq (c • v) = c ^ 2 * planeSq v  := @KAM.Kepler.planeSq_smul
end KAM.Planetary

#print axioms KAM.Head.sqMat_apply_entry

#print axioms KAM.Head.clm_prod_apply_eq_sum

#print axioms KAM.Kepler.sf_eq

#print axioms KAM.omegaZero_omegaZero

#print axioms KAM.differentiable_update

#print axioms KAM.Weighted.inClass_mono

#print axioms KAM.Weighted.wsum_nonneg

#print axioms KAM.Weighted.continuous_real_slice

#print axioms KAM.realInclusion_single

#print axioms KAM.Kepler.planeSq_smul
```

</details>

### Kernel replay

One module per invocation, sequentially (the user's tighter memory constraint overrides the brief's generic suggestion to pass multiple modules):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose "$mod"
```

Every invocation below returned exit 0. Exact stdout is the “replaying” line shown; there were no reported kernel errors. All nine modules are touched by this batch and together cover every merged duplicate group.

| Module | Group coverage | Exit | Exact output |
|---|---|---|---|
| `KAM.Apost.Hamiltonian` | 1 | 0 | `replaying KAM.Apost.Hamiltonian` |
| `KAM.Iso.Linear.Energy` | 2 | 0 | `replaying KAM.Iso.Linear.Energy` |
| `KAM.Kepler.DelaunaySymplectic` | 3 | 0 | `replaying KAM.Kepler.DelaunaySymplectic` |
| `KAM.Strip.RealRestriction` | 4 | 0 | `replaying KAM.Strip.RealRestriction` |
| `KAM.Planetary.TwoScale.StepSchwarz` | 5 | 0 | `replaying KAM.Planetary.TwoScale.StepSchwarz` |
| `KAM.Nekhoroshev.NormalForm.IterativeRemainder` | 6 | 0 | `replaying KAM.Nekhoroshev.NormalForm.IterativeRemainder` |
| `KAM.Weighted.Bracket` | 7 and 8 | 0 | `replaying KAM.Weighted.Bracket` |
| `KAM.Weighted.Coefficients` | 9 | 0 | `replaying KAM.Weighted.Coefficients` |
| `KAM.Kepler.Energy` | 10 | 0 | `replaying KAM.Kepler.Energy` |

## Uncertainties, errata and deviations

No suspected pinned-source or blueprint defect was discovered. This cleanup introduces no new source-facing mathematical assertion, so there is no new source erratum or frozen-statement repair to request. No production-code deviations were introduced by the auditor. The handoff's full-library success is a worker receipt; this audit independently reran all 23 touched targets and the representative kernel subset above, rather than claiming a second full-library rebuild.

The two nonblocking maintenance notes are the larger import closure in group 2 and the cryptic newly public `sf_eq` name. The four owner-designated pre-existing short-name reuses are recorded only for the later rename batch. Semantic conclusions are limited to the reviewed cleanup diff, its unchanged signatures and these verification gates; this audit does not re-prove campaign-level theorem or graph closure.

Final integrity check: `git diff --check inp...HEAD` and `git diff --no-index --check /dev/null docs/campaign/release/CLEANUP-B34-audit-1.md` exit 0 without output. `git status --short` lists only this new report. Scratch probes and logs were removed after copying the receipts into this report.
