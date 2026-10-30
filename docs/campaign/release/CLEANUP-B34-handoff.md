# Handoff CLEANUP-B34 (B3 unused helpers, B4 cross-directory duplicates)

Branch inp-b34. No renames. Nothing changed under KAM/Frozen, manifest, KAM/Certificate, KAM/SpinOrbit or KAM.lean, and no modules were added or removed. No new theorems, so there are no new `#print axioms` targets. All main results are untouched, and the frozen ABI hashes are unchanged (see checks).

## B3: helpers
For each of the 12, I searched for the name as a whole word across KAM/ (including Certificate and SpinOrbit), scripts/, docs/, manifest/ and blueprint*/. "Unused" below means the only hit is the declaration itself; a few also appear in historical audit logs (no Lean use). None is `@[simp]`. The full library builds green after deletion.

Deleted (8):
- `mSize_le_Theta`, KAM/Apost/Constants.lean:175. Only other hit: an axiom printout in docs/campaign/audits/P2-1b-audit-1.md:162 (historical).
- `nnfF_zero`, `nnfF_succ`, KAM/Nekhoroshev/Partial/NormalFormInduction.lean:398/404. No hits.
- `p11cTimeScale_one`, KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean:57. No hits.
- `qbc_tflat_le_one`, KAM/Planetary/Quantitative/BudgetPositivity.lean:163. No hits.
- `frameL0_mulVec`, `frameN0_mulVec`, KAM/Head/MatrixNorms.lean:60/65. Only other hits: axiom printouts in docs/campaign/audits/I-P4A-audit-1.md:171-172.
- `directionalCoeff_eq_sum`, KAM/Diophantine/Cohomological.lean:67. No hits.

Kept, because they are now used:
- `continuous_p11cTimeScale_apply` (PicardOp.lean:125, PicardComplex.lean:52)
- `continuous_p11cTimeScale` (PicardOp.lean:147)
- `isometry_ofReal_pi` (Head/HBounded.lean:64)
- `«lambda»` (Nekhoroshev/Averaging/Slab.lean:128; also a LEAN_REF in docs/graph/N)

The 24 API-looking lemmas are kept.

## B4: cross-directory duplicate groups
I regenerated the list with a scan of statement text (binders and conclusion up to `:=`, at least 60 characters) over KAM/ minus Frozen, Certificate, SpinOrbit and Provider. It found 10 groups spanning top-level directories (the plan said 9). I merged all 10. None of the names appears in KAM/Frozen, KAM/Provider, manifest or blueprints (checked with grep).

1. **sqMat entries.** Kept `KAM.Head.sqMat_apply_entry` (Head/TorsionRegularGeneral.lean; its import closure is 29 modules vs 35). Removed `KAM.Apost.sqMat_apply_eq` (Apost/Hamiltonian.lean:237). Uses rewritten: Apost/Hamiltonian.lean:244 and Apost/Frame.lean:275. Import added: Apost/Hamiltonian ← KAM.Head.TorsionRegularGeneral (3 new modules: Head.HamiltonianField, Head.PhaseAverage, Head.TorsionRegularGeneral; no cycle).
2. **Linear form on ℂⁿ×ℂⁿ.** Kept `KAM.Head.clm_prod_apply_eq_sum` (Head/Lagrangian.lean:58). Removed `KAM.Iso.Linear.Energy.apply_prod_decomp` (Iso/Linear/Energy.lean:45). Use rewritten: Iso/Linear/Energy.lean:54. Import added: Iso/Linear/Energy ← KAM.Head.Lagrangian. Note: Head.Lagrangian's closure (67) is slightly larger than Iso.Linear.Energy's (62), so "fewest imports" taken literally would keep the Iso copy. I kept Head because Head sits below Iso in the layering (Iso already uses Head lemmas), and the import pulls 11 Head/Frozen-Defs modules into a non-foundational file. Reversing this is a one-line change if the orchestrator prefers.
3. **symplecticForm on Phase 2.** Kept `KAM.Kepler.sf_eq` (Kepler/DelaunaySymplectic.lean:203, private → public). Removed private `bj_sf_eq` (Planetary/Poincare/Bijective.lean:174). Uses rewritten: Bijective.lean:176-179 and :198. Import already present.
4. **omegaZero_omegaZero.** Kept `KAM.omegaZero_omegaZero` (Matrix/Norms.lean:228). Removed the same-named copy in Strip/RealRestriction.lean:302. It had no uses; no module imports both files.
5. **differentiable_update.** Kept `KAM.differentiable_update` (Strip/Periodic.lean:152). Removed private `differentiable_update'` (Planetary/TwoScale/StepSchwarz.lean:27). Uses rewritten: StepSchwarz.lean:143 and :155. Import added: StepSchwarz ← KAM.Strip.Periodic (+ Strip.Averages).
6. **inClass_mono.** Kept `KAM.Weighted.inClass_mono` (Weighted/Bracket.lean:38, private → public). Removed private `inClass_mono'` (Nekhoroshev/NormalForm/IterativeRemainder.lean:38) and `inClass_mono''` (NormalForm/StepsOut.lean:154). Uses rewritten: IterativeRemainder.lean:52, 327, 329, 331, 360, 362 and StepsOut.lean:185, 216. Import already present (transitively).
7. **wsum_nonneg.** Kept `KAM.Weighted.wsum_nonneg` (Weighted/Bracket.lean:43, private → public). Removed private `wsum_nonneg'` (Nekhoroshev/NormalForm/BracketDecomp.lean:34). Uses rewritten: BracketDecomp.lean:137 and :142.
8. **Continuity of real slices.** Kept `KAM.Weighted.continuous_real_slice` (Weighted/Bracket.lean:48, private → public). Removed private `continuous_slice` (BracketDecomp.lean:38). Use rewritten: BracketDecomp.lean:123.
9. **realInclusion_single.** Kept `KAM.realInclusion_single` (Strip/RealRestriction.lean:235). Removed private `KAM.Weighted.realInclusion_single` (Weighted/Coefficients.lean:146) and `KAM.Planetary.realInclusion_single` (Planetary/PGAssembly/FastComplex.lean:192). Uses rewritten: Weighted/Coefficients.lean (two uses, now `KAM.realInclusion_single`) and FastComplex.lean:231. Import added: Weighted/Coefficients ← KAM.Strip.RealRestriction (+2 Frozen Defs: HamiltonianVectorField, HamiltonianVectorFieldC). Left alone: `KAM.Head.realInclusion_single` (Head/Frequency.lean:82) states the same fact, but with a type ascription, so the scan does not count it as identical. It has about 7 qualified uses in Iso/Planetary. Candidate for a later pass.
10. **planeSq_smul.** Kept `KAM.Kepler.planeSq_smul` (Kepler/Energy.lean:123, private → public; the other three files import it). Removed private `planeSq_smul_MK` (Kepler/Mass.lean:351), public `KAM.Planetary.planeSq_smul` (Planetary/Newtonian/Reduction.lean:84) and private `sy_planeSq_smul` (Planetary/Poincare/Symplectic.lean:342). Uses rewritten: Mass.lean:551 and :573, Reduction.lean:278, Symplectic.lean:394. Same-directory near-copies (`planeSq_smul'`/`''` in PlanarTorsion and SecularForm, with different binder names) were not touched.

Groups left: none of the cross-directory ones. Same-directory cross-file groups (about 90, e.g. Nekhoroshev/Partial RealSystem vs Symplectic, Planetary/PlanarAssembly vs FixedAssembly) were outside the brief's 9/10 cross-directory scope and are unchanged.

### Within-file groups (listed only, nothing changed)
- [('KAM/Iso/Linear/FullRangeStepsExt.lean', 39, 'step_eb_holo'), ('KAM/Iso/Linear/FullRangeStepsExt.lean', 103, 'step_eb_holo_conclude')]
- [('KAM/Nekhoroshev/Assembly/Confinement.lean', 75, 'cf_setting'), ('KAM/Nekhoroshev/Assembly/Confinement.lean', 99, 'head_theorem1_setting')]
- [('KAM/Nekhoroshev/Partial/Domain.lean', 117, 'domain_field'), ('KAM/Nekhoroshev/Partial/Domain.lean', 372, 'domain'), ('KAM/Nekhoroshev/Partial/Domain.lean', 701, 'domain_field_scaled'), ('KAM/Nekhoroshev/Partial/Domain.lean', 780, 'domain_physical_analytic')]
- [('KAM/Planetary/Averaging/OscillatorBracket.lean', 389, 'fderiv_oscFunction'), ('KAM/Planetary/Averaging/OscillatorBracket.lean', 716, 'osc_deriv_eqs')]
- [('KAM/Planetary/Averaging/OscillatorBracket.lean', 441, 'line_I'), ('KAM/Planetary/Averaging/OscillatorBracket.lean', 462, 'line_p'), ('KAM/Planetary/Averaging/OscillatorBracket.lean', 497, 'line_q')]
- [('KAM/Planetary/Averaging/OscillatorBracket.lean', 786, "lineI'"), ('KAM/Planetary/Averaging/OscillatorBracket.lean', 794, "lineP'"), ('KAM/Planetary/Averaging/OscillatorBracket.lean', 802, "lineQ'")]

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-b34 KAM` → `Build completed successfully (10429 jobs).`, rc=0, no errors. (An earlier attempt was cut short by my own 590 s tool timeout; it was re-run to completion.)
- `sh scripts/lint_sources.sh` → `check_lean_modules: PASS (1383 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`.
- `python3 scripts/check_frozen_anchors.py --root ... --manifest .../frozen-anchors.json` → `FROZEN-ANCHOR GUARD OK`.
- No maxHeartbeats or other overrides; no new sorry/axiom; every file is well under 1500 lines.

## Uncertainties and deviations
- Five private lemmas became public (`sf_eq`, `planeSq_smul`, `inClass_mono`, `wsum_nonneg`, `continuous_real_slice`). Their generic short names now live in KAM.Kepler and KAM.Weighted. The build is green, so there are no clashes today.
- Group 2 keeps the copy in the module with the larger closure (rationale above).
- The scan compares statement text, so binders hidden in `variable` declarations could make two "identical" texts differ. Every merge type-checked in the full build, which confirms the statements really were identical.
- Errata: none.

AUDIT FOCUS (release clean-up, code-changing): (1) every deleted declaration was really unused (grep the whole repo: KAM/ including Certificate and SpinOrbit, scripts/, docs/graph, manifest/, blueprint*/), and none is named by a frozen file, the manifest or a provider; (2) every merged duplicate group: the kept and removed statements are definitionally the same proposition (same binders, same conclusion) and every rewritten use now cites the kept one; no proof changed in meaning; (3) the five private-to-public promotions (sf_eq, planeSq_smul, inClass_mono, wsum_nonneg, continuous_real_slice): no clash or shadowing with Mathlib or other KAM names, and the names are acceptable public API (flag any that should be renamed later under D1); (4) no statement of a frozen anchor, provider or graph-referenced lemma changed; the dependency graphs' LEAN_REF entries still resolve (docs/graph/*/DEPGRAPH.md mention deleted or renamed names?); (5) build, lint, frozen guard and ABI hashes as reported.
