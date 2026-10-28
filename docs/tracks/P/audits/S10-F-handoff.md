# S10-F prover handoff (branch inp-s10f, 6b90a48b; contains inp-s10h (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all new; ~720 lines total)
- KAM/Planetary/Nondegeneracy/SymmetricRelation.lean (facade; `fc_analytic`, `f_nonzero`, induction, n=2 base)
- SymmetricRelation/Defs.lean (`relation`, `fc_def`, verbatim)
- SymmetricRelation/Analytic.lean (`relationPoly`, `esymm_sorted`, `exists_relation_poly`, `fc_analytic_aux`)
- SymmetricRelation/Limits.lean (`sigma_cons_close`, `tendsto_sigma_cons`, `relLim`, `tendsto_relation`, `sigma_one`)
- SymmetricRelation/Cases.lean (`tendsto_nu_zero`, `case_A`, `case_lim`, `peelPerm`, `peelRel`, `relLim_eq`)
- SymmetricRelation/Small.lean (`fc_ne_zero_single`, `exists_small_ratio`, `fc_ne_zero_two`)

## Approach
- fc_analytic (bpP:p10:Fc-analytic): prod_π (X + Σ c''_j σ_πj) ∈ ℝ[X][σ] is symmetric; `esymmAlgEquiv` over ℝ[X] gives a polynomial in e_k(σ) = ± charpoly coefficients of `coeffs D a` (analytic on axes n); expanded via `eval₂_eq'`.
- f_nonzero (bpP:p10:F-nonzero): induction on n≥2 with a = (t, a'), t↓0, using `peel` + `weyl` (σ(t,a') → (σ(a'),0)), `ν_1 → ∞`. Case A (c'_1≠0): L/ν_1 → c'_1. Case C1: limit of L_{c,π} equals a factor L^{(n-1)}_{c^{(d)},π''} (d=π⁻¹(last), π'' = `peelPerm π`), nonzero at an a' chosen by `generic` (S10-Z) from IH. C2 and single-nonzero-c'': σ_l<0. Base n=2: peeling with n-1=1 (σ_outer=0 by `sigma_one`), c'_2≠0 by limit; c'=0, both c'' nonzero via `n2` (σ₂/σ₁ arbitrarily small).
- No bijection S_n ≃ [n]×S_{n-1} needed: only factor-wise nonvanishing.

## Checks
- gate build `KAM.Planetary.Nondegeneracy.SymmetricRelation`: "Build completed successfully (9143 jobs)"; no sorry, no errors in my files (one unused-simp-arg linter warning in Analytic.lean).
- `scripts/lint_sources.sh`: PASS except "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated; not edited, orchestrator to regenerate for the new modules). Long-line warnings fixed.
- `#print axioms KAM.Planetary.Nondegeneracy.fc_analytic` and `...f_nonzero`: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no EuclideanSpace, no new axiom/sorry; each file ≤ 300 lines. Module path is KAM/Planetary/Nondegeneracy/SymmetricRelation (the existing Nondegeneracy sibling location).

## Uncertainties / errata / deviations
- Signatures verbatim (`relation`, `fc_def`, `fc_analytic`, `f_nonzero`); no statement changes, no extra hypotheses. No design signals.
- Extra public helper names introduced (all grep-checked unique): relationPoly, esymm_sorted, exists_relation_poly, fc_analytic_aux, analyticAt_nu_action, snocZero, coeffs_one, sigma_one, sigma_outer_nonpos, sigma_cons_close, tendsto_sigma_cons, eventually_cons_mem, relLim, relation_cons, tendsto_relation, tendsto_nu_zero, eventually_ne_of_cons, case_A, case_lim, peelPerm, peelRel, relLim_eq, relation_of_fast_zero, fc_ne_zero_single, two_forms_ne, exists_small_ratio, fc_ne_zero_two, f_nonzero_two, f_nonzero_aux.
- Source note: the blueprint's Case B (n=2) is covered by the limit criterion (c'_2≠0) plus `n2` ratio argument; matches source. No source defects found.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-F and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) relation, fc_def, fc_analytic, f_nonzero = signature file exactly, and the S10-F slice COMPLETE; (2) proofs sound (esymmAlgEquiv over R[X]; S10-H, S10-P, S10-Z consumed as designed; the spectral case split, limits and induction with the n=2 base); no added premises; (3) NAMES: several public names are generic (relation, case_A, case_lim, sigma_one, peelPerm, relLim...): confirm their fully qualified names collide with nothing in KAM (whole-library co-import), and flag any that would shadow common Mathlib names inside the namespace; (4) hygiene (no EuclideanSpace). Audit ONLY KAM/Planetary/Nondegeneracy/SymmetricRelation.lean and SymmetricRelation/*.lean.
