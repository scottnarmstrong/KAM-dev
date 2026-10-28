# P11A-C5 prover handoff (branch inp-p11ac5, 92d953c; contains inp-p11ac4 (audited) and W8; offloaded package run by the main orchestrator; prover on claude-12)


## Files
- `KAM/Planetary/MaximalStep/Homological.lean` (688 lines): defs `p11Solve`, `p11AngleClass`, `p11AngleAverage`
  (verbatim); `homological_maximal`, `homological_maximal_real`, `homological_maximal_param` (signatures verbatim);
  helpers (`hmCoef`, `hmCut`, `hmModes`, `p11Solve_eq`, `truncate_eq`, finite-trig-sum lemmas, `norm_coeff_le`,
  `differentiableOn_coeff`, `sum_exp_le_lambda`, `norm_hmCoef_le`, `norm_solve_le`, `solve_unique`, `fderiv_solve`,
  `coeff_solve`, `conj_character_real`, `coeff_neg_conj`, `hmCoef_neg_conj`, `param_cauchy_scalar`).
- `KAM/Planetary/MaximalStep/HomologicalBracket.lean` (84 lines): `p11Affine` (verbatim) and
  `p11_normal_affine_bracket`; publicly imported by `Homological`.
- Imports: C3 `Parameter`, C0 `Constants`; no provider / DRAFT_SORRY anchor. (C4 not needed.)

## Approach
`p11Solve` is the finite Fourier sum `fourierSum (hmCoef ..)`; truncation `truncate` = `fourierSum (hmCut ..)`.
Everything is read off the finite sums: termwise equation, coefficient decay from `KAM.norm_torusCoeff_le`,
`Λ` via `p11_lambda_spec` (n=0 handled separately, no `hn` needed in `_param`), holomorphy of coefficients in
b by a parametric-integral copy of `Weighted.coeff_param` on an arbitrary open B, uniqueness by comparing
coefficients of the two finite trig polynomials, reality by `a_{-k} = conj a_k`, parameter derivatives by the
Cauchy iteration on `E+t` (scalar copy of `param_cauchy`).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p11ac5 KAM.Planetary.MaximalStep.Homological`: "Build completed successfully (9089 jobs)".
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no long lines.
  (It prints "KAM.lean is out of date"; generated root, not touched.)
- No `sorry`/axiom/maxHeartbeats. `#print axioms` of all four theorems: `[propext, Classical.choice, Quot.sound]`.
- Warning only: unused hypotheses (`hn`, `hr`, `hT`, `hD`, ... in `_real`) because signatures are verbatim.

## Uncertainties / merge notes
- **`p11Affine` duplicate:** C6 (`AffineFlowBasic`, branch inp-p11ac6) also defines `p11Affine` with the same body.
  On merging both, delete one copy (suggested: drop mine in `HomologicalBracket.lean` and import `AffineFlowBasic`).
- `param_cauchy_scalar` duplicates `param_cauchy` (C3) for ℂ-valued maps (C3's is stated for `P11CVec q`); could be
  generalised in C3.
- `homological_maximal` proves a stronger fact than stated: `truncate T phi = phi` for all z (incl. b ∉ B).

## Errata / deviations
No suspected source errata. No signature changes; no statement needed extra hypotheses.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C5 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements and definitions = signature file exactly (p11Solve, p11AngleClass, p11AngleAverage, homological_maximal, homological_maximal_real, homological_maximal_param, and the bracket bridge if signed); (2) proofs sound (finite coefficients, averages and parameter derivatives; C4 consumed as designed); no added premises; (3) hygiene (no EuclideanSpace). Audit ONLY KAM/Planetary/MaximalStep/Homological.lean and HomologicalBracket.lean.
