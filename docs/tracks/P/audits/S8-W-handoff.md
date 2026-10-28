# S8-W prover handoff (branch inp-s8w, 59925ec; contains inp-s8b (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all new, no existing file changed)
Facade `KAM/Planetary/SecularForm/InvariantPolynomial.lean` (imports `.../TwoVectors`), plus under
`KAM/Planetary/SecularForm/InvariantPolynomial/`: `Coordinates` (145 lines), `Balanced` (116),
`Generators` (231), `Weyl` (109), `Homogeneous` (111), `TwoVectors` (154). All well under 1500 lines.

## Declarations
- `KAM.Planetary.SecularForm.e_weyl` (bpP:p8:e-weyl): statement byte-identical to
  `P810Signatures.lean`, now fully proved (no `sorry`).
- Quadratic / quartic invariant reductions (design row has no signatures; stated by me, helper namespace
  `SecularForm.Weyl`):
  - `exists_homogeneous_dot_poly`: homogeneous invariant of degree `2k` in `n` vectors = homogeneous
    degree-`k` polynomial in the dot products (hypotheses: invariance and `r^(2k)` scaling only).
  - `quadratic_invariant` (`P.IsHomogeneous 2`, n=2): `∃ c : Fin 3 → ℝ`, `P = Σ c k * quadraticTerms (u 0) (u 1) k`,
    terms `|u|², |v|², u·v`.
  - `quartic_invariant` (`P.IsHomogeneous 4`, n=2): `∃ c : Fin 6 → ℝ`, `P = Σ c k * quarticTerms (u 0) (u 1) k`,
    with `quarticTerms` having exactly the body of the design's `quarticMonomials` (so S8-4 can state
    `quarticMonomials = Weyl.quarticTerms` by `rfl`/`simp`). I did NOT define `quarticMonomials` here, to avoid
    a name clash with S8-4.
  - Supporting: `eval_smul_of_isHomogeneous`, `toZW`, `balancedPart`, `eval_balancedPart_toZW`, `sAlg`,
    `re_im_mem_sAlg`, `mem_dAlg_of_refl`, ...

## Approach
Complexify: `z=x+iy, w=x-iy` (`toZW`, `eval_toZW`). A unit complex `t` acts as the orthogonal matrix
`rotMat t`, i.e. `(z,w) ↦ (tz, t⁻¹w)`; invariance for all `|t|=1` plus infinitely many roots of a
polynomial in `t` (`sum_unbalanced_eq_zero`) kills all monomials with unequal z/w degree at real points
(`eval_balancedPart_toZW`). Balanced monomials are products of `m_jk = z_j w_k = d_jk + i c_jk`
(`balanced_mem`); real/imaginary parts of that algebra lie in `sAlg = 𝒟 ⊕ 𝒟·c` (dot-product algebra plus odd
combinations of cross products, closed under products by Binet–Cauchy `cross_mul_cross`). The reflection
`diag(1,-1)` fixes `d` and negates `c`, which forces membership in `𝒟` (`mem_dAlg_of_refl`), and
`Algebra.adjoin_range_eq_range_aeval` extracts `Q`. Homogeneous reduction: coefficient comparison of the
polynomial `r ↦ Q(r²·dots)` against `r^(2k) P(u)`; two-vector forms by monomial enumeration.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-s8w KAM.Planetary.SecularForm.InvariantPolynomial`:
  `Build completed successfully (9058 jobs)`, no warnings from my files in the final build.
- `scripts/lint_sources.sh`: only the expected `KAM.lean is out of date` note (generated file, not
  touched); `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms` of `e_weyl`, `Weyl.quadratic_invariant`, `Weyl.quartic_invariant`,
  `Weyl.exists_homogeneous_dot_poly`: `[propext, Classical.choice, Quot.sound]`.
- No `set_option` of any kind; no heartbeat issues.

## Uncertainties / notes
- The design table lists "quadratic and six quartic invariant reduction" without signatures; my
  statements are the natural ones (hypotheses `IsHomogeneous` + O(2) invariance). If S8-Q/S8-4 need a
  different shape (e.g. function-level homogeneity, or the pair embedded in `n` vectors) tell me; the
  core `exists_homogeneous_dot_poly` is generic in `n`.
- Only imports Mathlib and frozen Defs (PlaneDot/PlaneSq); no provider, no DRAFT_SORRY anchor.
  S8-B Basic is not imported (not needed).
- Suspected errata/deviations: none. e_weyl is true as stated.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-W and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (e_weyl, the quadratic and six quartic invariant reductions); (2) proofs sound (balanced/odd decomposition, homogeneity in the dot products, two-vector reductions); no added premises; (3) hygiene (facade + six modules). Audit ONLY KAM/Planetary/SecularForm/InvariantPolynomial.lean and InvariantPolynomial/*.lean (compare with branch inp-s8b).
