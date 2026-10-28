# S8-X prover handoff (branch inp-s8x, 0a5d9f1; off inp; offloaded package run by the main orchestrator; prover on claude-10)


Branch `inp-s8x`. Work only under the orchestrator ruling (S8-X has no signed declarations; its
statements are internal proof cuts of `quadratic_form`). No signed declaration, premise, frozen file or
`KAM.lean` was touched. No `sorry`, `axiom`, `maxHeartbeats` or `EuclideanSpace`. The longest file has
326 lines.

## Files (all new)
- `KAM/Planetary/SecularForm/CrossJet.lean`: facade and the final consumable `cross_hessian`.
- `KAM/Planetary/SecularForm/CrossJet/Variation.lean`: first orbit variation in `ξ`.
- `KAM/Planetary/SecularForm/CrossJet/Parametric.lean`: generic two-angle `e_diff` slice lemma and `integral_cell_two`.
- `KAM/Planetary/SecularForm/CrossJet/PairIntegrand.lean`: pair integrand on the `(λ₁,λ₂,ξ₁,ξ₂)` slice, open domain, analyticity.
- `KAM/Planetary/SecularForm/CrossJet/MixedKernel.lean`: the mixed Hessian of `-c/|α(s)-β(t)|` (`crossKernel`).
- `KAM/Planetary/SecularForm/CrossJet/PairAverage.lean`: differentiation of the literal `pairSlowSecular` under the double average.
- `KAM/Planetary/SecularForm/CrossJet/Selection.lean`: Fourier selection (torus change of variables, periodic IBP, Laplace coefficient).

## Inventory: blueprint node → helper
| Blueprint node | Lean helper |
|---|---|
| `stepP:p8:qf-cross`, first orbit variation (`bpP:p7:regular-kepler` (a): `∂_vF = (sin F, -cos F)`, `r'=-a cos λ`, `θ'=2 sin λ`, times `1/√Λ`) | `hasDerivAt_keplerLong_line`, `hasDerivAt_lineC`, `poincare_line_fst`, `hasDerivAt_poincare_fst_xi`: `∂_ξ q = (a/√Λ)(-1-sin²λ, sin λ cos λ)`, `a = Λ²/(m²κ)` |
| `stepP:p8:qf-cross`, "`B_ij` is determined by `⟨∂ξi∂ξj V⟩`" via `bpP:p8:e-diff` | `e_diff_slice`, `iteratedFDeriv_slice` (apply `e_diff`, k=2, to the two-angle cell), `integral_cell_two`, `pairIntegrand`, `pairDom`, `isOpen_pairDom`, `contDiffOn_pairIntegrand`, `slice_mem_pairDom`, `pairSlowSecular_mixed_jet` |
| Mixed derivative `U_{r_i r_j}r_i'r_j' - …`, done in Cartesian form | `crossKernel`, `hasDerivAt_pair_t`, `hasDerivAt_pair_s`, `iteratedFDeriv_two_mixed`: `∂s∂t(-c/|α-β|) = c(3(d·α')(d·β')/|d|⁵ - α'·β'/|d|³)` |
| Fourier selection (`⟨cos λi cos λj cos kϑ⟩ = δ_k1/4`, only `B_1` survives) | `torus_reduce` (`t = s-ϑ`), `crossU_diag`, `quad_integral`, `avg_cross_diag`: the `s`-average leaves a function of `ϑ` alone. No Laplace series is used. |
| Euler relation + identity (I2) giving `b_{3/2}^{(2)}` | Replaced by `fbar_eq` (exact pointwise identity) + `ibp_selection` (one periodic integration by parts) + `inv_cube_sep2`/`integral_cos_two_inv_cube`; result `cross_double_average`: `⟨⟨crossU⟩⟩ = laplace_def (3/2) 2 (a/b) / (2 b³)` |
| Statement `B_ij = 2𝔟_ij/√(Λ_iΛ_j)` | `cross_hessian`: `iteratedFDeriv ℝ 2 (y ↦ pairSlowSecular D i j Λ_i Λ_j (![y 0,0],![y 1,0])) 0 ![e₀,e₁] = 2 * coeffs D a i j` (for `a ∈ axes n`, `i<j`; `Λ = action D a`) |

## Interface for S8-Q (`quadratic_form`)
`cross_hessian` is the only result S8-Q needs from this package. It says the mixed `ξ_iξ_j` second
derivative of the literal pair average at 0 is `2 * coeffs D a i j`, which is the coefficient of
`ξ_iξ_j` in `quad (coeffs …) ξ`. It is recomputed from the orbit map; `coeffs` is never assumed. The
hypotheses are only `a ∈ axes n` and `i<j`. The `(η_i,η_j)` and the `ξη` blocks are not computed here:
S8-Q gets them from the O(2) invariance (S8-W `e_weyl`/rotation invariance, `Symmetry`), so the quadratic
part is `A|u_i|²+A'|u_j|²+B u_i·u_j`. If S8-Q prefers `η` variations, `hasDerivAt_poincare_fst_xi` has the
`ξ` analogue only.

## Approach notes
- Differentiation under the integral reuses the project's own `e_diff` (S8-P) at `n=d=2`, `k=2`. It runs
  through the tube lemma `IsCompact.exists_thickening_subset_open` around `cell 2 × {0}` and the
  slice formula `iteratedFDeriv_slice` (`iteratedFDerivWithin_comp_right` plus translation).
- The pair integrand is smooth only off collisions (domain `pairDom`); the hypothesis is `a_i<a_j`
  (`I²/(m_i²κ) < J²/(m_j²κ)`), as in the blueprint (inner `i`).
- Numerics (not part of the proof) confirm `⟨⟨crossKernel 1 …⟩⟩ = (α/2) b/…` to 1e-15 for α = 0.3, 0.5, 0.7.

## Checks run
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-s8x KAM.Planetary.SecularForm.CrossJet`: succeeded (9128 jobs), no warnings from my files.
- `#print axioms` for `cross_hessian`, `cross_double_average`, `pairSlowSecular_mixed_jet`,
  `hasDerivAt_poincare_fst_xi`, `e_diff_slice`: only `propext`, `Classical.choice`, `Quot.sound`.
- `sh scripts/lint_sources.sh`: all checks PASS (module check 690 files, frozen-anchor guard, ABI hashes), except
  `KAM.lean is out of date; run scripts/gen_root_imports.py`. That is expected: the new modules
  `SecularForm/CrossJet*` are not yet in the generated root file, which I may not edit. The orchestrator regenerates it at landing.
- Hard-rule grep: no `sorry`/`axiom`/`maxHeartbeats`/`EuclideanSpace` in `CrossJet*`.

## Uncertainties / design signals
- No heartbeat problems; nothing was split for performance (file lengths ≤ 326).
- `crossKernel`, `cvec`, `uvec`, `sep2`, `crossU` are new global names in `KAM.Planetary.SecularForm`. Rename at landing if they clash.

## Suspected errata / deviations
- No defect found in `stepP:p8:qf-cross`: the printed first variations (`r_i'=-a_i cos λ_i`, `θ_i'=2 sin λ_i`), the value `B_ij = 2𝔟_ij/√(Λ_iΛ_j)`
  and the normalisation (`b_{3/2}^{(2)}` in the `(2π)⁻¹∫` convention of `laplace_def`) agree with the Lean computation.
- Deviation: the intermediate steps "Euler relation `r_i∂_iB_1+r_j∂_jB_1=-B_1`" and identity (I2) are not used; the Fourier selection is done by direct
  integration with one periodic integration by parts, which gives the same closed form. Not an erratum.

AUDIT FOCUS. S8-X has NO signed declarations: by the 13:08 orchestrator ruling in docs/campaign/OVERNIGHT.md (design docs/tracks/P/design/P810-LEAN-DESIGN.md rows S8-X/S8-Q, the p8 L157 note and 'DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them'), its results are INTERNAL helper lemmas, proof cuts of the signed quadratic_form. Refute-first, against the pinned blueprint-P p8 (stepP:p8:qf-cross and neighbours): (1) each helper is a true identity about the LITERAL pair average, with only hypotheses the blueprint states; check each one against its cited blueprint node and the inventory (node -> helper); (2) nothing assumes a coefficient structure, the quadratic matrix, or a numerical ratio (the p8 L157 warning); no premise is added to any signed declaration and no frozen file is touched; (3) the statements are usable by S8-Q's quadratic_form proof as the design intends (orbit variations, Fourier selection, cross Hessian); (4) proofs sound, no sorry/axioms; (5) hygiene (no EuclideanSpace; distinct names; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/SecularForm/CrossJet.lean and CrossJet/*.lean.
