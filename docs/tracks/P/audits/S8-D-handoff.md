# S8-D prover handoff (branch inp-s8d, aff048b; off inp; offloaded package run by the main orchestrator; prover on claude-10)


Branch inp-s8d. Files (new; ~940 lines total, none above 255):
- KAM/Planetary/SecularForm/DiagonalJet.lean (facade + assembly `pairSlowSecular_diag_jet`)
- KAM/Planetary/SecularForm/DiagonalJet/Radial.lean, Orbit.lean, Pair.lean, Mean.lean
No signed declaration touched; no premise added; no coefficient structure / quadratic matrix assumed. KAM.lean not edited
(lint reports "KAM.lean is out of date"; the orchestrator regenerates it).

## Inventory: blueprint node -> helper
- stepP:p8:qf-scale (Phi symmetric, homogeneous deg -1, = r2^-1 b_{1/2}^(0)(r1/r2), analytic off the diagonal):
  `radialPhi_comm`, `radialPhi_smul`, `radialPhi_eq_laplace` (0<a<b), `analyticOnNhd_radialPhi`
  (on {0<r1, 0<r2, r1 ≠ r2}), `analyticAt_radialH`; helper `radial_base_nonneg` (Radial.lean).
- stepP:p8:qf-c0: `pairSlowSecular_zero` : pairSlowSecular D i j I J (0,0) = -G m_i m_j * radialPhi a_i a_j
  (hyp: 0<I, 0<J, a_i ≠ a_j; a = I^2/(m^2 G m0)) (Pair.lean); `poincare_circular_fst` (circular planet on the circle of
  radius Λ²/(mκ)), `circle_average` (average of 1/|q - b e(t)| over t = radialPhi |q| b) (Orbit.lean).
- stepP:p8:qf-diag (orbit radius r = a(1 - e cos u) and dλ = (1 - e cos u) du):
  `planeLength_poincare_fst` (|q| = a * keplerJac v F, via `planeSq_orbit_vec`), `integral_keplerLong_comp`
  (change of variables λ → F over one period), `pair_inner_average`,
  `pairSlowSecular_circular_partner`: pairSlowSecular (u,0) = -G m_i m_j (2π)^-1 ∫_0^{2π} radialH a_i a_j (v·e(F)) dF
  (hyp: poincareDom membership and orbit-radius separation a(1+|v|)<b ∨ b<a(1-|v|)).
- Exact diagonal derivatives: `circleMean_jet` (Mean.lean; ⟨cos²⟩=1/2, ⟨cos⁴⟩=3/8, odd means vanish; Taylor remainder
  O(e^6)), `iteratedDeriv_two_radialH_of_lt` (a<b: h''(0) = a/b² b_{3/2}^{(1)}(a/b)) and `_of_gt` (b<a:
  h''(0) = b/a² b_{3/2}^{(1)}(b/a)) via the signed `identities` (Radial.lean), and the assembled
  `pairSlowSecular_diag_jet`: for 0<I,0<J, a_i≠a_j, ∃ r C>0, ∀ u with planeLength u < r,
  |pairSlowSecular D i j I J (u,0) - (-G m_i m_j [h(0) + h''(0)/4 (|u|²/I) + (h⁗(0)/64 - h''(0)/16)(|u|²/I)²])| ≤ C |u|^6,
  h = radialH a_i a_j. Quadratic coefficient: -G m_i m_j h''(0)/(4I) = -pairA/Λ_i in both orderings; the quartic
  coefficient matches `quartic`'s c_0 formula (iteratedDeriv 4/64 - iteratedDeriv 2/16).
  (Design note: S8-Q/S8-4 should apply this lemma to both ordered pairs; the u-jet for the partner uses the symmetric
  swap, which `pairSlowSecular` does not do automatically.)

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-s8d KAM.Planetary.SecularForm.DiagonalJet`: "Build completed successfully";
  no sorry/warnings in my files after final edits.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated file, not mine); module check, frozen guard, ABI PASS.
- #print axioms of pairSlowSecular_diag_jet, pairSlowSecular_zero, pairSlowSecular_circular_partner,
  analyticOnNhd_radialPhi, radialPhi_smul, radialPhi_comm, iteratedDeriv_two_radialH_of_lt/_gt, circleMean_jet:
  all [propext, Classical.choice, Quot.sound].
- No set_option, no EuclideanSpace, no heartbeat issues.

## Uncertainties / errata / deviations
- Separation hypothesis (orbit radii avoid the partner radius) is needed since Φ has a log singularity on the diagonal;
  it is automatic for small |u| (used in the assembly), as in the blueprint's regime.
- Errata: none found. Deviations: statements are mine (no signed S8-D declarations), as ruled.
- Not delivered (belongs to S8-Q/S8-X): the cross term, the assembly of quadratic_form, and the swap for the case
  where the *eccentric* planet is the second argument of pairSlowSecular.
- Minor: `ring` -> `ring_nf` info in Radial.lean (one place) is silenced; no linter warnings.

AUDIT FOCUS. S8-D has NO signed declarations: by the 13:08 orchestrator ruling in docs/campaign/OVERNIGHT.md (design docs/tracks/P/design/P810-LEAN-DESIGN.md rows S8-D/S8-Q, the p8 L157 note; 'DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them'), its results are INTERNAL helper lemmas, proof cuts of the signed quadratic_form (and of quartic, row S8-4). Refute-first, against the pinned blueprint-P p8 (stepP:p8:qf-scale, qf-c0, qf-diag and the exact diagonal derivatives): (1) each helper is a true identity about the LITERAL pair average with only blueprint-stated hypotheses; check each against its cited node and the inventory (node -> helper); (2) nothing assumes a coefficient structure, the quadratic matrix or a numerical ratio; no premise added to any signed declaration; no frozen file touched; (3) the statements are usable by S8-Q (quadratic_form) and S8-4 (quartic) as designed; (4) proofs sound, no sorry/axioms; (5) hygiene (no EuclideanSpace; distinct names; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/SecularForm/DiagonalJet.lean and DiagonalJet/*.lean.
