# S8-Q prover handoff (branch inp-s8q, 7a82787a; contains inp-s8d and inp-s8x (audited internal helpers); offloaded package run by the main orchestrator; prover on claude-10)


## Files (all new; nothing existing edited)
`KAM/Planetary/SecularForm/Quadratic.lean` (facade + the signed `quadratic_form`, statement copied
verbatim from `P810Signatures.lean`, checked by string comparison) and `Quadratic/`:
`Marginal` (96), `PairSplit` (124), `PairIdentify` (80), `PairLocal` (226), `Calculus` (124),
`PairDiag` (165), `PairHessian` (223), `Algebra` (115), `Coeff` (110), `Jet` (177), `Schwarz` (180),
`Uniform` (257), `Constants` (82). Total about 2030 lines (design estimate 300; the proof is
genuinely long: Fubini marginal, pair identification, Hessian from symmetries, order-four Schwarz).
No file near the 1500 cap; largest is 257.

## Approach (nothing assumed; no quadratic matrix, no numerical ratio)
* `qf-pair`: `avg_pair_marginal` (independence of the coordinates of the normalised product measure)
  gives `secular_eq_sum_pair`: `S = Σ_{i<j} secular (pairData D i j) false (pairSlow x i j)`, and
  `secular_pair_eq` identifies each term with the literal `pairSlowSecular`. Exchange of the planets:
  `pairSlowSecular_swap`. Near `(u,v)=0`, `pairSlowSecular` is the 2-planet `secular` (via
  `perturbation_analytic` for `pairData`), hence analytic and invariant under the reflection
  `η→-η` and the quarter turn (`evenness`, S8-Y).
* diagonal/cross values: `pair_diag_first/second` (from S8-D `pairSlowSecular_diag_jet` and the
  exchange; second derivative along rays `s↦(su,0)`, `(0,sv)` is `-2 pairA/Λ |u|²`),
  `cross_hessian` (S8-X) for the mixed derivative `2 coeffs i j`. `hessian_pair_form` (generic,
  by hand from the two symmetries; S8-W's `quadratic_invariant` is NOT needed) gives
  `pair_second_derivative`. `pair_value_zero` gives the constant `C₀`.
* `qf-assembly`: `quad_pair_sum` (index algebra) turns the sum of pair second derivatives into
  `2(ξᵀQξ+ηᵀQη)`. `Jet`: along `s ↦ (sξ,Λ,sη)` the remainder `rayRemainder` is analytic with
  vanishing derivatives of order 0..3 at 0 (order 1,3 by `evenness`).
* uniform bound: order-four Schwarz lemma (`schwarz_order_four`, copied from the order-five version of
  `PGAssembly/Remainder` with the exponent lowered) on the complex line, with the holomorphic extension
  by `secularC` (bounded on a closed smaller polydisc), real/complex derivative bridge
  (`iteratedDeriv_ofReal`, `iteratedDeriv_ofReal_comp`), constants of `Constants`.
* `qf-diag2` is not a separate analytic fact: the statement is exactly `ξᵀQξ+ηᵀQη` and the
  diagonalisation `ρ^T` is S9-Q's matrix-level consumption; nothing added for it.

## Checks (all through the gate, LEAN_NUM_THREADS=1)
* `inp_lake_build.sh /root/code/KAM-inp-s8q KAM.Planetary.SecularForm.Quadratic`: "Build completed
  successfully (9169 jobs)"; no warning in the new files; no `sorry`/axiom/`maxHeartbeats`/
  `EuclideanSpace` in the new files (grep).
* `sh scripts/lint_sources.sh`: no long lines; `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK`. It prints "KAM.lean is out of date; run scripts/gen_root_imports.py": expected,
  I did not edit KAM.lean (generated; the orchestrator regenerates it to add the 14 new modules).
* `#print axioms` of `quadratic_form`, `quad_pair_sum`, `pair_second_derivative`,
  `secular_eq_sum_pair`: `[propext, Classical.choice, Quot.sound]`.
* New public names are unique (checked by grep against all of KAM; three initially clashing short
  names were renamed: `quadPairA_comm`, `quad_sum_erase_split`, `quadRemainder`).

## Uncertainties / notes
* Imports used: `Momentum`, `Symmetry`, `Analytic`, `AnalyticGeometry`, `Coefficients`,
  `DiagonalJet`, `CrossJet`, `CrossJet/Parametric` (public `integral_cell_two`); no provider, no
  DRAFT_SORRY anchor, no frozen theorem (frozen Defs only through existing modules).
* `schwarz_*_four` duplicates the shape of `schwarz_order_five` (different exponent); if the
  orchestrator prefers, a general-order lemma could replace both later.
* Statement unchanged; no extra hypothesis was needed.

## Suspected errata / deviations
* None new. (The p8 remark that the cited derivation is not pinned stays as in the ledger; the
  derivation here is the complete replacement.) Deviation from the design text: S8-W's
  `quadratic_invariant`/`quartic_invariant` are not used by this package (the quadratic invariants of
  two planar vectors are derived directly in `hessian_pair_form` from the reflection and quarter-turn
  symmetries); S8-W stays available for S8-4.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md rows S8-Q, S8-D, S8-X, the p8 L157 note and 'DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them'; the 13:08 ruling in docs/campaign/OVERNIGHT.md on main; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean). This package proves the SIGNED quadratic_form. Refute-first: (1) quadratic_form = signature file EXACTLY (string identity), and the S8-Q slice (qf-pair, qf-assembly, qf-diag2) is complete; (2) the proof assembles the literal pair-average identities from S8-D (pairSlowSecular_diag_jet etc.) and S8-X (cross_hessian) by summing, and never assumes the quadratic matrix, a coefficient structure, or a numerical ratio (p8 L157); the uniform remainder and order-four Schwarz bounds are proved, not assumed; (3) the deviation (S8-W invariants not used; quadratic invariants derived directly from reflection and quarter-turn symmetries in hessian_pair_form) is sound and loses nothing; (4) no sorry/axioms beyond standard; kernel replay; (5) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/SecularForm/Quadratic.lean and Quadratic/*.lean.
