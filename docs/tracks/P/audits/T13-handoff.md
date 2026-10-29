# T13 prover handoff (branch inp-p11c-t13, a73d2767; offloaded package run by the main orchestrator)


## Files
- New: `KAM/Planetary/PlanarTorsion/Beta.lean` (~300 lines). Imports Frame (for the existing
  `p11c_rotateSlow`, `p11c_Q_analyticAt`, `p11c_sigma0_analyticAt`, `p11c_axes_isOpen`), Quartic, Characters.
  No provider / DRAFT_SORRY imports. KAM.lean not edited (it is now out of date: the orchestrator must
  run scripts/gen_root_imports.py; this is the only lint complaint).

## Signed declarations (verbatim from P11CSignatures.lean)
- `beta_def`, `p11c_beta` (defs), `beta_formula` (bpP:p11b:beta-formula, with steps bf-gram, bf-avg),
  `beta_properties` (bpP:p11b:beta-def: entrywise analytic on `p11c_axes` + `IsSymm` for every a).
- `p11c_rotateSlow` was already in Frame.lean (T14), so it is imported, not redefined.

## Approach
- bf-gram: `p11c_quartic_rotateSlow_gram`: rotated quartic = `p11cBetaGram c γ s r0 r1 G`, a polynomial in
  r_j=|z_j|² and G=z₁·z₂ (pure ring identity). `p11cBetaGram_quad`: it is quadratic in G.
- bf-avg: `p11c_average_eq_boxIntegral` (average = ((2π)²)⁻¹ ∫ over box), `p11c_boxIntegral_prod` (product
  box lemma), `p11cGramRot_integral` (⟨G⟩=0), `p11cGramRot_sq_integral` (∫G² = 2π² r₁r₂), from one-variable
  integrals; `p11c_rotation_sq` (r_j invariant). Final identity is `ring` (checked beforehand in sympy).
- beta_properties: `p11c_projector_analyticAt` (σ₁ = trace − σ₀, σ₀−σ₁ ≠ 0) + coeffs analytic from
  `quartic_explicit`; symmetry `beta_def_isSymm` holds for every projector.
- New public helpers (names grepped unused in KAM before): beta_def_isSymm, p11c_projector_analyticAt,
  p11c_boxIntegral_prod, p11c_boxIntegrableOn, p11c_average_eq_boxIntegral, p11cBetaGram,
  p11c_quartic_rotateSlow_gram, p11cBetaGram_quad, p11cGramRot, p11c_rotation_sq,
  p11cGramRot_continuous, p11cGramRot_integral, p11cGramRot_sq_integral.

## Checks
- `inp_lake_build.sh <wt> KAM.Planetary.PlanarTorsion.Beta`: "Build completed successfully (9249 jobs)",
  only warning: unused variable `h` in `beta_formula`.
- `#print axioms beta_formula` / `beta_properties`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: all checks pass except "KAM.lean is out of date" (new module; generated file).
- No set_option, no sorry; lines ≤ 100.

## Uncertainties / deviations / errata
- Statement note: `beta_formula`'s hypothesis `g²+s²=1` is NOT needed (the identity is polynomial, because
  the π-entries are g², gs, s²); signature kept verbatim, hence the unused-variable warning. Not an erratum.
- No suspected source errata. No deviations from signatures. No heartbeat/design signals.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T13 (beta_def/formula/properties, Gram averages g, g^2; T6/T7/T12) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. T13 was built on T6 round 1; T6's fix round (qe-c12 diagonal consistency) is append-only: note whether T13 needs it. Quartic* is T6 (own audit). Audit ONLY KAM/Planetary/PlanarTorsion/Beta*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
