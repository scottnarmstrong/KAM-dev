# SO-MODEL prover handoff (branch inp-somodel, 1b08d8b1; off inp; track SO package run by the main orchestrator)


## Files (all new, unfrozen, none edited elsewhere)
- `KAM/SpinOrbit/Model.lean` (269 lines), `PeriodOne.lean` (147), `Hamiltonian.lean` (225),
  `ScalarEmbedding.lean` (317). All are Lean modules; no `sorry`, no axioms, no heartbeat options.
- Imports of existing KAM (read-only): `KAM.Frozen.Defs.{HamiltonianVectorField,HamiltonianVectorFieldC,
  FrequencyMap,InvarianceError,IsPrimaryOnStrip,ComplexStrip}`, `KAM.Frozen.Iso.Defs.BorderedHessian`,
  `KAM.Strip.Analytic` (only `analyticOnNhd_of_differentiableOn`). No theorem anchor/provider imported.
- Name collisions: all declarations use the `so*` prefix in `KAM.SpinOrbit`; grepped KAM before: none.

## Declarations
**Model**: `soEccQ/soEpsQ` (ℚ), `soEcc = 549/10000`, `soEps = 69/200000` (+ `_eq_ratCast`), `soCoeffPoly e m`
(the table A_1..A_7, 0 elsewhere; any field), `soA`, `soAQ` (`soA_eq_ratCast`), `soModes`, `soV`, `soVC`
(entire extension), `soVq/soVφ`, `soVqC/soVφC`; `soVC_ofReal` (real on reals), `soV_add_int`,
`soV_periodic_q/φ`, `soVC_add_int`, `soVC_periodic_q/φ`, `soVC_differentiable`, `soVC_differentiable_pi`,
`soVC_analyticOnNhd_q`, `soV_differentiable`, `hasDerivAt_soV_comp`, `hasDerivAt_soVC_comp`,
`hasDerivAt_soV_q/φ`, `hasDerivAt_soVC_q/φ`, `soField` (via `deriv`), `soField_eq` (explicit
ṗ = −4πε Σ A_m sin), `IsSoSolution`, `isSoSolution_iff`.
**PeriodOne**: `soVrad`, `soVradx`, `soV_eq_soVrad`, `soVq_eq_two_pi_mul_soVradx` (the force scaling 2π),
`hasDerivAt_soVrad_x`, `IsSoRadSolution`, `soToRad`, `soFromRad`, both round trips, `isSoRadSolution_soToRad`,
`isSoSolution_soFromRad`, `isSoRadSolution_iff` (x=2πq, y=p, f=2πφ, s=2πt, both directions).
**Hamiltonian**: `soHR`, `soHC`, `soH0`, `soHC_ofReal`, `fderiv_soHR_apply`, `fderiv_soHC_apply`,
`soExtField`, `soExtFieldC`, `hamiltonianVectorField_soHR`, `hamiltonianVectorFieldℂ_soHC` (X_𝓗 = autonomous
extension (p,1),(−∂_qV,−∂_φV) in frozen `(θ,I)=((q,φ),(p,J))` convention), `soExtFieldC_ofReal`,
`soBordered`, `det_soBordered` (= −1), `det_soHessian0` (=0), `soBorderEquiv`, `frequencyMap_soH0`,
`borderedHessian_soH0` (frozen `KAM.Iso.borderedHessian soH0 I` = reindexed `soBordered (I 0)`),
`det_borderedHessian_soH0` (= −1), helper `hasDerivAt_line`.
**ScalarEmbedding** (general `u : (Fin 2 → ℂ) → ℂ`, pointwise hypothesis `ContDiffAt ℂ 2 u θ`; holds on an open
set U for holomorphic u via `contDiffAt_of_differentiableOn`): `soDir`, `soOmega`, `soDnu`, `soP`, `soJ`, `soK`,
`soResidual`; `differentiableAt_soK`, `soDnu_q` (D_ν q = p), `soDnu_φ` (D_ν φ = 1), `soHC_soK` (𝓗∘K = 0, all θ),
`fderiv_soK_dir`, `invarianceError_soK` (E = ((0,0),(−r, p r)) for the frozen `invarianceError soHC (soK ν u)
(soOmega ν)`), `norm_error_form_le`, `norm_invarianceError_soK_le` (‖E‖ ≤ max(1,‖p‖)‖r‖ pointwise),
`norm_invarianceError_soK_le_strip` (sup form over any set S, e.g. `complexStrip 2 ρ`), `soK_primary`
(ℤ²-periodic u ⇒ `IsPrimaryOnStrip`), π-free: `soUofW` (u = w(2π·)/2π), `soRW` (R(w) = D_ν²w + 2ε Σ A_m
sin(2w + 2x₁ − m x₂)), `soDnu_soUofW`, `soDnu_soDnu_soUofW`, `soResidual_soUofW`: r(θ) = 2π·R(w)(2πθ).

## Approach
Directional derivatives via the line trick (`hasDerivAt_line`) so every derivative is a one-variable
`HasDerivAt` computed by explicit chain rule; `hasDerivAt_soV(C)_comp` handles the seven-term sum once.

## Checks
- Gate build: `inp_lake_build.sh .../KAM-inp-somodel KAM.SpinOrbit.{Model,PeriodOne,Hamiltonian,ScalarEmbedding}`
  → "Build completed successfully (2874 jobs)", no warnings, no sorry (final run after last edit).
- `scripts/lint_sources.sh`: line-length, forbidden-token, module, frozen-anchor and ABI checks PASS;
  its only complaint is "KAM.lean is out of date" (expected: KAM.lean is generated and I must not edit it;
  the orchestrator must run `scripts/gen_root_imports.py` on landing).
- `#print axioms` (scratch file, all main results): `[propext, Classical.choice, Quot.sound]` for
  soVC_differentiable, soVC_add_int, soField_eq, hasDerivAt_soVC_comp, isSoRadSolution_iff,
  hamiltonianVectorField_soHR, hamiltonianVectorFieldℂ_soHC, det_soBordered, det_borderedHessian_soH0,
  invarianceError_soK, soHC_soK, soDnu_q, soDnu_φ, norm_invarianceError_soK_le(_strip), soK_primary,
  soResidual_soUofW.

## Uncertainties / notes
- "Strip norm ‖·‖_ρ" is expressed as the pointwise bound over `complexStrip 2 ρ` (as `IG1Body` does); I found no
  named strip-norm def in KAM.
- The π-free statement is for u := soUofW w (w the phase-variable function); the D_ν in `soRW` is w.r.t. the
  phase variable x = 2πθ and so carries no π; π enters only via the lattice phases being absorbed into x.
- `soV_differentiable`/analyticity: only per-variable `AnalyticOnNhd` is stated (Mathlib's
  `Differentiable.analyticAt` is one-variable); two-variable entireness is `Differentiable ℂ`.
- No reality statement for `soK` (IsRealOnReals) was requested; not proved.
- No errata found in pinned sources. Deviation: none (the table, constants, V and the §5.2 identities are as in the proposal).

Orchestrator note: helper hasDerivAt_line renamed soHasDerivAt_line (short-name clash with KAM/Nekhoroshev/Averaging/Slab.lean).

CONTEXT: track SO (owner decision D30; plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md), the lunar spin-orbit certificate project. Unfrozen helper code; no graph and no signature file exist yet for track SO, so (a) and (b) are judged against the brief /root/code/KAM-inp/.drafts/briefs/offload-main/SO-MODEL.md and proposal §2, §5 (/root/code/KAM/docs/explorations/lunar-spin-orbit-certificate-proposal.md).

AUDIT FOCUS: (1) Model: the seven coefficient polynomials equal the proposal's table §2.3 EXACTLY (check every coefficient), e = 549/10000, eps = 69/200000, V = -eps sum A_m(e) cos(2pi(2q - m phi)), the physical field qdot = p, pdot = -dV/dq, phidot = 1; (2) PeriodOne: the radian-convention equivalence with the correct force scaling (no missing 2pi); (3) Hamiltonian: H = J + p^2/2 + V in the frozen conventions (KAM/Frozen/Defs/HamiltonianVectorField*.lean, InvarianceError, BorderedHessian): its vector field is the autonomous extension, det of the bordered matrix = -1; (4) ScalarEmbedding: the identities D_nu q = p, D_nu phi = 1, H o K = 0, the invariance error E = ((0,0),(-r, p r)) for the frozen invarianceError, the norm bound, IsPrimaryOnStrip for periodic u, and the pi-free form r = 2pi R(w)(2pi theta) with R written explicitly; check that the pointwise hypothesis ContDiffAt C 2 u theta is the only regularity premise and is legitimate; (5) note (not a failure unless the brief required it): soK's reality on reals is not proved. Audit KAM/SpinOrbit/Model.lean, PeriodOne.lean, Hamiltonian.lean and ScalarEmbedding.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
