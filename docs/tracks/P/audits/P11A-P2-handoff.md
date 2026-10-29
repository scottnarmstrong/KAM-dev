# P11A-P2 prover handoff (branch inp-p11ap2, ca049e2c; contains P11A-P1; offloaded package run by the main orchestrator)


Hard rules observed: no `set_option maxHeartbeats` (or any override), all files far below 1500 lines,
no sorry/axiom/admit/unsafe/opaque, no `EuclideanSpace`, no frozen/manifest/KAM.lean/README edits,
no provider import, lines <= 100.

## Status in one paragraph
Proved and building: the period-one polar chart and `total_chart` (nodes `bpP:p11:total-chart`,
`tc-polar`, `tc-lat`), the signature defs of the holomorphic secular package, and the `hc-rot`
building blocks (complex extension of the rotation, complex orthogonality, compactness bounds
`B_rho`, `B'_rho`). NOT proved: `holo_chart` (and its local steps hc-lift, hc-strip, hc-F, hc-id,
hc-lat, hc-mean in full; only hc-rot is done) and `total_chart_transport` (it needs the `chart`
field of `p11SecularData D := (holo_chart D).choose`, so it cannot be proved before `holo_chart`).
The package is far larger than the planned ~750 lines: the honest estimate for the missing part is
several thousand lines (see "What remains"). No signature was changed; nothing is stated with an
extra hypothesis; no statement looked false.

## Files (all new)
* `KAM/Planetary/Preparation/Holomorphic.lean` (~135 lines): verbatim signature defs
  `p11WorkingDom`, `P11SecularData`, `p11ChartInput`, `p11WorkingH`, `p11FastMean`,
  `P11SecularSpec`, `P11SecularFullSpec` (lines only re-wrapped to <= 100 columns, text unchanged).
  `holo_chart` and `p11SecularData` are NOT in the file (no sorry allowed). Imports
  `HolomorphicRotation`.
* `KAM/Planetary/Preparation/HolomorphicRotation.lean` (~160 lines), step `stepP:p11:hc-rot`:
  - `p11_rotation_complex`: a real analytic matrix family `R` (entrywise `AnalyticOnNhd` on a real
    ball) with `R^T R = 1` has a holomorphic entrywise extension `rho` on a complex max-norm ball of
    radius `t2 <= t1`, equal to `R` on real points, and `(rho z)^T rho z = 1` on the complex ball
    (via `p11_complexification` + `p11_real_slice_identity`).
  - `p11_rotation_bounds`: on a smaller closed ball, constants `B, B' >= 1` bounding
    `sum_j |rho i j|` and `sum_j |(rho^T d_l rho) i j|` (compactness; this is the exact shape of the
    `Brho`/`Bdrho` clauses of `P11SecularSpec`). Uses `open scoped Matrix.Norms.Elementwise in` for
    the proof only.
* `KAM/Planetary/Preparation/Polar.lean` (~270 lines): verbatim `p11PolarC`, `p11PolarR`;
  `total_chart` (all four conjuncts); public helpers `p11PolarScaleL`, `p11PolarScale` (the linear
  period conversion (zeta,rho) -> (2 pi zeta, rho/2pi) on the slow block) and `p11PolarR_eq`
  (`p11PolarR z = polarMap (p11PolarScale z)` for positive slow momenta) — the identity
  "tc-polar: the real chart is the Part 7 `polarMap` after the canonical period conversion".
  Private helpers: translation of fast actions (`polarMap_add_trans`, `exists_trans`,
  `polarMap_analyticAt`, `fderiv_polarMap_eq`, `polarMap_symplectic_pos`) so that the existing
  `polarDom`-restricted `analyticOnNhd_polarMap`, `polarMap_symplectic`, `polarMap_shift`,
  `polarMap_eq_shift` apply on the whole set `{rho_i > 0}`; `p11PolarScale_symplectic`.

## Node -> declaration
| node | declaration |
|---|---|
| `bpP:p11:total-chart` | `total_chart` (Polar) |
| `stepP:p11:tc-polar` | `p11PolarR_eq` + `polarMap` analytic/symplectic lemmas inside `total_chart` |
| `stepP:p11:tc-lat` | periodicity and injectivity conjuncts of `total_chart` (`polarMap_shift`, `polarMap_eq_shift` after the common translation) |
| `stepP:p11:hc-rot` (partial) | `p11_rotation_complex`, `p11_rotation_bounds` (HolomorphicRotation); the choice of the real rotation `R` itself (P9 `local_analytic`/`diagonalize` at a Diophantine `J0`, P10 simple spectrum from the patch spec) is NOT yet written |
| `bpP:p11:holo-chart`, `hc-lift`, `hc-strip`, `hc-F`, `hc-id`, `hc-lat`, `hc-mean` | not proved |
| `total_chart_transport` | not proved (blocked on `holo_chart`) |

## Checks run (all on branch inp-p11ap2, one process at a time)
* Gate builds: `inp_lake_build.sh /root/code/KAM-inp-p11ap2 KAM.Planetary.Preparation.HolomorphicRotation
  KAM.Planetary.Preparation.Holomorphic KAM.Planetary.Preparation.Polar` -> "Build completed successfully".
  (Final rebuild after the line re-wrapping of Holomorphic.lean: see the last line of this file.)
* `#print axioms` of `total_chart`, `p11PolarR_eq`, `p11_rotation_complex`, `p11_rotation_bounds`:
  all `[propext, Classical.choice, Quot.sound]`.
* `scripts/lint_sources.sh`: the only remaining message is "KAM.lean is out of date; run
  scripts/gen_root_imports.py" (new modules; KAM.lean is generated and was not edited — the
  orchestrator must regenerate it); `check_lean_modules: PASS`.

## What remains for holo_chart (map of existing results, in dependency order)
1. Choose the data (hc-rot, rest): `select` (BasePoint) gives `gamma, J0`; patch spec
   (`p11PatchData_spec`) gives `V` open, `sigma` strictly increasing with
   `charpoly (p11SecularMatrix D (J/2pi)) = prod (X - sigma_i)`. `p11SecularMatrix_eq`
   (PatchHessian) ties it to `SecularForm.coeffs`; then `SecularSpectrum.local_analytic`
   (needs `Function.Injective eigenvalues` at `J0/2pi`, from StrictMono) gives analytic `sigma, R`
   with `isSO`. Feed `R` (entries) to `p11_rotation_complex`; shrink `t2`; `rC <= min(pi t2/2,
   pi delta/8)`; bounds from `p11_rotation_bounds`. Complexify `sigma` entrywise
   (`p11_complexification`) for `Omega`; `h`, `omega` are explicit rational functions of `J`
   (clauses 2, 5, 6 of the spec); `L` by compactness (iteratedFDeriv continuity on the closed ball)
   including the Euclid bound of `P11SecularFullSpec`. Note: `fderiv`/`DifferentiableOn` on
   `Matrix`-valued maps need only the TVS structure in this Mathlib, but `ContDiffOn`,
   `AnalyticOnNhd` need a norm: use entries (`contDiffOn_pi`, `analyticOnNhd_of_differentiableOn`
   from `KAM.Strip.AnalyticTaylor`; `DifferentiableOn.analyticOnNhd` is ONE-variable only).
2. hc-lift: real lift `SecularSpectrum.lift`/`liftInv` and its formula
   `rotDiag_liftInv_assemble` (Diagonalize.lean) equal `p11ChartInput` on real points
   (need `fderiv ℂ rho (ri L) = (fderiv ℝ R L).map ofReal`); bounds `|rho x| <= B |x|`,
   `|H_rho| <= n B' |y||x|` are elementary.
3. hc-strip/hc-F (largest): complex-angle extension of `fFix`: `Poincare/Holomorphic`
   `poincare_holomorphic` + `SecularForm.separationC` (currently real angle `t` only:
   `perturbation_analytic` fixes real angles) -> need a uniform `Re s_ij >= (a_j-a_i)^2/4` on a
   strip of width `sigma'` by compactness of `[0,2pi]^n x closedball` and 2pi-periodicity; then
   `F := f_hat o Phi_rho^{-1} o T1` holomorphic with the sup bound `MF/coth(pi sigma)^n`,
   periodic (angle shift commutes), real on reals.
4. hc-id/hc-lat: `chart := poincareProd o liftInv R o T1` (T1 is the linear map
   `(2 pi theta, J/2pi)` on the fast block; same pattern as `p11PolarScale`): analytic/symplectic
   from `lift`, `analyticOnNhd_poincareProd`, `IsSymplecticOn.comp`; lattice from
   `liftMap_add_append`, `liftInv_injOn`, `poincareProd_lattice`, `poincareProd_eq_iff`
   (compare the private `rotated_shift`/`rotated_inj` in `SecularSpectrum/Transport.lean`);
   membership in `poincareProdDom` and `collisionFreeDomain` needs the quantitative smallness
   `rz <= rho_*/(8 B_rho)`, `rC <= pi delta/8` (`forward_tube`, `p11PhysicalDelta`); the energy
   identity `fixedHamiltonian = Re(h + eps F)` from `SecularForm.product_chart`/`lattice`,
   `Newtonian.Models` (`fFix`, `fMov`) and `hol_chart` (Hamiltonian/HolChart).
5. hc-mean: `F_0` holomorphic by `Weighted.holomorphic_parametric_integral`; real values from
   `SecularSpectrum.diagonalize` (b),(d) with `SecularForm.evenness/evenness_taylor/same_jets`;
   real jets vanish to order 3 -> complex jets (identity theorem in `z`), then
   `p11_radial_schwarz` (P0) gives `MF (|z|/rz)^4` after enlarging `MF`.
6. `total_chart_transport`: once `holo_chart` is in, the proof is `total_chart` composed with the
   chart clauses (analytic: comp; symplectic: `IsSymplecticOn.comp`; shifts: `hshift` + chart
   lattice clause + `polarMap`-lattice; injectivity: chart lattice clause then `total_chart`'s).
   NOTE (to check when proving): the signature's `hshift` is over `k : Fin (n+n) -> ℤ` acting on
   ALL angles `z.1`, but the `p11PolarR` lattice of `total_chart` and the chart's lattice shift only
   the slow (resp. fast) block each; the fast shift is the chart's period-one lattice
   (`Fin.append k 0`), the slow one `p11PolarR`'s (`Fin.append 0 k`); both appear, consistent.

## Uncertainties / suspected errata / deviations
* No errata found and no deviation from the signatures (only line re-wrapping of the verbatim
  declarations in Holomorphic.lean to satisfy the 100-column lint; the printed text is unchanged
  modulo whitespace).
* Estimate: the planned size (~750 lines) for P11A-P2 is far too low for `holo_chart` as signed
  (the 30-clause `P11SecularSpec` bundles the whole P7/P8/P9/P10 -> complex-strip bridge,
  steps hc-strip/hc-F/hc-mean in particular). Suggest splitting it into sub-packages
  (hc-rot data, hc-strip/F, hc-id/lat chart, hc-mean) each with its own module.

Final rebuild after re-wrapping: Build completed successfully (Holomorphic, Polar); lint: only 'KAM.lean is out of date' (expected, generated file), all other guards OK.

ORCHESTRATOR RULING (OVERNIGHT 20:40): P11A-P2 is SPLIT. This audit covers ONLY what P2 delivered: Preparation/Polar.lean (p11PolarC, p11PolarR, total_chart with all four conjuncts, p11PolarScale/L, p11PolarR_eq; nodes bpP:p11:total-chart, tc-polar, tc-lat), Preparation/HolomorphicRotation.lean (the hc-rot building blocks p11_rotation_complex, p11_rotation_bounds), and the verbatim signature definitions in Preparation/Holomorphic.lean (p11WorkingDom, P11SecularData, p11ChartInput, p11WorkingH, p11FastMean, P11SecularSpec, P11SecularFullSpec). holo_chart, its steps hc-lift..hc-mean and total_chart_transport are assigned to the split packages P2b..P2f and are NOT findings here.

AUDIT FOCUS: (a) every delivered SIGNED declaration = signature file /root/code/KAM-inp/.drafts/design/P11ASignatures.lean EXACTLY (definitions only line-wrapped); definitions mean the source objects on their whole carriers; (b) total_chart and the tc-polar/tc-lat nodes established; the hc-rot blocks correct and shaped for P2b; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Planetary/Preparation/{Holomorphic,HolomorphicRotation,Polar}.lean.
