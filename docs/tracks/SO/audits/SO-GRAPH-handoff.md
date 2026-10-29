# Handoff SO-GRAPH (branch inp-sograph)

## Files
- NEW `KAM/SpinOrbit/Graph/Cert.lean` (255 lines): `SoGraphCert`, `checkSoGraph` (signed), helpers
  `soGraphMonoModel`, `soGraphActionModel`, `norm_fst_apply_sub_le`, `norm_snd_apply_sub_le`,
  `realPt_one_zero`, `soGraph_deriv_transfer`, `checkSoGraph_sound`, `soGraph_exactTorus`, and the signed
  `soBarrier_of_cert`, `soRotBarrier_of_cert`.
- NEW `KAM/SpinOrbit/Tests/GraphCert.lean` (92 lines): `decide +kernel` tests.
- Signed statements reproduced verbatim from SOSignaturesLunar.lean §I.5 (no premise added or changed).
  No landed file edited. `SoGraphCert`/`checkSoGraph` live in `KAM.Certificate`, the theorems in
  `KAM.SpinOrbit` (same namespaces as the rest of the SO code).

## checkSoGraph (kernel-reducible, `Bool`)
`decide (disp < mono · ρ∞)` &&
`checkRealLowerBound weight cfgLow (soGraphMonoModel g) mono₀ mono sosMono` &&
`checkRealLowerBound weight cfgLow (soGraphActionModel g) pLo₀ pLo sosLo` &&
`checkRealLowerBound weight cfgLow (soGraphActionModel g).negM (-pHi₀) (-pHi) sosHi`.
- `soGraphMonoModel g = toDeg 0 (modelMatrixEntry (dkModels 2 emb weight piEnc) 0 0)` (the DK entry
  `∂_{θ₀} K_{.1 0}`, enclosed by the landed `dkModels_encloses`).
- `soGraphActionModel g = toDeg 0 (realCompModel 2 (actionDeg.getD 0 0) action[0]?)` (`K_{.2 0}`,
  `realCompModel_encloses`).
- SOS residual is PAID through landed `KAM/Certificate/Positivity.lean` (`checkRealLowerBound_sound`).

## Route
1. `checkSoGraph_sound` (weight/π validity from `checkStatic_sound`): on reals, `Re ∂_{θ₀}K_{.1 0} ≥ mono`,
   `Re K_{.2 0} ∈ [pLo, pHi]`, and `disp < mono ρ∞`.
2. `checkTorusCertificate_sound` → `CertifiedTorus`: `K∞` holomorphic on the OPEN strip `T_{ρ∞}`,
   `‖K∞ - K‖ ≤ disp` there. The displacement is given on exactly the strip needed (no gap).
3. `soGraph_deriv_transfer` (Cauchy, `norm_coordinate_fderiv_le_of_mem_complexStrip` with every
   `δ < ρ∞`, then a limit argument since the strip is open): `|Δ Re ∂_{θ₀}| · ρ∞ ≤ disp`. Values move by
   ≤ disp (component norm ≤ product max norm).
4. `soGraph_exactTorus`: m = mono - disp/ρ∞ > 0, band `[pLo - disp, pHi + disp]`, Diophantine for
   `s∞ ω*` with `γ' = s∞ γ` (landed `isDiophantine_smul_scale`, `s∞ > 1`).
5. Rotated: `c.H = (soRotHamExprScaled c).eval` by `hham`, then landed `soBarrier_of_exact_rotTorus`.
   Original: `c.H = soHC` (`soHamExpr_eval`), then landed `soBarrier_of_exact_torus`.
   (`torusCoeff_fderiv_real`/`eq_zero_of_torusCoeff_eq_zero` were not needed.)

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-sograph KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert`:
  `Build completed successfully (3325 jobs)`, no warnings in the new files.
- Tests (all `decide +kernel`): `graphTest_pass` (mono 4/5, range [97/100, 103/100], disp 1/1000,
  ρ∞ 1/200); fail-closed `graphTest_mono_fail` (mono 99/100), `graphTest_range_fail` (pLo 999/1000;
  pHi 1001/1000), `graphTest_margin_fail` (disp 1/200 ≥ mono ρ∞ = 1/250).
- `main_shortname_check.py ... KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert`: OK (rc 0).
- Lines ≤ 100 columns; no native_decide/ofReduceBool/sorry/macro/elab/run_cmd/implemented_by/extern.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; exit 1 only
  because "KAM.lean is out of date" (the two new modules); KAM.lean is generated and not editable by me
  (rule 10) — orchestrator regenerates at landing, as in the earlier "Regenerate KAM.lean (SO-…)" commits.

## Axioms
- `KAM.SpinOrbit.soRotBarrier_of_cert`: [propext, Classical.choice, Quot.sound]
- `KAM.SpinOrbit.soBarrier_of_cert`: [propext, Classical.choice, Quot.sound]

## Numerical conditions the lunar data must meet (for SO-DATA)
- Strict Cauchy margin: `disp < mono · ρ∞`; with `ρ∞ = 1/70000`: `mono > 70000 · disp`.
- Monotonicity: `supBound(model of (f + f*) - 2 g g* - 2 mono₀) ≤ 2 (mono₀ - mono)` with `f` the degree-0
  model of `∂_{θ₀}K_{.1 0}` (DK entry (0,0)), `g = sosMono` (product key `[7]`, cfgLow advice).
- Range: same with `f = K_{.2 0}` model, centre `pLo₀`, bound `pLo`; and with `-K_{.2 0}`, centre `-pHi₀`,
  bound `-pHi`.
- Resulting barrier band: `[pLo - disp, pHi + disp]` (must sit inside the O1 window for the final theorems).
- All three SOS checks run on `base.weight` (strip ρ) and `base.cfgLow`.

## Uncertainties / design signals
- None at default heartbeats; every file well under 1500 lines.
- `checkSoGraph` uses `cfgLow` (not `cfgFull`) for the SOS products; SO-DATA must register any advice
  there. If the owner prefers `cfgFull`, it is a one-token change in the definition body.

## Errata / deviations
- No suspected errata in pinned sources. No deviation from the signed statements.

AUDIT FOCUS: (1) SoGraphCert, checkSoGraph, soBarrier_of_cert, soRotBarrier_of_cert byte-identical to /root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean §I.5 (lines 390-468); the landed SoGraph.torus_of_rot and soBarrier_of_exact_rotTorus are used, not restated; (2) checkSoGraph's body: it bounds exactly ∂_{θ₀} of component (.1 0) (the DK entry (0,0)) from below and component (.2 0) above and below on the REAL torus, with the SOS residual paid through checkRealLowerBound_sound, and the strict margin disp < mono·ρ∞; confirm the models enclose those exact quantities (dkModels_encloses, realCompModel_encloses) and that every getD/default read is harmless; (3) the Cauchy transfer soGraph_deriv_transfer: the displacement from CertifiedTorus holds on the open strip T_{ρ∞}, every δ < ρ∞ is used and the limit argument is sound, so |Δ Re ∂_{θ₀}| ≤ disp/ρ∞ on the reals; values move by ≤ disp in the right norm; (4) soGraph_exactTorus: m = mono − disp/ρ∞ > 0, band [pLo − disp, pHi + disp], the Diophantine premise for s∞ω* from isDiophantine_smul_scale with s∞ > 1 (constant direction: γ' = s∞γ ≥ γ?), and that the conclusions match the hypotheses of soBarrier_of_exact_rotTorus exactly (frame: hham, c.H = (soRotHamExprScaled c).eval); (5) the original-frame route through soBarrier_of_exact_torus; (6) tests positive and fail-closed; (7) no conclusion-shaped hypotheses, kernel replay, axioms. Suspected design or source defects go in the report as errata candidates.
