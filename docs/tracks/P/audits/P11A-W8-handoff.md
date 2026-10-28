# P11A-W8 prover handoff (branch inp-p11aw8, db1a159; contains inp-p11aw7 and W0..W6 (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- KAM/Planetary/WeakMeasure/Bridge.lean (72 lines): `limit_bridge`, `limit_bridge_diophantine`.
- KAM/Planetary/WeakMeasure/PowerLaw.lean (247): `p11CDio`, `p11GammaStar` (verbatim defs), `power_law`; helpers
  `p11_modeSize_pos/ge_one`, `p11_pl_profile` (= pl-profile), `p11_pl_sum` (= pl-sum, via `KAM.Measure.lattice_sum`),
  `p11_C_nonneg`; pl-conc inlined in `power_law`.
- KAM/Planetary/WeakMeasure/ChartScaling.lean (~257): `chart_scaling`, `_geometry`, `_jets`, `_good`, `_upper`,
  `_closeness` (diagonal `true` gauge as in audit 3); helpers `p11_iteratedFDeriv_affine`, `p11_euclid_smul`,
  `p11_volume_affine`, `p11_pow_le_max`, `p11_min_le_pow`.
All signatures verbatim from P11ASignatures.lean (no change, no extra hypotheses).

## Approach
- limit_bridge: |k.(u-v)| <= |k|_1 ||u-v||_inf; triangle inequality.
- power_law: profile psi/|k|_2 <= sqrt(m) gamma |k|_1^(-tau-1) <= sqrt(m) gamma (|k|_2 >= |k|_1/sqrt m, |k|_1>=1);
  apply `diophantine_measure`; termwise bound by (sqrt m gamma)^q |k|_1^(-(tau+1)q), q=rho/mu; lattice_sum with
  tau'=(tau+1)q-1 (m-1<tau' iff tau>m mu/rho-1); constant identity matches p11CDio exactly; concentration by
  C gamma^q <= eps from gamma <= (eps/C)^(mu/rho), and measure_inter_add_sdiff (G compact => measurable).
- chart scaling: iteratedFDeriv of f(y0+lambda x) via `ContinuousLinearMap.iteratedFDerivWithin_comp_right`
  (on open sets, converted by `iteratedFDerivWithin_of_isOpen`) + `iteratedFDeriv_comp_add_left`; jets by
  attainment (`p11dg_attained`, `p11op_attained`) both directions; geometry via `diam_smul₀`, isometry of translation,
  `addHaar_preimage_smul`, `measure_preimage_add`.

## Checks
- Gate: `inp_lake_build.sh . KAM.Planetary.WeakMeasure.{PowerLaw,Bridge,ChartScaling}` -> "Build completed successfully (9061 jobs)", no sorry.
- `scripts/lint_sources.sh`: no long-line/sorry issues; PASS check_lean_modules, FROZEN-ANCHOR GUARD OK, ABI HASHES OK;
  only message: "KAM.lean is out of date" (not edited, per rules; the orchestrator regenerates).
- `#print axioms` for power_law, limit_bridge, limit_bridge_diophantine, chart_scaling, chart_scaling_geometry/jets/good/upper/closeness:
  all `[propext, Classical.choice, Quot.sound]`.

## Deviations / uncertainties
- ChartScaling imports `WeakMeasure.Stability` (W1, for `contDiffOn_p11scalar`) rather than only W0 as the design text says; no cycle
  (Stability imports W0 only). `p11_euclid_smul` re-proved locally to avoid importing Sublevel.
- No statement issues found; no heartbeat problems, no set_option used.
- Suspected errata: none.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W8 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements and definitions = design signatures exactly (limit_bridge, limit_bridge_diophantine, p11CDio, p11GammaStar, power_law, chart_scaling and its parts); (2) proofs sound (KAM.Measure.lattice_sum, modeSize_euclid_compare and W7 consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/WeakMeasure/{Bridge,PowerLaw,ChartScaling}.lean (compare with branch inp-p11aw7).
