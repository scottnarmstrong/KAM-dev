# P23-13 prover handoff (branch inp-p2313, 71f22ef; base inp-p2311; offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-p2313` (worktree /root/code/KAM-inp-p2313). No `sorry`, no axiom, no maxHeartbeats, all files < 1500 lines.
`scripts/lint_sources.sh`: PASS (only the generic "KAM.lean is out of date" notice; I did not touch KAM.lean).
Gate build of all six modules: succeeded (output: `Build completed successfully`).
`#print axioms` of `osc_iter_core`, `osc_fp_class`, `oscGen_class_bound`, `oscZero_class_bound`: `[propext, Classical.choice, Quot.sound]`.

## What is proved (files, all under KAM/Planetary/Averaging/)
- `OscillatorGen.lean` (≈210 l): `oscGen` (verbatim); `oscFunction_oscGen` (flat transport = `homGenParam K {0} (oscFreq)`);
  `osc_hom_local` (upstream `homological_param` applied at each flat parameter on a ball, D={x});
  `oscGen_class_bound` (oscClass φ ∧ oscBound φ (δ/(2πα))); `oscZero` + `oscZero_class_bound` (zero mode: class and bound δ);
  `oscClass_of_flat`, `wbound_congr_flat`.
- `OscillatorFlow.lean`: anisotropic gauge `oscScale` with `‖oscScale z‖ = oscGauge …` (`norm_oscScale`); `mem_oscDom_iff`;
  `oscDom_of_gauge_le` (gauge balls).
- `OscillatorFlowMap.lean`: `fastShift`, `oscDom_add_shift`, `oscDom_shift_image`, `oscClass.periodic_int`, `oscClass.field_periodic`.
- `OscillatorFlowProps.lean`: structure `OscFlowHyp` and, via `flow_a…flow_e`/`symplectic` at W=oscScale, Ω=𝒪: `smallField`, `half` (U ⊆ gaugeInterior 1/2),
  `one` (V ⊆ gaugeInterior 1), `diff_flow`, `mapsTo_flow`, `injOn_flow`, `inverse_flow`, `lattice_flow`, `gauge_disp`, `gauge_fderiv`,
  `symplectic_flow`, `real_flow`, `field_components`, `disp_components` (the four exact block displacements δ/(2παρ), δ/(e(2πα)σ), δ/(2παρp), δ/(2παρq)).
- `OscillatorClassAlgebra.lean`: `oscClass.add/sub/sum/congr`, `oscBound.congr`.
- `OscillatorStep.lean`: `oscStepMap` (verbatim); `osc_flowHyp`; **`osc_iter_core`** = the signature's `osc_iter` (same hypotheses, same `let`s) with every clause
  EXCEPT {oscClass fp, oscBound fp, and the conditional reality clause}: i.e. φ class/norm, DifferentiableOn Ψ U, MapsTo Ψ U O, InjOn Ψ V, fast-lattice law on U,
  inverse flow on V, oscClass gp, oscBound (gp-g) δ, Hamiltonian identity on V, gauge displacement on U, gauge derivative bound on V, symplecticity on U, four block displacements on U;
  **`osc_fp_class`** = holomorphy + fast periodicity of fp on V (the `oscClass` part of the fp clause, stated on the explicit expression of fp).

## What is NOT proved (the gap; needs a follow-up package)
1. `oscBound D (r-2ρ) … fp ((1-2e(1+m)δ/(2παd))⁻¹ (2(1+m)/(2παd)(Rsum+δ) + exp(-2πKσ)) δ)` — the **oscillator Lie-series transfer**. fp = Lie remainder + (f − T_K f)∘Ψ.
   Everything in N's `Canonical/{Adjoint,CompositionCoeff,CompositionSeries,CompositionIntegral*,Composition,Transform*}` and `NormalForm/IterativeRemainder` is typed with
   parameter dimension = angle dimension (`(Fin n → ℂ) × (Fin n → ℂ)`), so it cannot be instantiated for the flat parameter `Fin (n+(m+m))`; the generic parts needed
   (coeff_add/const_mul, wbound_add/const_mul/congr/tsum, adjoint induction with `osc_bracket`, lieTerm/lieSeries, `series_eq` via `taylor_lie` (generic in W,Ω: reusable on CPhase (n+m)),
   `composition_integral`, `transform`, truncation tail, integrand) must be re-done for `oscClass/oscBound`. Estimated 1800–2500 lines in ~8 modules, not the 700 lines of the design table.
   Constants worked out: one bracket step on the `h`-fold loss (ρ/h,ρp/h,ρq/h,σ/h) costs ≤ c_m h²Φ/(d(h+1+i)), c_m = 2(1/e+m), d=min(ρσ,ρpρq) (each ratio ρ_h/(r'-r+iρ_h+ρ_h) ≤ 1/(h+1+i));
   after Stirling the series ratio is q = e(1+e m)Φ/(2d), which is ≤ the signature's η=2e(1+m)δ/(2παd) (since (1+em)/2 ≤ 2(1+m)), so the signature constants are attainable
   with room to spare; q<1 follows from δ ≤ 2παd/(16(1+m)).
2. Conditional reality clause (`RealOn φ ∧ RealOn gp ∧ RealOn V fp ∧ Ψ real`): `OscFlowHyp.real_flow` gives the last conjunct from `RealOn φ`; still missing: reality of φ and of the zero mode
   (apply `homological_param` conclusion 10 on the ball D={x}, needs the transport of `RealOn (oscDom …)` to `RealOnParam` via `oscUnpack ∘ realInclusion` and
   reality of `freq h` at real actions from `RealOn (h ∘ firstBlock ∘ snd)`), reality of gp (from g real + zero mode), and of fp on V (Ψ real + RealOn h,g,f).
3. Final assembly `osc_iter` = `osc_iter_core` + the three items above (no further design change needed).

## Design notes / uncertainties / errata
- No statement looked false; signature unchanged (oscGen, oscStepMap verbatim). `osc_iter_core`/`osc_fp_class`/`OscFlowHyp` are helper names (distinct from `osc_iter`; no conclusion-shaped hypotheses).
- `OscFlowHyp` includes the premise `0 ≤ E`; for `osc_iter` it is supplied by `hδpos`.
- No heartbeat problems occurred anywhere (all default heartbeats).
- Deviation: file split (6 modules) instead of the single ≈700-line `OscillatorStep.lean`; `OscillatorStep.lean` is the facade holding the declared nodes `oscStepMap`, `osc_iter_core`.
- No errata in pinned sources found.
- `OscillatorStep.lean` is not yet in KAM.lean (generated; orchestrator to rerun `scripts/gen_root_imports.py`).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-13 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (oscGen, oscStepMap, the full osc_iter clauses of Revision 2: domains U/O/V, lattice/inverse/gauge, class/norm, conditional reality); consumes P23-11 and P23-05 as designed; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY Averaging/OscillatorStep*.lean (compare with branch inp-p2311).
