# P23-13i prover handoff (branch inp-p23r13i base inp-design-p23r3 (P23-13 partial + design rev 3); cdb8f64; offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-p2313i`. File (new): `KAM/Planetary/Averaging/OscillatorReality.lean` (337 lines). No other file touched
(KAM.lean not edited; orchestrator must rerun `scripts/gen_root_imports.py`).

## Declarations
- `osc_generator_real`, `osc_iter_reality`: statements copied VERBATIM from `P23Signatures.lean` (Appendix A.3);
  `osc_iter_reality` carries `set_option linter.unusedVariables false in` (as `osc_iter_core` does), no semantic change.
- Helpers (distinct names, no conclusion-shaped premises): `oscRealFlat`, `oscPack_real`, `oscRealUnpack`, `oscUnpack_real`
  (real append/unpack bridge), `freq_real` (real frequency by differentiating the real restriction), `h_real_of_realOn`,
  `osc_real_local` (homological_param conclusion 10 on a flat parameter ball, D={x0}, incl. zero mode).

## Approach
Real phase point x ↦ `oscPack (ι₂ x) = (ι θ, ι (oscRealFlat x))`; local ball ⊆ oscParams; `homological_param` conclusion 10
(Λ={0}) with `RealOnParam` of `oscFunction f` (from hrf via `oscUnpack_real`) and real `oscFreq` (from hrh: take real
phase (0, (I,0)), differentiate along real directions). Zero mode = `homResParam` = `modeAverage` on Dom (conclusion 6).
`osc_iter_reality`: φ real (generator), gp = g + zero mode real, `OscFlowHyp.real_flow` for Ψ, and fp on V real because
V ⊆ U, Ψ(real) = real ∈ O ⊆ oscDom, then hrh/hrg/hrf/gp at both points. Reality of the SUM g only is used.

## Checks
- Gate build `inp_lake_build.sh … KAM.Planetary.Averaging.OscillatorReality`: `Build completed successfully (9119 jobs)`; no warnings.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" notice; `check_lean_modules: PASS (529 Lean files…)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms osc_generator_real` / `osc_iter_reality`: `[propext, Classical.choice, Quot.sound]`.
- No maxHeartbeats, no sorry/axiom, default heartbeats throughout; file ≪ 1500 lines.

## Uncertainties / errata / deviations
None. No source defects found. Used `hwidths` of `osc_iter_reality` only through `osc_flowHyp`; `hn`, `hm`, `hg`, `hδ` partly unused (linter silenced).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md section 'Revision 3 (oscillator Lie-series transfer)', row P23-13i and Appendix A.3; design audit docs/tracks/P/design/P23-design-audit-1.md; signatures .drafts/design/P23Signatures.lean): (1) statements = Appendix A.3 signatures exactly (osc_generator_real, osc_iter_reality); (2) proofs sound (real append/unpack bridge, real freq, homological_param conclusion used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/Averaging/OscillatorReality*.lean (compare with branch inp-design-p23r3).
