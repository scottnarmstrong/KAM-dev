# W5-STEP-B handoff (audit scope: W5 step theorem, modified case, reality)

Package W5-STEP is audited in two runs. Run A (infrastructure) is `W5-STEP-A-handoff.md` / `W5-STEP-A-audit-1.md`
(its two findings, joint continuity in flow-calc (i) and the 𝒫^{p₊}-onto clause of flow-calc (iii), are being repaired
separately and are NOT in this run's scope). **This run (B)** covers the remaining W5 modules listed below:
new-ham, the step setup and core (`StepCore`, `WaveStepHyp`, `StepHypMod`), the step theorems
(`stepTheorem`, `stepTheoremMod` in `StepTheoremSrc`, the `*_of_eps0_pos` helpers), the modified-divisor
package (`Homological/Modified*`, `ModifiedStepSolve`) and the reality package (`Real*`).

Branch `inp-wpj` @ a7414cf7 (+ inp merged). Producer handoffs: `W5-STEP-handoff.md` (sessions 1–6 and the
W5W6-INTEGRATE part A AUDIT FOCUS at the end), `W5-MODIFIED-handoff.md`, `W5-REAL-handoff.md`.

## AUDIT FOCUS (run B)
1. **Source-facing step theorems.** `KAM.Wave.stepTheorem` and `KAM.Wave.stepTheoremMod` must state blueprint
   `bpW:w5:step` (w5-kamstep.tex, Theorem "One KAM step") clauses (i)–(v) verbatim, including reality of Φ and P₊,
   Dφ(w) onto 𝒫^{p₊}, the field-form weak conjugacy (new-ham (iii)), with only the blueprint's premises
   (step data Definition `bpW:w5:data`, smallness `bpW:w5:small`, modified case `2β ≤ p+1−p₊`). Check the ε₀
   splitting (`stepE0`, `stepE1`): the ε₀>0 forms are the distinctly named helpers `*_of_eps0_pos` and no
   ε₀>0 premise reaches the source-facing theorems. Check the hypothesis comparison recorded in the handoff
   (σ ≤ s/6 with σ>0 ⇒ 5σ<s; ε>0 from bpW:w5:data l. 336; clause (iv) of the modified theorem conditional on (H_α)
   per l. 581).
2. **W5 interface deviations reported by the W6 consumer (rule on these):** from `W6-ITER-handoff.md` (branch
   inp-wpr), quoted:
   - **D2** (W6 `prep-step` (ii)): `stepTheoremMod` (iii) bounds the normal shift with weight
     `(j+2)^{p₊−p} = J^{1/2}`, not `J` as W6's prep-step (ii) needs (blueprint: "with p̄ − p = 1"); the
     J-weighted bound needs the shift of the Taylor family at p̄ = p+1 (`StepHypMod.R1`) to equal that of the
     reweighted family used by the core, which W5 does not expose.
   - **D3** (W6 `prep-step` (iii)): clause (v) gives `|Φ_P − id|^λ ≤ 2M_{F,P}`; the blueprint's sharper sup bound
     `M_{F,P}` (step `f-flow` of `bpW:w5:flow`) is not exposed by `stepTheoremMod`.
   Decide whether each is a defect of the W5 Lean statement relative to the blueprint W5 statements (an omitted
   blueprint conclusion), or only a mismatch with what W6 later needs.
3. **Modified case** (`W5-MODIFIED-handoff.md`): `bpW:w5:w4-modified` (i)–(iii), the twisted multipliers, the
   reweighting `homReweight`, and `StepHypMod` → `StepCore`.
4. **Reality package** (`W5-REAL-handoff.md`): reality of Φ and P₊, Dφ onto 𝒫^{p₊} for the step map, the Riesz
   field X_N and the field-form weak conjugacy.
5. Definitions: carriers and totalized operations (Ring.inverse, tsum, fderiv) in source-facing objects.

Modules (run B):
- `KAM.Wave.KamStep.ModifiedStepSolve`
- `KAM.Wave.KamStep.NewHamBracket`
- `KAM.Wave.KamStep.NewHamConcrete`
- `KAM.Wave.KamStep.NewHamConj`
- `KAM.Wave.KamStep.NewHamExp`
- `KAM.Wave.KamStep.NewHamFlow`
- `KAM.Wave.KamStep.NewHamIntegral`
- `KAM.Wave.KamStep.NewHamLip`
- `KAM.Wave.KamStep.NewHamTransport`
- `KAM.Wave.KamStep.RealFlowPicard`
- `KAM.Wave.KamStep.RealNField`
- `KAM.Wave.KamStep.RealSmoothOnto`
- `KAM.Wave.KamStep.RealStep`
- `KAM.Wave.KamStep.RealTaylorFun`
- `KAM.Wave.KamStep.RealTaylorOf`
- `KAM.Wave.KamStep.RealWeakConj`
- `KAM.Wave.KamStep.StepBracket`
- `KAM.Wave.KamStep.StepClauses`
- `KAM.Wave.KamStep.StepConj`
- `KAM.Wave.KamStep.StepCore`
- `KAM.Wave.KamStep.StepCtx`
- `KAM.Wave.KamStep.StepFlowClauses`
- `KAM.Wave.KamStep.StepFlowConcrete`
- `KAM.Wave.KamStep.StepFlowFam`
- `KAM.Wave.KamStep.StepFreqBound`
- `KAM.Wave.KamStep.StepHyp`
- `KAM.Wave.KamStep.StepHypMod`
- `KAM.Wave.KamStep.StepLip`
- `KAM.Wave.KamStep.StepMargin`
- `KAM.Wave.KamStep.StepNplus`
- `KAM.Wave.KamStep.StepNuIntegral`
- `KAM.Wave.KamStep.StepPeriodicFlow`
- `KAM.Wave.KamStep.StepPeriodic`
- `KAM.Wave.KamStep.StepPlusA`
- `KAM.Wave.KamStep.StepPlusArith`
- `KAM.Wave.KamStep.StepPlusAssemble`
- `KAM.Wave.KamStep.StepPlusBound`
- `KAM.Wave.KamStep.StepPlusClass`
- `KAM.Wave.KamStep.StepPlusFam`
- `KAM.Wave.KamStep.StepPlusFinal`
- `KAM.Wave.KamStep.StepPlusLam`
- `KAM.Wave.KamStep.StepPlus`
- `KAM.Wave.KamStep.StepPullbackBound`
- `KAM.Wave.KamStep.StepReweight`
- `KAM.Wave.KamStep.StepReweightTaylor`
- `KAM.Wave.KamStep.StepSetup`
- `KAM.Wave.KamStep.StepSymplectic`
- `KAM.Wave.KamStep.StepTheorem`
- `KAM.Wave.KamStep.StepTheoremMod`
- `KAM.Wave.KamStep.StepTheoremSrc`
- `KAM.Wave.Homological.ModifiedAct`
- `KAM.Wave.Homological.ModifiedBounds`
- `KAM.Wave.Homological.ModifiedDivisors`
- `KAM.Wave.Homological.ModifiedEq`
- `KAM.Wave.Homological.ModifiedEquation`
- `KAM.Wave.Homological.ModifiedLipDeriv`
- `KAM.Wave.Homological.ModifiedLipField`
- `KAM.Wave.Homological.ModifiedLip`
- `KAM.Wave.Homological.ModifiedReal`
- `KAM.Wave.Homological.ModifiedReweight`
- `KAM.Wave.Homological.ModifiedSolve`

Names: commit ada9a34f renamed StepHyp → WaveStepHyp, stepFun → waveStepFun and made some namespaced names
protected (short-name hygiene only).
