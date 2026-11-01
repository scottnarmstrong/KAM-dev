/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorRv
public import KAM.Wave.KamStep.StepFlowConcrete
public import KAM.Wave.KamStep.Class
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The derivative of `R` is `ϖ(X_R, ·)` in the sense of Gateaux (blueprint-W `bpW:w5:taylor`,
`t-scale`, `t-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

* `stepSymp_scale`: `ϖ(X, S_t W') = ϖ(T_t X, W')` (step `t-scale`);
* `sympK`: `ϖ` as a continuous bilinear map on `KamPhase`;
* `sum_taylorCoeff_symp`: for a smoothing pair `(P, X)` on `D(s,r)`, the sum of the Taylor
  coefficients of `t ↦ DP(S_t w)(S_t W')` is `ϖ(X_R(w), W')`, `X_R = taylorXR X`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

instance factRealZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- `ϖ` as a continuous bilinear map on `KamPhase`. -/
def sympK {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') : KamPhase →L[ℂ] KamPhase →L[ℂ] ℂ :=
  (((stepSympCLM (q := q) (q' := q') ha hqq' 1).comp (stepOfKCLM 1)).flip.comp (stepOfKCLM 1)).flip

theorem sympK_apply {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (x W : KamPhase) :
    sympK (q := q) (q' := q') ha hqq' x W = stepSymp ha hqq' x W := rfl

/-- **Scaling identity** (`bpW:w5:taylor` step `t-scale`): `ϖ(X, S_t W') = ϖ(T_t X, W')`. -/
theorem stepSymp_scale {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (t : ℂ) (X W : KamPhase) :
    stepSymp ha hqq' X (scaleS t W) = stepSymp ha hqq' (scaleT t X) W := by
  unfold stepSymp scaleS scaleT
  simp only [map_smul, smul_apply, smul_eq_mul, Pi.smul_apply]
  have e1 : ∑ i, X.1 i * (t ^ 2 * W.2.1 i) = t ^ 2 * ∑ i, X.1 i * W.2.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, t ^ 2 * X.1 i * W.2.1 i = t ^ 2 * ∑ i, X.1 i * W.2.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]

theorem taylorCoeff_clm {g : ℂ → KamPhase} (L : KamPhase →L[ℂ] ℂ) (hg : ContDiffAt ℂ ⊤ g 0)
    (k : ℕ) :
    taylorCoeff (fun t => L (g t)) k = L (((k.factorial : ℂ)⁻¹) • iteratedDeriv k g 0) := by
  unfold taylorCoeff
  rw [map_smul]
  congr 1
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have := L.iteratedFDeriv_comp_left hg (i := k) (by exact_mod_cast le_top)
  have h2 := congrArg (fun m => m (fun _ : Fin k => (1 : ℂ))) this
  simpa using h2 |> fun h => (show (fun t => L (g t)) = ⇑L ∘ g from rfl) ▸ h

/-- **`DR = ϖ(X_R, ·)` in the Gateaux sense**: for a smoothing pair `(P, X)` on `D(s,r)`,
`∑_{k ≤ 2} (t^k-coefficient of t ↦ DP(S_t w)(S_t W')) = ϖ(X_R(w), W')`. -/
theorem sum_taylorCoeff_symp {a p pb s r : ℝ} (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) {P : KamPhase → ℂ}
    {X : KamPhase → KamPhase} (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X) (hr : 0 < r)
    {w : KamPhase} (hw : w ∈ kamDomain s r) (W : KamPhase) :
    ∑ k ∈ Finset.range 3, taylorCoeff (fun t : ℂ => fderiv ℂ P (scaleS t w) (scaleS t W)) k =
      stepSymp (q := pb) (q' := p) ha hqq (taylorXR X w) W := by
  set L : KamPhase →L[ℂ] ℂ := (sympK (q := pb) (q' := p) ha hqq).flip W with hL
  have hcd := contDiffAt_taylorG (r' := r) hP.holoX hr (by rw [div_self hr.ne']; exact one_pos) hw
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  have hk : ∀ k, taylorCoeff (fun t : ℂ => fderiv ℂ P (scaleS t w) (scaleS t W)) k =
      L (taylorField X w k) := by
    intro k
    have hcongr : (fun t : ℂ => fderiv ℂ P (scaleS t w) (scaleS t W)) =ᶠ[𝓝 0]
        fun t : ℂ => L (taylorG X w t) := by
      filter_upwards [hev] with t ht
      have htn : ‖t‖ * r < r := by
        rw [mem_ball_zero_iff] at ht
        nlinarith
      have hmem := scaleS_mem hr htn hw
      rw [hP.deriv_eq _ hmem, hL]
      simp only [ContinuousLinearMap.flip_apply, sympK_apply, taylorG]
      rw [stepSymp_scale]
    rw [taylorCoeff_congr_eventually hcongr, taylorCoeff_clm L hcd]
    rfl
  simp only [hk]
  unfold taylorXR
  rw [← sympK_apply (q := pb) (q' := p) ha hqq, map_sum, ContinuousLinearMap.sum_apply]
  rfl

end KAM.Wave
