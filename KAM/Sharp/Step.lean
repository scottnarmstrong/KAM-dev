/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Perturbation
public import KAM.Sharp.NewtonError
public import KAM.Apost.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The sharp KAM step

Blueprint `bp:p2s:step` (`KAM.Sharp.step_spec`): one quasi-Newton step `K ↦ K̄ = K + ΔK` on
`T_{r-2δ}` with general small-divisor data `(κ, c_R)`, under the split smallness
`C_step ε/(γ⁴δ^{2a}) ≤ 1` and `2d ≤ β`, where `d = C_ΔK ε/(γ²δ^a)` and `a = 2κ`:

* (a) `K̄` is holomorphic on `T_{r-2δ}`, primary and real;
* (b) `|K̄ - K| ≤ d` on `T_{r-2δ}`, with the ball margin `β - d`;
* (c) the new error is `≤ C_E ε²/(γ⁴δ^{2a}) ≤ ε`;
* (d) the frame and twist increments on `T_{r-3δ}` are `≤ rate · ε/(γ²δ^{a+1})`, with the rates
  `rateD`, `rateB`, `rateT`.

The proof follows the blueprint:

* `step:p2s:st-small`: `KAM.Sharp.step_small` turns the two smallness conditions into the
  hypotheses of the lemmas below;
* `step:p2s:st-err`: `KAM.Sharp.correction_bounds` and `KAM.Sharp.newton_error_bounds` (the
  qualitative clauses are the first conjunct of `KAM.Apost.correction_spec`, step (a) the helpers
  of `KAM.Apost.Step`);
* `step:p2s:st-pert`: `KAM.Sharp.perturbation_poly` with `K̃ = K̄`, `ω̃ = ω`,
  `ε̃ = C_E ε²/(γ⁴δ^{2a})`,
  and `twistD ≤ C_DT ε/(γ²δ^{a+1})` (`KAM.Sharp.StepSharp.twistD_le_cDT`, through
  `KAM.Sharp.absorb`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}
variable {τ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

namespace StepSharp

/-- `c (C ε/(γ²δ^{2κ}))/δ = c C ε/(γ²δ^{2κ+1})`. -/
theorem div_delta_eq {c C γ δ ε : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    c * (C * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ = c * C * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  have hs : 0 < δ ^ (2 * κ) := Real.rpow_pos_of_pos hδ _
  rw [Real.rpow_add_one hδ.ne']
  field_simp

/-- Step `step:p2s:st-pert`: the twist increment `twistD` at `d = C_ΔK ε/(γ²δ^{2κ})` is at most
`C_DT ε/(γ²δ^{2κ+1})` (absorption of `ε/δ` and `ε/(γδ^{κ+1})`). -/
theorem twistD_le_cDT {γ δ ε : ℝ} (hκ : 1 ≤ κ) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    twistD n κ cR M σK σB γ ε δ (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤
      cDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  obtain ⟨-, ⟨-, a2b, a2c, -⟩, -, -⟩ := absorb hκ hγ hγb hδ hδ1 hε
  have c1 : 0 ≤ (1 + vthh ^ 3) * cT1 n σK σB := by unfold cT1; rw [vthh_eq]; positivity
  have c2 : 0 ≤ (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK := by
    unfold wT cOm; rw [vthh_eq]; positivity
  have t1 : (1 + vthh ^ 3) * cT1 n σK σB * ε / δ ≤
      (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) :=
    calc (1 + vthh ^ 3) * cT1 n σK σB * ε / δ = (1 + vthh ^ 3) * cT1 n σK σB * (ε / δ) :=
          mul_div_assoc _ _ _
      _ ≤ (1 + vthh ^ 3) * cT1 n σK σB * (γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) :=
          mul_le_mul_of_nonneg_left a2b c1
      _ = _ := by ring
  have t2 : (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) ≤
      (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb *
        (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) :=
    calc (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) =
          (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * (ε / (γ * δ ^ (κ + 1))) :=
          mul_div_assoc _ _ _
      _ ≤ (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK *
            (γb * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) :=
          mul_le_mul_of_nonneg_left a2c c2
      _ = _ := by ring
  have t0 : (cDab n M σK σB + cDc n M σK σB) *
      (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ =
      (cDab n M σK σB + cDc n M σK σB) * cDK n cR M σK σB σT γb *
        (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
    rw [div_delta_eq hγ hδ, mul_div_assoc]
  calc twistD n κ cR M σK σB γ ε δ (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) =
        (cDab n M σK σB + cDc n M σK σB) *
          (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ +
        (1 + vthh ^ 3) * cT1 n σK σB * ε / δ +
        (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) := rfl
    _ ≤ (cDab n M σK σB + cDc n M σK σB) * cDK n cR M σK σB σT γb *
          (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) +
        (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) +
        (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb *
          (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
      rw [t0]; exact add_le_add (add_le_add le_rfl t1) t2
    _ = cDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by unfold cDT; ring

end StepSharp

/-- Blueprint `bp:p2s:step`: one sharp quasi-Newton step, with `K̄ = newtonMap h K ω (r - 2δ)`,
`d = C_ΔK ε/(γ²δ^a)` and `a = 2κ`. -/
theorem step_spec (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hγb : γ ≤ γb)
    {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : Admissible σK σB σT 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h3δ : 3 * δ < r)
    (hsmall : cStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1)
    (hβ : 2 * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤ β) :
    (DifferentiableOn ℂ (newtonMap h K ω (r - 2 * δ)) (complexStrip n (r - 2 * δ)) ∧
      IsPrimaryOnStrip (newtonMap h K ω (r - 2 * δ)) (r - 2 * δ) ∧
      IsRealOnReals (newtonMap h K ω (r - 2 * δ))) ∧
    ((∀ θ ∈ complexStrip n (r - 2 * δ), ‖newtonMap h K ω (r - 2 * δ) θ - K θ‖ ≤
        cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ∧
      ∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (newtonMap h K ω (r - 2 * δ) θ)
        (β - cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ⊆ 𝔅) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ‖ ≤
      cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ ε ∧
    (∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        rateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ∧
      IsUnit (gramMatrix (newtonMap h K ω (r - 2 * δ)) θ).det ∧
      ‖(gramMatrix (newtonMap h K ω (r - 2 * δ)) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤
        rateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    IsUnit (torsionAverage h (newtonMap h K ω (r - 2 * δ)) ω).det ∧
    ‖(torsionAverage h (newtonMap h K ω (r - 2 * δ)) ω)⁻¹ - (torsionAverage h K ω)⁻¹‖ ≤
      rateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  have hγ := hS.gamma_pos
  have hr := hK.r_pos
  have hβ0 := hK.β_pos
  have hε0 := hK.ε_nonneg
  have hσT := hS.σT_pos
  have h2δ : 2 * δ < r := by linarith
  have hr2 : 0 < r - 2 * δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  -- step `st-small`
  obtain ⟨hεδ, hTS, hsym, hs1, hs2, hs3, hE⟩ := step_small hC.one_le_kappa hC.cR_pos hS.M_pos
    hS.σK_pos hS.σB_pos hσT hγ hγb hδ hδ1 hε0 hsmall
  have hdβ : cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < β := by linarith
  -- step `st-err`
  obtain ⟨⟨-, -, -, hcd, hcp, hcr⟩, -⟩ := correction_spec hS hK hδ hδ1 h2δ
  have hbd := (correction_bounds hC hS hγb hK hδ hδ1 h2δ hεδ hTS).2.2.2
  have hnewt := (newton_error_bounds hC hS hγb hK hδ hδ1 h2δ hεδ hTS hdβ hsym).2.2.2
  have hdiff : DifferentiableOn ℂ (newtonMap h K ω (r - 2 * δ)) (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Step.newtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖newtonMap h K ω (r - 2 * δ) θ - K θ‖ ≤
      cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := fun θ hθ => by
    rw [NewtonError.newtonMap_of_mem hθ, add_sub_cancel_left]
    exact (hbd θ hθ).2.2.1
  -- step `st-pert`
  obtain ⟨hball, hfr, -, -, htw⟩ := perturbation_poly hC hS
    (CorrectionSharp.admissible_noTwist hK) hδ hδ1 h3δ hεδ hdiff hdist hdβ hnewt hE hs1 hs2
  have htD := StepSharp.twistD_le_cDT (n := n) (σT := σT) hC.one_le_kappa hC.cR_pos hS.M_pos
    hS.σK_pos hS.σB_pos hγ hγb hδ hδ1 hε0
  obtain ⟨hTu, -, hTd⟩ := htw hK.twist.1 hK.twist.2
    ((mul_le_mul_of_nonneg_left htD hσT.le).trans hs3)
  refine ⟨⟨hdiff, KAM.Apost.Step.newtonMap_isPrimaryOnStrip (by linarith) hK.primary hcp,
      KAM.Apost.Step.newtonMap_isRealOnReals hr2 hK.real hcr⟩, ⟨hdist, hball⟩, hnewt, hE,
    fun θ hθ => ?_, hTu, ?_⟩
  · obtain ⟨h1, -, h3, -, h5⟩ := hfr θ hθ
    exact ⟨h1.trans_eq (StepSharp.div_delta_eq hγ hδ), h3,
      h5.trans_eq (StepSharp.div_delta_eq hγ hδ)⟩
  · have hv : 0 ≤ vthh * σT ^ 2 := by rw [vthh_eq]; positivity
    calc _ ≤ vthh * σT ^ 2 *
          twistD n κ cR M σK σB γ ε δ (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) := hTd
      _ ≤ vthh * σT ^ 2 * (cDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) :=
          mul_le_mul_of_nonneg_left htD hv
      _ = rateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by unfold rateT; ring

end KAM.Sharp

end
