/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.NewErr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Option L10: the self-consistent tangential error (step `step:p2s2:selfcons`)

* `norm_invarianceError_le_eta_pt`: the recovery of `E` from `η` (`bp:p2s2:recovery`,
  SHARP2-B2's `norm_invarianceError_le_eta`) at one point.
* `omegaKb_le`: `Ω_K̄ = Dφᵀ (Ω_K̃ ∘ φ) Dφ` (`norm_lagrangeMat_comp_le`), so
  `|Ω_K̄| ≤ (1 + n ϑ_ξ)² C_Ω Q̃_N g X²` on `T_{r-3δ}`.
* `etaLb_self`: with the L10 conditions, recovery for `K̄` on `T_{r-3δ}` gives
  `|η̄ᴸ| ≤ (Q'_L + ϑ_N (C^N_E/C^L_E) Q̄_N g)/(1 - ϑ_N) μ X`.
* `etaLb_le`: `|η̄ᴸ| ≤ Q_L μ²/(γ δ^{κ+1})` (the crude bound, and with `selfcons` the minimum).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

namespace ModStepB

/-- `bp:p2s2:recovery` at one point (the proof of `norm_invarianceError_le_eta` is pointwise). -/
theorem norm_invarianceError_le_eta_pt {σK σN q εL εN : ℝ} {ω : Fin n → ℝ}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} (hq : q < 1) (hL : ‖tangentMat K θ‖ ≤ σK) (hN : ‖normalMat K θ‖ ≤ σN)
    (hG : IsUnit (gramMatrix K θ).det) (hΩK : ‖lagrangeMat K θ‖ ≤ q)
    (hΩN : ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ q)
    (hηL : ‖etaL h K ω θ‖ ≤ εL) (hηN : ‖etaN h K ω θ‖ ≤ εN) :
    ‖invarianceError h K ω θ‖ ≤
      (σK + σN * q) / (1 - q ^ 2) * εL + (σN + σK * q) / (1 - q ^ 2) * εN := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hΩK
  have hσK : 0 ≤ σK := (norm_nonneg _).trans hL
  have hσN : 0 ≤ σN := (norm_nonneg _).trans hN
  have hεL : 0 ≤ εL := (norm_nonneg _).trans hηL
  have hεN : 0 ≤ εN := (norm_nonneg _).trans hηN
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  obtain ⟨x, y, hxy⟩ := frame_surj hG hq hΩK hΩN (sumVec n (invarianceError h K ω θ))
  obtain ⟨p1, p2⟩ := frame_proj hG x y
  rw [hxy] at p1 p2
  have hN' : etaN h K ω θ = lagrangeMat K θ *ᵥ x - y := p1
  have hL' : etaL h K ω θ =
      -(x + ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y) := by
    rw [etaL, p2]
  have e1 : ‖y‖ ≤ q * ‖x‖ + εN := by
    have : y = lagrangeMat K θ *ᵥ x - etaN h K ω θ := by rw [hN']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hηN)
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right hΩK (norm_nonneg _))
  have e2 : ‖x‖ ≤ εL + q * ‖y‖ := by
    have : x = -etaL h K ω θ - ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ y := by
      rw [hL']; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]; exact hηL
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right hΩN (norm_nonneg _))
  have hx : ‖x‖ ≤ (εL + q * εN) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hy : ‖y‖ ≤ (εN + q * εL) / (1 - q ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hE : ‖invarianceError h K ω θ‖ ≤ σK * ‖x‖ + σN * ‖y‖ := by
    rw [← norm_sumVec, ← hxy, frameMat, Matrix.fromCols_mulVec_sumElim]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  calc _ ≤ σK * ‖x‖ + σN * ‖y‖ := hE
    _ ≤ σK * ((εL + q * εN) / (1 - q ^ 2)) + σN * ((εN + q * εL) / (1 - q ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hx hσK) (mul_le_mul_of_nonneg_left hy hσN)
    _ = _ := by field_simp; ring

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `|Ω_K̄| ≤ (1 + n ϑ_ξ)² C_Ω Q̃_N g X²` on `T_{r-3δ}` (the pullback of `Ω_K̃`). -/
theorem omegaKb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖lagrangeMat (modNewton h K ω (r - 2 * δ)) θ‖ ≤
      (1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * xX p γ εL εN δ ^ 2 := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hφ := H.phi3 hS hθ
  have e : lagrangeMat (modNewton h K ω (r - 2 * δ)) θ =
      lagrangeMat (fun y => modKtilde h K ω (y + modXiL h K ω y)) θ := by
    rw [lagrangeMat, lagrangeMat, tangentMat, tangentMat, (modNewton_eventuallyEq hθ2).fderiv_eq]
  obtain ⟨hr, hc⟩ := H.dXiL_b hS hθ
  rw [e]
  refine (norm_lagrangeMat_comp_le (H.Kt_diffAt hS _ (strip_sub
    (by linarith [H.δ_pos]) hφ)) (H.xiL_diffAt hS hθ2) hr hc (H.omegaKt hS _ hφ)).trans ?_
  have h1 : sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) ≤
      sCΩ p * sQtN p * sg p * xX p γ εL εN δ ^ 2 := by
    have hc0 : 0 ≤ sCΩ p * sQtN p * xX p γ εL εN δ :=
      mul_nonneg (mul_nonneg (nn_sCΩ H.ok) (nn_sQtN H.ok)) H.X_nonneg
    calc _ ≤ sCΩ p * sQtN p * xX p γ εL εN δ * (sg p * xX p γ εL εN δ) :=
          mul_le_mul_of_nonneg_left H.mu_div_δ_le hc0
      _ = _ := by ring
  calc _ ≤ (1 + p.n * p.θξ) ^ 2 * (sCΩ p * sQtN p * sg p * xX p γ εL εN δ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = _ := by ring

/-- Option L10 (`step:p2s2:selfcons`): the self-consistent bound of `η̄ᴸ` on `T_{r-3δ}`. -/
theorem etaLb_self (hsc : p.selfcons = true) : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaL h (modNewton h K ω (r - 2 * δ)) ω θ‖ ≤
      (sQL1 p + p.θN * (sCEN p / sCEL p) * sQbN p * sg p) / (1 - p.θN) *
        (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  obtain ⟨c1, c2⟩ := H.c_L10 hsc
  set Kb := modNewton h K ω (r - 2 * δ)
  set X := xX p γ εL εN δ with hXd
  set μ := mu p γ εL εN δ with hμd
  have hX := H.X_nonneg
  have hμ := H.mu_nonneg
  have hq1 := H.ok.ratios.2.2.2.2.2.2.2.1
  have hθN1 := H.ok.ratios.2.2.2.2.2.2.2.2.2.1
  -- the Lagrangian defects of `K̄`
  have hΩ := H.omegaKb_le hS θ hθ
  have hΩ0 : 0 ≤ (1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2 := by
    have := nn_sCΩ H.ok; have := nn_sQtN H.ok; have := nn_sg H.ok; positivity
  have hΩq : ‖lagrangeMat Kb θ‖ ≤ p.q :=
    hΩ.trans (by
      calc _ = 1 * ((1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2) := by ring
        _ ≤ max 1 (p.sB ^ 2) * ((1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΩ0
        _ = _ := by ring
        _ ≤ p.q := c2)
  obtain ⟨hGu, -, hBb⟩ := H.Gb hS θ hθ
  have hΩNq : ‖(normalMat Kb θ)ᵀ * omegaZeroMatrix n * normalMat Kb θ‖ ≤ p.q := by
    rw [Identities.fi_NtON]
    have nm := @FrameSharp.norm_mul_le_of_le
    refine (nm (nm hBb hΩ) hBb).trans ?_
    calc p.sB * ((1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2) * p.sB =
        p.sB ^ 2 * ((1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2) := by ring
      _ ≤ max 1 (p.sB ^ 2) * ((1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hΩ0
      _ = _ := by ring
      _ ≤ p.q := c2
  -- recovery for `K̄` at `θ`
  obtain ⟨a, ha⟩ : ∃ a, a = ‖etaL h Kb ω θ‖ := ⟨_, rfl⟩
  have hrec := norm_invarianceError_le_eta_pt (ω := ω) (h := h) hq1 (H.Lb_le hS θ hθ).1
    (H.Nb_sub_le hS θ hθ).2.1 hGu hΩq hΩNq ha.ge (H.etaNb_le hS θ hθ)
  -- the split
  obtain ⟨⟨-, hN2⟩, -⟩ := H.Nb_sub_le hS θ hθ
  have hsplit : ‖etaL h Kb ω θ‖ ≤ sQL1 p * (μ * X) + sCNbT p * X *
      (sCEL p * a + sCEN p * (sQbN p * μ ^ 2 / δ)) := by
    rw [etaLb_split θ]
    refine (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]; exact H.NtOEb_le hS θ hθ) ?_)
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
      (mul_nonneg (nn_sCNbT H.ok) hX))
    · rw [norm_mul_omegaZeroMatrix]; exact hN2
    · rw [norm_sumVec]
      exact hrec
  rw [← ha] at hsplit ⊢
  -- solve the inequality
  have hEL : 0 < sCEL p := by
    rw [sCEL]
    have := H.ok.caps.1; have := H.ok.caps.2.2.2.1; have := H.ok.ratios.2.2.2.2.2.2.1
    have hq2 : 0 < 1 - p.q ^ 2 := by nlinarith
    positivity
  have hEN := nn_sCEN H.ok
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  have hQb := nn_sQbN H.ok
  have hδ := H.δ_pos
  have hNbT := nn_sCNbT H.ok
  have hc : sCNbT p * X * sCEL p ≤ p.θN := by rw [mul_right_comm]; exact c1
  have hD : sCNbT p * X * (sCEN p * (sQbN p * μ ^ 2 / δ)) ≤
      p.θN * (sCEN p / sCEL p) * sQbN p * sg p * (μ * X) := by
    have e : sCNbT p * X * (sCEN p * (sQbN p * μ ^ 2 / δ)) =
        (sCNbT p * X * sCEL p) * (sCEN p / sCEL p) * sQbN p * (μ * (μ / δ)) := by
      field_simp
    rw [e]
    have hμδ : μ * (μ / δ) ≤ sg p * (μ * X) := by
      calc μ * (μ / δ) ≤ μ * (sg p * X) := mul_le_mul_of_nonneg_left H.mu_div_δ_le hμ
        _ = _ := by ring
    have hr0 : 0 ≤ sCEN p / sCEL p := div_nonneg hEN hEL.le
    calc (sCNbT p * X * sCEL p) * (sCEN p / sCEL p) * sQbN p * (μ * (μ / δ)) ≤
        p.θN * (sCEN p / sCEL p) * sQbN p * (μ * (μ / δ)) := by
          gcongr
      _ ≤ p.θN * (sCEN p / sCEL p) * sQbN p * (sg p * (μ * X)) := by
          have := H.ok.ratios.2.2.2.2.2.2.2.2.1
          exact mul_le_mul_of_nonneg_left hμδ (by positivity)
      _ = _ := by ring
  have hlin : a * (1 - p.θN) ≤ sQL1 p * (μ * X) + p.θN * (sCEN p / sCEL p) * sQbN p * sg p *
      (μ * X) := by
    have h1 : sCNbT p * X * (sCEL p * a) ≤ p.θN * a := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc ha0
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

/-- `bp:p2s2:step`: `|η̄ᴸ| ≤ Q_L μ²/(γ δ^{κ+1})` on `T_{r-3δ}`. -/
theorem etaLb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaL h (modNewton h K ω (r - 2 * δ)) ω θ‖ ≤
      sQL p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) := by
  intro θ hθ
  have e : sQL p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) =
      sQL p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [xX]; ring
  rw [e, sQL]
  simp only [H.fix, Bool.false_eq_true, ↓reduceIte]
  rw [sQLs]
  by_cases hsc : p.selfcons = true
  · simp only [hsc, ↓reduceIte]
    rw [min_mul_of_nonneg _ _ (mul_nonneg H.mu_nonneg H.X_nonneg)]
    exact le_min (H.etaLb_crude hS θ hθ) (H.etaLb_self hS hsc θ hθ)
  · simp only [hsc]
    exact H.etaLb_crude hS θ hθ

end Hyp

end ModStepB

end KAM.Sharp2

end
