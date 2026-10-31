/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.NewErr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Option L10 for the bordered step: the self-consistent tangential error

* `omegaKb_le`: `Ω_K̄ = Dφᵀ (Ω_K̃ ∘ φ) Dφ` (`norm_lagrangeMat_comp_le`), so
  `|Ω_K̄| ≤ (1 + n ϑ_ξ)² C_Ω Q̃_N g X²` on `T_{r-3δ}`.
* `etaLb_self`: with the L10 conditions, recovery for `K̄` at the frequency `ω̄` on `T_{r-3δ}` gives
  `|η̄ᴸ| ≤ (Q'_L + ϑ_N (C^N_E/C^L_E) Q̄_N g)/(1 - ϑ_N) μ X`.
* `etaLb_le`: `|η̄ᴸ| ≤ Q_L μ²/(γ δ^{κ+1})` (the crude bound, and with `selfcons` the minimum;
  for the bordered step `Q_L` also dominates `Q_ω`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Iso.Linear KAM.Iso.Apost
  KAM.Sharp2.ModStepB

variable {n : ℕ}

namespace ModStepB

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {E₀ γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω E₀ Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `|Ω_K̄| ≤ (1 + n ϑ_ξ)² C_Ω Q̃_N g X²` on `T_{r-3δ}` (the pullback of `Ω_K̃`). -/
theorem omegaKb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖lagrangeMat (newK h K ω E₀ (r - 2 * δ)) θ‖ ≤
      (1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * xX p γ εL εN δ ^ 2 := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hφ := H.phi3 hS hθ
  have e : lagrangeMat (newK h K ω E₀ (r - 2 * δ)) θ =
      lagrangeMat (fun y => tilK h K ω E₀ (y + xiLI h K ω E₀ y)) θ := by
    rw [lagrangeMat, lagrangeMat, tangentMat, tangentMat, (newK_eventuallyEq hθ2).fderiv_eq]
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
    ‖etaL h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ‖ ≤
      (sQL1 p + p.θN * (sCEN p / sCEL p) * sQbN p * sg p) / (1 - p.θN) *
        (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  obtain ⟨c1, c2⟩ := H.c_L10 hsc
  set Kb := newK h K ω E₀ (r - 2 * δ)
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
  obtain ⟨a, ha⟩ : ∃ a, a = ‖etaL h Kb (newOmega h K ω E₀) θ‖ := ⟨_, rfl⟩
  have hrec := norm_invarianceError_le_eta_pt (ω := newOmega h K ω E₀) (h := h) hq1
    (H.Lb_le hS θ hθ).1
    (H.Nb_sub_le hS θ hθ).2.1 hGu hΩq hΩNq ha.ge (H.etaNb_le hS θ hθ)
  -- the split
  obtain ⟨⟨-, hN2⟩, -⟩ := H.Nb_sub_le hS θ hθ
  have hsplit : ‖etaL h Kb (newOmega h K ω E₀) θ‖ ≤ sQL1 p * (μ * X) + sCNbT p * X *
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
    ‖etaL h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ‖ ≤
      sQL p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) := by
  intro θ hθ
  have e : sQL p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) =
      sQL p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [xX]; ring
  rw [e, sQL]
  simp only [H.iso, ↓reduceIte]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (mul_nonneg H.mu_nonneg H.X_nonneg))
  rw [sQLs]
  by_cases hsc : p.selfcons = true
  · simp only [hsc, ↓reduceIte]
    rw [min_mul_of_nonneg _ _ (mul_nonneg H.mu_nonneg H.X_nonneg)]
    exact le_min (H.etaLb_crude hS θ hθ) (H.etaLb_self hS hsc θ hθ)
  · simp only [hsc]
    exact H.etaLb_crude hS θ hθ

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
