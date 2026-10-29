/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Tori
public import KAM.Planetary.WeakKAM.Budgets

/-! # P11B displacement: `displacement`, `gamma_inverse`, the pointwise power

The displacement of the defect (`bpP:p11a:displacement`, steps `dp-tel`, `dp-size`), the size of
`γ⁻¹` (`bpP:p11a:gamma-inverse`, step `gi-branches`) and their pointwise combination
(`stepP:p11a:dpc-comb`, as `selectionDelta_le_power`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

def selectionDelta (d : SelectionData n) (ε : ℝ) : ℝ :=
  let a := selectionAdapted d ε
  selectionQ₀ a * max (3 * (a.strip / 24) / selectionCQ n) (a.s₀ / 16)
def selectionCDelta (d : SelectionData n) : ℝ :=
  selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ * Real.sqrt (2 * n * d.C₁) /
    (128 * π * (d.strip / 24) ^ (n + 1))
def selectionCGamma (d : SelectionData n) : ℝ :=
  2 * max (2 * Real.sqrt n * (4 : ℝ) ^ ((d.ρ : ℝ)⁻¹))
    ((selectionChat d / d.loss) ^ ((d.μ : ℝ) / d.ρ))

section GammaInverse
variable (d : SelectionData n)

theorem disp_rho_pos : (0 : ℝ) < d.ρ := by rcases d.rho_mem with h | h <;> simp [h]

theorem disp_inv_A (hβ : d.β ≤ 1) :
    ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹))⁻¹ ≤
      (2 * Real.sqrt n * (4 : ℝ) ^ ((d.ρ : ℝ)⁻¹)) * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hρ := disp_rho_pos d
  have hβ0 := d.beta_pos
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  set r : ℝ := (d.ρ : ℝ)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.2 hρ
  have e : ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ r)⁻¹ =
      2 * Real.sqrt n * (4 : ℝ) ^ r * d.β ^ (-r) := by
    rw [Real.div_rpow hβ0.le (by norm_num), Real.rpow_neg hβ0.le]
    have h4 : 0 < (4 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) r
    have hb : 0 < d.β ^ r := Real.rpow_pos_of_pos hβ0 r
    field_simp
  rw [e]
  have hexp : -((d.μ : ℝ) + 1) / d.ρ ≤ -r := by
    rw [hr, neg_div, neg_le_neg_iff, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg d.μ : (0 : ℝ) ≤ d.μ)])
      hρ.le
  have := Real.rpow_le_rpow_of_exponent_ge hβ0 hβ hexp
  have h4 : 0 < (4 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) r
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem disp_inv_B :
    (((d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ)))⁻¹ =
      (selectionChat d / d.loss) ^ ((d.μ : ℝ) / d.ρ) * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  have hρ := disp_rho_pos d
  have hμ : (0 : ℝ) < d.μ := by exact_mod_cast d.μ_pos
  have hβ0 := d.beta_pos
  have hC := selectionChat_pos d
  have hl := d.loss_pos
  have hexp : (-1 - (d.μ : ℝ)⁻¹) * ((d.μ : ℝ) / d.ρ) = -((d.μ : ℝ) + 1) / d.ρ := by
    field_simp
  rw [← Real.inv_rpow (by positivity)]
  have : (d.loss / selectionCDio d)⁻¹ = (selectionChat d / d.loss) * d.β ^ (-1 - (d.μ : ℝ)⁻¹) := by
    unfold selectionCDio
    have : 0 < d.β ^ (-1 - (d.μ : ℝ)⁻¹) := Real.rpow_pos_of_pos hβ0 _
    field_simp
  rw [this, Real.mul_rpow (by positivity) (Real.rpow_pos_of_pos hβ0 _).le, ← Real.rpow_mul hβ0.le,
    hexp]

/-- Step `gi-branches` of `bpP:p11a:gamma-inverse`. -/
theorem gamma_inverse (d : SelectionData n) (hβ : d.β ≤ 1) :
    (selectionGamma d)⁻¹ ≤ selectionCGamma d * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  have hg0 : 0 < d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := Real.rpow_pos_of_pos d.beta_pos _
  have hγ : (selectionGamma d)⁻¹ = 2 * (min ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ *
      (d.β / 4) ^ ((d.ρ : ℝ)⁻¹)) ((d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ)))⁻¹ := by
    unfold selectionGamma
    rw [inv_div]
    ring
  rw [hγ]
  unfold selectionCGamma
  rcases min_choice ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹))
      ((d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ)) with h | h
  · rw [h, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (disp_inv_A d hβ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)
  · rw [h, disp_inv_B, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le

end GammaInverse

section Defect
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable {b : SelectionR n}

theorem disp_angle_le (L : SelectionLimit d f a) (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    ‖(L.defect b θ).1‖ ≤ ∑' j, selectionA a j := by
  have hθ : selectionReal θ ∈ complexStrip n (d.strip / 4) :=
    selectionReal_mem_complexStrip (by linarith [d.strip_pos]) θ
  have h := L.complex_angle_bound b hb _ hθ
  rw [L.limit_real b hb θ] at h
  have e : (phaseToC ((θ, 0) + L.defect b θ)).1 - selectionReal θ =
      selectionReal (L.defect b θ).1 := by
    funext i; simp [phaseToC, selectionReal]
  rwa [e, norm_selectionReal] at h

theorem disp_action_le (L : SelectionLimit d f a) (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    ‖(L.defect b θ).2‖ ≤ ∑' j, selectionAlpha a j := by
  have hθ : selectionReal θ ∈ complexStrip n (d.strip / 4) :=
    selectionReal_mem_complexStrip (by linarith [d.strip_pos]) θ
  have h := L.complex_action_bound b hb _ hθ
  rw [L.limit_real b hb θ] at h
  have e : (phaseToC ((θ, 0) + L.defect b θ)).2 = selectionReal (L.defect b θ).2 := by
    funext i; simp [phaseToC, selectionReal]
  rwa [e, norm_selectionReal] at h

end Defect

section Scalars
variable {d : SelectionData n} {ε : ℝ}

theorem disp_Xi_ge (d : SelectionData n) : 2 ≤ selectionXi d := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (d.τ + 1) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) ≤ d.τ + 1 by linarith [d.tau_nonneg])
  have h0 := selectiont₀_pos d
  have hs : 0 < d.strip / 24 := by linarith [d.strip_pos]
  have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos (selectionT₀_pos d)
  unfold selectionXi
  have : 1 ≤ 1 + selectiont₀ d / (d.strip / 24) + (d.strip / 24) / selectiont₀ d +
      selectionT₀ d * (d.strip / 24) := by
    have : 0 ≤ selectiont₀ d / (d.strip / 24) + (d.strip / 24) / selectiont₀ d +
        selectionT₀ d * (d.strip / 24) := by positivity
    linarith
  nlinarith

/-- The `dp-size` inequalities and the `dp-tel` bound, at the adapted schedule. -/
theorem disp_scalar (hε : 0 < ε) (hsmall : ε ≤ selectionAdmissible d) :
    selectionDelta d ε ≤ selectionQ₀ (selectionAdapted d ε) / 128 ∧
    selectionDelta d ε ≤ (2 : ℝ)⁻¹ ^ 18 ∧
    selectionDelta d ε ≤ selectionCDelta d * Real.sqrt ε / selectionGamma d := by
  obtain ⟨hadm, hs, -, -, hratio, -⟩ := free_radius d ε hε hsmall
  set a := selectionAdapted d ε with ha
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hQ0 : 0 ≤ selectionQ₀ a := by
    have he' : 0 < a.ε₀ := by show 0 < 2 * ε; positivity
    exact wbud_Q₀_nonneg (weakBudgetCtx_of d a hadm rfl rfl rfl rfl rfl rfl hs he')
  have hCQ : (162 : ℝ) ≤ selectionCQ n := by unfold selectionCQ; nlinarith
  have hx : 3 * (a.strip / 24) / selectionCQ n ≤ 1 / 128 := by
    rw [div_le_iff₀ (by linarith)]
    have : a.strip ≤ 1 := d.strip_le
    show 3 * (d.strip / 24) ≤ _
    nlinarith [d.strip_pos]
  have hy : a.s₀ / 16 ≤ 1 / 128 := by
    have h1 := hadm.radius
    have h2 := hadm.t_le
    have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
    have h3 : a.t₀ ≤ 1 := h2.trans ((div_le_one (by linarith)).2 (d.theta_le.trans hsq))
    have h4 : a.t₀ / (8 * n) ≤ a.t₀ / 8 := by
      have := hadm.t_pos
      exact div_le_div_of_nonneg_left this.le (by norm_num) (by nlinarith)
    linarith
  have hD : selectionDelta d ε ≤ selectionQ₀ a / 128 := by
    unfold selectionDelta
    show selectionQ₀ a * max _ _ ≤ _
    calc selectionQ₀ a * max (3 * (a.strip / 24) / selectionCQ n) (a.s₀ / 16)
        ≤ selectionQ₀ a * (1 / 128) :=
          mul_le_mul_of_nonneg_left (max_le hx hy) hQ0
      _ = selectionQ₀ a / 128 := by ring
  refine ⟨hD, ?_, ?_⟩
  · have hw := hadm.weighted
    have hXi := disp_Xi_ge d
    have : selectionQ₀ a ≤ (2 : ℝ)⁻¹ ^ 11 := by nlinarith
    refine hD.trans ?_
    calc selectionQ₀ a / 128 ≤ (2 : ℝ)⁻¹ ^ 11 / 128 := by linarith
      _ = (2 : ℝ)⁻¹ ^ 18 := by norm_num
  · refine hD.trans (le_of_eq ?_)
    have hsq : Real.sqrt (2 * n * d.C₁ * ε) = Real.sqrt (2 * n * d.C₁) * Real.sqrt ε :=
      Real.sqrt_mul (by have := d.hessian_normalized; positivity) ε
    have hq : selectionQ₀ a = selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ *
        (Real.sqrt (2 * n * d.C₁) * Real.sqrt ε) /
        (π * selectionGamma d * (d.strip / 24) ^ (n + 1)) := by
      unfold selectionQ₀
      rw [hratio, hsq]
      rfl
    rw [hq]
    unfold selectionCDelta
    ring

end Scalars

/-- Step `dpc-comb` of `bpP:p11a:displacement-power`, pointwise in `d`, `ε`. -/
theorem selectionDelta_le_power (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (hβ : d.β ≤ 1) :
    selectionDelta d ε ≤
      selectionCDelta d * selectionCGamma d * Real.sqrt ε *
        d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  have h := (disp_scalar he hsmall).2.2
  have hg := gamma_inverse d hβ
  have hc : 0 ≤ selectionCDelta d * Real.sqrt ε := by
    unfold selectionCDelta
    have := selectionT₀_pos d
    have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos this
    have : 0 < d.strip / 24 := by linarith [d.strip_pos]
    have := selectionCQ_pos d.n_pos
    positivity
  calc selectionDelta d ε ≤ selectionCDelta d * Real.sqrt ε / selectionGamma d := h
    _ = selectionCDelta d * Real.sqrt ε * (selectionGamma d)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ selectionCDelta d * Real.sqrt ε *
          (selectionCGamma d * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ)) :=
        mul_le_mul_of_nonneg_left hg hc
    _ = _ := by ring

structure SelectionDisplacement (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionTori d f (selectionAdapted d ε) where
  displacement : ∀ b ∈ Kinf, ∀ θ, ‖defect b θ‖ ≤ selectionDelta d ε
  angle_displacement : ∀ b ∈ Kinf, ∀ θ, ‖(defect b θ).1‖ ≤
    3 * (d.strip / 24) * selectionQ₀ (selectionAdapted d ε) / selectionCQ n
  action_displacement : ∀ b ∈ Kinf, ∀ θ, ‖(defect b θ).2‖ ≤
    (selectionAdapted d ε).s₀ * selectionQ₀ (selectionAdapted d ε) / 16
  delta_small : selectionDelta d ε ≤ selectionQ₀ (selectionAdapted d ε) / 128
  delta_absolute : selectionDelta d ε ≤ (2 : ℝ)⁻¹ ^ 18
  delta_power : selectionDelta d ε ≤ selectionCDelta d * Real.sqrt ε / selectionGamma d

theorem displacement (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionDisplacement d f ε) := by
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  have cx := weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he'
  obtain ⟨L⟩ := limit_torus d ε he hsmall f hf
  obtain ⟨-, -, -, -, -, -, hA, hα, -⟩ := wbud_exported cx
  obtain ⟨hD, hD18, hDp⟩ := disp_scalar he hsmall
  have hQ0 := wbud_Q₀_nonneg cx
  have hang : ∀ b ∈ L.Kinf, ∀ θ, ‖(L.defect b θ).1‖ ≤
      3 * (d.strip / 24) * selectionQ₀ (selectionAdapted d ε) / selectionCQ n :=
    fun b hb θ => (disp_angle_le L.toSelectionLimit hb θ).trans hA
  have hact : ∀ b ∈ L.Kinf, ∀ θ, ‖(L.defect b θ).2‖ ≤
      (selectionAdapted d ε).s₀ * selectionQ₀ (selectionAdapted d ε) / 16 :=
    fun b hb θ => (disp_action_le L.toSelectionLimit hb θ).trans hα
  refine ⟨{ L with
    displacement := fun b hb θ => ?_
    angle_displacement := hang
    action_displacement := hact
    delta_small := hD
    delta_absolute := hD18
    delta_power := hDp }⟩
  rw [Prod.norm_def]
  unfold selectionDelta
  refine max_le ((hang b hb θ).trans ?_) ((hact b hb θ).trans ?_)
  · calc 3 * (d.strip / 24) * selectionQ₀ (selectionAdapted d ε) / selectionCQ n
        = selectionQ₀ (selectionAdapted d ε) * (3 * (d.strip / 24) / selectionCQ n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hQ0
  · calc (selectionAdapted d ε).s₀ * selectionQ₀ (selectionAdapted d ε) / 16
        = selectionQ₀ (selectionAdapted d ε) * ((selectionAdapted d ε).s₀ / 16) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0

end KAM.Planetary

end
