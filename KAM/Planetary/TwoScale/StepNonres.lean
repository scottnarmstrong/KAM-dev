/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepFreq

/-!
# Two-scale KAM step: constants facts and nonresonance (`stepP:p3:st-nonres`)

Consequences of `KamHyp` on the constants (`rhoHat`, `cutoff`, `eHat`, `L`), and the two-scale
nonresonance estimate on the complex `rhoHat`-neighbourhood of `D` with the divisors
`α₁ = (2/3) γ₁ K^(-τ)`, `α₂ = (2/3) γ₂ K^(-τ)`, from the mean value inequality on the Hessian
bounds. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

theorem γ₁_pos (H : KamHyp D sbar p h f) : 0 < p.γ₁ := lt_of_lt_of_le H.positive.1 H.gamma_order

theorem τ_pos (H : KamHyp D sbar p h f) : 0 < p.τ := by
  have h1 := H.τ_gt
  have h2 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem L_pos (H : KamHyp D sbar p h f) : 0 < p.L := by
  have h1 := H.L_bound
  have : p.Mbar ≤ initialL p.M p.Mhat p.Mbar := le_max_left _ _
  linarith [H.positive.2.2.2.2.2.2.1]

theorem K_pos (H : KamHyp D sbar p h f) : 0 < cutoff p := cutoff_pos H.positive.2.1

theorem R_pos (H : KamHyp D sbar p h f) : 0 < rhoHat p :=
  rhoHat_pos H.positive.2.1 H.γ₁_pos H.positive.1 H.positive.2.2.2.2.1
    H.positive.2.2.2.2.2.1 H.positive.2.2.1

theorem K_mul_s (H : KamHyp D sbar p h f) : 6 ≤ cutoff p * p.s := by
  have hs := H.positive.2.1
  unfold cutoff constants
  have h1 : (1 : ℝ) ≤ max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) := le_max_left _ _
  have : 6 / p.s ≤ 6 / p.s * max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) :=
    le_mul_of_one_le_right (by positivity) h1
  calc (6 : ℝ) = 6 / p.s * p.s := by field_simp
    _ ≤ _ := by gcongr

theorem R_le_ρ (_H : KamHyp D sbar p h f) : rhoHat p ≤ p.ρ := by
  unfold rhoHat constants; exact min_le_right _ _

theorem R_le_γ₁ (H : KamHyp D sbar p h f) :
    3 * p.M * cutoff p ^ (p.τ + 1) * rhoHat p ≤ p.γ₁ := by
  have hK := H.K_pos
  have hM := H.positive.2.2.2.2.1
  have hd : 0 < 3 * p.M * cutoff p ^ (p.τ + 1) := by positivity
  have : rhoHat p ≤ p.γ₁ / (3 * p.M * cutoff p ^ (p.τ + 1)) := by
    unfold rhoHat constants
    exact (min_le_left _ _).trans ((min_le_left _ _))
  rw [le_div_iff₀ hd] at this; linarith

theorem R_le_γ₂ (H : KamHyp D sbar p h f) :
    3 * p.Mhat * cutoff p ^ (p.τ + 1) * rhoHat p ≤ p.γ₂ := by
  have hK := H.K_pos
  have hM := H.positive.2.2.2.2.2.1
  have hd : 0 < 3 * p.Mhat * cutoff p ^ (p.τ + 1) := by positivity
  have : rhoHat p ≤ p.γ₂ / (3 * p.Mhat * cutoff p ^ (p.τ + 1)) := by
    unfold rhoHat constants
    exact (min_le_left _ _).trans ((min_le_right _ _))
  rw [le_div_iff₀ hd] at this; linarith

theorem eHat_eq (p : ScaleData) : eHat p = p.E * p.L / rhoHat p ^ 2 := rfl

theorem eHat_nonneg (H : KamHyp D sbar p h f) : 0 ≤ eHat p := by
  rw [eHat_eq]
  have := H.positive.2.2.2.1; have := H.L_pos
  positivity

/-- `E = Ê R² / L`; with `L ≥ M̂⁻¹` this gives `E ≤ Ê R² M̂` (and likewise for `M`). -/
theorem E_le_Mhat (H : KamHyp D sbar p h f) :
    p.E ≤ eHat p * rhoHat p ^ 2 * p.Mhat := by
  have hL := H.L_pos; have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.2.1
  have h1 : p.Mhat⁻¹ ≤ p.L := (le_max_right _ _).trans' (le_max_right _ _) |>.trans H.L_bound
  have h2 : p.Mhat * p.L ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hMh.le
    rwa [mul_inv_cancel₀ hMh.ne'] at this
  have hE : eHat p * rhoHat p ^ 2 = p.E * p.L := by
    rw [eHat_eq]; field_simp
  have h3 : eHat p * p.Mhat * rhoHat p ^ 2 = (p.E * p.L) * p.Mhat := by rw [← hE]; ring
  nlinarith [H.positive.2.2.2.1]

theorem E_le_M (H : KamHyp D sbar p h f) : p.E ≤ eHat p * rhoHat p ^ 2 * p.M := by
  have hL := H.L_pos; have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.1
  have h1 : p.M⁻¹ ≤ p.L := ((le_max_left _ _).trans (le_max_right _ _)).trans H.L_bound
  have h2 : p.M * p.L ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hMh.le
    rwa [mul_inv_cancel₀ hMh.ne'] at this
  have hE : eHat p * rhoHat p ^ 2 = p.E * p.L := by
    rw [eHat_eq]; field_simp
  have h3 : eHat p * p.M * rhoHat p ^ 2 = (p.E * p.L) * p.M := by rw [← hE]; ring
  nlinarith [H.positive.2.2.2.1]

theorem eHat_small (H : KamHyp D sbar p h f) : 2 ^ 14 * eHat p < 1 := by
  have h1 := H.small
  have h2 : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  have h3 : (2 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
    have := H.a_pos; have := H.b_pos
    exact_mod_cast (by omega : 2 ≤ a + b)
  have h4 := H.eHat_nonneg
  nlinarith

end KamHyp

theorem modeSize_pos_of_ne {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ KAM.Fourier.modeSize k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
  unfold KAM.Fourier.modeSize
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (Finset.single_le_sum (f := fun j => |(k j : ℝ)|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i))

theorem dotC_block_le {a b : ℕ} {k : Fin (a + b) → ℤ} (hk : firstBlock (b := b) k = 0)
    (w : Fin (a + b) → ℂ) :
    ‖dotC k w‖ ≤ KAM.Fourier.modeSize k * ‖lastBlock (a := a) w‖ := by
  unfold dotC KAM.Fourier.modeSize
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
  rw [h1]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have : k (Fin.castAdd b j) = 0 := congrFun hk j
    simp [this]
  · exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (lastBlock (a := a) w) j) (abs_nonneg _)

theorem dotC_real {n : ℕ} (k : Fin n → ℤ) (ω : Fin n → ℝ) :
    ‖dotC k (KAM.realInclusion n ω)‖ = |∑ i, (k i : ℝ) * ω i| := by
  have : dotC k (KAM.realInclusion n ω) = ((∑ i, (k i : ℝ) * ω i : ℝ) : ℂ) := by
    simp [dotC]
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- Frequency increments on the ball around a real point (`stepP:p3:st-nonres`, mean value). -/
theorem freq_diff_bounds (H : KamHyp D sbar p h f) {J : Fin (a + b) → ℝ} (hJ : J ∈ D)
    {I : Fin (a + b) → ℂ} (hI : ‖I - KAM.realInclusion (a + b) J‖ < rhoHat p) :
    ‖freq h I - freq h (KAM.realInclusion (a + b) J)‖ ≤ p.M * rhoHat p ∧
    ‖lastBlock (a := a) (freq h I - freq h (KAM.realInclusion (a + b) J))‖ ≤
      p.Mhat * rhoHat p := by
  have hρ := H.positive.2.2.1
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hsub : ball (KAM.realInclusion (a + b) J) (rhoHat p) ⊆ KAM.actionNbhd D p.ρ :=
    (actionNbhd_ball hJ).trans (actionNbhd_mono H.R_le_ρ)
  have hopen := isOpen_actionNbhd' D p.ρ
  have hF : ∀ x ∈ ball (KAM.realInclusion (a + b) J) (rhoHat p),
      DifferentiableAt ℂ (freq h) x := fun x hx =>
    differentiableAt_freq hopen H.holo (hsub hx)
  have hmem : I ∈ ball (KAM.realInclusion (a + b) J) (rhoHat p) := by
    simpa [dist_eq_norm] using hI
  have hc : ∀ x ∈ ball (KAM.realInclusion (a + b) J) (rhoHat p), ∀ v (j : Fin (a + b)),
      ‖fderiv ℂ (freq h) x v j‖ ≤ p.M * ‖v‖ := by
    intro x hx v j
    exact (norm_le_pi_norm _ j).trans
      (((fderiv ℂ (freq h) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (H.hessian x (hsub hx)).1 (norm_nonneg _)))
  have hc2 : ∀ (j : Fin b), ∀ x ∈ ball (KAM.realInclusion (a + b) J) (rhoHat p), ∀ v,
      ‖fderiv ℂ (freq h) x v (Fin.natAdd a j)‖ ≤ p.Mhat * ‖v‖ := by
    intro j x hx v
    exact (norm_le_pi_norm (lastBlock (a := a) (fderiv ℂ (freq h) x v)) j).trans
      ((H.hessian x (hsub hx)).2.1 v)
  have hcen : KAM.realInclusion (a + b) J ∈ ball (KAM.realInclusion (a + b) J) (rhoHat p) :=
    mem_ball_self hR
  have hnorm : ‖I - KAM.realInclusion (a + b) J‖ ≤ rhoHat p := hI.le
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (coord_mvt (convex_ball _ _) (by positivity) j hF (fun x hx v => hc x hx v j) hmem hcen).trans
      (mul_le_mul_of_nonneg_left hnorm hM.le)
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (coord_mvt (convex_ball _ _) (by positivity) (Fin.natAdd a j) hF (hc2 j) hmem hcen).trans
      (mul_le_mul_of_nonneg_left hnorm hMh.le)


/-- Divisors `α₁ = (2/3) γ₁ K^(-τ)`, `α₂ = (2/3) γ₂ K^(-τ)` (`stepP:p3:st-nonres`). -/
def alpha₁ (p : ScaleData) : ℝ := 2 / 3 * p.γ₁ / cutoff p ^ p.τ
def alpha₂ (p : ScaleData) : ℝ := 2 / 3 * p.γ₂ / cutoff p ^ p.τ

/-- Arithmetic core of the nonresonance estimate. -/
theorem nonres_arith {γ T Tm m K M R x y d : ℝ} (hT : 0 < T) (hTm : 0 < Tm) (hTT : Tm ≤ T)
    (hγ : 0 < γ) (hmK : m ≤ K) (hm0 : 0 ≤ m) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hc : 3 * M * (T * K) * R ≤ γ) (hdio : γ / Tm ≤ x) (hy : y ≤ m * (M * R))
    (hd : x - y ≤ d) : 2 / 3 * γ / T ≤ d := by
  have h1 : γ / T ≤ γ / Tm := div_le_div_of_nonneg_left hγ.le hTm hTT
  have h2 : m * (M * R) ≤ K * (M * R) := mul_le_mul_of_nonneg_right hmK (by positivity)
  have h3 : K * (M * R) ≤ γ / (3 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h4 : γ / (3 * T) = γ / T / 3 := by field_simp
  have h5 : 2 / 3 * γ / T = γ / T - γ / T / 3 := by field_simp; ring
  linarith

theorem twoDiv_of_kamHyp (H : KamHyp D sbar p h f)
    (hD : ∀ I ∈ D, realFreq h I ∈ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ) :
    TwoDiv (KAM.actionNbhd D (rhoHat p)) (cutoff p) (alpha₁ p) (alpha₂ p) 1 h := by
  intro I ⟨J, hJ, hlt⟩ k hk hkK
  have hK := H.K_pos
  have hτ := H.τ_pos
  have hρ := H.positive.2.2.1
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hsb : 0 < sbar + p.s := by have := H.widths.1; have := H.positive.2.1; linarith
  have hcen : KAM.realInclusion (a + b) J ∈ KAM.actionNbhd D p.ρ :=
    mem_actionNbhd_of_mem hρ hJ
  have hfr := freq_realInclusion_eq H.holo hsb H.real_h hcen
  obtain ⟨hd1, hd2⟩ := freq_diff_bounds H hJ hlt
  obtain ⟨hdio1, hdio2⟩ := hD J hJ
  set Δ := freq h I - freq h (KAM.realInclusion (a + b) J) with hΔ
  have hsplit : dotC k (freq h I) = dotC k (freq h (KAM.realInclusion (a + b) J)) + dotC k Δ := by
    simp only [hΔ, dotC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
  have hlow : ‖dotC k (freq h (KAM.realInclusion (a + b) J))‖ - ‖dotC k Δ‖ ≤
      ‖dotC k (freq h I)‖ := by
    rw [hsplit]
    have h := norm_sub_le (dotC k (freq h (KAM.realInclusion (a + b) J)) + dotC k Δ) (dotC k Δ)
    rw [add_sub_cancel_right] at h
    linarith
  rw [hfr, dotC_real] at hlow
  have hm1 := modeSize_pos_of_ne hk
  have hKt : cutoff p ^ (p.τ + 1) = cutoff p ^ p.τ * cutoff p := Real.rpow_add_one hK.ne' _
  have hT : 0 < cutoff p ^ p.τ := Real.rpow_pos_of_pos hK _
  have hmt : KAM.Fourier.modeSize k ^ p.τ ≤ cutoff p ^ p.τ :=
    Real.rpow_le_rpow (by linarith) hkK hτ.le
  have hmt0 : 0 < KAM.Fourier.modeSize k ^ p.τ := Real.rpow_pos_of_pos (by linarith) _
  have hRγ₁ := H.R_le_γ₁
  have hRγ₂ := H.R_le_γ₂
  rw [hKt] at hRγ₁ hRγ₂
  by_cases hfb : firstBlock (b := b) k = 0
  · rw [if_pos hfb, div_one]
    have hd := dotC_block_le hfb Δ
    refine le_trans ?_ hlow
    refine nonres_arith (x := |∑ i, (k i : ℝ) * realFreq h J i|)
      (y := ‖dotC k Δ‖) (K := cutoff p) (M := p.Mhat) (R := rhoHat p) hT hmt0 hmt
      H.positive.1 hkK (by linarith) hMh.le hR.le (by linarith) (hdio2 k hk hfb) ?_ le_rfl
    exact hd.trans (mul_le_mul_of_nonneg_left hd2 (by linarith))
  · rw [if_neg hfb, div_one]
    have hd := norm_dotC_le k Δ
    refine le_trans ?_ hlow
    refine nonres_arith (x := |∑ i, (k i : ℝ) * realFreq h J i|)
      (y := ‖dotC k Δ‖) (K := cutoff p) (M := p.M) (R := rhoHat p) hT hmt0 hmt
      H.γ₁_pos hkK (by linarith) hM.le hR.le (by linarith) (hdio1 k hfb) ?_ le_rfl
    exact hd.trans (mul_le_mul_of_nonneg_left hd1 (by linarith))

end KAM.Planetary

end
