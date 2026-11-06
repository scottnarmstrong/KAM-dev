/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic

/-!
# The `Γ` enclosure on a cell and eccentricities from `Γ` (T2-CONF, N6)

* `rdot a b = Re (a · conj b)`, in coordinates.
* `normSq_bounds_of_cell`: for `z = V₀ s₀ w₁ + V₁ s₁ w₂ + V₂ s₂` with `s_k ∈ [sl_k, sh_k]` and
  `w_a = P_a + x_a D_a + ρ_a` (`|x_a| ≤ h_a`, `‖ρ_a‖ ≤ ρ̄_a`, `‖w_a - P_a‖ ≤ ε_a`, `‖P_a‖ = 1`),
  and the
  centre value `z_c = V₀ s_c,0 P₁ + V₁ s_c,1 P₂ + V₂ s_c,2`, `G = |z_c|²`, the linearization gives
  `|z|² ≤ G + 2E + R²` and `(G - E)² ≤ |z|² G` when `0 ≤ E ≤ G`.
* `ecc_bounds_of_gamma`: rational conditions on `Γ_lo, Γ_hi` giving
  `lo ≤ √(1 - (1 - Γ/Λ)²) ≤ hi` for `Γ ∈ [Γ_lo, Γ_hi]`.
-/

@[expose] public section

open Complex

namespace KAM.EffectiveStability.Tube

/-- `Re (a · conj b)` in coordinates. -/
noncomputable def rdot (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

theorem rdot_self (a : ℂ) : rdot a a = Complex.normSq a := by
  simp [rdot, Complex.normSq_apply]

theorem abs_rdot_le (a b : ℂ) : |rdot a b| ≤ ‖a‖ * ‖b‖ := by
  have e : rdot a b = (a * (starRingEnd ℂ) b).re := by simp [rdot]
  rw [e, ← norm_conj b, ← norm_mul]
  exact Complex.abs_re_le_norm _

theorem normSq_add_rdot (a b : ℂ) :
    Complex.normSq (a + b) = Complex.normSq a + 2 * rdot a b + Complex.normSq b := by
  simp [Complex.normSq_apply, rdot]; ring

/-- The `Γ` enclosure on a cell (see the module docstring). -/
theorem normSq_bounds_of_cell {V₀ V₁ V₂ : ℝ} {sl sh s : Fin 3 → ℝ}
    (hsl : ∀ k, 0 ≤ sl k) (hs : ∀ k, sl k ≤ s k ∧ s k ≤ sh k)
    {P₁ P₂ D₁ D₂ w₁ w₂ : ℂ} (hP₁ : ‖P₁‖ = 1) (hP₂ : ‖P₂‖ = 1)
    {x₁ x₂ h₁ h₂ ε₁ ε₂ ρ₁ ρ₂ Z : ℝ} (hx₁ : |x₁| ≤ h₁) (hx₂ : |x₂| ≤ h₂)
    (hρ₁ : ‖w₁ - P₁ - (x₁ : ℂ) * D₁‖ ≤ ρ₁) (hρ₂ : ‖w₂ - P₂ - (x₂ : ℂ) * D₂‖ ≤ ρ₂)
    (hε₁ : ‖w₁ - P₁‖ ≤ ε₁) (hε₂ : ‖w₂ - P₂‖ ≤ ε₂) (hZ : 0 ≤ Z)
    (zc : ℂ) (hzc : zc = (V₀ : ℂ) * (((sl 0 + sh 0) / 2 : ℝ) : ℂ) * P₁ +
      (V₁ : ℂ) * (((sl 1 + sh 1) / 2 : ℝ) : ℂ) * P₂ + (V₂ : ℂ) * (((sl 2 + sh 2) / 2 : ℝ) : ℂ))
    (hzZ : Complex.normSq zc ≤ Z * Z) :
    Complex.normSq ((V₀ : ℂ) * (s 0 : ℂ) * w₁ + (V₁ : ℂ) * (s 1 : ℂ) * w₂ + (V₂ : ℂ) * (s 2 : ℂ)) ≤
      Complex.normSq zc + 2 * (|V₀| * ((sh 0 - sl 0) / 2) * |rdot zc P₁| +
        |V₁| * ((sh 1 - sl 1) / 2) * |rdot zc P₂| + |V₂| * ((sh 2 - sl 2) / 2) * |rdot zc 1| +
        |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) + |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂)) +
      (|V₀| * ((sh 0 - sl 0) / 2) + |V₁| * ((sh 1 - sl 1) / 2) + |V₂| * ((sh 2 - sl 2) / 2) +
        |V₀| * sh 0 * ε₁ + |V₁| * sh 1 * ε₂) *
      (|V₀| * ((sh 0 - sl 0) / 2) + |V₁| * ((sh 1 - sl 1) / 2) + |V₂| * ((sh 2 - sl 2) / 2) +
        |V₀| * sh 0 * ε₁ + |V₁| * sh 1 * ε₂) ∧
    (0 < Complex.normSq zc →
      |V₀| * ((sh 0 - sl 0) / 2) * |rdot zc P₁| + |V₁| * ((sh 1 - sl 1) / 2) * |rdot zc P₂| +
        |V₂| * ((sh 2 - sl 2) / 2) * |rdot zc 1| + |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) +
        |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂) ≤ Complex.normSq zc →
      (Complex.normSq zc - (|V₀| * ((sh 0 - sl 0) / 2) * |rdot zc P₁| +
        |V₁| * ((sh 1 - sl 1) / 2) * |rdot zc P₂| + |V₂| * ((sh 2 - sl 2) / 2) * |rdot zc 1| +
        |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) + |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂))) *
      (Complex.normSq zc - (|V₀| * ((sh 0 - sl 0) / 2) * |rdot zc P₁| +
        |V₁| * ((sh 1 - sl 1) / 2) * |rdot zc P₂| + |V₂| * ((sh 2 - sl 2) / 2) * |rdot zc 1| +
        |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) + |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂))) ≤
      Complex.normSq ((V₀ : ℂ) * (s 0 : ℂ) * w₁ + (V₁ : ℂ) * (s 1 : ℂ) * w₂ +
        (V₂ : ℂ) * (s 2 : ℂ)) * Complex.normSq zc) := by
  set z : ℂ := (V₀ : ℂ) * (s 0 : ℂ) * w₁ + (V₁ : ℂ) * (s 1 : ℂ) * w₂ + (V₂ : ℂ) * (s 2 : ℂ)
    with hzdef
  set ds : Fin 3 → ℝ := fun k => (sh k - sl k) / 2 with hdsdef
  set E : ℝ := |V₀| * ds 0 * |rdot zc P₁| + |V₁| * ds 1 * |rdot zc P₂| + |V₂| * ds 2 * |rdot zc 1| +
      |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) + |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂)
    with hEdef
  set R : ℝ := |V₀| * ds 0 + |V₁| * ds 1 + |V₂| * ds 2 + |V₀| * sh 0 * ε₁ + |V₁| * sh 1 * ε₂
    with hRdef
  set sc : Fin 3 → ℝ := fun k => (sl k + sh k) / 2 with hsc
  have hds : ∀ k, |s k - sc k| ≤ ds k := fun k => by
    rw [abs_le]; constructor <;> simp only [hsc, hdsdef] <;> linarith [(hs k).1, (hs k).2]
  have hs0 : ∀ k, 0 ≤ s k := fun k => le_trans (hsl k) (hs k).1
  have hss : ∀ k, |s k| ≤ sh k := fun k => by rw [abs_of_nonneg (hs0 k)]; exact (hs k).2
  have hsh : ∀ k, 0 ≤ sh k := fun k => le_trans (hs0 k) (hs k).2
  have hzcn : ‖zc‖ ≤ Z := by
    have h1 : ‖zc‖ ^ 2 ≤ Z ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; nlinarith [hzZ]
    exact (sq_le_sq₀ (norm_nonneg zc) hZ).mp h1
  set ρ₁' : ℂ := w₁ - P₁ - (x₁ : ℂ) * D₁ with hρ₁'
  set ρ₂' : ℂ := w₂ - P₂ - (x₂ : ℂ) * D₂ with hρ₂'
  -- the deviation from the centre value
  set δ : ℂ := z - zc with hδ
  have hδe : δ = (V₀ : ℂ) * ((s 0 - sc 0 : ℝ) : ℂ) * P₁ + (V₁ : ℂ) * ((s 1 - sc 1 : ℝ) : ℂ) * P₂ +
      (V₂ : ℂ) * ((s 2 - sc 2 : ℝ) : ℂ) + (V₀ : ℂ) * (s 0 : ℂ) * (w₁ - P₁) +
      (V₁ : ℂ) * (s 1 : ℂ) * (w₂ - P₂) := by
    simp only [hδ, hzdef, hzc, hsc]; push_cast; ring
  -- `Re (z_c conj δ)` term by term
  have hrd : rdot zc δ = V₀ * (s 0 - sc 0) * rdot zc P₁ + V₁ * (s 1 - sc 1) * rdot zc P₂ +
      V₂ * (s 2 - sc 2) * rdot zc 1 + V₀ * s 0 * (x₁ * rdot zc D₁ + rdot zc ρ₁') +
      V₁ * s 1 * (x₂ * rdot zc D₂ + rdot zc ρ₂') := by
    have hw₁ : w₁ - P₁ = (x₁ : ℂ) * D₁ + ρ₁' := by rw [hρ₁']; ring
    have hw₂ : w₂ - P₂ = (x₂ : ℂ) * D₂ + ρ₂' := by rw [hρ₂']; ring
    rw [hδe, hw₁, hw₂]
    simp only [rdot, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  have hE : |rdot zc δ| ≤ E := by
    rw [hrd]
    have t1 : |V₀ * (s 0 - sc 0) * rdot zc P₁| ≤ |V₀| * ds 0 * |rdot zc P₁| := by
      rw [abs_mul, abs_mul]; gcongr; exact hds 0
    have t2 : |V₁ * (s 1 - sc 1) * rdot zc P₂| ≤ |V₁| * ds 1 * |rdot zc P₂| := by
      rw [abs_mul, abs_mul]; gcongr; exact hds 1
    have t3 : |V₂ * (s 2 - sc 2) * rdot zc 1| ≤ |V₂| * ds 2 * |rdot zc 1| := by
      rw [abs_mul, abs_mul]; gcongr; exact hds 2
    have r1 : |rdot zc ρ₁'| ≤ Z * ρ₁ :=
      (abs_rdot_le _ _).trans (mul_le_mul hzcn hρ₁ (norm_nonneg _) hZ)
    have r2 : |rdot zc ρ₂'| ≤ Z * ρ₂ :=
      (abs_rdot_le _ _).trans (mul_le_mul hzcn hρ₂ (norm_nonneg _) hZ)
    have t4 : |V₀ * s 0 * (x₁ * rdot zc D₁ + rdot zc ρ₁')| ≤
        |V₀| * sh 0 * (h₁ * |rdot zc D₁| + Z * ρ₁) := by
      rw [abs_mul, abs_mul]
      have : |x₁ * rdot zc D₁ + rdot zc ρ₁'| ≤ h₁ * |rdot zc D₁| + Z * ρ₁ :=
        (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]; gcongr) r1)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hss 0) (abs_nonneg _)) this (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) (hsh 0))
    have t5 : |V₁ * s 1 * (x₂ * rdot zc D₂ + rdot zc ρ₂')| ≤
        |V₁| * sh 1 * (h₂ * |rdot zc D₂| + Z * ρ₂) := by
      rw [abs_mul, abs_mul]
      have : |x₂ * rdot zc D₂ + rdot zc ρ₂'| ≤ h₂ * |rdot zc D₂| + Z * ρ₂ :=
        (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]; gcongr) r2)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hss 1) (abs_nonneg _)) this (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) (hsh 1))
    calc _ ≤ |V₀ * (s 0 - sc 0) * rdot zc P₁| + |V₁ * (s 1 - sc 1) * rdot zc P₂| +
          |V₂ * (s 2 - sc 2) * rdot zc 1| + |V₀ * s 0 * (x₁ * rdot zc D₁ + rdot zc ρ₁')| +
          |V₁ * s 1 * (x₂ * rdot zc D₂ + rdot zc ρ₂')| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
      _ ≤ E := by rw [hEdef]; linarith
  have hR : ‖δ‖ ≤ R := by
    rw [hδe]
    have n1 : ‖(V₀ : ℂ) * ((s 0 - sc 0 : ℝ) : ℂ) * P₁‖ ≤ |V₀| * ds 0 := by
      rw [norm_mul, norm_mul, hP₁, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, mul_one]; gcongr; exact hds 0
    have n2 : ‖(V₁ : ℂ) * ((s 1 - sc 1 : ℝ) : ℂ) * P₂‖ ≤ |V₁| * ds 1 := by
      rw [norm_mul, norm_mul, hP₂, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, mul_one]; gcongr; exact hds 1
    have n3 : ‖(V₂ : ℂ) * ((s 2 - sc 2 : ℝ) : ℂ)‖ ≤ |V₂| * ds 2 := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]; gcongr; exact hds 2
    have n4 : ‖(V₀ : ℂ) * (s 0 : ℂ) * (w₁ - P₁)‖ ≤ |V₀| * sh 0 * ε₁ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hss 0) (abs_nonneg _)) hε₁ (norm_nonneg _)
        (mul_nonneg (abs_nonneg _) (hsh 0))
    have n5 : ‖(V₁ : ℂ) * (s 1 : ℂ) * (w₂ - P₂)‖ ≤ |V₁| * sh 1 * ε₂ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hss 1) (abs_nonneg _)) hε₂ (norm_nonneg _)
        (mul_nonneg (abs_nonneg _) (hsh 1))
    calc _ ≤ ‖(V₀ : ℂ) * ((s 0 - sc 0 : ℝ) : ℂ) * P₁‖ + ‖(V₁ : ℂ) * ((s 1 - sc 1 : ℝ) : ℂ) * P₂‖ +
          ‖(V₂ : ℂ) * ((s 2 - sc 2 : ℝ) : ℂ)‖ + ‖(V₀ : ℂ) * (s 0 : ℂ) * (w₁ - P₁)‖ +
          ‖(V₁ : ℂ) * (s 1 : ℂ) * (w₂ - P₂)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ R := by rw [hRdef]; linarith
  have hz : z = zc + δ := by rw [hδ]; ring
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
  constructor
  · rw [hz, normSq_add_rdot, Complex.normSq_eq_norm_sq δ]
    have h1 : ‖δ‖ ^ 2 ≤ R * R := by rw [sq]; exact mul_self_le_mul_self (norm_nonneg δ) hR
    have h2 : 2 * rdot zc δ ≤ 2 * E :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hE) (by norm_num)
    exact add_le_add (add_le_add le_rfl h2) h1
  · intro hG hEG
    have hlin : rdot zc z = Complex.normSq zc + rdot zc δ := by
      rw [hz, ← rdot_self]; simp only [rdot, Complex.add_re, Complex.add_im]; ring
    have h1 : Complex.normSq zc - E ≤ rdot zc z := by
      rw [hlin]; linarith [neg_abs_le (rdot zc δ)]
    have h2 : |rdot zc z| ≤ ‖zc‖ * ‖z‖ := abs_rdot_le _ _
    have h3 : (rdot zc z) ^ 2 ≤ (‖zc‖ * ‖z‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h4 : (‖zc‖ * ‖z‖) ^ 2 = Complex.normSq z * Complex.normSq zc := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; ring
    have h0 : 0 ≤ Complex.normSq zc - E := sub_nonneg.mpr hEG
    calc (Complex.normSq zc - E) * (Complex.normSq zc - E) ≤ rdot zc z * rdot zc z :=
          mul_self_le_mul_self h0 h1
      _ = (rdot zc z) ^ 2 := by ring
      _ ≤ (‖zc‖ * ‖z‖) ^ 2 := h3
      _ = _ := h4

/-- Eccentricity bounds from `Γ` bounds: with `u = 1 - Γ/Λ`, if `0 ≤ 1 - Γ_hi/Λ`,
`(1 - Γ_lo/Λ)² ≤ 1 - lo²` and `1 - hi² ≤ (1 - Γ_hi/Λ)²`, then `Γ ∈ [Γ_lo, Γ_hi]` gives
`lo ≤ √(1 - u²) ≤ hi`. -/
theorem ecc_bounds_of_gamma {Λ Γ Glo Ghi lo hi : ℝ} (hΛ : 0 < Λ) (hhi : 0 ≤ hi)
    (h1 : Glo ≤ Γ) (h2 : Γ ≤ Ghi) (hu : 0 ≤ 1 - Ghi / Λ)
    (hl : (1 - Glo / Λ) ^ 2 ≤ 1 - lo ^ 2) (hh : 1 - hi ^ 2 ≤ (1 - Ghi / Λ) ^ 2) :
    lo ≤ Real.sqrt (1 - (1 - Γ / Λ) ^ 2) ∧ Real.sqrt (1 - (1 - Γ / Λ) ^ 2) ≤ hi := by
  have hu1 : 1 - Ghi / Λ ≤ 1 - Γ / Λ := by
    have : Γ / Λ ≤ Ghi / Λ := div_le_div_of_nonneg_right h2 hΛ.le
    linarith
  have hu2 : 1 - Γ / Λ ≤ 1 - Glo / Λ := by
    have : Glo / Λ ≤ Γ / Λ := div_le_div_of_nonneg_right h1 hΛ.le
    linarith
  have hu0 : 0 ≤ 1 - Γ / Λ := le_trans hu hu1
  constructor
  · apply Real.le_sqrt_of_sq_le
    have : (1 - Γ / Λ) ^ 2 ≤ (1 - Glo / Λ) ^ 2 := pow_le_pow_left₀ hu0 hu2 2
    linarith
  · rw [show hi = Real.sqrt (hi ^ 2) from (Real.sqrt_sq hhi).symm]
    apply Real.sqrt_le_sqrt
    have : (1 - Ghi / Λ) ^ 2 ≤ (1 - Γ / Λ) ^ 2 := pow_le_pow_left₀ hu hu1 2
    linarith

end KAM.EffectiveStability.Tube

end
