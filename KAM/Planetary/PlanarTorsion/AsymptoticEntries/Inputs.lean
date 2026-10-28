/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading
public import KAM.Planetary.PlanarTorsion.SpectralAdapter

/-!
# Planar quartic torsion: the entries of `Q` at hierarchical axes (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-in`): at the axes
`a = ![α, 1]` the secular quadratic form satisfies `Q₁₁ = -(3 G m₂ / (8 √κ)) α ^ (3/2) (1 + O(α²))`,
`Q₂₂ = -(3 G m₁ / (8 √κ)) α ^ 2 (1 + O(α²))`, `Q₁₂ = O(α ^ (11/4))`, and the difference
`Δ_Q = Q₁₁ - Q₂₂` equals `Q₁₁ (1 + O(α ^ (1/2)))` and is negative for small `α`.
The relative errors are kept in the absolute form `leading + O(α ^ (leading exponent + 2))`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

variable (p : PlanarData)

theorem p11cAe_Q00 (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_Q p ![α, 1] 0 0 =
      -(p.G * p.m 1 / (4 * √p.kappa)) * (√α * p11c_laplace (3 / 2) 1 α) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ α = t ^ 2 := ⟨√α, Real.sqrt_pos.2 hα, (sq_sqrt hα.le).symm⟩
  simp only [p11c_Q, PlanarData.actions, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    div_one, mul_one]
  rw [Real.sqrt_mul hk.le, Real.sqrt_sq ht.le]
  field_simp

theorem p11cAe_Q11 (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_Q p ![α, 1] 1 1 = -(p.G * p.m 0 / (4 * √p.kappa)) * (α * p11c_laplace (3 / 2) 1 α) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm1 := hp.2.2 1
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  simp only [p11c_Q, PlanarData.actions, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    div_one, mul_one]
  field_simp

theorem p11cAe_Q01 (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_Q p ![α, 1] 0 1 = (p.G * p.m 0 * p.m 1 / (4 * √(p.m 0 * p.m 1 * p.kappa))) *
      ((α * p11c_laplace (3 / 2) 2 α) * α ^ (-(1 / 4) : ℝ)) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hI : p.actions ![α, 1] 0 * p.actions ![α, 1] 1 = p.m 0 * p.m 1 * p.kappa * α ^ (1 / 2 : ℝ) := by
    simp only [PlanarData.actions, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_one]
    rw [Real.sqrt_mul hk.le, ← Real.sqrt_eq_rpow]
    have : √p.kappa * √p.kappa = p.kappa := Real.mul_self_sqrt hk.le
    calc _ = p.m 0 * p.m 1 * (√p.kappa * √p.kappa) * √α := by ring
      _ = _ := by rw [this]
  have hs : √(p.actions ![α, 1] 0 * p.actions ![α, 1] 1) =
      √(p.m 0 * p.m 1 * p.kappa) * α ^ (1 / 4 : ℝ) := by
    rw [hI, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (α ^ (1 / 2 : ℝ)), ← Real.rpow_mul hα.le]
    norm_num
  have hpos : 0 < √(p.m 0 * p.m 1 * p.kappa) := Real.sqrt_pos.2 (by positivity)
  simp only [p11c_Q, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    div_one, mul_one]
  rw [hs, Real.rpow_neg hα.le]
  have : 0 < α ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hα _
  field_simp

/-! ### Big-O bounds -/

theorem p11cAe_id : (fun a : ℝ => a) =O[𝓝[>] 0] fun a : ℝ => a ^ (1 : ℝ) := by
  simpa using isBigO_refl (fun a : ℝ => a) (𝓝[>] 0)

theorem p11cAe_sqrt_isBigO : (fun a : ℝ => √a) =O[𝓝[>] 0] fun a : ℝ => a ^ (1 / 2 : ℝ) := by
  rw [p11cAe_sqrt]

theorem p11cAe_rpow_isBigO_of_lower {f : ℝ → ℝ} {k r : ℝ} (hk : 0 < k)
    (h : ∀ᶠ a : ℝ in 𝓝[>] 0, k * a ^ r ≤ -f a) :
    (fun a : ℝ => a ^ r) =O[𝓝[>] 0] f := by
  refine IsBigO.of_bound (1 / k) ?_
  filter_upwards [h, p11cAe_pos] with a ha h0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), one_div_mul_eq_div, le_div_iff₀ hk]
  have : -f a ≤ ‖f a‖ := by rw [Real.norm_eq_abs]; exact neg_le_abs _
  nlinarith [Real.rpow_nonneg h0.le r]

theorem p11cAe_lead_isBigO {f : ℝ → ℝ} {c r s : ℝ} (hrs : r ≤ s)
    (h : (fun a => f a - c * a ^ r) =O[𝓝[>] 0] fun a : ℝ => a ^ s) :
    f =O[𝓝[>] 0] fun a : ℝ => a ^ r :=
  ((h.trans (p11cAe_rpow_isBigO hrs)).add (p11cAe_const_mul c r)).congr_left fun a => by ring

theorem p11cAe_b1_lead : (fun a => p11c_laplace (3 / 2) 1 a) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (1 : ℝ) :=
  p11cAe_lead_isBigO (c := 3 / 2) (r := 1) (s := 3) (by norm_num) (by simpa using p11cAe_b1)

theorem p11cAe_b2_lead : (fun a => p11c_laplace (3 / 2) 2 a) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (2 : ℝ) :=
  p11cAe_lead_isBigO (c := 15 / 8) (r := 2) (s := 4) (by norm_num) (by simpa using p11cAe_b2)

theorem p11cAe_lead_isBigO' {f : ℝ → ℝ} {c r s : ℝ} (hrs : r ≤ s)
    (h : (fun a => f a + c * a ^ r) =O[𝓝[>] 0] fun a : ℝ => a ^ s) :
    f =O[𝓝[>] 0] fun a : ℝ => a ^ r :=
  ((h.trans (p11cAe_rpow_isBigO hrs)).add ((p11cAe_const_mul (-c) r))).congr_left
    fun a => by ring

theorem p11cAe_congr_exp {f : ℝ → ℝ} {r s : ℝ} (h : r = s)
    (hf : f =O[𝓝[>] 0] fun a : ℝ => a ^ r) : f =O[𝓝[>] 0] fun a : ℝ => a ^ s := by
  subst h; exact hf

theorem p11cAe_rpow_three_half {α : ℝ} (hα : 0 < α) : α ^ (3 / 2 : ℝ) = α * √α := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hα.le (by norm_num)]
  norm_num

/-- `bpP:p11b:asymptotics`, step `as-in`: the entries of `Q` at `a = ![α, 1]`. -/
theorem as_in (hp : p.Valid) :
    (fun α => p11c_Q p ![α, 1] 0 0 + 3 * p.G * p.m 1 / (8 * √p.kappa) * α ^ (3 / 2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_Q p ![α, 1] 1 1 + 3 * p.G * p.m 0 / (8 * √p.kappa) * α ^ (2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_Q p ![α, 1] 0 1) =O[𝓝[>] 0] (fun α : ℝ => α ^ (11 / 4 : ℝ)) ∧
      (∀ᶠ α : ℝ in 𝓝[>] 0, p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1 < 0) ∧
      (fun α => (p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) / p11c_Q p ![α, 1] 0 0 - 1)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (1 / 2 : ℝ)) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  have hk1 : 0 < 3 * p.G * p.m 1 / (8 * √p.kappa) := by
    have := hp.2.2 1; have := hp.1; positivity
  have hk2 : 0 < 3 * p.G * p.m 0 / (8 * √p.kappa) := by
    have := hp.2.2 0; have := hp.1; positivity
  have P1 : (fun α => p11c_Q p ![α, 1] 0 0 + 3 * p.G * p.m 1 / (8 * √p.kappa) * α ^ (3 / 2 : ℝ))
      =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) := by
    have h := p11cAe_mul p11cAe_sqrt_isBigO p11cAe_b1
    have h' := p11cAe_congr_exp (s := 7 / 2) (by norm_num)
      (h.const_mul_left (-(p.G * p.m 1 / (4 * √p.kappa))))
    refine h'.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [p11cAe_Q00 p hp ha, p11cAe_rpow_three_half ha]
    ring
  have P2 : (fun α => p11c_Q p ![α, 1] 1 1 + 3 * p.G * p.m 0 / (8 * √p.kappa) * α ^ (2 : ℝ))
      =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) := by
    have h := p11cAe_mul p11cAe_id p11cAe_b1
    have h' := p11cAe_congr_exp (s := 4) (by norm_num)
      (h.const_mul_left (-(p.G * p.m 0 / (4 * √p.kappa))))
    refine h'.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [p11cAe_Q11 p hp ha, Real.rpow_two]
    ring
  have P3 : (fun α => p11c_Q p ![α, 1] 0 1) =O[𝓝[>] 0] (fun α : ℝ => α ^ (11 / 4 : ℝ)) := by
    have h := p11cAe_mul (p11cAe_mul p11cAe_id p11cAe_b2_lead)
      (isBigO_refl (fun a : ℝ => a ^ (-(1 / 4) : ℝ)) (𝓝[>] 0))
    have h' := p11cAe_congr_exp (s := 11 / 4) (by norm_num)
      (h.const_mul_left (p.G * p.m 0 * p.m 1 / (4 * √(p.m 0 * p.m 1 * p.kappa))))
    refine h'.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    exact (p11cAe_Q01 p hp ha).symm
  have hQ11 : (fun α => p11c_Q p ![α, 1] 1 1) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 3 * p.G * p.m 0 / (8 * √p.kappa)) (by norm_num) P2
  have hlow0 := p11cAe_lower hk1 (by norm_num : (3 / 2 : ℝ) < 7 / 2) P1
  have P1' : (fun α => (p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) +
      3 * p.G * p.m 1 / (8 * √p.kappa) * α ^ (3 / 2 : ℝ)) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    ((P1.trans (p11cAe_rpow_isBigO (by norm_num : (2 : ℝ) ≤ 7 / 2))).sub hQ11).congr_left
      fun a => by ring
  have hlow := p11cAe_lower hk1 (by norm_num : (3 / 2 : ℝ) < 2) P1'
  have P4 : ∀ᶠ α : ℝ in 𝓝[>] 0, p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1 < 0 := by
    filter_upwards [hlow, p11cAe_pos] with a ha h0
    have : 0 < 3 * p.G * p.m 1 / (8 * √p.kappa) / 2 * a ^ (3 / 2 : ℝ) :=
      mul_pos (half_pos hk1) (Real.rpow_pos_of_pos h0 _)
    linarith
  have hQ00 : (fun a : ℝ => a ^ (3 / 2 : ℝ)) =O[𝓝[>] 0] fun a => p11c_Q p ![a, 1] 0 0 :=
    p11cAe_rpow_isBigO_of_lower (half_pos hk1) hlow0
  have hinv := hQ00.inv_rev (by
    filter_upwards [p11cAe_pos] with a h0 h
    exact absurd h (Real.rpow_pos_of_pos h0 _).ne')
  have hinv' : (fun a => (p11c_Q p ![a, 1] 0 0)⁻¹) =O[𝓝[>] 0]
      fun a : ℝ => a ^ (-(3 / 2) : ℝ) :=
    hinv.congr' EventuallyEq.rfl (p11cAe_pos.mono fun a ha => by
      exact (Real.rpow_neg ha.le _).symm)
  have P5 := p11cAe_congr_exp (s := 1 / 2) (by norm_num) (p11cAe_mul hQ11.neg_left hinv')
  refine ⟨P1, P2, P3, P4, P5.congr' ?_ EventuallyEq.rfl⟩
  filter_upwards [hlow0, p11cAe_pos] with a ha h0
  have : 0 < 3 * p.G * p.m 1 / (8 * √p.kappa) / 2 * a ^ (3 / 2 : ℝ) :=
    mul_pos (half_pos hk1) (Real.rpow_pos_of_pos h0 _)
  have hne : p11c_Q p ![a, 1] 0 0 ≠ 0 := by intro h; rw [h] at ha; linarith
  field_simp
  ring

end KAM.Planetary

end
