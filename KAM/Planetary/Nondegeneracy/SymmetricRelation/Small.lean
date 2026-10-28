/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs

/-!
# Symmetric relation product: purely spectral cases

Blueprint P, Part 10 (`stepP:p10:F-B`, `stepP:p10:F-C` Subcase C2): when `c' = 0` and only one
`c''_d` is nonzero, `F_c` vanishes nowhere on `𝒜_n` (all `σ_l < 0`); when `c' = 0` and `n = 2`
with both `c''` nonzero, `F_c ≠ 0` for `σ_2/σ_1` small (Proposition `bpP:p10:n2`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

lemma relation_of_fast_zero (D : Data n) {c : Vec n × Vec n} (h1 : c.1 = 0)
    (p : Equiv.Perm (Fin n)) (a : Vec n) :
    relation D c p a = ∑ j, c.2 j * sigma D a (p j) := by
  simp [relation, h1]

/-- Subcase C2: a single nonzero `c''_d`. -/
theorem fc_ne_zero_single (D : Data n) (hn : 2 ≤ n) {c : Vec n × Vec n} (h1 : c.1 = 0)
    {d : Fin n} (hd : c.2 d ≠ 0) (h2 : ∀ j, j ≠ d → c.2 j = 0) :
    ∃ a ∈ axes n, fc_def D c a ≠ 0 := by
  obtain ⟨a, ha⟩ := (isConnected_axes n).nonempty
  refine ⟨a, ha, Finset.prod_ne_zero_iff.2 fun p _ => ?_⟩
  rw [relation_of_fast_zero D h1, Finset.sum_eq_single d (fun j _ hj => by rw [h2 j hj, zero_mul])
    (fun h => absurd (Finset.mem_univ d) h)]
  exact mul_ne_zero hd (sigma_neg D hn ha _).ne

/-- The signs and the size of `s = σ₂/σ₁` that keep both relation forms nonzero. -/
lemma two_forms_ne {u v s σ0 : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hσ : σ0 ≠ 0) (hs : 0 < s)
    (hsd : s * (|u| + |v|) < min |u| |v|) :
    σ0 * (u + v * s) ≠ 0 ∧ σ0 * (v + u * s) ≠ 0 := by
  have hu' := abs_pos.2 hu
  have hv' := abs_pos.2 hv
  have m1 : min |u| |v| ≤ |u| := min_le_left _ _
  have m2 : min |u| |v| ≤ |v| := min_le_right _ _
  refine ⟨mul_ne_zero hσ fun h => ?_, mul_ne_zero hσ fun h => ?_⟩
  · have : u = -(v * s) := by linarith
    have h3 : |u| = |v| * s := by rw [this, abs_neg, abs_mul, abs_of_pos hs]
    nlinarith
  · have : v = -(u * s) := by linarith
    have h3 : |v| = |u| * s := by rw [this, abs_neg, abs_mul, abs_of_pos hs]
    nlinarith

/-- `stepP:p10:F-B`: on `𝒜₂` the ratio `σ₂/σ₁` is arbitrarily small (Proposition `bpP:p10:n2`). -/
lemma exists_small_ratio (D : Data 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a ∈ axes 2, 0 < sigma D a 1 / sigma D a 0 ∧ sigma D a 1 / sigma D a 0 < δ := by
  have hm0 := D.hm 0
  have hm1 := D.hm 1
  have hGm : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  set q : ℝ := 1 + 1 / δ with hq
  have hqp : 0 < q := by positivity
  set R : ℝ := D.m 1 / D.m 0 with hR
  have hRp : 0 < R := by positivity
  set a0 : ℝ := min (1 / 2) ((R / q) ^ 2) with ha0
  have ha0p : 0 < a0 := lt_min (by norm_num) (by positivity)
  have ha : (![a0, 1] : Vec 2) ∈ axes 2 := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ha0p]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨-, h2, h3, -⟩ := n2 D ha
  have hsa : √a0 ≤ R / q := by
    calc √a0 ≤ √((R / q) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = R / q := Real.sqrt_sq (by positivity)
  have hsp : 0 < √a0 := Real.sqrt_pos.2 ha0p
  have hr : q ≤ action D ![a0, 1] 1 / action D ![a0, 1] 0 := by
    have hw : 0 < √(D.G * D.m0) := Real.sqrt_pos.2 hGm
    have e : action D ![a0, 1] 1 / action D ![a0, 1] 0 = R / √a0 := by
      simp only [action, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
        Real.sqrt_mul hGm.le, hR]
      field_simp
    rw [e, le_div_iff₀ hsp]
    have := (le_div_iff₀ hqp).1 hsa
    linarith
  have hx : 1 / δ < sigma D ![a0, 1] 0 / sigma D ![a0, 1] 1 := by
    have : q - 1 = 1 / δ := by rw [hq]; ring
    linarith
  have hxp : 0 < sigma D ![a0, 1] 0 / sigma D ![a0, 1] 1 := lt_trans (by positivity) hx
  have hinv : sigma D ![a0, 1] 1 / sigma D ![a0, 1] 0 =
      (sigma D ![a0, 1] 0 / sigma D ![a0, 1] 1)⁻¹ := (inv_div _ _).symm
  refine ⟨_, ha, ?_, ?_⟩
  · rw [hinv]; exact inv_pos.2 hxp
  · rw [hinv, inv_lt_comm₀ hxp hδ]
    simpa using hx

/-- `stepP:p10:F-B`: `c' = 0`, `n = 2`, both `c''` nonzero. -/
theorem fc_ne_zero_two (D : Data 2) {c : Vec 2 × Vec 2} (h1 : c.1 = 0) (hu : c.2 0 ≠ 0)
    (hv : c.2 1 ≠ 0) : ∃ a ∈ axes 2, fc_def D c a ≠ 0 := by
  have hu' := abs_pos.2 hu
  have hv' := abs_pos.2 hv
  set δ : ℝ := min |c.2 0| |c.2 1| / (|c.2 0| + |c.2 1|) with hδ
  have hδp : 0 < δ := by positivity
  obtain ⟨a, ha, hs0, hsδ⟩ := exists_small_ratio D hδp
  refine ⟨a, ha, Finset.prod_ne_zero_iff.2 fun p _ => ?_⟩
  have hσ0 : sigma D a 0 ≠ 0 := (sigma_neg D le_rfl ha 0).ne
  have hσ1 : sigma D a 1 ≠ 0 := (sigma_neg D le_rfl ha 1).ne
  have hsd : sigma D a 1 / sigma D a 0 * (|c.2 0| + |c.2 1|) < min |c.2 0| |c.2 1| := by
    have := mul_lt_mul_of_pos_right hsδ (by positivity : 0 < |c.2 0| + |c.2 1|)
    rwa [hδ, div_mul_cancel₀ _ (by positivity)] at this
  obtain ⟨f1, f2⟩ := two_forms_ne hu hv hσ0 hs0 hsd
  have hp : (p 0 = 0 ∧ p 1 = 1) ∨ (p 0 = 1 ∧ p 1 = 0) := by
    have := p.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
    revert this
    generalize p 0 = x
    generalize p 1 = y
    fin_cases x <;> fin_cases y <;> simp
  rw [relation_of_fast_zero D h1, Fin.sum_univ_two]
  rcases hp with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [e0, e1]
    have : c.2 0 * sigma D a 0 + c.2 1 * sigma D a 1 =
        sigma D a 0 * (c.2 0 + c.2 1 * (sigma D a 1 / sigma D a 0)) := by
      field_simp
    rw [this]; exact f1
  · rw [e0, e1]
    have : c.2 0 * sigma D a 1 + c.2 1 * sigma D a 0 =
        sigma D a 0 * (c.2 1 + c.2 0 * (sigma D a 1 / sigma D a 0)) := by
      field_simp
      ring
    rw [this]; exact f2

end Nondegeneracy
end KAM.Planetary
end
