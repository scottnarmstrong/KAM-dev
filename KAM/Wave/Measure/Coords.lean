/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Nondegeneracy
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# W7: unperturbed frequencies and frequency coordinates (blueprint `bpW:w7:freqcoords`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

The unperturbed tangential frequency is `omegaTan m hm ξ = λ_J + A ξ` and the normal one is
`omegaNor m hm ξ ν = λ_{ν+3} + (B ξ)_ν` (landed in `KAM.Wave.Normal.Nondegeneracy`). Here we prove
Lemma `bpW:w7:freqcoords`: the constants `D_A = |det A|`, `N_A = ‖A‖_∞`, `L_A = ‖A⁻¹‖_∞`, the
identity `Ω⁰_ν = λ_ν + (4/(7 λ_ν)) s` with `s = ⟨λ_J, ω⁰ - λ_J⟩`, the Lebesgue measure scaling
under `ω⁰`, and the distance bounds.
-/

@[expose] public noncomputable section

open Real MeasureTheory

namespace KAM.Wave

/-- `D_A = 63 / (64 π² λ₁² λ₂²)` (blueprint `bpW:w7:freqcoords` (i)). -/
def measDA (m : ℝ) (hm : 0 < m) : ℝ :=
  63 / (64 * π ^ 2 * lamTan m hm 0 ^ 2 * lamTan m hm 1 ^ 2)

/-- `N_A = (3/(8π)) (3/λ₁² + 4/(λ₁λ₂))` (blueprint `bpW:w7:freqcoords` (ii)). -/
def measNA (m : ℝ) (hm : 0 < m) : ℝ :=
  3 / (8 * π) * (3 / lamTan m hm 0 ^ 2 + 4 / (lamTan m hm 0 * lamTan m hm 1))

/-- `L_A = (8π/21) λ₂ (4λ₁ + 3λ₂)` (blueprint `bpW:w7:freqcoords` (ii)). -/
def measLA (m : ℝ) (hm : 0 < m) : ℝ :=
  8 * π / 21 * lamTan m hm 1 * (4 * lamTan m hm 0 + 3 * lamTan m hm 1)

/-- The sup-norm of the tangential frequency difference, in the notation `|ω⁰ ξ - ω⁰ ξ'|_∞`. -/
def measS (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, lamTan m hm i * (omegaTan m hm ξ i - lamTan m hm i)

section basic

variable (m : ℝ) (hm : 0 < m)

theorem measLam_facts :
    1 < lamTan m hm 0 ∧ lamTan m hm 0 < lamTan m hm 1 ∧ 2 < lamTan m hm 1 := by
  have p0 := lamTan_pos m hm 0
  have p1 := lamTan_pos m hm 1
  have q0 := lamTan_zero_sq m hm
  have q1 := lamTan_one_sq m hm
  have g0 : 1 < lamTan m hm 0 := by nlinarith
  exact ⟨g0, by nlinarith, by nlinarith⟩

theorem measDA_pos : 0 < measDA m hm := by
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  unfold measDA
  positivity

theorem measDA_eq_abs_det : measDA m hm = |(actionAMat m hm).det| := by
  have h := (det_actionA m hm).2.1
  rw [h, measDA, abs_neg, abs_of_pos]
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  positivity

theorem measNA_pos : 0 < measNA m hm := by
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  unfold measNA
  positivity

theorem measLA_pos : 0 < measLA m hm := by
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  unfold measLA
  positivity

/-- `L_A = N_A / D_A`. -/
theorem measLA_eq : measLA m hm = measNA m hm / measDA m hm := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold measLA measNA measDA
  field_simp
  ring

theorem measNA_lt : measNA m hm < 3 / 5 := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hpi := Real.pi_gt_d2
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have e1 : 3 / lamTan m hm 0 ^ 2 < 3 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have e2 : 4 / (lamTan m hm 0 * lamTan m hm 1) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  unfold measNA
  have : 3 / (8 * π) * (3 / lamTan m hm 0 ^ 2 + 4 / (lamTan m hm 0 * lamTan m hm 1))
      < 3 / (8 * π) * 5 := by
    apply mul_lt_mul_of_pos_left (by linarith) (by positivity)
  refine this.trans ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- The affine bijection's linear part. -/
def measAlin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (actionAMat m hm)

theorem measAlin_apply (ξ : Fin 2 → ℝ) (i : Fin 2) :
    measAlin m hm ξ i = ∑ i', actionA m hm i i' * ξ i' := by
  simp [measAlin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, actionAMat]

theorem omegaTan_eq (ξ : Fin 2 → ℝ) :
    omegaTan m hm ξ = (fun i => lamTan m hm i) + measAlin m hm ξ := by
  funext i
  simp [omegaTan, measAlin_apply]

theorem det_measAlin : LinearMap.det (measAlin m hm) = (actionAMat m hm).det := by
  simp [measAlin, LinearMap.det_toLin']

/-- The unperturbed tangential frequency map is injective. -/
theorem omegaTan_sub (ξ ξ' : Fin 2 → ℝ) :
    omegaTan m hm ξ - omegaTan m hm ξ' = measAlin m hm (ξ - ξ') := by
  rw [omegaTan_eq, omegaTan_eq, map_sub]; abel

theorem omegaTan_sub_apply (ξ ξ' : Fin 2 → ℝ) (i : Fin 2) :
    omegaTan m hm ξ i - omegaTan m hm ξ' i = ∑ i', actionA m hm i i' * (ξ i' - ξ' i') := by
  have := congrFun (omegaTan_sub m hm ξ ξ') i
  rw [Pi.sub_apply, measAlin_apply] at this
  simpa using this

/-- Lebesgue measure scales by `D_A` under `ω⁰`. -/
theorem measure_omegaTan_image (F : Set (Fin 2 → ℝ)) :
    volume (omegaTan m hm '' F) = ENNReal.ofReal (measDA m hm) * volume F := by
  have h1 : omegaTan m hm '' F =
      (fun x => x + (-(fun i => lamTan m hm i : Fin 2 → ℝ))) ⁻¹' (measAlin m hm '' F) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [omegaTan_eq]; abel⟩
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, ?_⟩
      rw [omegaTan_eq, h]; abel
  rw [h1, measure_preimage_add_right, Measure.addHaar_image_linearMap, det_measAlin,
    ← measDA_eq_abs_det]

/-- `s = (21/(8π)) ⟨b, ξ⟩`. -/
theorem measS_eq (ξ : Fin 2 → ℝ) :
    measS m hm ξ = 21 / (8 * π) * (ξ 0 / lamTan m hm 0 + ξ 1 / lamTan m hm 1) := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  simp only [measS, Fin.sum_univ_two, omegaTan, actionA]
  simp
  field_simp
  ring

/-- `Ω⁰_ν = λ_ν + (4/(7 λ_ν)) s` (blueprint `bpW:w7:freqcoords` (iii)). -/
theorem omegaNor_eq (ξ : Fin 2 → ℝ) (ν : ℕ) :
    omegaNor m hm ξ ν = lamN m hm ν + 4 / (7 * lamN m hm ν) * measS m hm ξ := by
  have h0 := (lamTan_pos m hm 0).ne'
  have h1 := (lamTan_pos m hm 1).ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hN : lamN m hm ν ≠ 0 := by linarith [lamN_gt m hm ν]
  rw [measS_eq]
  simp only [omegaNor, Fin.sum_univ_two, actionBN]
  field_simp
  ring

/-- Lipschitz bound of `s` in the frequency coordinate. -/
theorem abs_measS_sub_le (ξ ξ' : Fin 2 → ℝ) :
    |measS m hm ξ - measS m hm ξ'| ≤
      (lamTan m hm 0 + lamTan m hm 1) * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have e : measS m hm ξ - measS m hm ξ' =
      ∑ i, lamTan m hm i * (omegaTan m hm ξ i - omegaTan m hm ξ' i) := by
    simp only [measS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e, Fin.sum_univ_two]
  have a0 : |omegaTan m hm ξ 0 - omegaTan m hm ξ' 0| ≤ ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
    have := norm_le_pi_norm (omegaTan m hm ξ - omegaTan m hm ξ') 0
    simpa using this
  have a1 : |omegaTan m hm ξ 1 - omegaTan m hm ξ' 1| ≤ ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
    have := norm_le_pi_norm (omegaTan m hm ξ - omegaTan m hm ξ') 1
    simpa using this
  calc _ ≤ |lamTan m hm 0 * (omegaTan m hm ξ 0 - omegaTan m hm ξ' 0)| +
        |lamTan m hm 1 * (omegaTan m hm ξ 1 - omegaTan m hm ξ' 1)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos hl0, abs_of_pos hl1]
      nlinarith [mul_le_mul_of_nonneg_left a0 hl0.le, mul_le_mul_of_nonneg_left a1 hl1.le]

/-- `|ω⁰ ξ - ω⁰ ξ'|_∞ ≤ N_A |ξ - ξ'|_∞`. -/
theorem norm_omegaTan_sub_le (ξ ξ' : Fin 2 → ℝ) :
    ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ measNA m hm * ‖ξ - ξ'‖ := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have hNA := measNA_pos m hm
  have hd : ∀ i, |(ξ - ξ') i| ≤ ‖ξ - ξ'‖ := fun i => by
    simpa using norm_le_pi_norm (ξ - ξ') i
  have hpi := Real.pi_pos
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply, omegaTan_sub_apply, Fin.sum_univ_two]
  have hA00 : |actionA m hm i 0| + |actionA m hm i 1| ≤ measNA m hm := by
    fin_cases i
    · simp only [actionA, measNA]
      simp
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      apply le_of_eq; field_simp; ring
    · simp only [actionA, measNA]
      simp
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      have h3 : 3 / lamTan m hm 1 ^ 2 ≤ 3 / lamTan m hm 0 ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith
      have h4 : 3 / (2 * π * lamTan m hm 1 * lamTan m hm 0) =
          3 / (8 * π) * (4 / (lamTan m hm 0 * lamTan m hm 1)) := by
        field_simp; ring
      have h5 : 9 / (8 * π * lamTan m hm 1 ^ 2) = 3 / (8 * π) * (3 / lamTan m hm 1 ^ 2) := by
        field_simp; ring
      rw [h4, h5, ← mul_add]
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc |actionA m hm i 0 * (ξ 0 - ξ' 0) + actionA m hm i 1 * (ξ 1 - ξ' 1)|
      ≤ |actionA m hm i 0 * (ξ 0 - ξ' 0)| + |actionA m hm i 1 * (ξ 1 - ξ' 1)| := abs_add_le _ _
    _ = |actionA m hm i 0| * |(ξ - ξ') 0| + |actionA m hm i 1| * |(ξ - ξ') 1| := by
      rw [abs_mul, abs_mul]; rfl
    _ ≤ |actionA m hm i 0| * ‖ξ - ξ'‖ + |actionA m hm i 1| * ‖ξ - ξ'‖ := by
      gcongr <;> exact hd _
    _ ≤ _ := by rw [← add_mul]; exact mul_le_mul_of_nonneg_right hA00 (norm_nonneg _)

/-- `|ξ - ξ'|_∞ ≤ L_A |ω⁰ ξ - ω⁰ ξ'|_∞`. -/
theorem norm_sub_le_measLA_mul (ξ ξ' : Fin 2 → ℝ) :
    ‖ξ - ξ'‖ ≤ measLA m hm * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have h0 := hl0.ne'
  have h1 := hl1.ne'
  have hpi := Real.pi_pos
  have hpi' : π ≠ 0 := Real.pi_ne_zero
  have hLA := measLA_pos m hm
  set d := omegaTan m hm ξ - omegaTan m hm ξ' with hd
  have hd0 : |d 0| ≤ ‖d‖ := by simpa using norm_le_pi_norm d 0
  have hd1 : |d 1| ≤ ‖d‖ := by simpa using norm_le_pi_norm d 1
  have e0 : d 0 = actionA m hm 0 0 * (ξ 0 - ξ' 0) + actionA m hm 0 1 * (ξ 1 - ξ' 1) := by
    rw [hd, Pi.sub_apply, omegaTan_sub_apply, Fin.sum_univ_two]
  have e1 : d 1 = actionA m hm 1 0 * (ξ 0 - ξ' 0) + actionA m hm 1 1 * (ξ 1 - ξ' 1) := by
    rw [hd, Pi.sub_apply, omegaTan_sub_apply, Fin.sum_univ_two]
  simp only [actionA] at e0 e1
  simp at e0 e1
  have i0 : ξ 0 - ξ' 0 = 8 * π / 21 *
      (-3 * lamTan m hm 0 ^ 2 * d 0 + 4 * lamTan m hm 0 * lamTan m hm 1 * d 1) := by
    rw [e0, e1]; field_simp; ring
  have i1 : ξ 1 - ξ' 1 = 8 * π / 21 *
      (4 * lamTan m hm 0 * lamTan m hm 1 * d 0 - 3 * lamTan m hm 1 ^ 2 * d 1) := by
    rw [e0, e1]; field_simp; ring
  have hdn := norm_nonneg d
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [i0, abs_mul, abs_of_pos (by positivity)]
    have : |-3 * lamTan m hm 0 ^ 2 * d 0 + 4 * lamTan m hm 0 * lamTan m hm 1 * d 1| ≤
        (3 * lamTan m hm 0 ^ 2 + 4 * lamTan m hm 0 * lamTan m hm 1) * ‖d‖ := by
      calc _ ≤ |-3 * lamTan m hm 0 ^ 2 * d 0| + |4 * lamTan m hm 0 * lamTan m hm 1 * d 1| :=
            abs_add_le _ _
        _ = 3 * lamTan m hm 0 ^ 2 * |d 0| + 4 * lamTan m hm 0 * lamTan m hm 1 * |d 1| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            rw [abs_of_neg (by norm_num : (-3 : ℝ) < 0), abs_of_pos (by positivity : 0 < lamTan m hm 0 ^ 2),
              abs_of_pos (by positivity : 0 < 4 * lamTan m hm 0), abs_of_pos hl1]
            ring
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd0 (by positivity : 0 ≤ 3 * lamTan m hm 0 ^ 2),
              mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ 4 * lamTan m hm 0 * lamTan m hm 1)]
    calc 8 * π / 21 * _ ≤ 8 * π / 21 * ((3 * lamTan m hm 0 ^ 2 + 4 * lamTan m hm 0 * lamTan m hm 1)
          * ‖d‖) := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ measLA m hm * ‖d‖ := by
          unfold measLA
          have : 3 * lamTan m hm 0 ^ 2 + 4 * lamTan m hm 0 * lamTan m hm 1 ≤
              lamTan m hm 1 * (4 * lamTan m hm 0 + 3 * lamTan m hm 1) := by nlinarith
          have h2 := mul_le_mul_of_nonneg_right this hdn
          have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 8 * π / 21)
          calc _ = 8 * π / 21 * ((3 * lamTan m hm 0 ^ 2 + 4 * lamTan m hm 0 * lamTan m hm 1) * ‖d‖) := by ring
            _ ≤ _ := h3
            _ = _ := by ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [i1, abs_mul, abs_of_pos (by positivity)]
    have : |4 * lamTan m hm 0 * lamTan m hm 1 * d 0 - 3 * lamTan m hm 1 ^ 2 * d 1| ≤
        (4 * lamTan m hm 0 * lamTan m hm 1 + 3 * lamTan m hm 1 ^ 2) * ‖d‖ := by
      calc _ ≤ |4 * lamTan m hm 0 * lamTan m hm 1 * d 0| + |3 * lamTan m hm 1 ^ 2 * d 1| :=
            abs_sub _ _
        _ = 4 * lamTan m hm 0 * lamTan m hm 1 * |d 0| + 3 * lamTan m hm 1 ^ 2 * |d 1| := by
            simp only [abs_mul, abs_pow, abs_of_pos hl0, abs_of_pos hl1,
              abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd0 (by positivity : 0 ≤ 4 * lamTan m hm 0 * lamTan m hm 1),
              mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ 3 * lamTan m hm 1 ^ 2)]
    calc 8 * π / 21 * _ ≤ 8 * π / 21 * ((4 * lamTan m hm 0 * lamTan m hm 1 + 3 * lamTan m hm 1 ^ 2)
          * ‖d‖) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = measLA m hm * ‖d‖ := by unfold measLA; ring

/-- Diameter bound: `diam ω⁰(F) ≤ N_A diam F`, in the form used for the zone estimates. -/
theorem measNA_dist_le (ξ ξ' : Fin 2 → ℝ) :
    dist (omegaTan m hm ξ) (omegaTan m hm ξ') ≤ measNA m hm * dist ξ ξ' := by
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_omegaTan_sub_le m hm ξ ξ'

end basic

end KAM.Wave

end
