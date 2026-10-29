/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.LaplaceReduction

/-!
# Planar quartic torsion: the half-integer Laplace coefficients used by the pair jet

Blueprint P, Part 11b (`stepP:p11b:pj-red`): the explicit reduction of the coefficients
`b_{s}^{(k)}`, `s ∈ {3/2, 5/2, 7/2, 9/2}`, `k ≤ 6`, to `b_{1/2}^{(0)}` and `b_{1/2}^{(1)}`.  Each
    entry
follows from the upward recurrence `laplace_up` (for `k ∈ {0, 1}`) or the level recurrence
`p11c_laplace_step` (for `k ≥ 2`) and the previous entries; the polynomial coefficients are
exact rational numbers.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory
namespace KAM.Planetary

theorem p11cPJ_laplace_neg (s : ℝ) (k : ℤ) (a : ℝ) :
    p11c_laplace s (-k) a = p11c_laplace s k a := by
  unfold p11c_laplace
  congr 2; ext t
  push_cast
  rw [neg_mul, Real.cos_neg]

theorem p11cPJtab_1_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (3/2 : ℝ) 0 a =
      (((1 : ℝ) + (1 : ℝ) * a ^ 2) * p11c_laplace (1 / 2) 0 a +
        ((-2 : ℝ) * a) * p11c_laplace (1 / 2) 1 a) / (a ^ 0 * (1 - a ^ 2) ^ 2) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((1/2 : ℝ)) a (by norm_num) ha).1
  rw [show ((1/2 : ℝ)) + 1 = (3/2 : ℝ) by norm_num] at h
  rw [h]
  field_simp
  ring

theorem p11cPJtab_1_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (3/2 : ℝ) 1 a =
      (((2 : ℝ) * a ^ 2) * p11c_laplace (1 / 2) 0 a +
        ((-1 : ℝ) * a + (-1 : ℝ) * a ^ 3) * p11c_laplace (1 / 2) 1 a) / (a ^ 1 * (1 - a ^ 2) ^ 2)
            := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((1/2 : ℝ)) a (by norm_num) ha).2.1
  rw [show ((1/2 : ℝ)) + 1 = (3/2 : ℝ) by norm_num] at h
  rw [h]
  field_simp
  ring

theorem p11cPJtab_1_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (3/2 : ℝ) 2 a =
      (((1 : ℝ) * a ^ 2 + (1 : ℝ) * a ^ 4) * p11c_laplace (1 / 2) 0 a +
        ((-2 : ℝ) * a + (2 : ℝ) * a ^ 3 + (-2 : ℝ) * a ^ 5) * p11c_laplace (1 / 2) 1 a) / (a ^ 2 *
            (1 - a ^ 2) ^ 2) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (3/2 : ℝ)) ha (1 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_1_0 ha, p11cPJtab_1_1 ha]
  field_simp
  ring

theorem p11cPJtab_1_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (3/2 : ℝ) 3 a =
      (((4/3 : ℝ) * a ^ 2 + (-2/3 : ℝ) * a ^ 4 + (4/3 : ℝ) * a ^ 6) * p11c_laplace (1 / 2) 0 a +
        ((-8/3 : ℝ) * a + (5/3 : ℝ) * a ^ 3 + (5/3 : ℝ) * a ^ 5 + (-8/3 : ℝ) * a ^ 7) *
            p11c_laplace (1 / 2) 1 a) / (a ^ 3 * (1 - a ^ 2) ^ 2) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (3/2 : ℝ)) ha (2 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_1_1 ha, p11cPJtab_1_2 ha]
  field_simp
  ring

theorem p11cPJtab_2_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (5/2 : ℝ) 0 a =
      (((1 : ℝ) + (10/3 : ℝ) * a ^ 2 + (1 : ℝ) * a ^ 4) * p11c_laplace (1 / 2) 0 a +
        ((-8/3 : ℝ) * a + (-8/3 : ℝ) * a ^ 3) * p11c_laplace (1 / 2) 1 a) / (a ^ 0 * (1 - a ^ 2) ^
            4) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((3/2 : ℝ)) a (by norm_num) ha).1
  rw [show ((3/2 : ℝ)) + 1 = (5/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_1_0 ha, p11cPJtab_1_1 ha]
  field_simp
  ring

theorem p11cPJtab_2_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (5/2 : ℝ) 1 a =
      (((8/3 : ℝ) * a ^ 2 + (8/3 : ℝ) * a ^ 4) * p11c_laplace (1 / 2) 0 a +
        ((-1/3 : ℝ) * a + (-14/3 : ℝ) * a ^ 3 + (-1/3 : ℝ) * a ^ 5) * p11c_laplace (1 / 2) 1 a) /
            (a ^ 1 * (1 - a ^ 2) ^ 4) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((3/2 : ℝ)) a (by norm_num) ha).2.1
  rw [show ((3/2 : ℝ)) + 1 = (5/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_1_0 ha, p11cPJtab_1_1 ha]
  field_simp
  ring

theorem p11cPJtab_2_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (5/2 : ℝ) 2 a =
      (((-1/3 : ℝ) * a ^ 2 + (6 : ℝ) * a ^ 4 + (-1/3 : ℝ) * a ^ 6) * p11c_laplace (1 / 2) 0 a +
        ((2/3 : ℝ) * a + (-10/3 : ℝ) * a ^ 3 + (-10/3 : ℝ) * a ^ 5 + (2/3 : ℝ) * a ^ 7) *
            p11c_laplace (1 / 2) 1 a) / (a ^ 2 * (1 - a ^ 2) ^ 4) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (5/2 : ℝ)) ha (1 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha]
  field_simp
  ring

theorem p11cPJtab_2_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (5/2 : ℝ) 3 a =
      (((-4/3 : ℝ) * a ^ 2 + (4 : ℝ) * a ^ 4 + (4 : ℝ) * a ^ 6 + (-4/3 : ℝ) * a ^ 8) * p11c_laplace
          (1 / 2) 0 a +
        ((8/3 : ℝ) * a + (-25/3 : ℝ) * a ^ 3 + (6 : ℝ) * a ^ 5 + (-25/3 : ℝ) * a ^ 7 + (8/3 : ℝ) *
            a ^ 9) * p11c_laplace (1 / 2) 1 a) / (a ^ 3 * (1 - a ^ 2) ^ 4) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (5/2 : ℝ)) ha (2 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha]
  field_simp
  ring

theorem p11cPJtab_2_4 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (5/2 : ℝ) 4 a =
      (((-8/3 : ℝ) * a ^ 2 + (19/3 : ℝ) * a ^ 4 + (-2 : ℝ) * a ^ 6 + (19/3 : ℝ) * a ^ 8 + (-8/3 :
          ℝ) * a ^ 10) * p11c_laplace (1 / 2) 0 a +
        ((16/3 : ℝ) * a + (-40/3 : ℝ) * a ^ 3 + (16/3 : ℝ) * a ^ 5 + (16/3 : ℝ) * a ^ 7 + (-40/3 :
            ℝ) * a ^ 9 + (16/3 : ℝ) * a ^ 11) * p11c_laplace (1 / 2) 1 a) / (a ^ 4 * (1 - a ^ 2) ^
            4) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (5/2 : ℝ)) ha (3 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha]
  field_simp
  ring

theorem p11cPJtab_3_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 0 a =
      (((1 : ℝ) + (113/15 : ℝ) * a ^ 2 + (113/15 : ℝ) * a ^ 4 + (1 : ℝ) * a ^ 6) * p11c_laplace (1
          / 2) 0 a +
        ((-46/15 : ℝ) * a + (-164/15 : ℝ) * a ^ 3 + (-46/15 : ℝ) * a ^ 5) * p11c_laplace (1 / 2) 1
            a) / (a ^ 0 * (1 - a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((5/2 : ℝ)) a (by norm_num) ha).1
  rw [show ((5/2 : ℝ)) + 1 = (7/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha]
  field_simp
  ring

theorem p11cPJtab_3_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 1 a =
      (((18/5 : ℝ) * a ^ 2 + (148/15 : ℝ) * a ^ 4 + (18/5 : ℝ) * a ^ 6) * p11c_laplace (1 / 2) 0 a +
        ((-1/5 : ℝ) * a + (-25/3 : ℝ) * a ^ 3 + (-25/3 : ℝ) * a ^ 5 + (-1/5 : ℝ) * a ^ 7) *
            p11c_laplace (1 / 2) 1 a) / (a ^ 1 * (1 - a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((5/2 : ℝ)) a (by norm_num) ha).2.1
  rw [show ((5/2 : ℝ)) + 1 = (7/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha]
  field_simp
  ring

theorem p11cPJtab_3_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 2 a =
      (((-1/15 : ℝ) * a ^ 2 + (43/5 : ℝ) * a ^ 4 + (43/5 : ℝ) * a ^ 6 + (-1/15 : ℝ) * a ^ 8) *
          p11c_laplace (1 / 2) 0 a +
        ((2/15 : ℝ) * a + (-22/15 : ℝ) * a ^ 3 + (-72/5 : ℝ) * a ^ 5 + (-22/15 : ℝ) * a ^ 7 + (2/15
            : ℝ) * a ^ 9) * p11c_laplace (1 / 2) 1 a) / (a ^ 2 * (1 - a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (7/2 : ℝ)) ha (1 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_3_0 ha, p11cPJtab_3_1 ha]
  field_simp
  ring

theorem p11cPJtab_3_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 3 a =
      (((4/15 : ℝ) * a ^ 2 + (-26/15 : ℝ) * a ^ 4 + (20 : ℝ) * a ^ 6 + (-26/15 : ℝ) * a ^ 8 + (4/15
          : ℝ) * a ^ 10) * p11c_laplace (1 / 2) 0 a +
        ((-8/15 : ℝ) * a + (53/15 : ℝ) * a ^ 3 + (-173/15 : ℝ) * a ^ 5 + (-173/15 : ℝ) * a ^ 7 +
            (53/15 : ℝ) * a ^ 9 + (-8/15 : ℝ) * a ^ 11) * p11c_laplace (1 / 2) 1 a) / (a ^ 3 * (1 -
            a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (7/2 : ℝ)) ha (2 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha]
  field_simp
  ring

theorem p11cPJtab_3_4 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 4 a =
      (((8/5 : ℝ) * a ^ 2 + (-121/15 : ℝ) * a ^ 4 + (15 : ℝ) * a ^ 6 + (15 : ℝ) * a ^ 8 + (-121/15
          : ℝ) * a ^ 10 + (8/5 : ℝ) * a ^ 12) * p11c_laplace (1 / 2) 0 a +
        ((-16/5 : ℝ) * a + (248/15 : ℝ) * a ^ 3 + (-478/15 : ℝ) * a ^ 5 + (20 : ℝ) * a ^ 7 +
            (-478/15 : ℝ) * a ^ 9 + (248/15 : ℝ) * a ^ 11 + (-16/5 : ℝ) * a ^ 13) * p11c_laplace (1
            / 2) 1 a) / (a ^ 4 * (1 - a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (7/2 : ℝ)) ha (3 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha]
  field_simp
  ring

theorem p11cPJtab_3_5 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (7/2 : ℝ) 5 a =
      (((64/15 : ℝ) * a ^ 2 + (-92/5 : ℝ) * a ^ 4 + (26 : ℝ) * a ^ 6 + (-20/3 : ℝ) * a ^ 8 + (26 :
          ℝ) * a ^ 10 + (-92/5 : ℝ) * a ^ 12 + (64/15 : ℝ) * a ^ 14) * p11c_laplace (1 / 2) 0 a +
        ((-128/15 : ℝ) * a + (568/15 : ℝ) * a ^ 3 + (-281/5 : ℝ) * a ^ 5 + (55/3 : ℝ) * a ^ 7 +
            (55/3 : ℝ) * a ^ 9 + (-281/5 : ℝ) * a ^ 11 + (568/15 : ℝ) * a ^ 13 + (-128/15 : ℝ) * a
            ^ 15) * p11c_laplace (1 / 2) 1 a) / (a ^ 5 * (1 - a ^ 2) ^ 6) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (7/2 : ℝ)) ha (4 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_3_3 ha, p11cPJtab_3_4 ha]
  field_simp
  ring

theorem p11cPJtab_4_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 0 a =
      (((1 : ℝ) + (1436/105 : ℝ) * a ^ 2 + (3062/105 : ℝ) * a ^ 4 + (1436/105 : ℝ) * a ^ 6 + (1 :
          ℝ) * a ^ 8) * p11c_laplace (1 / 2) 0 a +
        ((-352/105 : ℝ) * a + (-544/21 : ℝ) * a ^ 3 + (-544/21 : ℝ) * a ^ 5 + (-352/105 : ℝ) * a ^
            7) * p11c_laplace (1 / 2) 1 a) / (a ^ 0 * (1 - a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((7/2 : ℝ)) a (by norm_num) ha).1
  rw [show ((7/2 : ℝ)) + 1 = (9/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_3_0 ha, p11cPJtab_3_1 ha]
  field_simp
  ring

theorem p11cPJtab_4_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 1 a =
      (((32/7 : ℝ) * a ^ 2 + (864/35 : ℝ) * a ^ 4 + (864/35 : ℝ) * a ^ 6 + (32/7 : ℝ) * a ^ 8) *
          p11c_laplace (1 / 2) 0 a +
        ((-1/7 : ℝ) * a + (-428/35 : ℝ) * a ^ 3 + (-1182/35 : ℝ) * a ^ 5 + (-428/35 : ℝ) * a ^ 7 +
            (-1/7 : ℝ) * a ^ 9) * p11c_laplace (1 / 2) 1 a) / (a ^ 1 * (1 - a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := (laplace_up ((7/2 : ℝ)) a (by norm_num) ha).2.1
  rw [show ((7/2 : ℝ)) + 1 = (9/2 : ℝ) by norm_num] at h
  rw [h, p11cPJtab_3_0 ha, p11cPJtab_3_1 ha]
  field_simp
  ring

theorem p11cPJtab_4_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 2 a =
      (((-1/35 : ℝ) * a ^ 2 + (452/35 : ℝ) * a ^ 4 + (1146/35 : ℝ) * a ^ 6 + (452/35 : ℝ) * a ^ 8 +
          (-1/35 : ℝ) * a ^ 10) * p11c_laplace (1 / 2) 0 a +
        ((2/35 : ℝ) * a + (-38/35 : ℝ) * a ^ 3 + (-988/35 : ℝ) * a ^ 5 + (-988/35 : ℝ) * a ^ 7 +
            (-38/35 : ℝ) * a ^ 9 + (2/35 : ℝ) * a ^ 11) * p11c_laplace (1 / 2) 1 a) / (a ^ 2 * (1 -
            a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (9/2 : ℝ)) ha (1 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha]
  field_simp
  ring

theorem p11cPJtab_4_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 3 a =
      (((4/105 : ℝ) * a ^ 2 + (-44/105 : ℝ) * a ^ 4 + (3112/105 : ℝ) * a ^ 6 + (3112/105 : ℝ) * a ^
          8 + (-44/105 : ℝ) * a ^ 10 + (4/105 : ℝ) * a ^ 12) * p11c_laplace (1 / 2) 0 a +
        ((-8/105 : ℝ) * a + (89/105 : ℝ) * a ^ 3 + (-604/105 : ℝ) * a ^ 5 + (-5098/105 : ℝ) * a ^ 7
            + (-604/105 : ℝ) * a ^ 9 + (89/105 : ℝ) * a ^ 11 + (-8/105 : ℝ) * a ^ 13) *
            p11c_laplace (1 / 2) 1 a) / (a ^ 3 * (1 - a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (9/2 : ℝ)) ha (2 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_4_1 ha, p11cPJtab_4_2 ha]
  field_simp
  ring

theorem p11cPJtab_4_4 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 4 a =
      (((-8/35 : ℝ) * a ^ 2 + (67/35 : ℝ) * a ^ 4 + (-52/7 : ℝ) * a ^ 6 + (70 : ℝ) * a ^ 8 + (-52/7
          : ℝ) * a ^ 10 + (67/35 : ℝ) * a ^ 12 + (-8/35 : ℝ) * a ^ 14) * p11c_laplace (1 / 2) 0 a +
        ((16/35 : ℝ) * a + (-136/35 : ℝ) * a ^ 3 + (536/35 : ℝ) * a ^ 5 + (-288/7 : ℝ) * a ^ 7 +
            (-288/7 : ℝ) * a ^ 9 + (536/35 : ℝ) * a ^ 11 + (-136/35 : ℝ) * a ^ 13 + (16/35 : ℝ) * a
            ^ 15) * p11c_laplace (1 / 2) 1 a) / (a ^ 4 * (1 - a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (9/2 : ℝ)) ha (3 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_4_2 ha, p11cPJtab_4_3 ha]
  field_simp
  ring

theorem p11cPJtab_4_5 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 5 a =
      (((-64/35 : ℝ) * a ^ 2 + (452/35 : ℝ) * a ^ 4 + (-1324/35 : ℝ) * a ^ 6 + (56 : ℝ) * a ^ 8 +
          (56 : ℝ) * a ^ 10 + (-1324/35 : ℝ) * a ^ 12 + (452/35 : ℝ) * a ^ 14 + (-64/35 : ℝ) * a ^
          16) * p11c_laplace (1 / 2) 0 a +
        ((128/35 : ℝ) * a + (-184/7 : ℝ) * a ^ 3 + (551/7 : ℝ) * a ^ 5 + (-4212/35 : ℝ) * a ^ 7 +
            (70 : ℝ) * a ^ 9 + (-4212/35 : ℝ) * a ^ 11 + (551/7 : ℝ) * a ^ 13 + (-184/7 : ℝ) * a ^
            15 + (128/35 : ℝ) * a ^ 17) * p11c_laplace (1 / 2) 1 a) / (a ^ 5 * (1 - a ^ 2) ^ 8) :=
            by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (9/2 : ℝ)) ha (4 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha]
  field_simp
  ring

theorem p11cPJtab_4_6 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (9/2 : ℝ) 6 a =
      (((-128/21 : ℝ) * a ^ 2 + (4016/105 : ℝ) * a ^ 4 + (-9859/105 : ℝ) * a ^ 6 + (308/3 : ℝ) * a
          ^ 8 + (-70/3 : ℝ) * a ^ 10 + (308/3 : ℝ) * a ^ 12 + (-9859/105 : ℝ) * a ^ 14 + (4016/105
          : ℝ) * a ^ 16 + (-128/21 : ℝ) * a ^ 18) * p11c_laplace (1 / 2) 0 a +
        ((256/21 : ℝ) * a + (-8192/105 : ℝ) * a ^ 3 + (20662/105 : ℝ) * a ^ 5 + (-7894/35 : ℝ) * a
            ^ 7 + (196/3 : ℝ) * a ^ 9 + (196/3 : ℝ) * a ^ 11 + (-7894/35 : ℝ) * a ^ 13 + (20662/105
            : ℝ) * a ^ 15 + (-8192/105 : ℝ) * a ^ 17 + (256/21 : ℝ) * a ^ 19) * p11c_laplace (1 /
            2) 1 a) / (a ^ 6 * (1 - a ^ 2) ^ 8) := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  have h := p11c_laplace_step (s := (9/2 : ℝ)) ha (5 : ℤ) (by norm_num)
  norm_num at h
  rw [h, p11cPJtab_4_4 ha, p11cPJtab_4_5 ha]
  field_simp
  ring

end KAM.Planetary

end
