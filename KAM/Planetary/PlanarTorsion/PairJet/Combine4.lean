/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Piece4a
public import KAM.Planetary.PlanarTorsion.PairJet.Piece4b
public import KAM.Planetary.PlanarTorsion.PairJet.Piece4c
public import KAM.Planetary.PlanarTorsion.PairCoefficients
public import KAM.Planetary.PlanarTorsion.PairJet.Ray

/-!
# Planar quartic torsion: the degree-4 part of the average of the pair jet

Blueprint P, Part 11b (`stepP:p11b:pj-red`): the pieces of the degree-4 coefficient of `N^{-1/2}`
    are averaged
(`Piece*` files) and the resulting Laplace coefficients are reduced to `b_{1/2}^{(0)}`,
    `b_{1/2}^{(1)}` by the
explicit table of `Reduction`; the result is the corresponding homogeneous part of `p11c_pairJet`
(`p11cPJ_avg4`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

theorem p11cPJ_mu4_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_0 a + ((3/4 : ℝ)) * p11cPJC_q413_0 a + ((3/8 : ℝ)) * p11cPJC_q422_0
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_0 a + ((35/128 : ℝ)) * p11cPJC_q4114_0 a =
      (1 : ℝ) * p11c_pairCoeffs a 3 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_0, p11cPJC_q413_0, p11cPJC_q422_0, p11cPJC_q4112_0, p11cPJC_q4114_0,
      p11cPJtab_1_1 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_3_0 ha,
      p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha,
      p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha, p11c_pairCoeffs_apply a 3]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_1 a + ((3/4 : ℝ)) * p11cPJC_q413_1 a + ((3/8 : ℝ)) * p11cPJC_q422_1
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_1 a + ((35/128 : ℝ)) * p11cPJC_q4114_1 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 7 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_1, p11cPJC_q413_1, p11cPJC_q422_1, p11cPJC_q4112_1, p11cPJC_q4114_1,
      p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha,
      p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_3_4 ha,
      p11cPJtab_4_0 ha, p11cPJtab_4_1 ha, p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha,
      p11cPJtab_4_5 ha, p11c_pairCoeffs_apply a 7]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_2 a + ((3/4 : ℝ)) * p11cPJC_q413_2 a + ((3/8 : ℝ)) * p11cPJC_q422_2
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_2 a + ((35/128 : ℝ)) * p11cPJC_q4114_2 a =
      (1/4 : ℝ) * p11c_pairCoeffs a 5 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_2, p11cPJC_q413_2, p11cPJC_q422_2, p11cPJC_q4112_2, p11cPJC_q4114_2,
      p11cPJtab_1_1 ha, p11cPJtab_1_3 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha,
      p11cPJtab_2_3 ha, p11cPJtab_2_4 ha, p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha,
      p11cPJtab_3_3 ha, p11cPJtab_3_4 ha, p11cPJtab_3_5 ha, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha,
      p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha, p11cPJtab_4_5 ha, p11cPJtab_4_6 ha,
      p11c_pairCoeffs_apply a 5]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_3 a + ((3/4 : ℝ)) * p11cPJC_q413_3 a + ((3/8 : ℝ)) * p11cPJC_q422_3
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_3 a + ((35/128 : ℝ)) * p11cPJC_q4114_3 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 7 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_3, p11cPJC_q413_3, p11cPJC_q422_3, p11cPJC_q4112_3, p11cPJC_q4114_3,
      p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha,
      p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_3_4 ha,
      p11cPJtab_4_0 ha, p11cPJtab_4_1 ha, p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha,
      p11cPJtab_4_5 ha, p11c_pairCoeffs_apply a 7]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_4 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_4 a + ((3/4 : ℝ)) * p11cPJC_q413_4 a + ((3/8 : ℝ)) * p11cPJC_q422_4
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_4 a + ((35/128 : ℝ)) * p11cPJC_q4114_4 a =
      (1 : ℝ) * p11c_pairCoeffs a 4 + (1/2 : ℝ) * p11c_pairCoeffs a 5 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_4, p11cPJC_q413_4, p11cPJC_q422_4, p11cPJC_q4112_4, p11cPJC_q4114_4,
      p11cPJtab_1_1 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_3_0 ha,
      p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha,
      p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha, p11c_pairCoeffs_apply a 4,
      p11c_pairCoeffs_apply a 5]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_5 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_5 a + ((3/4 : ℝ)) * p11cPJC_q413_5 a + ((3/8 : ℝ)) * p11cPJC_q422_5
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_5 a + ((35/128 : ℝ)) * p11cPJC_q4114_5 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 6 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_5, p11cPJC_q413_5, p11cPJC_q422_5, p11cPJC_q4112_5, p11cPJC_q4114_5,
      p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha,
      p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_3_4 ha,
      p11cPJtab_4_0 ha, p11cPJtab_4_1 ha, p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha,
      p11cPJtab_4_5 ha, p11c_pairCoeffs_apply a 6]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_6 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_6 a + ((3/4 : ℝ)) * p11cPJC_q413_6 a + ((3/8 : ℝ)) * p11cPJC_q422_6
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_6 a + ((35/128 : ℝ)) * p11cPJC_q4114_6 a =
      (1/4 : ℝ) * p11c_pairCoeffs a 5 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_6, p11cPJC_q413_6, p11cPJC_q422_6, p11cPJC_q4112_6, p11cPJC_q4114_6,
      p11cPJtab_1_1 ha, p11cPJtab_1_3 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha,
      p11cPJtab_2_3 ha, p11cPJtab_2_4 ha, p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha,
      p11cPJtab_3_3 ha, p11cPJtab_3_4 ha, p11cPJtab_3_5 ha, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha,
      p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha, p11cPJtab_4_5 ha, p11cPJtab_4_6 ha,
      p11c_pairCoeffs_apply a 5]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_7 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_7 a + ((3/4 : ℝ)) * p11cPJC_q413_7 a + ((3/8 : ℝ)) * p11cPJC_q422_7
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_7 a + ((35/128 : ℝ)) * p11cPJC_q4114_7 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 6 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_7, p11cPJC_q413_7, p11cPJC_q422_7, p11cPJC_q4112_7, p11cPJC_q4114_7,
      p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha,
      p11cPJtab_3_0 ha, p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_3_4 ha,
      p11cPJtab_4_0 ha, p11cPJtab_4_1 ha, p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha,
      p11cPJtab_4_5 ha, p11c_pairCoeffs_apply a 6]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu4_8 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q44a_8 a + ((3/4 : ℝ)) * p11cPJC_q413_8 a + ((3/8 : ℝ)) * p11cPJC_q422_8
        a + ((-15/16 : ℝ)) * p11cPJC_q4112_8 a + ((35/128 : ℝ)) * p11cPJC_q4114_8 a =
      (1 : ℝ) * p11c_pairCoeffs a 2 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q44a_8, p11cPJC_q413_8, p11cPJC_q422_8, p11cPJC_q4112_8, p11cPJC_q4114_8,
      p11cPJtab_1_1 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_3_0 ha,
      p11cPJtab_3_1 ha, p11cPJtab_3_2 ha, p11cPJtab_3_3 ha, p11cPJtab_4_0 ha, p11cPJtab_4_1 ha,
      p11cPJtab_4_2 ha, p11cPJtab_4_3 ha, p11cPJtab_4_4 ha, p11c_pairCoeffs_apply a 2]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_avg4 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), (p11cPJcJet (p11cPJN (a : ℂ) (ζ1 *
        p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l
        1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)))
        ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).a4 =
      ((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) * (((p11c_pairCoeffs a 2 : ℝ) : ℂ) * (ζ1 * ζb1) ^ 2 +
          ((p11c_pairCoeffs a 3 : ℝ) : ℂ) * (ζ2 * ζb2) ^ 2 + ((p11c_pairCoeffs a 4 : ℝ) : ℂ) * (ζ1
          * ζb1) * (ζ2 * ζb2) +
        ((p11c_pairCoeffs a 5 : ℝ) : ℂ) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) ^ 2 + ((p11c_pairCoeffs a 6 :
            ℝ) : ℂ) * (ζ1 * ζb1) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) +
        ((p11c_pairCoeffs a 7 : ℝ) : ℂ) * (ζ2 * ζb2) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2)) := by
  set f0 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq44a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE
      1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l
      1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf0
  have i0 : IntegrableOn f0 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
      p11cPJ_q44a_integrable ha ζ1 ζb1 ζ2 ζb2
  have a0 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f0 l = _ := p11cPJ_q44a_avg
      ha ζ1 ζb1 ζ2 ζb2
  set f1 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq413 (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE
      1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l
      1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf1
  have i1 : IntegrableOn f1 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
      p11cPJ_q413_integrable ha ζ1 ζb1 ζ2 ζb2
  have a1 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f1 l = _ := p11cPJ_q413_avg
      ha ζ1 ζb1 ζ2 ζb2
  set f2 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq422 (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE
      1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l
      1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf2
  have i2 : IntegrableOn f2 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
      p11cPJ_q422_integrable ha ζ1 ζb1 ζ2 ζb2
  have a2 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f2 l = _ := p11cPJ_q422_avg
      ha ζ1 ζb1 ζ2 ζb2
  set f3 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq4112 (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE
      1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l
      1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf3
  have i3 : IntegrableOn f3 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
      p11cPJ_q4112_integrable ha ζ1 ζb1 ζ2 ζb2
  have a3 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f3 l = _ := p11cPJ_q4112_avg
      ha ζ1 ζb1 ζ2 ζb2
  set f4 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq4114 (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE
      1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l
      1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf4
  have i4 : IntegrableOn f4 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
      p11cPJ_q4114_integrable ha ζ1 ζb1 ζ2 ζb2
  have a4 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f4 l = _ := p11cPJ_q4114_avg
      ha ζ1 ζb1 ζ2 ζb2
  have e : (fun l : Fin 2 → ℝ => (p11cPJcJet (p11cPJN (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 *
      p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE
      (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).a4) =
      fun l => ((-1/2 : ℂ)) * f0 l + ((3/4 : ℂ)) * f1 l + ((3/8 : ℂ)) * f2 l + ((-15/16 : ℂ)) * f3
      l + ((35/128 : ℂ)) * f4 l := by
    funext l
    simp only [hf0, hf1, hf2, hf3, hf4, p11cPJcJet, p11cPJq44a, p11cPJq413, p11cPJq422,
        p11cPJq4112, p11cPJq4114]
    ring
  rw [e]
  have hs1 : IntegrableOn (fun l => ((-1/2 : ℂ)) * f0 l + ((3/4 : ℂ)) * f1 l) (Set.pi univ (fun _ :
      Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
    ((i0.const_mul ((-1/2 : ℂ)))).add (i1.const_mul ((3/4 : ℂ)))
  have hs2 : IntegrableOn (fun l => ((-1/2 : ℂ)) * f0 l + ((3/4 : ℂ)) * f1 l + ((3/8 : ℂ)) * f2 l)
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
    hs1.add (i2.const_mul ((3/8 : ℂ)))
  have hs3 : IntegrableOn (fun l => ((-1/2 : ℂ)) * f0 l + ((3/4 : ℂ)) * f1 l + ((3/8 : ℂ)) * f2 l +
      ((-15/16 : ℂ)) * f3 l) (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume :=
    hs2.add (i3.const_mul ((-15/16 : ℂ)))
  rw [integral_add hs3 (i4.const_mul ((35/128 : ℂ))), integral_add hs2 (i3.const_mul ((-15/16 :
      ℂ))), integral_add hs1 (i2.const_mul ((3/8 : ℂ))), integral_add (i0.const_mul ((-1/2 : ℂ)))
      (i1.const_mul ((3/4 : ℂ)))]
  simp only [integral_const_mul]
  rw [a0, a1, a2, a3, a4]
  have h0 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_0 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h0
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_1 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h1
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_2 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h2
  have h3 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_3 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h3
  have h4 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_4 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h4
  have h5 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_5 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h5
  have h6 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_6 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h6
  have h7 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_7 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h7
  have h8 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu4_8 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h8
  push_cast at *
  linear_combination ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ2 ^ 2 * ζb2 ^ 2)) * h0 + ((2 * (π : ℂ)) *
      (2 * (π : ℂ)) * (ζb1 * ζ2 ^ 2 * ζb2)) * h1 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζb1 ^ 2 * ζ2 ^
      2)) * h2 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 * ζ2 * ζb2 ^ 2)) * h3 + ((2 * (π : ℂ)) * (2 *
      (π : ℂ)) * (ζ1 * ζb1 * ζ2 * ζb2)) * h4 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 * ζb1 ^ 2 *
      ζ2)) * h5 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 ^ 2 * ζb2 ^ 2)) * h6 + ((2 * (π : ℂ)) * (2 *
      (π : ℂ)) * (ζ1 ^ 2 * ζb1 * ζb2)) * h7 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 ^ 2 * ζb1 ^ 2))
      * h8


end KAM.Planetary

end
