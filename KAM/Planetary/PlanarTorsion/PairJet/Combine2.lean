/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Piece22
public import KAM.Planetary.PlanarTorsion.PairCoefficients
public import KAM.Planetary.PlanarTorsion.PairJet.Ray

/-!
# Planar quartic torsion: the degree-2 part of the average of the pair jet

Blueprint P, Part 11b (`stepP:p11b:pj-red`): the pieces of the degree-2 coefficient of `N^{-1/2}` are averaged
(`Piece*` files) and the resulting Laplace coefficients are reduced to `b_{1/2}^{(0)}`, `b_{1/2}^{(1)}` by the
explicit table of `Reduction`; the result is the corresponding homogeneous part of `p11c_pairJet`
(`p11cPJ_avg2`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

theorem p11cPJ_mu2_0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q22a_0 a + ((3/8 : ℝ)) * p11cPJC_q22b_0 a =
      (1 : ℝ) * p11c_pairCoeffs a 0 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q22a_0, p11cPJC_q22b_0, p11cPJtab_1_0 ha, p11cPJtab_1_1 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11c_pairCoeffs_apply a 0]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu2_1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q22a_1 a + ((3/8 : ℝ)) * p11cPJC_q22b_1 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 1 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q22a_1, p11cPJC_q22b_1, p11cPJtab_1_0 ha, p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha, p11c_pairCoeffs_apply a 1]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu2_2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q22a_2 a + ((3/8 : ℝ)) * p11cPJC_q22b_2 a =
      (1/2 : ℝ) * p11c_pairCoeffs a 1 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q22a_2, p11cPJC_q22b_2, p11cPJtab_1_0 ha, p11cPJtab_1_2 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11cPJtab_2_3 ha, p11c_pairCoeffs_apply a 1]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_mu2_3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ((-1/2 : ℝ)) * p11cPJC_q22a_3 a + ((3/8 : ℝ)) * p11cPJC_q22b_3 a =
      (1 : ℝ) * p11c_pairCoeffs a 0 := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ≠ 0 := p11c_one_sub_sq_ne ha
  simp only [p11cPJC_q22a_3, p11cPJC_q22b_3, p11cPJtab_1_0 ha, p11cPJtab_1_1 ha, p11cPJtab_2_0 ha, p11cPJtab_2_1 ha, p11cPJtab_2_2 ha, p11c_pairCoeffs_apply a 0]
  simp only [p11cN0, p11cN1, p11cDn]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  generalize p11c_laplace (1 / 2) 0 a = b0
  generalize p11c_laplace (1 / 2) 1 a = b1
  field_simp
  ring

theorem p11cPJ_avg2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), (p11cPJcJet (p11cPJN (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).a2 =
      ((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) * (((p11c_pairCoeffs a 0 : ℝ) : ℂ) * (ζ1 * ζb1 + ζ2 * ζb2) + ((p11c_pairCoeffs a 1 : ℝ) : ℂ) * (ζb1 * ζ2 + ζ1 * ζb2) / 2) := by
  set f0 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq22a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf0
  have i0 : IntegrableOn f0 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := p11cPJ_q22a_integrable ha ζ1 ζb1 ζ2 ζb2
  have a0 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f0 l = _ := p11cPJ_q22a_avg ha ζ1 ζb1 ζ2 ζb2
  set f1 : (Fin 2 → ℝ) → ℂ := fun l => p11cPJq22b (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) with hf1
  have i1 : IntegrableOn f1 (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := p11cPJ_q22b_integrable ha ζ1 ζb1 ζ2 ζb2
  have a1 : ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), f1 l = _ := p11cPJ_q22b_avg ha ζ1 ζb1 ζ2 ζb2
  have e : (fun l : Fin 2 → ℝ => (p11cPJcJet (p11cPJN (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0)) (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1)) (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).a2) = fun l => ((-1/2 : ℂ)) * f0 l + ((3/8 : ℂ)) * f1 l := by
    funext l
    simp only [hf0, hf1, p11cPJcJet, p11cPJq22a, p11cPJq22b]
    ring
  rw [e]
  rw [integral_add (i0.const_mul ((-1/2 : ℂ))) (i1.const_mul ((3/8 : ℂ)))]
  simp only [integral_const_mul]
  rw [a0, a1]
  have h0 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu2_0 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h0
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu2_1 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h1
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu2_2 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h2
  have h3 := congrArg (fun x : ℝ => (x : ℂ)) (p11cPJ_mu2_3 ha)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at h3
  push_cast at *
  linear_combination ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ2 * ζb2)) * h0 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζb1 * ζ2)) * h1 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 * ζb2)) * h2 + ((2 * (π : ℂ)) * (2 * (π : ℂ)) * (ζ1 * ζb1)) * h3


end KAM.Planetary

end
