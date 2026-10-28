/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Rot
public import KAM.Planetary.PlanarTorsion.PairJet.Reduction

/-!
# Planar quartic torsion: Fourier expansion and torus average of pieces of the pair jet

Blueprint P, Part 11b (`stepP:p11b:pj-bin`, `stepP:p11b:pj-avg`): the pieces q22a, q22b of the
    binomial
expansion are expanded as finite Fourier sums (`p11cPJLN_*` neutral terms, `p11cPJLC_*` charged
terms) and averaged over the torus; only the neutral terms contribute.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

def p11cPJLN_q22a_0 (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm := [
    ⟨(1/2 : ℂ) * α * ζ1 * ζb1, 1, 1, 0, 0, 1, 0, 3⟩,
    ⟨(1/2 : ℂ) * α * ζ1 * ζb1, 1, 1, 0, 0, 0, 1, 3⟩,
    ⟨(3/2 : ℂ) * α ^ 2 * ζ1 * ζb1, 1, 1, 0, 0, 0, 0, 3⟩,
    ⟨(-9/4 : ℂ) * α * ζ1 * ζb2, 1, 0, 0, 1, 1, 0, 3⟩,
    ⟨(-1/4 : ℂ) * α * ζ1 * ζb2, 1, 0, 0, 1, 0, 1, 3⟩,
    ⟨(-1/4 : ℂ) * α * ζb1 * ζ2, 0, 1, 1, 0, 1, 0, 3⟩,
    ⟨(-9/4 : ℂ) * α * ζb1 * ζ2, 0, 1, 1, 0, 0, 1, 3⟩,
    ⟨(1/2 : ℂ) * α * ζ2 * ζb2, 0, 0, 1, 1, 1, 0, 3⟩,
    ⟨(1/2 : ℂ) * α * ζ2 * ζb2, 0, 0, 1, 1, 0, 1, 3⟩,
    ⟨(3/2 : ℂ) * ζ2 * ζb2, 0, 0, 1, 1, 0, 0, 3⟩]

def p11cPJLN_q22a (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm :=
  p11cPJLN_q22a_0 α ζ1 ζb1 ζ2 ζb2

def p11cPJLC_q22a_0 (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm := [
    ⟨(-1/8 : ℂ) * α * ζ1 ^ 2, 2, 0, 0, 0, 1, 0, 3⟩,
    ⟨(-3/8 : ℂ) * α * ζ1 ^ 2, 2, 0, 0, 0, 0, 1, 3⟩,
    ⟨(-1/4 : ℂ) * α ^ 2 * ζ1 ^ 2, 2, 0, 0, 0, 0, 0, 3⟩,
    ⟨(3/4 : ℂ) * α * ζ1 * ζ2, 1, 0, 1, 0, 1, 0, 3⟩,
    ⟨(3/4 : ℂ) * α * ζ1 * ζ2, 1, 0, 1, 0, 0, 1, 3⟩,
    ⟨(-3/8 : ℂ) * α * ζb1 ^ 2, 0, 2, 0, 0, 1, 0, 3⟩,
    ⟨(-1/8 : ℂ) * α * ζb1 ^ 2, 0, 2, 0, 0, 0, 1, 3⟩,
    ⟨(-1/4 : ℂ) * α ^ 2 * ζb1 ^ 2, 0, 2, 0, 0, 0, 0, 3⟩,
    ⟨(3/4 : ℂ) * α * ζb1 * ζb2, 0, 1, 0, 1, 1, 0, 3⟩,
    ⟨(3/4 : ℂ) * α * ζb1 * ζb2, 0, 1, 0, 1, 0, 1, 3⟩,
    ⟨(-3/8 : ℂ) * α * ζ2 ^ 2, 0, 0, 2, 0, 1, 0, 3⟩,
    ⟨(-1/8 : ℂ) * α * ζ2 ^ 2, 0, 0, 2, 0, 0, 1, 3⟩,
    ⟨(-1/4 : ℂ) * ζ2 ^ 2, 0, 0, 2, 0, 0, 0, 3⟩,
    ⟨(-1/8 : ℂ) * α * ζb2 ^ 2, 0, 0, 0, 2, 1, 0, 3⟩,
    ⟨(-3/8 : ℂ) * α * ζb2 ^ 2, 0, 0, 0, 2, 0, 1, 3⟩,
    ⟨(-1/4 : ℂ) * ζb2 ^ 2, 0, 0, 0, 2, 0, 0, 3⟩]

def p11cPJLC_q22a (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm :=
  p11cPJLC_q22a_0 α ζ1 ζb1 ζ2 ζb2

def p11cPJC_q22a_0 (a : ℝ) : ℝ :=
  ((3/2 : ℝ)) * p11c_laplace (3/2 : ℝ) 0 a +
        ((1 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 1 a

def p11cPJC_q22a_1 (a : ℝ) : ℝ :=
  ((-9/4 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 0 a +
        ((-1/4 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 2 a

def p11cPJC_q22a_2 (a : ℝ) : ℝ :=
  ((-9/4 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 0 a +
        ((-1/4 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 2 a

def p11cPJC_q22a_3 (a : ℝ) : ℝ :=
  ((3/2 : ℝ) * a ^ 2) * p11c_laplace (3/2 : ℝ) 0 a +
        ((1 : ℝ) * a) * p11c_laplace (3/2 : ℝ) 1 a

theorem p11cPJLN_q22a_0_ok (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLN_q22a_0 α ζ1 ζb1 ζ2 ζb2, t.charge
    = 0 := by
  unfold p11cPJLN_q22a_0
  simp [PJTerm.charge]

theorem p11cPJLC_q22a_0_ok (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLC_q22a_0 α ζ1 ζb1 ζ2 ζb2, t.charge
    ≠ 0 := by
  unfold p11cPJLC_q22a_0
  simp [PJTerm.charge]

theorem p11cPJ_q22a_neutral (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLN_q22a α ζ1 ζb1 ζ2 ζb2, t.charge =
    0 := by
  unfold p11cPJLN_q22a
  exact p11cPJLN_q22a_0_ok _ _ _ _ _

theorem p11cPJ_q22a_charged (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLC_q22a α ζ1 ζb1 ζ2 ζb2, t.charge ≠
    0 := by
  unfold p11cPJLC_q22a
  exact p11cPJLC_q22a_0_ok _ _ _ _ _

theorem p11cPJ_q22a_eq (α ζ1 ζb1 ζ2 ζb2 Em0 Ep0 Em1 Ep1 S : ℂ) :
    p11cPJq22a α (ζ1 * Em0) (ζb1 * Ep0) (ζ2 * Em1) (ζb2 * Ep1) (Ep0 * Em1) (Em0 * Ep1) S =
      p11cPJsum (p11cPJLN_q22a α ζ1 ζb1 ζ2 ζb2) Em0 Ep0 Em1 Ep1 S +
        p11cPJsum (p11cPJLC_q22a α ζ1 ζb1 ζ2 ζb2) Em0 Ep0 Em1 Ep1 S := by
  simp only [p11cPJq22a, p11cPJLN_q22a, p11cPJLC_q22a, p11cPJLN_q22a_0, p11cPJLC_q22a_0, p11cPJN,
      p11cPJv, p11cPJj1, p11cPJj2, p11cPJj3, p11cPJj4, Jet5.add, Jet5.mul, Jet5.smul, Jet5.neg,
      p11cPJsum, p11cPJKa, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem p11cPJ_q22a_avg {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJq22a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) * (
      ζ2 * ζb2 * ((p11cPJC_q22a_0 a : ℝ) : ℂ) +
      ζb1 * ζ2 * ((p11cPJC_q22a_1 a : ℝ) : ℂ) +
      ζ1 * ζb2 * ((p11cPJC_q22a_2 a : ℝ) : ℂ) +
      ζ1 * ζb1 * ((p11cPJC_q22a_3 a : ℝ) : ℂ)) := by
  have h : ∀ l : Fin 2 → ℝ,
      p11cPJq22a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
        p11cPJat a (p11cPJLN_q22a (a : ℂ) ζ1 ζb1 ζ2 ζb2) l +
          p11cPJat a (p11cPJLC_q22a (a : ℂ) ζ1 ζb1 ζ2 ζb2) l := fun l =>
    p11cPJ_q22a_eq _ _ _ _ _ _ _ _ _ _
  simp_rw [h]
  rw [integral_add (p11cPJat_integrableOn ha _) (p11cPJat_integrableOn ha _),
    p11cPJ_sum_integral_charged ha _ (p11cPJ_q22a_charged _ _ _ _ _),
    p11cPJ_sum_integral_neutral ha _ (p11cPJ_q22a_neutral _ _ _ _ _), add_zero]
  simp only [p11cPJLN_q22a, p11cPJLN_q22a_0, p11cPJC_q22a_0, p11cPJC_q22a_1, p11cPJC_q22a_2,
      p11cPJC_q22a_3, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, PJTerm.fourierIdx]
  norm_num [p11cPJ_laplace_neg]
  ring

theorem p11cPJ_q22a_integrable {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    IntegrableOn (fun l : Fin 2 → ℝ =>
        p11cPJq22a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ))
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := by
  have h : ∀ l : Fin 2 → ℝ,
      p11cPJq22a (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
        p11cPJat a (p11cPJLN_q22a (a : ℂ) ζ1 ζb1 ζ2 ζb2) l +
          p11cPJat a (p11cPJLC_q22a (a : ℂ) ζ1 ζb1 ζ2 ζb2) l := fun l =>
    p11cPJ_q22a_eq _ _ _ _ _ _ _ _ _ _
  simp_rw [h]
  exact (p11cPJat_integrableOn ha _).add (p11cPJat_integrableOn ha _)

def p11cPJLN_q22b_0 (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm := [
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ1 * ζb1, 1, 1, 0, 0, 2, 0, 5⟩,
    ⟨(5 : ℂ) * α ^ 2 * ζ1 * ζb1, 1, 1, 0, 0, 1, 1, 5⟩,
    ⟨(-2 : ℂ) * α ^ 3 * ζ1 * ζb1, 1, 1, 0, 0, 1, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ1 * ζb1, 1, 1, 0, 0, 0, 2, 5⟩,
    ⟨(-2 : ℂ) * α ^ 3 * ζ1 * ζb1, 1, 1, 0, 0, 0, 1, 5⟩,
    ⟨(2 : ℂ) * α ^ 4 * ζ1 * ζb1, 1, 1, 0, 0, 0, 0, 5⟩,
    ⟨(9/2 : ℂ) * α ^ 2 * ζ1 * ζb2, 1, 0, 0, 1, 2, 0, 5⟩,
    ⟨(-3 : ℂ) * α ^ 2 * ζ1 * ζb2, 1, 0, 0, 1, 1, 1, 5⟩,
    ⟨((-3 : ℂ) * α + (-3 : ℂ) * α ^ 3) * ζ1 * ζb2, 1, 0, 0, 1, 1, 0, 5⟩,
    ⟨(1/2 : ℂ) * α ^ 2 * ζ1 * ζb2, 1, 0, 0, 1, 0, 2, 5⟩,
    ⟨((1 : ℂ) * α + (1 : ℂ) * α ^ 3) * ζ1 * ζb2, 1, 0, 0, 1, 0, 1, 5⟩,
    ⟨(2 : ℂ) * α ^ 2 * ζ1 * ζb2, 1, 0, 0, 1, 0, 0, 5⟩,
    ⟨(1/2 : ℂ) * α ^ 2 * ζb1 * ζ2, 0, 1, 1, 0, 2, 0, 5⟩,
    ⟨(-3 : ℂ) * α ^ 2 * ζb1 * ζ2, 0, 1, 1, 0, 1, 1, 5⟩,
    ⟨((1 : ℂ) * α + (1 : ℂ) * α ^ 3) * ζb1 * ζ2, 0, 1, 1, 0, 1, 0, 5⟩,
    ⟨(9/2 : ℂ) * α ^ 2 * ζb1 * ζ2, 0, 1, 1, 0, 0, 2, 5⟩,
    ⟨((-3 : ℂ) * α + (-3 : ℂ) * α ^ 3) * ζb1 * ζ2, 0, 1, 1, 0, 0, 1, 5⟩,
    ⟨(2 : ℂ) * α ^ 2 * ζb1 * ζ2, 0, 1, 1, 0, 0, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ2 * ζb2, 0, 0, 1, 1, 2, 0, 5⟩,
    ⟨(5 : ℂ) * α ^ 2 * ζ2 * ζb2, 0, 0, 1, 1, 1, 1, 5⟩,
    ⟨(-2 : ℂ) * α * ζ2 * ζb2, 0, 0, 1, 1, 1, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ2 * ζb2, 0, 0, 1, 1, 0, 2, 5⟩,
    ⟨(-2 : ℂ) * α * ζ2 * ζb2, 0, 0, 1, 1, 0, 1, 5⟩,
    ⟨(2 : ℂ) * ζ2 * ζb2, 0, 0, 1, 1, 0, 0, 5⟩]

def p11cPJLN_q22b (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm :=
  p11cPJLN_q22b_0 α ζ1 ζb1 ζ2 ζb2

def p11cPJLC_q22b_0 (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm := [
    ⟨(9/4 : ℂ) * α ^ 2 * ζ1 ^ 2, 2, 0, 0, 0, 2, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ1 ^ 2, 2, 0, 0, 0, 1, 1, 5⟩,
    ⟨(-3 : ℂ) * α ^ 3 * ζ1 ^ 2, 2, 0, 0, 0, 1, 0, 5⟩,
    ⟨(1/4 : ℂ) * α ^ 2 * ζ1 ^ 2, 2, 0, 0, 0, 0, 2, 5⟩,
    ⟨(1 : ℂ) * α ^ 3 * ζ1 ^ 2, 2, 0, 0, 0, 0, 1, 5⟩,
    ⟨(1 : ℂ) * α ^ 4 * ζ1 ^ 2, 2, 0, 0, 0, 0, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ1 * ζ2, 1, 0, 1, 0, 2, 0, 5⟩,
    ⟨(5 : ℂ) * α ^ 2 * ζ1 * ζ2, 1, 0, 1, 0, 1, 1, 5⟩,
    ⟨((-3 : ℂ) * α + (1 : ℂ) * α ^ 3) * ζ1 * ζ2, 1, 0, 1, 0, 1, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ1 * ζ2, 1, 0, 1, 0, 0, 2, 5⟩,
    ⟨((1 : ℂ) * α + (-3 : ℂ) * α ^ 3) * ζ1 * ζ2, 1, 0, 1, 0, 0, 1, 5⟩,
    ⟨(2 : ℂ) * α ^ 2 * ζ1 * ζ2, 1, 0, 1, 0, 0, 0, 5⟩,
    ⟨(1/4 : ℂ) * α ^ 2 * ζb1 ^ 2, 0, 2, 0, 0, 2, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζb1 ^ 2, 0, 2, 0, 0, 1, 1, 5⟩,
    ⟨(1 : ℂ) * α ^ 3 * ζb1 ^ 2, 0, 2, 0, 0, 1, 0, 5⟩,
    ⟨(9/4 : ℂ) * α ^ 2 * ζb1 ^ 2, 0, 2, 0, 0, 0, 2, 5⟩,
    ⟨(-3 : ℂ) * α ^ 3 * ζb1 ^ 2, 0, 2, 0, 0, 0, 1, 5⟩,
    ⟨(1 : ℂ) * α ^ 4 * ζb1 ^ 2, 0, 2, 0, 0, 0, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζb1 * ζb2, 0, 1, 0, 1, 2, 0, 5⟩,
    ⟨(5 : ℂ) * α ^ 2 * ζb1 * ζb2, 0, 1, 0, 1, 1, 1, 5⟩,
    ⟨((1 : ℂ) * α + (-3 : ℂ) * α ^ 3) * ζb1 * ζb2, 0, 1, 0, 1, 1, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζb1 * ζb2, 0, 1, 0, 1, 0, 2, 5⟩,
    ⟨((-3 : ℂ) * α + (1 : ℂ) * α ^ 3) * ζb1 * ζb2, 0, 1, 0, 1, 0, 1, 5⟩,
    ⟨(2 : ℂ) * α ^ 2 * ζb1 * ζb2, 0, 1, 0, 1, 0, 0, 5⟩,
    ⟨(1/4 : ℂ) * α ^ 2 * ζ2 ^ 2, 0, 0, 2, 0, 2, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζ2 ^ 2, 0, 0, 2, 0, 1, 1, 5⟩,
    ⟨(1 : ℂ) * α * ζ2 ^ 2, 0, 0, 2, 0, 1, 0, 5⟩,
    ⟨(9/4 : ℂ) * α ^ 2 * ζ2 ^ 2, 0, 0, 2, 0, 0, 2, 5⟩,
    ⟨(-3 : ℂ) * α * ζ2 ^ 2, 0, 0, 2, 0, 0, 1, 5⟩,
    ⟨(1 : ℂ) * ζ2 ^ 2, 0, 0, 2, 0, 0, 0, 5⟩,
    ⟨(9/4 : ℂ) * α ^ 2 * ζb2 ^ 2, 0, 0, 0, 2, 2, 0, 5⟩,
    ⟨(-3/2 : ℂ) * α ^ 2 * ζb2 ^ 2, 0, 0, 0, 2, 1, 1, 5⟩,
    ⟨(-3 : ℂ) * α * ζb2 ^ 2, 0, 0, 0, 2, 1, 0, 5⟩,
    ⟨(1/4 : ℂ) * α ^ 2 * ζb2 ^ 2, 0, 0, 0, 2, 0, 2, 5⟩,
    ⟨(1 : ℂ) * α * ζb2 ^ 2, 0, 0, 0, 2, 0, 1, 5⟩,
    ⟨(1 : ℂ) * ζb2 ^ 2, 0, 0, 0, 2, 0, 0, 5⟩]

def p11cPJLC_q22b (α ζ1 ζb1 ζ2 ζb2 : ℂ) : List PJTerm :=
  p11cPJLC_q22b_0 α ζ1 ζb1 ζ2 ζb2

def p11cPJC_q22b_0 (a : ℝ) : ℝ :=
  ((2 : ℝ) + (5 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 0 a +
        ((-4 : ℝ) * a) * p11c_laplace (5/2 : ℝ) 1 a +
        ((-3 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 2 a

def p11cPJC_q22b_1 (a : ℝ) : ℝ :=
  ((-3 : ℝ) * a + (-3 : ℝ) * a ^ 3) * p11c_laplace (5/2 : ℝ) 0 a +
        ((7/2 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 1 a +
        ((1 : ℝ) * a + (1 : ℝ) * a ^ 3) * p11c_laplace (5/2 : ℝ) 2 a +
        ((1/2 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 3 a

def p11cPJC_q22b_2 (a : ℝ) : ℝ :=
  ((-3 : ℝ) * a + (-3 : ℝ) * a ^ 3) * p11c_laplace (5/2 : ℝ) 0 a +
        ((7/2 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 1 a +
        ((1 : ℝ) * a + (1 : ℝ) * a ^ 3) * p11c_laplace (5/2 : ℝ) 2 a +
        ((1/2 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 3 a

def p11cPJC_q22b_3 (a : ℝ) : ℝ :=
  ((5 : ℝ) * a ^ 2 + (2 : ℝ) * a ^ 4) * p11c_laplace (5/2 : ℝ) 0 a +
        ((-4 : ℝ) * a ^ 3) * p11c_laplace (5/2 : ℝ) 1 a +
        ((-3 : ℝ) * a ^ 2) * p11c_laplace (5/2 : ℝ) 2 a

theorem p11cPJLN_q22b_0_ok (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLN_q22b_0 α ζ1 ζb1 ζ2 ζb2, t.charge
    = 0 := by
  unfold p11cPJLN_q22b_0
  simp [PJTerm.charge]

theorem p11cPJLC_q22b_0_ok (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLC_q22b_0 α ζ1 ζb1 ζ2 ζb2, t.charge
    ≠ 0 := by
  unfold p11cPJLC_q22b_0
  simp [PJTerm.charge]

theorem p11cPJ_q22b_neutral (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLN_q22b α ζ1 ζb1 ζ2 ζb2, t.charge =
    0 := by
  unfold p11cPJLN_q22b
  exact p11cPJLN_q22b_0_ok _ _ _ _ _

theorem p11cPJ_q22b_charged (α ζ1 ζb1 ζ2 ζb2 : ℂ) : ∀ t ∈ p11cPJLC_q22b α ζ1 ζb1 ζ2 ζb2, t.charge ≠
    0 := by
  unfold p11cPJLC_q22b
  exact p11cPJLC_q22b_0_ok _ _ _ _ _

theorem p11cPJ_q22b_eq (α ζ1 ζb1 ζ2 ζb2 Em0 Ep0 Em1 Ep1 S : ℂ) :
    p11cPJq22b α (ζ1 * Em0) (ζb1 * Ep0) (ζ2 * Em1) (ζb2 * Ep1) (Ep0 * Em1) (Em0 * Ep1) S =
      p11cPJsum (p11cPJLN_q22b α ζ1 ζb1 ζ2 ζb2) Em0 Ep0 Em1 Ep1 S +
        p11cPJsum (p11cPJLC_q22b α ζ1 ζb1 ζ2 ζb2) Em0 Ep0 Em1 Ep1 S := by
  simp only [p11cPJq22b, p11cPJLN_q22b, p11cPJLC_q22b, p11cPJLN_q22b_0, p11cPJLC_q22b_0, p11cPJN,
      p11cPJv, p11cPJj1, p11cPJj2, p11cPJj3, p11cPJj4, Jet5.add, Jet5.mul, Jet5.smul, Jet5.neg,
      p11cPJsum, p11cPJKa, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem p11cPJ_q22b_avg {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJq22b (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) * (
      ζ2 * ζb2 * ((p11cPJC_q22b_0 a : ℝ) : ℂ) +
      ζb1 * ζ2 * ((p11cPJC_q22b_1 a : ℝ) : ℂ) +
      ζ1 * ζb2 * ((p11cPJC_q22b_2 a : ℝ) : ℂ) +
      ζ1 * ζb1 * ((p11cPJC_q22b_3 a : ℝ) : ℂ)) := by
  have h : ∀ l : Fin 2 → ℝ,
      p11cPJq22b (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
        p11cPJat a (p11cPJLN_q22b (a : ℂ) ζ1 ζb1 ζ2 ζb2) l +
          p11cPJat a (p11cPJLC_q22b (a : ℂ) ζ1 ζb1 ζ2 ζb2) l := fun l =>
    p11cPJ_q22b_eq _ _ _ _ _ _ _ _ _ _
  simp_rw [h]
  rw [integral_add (p11cPJat_integrableOn ha _) (p11cPJat_integrableOn ha _),
    p11cPJ_sum_integral_charged ha _ (p11cPJ_q22b_charged _ _ _ _ _),
    p11cPJ_sum_integral_neutral ha _ (p11cPJ_q22b_neutral _ _ _ _ _), add_zero]
  simp only [p11cPJLN_q22b, p11cPJLN_q22b_0, p11cPJC_q22b_0, p11cPJC_q22b_1, p11cPJC_q22b_2,
      p11cPJC_q22b_3, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, PJTerm.fourierIdx]
  norm_num [p11cPJ_laplace_neg]
  ring

theorem p11cPJ_q22b_integrable {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    IntegrableOn (fun l : Fin 2 → ℝ =>
        p11cPJq22b (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ))
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := by
  have h : ∀ l : Fin 2 → ℝ,
      p11cPJq22b (a : ℂ) (ζ1 * p11cPJE (-1) (l 0)) (ζb1 * p11cPJE 1 (l 0))
          (ζ2 * p11cPJE (-1) (l 1)) (ζb2 * p11cPJE 1 (l 1))
          (p11cPJE 1 (l 0) * p11cPJE (-1) (l 1)) (p11cPJE (-1) (l 0) * p11cPJE 1 (l 1))
          ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
        p11cPJat a (p11cPJLN_q22b (a : ℂ) ζ1 ζb1 ζ2 ζb2) l +
          p11cPJat a (p11cPJLC_q22b (a : ℂ) ζ1 ζb1 ζ2 ζb2) l := fun l =>
    p11cPJ_q22b_eq _ _ _ _ _ _ _ _ _ _
  simp_rw [h]
  exact (p11cPJat_integrableOn ha _).add (p11cPJat_integrableOn ha _)


end KAM.Planetary

end
