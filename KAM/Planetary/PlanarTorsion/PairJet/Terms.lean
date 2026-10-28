/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Average

/-!
# Planar quartic torsion: finite Fourier sums over the torus

Blueprint P, Part 11b (`stepP:p11b:pj-avg`, `stepP:p11b:pj-red`): a finite sum of terms
`c · E₀⁻ᵃ E₀ᵇ E₁⁻ᶜ E₁ᵈ (E₀ E₁⁻¹)ᵘ (E₀⁻¹ E₁)ᵛ Sᵉ`, with `E_k = e^{i λ_k}` and `S = s(λ₀ - λ₁)^{-1/2}`,
is integrated over `[0,2π]²` term by term: only the terms with `b - a + d - c = 0` survive, and each
of them is a Laplace coefficient (`p11cPJ_integral_term`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary

/-- One term of a finite Fourier sum: a coefficient and the exponents `(a, b, c, d, u, v, e)`. -/
structure PJTerm where
  coef : ℂ
  na : ℕ
  nb : ℕ
  nc : ℕ
  nd : ℕ
  nu : ℕ
  nv : ℕ
  ne : ℕ

/-- The monomial of a term in the five atoms. -/
def p11cPJKa (t : PJTerm) (Em0 Ep0 Em1 Ep1 S : ℂ) : ℂ :=
  Em0 ^ t.na * Ep0 ^ t.nb * Em1 ^ t.nc * Ep1 ^ t.nd * (Ep0 * Em1) ^ t.nu * (Em0 * Ep1) ^ t.nv *
    S ^ t.ne

/-- The value of a finite Fourier sum. -/
def p11cPJsum (L : List PJTerm) (Em0 Ep0 Em1 Ep1 S : ℂ) : ℂ :=
  (L.map fun t => t.coef * p11cPJKa t Em0 Ep0 Em1 Ep1 S).sum

/-- The charge of a term: the net exponent of the second angle. -/
def PJTerm.charge (t : PJTerm) : ℤ := (t.nb : ℤ) - t.na + t.nd - t.nc

/-- The Fourier index of a term in the first angle (after taking `λ₀ - λ₁` as the kernel angle). -/
def PJTerm.freq (t : PJTerm) : ℤ := (t.nb : ℤ) - t.na + t.nu - t.nv

theorem p11cPJE_pow (n : ℤ) (k : ℕ) (θ : ℝ) : p11cPJE n θ ^ k = p11cPJE (n * k) θ := by
  unfold p11cPJE
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem p11cPJKa_eq (a : ℝ) (t : PJTerm) (l : Fin 2 → ℝ) :
    p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1)) (p11cPJE 1 (l 1))
        ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
      p11cPJE t.freq (l 0) * p11cPJE (-t.freq + t.charge) (l 1) *
        (((p11cPJS a (l 0 - l 1)) ^ t.ne : ℝ) : ℂ) := by
  unfold p11cPJKa
  simp only [mul_pow, p11cPJE_pow]
  rw [Complex.ofReal_pow]
  have h1 : ∀ (n : ℤ), p11cPJE (-1 * n) (l 0) = p11cPJE (-n) (l 0) := fun n => by
    rw [neg_one_mul]
  have e0 : p11cPJE (-1 * (t.na : ℤ)) (l 0) * p11cPJE (1 * (t.nb : ℤ)) (l 0) *
      p11cPJE (1 * (t.nu : ℤ)) (l 0) * p11cPJE (-1 * (t.nv : ℤ)) (l 0) = p11cPJE t.freq (l 0) := by
    simp only [p11cPJE_add_int, PJTerm.freq]
    congr 1; ring
  have e1 : p11cPJE (-1 * (t.nc : ℤ)) (l 1) * p11cPJE (1 * (t.nd : ℤ)) (l 1) *
      p11cPJE (-1 * (t.nu : ℤ)) (l 1) * p11cPJE (1 * (t.nv : ℤ)) (l 1) =
        p11cPJE (-t.freq + t.charge) (l 1) := by
    simp only [p11cPJE_add_int, PJTerm.freq, PJTerm.charge]
    congr 1; ring
  rw [← e0, ← e1]
  ring

/-- The finite Fourier sum evaluated at the atoms of the angle pair `l`. -/
def p11cPJat (a : ℝ) (L : List PJTerm) (l : Fin 2 → ℝ) : ℂ :=
  p11cPJsum L (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1)) (p11cPJE 1 (l 1))
    ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)

theorem continuous_p11cPJKa {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (t : PJTerm) :
    Continuous fun l : Fin 2 → ℝ =>
      p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1)) (p11cPJE 1 (l 1))
        ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) := by
  have c0 : Continuous fun l : Fin 2 → ℝ => l 0 := continuous_apply 0
  have c1 : Continuous fun l : Fin 2 → ℝ => l 1 := continuous_apply 1
  have h0 : Continuous fun l : Fin 2 → ℝ => p11cPJE (-1) (l 0) :=
    (p11cPJE_continuous (-1)).comp c0
  have h1 : Continuous fun l : Fin 2 → ℝ => p11cPJE 1 (l 0) := (p11cPJE_continuous 1).comp c0
  have h2 : Continuous fun l : Fin 2 → ℝ => p11cPJE (-1) (l 1) :=
    (p11cPJE_continuous (-1)).comp c1
  have h3 : Continuous fun l : Fin 2 → ℝ => p11cPJE 1 (l 1) := (p11cPJE_continuous 1).comp c1
  have h4 : Continuous fun l : Fin 2 → ℝ => ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((p11cPJS_continuous ha).comp (c0.sub c1))
  unfold p11cPJKa
  fun_prop

theorem p11cPJ_term_integral {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (t : PJTerm) (ht : t.charge = 0) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
      p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1)) (p11cPJE 1 (l 1))
        ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) * ((2 * π * p11c_laplace ((t.ne : ℝ) / 2) t.freq a : ℝ) : ℂ) := by
  simp_rw [p11cPJKa_eq a t, ht, add_zero]
  have hgc : Continuous fun θ : ℝ => (((p11cPJS a θ) ^ t.ne : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((p11cPJS_continuous ha).pow _)
  have hgp : Function.Periodic (fun θ : ℝ => (((p11cPJS a θ) ^ t.ne : ℝ) : ℂ)) (2 * π) := by
    intro θ; simp only [p11cPJS_periodic a θ]
  rw [p11cPJ_cell_neutral hgc hgp t.freq, p11cPJ_laplace ha]

theorem p11cPJ_term_integral_charged {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (t : PJTerm)
    (ht : t.charge ≠ 0) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
      p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1)) (p11cPJE 1 (l 1))
        ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) = 0 := by
  simp_rw [p11cPJKa_eq a t]
  have hgc : Continuous fun θ : ℝ => (((p11cPJS a θ) ^ t.ne : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((p11cPJS_continuous ha).pow _)
  have hgp : Function.Periodic (fun θ : ℝ => (((p11cPJS a θ) ^ t.ne : ℝ) : ℂ)) (2 * π) := by
    intro θ; simp only [p11cPJS_periodic a θ]
  exact p11cPJ_cell_charged hgc hgp (by simpa using ht)

theorem p11cPJat_integrableOn {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (L : List PJTerm) :
    IntegrableOn (fun l => p11cPJat a L l)
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := by
  have hint : ∀ t : PJTerm, IntegrableOn (fun l : Fin 2 → ℝ =>
      t.coef * p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1))
        (p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ))
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := fun t =>
    (continuous_const.mul (continuous_p11cPJKa ha t)).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  induction L with
  | nil => simp [p11cPJat, p11cPJsum]
  | cons t L ih =>
    have e : ∀ l, p11cPJat a (t :: L) l =
        t.coef * p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1))
          (p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) + p11cPJat a L l := by
      intro l
      simp [p11cPJat, p11cPJsum, List.map_cons, List.sum_cons]
    simp_rw [e]
    exact (hint t).add ih

theorem p11cPJ_sum_integral {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (L : List PJTerm) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), p11cPJat a L l =
      (L.map fun t => t.coef * ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1))
          (p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).sum := by
  have hint : ∀ t : PJTerm, IntegrableOn (fun l : Fin 2 → ℝ =>
      t.coef * p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1))
        (p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ))
      (Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))) volume := fun t =>
    (continuous_const.mul (continuous_p11cPJKa ha t)).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  induction L with
  | nil => simp [p11cPJat, p11cPJsum]
  | cons t L ih =>
    have e : ∀ l, p11cPJat a (t :: L) l =
        t.coef * p11cPJKa t (p11cPJE (-1) (l 0)) (p11cPJE 1 (l 0)) (p11cPJE (-1) (l 1))
          (p11cPJE 1 (l 1)) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ) + p11cPJat a L l := by
      intro l
      simp [p11cPJat, p11cPJsum, List.map_cons, List.sum_cons]
    simp_rw [e]
    have hL := p11cPJat_integrableOn ha L
    rw [integral_add (hint t) hL, ih, List.map_cons, List.sum_cons, integral_const_mul]

theorem p11cPJ_sum_integral_charged {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (L : List PJTerm)
    (h : ∀ t ∈ L, t.charge ≠ 0) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), p11cPJat a L l = 0 := by
  rw [p11cPJ_sum_integral ha]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  rw [p11cPJ_term_integral_charged ha t (h t ht), mul_zero]

theorem p11cPJ_sum_integral_neutral {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (L : List PJTerm)
    (h : ∀ t ∈ L, t.charge = 0) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)), p11cPJat a L l =
      (L.map fun t => t.coef * (((2 * π : ℝ) : ℂ) *
        ((2 * π * p11c_laplace ((t.ne : ℝ) / 2) t.freq a : ℝ) : ℂ))).sum := by
  rw [p11cPJ_sum_integral ha]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [p11cPJ_term_integral ha t (h t ht)]

end KAM.Planetary

end
