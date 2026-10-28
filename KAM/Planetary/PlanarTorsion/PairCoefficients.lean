/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.LaplaceReduction
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.PairCoefficients.Laplace

/-!
# Planar quartic torsion: the pair coefficients `A, B, p₁, …, p₆` (P11C, package T4)

Blueprint P, Part 11b (`bpP:p11b:pair-jet`): the eight rational coefficients `p11c_pairCoeffs`
written in `b_{1/2}^{(0)}, b_{1/2}^{(1)}`, their analyticity on `(-1, 1)` and the explicit series
(`pair_series`), and the identification of the first two with `b_{3/2}^{(1)}, b_{3/2}^{(2)}`
(`pair_quadratic_consistency`).

The coefficients are expressed through `p11c_laplace (1/2) 0/1`, which on `(-1, 1)` is the Part-8
power series `p11cHalf`. Writing `b_k = head_k + a ^ 8 * tail_k` with `tail_k` analytic, every
component of `p11c_pairCoeffs - p11c_pairSeriesJet` is `a ^ m * (analytic)`; the exact polynomial
identities behind this are finite and checked by `ring`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter
open scoped ContDiff Topology
namespace KAM.Planetary

/-- [A,B,p1,...,p6], exactly the displayed rational formulas. -/
def p11c_pairCoeffs (a : ℝ) : Fin 8 → ℝ :=
  let b0 := p11c_laplace (1 / 2) 0 a
  let b1 := p11c_laplace (1 / 2) 1 a
  let D := 1 - a ^ 2
  ![a * (2 * a * b0 - (1 + a ^ 2) * b1) / (4 * D ^ 2),
    (2 * (1 - a ^ 2 + a ^ 4) * b1 - a * (1 + a ^ 2) * b0) / (2 * D ^ 2),
    a * ((a + 14 * a ^ 3 + 33 * a ^ 5) * b0 - (2 - 6 * a ^ 2 + 46 * a ^ 4 + 6 * a ^ 6) * b1) / (64 * D ^ 4),
    a * ((33 * a + 14 * a ^ 3 + a ^ 5) * b0 - (6 + 46 * a ^ 2 - 6 * a ^ 4 + 2 * a ^ 6) * b1) / (64 * D ^ 4),
    3 * a * ((7 * a + 2 * a ^ 3 + 7 * a ^ 5) * b0 - (2 + 6 * a ^ 2 + 6 * a ^ 4 + 2 * a ^ 6) * b1) / (32 * D ^ 4),
    3 * a * ((-a + 18 * a ^ 3 - a ^ 5) * b0 + (2 - 10 * a ^ 2 - 10 * a ^ 4 + 2 * a ^ 6) * b1) / (16 * D ^ 4),
    ((4 - 15 * a ^ 2 + 50 * a ^ 4 + 9 * a ^ 6) * b1 - (2 * a + 4 * a ^ 3 + 42 * a ^ 5) * b0) / (16 * D ^ 4),
    a ^ 2 * ((9 + 50 * a ^ 2 - 15 * a ^ 4 + 4 * a ^ 6) * b1 - (42 * a + 4 * a ^ 3 + 2 * a ^ 5) * b0) / (16 * D ^ 4)]

def p11c_pairSeriesJet (a : ℝ) : Fin 8 → ℝ :=
  ![3 / 8 * a ^ 2 + 45 / 64 * a ^ 4 + 525 / 512 * a ^ 6,
    -15 / 16 * a ^ 3 - 105 / 64 * a ^ 5 - 4725 / 2048 * a ^ 7,
    135 / 512 * a ^ 4 + 2625 / 2048 * a ^ 6,
    15 / 32 * a ^ 2 + 945 / 512 * a ^ 4 + 4725 / 1024 * a ^ 6,
    9 / 16 * a ^ 2 + 585 / 256 * a ^ 4 + 1575 / 256 * a ^ 6,
    315 / 128 * a ^ 4 + 4725 / 512 * a ^ 6,
    -45 / 64 * a ^ 3 - 525 / 128 * a ^ 5,
    -75 / 32 * a ^ 3 - 2205 / 256 * a ^ 5]

/-! ### The coefficients as `(N₀ b₀ + N₁ b₁) / Dn` -/

/-- Numerator of `b_{1/2}^{(0)}` in the `i`-th coefficient. -/
def p11cN0 : Fin 8 → ℝ → ℝ :=
  ![fun a => 2 * a ^ 2, fun a => -(a * (1 + a ^ 2)),
    fun a => a * (a + 14 * a ^ 3 + 33 * a ^ 5), fun a => a * (33 * a + 14 * a ^ 3 + a ^ 5),
    fun a => 3 * a * (7 * a + 2 * a ^ 3 + 7 * a ^ 5), fun a => 3 * a * (-a + 18 * a ^ 3 - a ^ 5),
    fun a => -(2 * a + 4 * a ^ 3 + 42 * a ^ 5), fun a => -(a ^ 2 * (42 * a + 4 * a ^ 3 + 2 * a ^ 5))]

/-- Numerator of `b_{1/2}^{(1)}` in the `i`-th coefficient. -/
def p11cN1 : Fin 8 → ℝ → ℝ :=
  ![fun a => -(a * (1 + a ^ 2)), fun a => 2 * (1 - a ^ 2 + a ^ 4),
    fun a => -(a * (2 - 6 * a ^ 2 + 46 * a ^ 4 + 6 * a ^ 6)),
    fun a => -(a * (6 + 46 * a ^ 2 - 6 * a ^ 4 + 2 * a ^ 6)),
    fun a => -(3 * a * (2 + 6 * a ^ 2 + 6 * a ^ 4 + 2 * a ^ 6)),
    fun a => 3 * a * (2 - 10 * a ^ 2 - 10 * a ^ 4 + 2 * a ^ 6),
    fun a => 4 - 15 * a ^ 2 + 50 * a ^ 4 + 9 * a ^ 6,
    fun a => a ^ 2 * (9 + 50 * a ^ 2 - 15 * a ^ 4 + 4 * a ^ 6)]

/-- Denominator of the `i`-th coefficient. -/
def p11cDn : Fin 8 → ℝ → ℝ :=
  ![fun a => 4 * (1 - a ^ 2) ^ 2, fun a => 2 * (1 - a ^ 2) ^ 2, fun a => 64 * (1 - a ^ 2) ^ 4,
    fun a => 64 * (1 - a ^ 2) ^ 4, fun a => 32 * (1 - a ^ 2) ^ 4, fun a => 16 * (1 - a ^ 2) ^ 4,
    fun a => 16 * (1 - a ^ 2) ^ 4, fun a => 16 * (1 - a ^ 2) ^ 4]

/-- Order of vanishing of the `i`-th coefficient minus its series jet. -/
def p11cOrd : Fin 8 → ℕ := ![8, 8, 8, 8, 8, 8, 7, 7]

/-- The exact quotient `(N₀ head₀ + N₁ head₁ - Dn jet) / a ^ ord`. -/
def p11cQuot : Fin 8 → ℝ → ℝ :=
  ![
    fun a => (11025/2048:ℝ) * a^0 + (-8575/2048:ℝ) * a^2,
    fun a => (-6125/1024:ℝ) * a^1 + (1225/256:ℝ) * a^3,
    fun a => (231525/1024:ℝ) * a^0 + (-434875/1024:ℝ) * a^2 + (317275/1024:ℝ) * a^4 + (-84525/1024:ℝ) * a^6,
    fun a => (606375/1024:ℝ) * a^0 + (-1363425/1024:ℝ) * a^2 + (1089025/1024:ℝ) * a^4 + (-302575/1024:ℝ) * a^6,
    fun a => (429975/1024:ℝ) * a^0 + (-929775/1024:ℝ) * a^2 + (731325/1024:ℝ) * a^4 + (-202125/1024:ℝ) * a^6,
    fun a => (363825/1024:ℝ) * a^0 + (-746025/1024:ℝ) * a^2 + (562275/1024:ℝ) * a^4 + (-150675/1024:ℝ) * a^6,
    fun a => (-99225/512:ℝ) * a^0 + (714175/2048:ℝ) * a^2 + (-256025/1024:ℝ) * a^4 + (135975/2048:ℝ) * a^6,
    fun a => (-42525/128:ℝ) * a^0 + (1387575/2048:ℝ) * a^2 + (-523425/1024:ℝ) * a^4 + (280175/2048:ℝ) * a^6 + (175/512:ℝ) * a^8]

theorem p11c_pairCoeffs_apply (a : ℝ) (i : Fin 8) :
    p11c_pairCoeffs a i = (p11cN0 i a * p11c_laplace (1 / 2) 0 a +
      p11cN1 i a * p11c_laplace (1 / 2) 1 a) / p11cDn i a := by
  fin_cases i <;> simp [p11c_pairCoeffs, p11cN0, p11cN1, p11cDn] <;> ring

theorem p11c_laplace_half_zero {x : ℝ} (hx : |x| < 1) :
    p11c_laplace (1 / 2) 0 x = p11cHalf 0 x := by simpa using p11c_laplace_half 0 hx

theorem p11c_laplace_half_one {x : ℝ} (hx : |x| < 1) :
    p11c_laplace (1 / 2) 1 x = p11cHalf 1 x := by simpa using p11c_laplace_half 1 hx

theorem p11cDn_ne {a : ℝ} (ha : |a| < 1) (i : Fin 8) : p11cDn i a ≠ 0 := by
  have h : 0 < 1 - a ^ 2 := by nlinarith [abs_lt.1 ha, sq_abs a]
  fin_cases i <;> simp only [p11cDn] <;>
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h.ne')

theorem p11cOrd_le (i : Fin 8) : p11cOrd i ≤ 8 := by fin_cases i <;> simp [p11cOrd]

theorem p11cOrd_ge (i : Fin 8) : 7 ≤ p11cOrd i := by fin_cases i <;> simp [p11cOrd]

theorem p11c_pair_identity (i : Fin 8) (a : ℝ) :
    p11cN0 i a * p11cHead 0 a + p11cN1 i a * p11cHead 1 a - p11cDn i a * p11c_pairSeriesJet a i =
      a ^ p11cOrd i * p11cQuot i a := by
  rw [p11cHead_zero, p11cHead_one]
  fin_cases i <;> simp [p11cN0, p11cN1, p11cDn, p11cOrd, p11cQuot, p11c_pairSeriesJet] <;> ring

section Analytic

theorem p11cN0_analyticAt (i : Fin 8) (x : ℝ) : AnalyticAt ℝ (p11cN0 i) x := by
  fin_cases i <;> simp only [p11cN0] <;> simp <;> fun_prop

theorem p11cN1_analyticAt (i : Fin 8) (x : ℝ) : AnalyticAt ℝ (p11cN1 i) x := by
  fin_cases i <;> simp only [p11cN1] <;> simp <;> fun_prop

theorem p11cDn_analyticAt (i : Fin 8) (x : ℝ) : AnalyticAt ℝ (p11cDn i) x := by
  fin_cases i <;> simp only [p11cDn] <;> simp <;> fun_prop

theorem p11cQuot_analyticAt (i : Fin 8) (x : ℝ) : AnalyticAt ℝ (p11cQuot i) x := by
  fin_cases i <;> simp only [p11cQuot] <;> simp <;> fun_prop

theorem p11c_pairSeriesJet_analyticAt (i : Fin 8) (x : ℝ) :
    AnalyticAt ℝ (fun a => p11c_pairSeriesJet a i) x := by
  fin_cases i <;> simp only [p11c_pairSeriesJet] <;> simp <;> fun_prop

theorem p11c_abs_lt_one_nhds {a : ℝ} (ha : |a| < 1) : ∀ᶠ x in 𝓝 a, |x| < 1 :=
  (isOpen_lt continuous_abs continuous_const).mem_nhds ha

theorem p11c_comp_analyticAt {a : ℝ} (ha : |a| < 1) (i : Fin 8) :
    AnalyticAt ℝ (fun x => p11c_pairCoeffs x i) a := by
  have e : (fun x => p11c_pairCoeffs x i) =ᶠ[𝓝 a] fun x =>
      (p11cN0 i x * p11cHalf 0 x + p11cN1 i x * p11cHalf 1 x) / p11cDn i x := by
    filter_upwards [p11c_abs_lt_one_nhds ha] with x hx
    rw [p11c_pairCoeffs_apply, p11c_laplace_half_zero hx, p11c_laplace_half_one hx]
  refine AnalyticAt.congr ?_ e.symm
  exact (((p11cN0_analyticAt i a).mul (p11cHalf_analyticAt 0 ha)).add
    ((p11cN1_analyticAt i a).mul (p11cHalf_analyticAt 1 ha))).div (p11cDn_analyticAt i a)
    (p11cDn_ne ha i)

theorem p11c_comp_vanishes (i : Fin 8) :
    p11cVanishes (p11cOrd i) (fun a => p11c_pairCoeffs a i - p11c_pairSeriesJet a i) := by
  have h0 : |(0 : ℝ)| < 1 := by simp
  refine ⟨fun a => (p11cQuot i a + a ^ (8 - p11cOrd i) * (p11cN0 i a * p11cTail 0 a +
    p11cN1 i a * p11cTail 1 a)) / p11cDn i a, ?_, ?_⟩
  · exact (((p11cQuot_analyticAt i 0).add ((analyticAt_id.pow _).mul
      (((p11cN0_analyticAt i 0).mul (p11cTail_analyticAt 0 h0)).add
        ((p11cN1_analyticAt i 0).mul (p11cTail_analyticAt 1 h0)))))).div
      (p11cDn_analyticAt i 0) (p11cDn_ne h0 i)
  · filter_upwards [p11c_abs_lt_one_nhds h0] with a ha
    rw [p11c_pairCoeffs_apply, p11c_laplace_half_zero ha, p11c_laplace_half_one ha,
      p11cHalf_eq_head_add 0 ha, p11cHalf_eq_head_add 1 ha]
    have hD := p11cDn_ne ha i
    have hid := p11c_pair_identity i a
    have e8 : a ^ 8 = a ^ (p11cOrd i) * a ^ (8 - p11cOrd i) := by
      rw [← pow_add]; congr 1; have := p11cOrd_le i; omega
    rw [e8]
    field_simp
    linear_combination hid

theorem p11c_iteratedFDeriv_eq_of_vanishes_real {m : ℕ} {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) (hv : p11cVanishes m (fun a => f a - g a)) :
    ∀ j < m, iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0 := fun j hj =>
  ContinuousMultilinearMap.ext_ring (by
    rw [← iteratedDeriv_eq_iteratedFDeriv, ← iteratedDeriv_eq_iteratedFDeriv]
    exact p11c_iteratedDeriv_eq_of_vanishes hf hg hv j hj)

end Analytic

theorem pair_series :
    AnalyticOnNhd ℝ p11c_pairCoeffs (Ioo (-1 : ℝ) 1) ∧
    p11c_JetEq 6 p11c_pairCoeffs p11c_pairSeriesJet ∧
    p11c_JetEq 7 (fun a => p11c_pairCoeffs a 1) (fun a => p11c_pairSeriesJet a 1) := by
  have h0 : |(0 : ℝ)| < 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · exact (analyticOnNhd_pi_iff (f := fun i x => p11c_pairCoeffs x i)).2 fun i a ha =>
      p11c_comp_analyticAt (abs_lt.2 ha) i
  · intro j hj
    exact p11c_iteratedFDeriv_eq_of_vanishes (m := 7)
      (fun i => p11c_comp_analyticAt h0 i) (fun i => p11c_pairSeriesJet_analyticAt i 0)
      (fun i => (p11c_comp_vanishes i).mono (p11cOrd_ge i)) j (by omega)
  · intro j hj
    have hv := p11c_comp_vanishes 1
    have h8 : p11cOrd 1 = 8 := by simp [p11cOrd]
    rw [h8] at hv
    exact p11c_iteratedFDeriv_eq_of_vanishes_real (p11c_comp_analyticAt h0 1)
      (p11c_pairSeriesJet_analyticAt 1 0) hv j (by omega)

theorem pair_quadratic_consistency (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_pairCoeffs a 0 = a * p11c_laplace (3 / 2) 1 a / 4 ∧
    p11c_pairCoeffs a 1 = -a * p11c_laplace (3 / 2) 2 a / 2 := by
  obtain ⟨h0, h1, h2⟩ := laplace_up (1 / 2) a le_rfl ha
  have e : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [e] at h0 h1 h2
  have h2' := h2 1 le_rfl
  have hD : 1 - a ^ 2 ≠ 0 := p11c_one_sub_sq_ne ha
  have ha0 : a ≠ 0 := ha.1.ne'
  norm_num at h2'
  have c0 : p11c_pairCoeffs a 0 = a * (2 * a * p11c_laplace (1 / 2) 0 a -
      (1 + a ^ 2) * p11c_laplace (1 / 2) 1 a) / (4 * (1 - a ^ 2) ^ 2) := rfl
  have c1 : p11c_pairCoeffs a 1 = (2 * (1 - a ^ 2 + a ^ 4) * p11c_laplace (1 / 2) 1 a -
      a * (1 + a ^ 2) * p11c_laplace (1 / 2) 0 a) / (2 * (1 - a ^ 2) ^ 2) := rfl
  constructor
  · rw [c0, h1]
    field_simp
    ring
  · rw [c1, h2', h0]
    field_simp
    ring

end KAM.Planetary
