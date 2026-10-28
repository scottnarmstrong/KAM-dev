/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.SecularForm.Laplace

/-!
# Secular form: Laplace-coefficient identities and the radial functions

Blueprint P, Part 8 (`bpP:p8:identities`): the two differential identities satisfied by the
half-integer Laplace coefficients `b_{1/2}^{(0)}`, `b_{1/2}^{(1)}` in terms of `b_{3/2}^{(1)}`,
`b_{3/2}^{(2)}`, proved by termwise differentiation of the binomial power series; and the radial
functions `radialPhi`, `radialH` of the quartic coefficients.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-! ### Termwise differentiation of power series with polynomially bounded coefficients -/

/-- Termwise differentiation of `∑ a q z^(e q)` inside the unit disc. -/
theorem hasDerivAt_tsum_pow (a : ℕ → ℝ) (e : ℕ → ℕ) (C : ℝ) (m j : ℕ)
    (hb : ∀ q, |a q| ≤ C * ((q : ℝ) + 1) ^ m) (he : ∀ q, e q ≤ 2 * q + 2)
    (hj : ∀ q, q ≤ e q + j) {y : ℝ} (hy : |y| < 1) :
    Summable (fun q => a q * ((e q : ℝ) * y ^ (e q - 1))) ∧
    HasDerivAt (fun z => ∑' q, a q * z ^ (e q)) (∑' q, a q * ((e q : ℝ) * y ^ (e q - 1))) y := by
  have hC : 0 ≤ C := by
    have := hb 0
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  set r : ℝ := (|y| + 1) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hyr : |y| < r := by rw [hr]; linarith
  have hrn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0.le]; exact hr1
  have hpr : 0 < r ^ (j + 1) := pow_pos hr0 _
  set u : ℕ → ℝ := fun q => (2 * C / r ^ (j + 1)) * (((q : ℝ) + 1) ^ (m + 1) * r ^ q) with hu
  have hsum : Summable (fun q : ℕ => ((q : ℝ) + 1) ^ (m + 1) * r ^ q) := by
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (m + 1) * r ^ n) 1).2
      (summable_pow_mul_geometric_of_norm_lt_one (m + 1) hrn)
    have h2 := h1.mul_right r⁻¹
    refine h2.congr fun q => ?_
    push_cast
    rw [pow_succ]
    field_simp
    ring
  have hu_sum : Summable u := hsum.mul_left _
  have hgeo : ∀ q, r ^ (e q - 1) ≤ r ^ q / r ^ (j + 1) := by
    intro q
    have h1 : r ^ (e q - 1) ≤ r ^ (q - (j + 1)) :=
      pow_le_pow_of_le_one hr0.le hr1.le (by have := hj q; omega)
    refine h1.trans ?_
    rw [le_div_iff₀ hpr]
    by_cases hq : j + 1 ≤ q
    · rw [← pow_add, Nat.sub_add_cancel hq]
    · have h0 : q - (j + 1) = 0 := by omega
      rw [h0, pow_zero, one_mul]
      exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  have hbound : ∀ q (z : ℝ), |z| ≤ r →
      ‖a q * ((e q : ℝ) * z ^ (e q - 1))‖ ≤ u q := by
    intro q z hz
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have h1 : |z| ^ (e q - 1) ≤ r ^ q / r ^ (j + 1) :=
      (pow_le_pow_left₀ (abs_nonneg _) hz _).trans (hgeo q)
    have h2 : (e q : ℝ) ≤ 2 * q + 2 := by exact_mod_cast he q
    have h3 := hb q
    calc |a q| * ((e q : ℝ) * |z| ^ (e q - 1))
        ≤ (C * ((q : ℝ) + 1) ^ m) * ((2 * q + 2) * (r ^ q / r ^ (j + 1))) := by
          gcongr
      _ = u q := by rw [hu]; simp only; ring
  have hy0 : Summable (fun q => a q * (0 : ℝ) ^ (e q)) := by
    refine summable_of_ne_finset_zero (s := Finset.range (j + 1)) fun q hq => ?_
    have : e q ≠ 0 := by
      have := hj q
      simp only [Finset.mem_range, not_lt] at hq
      omega
    simp [this]
  have hmem : y ∈ Metric.ball (0 : ℝ) r := by simpa [Real.norm_eq_abs] using hyr
  refine ⟨Summable.of_norm_bounded hu_sum fun q => hbound q y hyr.le, ?_⟩
  exact hasDerivAt_tsum_of_isPreconnected (g := fun q z => a q * z ^ (e q))
    (g' := fun q z => a q * ((e q : ℝ) * z ^ (e q - 1))) (y₀ := 0) hu_sum Metric.isOpen_ball
    (convex_ball _ _).isPreconnected
    (fun q z _ => (hasDerivAt_pow (e q) z).const_mul (a q))
    (fun q z hz => hbound q z (by
      have : ‖z‖ < r := by simpa using hz
      rw [Real.norm_eq_abs] at this; exact this.le))
    (Metric.mem_ball_self hr0) hy0 hmem

/-! ### Half-integer Laplace coefficients as power series -/

/-- The power-series coefficient of `b_{1/2}^{(k)}`. -/
def halfCoef (k q : ℕ) : ℝ := pcoef (1/2) (q + k) * pcoef (1/2) q

theorem pcoef_succ (s : ℝ) (q : ℕ) : pcoef s (q + 1) = pcoef s q * ((s + q) / (q + 1)) := by
  unfold pcoef
  rw [poch_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem pcoef_half_le_one (q : ℕ) : pcoef (1/2) q ≤ 1 := by
  induction q with
  | zero => simp [pcoef, poch]
  | succ q ih =>
    rw [pcoef_succ]
    have h0 := pcoef_nonneg (s := 1/2) (by norm_num) q
    have h1 : ((1/2 : ℝ) + q) / (q + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc pcoef (1/2) q * (((1/2 : ℝ) + q) / (q + 1)) ≤ 1 * 1 := by
          gcongr
      _ = 1 := one_mul 1

theorem halfCoef_abs_le (k q : ℕ) : |halfCoef k q| ≤ 1 * ((q : ℝ) + 1) ^ 0 := by
  have h1 := pcoef_nonneg (s := 1/2) (by norm_num) (q + k)
  have h2 := pcoef_nonneg (s := 1/2) (by norm_num) q
  have h3 := pcoef_half_le_one (q + k)
  have h4 := pcoef_half_le_one q
  rw [abs_of_nonneg (by unfold halfCoef; positivity), pow_zero, one_mul]
  exact (mul_le_mul h3 h4 h2 zero_le_one).trans (by norm_num)

theorem laplaceTerm_half (k q : ℕ) (α : ℝ) :
    laplaceTerm (1/2) k q α = halfCoef k q * α ^ (2 * q + k) := by
  unfold laplaceTerm halfCoef pcoef
  rw [div_mul_div_comm]

theorem laplace_def_half_eventually {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    laplace_def (1/2) k =ᶠ[𝓝 α]
      fun z => ∑' q, halfCoef k q * z ^ (2 * q + k) := by
  filter_upwards [isOpen_Ioo.mem_nhds hα] with z hz
  rw [← (hasSum_laplaceTerm (by norm_num) hz.1.le hz.2 k).tsum_eq]
  exact tsum_congr fun q => laplaceTerm_half k q z

/-- First derivative of `b_{1/2}^{(k)}`. -/
theorem half_deriv1 {k : ℕ} (hk : k ≤ 2) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Summable (fun q => halfCoef k q * (((2 * q + k : ℕ) : ℝ) * α ^ (2 * q + k - 1))) ∧
    HasDerivAt (laplace_def (1/2) k)
      (∑' q, halfCoef k q * (((2 * q + k : ℕ) : ℝ) * α ^ (2 * q + k - 1))) α := by
  have hy : |α| < 1 := by rw [abs_of_pos hα.1]; exact hα.2
  obtain ⟨h1, h2⟩ := hasDerivAt_tsum_pow (halfCoef k) (fun q => 2 * q + k) 1 0 0
    (halfCoef_abs_le k) (fun q => by omega) (fun q => by omega) hy
  exact ⟨h1, h2.congr_of_eventuallyEq (laplace_def_half_eventually hα)⟩

/-- Second derivative of `b_{1/2}^{(k)}`. -/
theorem half_deriv2 {k : ℕ} (hk : k ≤ 2) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Summable (fun q => (halfCoef k q * ((2 * q + k : ℕ) : ℝ)) *
      ((((2 * q + k - 1 : ℕ)) : ℝ) * α ^ (2 * q + k - 1 - 1))) ∧
    iteratedDeriv 2 (laplace_def (1/2) k) α =
      ∑' q, (halfCoef k q * ((2 * q + k : ℕ) : ℝ)) *
        ((((2 * q + k - 1 : ℕ)) : ℝ) * α ^ (2 * q + k - 1 - 1)) := by
  have hy : |α| < 1 := by rw [abs_of_pos hα.1]; exact hα.2
  obtain ⟨h1, h2⟩ := hasDerivAt_tsum_pow (fun q => halfCoef k q * ((2 * q + k : ℕ) : ℝ))
    (fun q => 2 * q + k - 1) 2 1 1
    (fun q => by
      have := halfCoef_abs_le k q
      have h5 : ((2 * q + k : ℕ) : ℝ) ≤ 2 * ((q : ℝ) + 1) := by
        have : 2 * q + k ≤ 2 * q + 2 := by omega
        have h6 : ((2 * q + k : ℕ) : ℝ) ≤ ((2 * q + 2 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h6 ⊢; linarith
      rw [abs_mul, Nat.abs_cast]
      calc |halfCoef k q| * ((2 * q + k : ℕ) : ℝ)
          ≤ (1 * ((q : ℝ) + 1) ^ 0) * (2 * ((q : ℝ) + 1)) := by gcongr
        _ = 2 * ((q : ℝ) + 1) ^ 1 := by ring)
    (fun q => by omega) (fun q => by omega) hy
  refine ⟨h1, ?_⟩
  have hev : deriv (laplace_def (1/2) k) =ᶠ[𝓝 α]
      fun z => ∑' q, (halfCoef k q * ((2 * q + k : ℕ) : ℝ)) * z ^ (2 * q + k - 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds hα] with z hz
    rw [(half_deriv1 hk hz).2.deriv]
    exact tsum_congr fun q => by ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  exact h2.deriv

/-! ### The identities -/

theorem poch_succ' (s : ℝ) (q : ℕ) : poch s (q + 1) = s * poch (s + 1) q := by
  unfold poch
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => by ring

theorem poch_three_halves (q : ℕ) : poch (3/2) q = 2 * poch (1/2) (q + 1) := by
  rw [poch_succ' (1/2)]
  norm_num
  ring

theorem pow_aux1 (α : ℝ) (e : ℕ) : α * ((e : ℝ) * α ^ (e - 1)) = e * α ^ e := by
  cases e with
  | zero => simp
  | succ e => simp [pow_succ]; ring

theorem pow_aux2 (α : ℝ) (e : ℕ) :
    α ^ 2 * ((e : ℝ) * (((e - 1 : ℕ) : ℝ) * α ^ (e - 1 - 1))) = e * (e - 1) * α ^ e := by
  rcases e with _ | _ | e
  · simp
  · simp
  · simp [pow_succ]; ring

theorem hasSum_shift_unique {f g : ℕ → ℝ} {L M : ℝ} (hf : HasSum f L) (hg : HasSum g M)
    (h0 : f 0 = 0) (hfg : ∀ q, f (q + 1) = g q) : L = M := by
  have h1 := (hasSum_nat_add_iff' 1).2 hf
  simp only [Finset.range_one, Finset.sum_singleton, h0, sub_zero, hfg] at h1
  exact h1.unique hg

theorem poch_half_two (q : ℕ) :
    poch (1/2) (q + 1) = poch (1/2) q * (1/2 + q) := poch_succ _ _

theorem term_comb1 (h α : ℝ) (e : ℕ) :
    α ^ 2 * (h * e * (((e - 1 : ℕ) : ℝ) * α ^ (e - 1 - 1))) + 2 * α * (h * ((e : ℝ) * α ^ (e - 1))) =
      h * ((e : ℝ) * (e - 1) + 2 * e) * α ^ e := by
  linear_combination h * pow_aux2 α e + 2 * h * pow_aux1 α e

theorem term_comb2 (h α : ℝ) (e : ℕ) :
    α * (h * ((e : ℝ) * α ^ (e - 1))) + α ^ 2 / 2 * (h * e * (((e - 1 : ℕ) : ℝ) * α ^ (e - 1 - 1))) -
      h * α ^ e = h * ((e : ℝ) + e * (e - 1) / 2 - 1) * α ^ e := by
  linear_combination h * pow_aux1 α e + h / 2 * pow_aux2 α e

theorem coef1 (q : ℕ) :
    halfCoef 0 (q + 1) * (((2 * (q + 1) + 0 : ℕ) : ℝ) * (((2 * (q + 1) + 0 : ℕ) : ℝ) - 1) +
      2 * ((2 * (q + 1) + 0 : ℕ) : ℝ)) =
    poch (3/2) (q + 1) * poch (3/2) q / (((q + 1).factorial : ℝ) * q.factorial) := by
  have hq : (0 : ℝ) < q.factorial := by exact_mod_cast q.factorial_pos
  unfold halfCoef pcoef
  rw [poch_three_halves, poch_three_halves, poch_succ (1/2) (q + 1), poch_succ (1/2) q]
  simp only [add_zero, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem coef2 (q : ℕ) :
    halfCoef 1 (q + 1) * (((2 * (q + 1) + 1 : ℕ) : ℝ) +
      ((2 * (q + 1) + 1 : ℕ) : ℝ) * (((2 * (q + 1) + 1 : ℕ) : ℝ) - 1) / 2 - 1) =
    1 / 2 * (poch (3/2) (q + 2) * poch (3/2) q / (((q + 2).factorial : ℝ) * q.factorial)) := by
  have hq : (0 : ℝ) < q.factorial := by exact_mod_cast q.factorial_pos
  unfold halfCoef pcoef
  rw [poch_three_halves, poch_three_halves]
  simp only [show q + 2 = q + 1 + 1 from rfl, poch_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem identities {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    α^2 * iteratedDeriv 2 (laplace_def (1/2) 0) α + 2*α*deriv (laplace_def (1/2) 0) α =
      α * laplace_def (3/2) 1 α ∧
    α * deriv (laplace_def (1/2) 1) α + α^2/2 * iteratedDeriv 2 (laplace_def (1/2) 1) α -
      laplace_def (1/2) 1 α = α/2 * laplace_def (3/2) 2 α := by
  have hmem : α ∈ Ioo (0 : ℝ) 1 := ⟨hα, hα1⟩
  have key : ∀ k : ℕ, k ≤ 2 →
      HasSum (fun q => halfCoef k q * (((2 * q + k : ℕ) : ℝ) * α ^ (2 * q + k - 1)))
        (deriv (laplace_def (1/2) k) α) ∧
      HasSum (fun q => (halfCoef k q * ((2 * q + k : ℕ) : ℝ)) *
        ((((2 * q + k - 1 : ℕ)) : ℝ) * α ^ (2 * q + k - 1 - 1)))
        (iteratedDeriv 2 (laplace_def (1/2) k) α) ∧
      HasSum (fun q => halfCoef k q * α ^ (2 * q + k)) (laplace_def (1/2) k α) := by
    intro k hk
    obtain ⟨s1, d1⟩ := half_deriv1 hk hmem
    obtain ⟨s2, d2⟩ := half_deriv2 hk hmem
    refine ⟨?_, ?_, ?_⟩
    · rw [d1.deriv]; exact s1.hasSum
    · rw [d2]; exact s2.hasSum
    · have := hasSum_laplaceTerm (s := 1/2) (by norm_num) hα.le hα1 k
      simpa only [laplaceTerm_half] using this
  have lap32 : ∀ k : ℕ, HasSum (fun q => laplaceTerm (3/2) k q α) (laplace_def (3/2) k α) :=
    fun k => hasSum_laplaceTerm (by norm_num) hα.le hα1 k
  constructor
  · obtain ⟨h1, h2, -⟩ := key 0 (by norm_num)
    have H := (h2.mul_left (α ^ 2)).add (h1.mul_left (2 * α))
    have G := (lap32 1).mul_left α
    simp only [Nat.cast_zero] at H ⊢
    refine hasSum_shift_unique H G ?_ fun q => ?_
    · simp
    · refine (term_comb1 _ _ _).trans ?_
      simp only [laplaceTerm]
      have hp : α ^ (2 * (q + 1) + 0) = α * α ^ (2 * q + 1) := by ring
      rw [coef1 q, hp]
      ring
  · obtain ⟨h1, h2, h3⟩ := key 1 (by norm_num)
    have H := ((h1.mul_left α).add (h2.mul_left (α ^ 2 / 2))).sub h3
    have G := (lap32 2).mul_left (α / 2)
    simp only [Nat.cast_one] at H ⊢
    refine hasSum_shift_unique H G ?_ fun q => ?_
    · simp; ring
    · refine (term_comb2 _ _ _).trans ?_
      simp only [laplaceTerm]
      have hp : α ^ (2 * (q + 1) + 1) = α * α ^ (2 * q + 2) := by ring
      rw [coef2 q, hp]
      ring

/-! ### Radial functions of the quartic coefficients -/

def radialPhi (a b : ℝ) : ℝ := (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
  (a^2+b^2-2*a*b*Real.cos t) ^ (-1/2 : ℝ)
def radialH (a b ε : ℝ) : ℝ := radialPhi (a*(1-ε)) b * (1-ε)

end SecularForm
end KAM.Planetary
