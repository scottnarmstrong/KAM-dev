/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Constants
public import KAM.Planetary.MaximalStep.FourierCutoffTail

/-!
# The loss of the Fourier cutoff (P11A-C2)

`loss_choice` (`bpP:p11a:loss-choice`): with `d_T(α) = p11Loss n T α` the cutoff error
`p11Error n T d_T` is at most `α` once `d_T ≤ 1`, and `d_T(α)` is antitone in `T ∈ [1,∞)` and in
`α ∈ (0,1]`. `loss_sum` (`bpP:p11a:loss-sum`): the geometric and arithmetico-geometric sums of the
losses along `T_ν = T₀ θ^ν`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace KAM.Planetary

/-- `1 < log (π T)` for `T ≥ 1`. -/
private theorem one_lt_log_piT {T : ℝ} (hT : 1 ≤ T) : 1 < Real.log (Real.pi * T) := by
  have hpi := Real.pi_gt_three
  have hu0 : 0 < Real.pi * T := by nlinarith
  rw [Real.lt_log_iff_exp_lt hu0]
  have := Real.exp_one_lt_d9
  nlinarith

/-- `log (2 c_N / α) > 0` for `0 < α ≤ 1`. -/
private theorem log_two_c_pos {n : ℕ} (hn : 1 ≤ n) {alpha : ℝ} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) : 0 < Real.log (2 * p11C n / alpha) := by
  have hc := p11C_ge_one hn
  apply Real.log_pos
  rw [lt_div_iff₀ ha]
  nlinarith

/-- `stepP:p11a:lc-mono` in the variable `u = π T`. -/
private theorem loss_anti_aux {n : ℕ} {A u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (hA : (n : ℝ) ≤ A + n * Real.log u) :
    (A + n * Real.log v) / v ≤ (A + n * Real.log u) / u := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  rw [div_le_div_iff₀ hv0 hu0]
  have hl : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hv0.ne' hu0.ne'] at hl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : u * Real.log v - u * Real.log u ≤ v - u := by
    have := mul_le_mul_of_nonneg_left hl hu0.le
    have e : u * (v / u - 1) = v - u := by field_simp
    nlinarith
  have h2 : (n : ℝ) * (u * Real.log v - u * Real.log u) ≤ n * (v - u) :=
    mul_le_mul_of_nonneg_left h1 hn0
  have h3 : (n : ℝ) * (v - u) ≤ (A + n * Real.log u) * (v - u) :=
    mul_le_mul_of_nonneg_right hA (by linarith)
  nlinarith

theorem loss_choice {n : ℕ} (hn : 1 ≤ n) {alpha T : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hT : 1 ≤ T) :
    0 < p11Loss n T alpha ∧
    (p11Loss n T alpha ≤ 1 → p11Error n T (p11Loss n T alpha) ≤ alpha) ∧
    AntitoneOn (fun t => p11Loss n t alpha) (Ici 1) ∧
    AntitoneOn (fun a => p11Loss n T a) (Ioc 0 1) := by
  have hc := p11C_ge_one hn
  have hpi := Real.pi_gt_three
  have hu : 3 < Real.pi * T := by nlinarith
  have hu0 : 0 < Real.pi * T := by linarith
  have hlogu := one_lt_log_piT hT
  have hA := log_two_c_pos hn ha ha1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnl : (1 : ℝ) ≤ n * Real.log (Real.pi * T) := by nlinarith
  have hpos : 0 < p11Loss n T alpha := by
    unfold p11Loss
    exact div_pos (by linarith) hu0
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro hd
    set d := p11Loss n T alpha with hd_def
    have hπTd : Real.pi * T * d =
        Real.log (2 * p11C n / alpha) + n * Real.log (Real.pi * T) := by
      rw [hd_def]; unfold p11Loss; field_simp
    have h2c : 0 < 2 * p11C n / alpha := by positivity
    have hexp : Real.exp (-Real.pi * T * d) =
        alpha / (2 * p11C n) * ((Real.pi * T) ^ n)⁻¹ := by
      have : -Real.pi * T * d = -(Real.log (2 * p11C n / alpha) + n * Real.log (Real.pi * T)) := by
        rw [← hπTd]; ring
      rw [this, Real.exp_neg, Real.exp_add, Real.exp_log h2c, Real.exp_nat_mul,
        Real.exp_log hu0]
      field_simp
    have hX : ((Real.pi * T) ^ n)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hY : ((d ^ n)⁻¹) * ((Real.pi * T) ^ n)⁻¹ ≤ 1 := by
      rw [← mul_inv, ← mul_pow, mul_comm d, hπTd]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hX0 : 0 ≤ ((Real.pi * T) ^ n)⁻¹ := by positivity
    unfold p11Error
    rw [hexp]
    have hc0 : 0 < p11C n := by linarith
    have : p11C n * (1 + (d ^ n)⁻¹) * (alpha / (2 * p11C n) * ((Real.pi * T) ^ n)⁻¹) =
        alpha / 2 * (((Real.pi * T) ^ n)⁻¹ + (d ^ n)⁻¹ * ((Real.pi * T) ^ n)⁻¹) := by
      field_simp
    rw [this]
    nlinarith
  · intro s hs t ht hst
    have hs1 : (1 : ℝ) ≤ s := hs
    show p11Loss n t alpha ≤ p11Loss n s alpha
    have hlogs := one_lt_log_piT hs1
    have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith
    have := loss_anti_aux (n := n) (A := Real.log (2 * p11C n / alpha))
      (u := Real.pi * s) (v := Real.pi * t) (by nlinarith)
      (mul_le_mul_of_nonneg_left hst Real.pi_pos.le)
      (by nlinarith)
    exact this
  · intro a ha' b hb hab
    show p11Loss n T b ≤ p11Loss n T a
    unfold p11Loss
    have h0 : 0 < a := ha'.1
    have hb0 : 0 < b := h0.trans_le hab
    have hlg : Real.log (2 * p11C n / b) ≤ Real.log (2 * p11C n / a) :=
      Real.log_le_log (by positivity) (by gcongr)
    exact div_le_div_of_nonneg_right (by linarith) hu0.le

theorem loss_sum {n : ℕ} (hn : 1 ≤ n) {theta T0 a b : ℝ}
    (ht : 1 < theta) (hT : 1 ≤ T0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (alpha : ℕ → ℝ) (hap : ∀ j, 0 < alpha j ∧ alpha j ≤ 1)
    (hlog : ∀ j, Real.log (2*p11C n/alpha j) ≤ a+b*j) :
    Summable (fun j => p11Loss n (T0*theta^j) (alpha j)) ∧
    (∀ j, p11Loss n (T0*theta^j) (alpha j) ≤
      (a+b*j+n*Real.log (Real.pi*T0)+n*j*Real.log theta)/(Real.pi*T0*theta^j)) ∧
    (∑' j, p11Loss n (T0*theta^j) (alpha j)) ≤
      ((a+n*Real.log (Real.pi*T0))*theta/(theta-1)+
        (b+n*Real.log theta)*theta/(theta-1)^2)/(Real.pi*T0) := by
  have hpi := Real.pi_gt_three
  have hT0 : 0 < T0 := by linarith
  have hπT0 : 0 < Real.pi * T0 := by positivity
  have hlt : 0 < Real.log theta := Real.log_pos ht
  have hth : 0 < theta := by linarith
  have hlogT : 0 < Real.log (Real.pi * T0) := by linarith [one_lt_log_piT hT]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set A := a + n * Real.log (Real.pi * T0) with hAdef
  set B := b + n * Real.log theta with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hge : ∀ j : ℕ, 1 ≤ T0 * theta ^ j := fun j => by
    have := one_le_pow₀ (n := j) ht.le
    nlinarith
  have hbd : ∀ j : ℕ, p11Loss n (T0 * theta ^ j) (alpha j) ≤
      (a + b * j + n * Real.log (Real.pi * T0) + n * j * Real.log theta) /
        (Real.pi * T0 * theta ^ j) := fun j => by
    unfold p11Loss
    have hl : Real.log (Real.pi * (T0 * theta ^ j)) =
        Real.log (Real.pi * T0) + j * Real.log theta := by
      rw [← mul_assoc, Real.log_mul hπT0.ne' (by positivity), Real.log_pow]
    rw [hl, ← mul_assoc Real.pi]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := hlog j
    nlinarith
  have hpos : ∀ j : ℕ, 0 < p11Loss n (T0 * theta ^ j) (alpha j) := fun j =>
    (loss_choice hn (hap j).1 (hap j).2 (hge j)).1
  have hrw : ∀ j : ℕ, (a + b * j + n * Real.log (Real.pi * T0) + n * j * Real.log theta) /
        (Real.pi * T0 * theta ^ j) =
      (A + B * j) * (theta⁻¹) ^ j / (Real.pi * T0) := fun j => by
    rw [hAdef, hBdef, inv_pow]
    field_simp
    ring
  have hr0 : 0 ≤ theta⁻¹ := by positivity
  have hr1 : theta⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hg : Summable (fun j : ℕ => (theta⁻¹) ^ j) := summable_geometric_of_lt_one hr0 hr1
  have hg2 : Summable (fun j : ℕ => (j : ℝ) * (theta⁻¹) ^ j) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := theta⁻¹)
      (by rwa [Real.norm_of_nonneg hr0])
    simpa using this
  have hsum : Summable (fun j : ℕ => (A + B * j) * (theta⁻¹) ^ j / (Real.pi * T0)) := by
    have := ((hg.mul_left A).add (hg2.mul_left B)).div_const (Real.pi * T0)
    refine this.congr fun j => ?_
    ring
  have hsumm : Summable (fun j => p11Loss n (T0 * theta ^ j) (alpha j)) :=
    Summable.of_nonneg_of_le (fun j => (hpos j).le)
      (fun j => (hbd j).trans_eq (hrw j)) hsum
  refine ⟨hsumm, hbd, ?_⟩
  have h1 := hsumm.tsum_le_tsum (fun j => (hbd j).trans_eq (hrw j)) hsum
  refine h1.trans (le_of_eq ?_)
  have e1 : ∑' j : ℕ, (theta⁻¹) ^ j = theta / (theta - 1) := by
    rw [tsum_geometric_of_lt_one hr0 hr1]
    field_simp
  have e2 : ∑' j : ℕ, (j : ℝ) * (theta⁻¹) ^ j = theta / (theta - 1) ^ 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hr0])]
    have : theta - 1 ≠ 0 := by linarith
    field_simp
  have : (fun j : ℕ => (A + B * j) * (theta⁻¹) ^ j / (Real.pi * T0)) =
      fun j : ℕ => (A * (theta⁻¹) ^ j + B * ((j : ℝ) * (theta⁻¹) ^ j)) / (Real.pi * T0) := by
    funext j; ring
  rw [this, tsum_div_const, (hg.mul_left A).tsum_add (hg2.mul_left B), tsum_mul_left,
    tsum_mul_left, e1, e2]
  have : theta - 1 ≠ 0 := by linarith
  field_simp

end KAM.Planetary
