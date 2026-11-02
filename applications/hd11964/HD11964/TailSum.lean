/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# The tail weight of a mode set (HD11964-ROT, piece 2e)

The sup bound on a Fourier tail `D_i (Q - Π_S Q)` from a strip of width `ρ` carries the weight
`tailWeight S i ρ = Σ_{k ∉ S} |k_i| e^{-2πρ|k|₁}` (`HD11964.TailBound`). Here:

* `summable_absMul_exp`: the weight's series converges;
* `tailWeight_box_le` (2e): for a box mode set (`S ⊇ {k ≠ 0 : |k_0| ≤ K₀, |k_1| ≤ K₁}`, e.g.
  `modesHD`), the weight is bounded by products of the one-dimensional sums
  `Σ_ℤ q^{|m|} = (1 + q)/(1 - q)`, `Σ_ℤ |m| q^{|m|} = 2q/(1 - q)²`,
  `Σ_{|m| > K} q^{|m|} = 2q^{K+1}/(1 - q)` and
  `Σ_{|m| > K} |m| q^{|m|} = 2q^{K+1}((K + 1) - Kq)/(1 - q)²`,
  at any `q < 1` with `e^{-2πρ} ≤ q` (a rational upper bound is data).
* `tailWeightA`, `summable_absMul_expA`, `tailWeightA_box_le`: the same on an anisotropic strip
  (widths `σ₀`, `σ₁` for the two angles; `q₀ ≥ e^{-2πσ₀}`, `q₁ ≥ e^{-2πσ₁}`).
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped Real

namespace HD11964.Cover

/-- The tail weight `Σ_{k ∉ S} |k_i| e^{-2πρ|k|₁}`. -/
def tailWeight (S : Finset (Fin 2 → ℤ)) (i : Fin 2) (ρ : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ,
    if k ∈ S then 0 else |(k i : ℝ)| * Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|))

/-- `Σ_{m ∈ ℤ} q^{|m|} = (1 + q)/(1 - q)`. -/
def geomS0 (q : ℝ) : ℝ := (1 + q) / (1 - q)

/-- `Σ_{m ∈ ℤ} |m| q^{|m|} = 2q/(1 - q)²`. -/
def geomS1 (q : ℝ) : ℝ := 2 * q / (1 - q) ^ 2

/-- `Σ_{|m| > K} q^{|m|} = 2q^{K+1}/(1 - q)`. -/
def geomT0 (K : ℕ) (q : ℝ) : ℝ := 2 * q ^ (K + 1) / (1 - q)

/-- `Σ_{|m| > K} |m| q^{|m|} = 2q^{K+1}((K + 1) - Kq)/(1 - q)²`. -/
def geomT1 (K : ℕ) (q : ℝ) : ℝ := 2 * q ^ (K + 1) * ((K + 1) - K * q) / (1 - q) ^ 2

/-! ### One-dimensional sums -/

/-- A sum over `ℕ` gives the symmetric sum over `ℤ`: `Σ_ℤ g(|m|) = 2 Σ_ℕ g - g(0)`. -/
theorem hasSum_int_natAbs {g : ℕ → ℝ} {a : ℝ} (hg : HasSum g a) :
    HasSum (fun m : ℤ => g m.natAbs) (2 * a - g 0) := by
  have h1 : HasSum (fun n : ℕ => g (n + 1)) (a - g 0) := by
    have h := (hasSum_nat_add_iff' (f := g) 1).mpr hg
    simpa using h
  have h2 : HasSum (fun n : ℕ => g (-((n : ℤ) + 1)).natAbs) (a - g 0) := by
    convert h1 using 2 with n
    congr 1
  have h := HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => g m.natAbs) (m := a)
    (by simpa using hg) h2
  convert h using 1
  ring

variable {q : ℝ}

theorem hasSum_nat_pow (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ :=
  hasSum_geometric_of_lt_one hq0 hq1

theorem hasSum_nat_mul_pow (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * q ^ n) (q / (1 - q) ^ 2) := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  exact h

/-- `Σ_{n > K} q^n = q^{K+1}/(1 - q)`, as an indicator sum over `ℕ`. -/
theorem hasSum_nat_tail_pow (K : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => if K < n then q ^ n else 0) (q ^ (K + 1) / (1 - q)) := by
  refine (hasSum_nat_add_iff' (K + 1)).mp ?_
  have hz : ∑ i ∈ Finset.range (K + 1), (if K < i then q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp [show ¬K < i by omega]
  rw [hz, sub_zero]
  have h := (hasSum_nat_pow hq0 hq1).mul_left (q ^ (K + 1))
  convert h using 1
  · funext n
    rw [ite_eq_left (show K < n + (K + 1) by omega), pow_add, mul_comm]
  · rw [div_eq_mul_inv]

/-- `Σ_{n > K} n q^n = q^{K+1}((K + 1) - Kq)/(1 - q)²`, as an indicator sum over `ℕ`. -/
theorem hasSum_nat_tail_mul_pow (K : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => if K < n then (n : ℝ) * q ^ n else 0)
      (q ^ (K + 1) * ((K + 1) - K * q) / (1 - q) ^ 2) := by
  refine (hasSum_nat_add_iff' (K + 1)).mp ?_
  have hz : ∑ i ∈ Finset.range (K + 1), (if K < i then (i : ℝ) * q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp [show ¬K < i by omega]
  rw [hz, sub_zero]
  have hne : (1 - q) ≠ 0 := by linarith
  have h := ((hasSum_nat_mul_pow hq0 hq1).add
    ((hasSum_nat_pow hq0 hq1).mul_left ((K : ℝ) + 1))).mul_left (q ^ (K + 1))
  convert h using 1
  · funext n
    rw [ite_eq_left (show K < n + (K + 1) by omega), pow_add]
    push_cast
    ring
  · field_simp
    ring

theorem hasSum_int_pow (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℤ => q ^ m.natAbs) (geomS0 q) := by
  have h := hasSum_int_natAbs (hasSum_nat_pow hq0 hq1)
  have hne : (1 - q) ≠ 0 := by linarith
  convert h using 1
  unfold geomS0
  field_simp
  ring

theorem hasSum_int_mul_pow (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℤ => (m.natAbs : ℝ) * q ^ m.natAbs) (geomS1 q) := by
  have h := hasSum_int_natAbs (hasSum_nat_mul_pow hq0 hq1)
  convert h using 1
  unfold geomS1
  simp
  ring

theorem hasSum_int_tail_pow (K : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℤ => if K < m.natAbs then q ^ m.natAbs else 0) (geomT0 K q) := by
  have h := hasSum_int_natAbs (hasSum_nat_tail_pow K hq0 hq1)
  convert h using 1
  unfold geomT0
  simp
  ring

theorem hasSum_int_tail_mul_pow (K : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℤ => if K < m.natAbs then (m.natAbs : ℝ) * q ^ m.natAbs else 0)
      (geomT1 K q) := by
  have h := hasSum_int_natAbs (hasSum_nat_tail_mul_pow K hq0 hq1)
  convert h using 1
  unfold geomT1
  simp
  ring

/-! ### Two-dimensional products -/

/-- A product of two nonnegative summable sequences over `ℤ`, summed over `ℤ²`. -/
theorem hasSum_fin2_mul {f g : ℤ → ℝ} {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    (hf0 : ∀ m, 0 ≤ f m) (hg0 : ∀ m, 0 ≤ g m) :
    HasSum (fun k : Fin 2 → ℤ => f (k 0) * g (k 1)) (a * b) := by
  have hfn : Summable fun m => ‖f m‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hf.summable
  have hgn : Summable fun m => ‖g m‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hg.summable
  have hp : HasSum (fun p : ℤ × ℤ => f p.1 * g p.2) (a * b) :=
    hf.mul hg (summable_mul_of_summable_norm hfn hgn)
  rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff]
  convert hp using 1
  funext p
  rfl

theorem natAbs_cast_eq_abs (m : ℤ) : (m.natAbs : ℝ) = |(m : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem exp_modeSize_eq_pow (ρ : ℝ) (k : Fin 2 → ℤ) :
    Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) =
      Real.exp (-(2 * π * ρ)) ^ ((k 0).natAbs + (k 1).natAbs) := by
  rw [← Real.exp_nat_mul]
  congr 1
  rw [Fin.sum_univ_two]
  push_cast
  rw [natAbs_cast_eq_abs, natAbs_cast_eq_abs]
  ring

/-- **The weight's series converges**: `Σ_k |k_i| e^{-2πρ|k|₁} < ∞` for `ρ > 0`. -/
theorem summable_absMul_exp (i : Fin 2) {ρ : ℝ} (hρ : 0 < ρ) :
    Summable fun k : Fin 2 → ℤ => |(k i : ℝ)| * Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) := by
  set q := Real.exp (-(2 * π * ρ)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by have := Real.pi_pos; nlinarith)
  have h0 := hasSum_int_pow hq0 hq1
  have h1 := hasSum_int_mul_pow hq0 hq1
  have hn0 : ∀ m : ℤ, 0 ≤ q ^ m.natAbs := fun m => pow_nonneg hq0 _
  have hn1 : ∀ m : ℤ, 0 ≤ (m.natAbs : ℝ) * q ^ m.natAbs := fun m => by positivity
  fin_cases i
  · refine (hasSum_fin2_mul h1 h0 hn1 hn0).summable.congr fun k => ?_
    simp only [exp_modeSize_eq_pow, ← hq, pow_add, natAbs_cast_eq_abs]
    simp
    ring
  · refine (hasSum_fin2_mul h0 h1 hn0 hn1).summable.congr fun k => ?_
    simp only [exp_modeSize_eq_pow, ← hq, pow_add, natAbs_cast_eq_abs]
    simp
    ring

/-- The terms of `tailWeight` are summable (for every `S`). -/
theorem summable_tailTerm (S : Finset (Fin 2 → ℤ)) (i : Fin 2) {ρ : ℝ} (hρ : 0 < ρ) :
    Summable fun k : Fin 2 → ℤ =>
      if k ∈ S then 0 else |(k i : ℝ)| * Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) :=
  (summable_absMul_exp i hρ).of_nonneg_of_le (fun k => by split_ifs <;> positivity)
    fun k => by split_ifs <;> [positivity; exact le_rfl]

/-- **(2e) The tail weight of a box mode set in closed form.** -/
theorem tailWeight_box_le (K₀ K₁ : ℕ) {S : Finset (Fin 2 → ℤ)} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ k : Fin 2 → ℤ, k ≠ 0 → |k 0| ≤ K₀ → |k 1| ≤ K₁ → k ∈ S)
    (hq : Real.exp (-(2 * π * ρ)) ≤ q) (hq1 : q < 1) :
    tailWeight S 0 ρ ≤ geomT1 K₀ q * geomS0 q + geomS1 q * geomT0 K₁ q ∧
      tailWeight S 1 ρ ≤ geomT0 K₀ q * geomS1 q + geomS0 q * geomT1 K₁ q := by
  have hq0 : 0 ≤ q := (Real.exp_pos _).le.trans hq
  -- the majorant
  set M : Fin 2 → (Fin 2 → ℤ) → ℝ := fun i k =>
    ((k i).natAbs : ℝ) * q ^ ((k 0).natAbs + (k 1).natAbs) *
      ((if K₀ < (k 0).natAbs then 1 else 0) + (if K₁ < (k 1).natAbs then 1 else 0)) with hM
  have hle : ∀ i k, (if k ∈ S then 0 else
      |(k i : ℝ)| * Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|))) ≤ M i k := by
    intro i k
    have hM0 : 0 ≤ M i k := by rw [hM]; positivity
    split_ifs with hk
    · exact hM0
    · by_cases h0 : k = 0
      · subst h0
        simp only [Pi.zero_apply, Int.cast_zero, abs_zero, zero_mul]
        exact hM0
      have hout : K₀ < (k 0).natAbs ∨ K₁ < (k 1).natAbs := by
        by_contra hc
        push Not at hc
        refine hk (hS k h0 ?_ ?_)
        · rw [← Int.natCast_natAbs]; exact_mod_cast hc.1
        · rw [← Int.natCast_natAbs]; exact_mod_cast hc.2
      have hind : 1 ≤ ((if K₀ < (k 0).natAbs then (1 : ℝ) else 0) +
          (if K₁ < (k 1).natAbs then 1 else 0)) := by
        have hA : (0 : ℝ) ≤ if K₀ < (k 0).natAbs then 1 else 0 := by split_ifs <;> norm_num
        have hB : (0 : ℝ) ≤ if K₁ < (k 1).natAbs then 1 else 0 := by split_ifs <;> norm_num
        rcases hout with h | h
        · have e : (if K₀ < (k 0).natAbs then (1 : ℝ) else 0) = 1 := by simp [h]
          linarith
        · have e : (if K₁ < (k 1).natAbs then (1 : ℝ) else 0) = 1 := by simp [h]
          linarith
      rw [exp_modeSize_eq_pow, ← natAbs_cast_eq_abs, hM]
      calc ((k i).natAbs : ℝ) * Real.exp (-(2 * π * ρ)) ^ ((k 0).natAbs + (k 1).natAbs)
          ≤ ((k i).natAbs : ℝ) * q ^ ((k 0).natAbs + (k 1).natAbs) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hq _) (by positivity)
        _ = ((k i).natAbs : ℝ) * q ^ ((k 0).natAbs + (k 1).natAbs) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hind (by positivity)
  have h0 := hasSum_int_pow hq0 hq1
  have h1 := hasSum_int_mul_pow hq0 hq1
  have t0 := fun K => hasSum_int_tail_pow K hq0 hq1
  have t1 := fun K => hasSum_int_tail_mul_pow K hq0 hq1
  have hn0 : ∀ m : ℤ, 0 ≤ q ^ m.natAbs := fun m => pow_nonneg hq0 _
  have hn1 : ∀ m : ℤ, 0 ≤ (m.natAbs : ℝ) * q ^ m.natAbs := fun m => by positivity
  have tn0 : ∀ (K : ℕ) (m : ℤ), 0 ≤ if K < m.natAbs then q ^ m.natAbs else 0 :=
    fun K m => by split_ifs <;> positivity
  have tn1 : ∀ (K : ℕ) (m : ℤ), 0 ≤ if K < m.natAbs then (m.natAbs : ℝ) * q ^ m.natAbs else 0 :=
    fun K m => by split_ifs <;> positivity
  have hM0 : HasSum (M 0) (geomT1 K₀ q * geomS0 q + geomS1 q * geomT0 K₁ q) := by
    convert (hasSum_fin2_mul (t1 K₀) h0 (tn1 K₀) hn0).add
      (hasSum_fin2_mul h1 (t0 K₁) hn1 (tn0 K₁)) using 1
    funext k
    simp only [hM, pow_add]
    split_ifs <;> ring
  have hM1 : HasSum (M 1) (geomT0 K₀ q * geomS1 q + geomS0 q * geomT1 K₁ q) := by
    convert (hasSum_fin2_mul (t0 K₀) h1 (tn0 K₀) hn1).add
      (hasSum_fin2_mul h0 (t1 K₁) hn0 (tn1 K₁)) using 1
    funext k
    simp only [hM, pow_add]
    split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [← hM0.tsum_eq]
    exact (summable_tailTerm S 0 hρ).tsum_le_tsum (hle 0) hM0.summable
  · rw [← hM1.tsum_eq]
    exact (summable_tailTerm S 1 hρ).tsum_le_tsum (hle 1) hM1.summable

/-- The closed-form bound of `tailWeight_box_le`, per angle. -/
def boxTailBound (K₀ K₁ : ℕ) (i : Fin 2) (q : ℝ) : ℝ :=
  if i = 0 then geomT1 K₀ q * geomS0 q + geomS1 q * geomT0 K₁ q
  else geomT0 K₀ q * geomS1 q + geomS0 q * geomT1 K₁ q

/-- `tailWeight_box_le` for either angle. -/
theorem tailWeight_le_boxTailBound (K₀ K₁ : ℕ) {S : Finset (Fin 2 → ℤ)} (i : Fin 2) {ρ : ℝ}
    (hρ : 0 < ρ) (hS : ∀ k : Fin 2 → ℤ, k ≠ 0 → |k 0| ≤ K₀ → |k 1| ≤ K₁ → k ∈ S)
    (hq : Real.exp (-(2 * π * ρ)) ≤ q) (hq1 : q < 1) :
    tailWeight S i ρ ≤ boxTailBound K₀ K₁ i q := by
  have h := tailWeight_box_le K₀ K₁ hρ hS hq hq1
  fin_cases i
  · simpa [boxTailBound] using h.1
  · simpa [boxTailBound] using h.2

/-! ### The anisotropic weight -/

/-- The anisotropic tail weight `Σ_{k ∉ S} |k_i| e^{-2π(σ₀|k_0| + σ₁|k_1|)}`. -/
def tailWeightA (S : Finset (Fin 2 → ℤ)) (i : Fin 2) (σ₀ σ₁ : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ,
    if k ∈ S then 0 else |(k i : ℝ)| * Real.exp (-(2 * π * (σ₀ * |(k 0 : ℝ)| + σ₁ * |(k 1 : ℝ)|)))

theorem exp_aniso_eq_pow (σ₀ σ₁ : ℝ) (k : Fin 2 → ℤ) :
    Real.exp (-(2 * π * (σ₀ * |(k 0 : ℝ)| + σ₁ * |(k 1 : ℝ)|))) =
      Real.exp (-(2 * π * σ₀)) ^ (k 0).natAbs * Real.exp (-(2 * π * σ₁)) ^ (k 1).natAbs := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, natAbs_cast_eq_abs,
    natAbs_cast_eq_abs]
  ring_nf

theorem exp_neg_lt_one {σ : ℝ} (hσ : 0 < σ) : Real.exp (-(2 * π * σ)) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by have := Real.pi_pos; nlinarith)

/-- **The anisotropic weight's series converges** for `σ₀, σ₁ > 0`. -/
theorem summable_absMul_expA (i : Fin 2) {σ₀ σ₁ : ℝ} (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) :
    Summable fun k : Fin 2 → ℤ =>
      |(k i : ℝ)| * Real.exp (-(2 * π * (σ₀ * |(k 0 : ℝ)| + σ₁ * |(k 1 : ℝ)|))) := by
  set q₀ := Real.exp (-(2 * π * σ₀))
  set q₁ := Real.exp (-(2 * π * σ₁))
  have hq₀ : 0 ≤ q₀ := (Real.exp_pos _).le
  have hq₁ : 0 ≤ q₁ := (Real.exp_pos _).le
  have hn0 : ∀ (q : ℝ), 0 ≤ q → ∀ m : ℤ, 0 ≤ q ^ m.natAbs := fun q hq m => pow_nonneg hq _
  have hn1 : ∀ (q : ℝ), 0 ≤ q → ∀ m : ℤ, 0 ≤ (m.natAbs : ℝ) * q ^ m.natAbs :=
    fun q hq m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)
  fin_cases i
  · refine (hasSum_fin2_mul (hasSum_int_mul_pow hq₀ (exp_neg_lt_one h₀))
      (hasSum_int_pow hq₁ (exp_neg_lt_one h₁)) (hn1 q₀ hq₀) (hn0 q₁ hq₁)).summable.congr fun k => ?_
    simp only [exp_aniso_eq_pow, natAbs_cast_eq_abs]
    simp
    ring
  · refine (hasSum_fin2_mul (hasSum_int_pow hq₀ (exp_neg_lt_one h₀))
      (hasSum_int_mul_pow hq₁ (exp_neg_lt_one h₁)) (hn0 q₀ hq₀) (hn1 q₁ hq₁)).summable.congr
        fun k => ?_
    simp only [exp_aniso_eq_pow, natAbs_cast_eq_abs]
    simp
    ring

theorem summable_tailTermA (S : Finset (Fin 2 → ℤ)) (i : Fin 2) {σ₀ σ₁ : ℝ} (h₀ : 0 < σ₀)
    (h₁ : 0 < σ₁) :
    Summable fun k : Fin 2 → ℤ => if k ∈ S then 0 else
      |(k i : ℝ)| * Real.exp (-(2 * π * (σ₀ * |(k 0 : ℝ)| + σ₁ * |(k 1 : ℝ)|))) :=
  (summable_absMul_expA i h₀ h₁).of_nonneg_of_le (fun k => by split_ifs <;> positivity)
    fun k => by split_ifs <;> [positivity; exact le_rfl]

/-- The closed-form bound of `tailWeightA_box_le`, per angle. -/
def boxTailBoundA (K₀ K₁ : ℕ) (i : Fin 2) (q₀ q₁ : ℝ) : ℝ :=
  if i = 0 then geomT1 K₀ q₀ * geomS0 q₁ + geomS1 q₀ * geomT0 K₁ q₁
  else geomT0 K₀ q₀ * geomS1 q₁ + geomS0 q₀ * geomT1 K₁ q₁

/-- **The anisotropic tail weight of a box mode set in closed form**, at any `q₀, q₁ < 1` with
`e^{-2πσ₀} ≤ q₀`, `e^{-2πσ₁} ≤ q₁`. -/
theorem tailWeightA_le_boxTailBoundA (K₀ K₁ : ℕ) {S : Finset (Fin 2 → ℤ)} (i : Fin 2)
    {σ₀ σ₁ q₀ q₁ : ℝ} (h₀ : 0 < σ₀) (h₁ : 0 < σ₁)
    (hS : ∀ k : Fin 2 → ℤ, k ≠ 0 → |k 0| ≤ K₀ → |k 1| ≤ K₁ → k ∈ S)
    (hq₀ : Real.exp (-(2 * π * σ₀)) ≤ q₀) (hq₀1 : q₀ < 1)
    (hq₁ : Real.exp (-(2 * π * σ₁)) ≤ q₁) (hq₁1 : q₁ < 1) :
    tailWeightA S i σ₀ σ₁ ≤ boxTailBoundA K₀ K₁ i q₀ q₁ := by
  have hq0 : 0 ≤ q₀ := (Real.exp_pos _).le.trans hq₀
  have hq1 : 0 ≤ q₁ := (Real.exp_pos _).le.trans hq₁
  set M : (Fin 2 → ℤ) → ℝ := fun k =>
    ((k i).natAbs : ℝ) * (q₀ ^ (k 0).natAbs * q₁ ^ (k 1).natAbs) *
      ((if K₀ < (k 0).natAbs then 1 else 0) + (if K₁ < (k 1).natAbs then 1 else 0)) with hM
  have hle : ∀ k, (if k ∈ S then 0 else |(k i : ℝ)| *
      Real.exp (-(2 * π * (σ₀ * |(k 0 : ℝ)| + σ₁ * |(k 1 : ℝ)|)))) ≤ M k := by
    intro k
    have hM0 : 0 ≤ M k := by rw [hM]; positivity
    split_ifs with hk
    · exact hM0
    · by_cases h0 : k = 0
      · subst h0
        simp only [Pi.zero_apply, Int.cast_zero, abs_zero, zero_mul]
        exact hM0
      have hout : K₀ < (k 0).natAbs ∨ K₁ < (k 1).natAbs := by
        by_contra hc
        push Not at hc
        refine hk (hS k h0 ?_ ?_)
        · rw [← Int.natCast_natAbs]; exact_mod_cast hc.1
        · rw [← Int.natCast_natAbs]; exact_mod_cast hc.2
      have hind : 1 ≤ ((if K₀ < (k 0).natAbs then (1 : ℝ) else 0) +
          (if K₁ < (k 1).natAbs then 1 else 0)) := by
        have hA : (0 : ℝ) ≤ if K₀ < (k 0).natAbs then 1 else 0 := by split_ifs <;> norm_num
        have hB : (0 : ℝ) ≤ if K₁ < (k 1).natAbs then 1 else 0 := by split_ifs <;> norm_num
        rcases hout with h | h
        · have e : (if K₀ < (k 0).natAbs then (1 : ℝ) else 0) = 1 := by simp [h]
          linarith
        · have e : (if K₁ < (k 1).natAbs then (1 : ℝ) else 0) = 1 := by simp [h]
          linarith
      rw [exp_aniso_eq_pow, ← natAbs_cast_eq_abs, hM]
      have hpow : Real.exp (-(2 * π * σ₀)) ^ (k 0).natAbs * Real.exp (-(2 * π * σ₁)) ^ (k 1).natAbs
          ≤ q₀ ^ (k 0).natAbs * q₁ ^ (k 1).natAbs :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le hq₀ _)
          (pow_le_pow_left₀ (Real.exp_pos _).le hq₁ _) (by positivity) (pow_nonneg hq0 _)
      calc ((k i).natAbs : ℝ) * (Real.exp (-(2 * π * σ₀)) ^ (k 0).natAbs *
            Real.exp (-(2 * π * σ₁)) ^ (k 1).natAbs)
          ≤ ((k i).natAbs : ℝ) * (q₀ ^ (k 0).natAbs * q₁ ^ (k 1).natAbs) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((k i).natAbs : ℝ) * (q₀ ^ (k 0).natAbs * q₁ ^ (k 1).natAbs) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hind (by positivity)
  have hn0 : ∀ (q : ℝ), 0 ≤ q → ∀ m : ℤ, 0 ≤ q ^ m.natAbs := fun q hq m => pow_nonneg hq _
  have hn1 : ∀ (q : ℝ), 0 ≤ q → ∀ m : ℤ, 0 ≤ (m.natAbs : ℝ) * q ^ m.natAbs :=
    fun q hq m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)
  have tn0 : ∀ (q : ℝ), 0 ≤ q → ∀ (K : ℕ) (m : ℤ), 0 ≤ if K < m.natAbs then q ^ m.natAbs else 0 :=
    fun q hq K m => by split_ifs <;> [exact pow_nonneg hq _; exact le_rfl]
  have tn1 : ∀ (q : ℝ), 0 ≤ q → ∀ (K : ℕ) (m : ℤ),
      0 ≤ if K < m.natAbs then (m.natAbs : ℝ) * q ^ m.natAbs else 0 :=
    fun q hq K m => by split_ifs <;> [exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _);
      exact le_rfl]
  have hMs : HasSum M (boxTailBoundA K₀ K₁ i q₀ q₁) := by
    fin_cases i
    · convert (hasSum_fin2_mul (hasSum_int_tail_mul_pow K₀ hq0 hq₀1) (hasSum_int_pow hq1 hq₁1)
        (tn1 q₀ hq0 K₀) (hn0 q₁ hq1)).add (hasSum_fin2_mul (hasSum_int_mul_pow hq0 hq₀1)
        (hasSum_int_tail_pow K₁ hq1 hq₁1) (hn1 q₀ hq0) (tn0 q₁ hq1 K₁)) using 1
      · funext k
        simp only [hM]
        split_ifs <;> simp <;> ring
      · simp [boxTailBoundA]
    · convert (hasSum_fin2_mul (hasSum_int_tail_pow K₀ hq0 hq₀1) (hasSum_int_mul_pow hq1 hq₁1)
        (tn0 q₀ hq0 K₀) (hn1 q₁ hq1)).add (hasSum_fin2_mul (hasSum_int_pow hq0 hq₀1)
        (hasSum_int_tail_mul_pow K₁ hq1 hq₁1) (hn0 q₀ hq0) (tn1 q₁ hq1 K₁)) using 1
      · funext k
        simp only [hM]
        split_ifs <;> simp <;> ring
      · simp [boxTailBoundA]
  rw [← hMs.tsum_eq]
  exact (summable_tailTermA S i h₀ h₁).tsum_le_tsum hle hMs.summable

end HD11964.Cover

end
