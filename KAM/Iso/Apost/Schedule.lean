/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Constants
import KAM.Analysis.Iteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The schedule of the iteration and the decay of the errors (blueprint `bpI:p2:schedule`,
`bpI:p2:error-decay`)

The schedule of Definition `bpI:p2:schedule` consists of the sequences `δ_s = 2^{-s} δ₀` and
`r_s = ρ - 8 δ₀ (1 - 2^{-s})`, which are `KAM.Apost.deltaSeq` and `KAM.Apost.rSeq`
(reused unchanged; the claims of the schedule `r₀ = ρ`, `r_{s+1} = r_s - 4 δ_s`,
`ρ_∞ ≤ ρ - 8 δ₀ < r_s`, `δ_s ≤ 1`, `4 δ_s < r_s` are `KAM.Apost.schedule`), and of the two
sequences `isoEpsSeq` (`ε_s`, `ε₀ = e`, `ε_{s+1} = Ĉ_E ε_s² / (γ⁴ δ_s^{2a})`) and `isoDSeq`
(`d_s = Ĉ_Δ ε_s / (γ² δ_s^a)`) of `KAM/Iso/Apost/Defs.lean`.

`iso_error_decay` (Lemma `bpI:p2:error-decay`) is `KAM.Apost.error_decay` with `Ĉ_E` in place of
`C_E` (only `1 ≤ Ĉ_E` is used): it bounds the errors by
`ε_s ≤ q^{2^s - 1} 2^{-2as} e ≤ 2^{-2as} e`, for `q = 2^{2a} Ĉ_E e / (γ⁴ δ₀^{2a})`, then
`ε_s / δ_s^j ≤ e / δ₀^j` for `0 ≤ j ≤ 2a`, and finally `∑ ε_s / δ_s^j ≤ 2 e / δ₀^j` for
`0 ≤ j ≤ 2a - 1`. The first bound is `KAM.quadratic_iteration_linear` for `y_s = ε_s`,
`Q = Ĉ_E / (γ⁴ δ₀^{2a})` and `p = 2a`; the sums are a comparison with a geometric series.

The helper lemmas (`isoEpsSeq_*`, `isoEps_*`) are what the induction `bpI:p2:iteration` uses.
-/

public section

namespace KAM.Iso.Apost

open KAM KAM.Apost

section Errors

variable {n : ℕ} {τ M σK σB σT : ℝ} {ρ ρinf γ e : ℝ}

theorem isoEpsSeq_zero : isoEpsSeq n τ M σK σB σT ρ ρinf γ e 0 = e := rfl

theorem isoEpsSeq_succ (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e (s + 1) =
      hatCE n τ M σK σB σT * isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ^ 2 /
        (γ ^ 4 * deltaSeq ρ ρinf s ^ (2 * aExp n τ)) := rfl

theorem isoEpsSeq_nonneg (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (he : 0 ≤ e) (s : ℕ) :
    0 ≤ isoEpsSeq n τ M σK σB σT ρ ρinf γ e s := by
  induction s with
  | zero => exact he
  | succ s ih =>
    have hC := zero_le_one.trans (one_le_hatCE hP)
    have hδ := (deltaSeq_pos hρ s).le
    rw [isoEpsSeq_succ]
    positivity

/-- The recursion `ε_{s+1} = Q' 2^{2as} ε_s²` with `Q' = Ĉ_E / (γ⁴ δ₀^{2a})`. -/
theorem isoEpsSeq_succ_eq (hρ : ρinf < ρ) (hγ : 0 < γ) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e (s + 1) =
      hatCE n τ M σK σB σT / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) *
        (2 : ℝ) ^ (2 * aExp n τ * (s : ℝ)) * isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ^ 2 := by
  have hd0 := delta0_pos hρ
  have hD : 0 < delta0 ρ ρinf ^ (2 * aExp n τ) := Real.rpow_pos_of_pos hd0 _
  have h2 : 0 < (2 : ℝ) ^ (2 * aExp n τ * (s : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [isoEpsSeq_succ, deltaSeq_rpow hd0.le, Real.rpow_neg (by norm_num)]
  field_simp

/-- `ε_s ≤ q^{2^s - 1} 2^{-2as} e`, by `KAM.quadratic_iteration_linear`. -/
theorem isoEpsSeq_le_q_pow (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤
      ((2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
        (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ))) ^ (2 ^ s - 1) *
        (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e := by
  have hD : 0 < γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos (delta0_pos hρ) _)
  have hQ : 0 < hatCE n τ M σK σB σT / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) :=
    div_pos (zero_lt_one.trans_le (one_le_hatCE hP)) hD
  have key : isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤
      (hatCE n τ M σK σB σT / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) *
        (2 : ℝ) ^ (2 * aExp n τ) * isoEpsSeq n τ M σK σB σT ρ ρinf γ e 0) ^ (2 ^ s - 1) *
        (2 : ℝ) ^ (-(2 * aExp n τ * (s : ℝ))) * isoEpsSeq n τ M σK σB σT ρ ρinf γ e 0 :=
    quadratic_iteration_linear (y := isoEpsSeq n τ M σK σB σT ρ ρinf γ e) hQ
      (isoEpsSeq_nonneg hP hρ he) (fun m => (isoEpsSeq_succ_eq hρ hγ m).le) s
  rwa [isoEpsSeq_zero, q_eq] at key

/-- `0 ≤ q`. -/
theorem iso_q_nonneg (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e) :
    0 ≤ (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) := by
  have hD : 0 < γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos (delta0_pos hρ) _)
  have hC := zero_le_one.trans (one_le_hatCE hP)
  positivity

/-- The first inequality chain of Lemma `bpI:p2:error-decay`. -/
theorem iso_error_decay_eps (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤
        ((2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
          (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ))) ^ (2 ^ s - 1) *
          (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e ∧
      ((2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
          (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ))) ^ (2 ^ s - 1) *
          (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e ≤ (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e := by
  refine ⟨isoEpsSeq_le_q_pow hP hρ hγ he s, ?_⟩
  have h1 := pow_le_one₀ (iso_q_nonneg hP hρ hγ he) hq (n := 2 ^ s - 1)
  have h2 : 0 ≤ (2 : ℝ) ^ (-(2 * aExp n τ * (s : ℝ))) * e := by positivity
  calc _ ≤ 1 * ((2 : ℝ) ^ (-(2 * aExp n τ * (s : ℝ))) * e) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) he
    _ = _ := one_mul _

/-- The weighted bounds `ε_s / δ_s^j ≤ 2^{-(2a - j)s} e / δ₀^j ≤ e / δ₀^j` for `j ≤ 2a`. -/
theorem iso_error_decay_weighted (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) {j : ℝ}
    (hj2 : j ≤ 2 * aExp n τ) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤
          (2 : ℝ) ^ (-((2 * aExp n τ - j) * s)) * e / delta0 ρ ρinf ^ j ∧
        (2 : ℝ) ^ (-((2 * aExp n τ - j) * s)) * e / delta0 ρ ρinf ^ j ≤ e / delta0 ρ ρinf ^ j := by
  have hd0 := delta0_pos hρ
  have hDj : 0 < delta0 ρ ρinf ^ j := Real.rpow_pos_of_pos hd0 _
  have h2j : 0 < (2 : ℝ) ^ (-(j * (s : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (-((2 * aExp n τ - j) * (s : ℝ))) =
      (2 : ℝ) ^ (-(2 * aExp n τ * (s : ℝ))) / (2 : ℝ) ^ (-(j * (s : ℝ))) := by
    rw [← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hε := (iso_error_decay_eps hP hρ hγ he hq s).1.trans
      (iso_error_decay_eps hP hρ hγ he hq s).2
    rw [deltaSeq_rpow hd0.le, hsplit]
    calc _ ≤ (2 : ℝ) ^ (-(2 * aExp n τ * (s : ℝ))) * e /
          ((2 : ℝ) ^ (-(j * (s : ℝ))) * delta0 ρ ρinf ^ j) :=
          div_le_div_of_nonneg_right hε (by positivity)
      _ = _ := by field_simp
  · have h1 : (2 : ℝ) ^ (-((2 * aExp n τ - j) * (s : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (mul_nonneg (by linarith) (Nat.cast_nonneg s)))
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left he h1) hDj.le

/-- The summed bounds `∑ ε_s / δ_s^j ≤ 2 e / δ₀^j` for `j ≤ 2a - 1`: comparison with the
geometric series of ratio `2^{-(2a - j)} ≤ 1/2`. -/
theorem iso_error_decay_sum (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) {j : ℝ}
    (hj2 : j ≤ 2 * aExp n τ - 1) :
    Summable (fun s => isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j) ∧
      ∑' s, isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤
        2 * e / delta0 ρ ρinf ^ j := by
  have hd0 := delta0_pos hρ
  have hDj : 0 < delta0 ρ ρinf ^ j := Real.rpow_pos_of_pos hd0 _
  set r : ℝ := (2 : ℝ) ^ (-(2 * aExp n τ - j)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r ≤ 1 / 2 := by
    have : r ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have hgeo : ∀ s : ℕ, (2 : ℝ) ^ (-((2 * aExp n τ - j) * (s : ℝ))) = r ^ s := by
    intro s
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hle : ∀ s : ℕ, isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤
      e / delta0 ρ ρinf ^ j * r ^ s := by
    intro s
    have := (iso_error_decay_weighted hP hρ hγ he hq (j := j) (by linarith) s).1
    rw [hgeo] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hnn : ∀ s : ℕ,
      0 ≤ isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j := by
    intro s
    have := isoEpsSeq_nonneg hP hρ he (γ := γ) s
    have := (Real.rpow_pos_of_pos (deltaSeq_pos hρ s) j)
    positivity
  have hsum : Summable (fun s : ℕ => e / delta0 ρ ρinf ^ j * r ^ s) :=
    (summable_geometric_of_lt_one hr0.le (by linarith)).mul_left _
  refine ⟨Summable.of_nonneg_of_le hnn hle hsum, ?_⟩
  calc _ ≤ ∑' s : ℕ, e / delta0 ρ ρinf ^ j * r ^ s :=
        (Summable.of_nonneg_of_le hnn hle hsum).tsum_le_tsum hle hsum
    _ = e / delta0 ρ ρinf ^ j * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le (by linarith)]
    _ ≤ e / delta0 ρ ρinf ^ j * 2 := by
        have h2 : (1 - r)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * e / delta0 ρ ρinf ^ j := by ring

/-! ### Corollaries used by the induction -/

/-- The terms `ε_i / δ_i^j` of the sums of Lemma `bpI:p2:error-decay` are nonnegative. -/
theorem isoEps_div_nonneg (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (he : 0 ≤ e) (j : ℝ)
    (i : ℕ) : 0 ≤ isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ j := by
  have h1 := isoEpsSeq_nonneg hP hρ he (γ := γ) i
  have h2 := Real.rpow_pos_of_pos (deltaSeq_pos hρ i) j
  positivity

/-- Partial sums of `X ε_i/δ_i^j` are bounded by `X · 2e/δ₀^j`, for `0 ≤ X` and `j ≤ 2a - 1`. -/
theorem isoEps_partial_sum_le (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) {j X : ℝ} (hj : j ≤ 2 * aExp n τ - 1)
    (hX : 0 ≤ X) (s : ℕ) :
    ∑ i ∈ Finset.range s,
        X * (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ j) ≤
      X * (2 * e / delta0 ρ ρinf ^ j) := by
  obtain ⟨hsum, htsum⟩ := iso_error_decay_sum hP hρ hγ he hq hj
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((hsum.sum_le_tsum _ fun i _ => isoEps_div_nonneg hP hρ he j i).trans htsum) hX

/-- The weighted form for every `j ≤ 2a`: `ε_s/δ_s^j ≤ e/δ₀^j`. -/
theorem isoEps_div_le (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) {j : ℝ} (hj : j ≤ 2 * aExp n τ) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤ e / delta0 ρ ρinf ^ j :=
  (iso_error_decay_weighted hP hρ hγ he hq hj s).1.trans
    (iso_error_decay_weighted hP hρ hγ he hq hj s).2

/-- `ε_s ≤ e` (`j = 0`). -/
theorem isoEps_le (hP : Params n τ M σK σB σT) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) (s : ℕ) :
    isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤ e := by
  have h0 : (0 : ℝ) ≤ 2 * aExp n τ := by
    have := eight_le_aExp hP
    linarith
  simpa using isoEps_div_le hP hρ hγ he hq h0 s

/-- `d_i = (Ĉ_Δ/γ²) · ε_i/δ_i^a`. -/
theorem isoDSeq_eq (i : ℕ) : isoDSeq n τ M σK σB σT ρ ρinf γ e i =
    hatCDelta n τ M σK σB σT / γ ^ 2 *
      (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ aExp n τ) := by
  unfold isoDSeq dStep
  rw [mul_div_mul_comm]

end Errors

variable {n : ℕ}

/-- `bpI:p2:error-decay` (as `KAM.Apost.error_decay`, with `Ĉ_E`). -/
theorem iso_error_decay {τ M σK σB σT : ℝ} (hP : Params n τ M σK σB σT) {ρ ρinf γ e : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
      (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    (∀ s : ℕ, isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤
        ((2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e /
          (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ))) ^ (2 ^ s - 1) *
          (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e ∧
      isoEpsSeq n τ M σK σB σT ρ ρinf γ e s ≤ (2 : ℝ) ^ (-(2 * aExp n τ * s)) * e) ∧
    (∀ j : ℝ, 0 ≤ j → j ≤ 2 * aExp n τ → ∀ s : ℕ,
      isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤ e / delta0 ρ ρinf ^ j) ∧
    (∀ j : ℝ, 0 ≤ j → j ≤ 2 * aExp n τ - 1 →
      Summable (fun s => isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j) ∧
      ∑' s, isoEpsSeq n τ M σK σB σT ρ ρinf γ e s / deltaSeq ρ ρinf s ^ j ≤
        2 * e / delta0 ρ ρinf ^ j) := by
  have _hρinf := hρinf
  exact ⟨fun s => ⟨(iso_error_decay_eps hP hρ hγ he hq s).1,
      (iso_error_decay_eps hP hρ hγ he hq s).1.trans (iso_error_decay_eps hP hρ hγ he hq s).2⟩,
    fun _ _ hj2 s => isoEps_div_le hP hρ hγ he hq hj2 s,
    fun _ _ hj2 => iso_error_decay_sum hP hρ hγ he hq hj2⟩

end KAM.Iso.Apost
