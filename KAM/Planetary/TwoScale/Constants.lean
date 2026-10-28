/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Two-scale KAM constants

`bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:rem-norm`, `bpP:p3:sums`: the formula data `ScaleData`,
the cutoff / radius / error constants, the scale update `nextScale` and its iterate `seq`, the
normalization comparison `rem_norm` (lowering `Mhat` with `L` fixed keeps `cutoff` and `initialL`,
increases `rhoHat` and decreases `eHat`), the scalar recurrence package `sums`, and the row
restriction bound `rem_norm_blocks`.

Positivity of the data stays in the hypothesis bundle `KamHyp` of the step module; the formulas here
are total.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Planetary

/-! ## Two-scale constants: formula data only. Positivity stays in KamHyp. -/
structure ScaleData where
  τ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  s : ℝ
  ρ : ℝ
  E : ℝ
  M : ℝ
  Mhat : ℝ
  Mbar : ℝ
  Mbar₁ : ℝ
  Mbar₂ : ℝ
  L : ℝ

def constants (p : ScaleData) : ℝ × ℝ × ℝ :=
  let x := p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2
  let K := 6 / p.s * max 1 (log (1 / x))
  let R := min (min (p.γ₁ / (3 * p.M * K ^ (p.τ + 1)))
    (p.γ₂ / (3 * p.Mhat * K ^ (p.τ + 1)))) p.ρ
  (K, R, p.E * p.L / R ^ 2)
def cutoff (p : ScaleData) : ℝ := (constants p).1
def rhoHat (p : ScaleData) : ℝ := (constants p).2.1
def eHat (p : ScaleData) : ℝ := (constants p).2.2
def kamConstant (n : ℕ) (τ : ℝ) : ℝ := max (2 ^ 13 * (n : ℝ)) ((24 : ℝ) ^ (τ + 1) / 3)
def complementConstant (n : ℕ) : ℝ := 1 + (1 + 2 ^ n) * (1 + (4 / 3 : ℝ) ^ n)
def initialL (M Mhat Mbar : ℝ) : ℝ := max Mbar (max M⁻¹ Mhat⁻¹)
def nextScale (p : ScaleData) : ScaleData :=
  { p with
    s := p.s / 12
    ρ := rhoHat p / 16
    E := p.E ^ 2 * p.L * p.M ^ 2 / p.γ₁ ^ 2
    M := 2 * p.M
    Mhat := 2 * p.Mhat
    Mbar := 2 * p.Mbar
    Mbar₁ := 2 * p.Mbar₁
    Mbar₂ := 2 * p.Mbar₂
    L := 2 * p.L }
def seq (p : ScaleData) : ℕ → ScaleData
  | 0 => p
  | j + 1 => nextScale (seq p j)

theorem cutoff_pos {p : ScaleData} (hs : 0 < p.s) : 0 < cutoff p := by
  unfold cutoff constants
  have : (1 : ℝ) ≤ max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) := le_max_left _ _
  have h6 : 0 < 6 / p.s := by positivity
  exact mul_pos h6 (lt_of_lt_of_le one_pos this)

theorem rhoHat_pos {p : ScaleData} (hs : 0 < p.s) (hγ₁ : 0 < p.γ₁) (hγ₂ : 0 < p.γ₂)
    (hM : 0 < p.M) (hMh : 0 < p.Mhat) (hρ : 0 < p.ρ) : 0 < rhoHat p := by
  have hK := cutoff_pos hs
  have hKp : 0 < cutoff p ^ (p.τ + 1) := Real.rpow_pos_of_pos hK _
  unfold rhoHat constants
  refine lt_min (lt_min ?_ ?_) hρ
  · exact div_pos hγ₁ (by positivity)
  · exact div_pos hγ₂ (by positivity)

/-- Lowering `Mhat` with `L` fixed: correct normalization direction. -/
theorem rem_norm (p : ScaleData) (hp : 0 < p.E ∧ 0 < p.M ∧ 0 < p.Mhat ∧ 0 < p.Mbar ∧
    0 < p.s ∧ 0 < p.γ₁ ∧ 0 < p.γ₂ ∧ 0 < p.ρ ∧ 0 < p.L ∧ 0 < p.τ) :
    let p' := {p with Mhat := min p.Mhat p.M}
    initialL p'.M p'.Mhat p'.Mbar = initialL p.M p.Mhat p.Mbar ∧
    cutoff p' = cutoff p ∧ rhoHat p ≤ rhoHat p' ∧ eHat p' ≤ eHat p := by
  obtain ⟨hE, hM, hMh, -, hs, hγ₁, hγ₂, hρ, hL, -⟩ := hp
  intro p'
  have hm : 0 < min p.Mhat p.M := lt_min hMh hM
  have hmle : min p.Mhat p.M ≤ p.Mhat := min_le_left _ _
  have hK : 0 < cutoff p := cutoff_pos hs
  have hKp : 0 < cutoff p ^ (p.τ + 1) := Real.rpow_pos_of_pos hK _
  have hrho : rhoHat p ≤ rhoHat p' := by
    unfold rhoHat constants
    refine min_le_min_right _ (min_le_min_left _ ?_)
    have h3 : 3 * min p.Mhat p.M * cutoff p ^ (p.τ + 1) ≤ 3 * p.Mhat * cutoff p ^ (p.τ + 1) := by
      gcongr
    exact div_le_div_of_nonneg_left hγ₂.le (by positivity) h3
  refine ⟨?_, rfl, hrho, ?_⟩
  · show max p.Mbar (max p.M⁻¹ (min p.Mhat p.M)⁻¹) = max p.Mbar (max p.M⁻¹ p.Mhat⁻¹)
    rcases le_total p.Mhat p.M with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      have h2 : p.Mhat⁻¹ ≤ p.M⁻¹ := inv_anti₀ hM h
      rw [max_eq_left h2, max_self]
  · have hR := rhoHat_pos hs hγ₁ hγ₂ hM hMh hρ
    show p.E * p.L / rhoHat p' ^ 2 ≤ p.E * p.L / rhoHat p ^ 2
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hR.le hrho 2)

/-- Row restrictions cannot exceed the full operator bound. -/
theorem rem_norm_blocks {a b : ℕ} (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) :
    (∀ v, ‖fun i : Fin a => A v (Fin.castAdd b i)‖ ≤ ‖A‖ * ‖v‖) ∧
    (∀ v, ‖fun i : Fin b => A v (Fin.natAdd a i)‖ ≤ ‖A‖ * ‖v‖) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · refine le_trans ?_ (A.le_opNorm v)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact norm_le_pi_norm (A v) _
  · refine le_trans ?_ (A.le_opNorm v)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact norm_le_pi_norm (A v) _

/-- Scalar sums package independent of a particular choice of KAM witnesses. -/
theorem sums {e R s : ℕ → ℝ} {c : ℝ}
    (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2) (hquad : ∀ j, e (j + 1) ≤ e j ^ 2)
    (hc : 0 ≤ c) (hce : c * e 0 ≤ 1 / 2)
    (hR : ∀ j, 0 ≤ R j ∧ R (j + 1) ≤ R j / 16)
    (hs : ∀ j, s (j + 1) = s j / 12) :
    (∀ m k, m ≤ k → e k ≤ e m ^ (2 ^ (k - m))) ∧
    (∀ m, Summable (fun k => e (m + k)) ∧ ∑' k, e (m + k) ≤ 2 * e m) ∧
    Summable (fun k => c ^ k * e k) ∧ (∑' k, c ^ k * e k) ≤ 2 * e 0 ∧
    (∀ k, R k ≤ R 0 / 16 ^ k ∧ s k = s 0 / 12 ^ k) := by
  have hhalf : ∀ j, e j ≤ 1 / 2 := by
    intro j
    induction j with
    | zero => exact he₀.le
    | succ j ih =>
      calc e (j + 1) ≤ e j ^ 2 := hquad j
        _ ≤ e j * 1 := by rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (he j)
        _ ≤ 1 / 2 := by linarith
  have hmono : ∀ j, e (j + 1) ≤ e j := by
    intro j
    calc e (j + 1) ≤ e j ^ 2 := hquad j
      _ = e j * e j := sq _
      _ ≤ e j * 1 := mul_le_mul_of_nonneg_left (by linarith [hhalf j]) (he j)
      _ = e j := mul_one _
  have hmono' : ∀ m, e m ≤ e 0 := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ m ih => exact (hmono m).trans ih
  have hpow : ∀ m k, m ≤ k → e k ≤ e m ^ (2 ^ (k - m)) := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      calc e (k + 1) ≤ e k ^ 2 := hquad k
        _ ≤ (e m ^ (2 ^ (k - m))) ^ 2 := pow_le_pow_left₀ (he k) ih 2
        _ = e m ^ (2 ^ (k + 1 - m)) := by
          rw [← pow_mul, Nat.succ_sub hmk, pow_succ]
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeom_sum : ∑' k : ℕ, (1 / 2 : ℝ) ^ k = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  -- bound `e (m + k) ≤ e m * (1/2)^k`
  have hbd : ∀ m k, e (m + k) ≤ e m * (1 / 2) ^ k := by
    intro m k
    have h1 := hpow m (m + k) (Nat.le_add_right m k)
    rw [Nat.add_sub_cancel_left] at h1
    have hk : k ≤ 2 ^ k - 1 := by
      have := Nat.lt_two_pow_self (n := k)
      omega
    have h2 : e m ^ (2 ^ k) = e m * e m ^ (2 ^ k - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.one_le_two_pow (n := k); omega
    have h3 : e m ^ (2 ^ k - 1) ≤ (1 / 2) ^ (2 ^ k - 1) :=
      pow_le_pow_left₀ (he m) (hhalf m) _
    have h4 : ((1 : ℝ) / 2) ^ (2 ^ k - 1) ≤ (1 / 2) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    calc e (m + k) ≤ e m ^ (2 ^ k) := h1
      _ = e m * e m ^ (2 ^ k - 1) := h2
      _ ≤ e m * (1 / 2) ^ k := mul_le_mul_of_nonneg_left (h3.trans h4) (he m)
  have hcb : ∀ k, c ^ k * e k ≤ e 0 * (1 / 2 : ℝ) ^ k := by
    intro k
    have h1 : e k ≤ e 0 ^ (2 ^ k) := by simpa using hpow 0 k (Nat.zero_le k)
    have hk : k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
    have h2 : e 0 ^ (2 ^ k) = e 0 ^ k * e 0 ^ (2 ^ k - k) := by
      rw [← pow_add]; congr 1; omega
    have h3 : e 0 ^ (2 ^ k - k) ≤ e 0 :=
      pow_le_of_le_one (he 0) (by linarith) (by have := Nat.lt_two_pow_self (n := k); omega)
    have h4 : (c * e 0) ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ (mul_nonneg hc (he 0)) hce k
    calc c ^ k * e k ≤ c ^ k * (e 0 ^ k * e 0 ^ (2 ^ k - k)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (pow_nonneg hc k)
      _ = (c * e 0) ^ k * e 0 ^ (2 ^ k - k) := by rw [mul_pow]; ring
      _ ≤ (1 / 2) ^ k * e 0 :=
          mul_le_mul h4 h3 (pow_nonneg (he 0) _) (by positivity)
      _ = e 0 * (1 / 2) ^ k := mul_comm _ _
  have hgm : ∀ m, Summable (fun k => e m * (1 / 2 : ℝ) ^ k) := fun m => hgeom.mul_left _
  refine ⟨hpow, fun m => ⟨?_, ?_⟩, ?_, ?_, fun k => ⟨?_, ?_⟩⟩
  · exact Summable.of_nonneg_of_le (fun k => he _) (hbd m) (hgm m)
  · calc ∑' k, e (m + k) ≤ ∑' k, e m * (1 / 2 : ℝ) ^ k :=
          Summable.tsum_le_tsum (hbd m) (Summable.of_nonneg_of_le (fun k => he _) (hbd m) (hgm m))
            (hgm m)
      _ = 2 * e m := by rw [tsum_mul_left, hgeom_sum]; ring
  · exact Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hc k) (he k)) hcb (hgm 0)
  · calc ∑' k, c ^ k * e k ≤ ∑' k, e 0 * (1 / 2 : ℝ) ^ k :=
          Summable.tsum_le_tsum hcb
            (Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hc k) (he k)) hcb (hgm 0))
            (hgm 0)
      _ = 2 * e 0 := by rw [tsum_mul_left, hgeom_sum]; ring
  · induction k with
    | zero => simp
    | succ k ih =>
      calc R (k + 1) ≤ R k / 16 := (hR k).2
        _ ≤ R 0 / 16 ^ k / 16 := by gcongr
        _ = R 0 / 16 ^ (k + 1) := by rw [pow_succ]; field_simp
  · induction k with
    | zero => simp
    | succ k ih => rw [hs, ih, pow_succ]; field_simp

end KAM.Planetary
