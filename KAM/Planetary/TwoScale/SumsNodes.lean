/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapDisp

/-!
# Two-scale KAM: literal exports of the constant and sum nodes (GAP-P13)

Unsigned exports stating the literal conclusions of `bpP:p3b#kam-bounds`, `stepP:p3:sum-doubling`
and `stepP:p3:sum-weighted`, over the abstract sequence of `sums` and for `seq p`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Planetary

/-- `bpP:p3b#kam-bounds`: the KAM condition `ĉ Ê₀ < 1` gives `Ê₀ < 1/(8192 n)` and
`(24^{τ+1}/6) Ê₀ < 1/2`. -/
theorem kam_bounds {n : ℕ} (hn : 0 < n) {τ E : ℝ} (h : kamConstant n τ * E < 1) :
    E < 1 / (8192 * (n : ℝ)) ∧ (24 : ℝ) ^ (τ + 1) / 6 * E < 1 / 2 := by
  have h1 : (24 : ℝ) ^ (τ + 1) / 3 ≤ kamConstant n τ := le_max_right _ _
  have h2 : 2 ^ 13 * (n : ℝ) ≤ kamConstant n τ := le_max_left _ _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (24 : ℝ) ^ (τ + 1) := Real.rpow_pos_of_pos (by norm_num) _
  rcases le_or_gt E 0 with hE | hE
  · refine ⟨lt_of_le_of_lt hE (by positivity), ?_⟩
    nlinarith
  · refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h2 hE.le]
    · nlinarith [mul_le_mul_of_nonneg_right h1 hE.le]

private theorem sum_half {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2)
    (hquad : ∀ j, e (j + 1) ≤ e j ^ 2) (j : ℕ) : e j ≤ 1 / 2 := by
  induction j with
  | zero => exact he₀.le
  | succ j ih =>
    calc e (j + 1) ≤ e j ^ 2 := hquad j
      _ ≤ e j * 1 := by rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (he j)
      _ ≤ 1 / 2 := by linarith

private theorem sum_pow_le {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2)
    (hquad : ∀ j, e (j + 1) ≤ e j ^ 2) {m k : ℕ} (hmk : m ≤ k) :
    e k ≤ e m ^ (2 ^ (k - m)) :=
  (sums (e := e) (R := fun _ => 0) (s := fun _ => 0) (c := 0) he he₀ hquad le_rfl (by simp)
    (fun _ => ⟨le_rfl, by simp⟩) (fun _ => by simp)).1 m k hmk

/-- Conditional helper (not a node export): `Ê_k ≤ Ê_m^{2^{k-m}} ≤ Ê_m^{k-m+1}` for `m ≤ k`, and
`Σ_{k≥m} Ê_k ≤ Ê_m/(1-Ê_m) ≤ 2 Ê_m`. -/
theorem sums_doubling_of_quad {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2)
    (hquad : ∀ j, e (j + 1) ≤ e j ^ 2) (m : ℕ) :
    (∀ k, m ≤ k → e k ≤ e m ^ (2 ^ (k - m)) ∧ e m ^ (2 ^ (k - m)) ≤ e m ^ (k - m + 1)) ∧
    Summable (fun k => e (m + k)) ∧
      ∑' k, e (m + k) ≤ e m / (1 - e m) ∧ e m / (1 - e m) ≤ 2 * e m := by
  have hm := sum_half he he₀ hquad m
  have hm1 : 0 < 1 - e m := by linarith
  have hpow : ∀ i : ℕ, e m ^ (2 ^ i) ≤ e m ^ (i + 1) := fun i =>
    pow_le_pow_of_le_one (he m) (by linarith) (Nat.lt_two_pow_self (n := i))
  have hbd : ∀ k, e (m + k) ≤ e m ^ (k + 1) := fun k => by
    have := sum_pow_le he he₀ hquad (Nat.le_add_right m k)
    rw [Nat.add_sub_cancel_left] at this
    exact this.trans (hpow k)
  have hg : Summable (fun k : ℕ => e m ^ (k + 1)) := by
    simpa [pow_succ] using
      (summable_geometric_of_lt_one (he m) (by linarith : e m < 1)).mul_right (e m)
  have hs : Summable (fun k => e (m + k)) :=
    Summable.of_nonneg_of_le (fun k => he _) hbd hg
  refine ⟨fun k hk => ⟨sum_pow_le he he₀ hquad hk, hpow _⟩,
    hs, ?_, ?_⟩
  · have hgs : ∑' k : ℕ, e m ^ (k + 1) = e m / (1 - e m) := by
      have : ∑' k : ℕ, e m ^ (k + 1) = e m * ∑' k : ℕ, e m ^ k := by
        rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
      rw [this, tsum_geometric_of_lt_one (he m) (by linarith : e m < 1)]; field_simp
    exact (hs.tsum_le_tsum hbd hg).trans hgs.le
  · rw [div_le_iff₀ hm1]; nlinarith [he m]

/-- Conditional helper (not a node export): `c^k Ê_k ≤ c^k Ê₀^{k+1} = Ê₀ (c Ê₀)^k ≤ Ê₀ 2^{-k}` and
`Σ c^k Ê_k ≤ 2 Ê₀`. -/
theorem sums_weighted_of_quad {e : ℕ → ℝ} {c : ℝ} (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2)
    (hquad : ∀ j, e (j + 1) ≤ e j ^ 2) (hc : 0 ≤ c) (hce : c * e 0 ≤ 1 / 2) :
    (∀ k, c ^ k * e k ≤ c ^ k * e 0 ^ (k + 1) ∧ c ^ k * e 0 ^ (k + 1) = e 0 * (c * e 0) ^ k ∧
      e 0 * (c * e 0) ^ k ≤ e 0 * (1 / 2) ^ k) ∧
    Summable (fun k => c ^ k * e k) ∧ ∑' k, c ^ k * e k ≤ 2 * e 0 := by
  have hpow : ∀ k, e k ≤ e 0 ^ (k + 1) := fun k => by
    have := sum_pow_le he he₀ hquad (Nat.zero_le k)
    rw [Nat.sub_zero] at this
    exact this.trans (pow_le_pow_of_le_one (he 0) (by linarith) (Nat.lt_two_pow_self (n := k)))
  refine ⟨fun k => ⟨mul_le_mul_of_nonneg_left (hpow k) (pow_nonneg hc k), by ring,
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hc (he 0)) hce k) (he 0)⟩, ?_⟩
  have := (sums (e := e) (R := fun _ => 0) (s := fun _ => 0) (c := c) he he₀ hquad hc hce
    (fun _ => ⟨le_rfl, by simp⟩) (fun _ => by simp)).2.2
  exact ⟨this.1, this.2.1⟩

namespace PsiSteps

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

/-- `stepP:p3:sum-doubling` for `Ê_k = eHat (seq p k)`. -/
theorem seq_sum_doubling (P : PsiSteps sbar p Ds hs fs Ψ Φ) (m : ℕ) :
    (∀ k, m ≤ k → eHat (seq p k) ≤ eHat (seq p m) ^ (2 ^ (k - m)) ∧
      eHat (seq p m) ^ (2 ^ (k - m)) ≤ eHat (seq p m) ^ (k - m + 1)) ∧
    Summable (fun k => eHat (seq p (m + k))) ∧
      ∑' k, eHat (seq p (m + k)) ≤ eHat (seq p m) / (1 - eHat (seq p m)) ∧
      eHat (seq p m) / (1 - eHat (seq p m)) ≤ 2 * eHat (seq p m) :=
  sums_doubling_of_quad (fun j => (P.hyp j).eHat_nonneg)
    (by have := (P.hyp 0).eHat_lt_small; linarith) (fun j => (P.eHat_sq j).le) m

/-- `stepP:p3:sum-weighted` for `Ê_k = eHat (seq p k)`, `c = 24^{τ+1}/6`. -/
theorem seq_sum_weighted (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    (∀ k, ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k) ≤
        ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat p ^ (k + 1) ∧
      ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat p ^ (k + 1) =
        eHat p * ((24 : ℝ) ^ (p.τ + 1) / 6 * eHat p) ^ k ∧
      eHat p * ((24 : ℝ) ^ (p.τ + 1) / 6 * eHat p) ^ k ≤ eHat p * (1 / 2) ^ k) ∧
    Summable (fun k => ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k)) ∧
      ∑' k, ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k) ≤ 2 * eHat p :=
  sums_weighted_of_quad (e := fun j => eHat (seq p j)) (fun j => (P.hyp j).eHat_nonneg)
    (by have := (P.hyp 0).eHat_lt_small; linarith) (fun j => (P.eHat_sq j).le)
    (by positivity) (P.kam_small).1

end PsiSteps

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- `stepP:p3:sum-doubling` from the original KAM hypotheses only. -/
theorem sum_doubling (H : KamHyp D sbar p h f) (m : ℕ) :
    (∀ k, m ≤ k → eHat (seq p k) ≤ eHat (seq p m) ^ (2 ^ (k - m)) ∧
      eHat (seq p m) ^ (2 ^ (k - m)) ≤ eHat (seq p m) ^ (k - m + 1)) ∧
    Summable (fun k => eHat (seq p (m + k))) ∧
      ∑' k, eHat (seq p (m + k)) ≤ eHat (seq p m) / (1 - eHat (seq p m)) ∧
      eHat (seq p m) / (1 - eHat (seq p m)) ≤ 2 * eHat (seq p m) := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, _, _, P⟩ := iterative_steps H
  exact P.seq_sum_doubling m

/-- `stepP:p3:sum-weighted` from the original KAM hypotheses only. -/
theorem sum_weighted (H : KamHyp D sbar p h f) :
    (∀ k, ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k) ≤
        ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat p ^ (k + 1) ∧
      ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat p ^ (k + 1) =
        eHat p * ((24 : ℝ) ^ (p.τ + 1) / 6 * eHat p) ^ k ∧
      eHat p * ((24 : ℝ) ^ (p.τ + 1) / 6 * eHat p) ^ k ≤ eHat p * (1 / 2) ^ k) ∧
    Summable (fun k => ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k)) ∧
      ∑' k, ((24 : ℝ) ^ (p.τ + 1) / 6) ^ k * eHat (seq p k) ≤ 2 * eHat p := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, _, _, P⟩ := iterative_steps H
  exact P.seq_sum_weighted

end KAM.Planetary
