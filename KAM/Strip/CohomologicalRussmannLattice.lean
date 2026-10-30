/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalRussmannSep
public import KAM.Fourier.ExponentialDecay
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The dyadic-free lattice sum for Rüssmann's estimate

`∑_{k≠0} |k·ω|⁻² e^{-2πδ|k|₁} ≤ 6 (1 + 2^τ) γ⁻² (2τ/(eπδ))^{2τ}` for every `δ > 0`.

The shell bounds `S_N ≤ 2 (1 + 2^τ) γ⁻² N^{2τ}` (`KAM.sum_inv_sq_frequencyDot_le`) are combined with
the weight `w(N) = e^{-bN}` (`b = 2πδ`) by discrete Abel summation (`KAM.abel_finite`), then
`(1 - e^{-b}) ≤ b`, `N^{2τ} e^{-bN/2} ≤ (2·2τ/(eb))^{2τ}` and a geometric sum `≤ 2/b`.
This uses no dyadic decomposition, and is also valid for `τ = 0`.
-/

public noncomputable section

namespace KAM

section Abel

variable {ι : Type*}

theorem abel_telescope (w : ℕ → ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    ∑ N ∈ Finset.Ico 1 M, (w N - w (N + 1)) * (if m ≤ N then 1 else 0) = w m - w M := by
  induction M, hmM using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · ring
    · intro N hN
      have := (Finset.mem_Ico.mp hN).2
      simp [show ¬ m ≤ N by omega]
  | succ M hmM ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, if_pos hmM]
    ring

/-- **Discrete Abel summation** over a finite family with weights `w (m k)`, `1 ≤ m k ≤ M`. -/
theorem abel_finite [DecidableEq ι] (F : Finset ι) (m : ι → ℕ) (a : ι → ℝ) (w : ℕ → ℝ) (M : ℕ)
    (hm : ∀ k ∈ F, 1 ≤ m k ∧ m k ≤ M) :
    ∑ k ∈ F, a k * w (m k) =
      ∑ N ∈ Finset.Ico 1 M, (w N - w (N + 1)) * ∑ k ∈ F.filter (fun k => m k ≤ N), a k +
        w M * ∑ k ∈ F, a k := by
  have h1 : ∀ N, ∑ k ∈ F.filter (fun k => m k ≤ N), a k = ∑ k ∈ F, a k * (if m k ≤ N then 1 else 0) := by
    intro N
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := abel_telescope w (hm k hk).1 (hm k hk).2
  calc a k * w (m k) = a k * (w (m k) - w M) + w M * a k := by ring
    _ = _ := by
      rw [← this, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun N _ => by ring

end Abel

section Analytic

/-- The geometric sum `∑_{N≥1} e^{-cN} ≤ 1/c`, finite form. -/
theorem sum_exp_neg_Ico_le {c : ℝ} (hc : 0 < c) (M : ℕ) :
    ∑ N ∈ Finset.Ico 1 M, Real.exp (-c * N) ≤ 1 / c := by
  set x : ℝ := Real.exp (-c) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ N : ℕ, Real.exp (-c * N) = x ^ N := fun N => by
    rw [hx, ← Real.exp_nat_mul]; congr 1; ring
  simp only [hterm]
  refine (geom_sum_Ico_le_of_lt_one hx0.le hx1).trans ?_
  rw [pow_one, div_le_div_iff₀ (by linarith) hc, one_mul]
  have h1 : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
  have h2 : x * Real.exp c = 1 := by rw [hx, ← Real.exp_add]; simp
  nlinarith [mul_le_mul_of_nonneg_left h1 hx0.le]

/-- Pointwise: `(e^{-bN} - e^{-b(N+1)}) N^a ≤ b R e^{-bN/2}`, with `R = (a/(e b/2))^a`. -/
theorem abel_term_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (N : ℕ) :
    (Real.exp (-b * N) - Real.exp (-b * (N + 1 : ℕ))) * (N : ℝ) ^ a ≤
      b * (a / (Real.exp 1 * (b / 2))) ^ a * Real.exp (-(b / 2) * N) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hd : Real.exp (-b * N) - Real.exp (-b * (N + 1 : ℕ)) ≤ b * Real.exp (-b * N) := by
    have : Real.exp (-b * (N + 1 : ℕ)) = Real.exp (-b * N) * Real.exp (-b) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [this]
    have h1 : 1 - b ≤ Real.exp (-b) := by linarith [Real.add_one_le_exp (-b)]
    nlinarith [Real.exp_pos (-b * N)]
  have hsup := Fourier.rpow_mul_exp_neg_le (x := (N : ℝ)) (τ := a) (δ := b / 2) hN ha
    (by linarith)
  have hsplit : Real.exp (-b * N) = Real.exp (-(b / 2) * N) * Real.exp (-(b / 2) * N) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ b * Real.exp (-b * N) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hN _)
    _ = b * ((N : ℝ) ^ a * Real.exp (-(b / 2) * N)) * Real.exp (-(b / 2) * N) := by
        rw [hsplit]; ring
    _ ≤ b * (a / (Real.exp 1 * (b / 2))) ^ a * Real.exp (-(b / 2) * N) := by
        gcongr

end Analytic

variable {n : ℕ}

/-- **The lattice sum.** For every finite set `s` of modes and `δ > 0`,
`∑_{k∈s, k≠0} |k·ω|⁻² e^{-2πδ|k|₁} ≤ 6 (1 + 2^τ) γ⁻² (2τ/(eπδ))^{2τ}`. -/
theorem sum_inv_sq_exp_le {ω : Fin n → ℝ} {γ τ δ : ℝ} (hω : Diophantine.Condition ω γ τ)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s.filter (· ≠ 0), ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ *
        Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) ≤
      6 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) := by
  classical
  set F := s.filter (· ≠ 0) with hF
  set b : ℝ := 2 * Real.pi * δ with hb
  have hb0 : 0 < b := by positivity
  set C : ℝ := 2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ with hC
  have hC0 : 0 ≤ C := by positivity
  set R : ℝ := (2 * τ / (Real.exp 1 * (b / 2))) ^ (2 * τ) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hRe : R = (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) := by
    rw [hR, hb]; congr 2; ring
  set M : ℕ := F.sup modeNat + 1 with hM
  set w : ℕ → ℝ := fun N => Real.exp (-b * N) with hw
  set a : (Fin n → ℤ) → ℝ := fun k => ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ with ha
  have hFne : ∀ k ∈ F, k ≠ 0 := fun k hk => (Finset.mem_filter.mp hk).2
  have hm : ∀ k ∈ F, 1 ≤ modeNat k ∧ modeNat k ≤ M := fun k hk =>
    ⟨modeNat_pos (hFne k hk), by
      have := Finset.le_sup (f := modeNat) hk
      omega⟩
  have hterm : ∀ k ∈ F, a k * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) =
      a k * w (modeNat k) := fun k _ => by
    rw [hw, modeSize_eq_modeNat]
  rw [Finset.sum_congr rfl hterm, abel_finite F modeNat a w M hm]
  have hT : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ F.filter (fun k => modeNat k ≤ N), a k ≤ C * (N : ℝ) ^ (2 * τ) :=
    fun N hN => sum_inv_sq_frequencyDot_le hω hγ hτ hN _ fun k hk =>
      ⟨hFne k (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  have hTM : ∑ k ∈ F, a k ≤ C * (M : ℝ) ^ (2 * τ) := by
    have hMge : 1 ≤ M := by omega
    have := hT M hMge
    rwa [Finset.filter_true_of_mem fun k hk => (hm k hk).2] at this
  have hdnn : ∀ N : ℕ, 0 ≤ w N - w (N + 1) := fun N => by
    simp only [hw]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast
      nlinarith))
  -- first part
  have hfirst : ∑ N ∈ Finset.Ico 1 M, (w N - w (N + 1)) * ∑ k ∈ F.filter (fun k => modeNat k ≤ N), a k
      ≤ ∑ N ∈ Finset.Ico 1 M, C * (b * R * Real.exp (-(b / 2) * N)) := by
    refine Finset.sum_le_sum fun N hN => ?_
    have hN1 : 1 ≤ N := (Finset.mem_Ico.mp hN).1
    calc _ ≤ (w N - w (N + 1)) * (C * (N : ℝ) ^ (2 * τ)) :=
          mul_le_mul_of_nonneg_left (hT N hN1) (hdnn N)
      _ = C * ((w N - w (N + 1)) * (N : ℝ) ^ (2 * τ)) := by ring
      _ ≤ C * (b * R * Real.exp (-(b / 2) * N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          have := abel_term_le (a := 2 * τ) (b := b) (by linarith) hb0 N
          simpa only [hw, hR] using this
  have hgeo := sum_exp_neg_Ico_le (c := b / 2) (by positivity) M
  have hsum1 : ∑ N ∈ Finset.Ico 1 M, C * (b * R * Real.exp (-(b / 2) * N)) ≤ 2 * C * R := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc C * (b * R * ∑ N ∈ Finset.Ico 1 M, Real.exp (-(b / 2) * N))
        ≤ C * (b * R * (1 / (b / 2))) := by gcongr
      _ = 2 * C * R := by field_simp
  -- second part
  have hsecond : w M * ∑ k ∈ F, a k ≤ C * R := by
    have hsup := Fourier.rpow_mul_exp_neg_le (x := (M : ℝ)) (τ := 2 * τ) (δ := b / 2)
      (Nat.cast_nonneg M) (by linarith) (by positivity)
    have hwM : w M ≤ Real.exp (-(b / 2) * M) := by
      simp only [hw]
      exact Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        nlinarith)
    calc w M * ∑ k ∈ F, a k ≤ Real.exp (-(b / 2) * M) * (C * (M : ℝ) ^ (2 * τ)) :=
          mul_le_mul hwM hTM (Finset.sum_nonneg fun k _ => by positivity) (Real.exp_pos _).le
      _ = C * ((M : ℝ) ^ (2 * τ) * Real.exp (-(b / 2) * M)) := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_left hsup hC0
  have htot := add_le_add (hfirst.trans hsum1) hsecond
  rw [← hRe]
  calc _ ≤ 2 * C * R + C * R := htot
    _ = 6 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * R := by rw [hC]; ring

end KAM

end
