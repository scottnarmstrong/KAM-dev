/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalRussmannCount
public import KAM.Diophantine.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Separation of the small divisors and the shell sums `S_N`

For `ω` `(γ, τ)`-Diophantine, the reals `k·ω` with `0 < |k|₁ ≤ N` are pairwise
`γ (2N)^{-τ}`-separated
and have modulus at least `γ N^{-τ}`. Rüssmann's counting lemma then gives
`∑_{0<|k|₁≤N} |k·ω|⁻² ≤ 2 (1 + 2^τ) γ⁻² N^{2τ}` (`KAM.sum_inv_sq_frequencyDot_le`).
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- The `ℓ¹` size of a mode as a natural number. -/
@[expose] def modeNat (k : Fin n → ℤ) : ℕ := ∑ j, (k j).natAbs

theorem modeSize_eq_modeNat (k : Fin n → ℤ) : Fourier.modeSize k = (modeNat k : ℝ) := by
  simp [Fourier.modeSize, modeNat, Nat.cast_sum]

theorem modeNat_pos {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < modeNat k := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  exact lt_of_lt_of_le (Int.natAbs_pos.mpr hj)
    (Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j))

theorem modeNat_sub_le (k k' : Fin n → ℤ) : modeNat (k - k') ≤ modeNat k + modeNat k' := by
  unfold modeNat
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Pi.sub_apply]
  omega

theorem frequencyDot_sub' (ω : Fin n → ℝ) (k k' : Fin n → ℤ) :
    Diophantine.frequencyDot ω (k - k') =
      Diophantine.frequencyDot ω k - Diophantine.frequencyDot ω k' := by
  simp [Diophantine.frequencyDot, sub_mul, Finset.sum_sub_distrib]

/-- **Shell sums.** For a finite set `F` of nonzero modes of size at most `N` (`N ≥ 1`),
`∑_{k∈F} |k·ω|⁻² ≤ 2 (1 + 2^τ) γ⁻² N^{2τ}`. -/
theorem sum_inv_sq_frequencyDot_le {ω : Fin n → ℝ} {γ τ : ℝ} (hω : Diophantine.Condition ω γ τ)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) {N : ℕ} (hN : 1 ≤ N) (F : Finset (Fin n → ℤ))
    (hF : ∀ k ∈ F, k ≠ 0 ∧ modeNat k ≤ N) :
    ∑ k ∈ F, ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ ≤
      2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (N : ℝ) ^ (2 * τ) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set t₀ : ℝ := γ / (N : ℝ) ^ τ with ht₀
  set s : ℝ := γ / (2 * (N : ℝ)) ^ τ with hs
  have hNτ : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 τ
  have h2Nτ : 0 < (2 * (N : ℝ)) ^ τ := Real.rpow_pos_of_pos (by positivity) τ
  have ht0 : 0 < t₀ := div_pos hγ hNτ
  have hs0 : 0 < s := div_pos hγ h2Nτ
  have hmode : ∀ k ∈ F, Fourier.modeSize k ≤ N := fun k hk => by
    rw [modeSize_eq_modeNat]; exact_mod_cast (hF k hk).2
  have hmpos : ∀ k ∈ F, 0 < Fourier.modeSize k := fun k hk => by
    rw [modeSize_eq_modeNat]; exact_mod_cast modeNat_pos (hF k hk).1
  have hge : ∀ k ∈ F, t₀ ≤ |Diophantine.frequencyDot ω k| := fun k hk =>
    le_trans (div_le_div_of_nonneg_left hγ.le (Real.rpow_pos_of_pos (hmpos k hk) τ)
      (Real.rpow_le_rpow (hmpos k hk).le (hmode k hk) hτ)) (hω k (hF k hk).1)
  have hsep : ∀ k ∈ F, ∀ k' ∈ F, k ≠ k' →
      s ≤ |Diophantine.frequencyDot ω k - Diophantine.frequencyDot ω k'| := by
    intro k hk k' hk' hne
    rw [← frequencyDot_sub']
    have hne' : k - k' ≠ 0 := sub_ne_zero.mpr hne
    have hp : 0 < Fourier.modeSize (k - k') := by
      rw [modeSize_eq_modeNat]; exact_mod_cast modeNat_pos hne'
    have hle : Fourier.modeSize (k - k') ≤ 2 * N := by
      rw [modeSize_eq_modeNat]
      have := modeNat_sub_le k k'
      have h1 := (hF k hk).2
      have h2 := (hF k' hk').2
      exact_mod_cast (by omega : modeNat (k - k') ≤ 2 * N)
    exact le_trans (div_le_div_of_nonneg_left hγ.le (Real.rpow_pos_of_pos hp τ)
      (Real.rpow_le_rpow hp.le hle hτ)) (hω _ hne')
  have hinj : Set.InjOn (Diophantine.frequencyDot ω) (F : Set (Fin n → ℤ)) := by
    intro k hk k' hk' h
    by_contra hne
    have := hsep k hk k' hk' hne
    rw [h, sub_self, abs_zero] at this
    linarith
  have hcount := sum_inv_sq_le_of_separated hs0 ht0 (F.image (Diophantine.frequencyDot ω))
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact hge k hk)
    (fun x hx y hy hxy => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hy
      exact hsep k hk k' hk' fun h => hxy (by rw [h]))
  rw [Finset.sum_image hinj] at hcount
  refine hcount.trans (le_of_eq ?_)
  have h2τ : (2 * (N : ℝ)) ^ τ = 2 ^ τ * (N : ℝ) ^ τ := Real.mul_rpow (by norm_num) hN0.le
  have hNN : (N : ℝ) ^ (2 * τ) = (N : ℝ) ^ τ * (N : ℝ) ^ τ := by
    rw [two_mul, Real.rpow_add hN0]
  have h2pos : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) τ
  rw [hNN, ht₀, hs, h2τ]
  field_simp

end KAM

end
