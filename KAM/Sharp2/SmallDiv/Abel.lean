/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Shell
public import KAM.Sharp2.SmallDiv.Bound
public import KAM.Strip.CohomologicalRussmannLattice
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Exact Abel summation for the tail (blueprint `bp:p2s2sd:abel`)

`sdTail_ge`: for `ω` `(γ, τ)`-Diophantine, a finite set `F` of modes with `|k|₁ > N` has
`∑_{k∈F} |k·ω|⁻² e^{-4πb|k|₁} ≤ T_N(b)` (`KAM.Sharp2.sdTail`). Summation by parts with the shell
bound `shell_sum_le`; the boundary term `C M^{2τ} e^{-4πbM}` tends to `0`.
`sdSum_le_finite_add_tail`: `S(ω, b) ≤ sdFinite ω b N + T_N(b)`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

open KAM

variable {n : ℕ}

theorem summable_tailTerm {p β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Summable fun M : ℕ => if M ≤ N then (0 : ℝ) else (M : ℝ) ^ p * Real.exp (-β * M) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul ⌈p⌉₊ hβ
  refine hs.of_nonneg_of_le (fun M => by positivity) fun M => ?_
  split_ifs with h
  · positivity
  · have hM : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (M : ℝ) ^ p ≤ (M : ℝ) ^ (⌈p⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (Nat.le_ceil p)
      _ = (M : ℝ) ^ ⌈p⌉₊ := Real.rpow_natCast _ _

/-- **The tail** (Abel summation). -/
theorem sum_term_tail_le {ω : Fin n → ℝ} {γ τ b : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hb : 0 < b) (N : ℕ) (F : Finset (Fin n → ℤ))
    (hF : ∀ k ∈ F, N < modeNat k) :
    ∑ k ∈ F, smallDivisorTerm ω (2 * b) k ≤ sdTail τ γ b N := by
  classical
  set β : ℝ := 4 * Real.pi * b with hβ
  have hβ0 : 0 < β := by positivity
  set C : ℝ := shellConst τ * (γ ^ 2)⁻¹ with hC
  have hC0 : 0 ≤ C := by have := shellConst_pos hτ; positivity
  set g : ℕ → ℝ := fun M => if M ≤ N then 0 else (M : ℝ) ^ (2 * τ) * Real.exp (-β * M) with hg
  have hgs : Summable g := summable_tailTerm hβ0 N
  have hg0 : ∀ M, 0 ≤ g M := fun M => by simp only [hg]; split_ifs <;> positivity
  set x : ℝ := Real.exp (-β) with hx
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hk0 : ∀ k ∈ F, k ≠ 0 := fun k hk h => by
    have := hF k hk
    rw [h] at this
    simp [modeNat] at this
  set a : (Fin n → ℤ) → ℝ := fun k => ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ with ha
  set w : ℕ → ℝ := fun m => Real.exp (-β * m) with hw
  have hterm : ∀ k ∈ F, smallDivisorTerm ω (2 * b) k = a k * w (modeNat k) := fun k hk => by
    rw [smallDivisorTerm_of_ne (hk0 k hk), modeSize_eq_modeNat]
    simp only [ha, hw, hβ]
    congr 2
    ring
  have hshell : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k ≤ C * (m : ℝ) ^ (2 * τ) := fun m hm => by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := modeBox n m) ?_
      fun k _ _ => by positivity) (shell_sum_le hω hγ hτ hm)
    intro k hk
    obtain ⟨hkF, hkm⟩ := Finset.mem_filter.mp hk
    exact mem_modeBox.mpr ⟨hk0 k hkF, hkm⟩
  have hempty : ∀ m : ℕ, m ≤ N → ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k = 0 := by
    intro m hm
    rw [Finset.filter_false_of_mem fun k hk => by have := hF k hk; omega, Finset.sum_empty]
  set T : ℝ := (1 - x) * C * ∑' M, g M with hT
  have hTeq : sdTail τ γ b N = T := by
    simp only [sdTail, hT, hC, hg, hx, hβ]
    have e : ∀ M : ℕ, (if M ≤ N then (0 : ℝ) else (M : ℝ) ^ (2 * τ) *
        Real.exp (-4 * Real.pi * b * M)) =
        (if M ≤ N then 0 else (M : ℝ) ^ (2 * τ) * Real.exp (-(4 * Real.pi * b) * M)) :=
      fun M => by congr 3; ring
    simp only [e]
    rw [show -4 * Real.pi * b = -(4 * Real.pi * b) by ring, inv_pow]
    ring
  have hmain : ∀ M : ℕ, N + 1 ≤ M → (∀ k ∈ F, modeNat k ≤ M) →
      ∑ k ∈ F, smallDivisorTerm ω (2 * b) k ≤ T + C * ((M : ℝ) ^ (2 * τ) * Real.exp (-β * M)) := by
    intro M hM hFM
    have hm : ∀ k ∈ F, 1 ≤ modeNat k ∧ modeNat k ≤ M := fun k hk =>
      ⟨by have := hF k hk; omega, hFM k hk⟩
    rw [Finset.sum_congr rfl hterm, abel_finite F modeNat a w M hm]
    have hfirst : ∀ m ∈ Finset.Ico 1 M,
        (w m - w (m + 1)) * ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k ≤ (1 - x) * C * g m := by
      intro m hm1
      have hm1' : 1 ≤ m := (Finset.mem_Ico.mp hm1).1
      have hd : w m - w (m + 1) = (1 - x) * Real.exp (-β * m) := by
        simp only [hw, hx]
        rw [show -β * ((m + 1 : ℕ) : ℝ) = -β * m + -β by push_cast; ring, Real.exp_add]
        ring
      by_cases hNm : m ≤ N
      · rw [hempty m hNm, mul_zero]
        simp only [hg, hNm, ite_true, mul_zero, le_refl]
      · have hgm : g m = (m : ℝ) ^ (2 * τ) * Real.exp (-β * m) := by simp only [hg, hNm, ite_false]
        rw [hgm, hd]
        calc (1 - x) * Real.exp (-β * m) * ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k
            ≤ (1 - x) * Real.exp (-β * m) * (C * (m : ℝ) ^ (2 * τ)) :=
              mul_le_mul_of_nonneg_left (hshell m hm1') (by have := Real.exp_pos (-β * m); nlinarith)
          _ = _ := by ring
    have hsum1 : ∑ m ∈ Finset.Ico 1 M, (w m - w (m + 1)) *
        ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k ≤ T := by
      refine (Finset.sum_le_sum hfirst).trans ?_
      rw [← Finset.mul_sum, hT]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) hC0)
      exact hgs.sum_le_tsum _ fun m _ => hg0 m
    have hsecond : w M * ∑ k ∈ F, a k ≤ C * ((M : ℝ) ^ (2 * τ) * Real.exp (-β * M)) := by
      have hFa : ∑ k ∈ F, a k ≤ C * (M : ℝ) ^ (2 * τ) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := modeBox n M) ?_
          fun k _ _ => by positivity) (shell_sum_le hω hγ hτ (by omega))
        intro k hk
        exact mem_modeBox.mpr ⟨hk0 k hk, hFM k hk⟩
      calc w M * ∑ k ∈ F, a k ≤ Real.exp (-β * M) * (C * (M : ℝ) ^ (2 * τ)) :=
            mul_le_mul_of_nonneg_left hFa (Real.exp_pos _).le
        _ = _ := by ring
    exact add_le_add hsum1 hsecond
  have hlim : Tendsto (fun M : ℕ => T + C * ((M : ℝ) ^ (2 * τ) * Real.exp (-β * M))) atTop
      (𝓝 T) := by
    have h1 : Tendsto (fun M : ℕ => (M : ℝ) ^ (2 * τ) * Real.exp (-β * M)) atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * τ) β hβ0).comp tendsto_natCast_atTop_atTop
    simpa using (h1.const_mul C).const_add T
  rw [hTeq]
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨max (N + 1) (F.sup modeNat), fun M hM =>
    hmain M (le_of_max_le_left hM) fun k hk =>
      (Finset.le_sup (f := modeNat) hk).trans (le_of_max_le_right hM)⟩)

theorem sdFinite_summand (ω : Fin n → ℝ) (b : ℝ) (N : ℕ) (k : Fin n → ℤ) :
    (if k = 0 ∨ N < ∑ i, (k i).natAbs then (0 : ℝ) else
      (|∑ i, (k i : ℝ) * ω i|)⁻¹ ^ 2 * Real.exp (-4 * Real.pi * b * ∑ i, |(k i : ℝ)|)) =
      if N < modeNat k then 0 else smallDivisorTerm ω (2 * b) k := by
  by_cases hk : k = 0
  · subst hk; simp [smallDivisorTerm]
  · have h := sdSum_term_eq ω b k
    simp only [hk, ite_false] at h
    by_cases hN : N < modeNat k
    · have : N < ∑ i, (k i).natAbs := hN
      simp [hk, this, hN]
    · have : ¬ N < ∑ i, (k i).natAbs := hN
      simp only [hk, this, hN, or_self, ite_false]
      exact h

/-- **The classical split**: `S(ω, b) ≤ (finite part up to N) + T_N(b)`. -/
theorem sdSum_le_finite_add_tail {ω : Fin n → ℝ} {γ τ b : ℝ} (hω : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hb : 0 < b) (N : ℕ) :
    sdSum ω b ≤ sdFinite ω b N + sdTail τ γ b N := by
  classical
  have h2b : 0 < 2 * b := by positivity
  rw [sdSum_eq_smallDivisorSum]
  have hsum := summable_smallDivisorTerm hω.condition hγ hτ h2b
  refine hsum.tsum_le_of_sum_le fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun k => modeNat k ≤ N)]
  refine add_le_add ?_ (sum_term_tail_le hω hγ hτ hb N _ fun k hk => by
    have := (Finset.mem_filter.mp hk).2
    omega)
  unfold sdFinite
  simp only [sdFinite_summand]
  have hsub : u.filter (fun k => modeNat k ≤ N) ⊆
      Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) N) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    have hkN := (Finset.mem_filter.mp hk).2
    have hj : (k j).natAbs ≤ modeNat k :=
      Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have habs : |k j| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hj.trans hkN
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  calc ∑ k ∈ u.filter (fun k => modeNat k ≤ N), smallDivisorTerm ω (2 * b) k
      = ∑ k ∈ u.filter (fun k => modeNat k ≤ N),
          (if N < modeNat k then 0 else smallDivisorTerm ω (2 * b) k) :=
        Finset.sum_congr rfl fun k hk => by
          simp [not_lt.mpr (Finset.mem_filter.mp hk).2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by
          split_ifs
          · exact le_rfl
          · exact smallDivisorTerm_nonneg _ _ _

end KAM.Sharp2

end
