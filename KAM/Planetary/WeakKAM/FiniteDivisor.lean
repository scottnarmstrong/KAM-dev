/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.StripBudget
public import KAM.Planetary.WeakKAM.Extension

/-! # P11B weak-KAM finite-stage divisor invariant

`finite_divisor` (`bpP:p11a:finite-divisor`): on the retained set `K_{ν+1}`, every nonzero mode
`k` with `|k|₁ ≤ T_ν` satisfies `|k·ω_ν(b)| ≥ γ |k|₁^{-τ} ≥ D_ν`. The three source steps are
the named local lemmas `fd_tel` (telescoping, `stepP:p11a:fd-tel`), `fd_test` (the mode was tested
at its shell stage, `stepP:p11a:fd-test`) and `fd_concl` (conclusion, `stepP:p11a:fd-concl`);
only the final inequality is public. The shell-index facts for `selectionModeStage` are proved here.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ τ : ℝ}

/-- The mode stage `m = ν(k)` is a shell index: `|k|₁ ≤ T_m` and `T_{m-1} < |k|₁` (or `m = 0`). -/
theorem selectionModeStage_mem_shell (a : SelectionSchedule n) (hT : 1 ≤ a.T₀)
    {k : Fin n → ℤ} (hk : 0 < selectionModeLength k) :
    k ∈ selectionShell a (selectionModeStage a k) := by
  have hT0 : 0 < a.T₀ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := selectionModeLength k with hL
  set m := selectionModeStage a k with hm
  have hx : Real.log (L / a.T₀) / Real.log 2 ≤ m := Nat.le_ceil _
  have hx' : Real.log (L / a.T₀) ≤ (m : ℝ) * Real.log 2 := by
    rwa [div_le_iff₀ hl2] at hx
  refine ⟨hk, ?_, ?_⟩
  · rw [← Real.log_pow] at hx'
    have := (Real.log_le_log_iff (by positivity) (by positivity)).1 hx'
    rw [div_le_iff₀ hT0] at this
    unfold selectionT
    linarith
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact Or.inl h0
    · right
      have hlt : ((m - 1 : ℕ) : ℝ) < Real.log (L / a.T₀) / Real.log 2 :=
        Nat.lt_ceil.1 (show m - 1 < m by omega)
      rw [lt_div_iff₀ hl2, ← Real.log_pow] at hlt
      have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 hlt
      rw [lt_div_iff₀ hT0] at this
      unfold selectionT
      linarith

/-- A mode of length at most `T_ν` has stage at most `ν`. -/
theorem selectionModeStage_le (a : SelectionSchedule n) (hT : 1 ≤ a.T₀) {k : Fin n → ℤ}
    {ν : ℕ} (hk : 0 < selectionModeLength k) (hkT : selectionModeLength k ≤ selectionT a ν) :
    selectionModeStage a k ≤ ν := by
  have hT0 : 0 < a.T₀ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Nat.ceil_le.2
  rw [div_le_iff₀ hl2, ← Real.log_pow]
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ hT0]
  unfold selectionT at hkT
  linarith

/-- Retained-prefix nesting: `K_j ⊆ K_i` for `i ≤ j ≤ ν`. -/
theorem selection_chain_antitone {d : SelectionData n} {a : SelectionSchedule n}
    {c : SelectionChain n} {ν : ℕ} (hc : SelectionExtensionChain d a c ν)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ ν) : c.K j ⊆ c.K i := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j hij ih => exact (hc.nested j (by omega)).trans (ih (by omega))

/-- `fd_tel`: the finite increment tail from stage `m` to `ν` is bounded by `selectionTail a m`. -/
theorem fd_tel {d : SelectionData n} {a : SelectionSchedule n} {c : SelectionChain n} {ν : ℕ}
    (hc : SelectionExtensionChain d a c ν) (ht : 0 < a.t₀) (hτ : 0 ≤ a.τ)
    (hs : 0 < a.s₀) (he : 0 < a.ε₀) {m : ℕ} (hm : m ≤ ν)
    (hsum : Summable (fun j => selectionell a (j + m))) {b : SelectionR n}
    (hb : b ∈ c.K ν) :
    ‖selectionFrequency d c ν (selectionReal b) - selectionFrequency d c m (selectionReal b)‖ ≤
      selectionTail a m := by
  have hvp := (selectionVarpi_pos_le_one n a.μ hτ).1
  have hq : 0 < selectionQ n a.μ a.τ := by
    unfold selectionQ
    have := Real.sqrt_pos.2 hvp
    linarith
  have hnn : ∀ j, 0 ≤ selectionell a (j + m) := by
    intro j
    unfold selectionell selectionε selections
    positivity
  have hdiff : selectionFrequency d c ν (selectionReal b) - selectionFrequency d c m
      (selectionReal b) = ∑ i ∈ Finset.Ico m ν, c.Δω i (selectionReal b) := by
    unfold selectionFrequency
    rw [← Finset.sum_range_add_sum_Ico _ hm]
    abel
  rw [hdiff, Finset.sum_Ico_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (ν - m), c.Δω (m + i) (selectionReal b)‖
      ≤ ∑ i ∈ Finset.range (ν - m), ‖c.Δω (m + i) (selectionReal b)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (ν - m), selectionell a (i + m) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiν : m + i < ν := by
          have := Finset.mem_range.1 hi
          omega
        rw [add_comm m i]
        have hbK : b ∈ c.K (i + m) := by
          rw [add_comm]
          exact selection_chain_antitone hc hiν.le le_rfl hb
        apply hc.bound (i + m) (by omega)
        have htj : 0 < selectiont a (i + m) := by
          unfold selectiont
          positivity
        have h0 : selectionReal b - (fun i => ((b i : ℝ) : ℂ)) = 0 := by
          ext i
          simp [selectionReal]
        exact ⟨b, hbK, by rw [h0, norm_zero]; exact htj⟩
    _ ≤ selectionTail a m := Summable.sum_le_tsum _ (fun i _ => hnn i) hsum

/-- `fd_test`: a point of `K_{ν+1}` lies in every `K_{m+1}`, hence passes the stage-`m` shell test. -/
theorem fd_test {d : SelectionData n} {a : SelectionSchedule n} {c : SelectionChain n} {ν : ℕ}
    (hc : SelectionFiniteChain d a c ν) {m : ℕ} (hm : m ≤ ν) {b : SelectionR n}
    (hb : b ∈ selectionRetained a d c ν) {k : Fin n → ℤ} (hk : k ∈ selectionShell a m) :
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      ‖∑ i, (k i : ℂ) * selectionFrequency d c m (selectionReal b) i‖ := by
  have hbm : b ∈ selectionRetained a d c m := by
    rcases hm.eq_or_lt with h | h
    · rw [h]; exact hb
    · rw [← hc.retained m h]
      exact selection_chain_antitone hc.toSelectionExtensionChain (by omega) le_rfl hb.1
  exact hbm.2 k hk

/-- `fd_concl`: the tested divisor `2γ/|k|^τ` minus the tail error `γ/|k|^τ`. -/
theorem fd_concl {x y : SelectionC n} {k : Fin n → ℤ} {γ τ T : ℝ}
    (hk : 0 < selectionModeLength k) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hxy : ‖x - y‖ ≤ γ * T ^ (-τ - 1)) (hkT : selectionModeLength k ≤ T)
    (htest : 2 * γ / selectionModeLength k ^ τ ≤ ‖∑ i, (k i : ℂ) * y i‖) :
    γ / selectionModeLength k ^ τ ≤ ‖∑ i, (k i : ℂ) * x i‖ := by
  set L := selectionModeLength k with hL
  have hsplit : ∑ i, (k i : ℂ) * x i =
      ∑ i, (k i : ℂ) * y i + ∑ i, (k i : ℂ) * (x - y) i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  have herr : ‖∑ i, (k i : ℂ) * (x - y) i‖ ≤ L * ‖x - y‖ := by
    calc ‖∑ i, (k i : ℂ) * (x - y) i‖ ≤ ∑ i, ‖(k i : ℂ) * (x - y) i‖ := norm_sum_le _ _
      _ ≤ ∑ i, |(k i : ℝ)| * ‖x - y‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          gcongr
          · simp
          · exact norm_le_pi_norm (x - y) i
      _ = L * ‖x - y‖ := by rw [hL, selectionModeLength, Finset.sum_mul]
  have hTL : T ^ (-τ - 1) ≤ L ^ (-τ - 1) :=
    Real.rpow_le_rpow_of_nonpos hk hkT (by linarith)
  have hLp : 0 < L ^ τ := Real.rpow_pos_of_pos hk τ
  have hid : L * (γ * L ^ (-τ - 1)) = γ / L ^ τ := by
    rw [Real.rpow_sub_one hk.ne', Real.rpow_neg hk.le]
    field_simp
  have h2 : 2 * γ / L ^ τ = γ / L ^ τ + γ / L ^ τ := by ring
  have hE : L * ‖x - y‖ ≤ γ / L ^ τ := by
    rw [← hid]
    gcongr
    exact hxy.trans (by gcongr)
  rw [hsplit]
  have := norm_sub_norm_le (∑ i, (k i : ℂ) * y i) (-∑ i, (k i : ℂ) * (x - y) i)
  rw [sub_neg_eq_add, norm_neg] at this
  linarith

/-- The finite-stage divisor invariant (`bpP:p11a:finite-divisor`). -/
theorem finite_divisor (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionFiniteChain d a c ν)
    (ht : 0 < a.t₀) (hT : 1 ≤ a.T₀) (hτ : 0 ≤ a.τ) (hγ : 0 < a.γ)
    (hs : 0 < a.s₀) (he : 0 < a.ε₀)
    (htail : ∀ m ≤ ν, Summable (fun j => selectionell a (j + m)) ∧
      selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1)) :
    ∀ b ∈ selectionRetained a d c ν, ∀ k : Fin n → ℤ,
      0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
      a.γ / selectionModeLength k ^ a.τ ≤
        ‖∑ i, (k i : ℂ) * selectionFrequency d c ν (selectionReal b) i‖ ∧
      selectionD a ν ≤ a.γ / selectionModeLength k ^ a.τ := by
  intro b hb k hk hkT
  have hm := selectionModeStage_le a hT hk hkT
  have hsh := selectionModeStage_mem_shell a hT hk
  set m := selectionModeStage a k
  have hkm : selectionModeLength k ≤ selectionT a m := hsh.2.1
  refine ⟨?_, ?_⟩
  · refine fd_concl hk hγ hτ ?_ hkm (fd_test hc hm hb hsh)
    exact (fd_tel hc.toSelectionExtensionChain ht hτ hs he hm (htail m hm).1 hb.1).trans
      (htail m hm).2
  · unfold selectionD
    have hLp : 0 < selectionModeLength k ^ a.τ := Real.rpow_pos_of_pos hk _
    rw [Real.rpow_neg (by unfold selectionT; positivity), div_eq_mul_inv]
    gcongr

end KAM.Planetary
