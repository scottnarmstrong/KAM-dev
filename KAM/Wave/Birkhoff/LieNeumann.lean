/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieVar

/-!
# Neumann inverses (blueprint-W `bpW:w3:flow` (iii), invertibility of `DΓ_t`)

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`neumann_inv`: a bounded operator `A` with `‖A - 1‖ ≤ 1/2` is invertible with a bounded two-sided
inverse `B`, `‖B‖ ≤ 2` and `‖B - 1‖ ≤ 2 ‖A - 1‖`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

theorem neumann_inv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (A : G →L[ℂ] G) (h : ‖A - 1‖ ≤ 1 / 2) :
    ∃ B : G →L[ℂ] G, A * B = 1 ∧ B * A = 1 ∧ ‖B‖ ≤ 2 ∧ ‖B - 1‖ ≤ 2 * ‖A - 1‖ := by
  set x : G →L[ℂ] G := 1 - A with hx
  have hxn : ‖x‖ = ‖A - 1‖ := by rw [hx, norm_sub_rev]
  have hlt : ‖x‖ < 1 := by rw [hxn]; linarith
  have hA : A = 1 - x := by rw [hx]; abel
  refine ⟨∑' n : ℕ, x ^ n, ?_, ?_, ?_, ?_⟩
  · rw [hA]; exact mul_neg_geom_series x hlt
  · rw [hA]; exact geom_series_mul_neg x hlt
  · have h1 := tsum_geometric_le_of_norm_lt_one x hlt
    have h2 : ‖(1 : G →L[ℂ] G)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h3 : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  · have hB : A * ∑' n : ℕ, x ^ n = 1 := by rw [hA]; exact mul_neg_geom_series x hlt
    have hnB : ‖∑' n : ℕ, x ^ n‖ ≤ 2 := by
      have h1 := tsum_geometric_le_of_norm_lt_one x hlt
      have h2 : ‖(1 : G →L[ℂ] G)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      have h3 : (1 - ‖x‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    have e : (∑' n : ℕ, x ^ n) - 1 = x * ∑' n : ℕ, x ^ n := by
      have : (1 - x) * ∑' n : ℕ, x ^ n = 1 := by rw [← hA]; exact hB
      rw [sub_mul, one_mul] at this
      have h' : (∑' n : ℕ, x ^ n) - x * (∑' n : ℕ, x ^ n) - 1 = 0 := by rw [this]; simp
      calc (∑' n : ℕ, x ^ n) - 1 = ((∑' n : ℕ, x ^ n) - x * (∑' n : ℕ, x ^ n) - 1) +
            x * (∑' n : ℕ, x ^ n) := by abel
        _ = x * ∑' n : ℕ, x ^ n := by rw [h', zero_add]
    rw [e, ← hxn]
    calc ‖x * ∑' n : ℕ, x ^ n‖ ≤ ‖x‖ * ‖∑' n : ℕ, x ^ n‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * 2 := mul_le_mul_of_nonneg_left hnB (norm_nonneg _)
      _ = 2 * ‖x‖ := by ring

end KAM.Wave

end
