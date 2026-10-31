/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.YSeries3

/-!
# Analyticity of the sums `Σ c_n V_n(w,…,w)` (blueprint-W `bpW:w3:Yseries`)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

`lieSeriesV c`: the formal multilinear series with the coefficient `c_n V_n` in degree `2n+3`
and `0` elsewhere. `hasFPowerSeriesOnBall_lieV`: for `‖c_n‖ ≤ 1` it is a power series of
`w ↦ Σ_n c_n V_n(w,…,w)` on every ball `‖w‖ < ρ`, `2Cρ² ≤ 1/80`, hence this map is analytic there
(`analyticAt_lieV`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S N : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)

/-- The formal series with `c_n V_n` in degree `2n + 3`. -/
def lieSeriesV (c : ℕ → ℂ) : FormalMultilinearSeries ℂ E F := fun m =>
  if h : m % 2 = 1 ∧ 3 ≤ m then
    ContinuousMultilinearMap.domDomCongr
      (finCongr (by omega : 2 * ((m - 3) / 2) + 3 = m))
      (c ((m - 3) / 2) • lieV ι S N ((m - 3) / 2))
  else 0

theorem lieSeriesV_const (c : ℕ → ℂ) (m : ℕ) (y : E) :
    lieSeriesV ι S N c m (fun _ => y) =
      if m % 2 = 1 ∧ 3 ≤ m then c ((m - 3) / 2) • lieV ι S N ((m - 3) / 2) (fun _ => y)
      else 0 := by
  unfold lieSeriesV
  split_ifs with h
  · simp [ContinuousMultilinearMap.domDomCongr_apply]
  · simp

theorem norm_lieSeriesV_le (c : ℕ → ℂ) (m : ℕ) :
    ‖lieSeriesV ι S N c m‖ ≤
      if m % 2 = 1 ∧ 3 ≤ m then ‖c ((m - 3) / 2)‖ * ‖lieV ι S N ((m - 3) / 2)‖ else 0 := by
  unfold lieSeriesV
  split_ifs with h
  · rw [ContinuousMultilinearMap.norm_domDomCongr, norm_smul]
  · simp

variable {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ‖S‖ ≤ C)

include hC hι hS in
theorem hasFPowerSeriesOnBall_lieV (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : 2 * C * ρ ^ 2 ≤ 1 / 80) :
    HasFPowerSeriesOnBall (fun y : E => ∑' n : ℕ, c n • lieV ι S N n (fun _ => y))
      (lieSeriesV ι S N c) 0 (ENNReal.ofReal ρ) := by
  have hq0 : 0 ≤ 2 * C * ρ ^ 2 := by positivity
  refine ⟨?_, by simpa using hρ, ?_⟩
  · show ((ρ.toNNReal : NNReal) : ENNReal) ≤ _
    refine FormalMultilinearSeries.le_radius_of_bound _ (4 * ‖N‖ * ρ ^ 3) fun m => ?_
    have := norm_lieSeriesV_le ι S N c m
    rw [Real.coe_toNNReal ρ hρ.le]
    split_ifs at this with h
    · obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n + 3 := ⟨(m - 3) / 2, by omega⟩
      have e : (2 * n + 3 - 3) / 2 = n := by omega
      rw [e] at this
      have h2 := norm_lieV_le ι S N hC hι hS ρ hρ n
      have h10 : (10 * (2 * C * ρ ^ 2)) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      calc ‖lieSeriesV ι S N c (2 * n + 3)‖ * ρ ^ (2 * n + 3)
          ≤ (‖c n‖ * ‖lieV ι S N n‖) * ρ ^ (2 * n + 3) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ (1 * ‖lieV ι S N n‖) * ρ ^ (2 * n + 3) := by
            gcongr; exact hc n
        _ = (‖lieV ι S N n‖ * ρ ^ (2 * n)) * ρ ^ 3 := by rw [one_mul, pow_add]; ring
        _ ≤ (4 * ‖N‖ * (10 * (2 * C * ρ ^ 2)) ^ n) * ρ ^ 3 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ (4 * ‖N‖ * 1) * ρ ^ 3 := by gcongr
        _ = 4 * ‖N‖ * ρ ^ 3 := by ring
    · have : ‖lieSeriesV ι S N c m‖ ≤ 0 := this
      calc ‖lieSeriesV ι S N c m‖ * ρ ^ m ≤ 0 * ρ ^ m :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 0 := zero_mul _
        _ ≤ 4 * ‖N‖ * ρ ^ 3 := by positivity
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have h2 : ENNReal.ofReal ‖y‖ < ENNReal.ofReal ρ := by rwa [ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 h2
    have hs := summable_lieV ι S N hC hι hS ρ hρ hq 1 (by norm_num) y hy'.le
    have hs' : Summable fun n : ℕ => ‖c n • lieV ι S N n (fun _ => y)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
      rw [norm_smul, one_pow, one_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc n)
    rw [zero_add]
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 3) := fun a b h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff (f := fun m : ℕ => lieSeriesV ι S N c m fun _ => y)]
    · have e : ((fun m : ℕ => lieSeriesV ι S N c m fun _ => y) ∘ fun n : ℕ => 2 * n + 3) =
          fun n => c n • lieV ι S N n (fun _ => y) := by
        funext n
        simp only [Function.comp, lieSeriesV_const]
        rw [if_pos (by omega), show (2 * n + 3 - 3) / 2 = n by omega]
      rw [e]; exact hs'.of_norm.hasSum
    · intro m hm
      rw [lieSeriesV_const, if_neg]
      intro h
      exact hm ⟨(m - 3) / 2, by show 2 * ((m - 3) / 2) + 3 = m; omega⟩

include hC hι hS in
theorem analyticAt_lieV (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : 2 * C * ρ ^ 2 ≤ 1 / 80) (w : E) (hw : ‖w‖ < ρ) :
    AnalyticAt ℂ (fun y : E => ∑' n : ℕ, c n • lieV ι S N n (fun _ => y)) w := by
  refine (hasFPowerSeriesOnBall_lieV ι S N hC hι hS c hc ρ hρ hq).analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hw

end KAM.Wave

end
