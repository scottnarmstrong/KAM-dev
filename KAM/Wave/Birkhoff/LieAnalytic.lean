/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieMulti

/-!
# Analyticity of the flow `Γ_t` (blueprint-W `bpW:w3:flow` (i))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`lieSeries T t`: the formal multilinear series with coefficient `t^k Φ_k` in degree `2k+1`
(`Φ_k = lieMulti T k`) and `0` in even degrees. `lieGamma_hasFPowerSeriesOnBall`: it is a power
series of `w ↦ Γ_t(w)` on every ball `‖w‖ < ρ` with `2|t|Cρ² ≤ 1/10`; `analyticAt_lieGamma`:
`Γ_t` is analytic at every `w` with `|t| < 2`, `40 C ‖w‖² < 1`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

/-- The power series of `Γ_t`. -/
def lieSeries (t : ℝ) : FormalMultilinearSeries ℂ E E := fun n =>
  if h : n % 2 = 1 then
    ContinuousMultilinearMap.domDomCongr (finCongr (by omega : 2 * (n / 2) + 1 = n))
      (((t : ℂ) ^ (n / 2)) • lieMulti T (n / 2))
  else 0

theorem lieSeries_const (t : ℝ) (n : ℕ) (y : E) :
    lieSeries T t n (fun _ => y) =
      if n % 2 = 1 then ((t : ℂ) ^ (n / 2)) • lieSeq T y (n / 2) else 0 := by
  unfold lieSeries
  split_ifs with h
  · simp [ContinuousMultilinearMap.domDomCongr_apply, lieMulti_const]
  · simp

theorem norm_lieSeries_le {C : ℝ} (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) (t : ℝ) (n : ℕ) :
    ‖lieSeries T t n‖ ≤ if n % 2 = 1 then (2 * |t| * C) ^ (n / 2) else 0 := by
  unfold lieSeries
  split_ifs with h
  · rw [ContinuousMultilinearMap.norm_domDomCongr, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    have hm := birkLieM_le_pow (n / 2)
    have := norm_lieMulti_le T hC hT (n / 2)
    calc |t| ^ (n / 2) * ‖lieMulti T (n / 2)‖ ≤ |t| ^ (n / 2) * (2 ^ (n / 2) * C ^ (n / 2)) := by
          gcongr
          exact this.trans (by gcongr)
      _ = (2 * |t| * C) ^ (n / 2) := by rw [mul_pow, mul_pow]; ring
  · simp

variable [CompleteSpace E]

theorem lieGamma_hasFPowerSeriesOnBall {C : ℝ} (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) (t ρ : ℝ)
    (hρ : 0 < ρ) (hq : 2 * |t| * C * ρ ^ 2 ≤ 1 / 10) :
    HasFPowerSeriesOnBall (lieGamma T t) (lieSeries T t) 0 (ENNReal.ofReal ρ) := by
  have hT' : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖ := fun v =>
    (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (by positivity))
  have h0 : 0 ≤ 2 * |t| * C * ρ ^ 2 := by positivity
  refine ⟨?_, by simpa using hρ, ?_⟩
  · show ((ρ.toNNReal : NNReal) : ENNReal) ≤ _
    refine FormalMultilinearSeries.le_radius_of_bound _ ρ fun n => ?_
    have := norm_lieSeries_le T hC hT t n
    rw [Real.coe_toNNReal ρ hρ.le]
    split_ifs at this with h
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      have e : (2 * k + 1) / 2 = k := by omega
      rw [e] at this
      calc ‖lieSeries T t (2 * k + 1)‖ * ρ ^ (2 * k + 1) ≤ (2 * |t| * C) ^ k * ρ ^ (2 * k + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (2 * |t| * C * ρ ^ 2) ^ k * ρ := by
            rw [pow_succ, pow_mul, mul_pow]; ring
        _ ≤ 1 * ρ := by
            gcongr
            exact pow_le_one₀ h0 (by linarith)
        _ = ρ := one_mul ρ
    · have : ‖lieSeries T t n‖ ≤ 0 := this
      calc ‖lieSeries T t n‖ * ρ ^ n ≤ 0 * ρ ^ n := mul_le_mul_of_nonneg_right this (by positivity)
        _ = 0 := zero_mul _
        _ ≤ ρ := hρ.le
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have h2 : ENNReal.ofReal ‖y‖ < ENNReal.ofReal ρ := by rwa [ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 h2
    have hqy : 2 * |t| * C * ‖y‖ ^ 2 ≤ 1 / 10 := by
      have h1 : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy'.le 2
      have h2 : 0 ≤ 2 * |t| * C := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    have hs := (summable_lieTerm T hC hT' t y hqy).hasSum
    rw [zero_add]
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff (f := fun n : ℕ => lieSeries T t n fun _ => y)]
    · have e : ((fun n : ℕ => lieSeries T t n fun _ => y) ∘ fun k : ℕ => 2 * k + 1) =
          fun k => (t ^ k) • lieSeq T y k := by
        funext k
        simp only [Function.comp, lieSeries_const]
        rw [if_pos (by omega), show (2 * k + 1) / 2 = k by omega, ← Complex.coe_smul]
        push_cast; rfl
      rw [e]; exact hs
    · intro n hn
      rw [lieSeries_const, if_neg]
      intro h
      exact hn ⟨n / 2, by show 2 * (n / 2) + 1 = n; omega⟩

/-- (`bpW:w3:flow` (i), analyticity) `Γ_t` is analytic at every `w` with `|t| < 2` and
`40 C ‖w‖² < 1` (`‖w‖ < ρ₀`). -/
theorem analyticAt_lieGamma {C : ℝ} (hCp : 0 < C) (hT : ‖T‖ ≤ C) (t : ℝ) (w : E)
    (ht : |t| < 2) (hw : 40 * C * ‖w‖ ^ 2 < 1) : AnalyticAt ℂ (lieGamma T t) w := by
  have h40 : 0 < 40 * C := by positivity
  have hw' : ‖w‖ ^ 2 < 1 / (40 * C) := by rw [lt_div_iff₀ h40]; linarith
  set r2 : ℝ := (‖w‖ ^ 2 + 1 / (40 * C)) / 2 with hr2
  have hr2a : ‖w‖ ^ 2 < r2 := by rw [hr2]; linarith
  have hr2b : r2 < 1 / (40 * C) := by rw [hr2]; linarith
  have hr2p : 0 < r2 := lt_of_le_of_lt (sq_nonneg _) hr2a
  have hρ : 0 < Real.sqrt r2 := Real.sqrt_pos.2 hr2p
  have hρ2 : Real.sqrt r2 ^ 2 = r2 := Real.sq_sqrt hr2p.le
  have hwρ : ‖w‖ < Real.sqrt r2 :=
    Real.lt_sqrt (norm_nonneg w) |>.2 hr2a
  have hq : 2 * |t| * C * Real.sqrt r2 ^ 2 ≤ 1 / 10 := by
    rw [hρ2]
    have h1 : r2 * (40 * C) < 1 := by rwa [lt_div_iff₀ h40] at hr2b
    have h2 : 0 ≤ C * r2 := by positivity
    nlinarith [abs_nonneg t]
  have h := lieGamma_hasFPowerSeriesOnBall T hCp.le hT t (Real.sqrt r2) hρ hq
  refine h.analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hwρ

end KAM.Wave

end
