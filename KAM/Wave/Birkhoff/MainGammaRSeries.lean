/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainBallReal

/-!
# The real power series of `Γ^ℝ` (blueprint-W `bpW:w3:gamma-real` (i))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-MAIN, blueprint label `bpW:w3:gamma-real` (i).

`birkGammaRSeries`: the real formal series on `E = E_{a,p}` whose `n`-th term is
`Π ∘ q_n(𝒵·, …, 𝒵·)` for the complex series `q = lieSeries T 1` of `Γ = Γ_1`; its `(2k+1)`-st term
is `Π Φ_k(𝒵·, …, 𝒵·)` (`birkGammaRSeries_odd`, `Φ_k = lieMulti T k`) and its even terms vanish
(`birkGammaRSeries_even`); here `Π = Re 𝒵⁻¹` (`= 𝒵⁻¹` on real points).
`hasFPowerSeriesOnBall_birkGammaR`: `Γ^ℝ` has this power series on `B^E_{r₁}`
(`r₁ = ρ₁/√2 = birkRealRho1`, `birkRealBall1_eq_ball`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- (`bpW:w3:gamma-real` (i)) The real power series of `Γ^ℝ`: `n`-th term
`Π q_n(𝒵·, …, 𝒵·)`, `q = lieSeries T 1` the series of `Γ`. -/
def birkGammaRSeries : FormalMultilinearSeries ℝ BirkReal BirkReal :=
  birkPi.compFormalMultilinearSeries
    (((lieSeries (birkT m hm ha hp) 1).restrictScalars ℝ).compContinuousLinearMap birkZR)

/-- `r₁ = ρ₁ / √2`. -/
def birkRealRho1 (m p : ℝ) : ℝ := birkRho1 m p / Real.sqrt 2

variable {m hm ha hp}

theorem birkGammaRSeries_apply (n : ℕ) (v : Fin n → BirkReal) :
    birkGammaRSeries m hm ha hp n v =
      birkPi (lieSeries (birkT m hm ha hp) 1 n (fun i => birkZR (v i))) := rfl

/-- (`bpW:w3:gamma-real` (i)) The `(2k+1)`-st term is `Π Φ_k(𝒵·, …, 𝒵·)`. -/
theorem birkGammaRSeries_odd (k : ℕ) (v : Fin (2 * k + 1) → BirkReal) :
    birkGammaRSeries m hm ha hp (2 * k + 1) v =
      birkPi (lieMulti (birkT m hm ha hp) k (fun i => birkZR (v i))) := by
  rw [birkGammaRSeries_apply]
  congr 1
  have key : ∀ j (hj : j = k) (h : 2 * j + 1 = 2 * k + 1) (u : Fin (2 * k + 1) → BirkSpace),
      ContinuousMultilinearMap.domDomCongr (finCongr h)
          ((((1 : ℝ) : ℂ) ^ j) • lieMulti (birkT m hm ha hp) j) u =
        lieMulti (birkT m hm ha hp) k u := by
    rintro j rfl h u
    simp
  unfold lieSeries
  split_ifs with h
  · exact key _ (by omega) _ _
  · exact absurd (by omega) h

/-- (`bpW:w3:gamma-real` (i)) The even terms vanish. -/
theorem birkGammaRSeries_even (k : ℕ) : birkGammaRSeries m hm ha hp (2 * k) = 0 := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [birkGammaRSeries_apply]
  unfold lieSeries
  split_ifs with h
  · exact absurd h (by omega)
  · simp

include hm hp in
theorem birkRealRho1_pos : 0 < birkRealRho1 m p :=
  div_pos (birkRho1_pos (hm := hm) (hp := hp)) (Real.sqrt_pos.2 (by norm_num))

include hm hp in
/-- `B^E_{r₁} = {320 C_F ‖x‖² < 1}` is the open ball of radius `r₁ = ρ₁/√2`. -/
theorem birkRealBall1_eq_ball : birkRealBall1 m p = Metric.ball 0 (birkRealRho1 m p) := by
  have hC := birkCF_pos m hm hp
  have hr := birkRealRho1_pos (hm := hm) (hp := hp)
  have hsq : birkRealRho1 m p ^ 2 = 1 / (320 * birkCF m p) := by
    unfold birkRealRho1
    rw [div_pow, birkRho1_sq (hm := hm) (hp := hp), Real.sq_sqrt (by norm_num)]
    field_simp
    ring
  ext x
  rw [mem_ball_zero_iff]
  show 320 * birkCF m p * ‖x‖ ^ 2 < 1 ↔ _
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg x) hr.le two_ne_zero, hsq, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

include hm hp in
/-- (`bpW:w3:gamma-real` (i)) `Γ^ℝ` has on `B^E_{r₁}` the real power series `birkGammaRSeries`:
every map `g` agreeing with `Γ^ℝ` on `B^E_{r₁}` satisfies `HasFPowerSeriesOnBall g q^ℝ 0 r₁`. -/
theorem hasFPowerSeriesOnBall_birkGammaR (g : BirkReal → BirkReal)
    (hg : IsBirkExtension (birkGammaR m hm ha hp) g) :
    HasFPowerSeriesOnBall g (birkGammaRSeries m hm ha hp) 0
      (ENNReal.ofReal (birkRealRho1 m p)) := by
  have hC := birkCF_pos m hm hp
  have hρ := birkRho1_pos (hm := hm) (hp := hp)
  have hq : 2 * |(1 : ℝ)| * birkCF m p * birkRho1 m p ^ 2 ≤ 1 / 10 := by
    rw [abs_one, mul_one, birkRho1_q (hm := hm) (hp := hp)]; norm_num
  have h1 := lieGamma_hasFPowerSeriesOnBall (birkT m hm ha hp) hC.le
    (norm_birkT_le_cf (hm := hm) (hp := hp) (ha := ha)) 1 (birkRho1 m p) hρ hq
  have h2 : HasFPowerSeriesOnBall (lieGamma (birkT m hm ha hp) 1)
      ((lieSeries (birkT m hm ha hp) 1).restrictScalars ℝ) (birkZR 0)
      (ENNReal.ofReal (birkRho1 m p)) := by
    rw [map_zero]; exact h1.restrictScalars
  have h4 := birkPi.comp_hasFPowerSeriesOnBall h2.compContinuousLinearMap
  have hZ : ‖birkZR‖ ≤ Real.sqrt 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) norm_birkZR_le
  have hle : ENNReal.ofReal (birkRealRho1 m p) ≤ ENNReal.ofReal (birkRho1 m p) / ‖birkZR‖ₑ := by
    unfold birkRealRho1
    rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by norm_num))]
    refine ENNReal.div_le_div_left ?_ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hZ
  refine (h4.mono (ENNReal.ofReal_pos.2 (birkRealRho1_pos (hm := hm) (hp := hp))) hle).congr ?_
  intro x hx
  have hx' : x ∈ birkRealBall1 m p := by
    rw [birkRealBall1_eq_ball (hm := hm) (hp := hp), mem_ball_zero_iff]
    rw [Metric.mem_eball, edist_zero_right] at hx
    have h5 : ENNReal.ofReal ‖x‖ < ENNReal.ofReal (birkRealRho1 m p) := by rwa [ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff (birkRealRho1_pos (hm := hm) (hp := hp))).1 h5
  exact (hg ⟨x, hx'⟩).symm

end KAM.Wave

end
