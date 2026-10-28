/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.LogBounds

/-!
# Fast averaging: the parameter arithmetic (P11A-P5, `stepP:p11:af-o2`)

With `K = 6/(πσ) · log (1/(ε M))`, `α = γ/2 · K^{-τ}`, `s₁ = min r_C (γ/(4 L K^{τ+1}))` and
`d = min (s₁ σ) r_z^2` (the signed `p11d1`), the smallness `(S1)`
`2^12 (1+n) K ε M σ ≤ α d` holds for all small `ε`: `K ≤ c₃ log (1/ε)`, `s₁ ≥ c₁ K^{-(τ+1)}`,
`α d ≥ c K^{-(2τ+1)}`, and `ε log (1/ε)^{3(τ+1)} → 0` by `e4`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- Lower bound for the right-hand side of (S1) in terms of `P = K^{τ+1} ≥ 1`. -/
theorem fast_rhs_lower {γ τ L rC σ rz K : ℝ} (hγ : 0 < γ) (hL : 1 ≤ L)
    (hrC : 0 < rC) (hσ : 0 < σ) (hrz : 0 < rz) (hK : 1 ≤ K) (hτ : 0 < τ) :
    γ * (min (min rC (γ / (4 * L)) * σ) (rz ^ 2)) / (2 * (K ^ (τ + 1)) ^ 2) ≤
      γ / 2 * K ^ (-τ) *
        (min (min rC (γ / (4 * L * K ^ (τ + 1))) * σ) (rz ^ 2)) := by
  set P : ℝ := K ^ (τ + 1) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hK (by linarith)
  have hP0 : 0 < P := by linarith
  set q : ℝ := 1 / P with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact div_le_one_of_le₀ hP1 hP0.le
  have hKτ : q ≤ K ^ (-τ) := by
    rw [Real.rpow_neg (by linarith), hq, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
  set c1 : ℝ := min rC (γ / (4 * L)) with hc1
  have hL0 : 0 < L := by linarith
  have hc10 : 0 < c1 := lt_min hrC (by positivity)
  set c2 : ℝ := min (c1 * σ) (rz ^ 2) with hc2
  have hc20 : 0 < c2 := lt_min (by positivity) (by positivity)
  have hs1 : c1 * q ≤ min rC (γ / (4 * L * P)) := by
    refine le_min ?_ ?_
    · calc c1 * q ≤ rC * 1 := mul_le_mul (min_le_left _ _) hq1 hq0.le hrC.le
        _ = rC := mul_one _
    · calc c1 * q ≤ γ / (4 * L) * q := mul_le_mul_of_nonneg_right (min_le_right _ _) hq0.le
        _ = γ / (4 * L * P) := by rw [hq]; field_simp
  have hd : c2 * q ≤ min (min rC (γ / (4 * L * P)) * σ) (rz ^ 2) := by
    refine le_min ?_ ?_
    · calc c2 * q ≤ (c1 * σ) * q := mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le
        _ = (c1 * q) * σ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hs1 hσ.le
    · calc c2 * q ≤ rz ^ 2 * 1 := mul_le_mul (min_le_right _ _) hq1 hq0.le (by positivity)
        _ = rz ^ 2 := mul_one _
  calc γ * c2 / (2 * P ^ 2) = γ / 2 * q * (c2 * q) := by rw [hq]; field_simp
    _ ≤ γ / 2 * K ^ (-τ) * (min (min rC (γ / (4 * L * P)) * σ) (rz ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hKτ (by positivity)) hd (by positivity)
          (by positivity)

/-- `d₁ ≥ c K^{-(τ+1)}`: the source `d₁ = min (s₁ σ) r_z²` decays like `K^{-(τ+1)}`. -/
theorem fast_d_lower {γ τ L rC σ rz K : ℝ} (hγ : 0 < γ) (hL : 1 ≤ L)
    (hrC : 0 < rC) (hσ : 0 < σ) (hrz : 0 < rz) (hK : 1 ≤ K) (hτ : 0 < τ) :
    min (min rC (γ / (4 * L)) * σ) (rz ^ 2) / K ^ (τ + 1) ≤
      min (min rC (γ / (4 * L * K ^ (τ + 1))) * σ) (rz ^ 2) := by
  set P : ℝ := K ^ (τ + 1) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hK (by linarith)
  have hP0 : 0 < P := by linarith
  have hq0 : 0 < 1 / P := by positivity
  have hq1 : 1 / P ≤ 1 := div_le_one_of_le₀ hP1 hP0.le
  have hL0 : 0 < L := by linarith
  set c1 : ℝ := min rC (γ / (4 * L)) with hc1
  have hs1 : c1 * (1 / P) ≤ min rC (γ / (4 * L * P)) := by
    refine le_min ?_ ?_
    · calc c1 * (1 / P) ≤ rC * 1 := mul_le_mul (min_le_left _ _) hq1 hq0.le hrC.le
        _ = rC := mul_one _
    · calc c1 * (1 / P) ≤ γ / (4 * L) * (1 / P) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hq0.le
        _ = γ / (4 * L * P) := by field_simp
  have e : min (c1 * σ) (rz ^ 2) / P = min (c1 * σ) (rz ^ 2) * (1 / P) := by ring
  rw [e]
  refine le_min ?_ ?_
  · calc min (c1 * σ) (rz ^ 2) * (1 / P) ≤ (c1 * σ) * (1 / P) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le
      _ = (c1 * (1 / P)) * σ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs1 hσ.le
  · calc min (c1 * σ) (rz ^ 2) * (1 / P) ≤ rz ^ 2 * 1 :=
        mul_le_mul (min_le_right _ _) hq1 hq0.le (by positivity)
      _ = rz ^ 2 := mul_one _

/-- `stepP:p11:af-o2`: (S1) and `ε M ≤ e⁻¹` hold for all small `ε`. -/
theorem fast_small_eventually {n : ℕ} {γ τ L rC σ rz M : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hL : 1 ≤ L) (hrC : 0 < rC) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 4) (hrz : 0 < rz) (hM : 1 ≤ M) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε1 →
      ε * M ≤ Real.exp (-1) ∧
      ∀ K : ℝ, K = 6 / (Real.pi * σ) * Real.log (1 / (ε * M)) →
        2 ^ 12 * (1 + (n : ℝ)) * K * ε * M * σ ≤
          γ / 2 * K ^ (-τ) *
            (min (min rC (γ / (4 * L * K ^ (τ + 1))) * σ) (rz ^ 2)) := by
  have hM0 : 0 < M := by linarith
  set c3 : ℝ := 6 / (Real.pi * σ) with hc3
  have hc30 : 0 < c3 := by positivity
  have hc31 : 1 ≤ c3 := by
    rw [hc3, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  set b : ℝ := 3 * (τ + 1) with hb
  have hb0 : 0 ≤ b := by positivity
  set c2 : ℝ := min (min rC (γ / (4 * L)) * σ) (rz ^ 2) with hc2
  have hL0 : 0 < L := by linarith
  have hc20 : 0 < c2 :=
    lt_min (mul_pos (lt_min hrC (by positivity)) hσ) (by positivity)
  set η : ℝ := γ * c2 / 2 / (2 ^ 12 * (1 + (n : ℝ)) * σ * M * c3 ^ b) with hη
  have hη0 : 0 < η := by positivity
  have hev := (e4 (a := 1) (b := b) one_pos hb0).eventually (Iic_mem_nhds hη0)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hu0 : 0 < u := hu
  refine ⟨min (u / 2) (min (Real.exp (-1) / M) (1 / 2)), lt_min (by linarith)
    (lt_min (by positivity) (by norm_num)), lt_of_le_of_lt (min_le_of_right_le (min_le_right _ _))
    (by norm_num), fun ε hε hεle => ?_⟩
  have hε1 : ε ≤ u / 2 := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ Real.exp (-1) / M :=
    hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε * M ≤ Real.exp (-1) := by rwa [le_div_iff₀ hM0] at hε2
  refine ⟨hεM, fun K hK => ?_⟩
  have hεM0 : 0 < ε * M := by positivity
  have hℓ1 : 1 ≤ Real.log (1 / (ε * M)) := log_inv_ge_one hεM0 hεM
  have hℓΛ : Real.log (1 / (ε * M)) ≤ Real.log (1 / ε) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hε.ne' hM0.ne']
    have := Real.log_nonneg hM
    linarith
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have hKΛ : K ≤ c3 * Real.log (1 / ε) := by
    rw [hK]; exact mul_le_mul_of_nonneg_left hℓΛ hc30.le
  have hKP : K ≤ K ^ (τ + 1) := by
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ (τ + 1) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hP1 : 1 ≤ K ^ (τ + 1) := Real.one_le_rpow hK1 (by linarith)
  have hlow := fast_rhs_lower (K := K) hγ hL hrC hσ hrz hK1 hτ
  refine le_trans ?_ hlow
  have hev1 : ε ^ (1 : ℝ) * Real.log (1 / ε) ^ b ≤ η := hsub ⟨hε, by linarith⟩
  rw [Real.rpow_one] at hev1
  have hΛ0 : 0 ≤ Real.log (1 / ε) := le_trans zero_le_one (hℓ1.trans hℓΛ)
  have hKb : K ^ b ≤ (c3 * Real.log (1 / ε)) ^ b := Real.rpow_le_rpow (by linarith) hKΛ hb0
  have hPb : (K ^ (τ + 1)) ^ 3 = K ^ b := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf
  have hKP3 : K * (K ^ (τ + 1)) ^ 2 ≤ K ^ b := by
    rw [← hPb]
    calc K * (K ^ (τ + 1)) ^ 2 ≤ K ^ (τ + 1) * (K ^ (τ + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right hKP (by positivity)
      _ = _ := by ring
  have hcb : (c3 * Real.log (1 / ε)) ^ b = c3 ^ b * Real.log (1 / ε) ^ b :=
    Real.mul_rpow hc30.le hΛ0
  have hηe : 2 ^ 12 * (1 + (n : ℝ)) * σ * M * c3 ^ b * η = γ * c2 / 2 := by
    rw [hη]; field_simp
  have hP0 : 0 < K ^ (τ + 1) := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hA : 0 ≤ 2 ^ 12 * (1 + (n : ℝ)) * σ * M * ε := by positivity
  calc 2 ^ 12 * (1 + (n : ℝ)) * K * ε * M * σ * (2 * (K ^ (τ + 1)) ^ 2)
      = 2 * (2 ^ 12 * (1 + (n : ℝ)) * σ * M * ε) * (K * (K ^ (τ + 1)) ^ 2) := by ring
    _ ≤ 2 * (2 ^ 12 * (1 + (n : ℝ)) * σ * M * ε) * (c3 ^ b * Real.log (1 / ε) ^ b) := by
        rw [← hcb]
        exact mul_le_mul_of_nonneg_left (hKP3.trans hKb) (by positivity)
    _ = 2 * (2 ^ 12 * (1 + (n : ℝ)) * σ * M * c3 ^ b) * (ε * Real.log (1 / ε) ^ b) := by ring
    _ ≤ 2 * (2 ^ 12 * (1 + (n : ℝ)) * σ * M * c3 ^ b) * η :=
        mul_le_mul_of_nonneg_left hev1 (by positivity)
    _ = γ * c2 := by rw [mul_assoc, hηe]; ring

end KAM.Planetary

end
