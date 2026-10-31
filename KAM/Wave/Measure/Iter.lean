/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.IterMinus
public import KAM.Wave.Measure.Prep

/-!
# W7: the iteration zones (blueprint `bpW:w7:iter`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`volume ℰ_it ≤ ρ_ζ D_A⁻¹ (Z₃ (8 + 32ϑ⁻³ + 16 (2 + a_κ) ϑ⁻²) α̌^{2/3} + 32 Z₃ ϑ⁻¹ (ε₁ + ε₂) + 4 N_X K_*² ϑ⁻¹ σ_X⁻¹ α̌)`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

theorem zoneSet_neg (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ → ℝ) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) :
    zoneSet D ω Ω a k (-l) = zoneSet D ω Ω a (-k) l := by
  ext ξ
  simp only [zoneSet, Set.mem_ofPred_eq, japL_neg, kAk_neg, linF_neg]
  have : ∑ i, (((-k) i : ℤ) : ℝ) * ω ξ i = -∑ i, (k i : ℝ) * ω ξ i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [this, ← abs_neg]
  have : -(∑ i, (k i : ℝ) * ω ξ i + -linF l (Ω ξ)) =
      -∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ) := by ring
  rw [this]

/-- The per-`k` real bound of the iteration zones. -/
theorem iter_perk_real {a ρ DA ϑ aκ ε : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hρ : 0 ≤ ρ)
    (hDA : 0 < DA) (hϑ : 0 < ϑ) (hκ : 0 < aκ) (hε : 0 ≤ ε) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA) +
      32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) +
      2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) * (kAbs k / ϑ) ^ 2 +
        (16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) ≤
      (ρ / DA * (a ^ (2 / 3 : ℝ) * (8 + 32 * (ϑ⁻¹) ^ 3 + 16 * (2 + aκ) * (ϑ⁻¹) ^ 2) +
        32 * ϑ⁻¹ * ε)) / kAbs k ^ 3 := by
  have hk1 := one_le_kAbs hk
  have hkpos : 0 < kAbs k := by linarith
  have hA := kAk_pos k
  have hApos : 0 < kAk k := by linarith
  have ha8 : a ≤ a ^ (2 / 3 : ℝ) := by
    calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by norm_num)
  have ha8pos : 0 < a ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have p3 := pow_le_kAk_rpow hk (e := 3) (s := 1) (by norm_num) (by norm_num)
  have p6 := pow_le_kAk_rpow hk (e := 6) (s := 1) (by norm_num) (by norm_num)
  have p5 := pow_le_kAk_rpow hk (e := 5) (s := 2 / 3) (by norm_num) (by norm_num)
  have p4 := pow_le_kAk_rpow hk (e := 4) (s := 1 / 6) (by norm_num) (by norm_num)
  rw [Real.rpow_one] at p3 p6
  have hA23 : 0 < kAk k ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hA16 : 0 < kAk k ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hdiv : (a / kAk k) ^ (2 / 3 : ℝ) = a ^ (2 / 3 : ℝ) / kAk k ^ (2 / 3 : ℝ) :=
    Real.div_rpow ha0.le hApos.le _
  have hneg : kAk k ^ (-(1 / 6 : ℝ)) = (kAk k ^ (1 / 6 : ℝ))⁻¹ := Real.rpow_neg hApos.le _
  have hk3 : 0 < kAbs k ^ 3 := by positivity
  set u3 : ℝ := (kAbs k ^ 3)⁻¹ with hu3
  have hu3pos : 0 < u3 := by positivity
  have hu3e : ∀ x : ℝ, x / kAbs k ^ 3 = x * u3 := fun x => by rw [hu3, div_eq_mul_inv]
  have f0 : (kAk k)⁻¹ ≤ u3 := inv_anti₀ hk3 p3
  have f1 : kAbs k ^ 3 / kAk k ≤ u3 := by
    rw [div_le_iff₀ hApos]
    calc kAbs k ^ 3 = u3 * kAbs k ^ 6 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k := mul_le_mul_of_nonneg_left p6 hu3pos.le
  have f2 : kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ) ≤ u3 := by
    rw [div_le_iff₀ hA23]
    calc kAbs k ^ 2 = u3 * kAbs k ^ 5 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left p5 hu3pos.le
  have f3 : kAbs k / kAk k ^ (1 / 6 : ℝ) ≤ u3 := by
    rw [div_le_iff₀ hA16]
    calc kAbs k = u3 * kAbs k ^ 4 := by rw [hu3]; field_simp
      _ ≤ u3 * kAk k ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left p4 hu3pos.le
  have e0 : kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA)) = (8 * a * ρ / DA) * (kAk k)⁻¹ := by
    field_simp
  have e1 : kAbs k * (32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA)) =
      (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 3 / kAk k) := by field_simp
  have e2 : kAbs k * (2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) *
      (kAbs k / ϑ) ^ 2)) = (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) *
      (kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ)) := by
    rw [hdiv]; field_simp; ring
  have e3 : kAbs k * (2 * ((16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) *
      (kAbs k / ϑ))) = (32 * ρ * ε / (ϑ * DA)) * (kAbs k / kAk k ^ (1 / 6 : ℝ)) := by
    rw [hneg]; field_simp; ring
  have hsplit : kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA) +
      32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA) +
      2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) * (kAbs k / ϑ) ^ 2 +
        (16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) =
      kAbs k * (8 * (a / kAk k) * ρ / (kAbs k * DA)) +
      kAbs k * (32 * a * ρ * kAbs k ^ 2 / (ϑ ^ 3 * kAk k * DA)) +
      kAbs k * (2 * ((8 * ρ * (2 + aκ) * (a / kAk k) ^ (2 / 3 : ℝ) / (kAbs k * DA)) *
        (kAbs k / ϑ) ^ 2)) +
      kAbs k * (2 * ((16 * ρ * ε * kAk k ^ (-(1 / 6 : ℝ)) / (kAbs k * DA)) * (kAbs k / ϑ))) := by
    ring
  rw [hsplit, e0, e1, e2, e3, hu3e]
  have c1 : 0 ≤ 8 * a * ρ / DA := by positivity
  have c2 : 0 ≤ 32 * a * ρ / (ϑ ^ 3 * DA) := by positivity
  have c3 : 0 ≤ 16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA) := by positivity
  have c4 : 0 ≤ 32 * ρ * ε / (ϑ * DA) := by positivity
  calc (8 * a * ρ / DA) * (kAk k)⁻¹ + (32 * a * ρ / (ϑ ^ 3 * DA)) * (kAbs k ^ 3 / kAk k) +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) *
          (kAbs k ^ 2 / kAk k ^ (2 / 3 : ℝ)) +
        (32 * ρ * ε / (ϑ * DA)) * (kAbs k / kAk k ^ (1 / 6 : ℝ))
      ≤ (8 * a * ρ / DA) * u3 + (32 * a * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) * u3 +
        (32 * ρ * ε / (ϑ * DA)) * u3 := by gcongr
    _ ≤ (8 * a ^ (2 / 3 : ℝ) * ρ / DA) * u3 + (32 * a ^ (2 / 3 : ℝ) * ρ / (ϑ ^ 3 * DA)) * u3 +
        (16 * ρ * (2 + aκ) * a ^ (2 / 3 : ℝ) / (ϑ ^ 2 * DA)) * u3 +
        (32 * ρ * ε / (ϑ * DA)) * u3 := by gcongr
    _ = _ := by field_simp

end KAM.Wave

end
