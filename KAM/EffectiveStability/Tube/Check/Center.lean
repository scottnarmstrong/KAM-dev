/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Center

/-!
# Range of the tube centre from the Lipschitz sums (T2-CONF, N5b)

For the tube centre `B_k(φ) = Ī_k + Σ_m (-m_k σ_m) cos(m₁ φ₀ + m₂ φ₁)` (N6's `tubeCenter`),

  `|B_k(φ) - Ī_k| ≤ Σ_m |m_k σ_m| ≤ Σ_m |m_k σ_m| (|m₁| + |m₂|) = lipSum₁ k + lipSum₂ k`,

since a mode with `m₁ = m₂ = 0` has `m_k = 0`, and otherwise `|m₁| + |m₂| ≥ 1`. So the bounds
`bmin ≤ B ≤ bmax` of the tube checker follow from N6's global check (`globalOK`: `lipSum_a ≤ L_a`)
with no further kernel computation (`tubeCenter_bounds_of_globalOK`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- One mode's amplitude is at most its Lipschitz weight: `|m_k σ| ≤ |m_k σ| (|m₁| + |m₂|)`. -/
theorem abs_modeK_mul_le (m₁ m₂ : ℤ) (σ : ℚ) (k : Fin 3) :
    |((modeK m₁ m₂ k : ℤ) : ℝ)| * |(σ : ℝ)| ≤
      |((modeK m₁ m₂ k : ℤ) : ℝ)| * |(σ : ℝ)| * (|(m₁ : ℝ)| + |(m₂ : ℝ)|) := by
  by_cases h : m₁ = 0 ∧ m₂ = 0
  · obtain ⟨rfl, rfl⟩ := h
    have : modeK 0 0 k = 0 := by fin_cases k <;> simp [modeK]
    simp [this]
  · have h1 : (1 : ℝ) ≤ |(m₁ : ℝ)| + |(m₂ : ℝ)| := by
      rcases not_and_or.1 h with h | h
      · have := Int.one_le_abs h
        have : (1 : ℝ) ≤ |(m₁ : ℝ)| := by exact_mod_cast this
        linarith [abs_nonneg (m₂ : ℝ)]
      · have := Int.one_le_abs h
        have : (1 : ℝ) ≤ |(m₂ : ℝ)| := by exact_mod_cast this
        linarith [abs_nonneg (m₁ : ℝ)]
    have h0 : 0 ≤ |((modeK m₁ m₂ k : ℤ) : ℝ)| * |(σ : ℝ)| := by positivity
    nlinarith

/-- **Range of the tube centre**: `|B_k(φ) - Ī_k| ≤ lipSum₁ k + lipSum₂ k`. -/
theorem abs_tubeCenter_sub_le (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (φ : Fin 2 → ℝ) :
    |tubeCenter modes Ibar k φ - Ibar k| ≤ ((lipSum₁ modes k + lipSum₂ modes k : ℚ) : ℝ) := by
  have hcast : ((lipSum₁ modes k + lipSum₂ modes k : ℚ) : ℝ) =
      (modes.map fun x => |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| *
        (|(x.1 : ℝ)| + |(x.2.1 : ℝ)|)).sum := by
    rw [lipSum₁, lipSum₂, treeSumQ_eq, treeSumQ_eq, Rat.cast_add, cast_list_sum_map,
      cast_list_sum_map, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    push_cast
    ring
  rw [hcast]
  have h := abs_list_sum_sub_le modes
    (fun x => -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * Real.cos (x.1 * φ 0 + x.2.1 * φ 1))
    (fun _ => 0)
    (fun x => |((modeK x.1 x.2.1 k : ℤ) : ℝ)| * |(x.2.2 : ℝ)| * (|(x.1 : ℝ)| + |(x.2.1 : ℝ)|))
    (fun x _ => by
      rw [sub_zero, abs_mul, abs_mul, abs_neg]
      refine le_trans ?_ (abs_modeK_mul_le x.1 x.2.1 x.2.2 k)
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
  simp only [List.map_const', List.sum_replicate, smul_zero, sub_zero] at h
  simpa [tubeCenter] using h

/-- **Bounds of the tube centre from N6's global check**:
`Ī_k - (L₁ k + L₂ k) ≤ B_k(φ) ≤ Ī_k + (L₁ k + L₂ k)`. -/
theorem tubeCenter_bounds_of_globalOK {d : EccData} (hg : globalOK d = true) (k : Fin 3)
    (φ : Fin 2 → ℝ) :
    ((d.Ibar k - (d.L₁ k + d.L₂ k) : ℚ) : ℝ) ≤ tubeCenter d.modes d.Ibar k φ ∧
      tubeCenter d.modes d.Ibar k φ ≤ ((d.Ibar k + (d.L₁ k + d.L₂ k) : ℚ) : ℝ) := by
  obtain ⟨-, -, hL⟩ := globalOK_spec hg
  obtain ⟨h1, h2, -⟩ := hL k
  have hle : ((lipSum₁ d.modes k + lipSum₂ d.modes k : ℚ) : ℝ) ≤ ((d.L₁ k + d.L₂ k : ℚ) : ℝ) := by
    exact_mod_cast add_le_add h1 h2
  have h := (abs_tubeCenter_sub_le d.modes d.Ibar k φ).trans hle
  rw [abs_le] at h
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

end KAM.EffectiveStability.Tube

end
