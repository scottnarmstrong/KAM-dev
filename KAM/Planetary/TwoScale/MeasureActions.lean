/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Cover
public import KAM.Planetary.TwoScale.Constants
public import KAM.Planetary.Averaging.Setting
public import KAM.Measure.Lipschitz

/-!
# Two-scale KAM: the private conditional helper `meas_actions_of_limit` (`bpP:p3:meas-actions`)

Packages `stepP:p3:ma-ext` and `stepP:p3:ma-meas`. `ActionsMeas` bundles the proved outputs of
`limit_actions_of_steps` on the shared witnesses (`D₀ = Ds 0`, `i` the limit action map); the
helper is conditional on it and is discharged by the applicability theorem
`meas_of_iterative` (design finding N2, package P23-21). Closed shells are the existential
distances `∃ J ∈ D₀, ‖x - J‖ ≤ ρ`, contained in the open real tube `realTube D r` as `ρ < r`.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

/-- Membership in the real tube through an existential distance. -/
theorem mem_realTube_of {n : ℕ} {D : Set (Fin n → ℝ)} {r : ℝ} {x J : Fin n → ℝ}
    (hJ : J ∈ D) (hx : ‖x - J‖ < r) : x ∈ realTube D r := by
  refine ⟨J, hJ, ?_⟩
  have e : (fun k => ((J k : ℝ) : ℂ)) = KAM.realInclusion n J := rfl
  rw [e, ← map_sub, KAM.norm_realInclusion]
  exact hx

/-- The proved outputs of `limit_actions_of_steps` used by the measure estimates: `D₀ ⊆ D`, the
displacement `20 Ê ρ̂`, the defect Lipschitz constant `2560 n Ê < 1/3`. -/
structure ActionsMeas {n : ℕ} (D D₀ : Set (Fin n → ℝ)) (i : (Fin n → ℝ) → (Fin n → ℝ))
    (Ehat Rhat : ℝ) : Prop where
  sub : D₀ ⊆ D
  E_nonneg : 0 ≤ Ehat
  pos : 0 < Ehat * Rhat
  bd : ∀ I ∈ D₀, ‖i I - I‖ ≤ 20 * Ehat * Rhat
  lip : ∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (n : ℝ) * Ehat * ‖I - J‖
  small : 2560 * (n : ℝ) * Ehat < 1 / 3

variable {n : ℕ} {D D₀ : Set (Fin n → ℝ)} {i : (Fin n → ℝ) → (Fin n → ℝ)} {Ehat Rhat : ℝ}


/-- **`bpP:p3:meas-actions`** (private conditional helper). `meas(D₀ ∖ ǐ(D₀)) ≤ (4/3)ⁿ (a + b)` and
`meas(D ∖ ǐ(D₀)) ≤ a + (4/3)ⁿ (a + b)`, with `a = meas(D ∖ D₀)`,
`b = meas(realTube D r ∖ D)`, `r = 32 Ê ρ̂`. -/
theorem meas_actions_of_limit (A : ActionsMeas D D₀ i Ehat Rhat) :
    volume (D₀ \ i '' D₀) ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) ∧
      volume (D \ i '' D₀) ≤ volume (D \ D₀) + ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) := by
  have hl0 : 0 ≤ 2560 * (n : ℝ) * Ehat := by have := A.E_nonneg; positivity
  have hl1 := A.small
  set lam := 2560 * (n : ℝ) * Ehat with hlam
  have hpos := A.pos
  -- `ma-ext`: the cover `F = ǐ_e`
  obtain ⟨F, hFX, hFbi, hFloc⟩ := cover (N := n) (X := D₀) (g := fun I => i I - I)
    (lam := lam) (η := 20 * Ehat * Rhat) ⟨hl0, by linarith⟩ (by linarith)
    A.lip (fun I hI => A.bd I hI)
  have hρ : 20 * Ehat * Rhat / (1 - lam) < 32 * Ehat * Rhat := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hFx : ∀ x ∈ D₀, F x = i x := fun x hx => by rw [hFX x hx]; abel
  have hsub : D₀ \ i '' D₀ ⊆ F '' (realTube D (32 * Ehat * Rhat) \ D₀) := by
    intro y hy
    refine ⟨F.symm y, ⟨?_, ?_⟩, F.apply_symm_apply y⟩
    · exact mem_realTube_of (A.sub hy.1) ((hFloc y hy.1).trans_lt hρ)
    · intro hx
      exact hy.2 ⟨F.symm y, hx, by rw [← hFx _ hx, F.apply_symm_apply]⟩
  -- `ma-meas`
  have hlip : ∀ x ∈ realTube D (32 * Ehat * Rhat) \ D₀, ∀ y ∈ realTube D (32 * Ehat * Rhat) \ D₀,
      ‖F x - F y‖ ≤ (1 + lam) * ‖x - y‖ := fun x _ y _ => (hFbi x y).2
  have himg := KAM.lip_image (d := n) (F := F) hlip
  have hq : ENNReal.ofReal ((1 + lam) ^ n) ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ n) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) (by linarith) n)
  have hsplit : realTube D (32 * Ehat * Rhat) \ D₀ ⊆
      (realTube D (32 * Ehat * Rhat) \ D) ∪ (D \ D₀) := by
    intro x hx
    by_cases hD : x ∈ D
    · exact Or.inr ⟨hD, hx.2⟩
    · exact Or.inl ⟨hx.1, hD⟩
  have h1 : volume (D₀ \ i '' D₀) ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
      (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) := by
    calc volume (D₀ \ i '' D₀) ≤ volume (F '' (realTube D (32 * Ehat * Rhat) \ D₀)) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal ((1 + lam) ^ n) * volume (realTube D (32 * Ehat * Rhat) \ D₀) := himg
      _ ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
          (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) := by
          refine mul_le_mul' hq ((measure_mono hsplit).trans ?_)
          rw [add_comm]
          exact measure_union_le _ _
  refine ⟨h1, ?_⟩
  have hDs : D \ i '' D₀ ⊆ (D \ D₀) ∪ (D₀ \ i '' D₀) := by
    intro x hx
    by_cases h : x ∈ D₀
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  exact (measure_mono hDs).trans ((measure_union_le _ _).trans (by gcongr))

end KAM.Planetary

end
