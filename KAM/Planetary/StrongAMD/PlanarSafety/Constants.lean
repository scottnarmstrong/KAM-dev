/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain
public import KAM.Planetary.StrongAMD.Modulus
public import KAM.Planetary.StrongAMD.Momentum
public import KAM.Planetary.StrongAMD.Orbital

/-!
# Constants and elementary estimates of the planar assembly

Package LP-PS (planar theorem LP1, `LP:MAIN L14 (468–500)`, `L15`), track LP, non-frozen.

* `exists_budget_radius`: the budget `n r + Ω_B(r) ≤ δ/4` of MAIN (39) for every small `r`.
* `norm_axis_sub_le`: the action-to-axis estimate (MAIN line 497).
* `mem_strongLSet_actionVector`: axes in `A` put the initial actions in `𝓛`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Filter Topology

variable {n : ℕ}

/-- (MAIN (39), N6) There is a radius below which the budget `n r + Ω_B(r) ≤ δ/4` holds. -/
theorem exists_budget_radius {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r1 : ℝ, 0 < r1 ∧ ∀ r : ℝ, 0 < r → r ≤ r1 →
      (n : ℝ) * r + strongThresholdModulus ν U r ≤ δ / 4 := by
  have ht := tendsto_strongThresholdModulus hν hn hUc hUch
  rw [Metric.tendsto_nhdsWithin_nhds] at ht
  obtain ⟨η, hη, hη'⟩ := ht (δ / 8) (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨min (η / 2) (δ / (8 * n)), by positivity, fun r hr hrle => ?_⟩
  have h1 : r ≤ η / 2 := hrle.trans (min_le_left _ _)
  have h2 : r ≤ δ / (8 * n) := hrle.trans (min_le_right _ _)
  have h3 := hη' (x := r) hr (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; linarith)
  rw [Real.dist_eq, sub_zero, abs_lt] at h3
  have h4 : (n : ℝ) * r ≤ δ / 8 := by
    have := mul_le_mul_of_nonneg_left h2 hn0.le
    calc (n : ℝ) * r ≤ n * (δ / (8 * n)) := this
      _ = δ / 8 := by field_simp
  linarith [h3.2]

/-- Physical states satisfy `a_i = Λ_i² / ν_i²`. -/
theorem keplerAxis_eq_action_sq {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {z : Phase (n * 2)}
    (hz : ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) (i : Fin n) :
    keplerAxis ν z i = keplerAction ν z i ^ 2 / ν i ^ 2 := by
  obtain ⟨-, -, h3, -⟩ := orbital_identities (z := z) i ⟨hν i, hz i⟩
  have := hν i
  rw [h3]; field_simp

/-- The action-to-axis estimate (MAIN line 497): `|a_i - a_i⁰| ≤ |Λ_i - Λ_i⁰| (|Λ_i| + |Λ_i⁰|)/ν_i²`. -/
theorem norm_axis_sub_le {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {C ρ : ℝ} (hC0 : 0 ≤ C) {z z' : Phase (n * 2)}
    (hz : ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    (hz' : ∀ i, 0 < planeLength (bodyVector z'.1 i) ∧ keplerEnergy ν z' i < 0)
    (hC : ∀ i, |keplerAction ν z i| ≤ C) (hC' : ∀ i, |keplerAction ν z' i| ≤ C)
    (hρ : ‖(fun i => keplerAction ν z i) - fun i => keplerAction ν z' i‖ ≤ ρ) :
    ‖(fun i => keplerAxis ν z i) - fun i => keplerAxis ν z' i‖ ≤
      ρ * (2 * C) * ∑ k, 1 / ν k ^ 2 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hS : 0 ≤ ∑ k, 1 / ν k ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hi := hν i
  have h1 : |keplerAction ν z i - keplerAction ν z' i| ≤ ρ := by
    have := norm_le_pi_norm ((fun i => keplerAction ν z i) - fun i => keplerAction ν z' i) i
    simpa using this.trans hρ
  have h2 : |keplerAction ν z i + keplerAction ν z' i| ≤ 2 * C :=
    (abs_add_le _ _).trans (by linarith [hC i, hC' i])
  have h3 : keplerAxis ν z i - keplerAxis ν z' i =
      (keplerAction ν z i - keplerAction ν z' i) * (keplerAction ν z i + keplerAction ν z' i) /
        ν i ^ 2 := by
    rw [keplerAxis_eq_action_sq hν hz, keplerAxis_eq_action_sq hν hz']; ring
  have h4 : 1 / ν i ^ 2 ≤ ∑ k, 1 / ν k ^ 2 :=
    Finset.single_le_sum (f := fun k => 1 / ν k ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ i)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [h3, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ν i ^ 2), div_eq_mul_one_div]
  calc _ ≤ (ρ * (2 * C)) * (1 / ν i ^ 2) := by
        apply mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hρ0) le_rfl (by positivity)
          (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- Axes in `A` put the initial actions in `𝓛 = strongLSet ν A` (physical states). -/
theorem mem_strongLSet_actionVector {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {A : Set (Fin n → ℝ)}
    {z : Phase (n * 2)} (hz : ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    (hA : (fun i => keplerAxis ν z i) ∈ A) : actionVector ν z ∈ strongLSet ν A := by
  refine ⟨fun i => keplerAxis ν z i, hA, funext fun i => ?_⟩
  obtain ⟨ha, hΛ, h3, -⟩ := orbital_identities (z := z) i ⟨hν i, hz i⟩
  have hνi := hν i
  show ν i * Real.sqrt (keplerAxis ν z i) = keplerAction ν z i
  have h : (ν i * Real.sqrt (keplerAxis ν z i)) ^ 2 = keplerAction ν z i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha.le, h3]
  exact (sq_eq_sq₀ (by positivity) hΛ.le).1 h

end KAM.Planetary.StrongAMD

end
