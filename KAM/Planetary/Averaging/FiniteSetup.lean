/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteGen
public import KAM.Planetary.Averaging.FiniteNumerics

/-!
# P Part 2: the loss budget of the finite averaging iteration, single-step case
(`stepP:p2:nfb-first`, Case B, and `stepP:p2:nfb-N`, `N = 0`)

`GoodSched` packages a schedule, remainder bounds `ε` and a number of stages for which the
iteration is admissible (`IterSetup`) and the final domain, remainder, correction and displacement
bounds of `nfb` hold. `goodSched_single` is the single doubled-loss step, used when
`y₀ < e^{-κ/6}` (this includes `N = 0`). Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`,
package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

/-- A schedule meeting the `nfb` budget: admissible, with the final bounds of the proposition. -/
def GoodSched (D : Set (Fin (a + b) → ℝ)) (r sbar s K α₁ α₂ E : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop :=
  ∃ (c : Sched) (ε : ℕ → ℝ) (m : ℕ),
    IterSetup (realBase D) c K α₁ α₂ h f ε m ∧ c.r = r ∧ c.s = sbar + s ∧
    r / 2 ≤ c.R (m + 1) ∧ sbar + s / 6 ≤ c.S (m + 1) ∧
    ε (m + 1) ≤ Real.exp (-(2 * π * K * s) / 6) * E ∧
    ∑ j ∈ Finset.range m, ε (j + 1) ≤ E / (2 * π * K * s) ∧
    (2 * π * α₁) * s * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (Real.exp 1 * (2 * π * α₁) * c.σ i) ≤ 3 * E ∧
    (2 * π * α₂) * s * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (Real.exp 1 * (2 * π * α₂) * c.σ i) ≤ 3 * E ∧
    (2 * π * α₂) * r * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (2 * π * α₂ * c.ρ i) ≤ 9 * E

section Common

variable {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ} {h : (Fin (a + b) → ℂ) → ℂ}
  {f : CHam (a + b)}

/-- The smallness hypothesis in the form `E ≤ θ r s / (128 κ)`. -/
theorem E_le_kappa (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    E ≤ 3 / (8 * (2 * π * K * s)) * (2 * π * α₂ * (r / 8) * (s / 6)) := by
  have hK := H.K_pos
  have hs := H.s_pos
  have hπ := Real.pi_pos
  have e : 3 / (8 * (2 * π * K * s)) * (2 * π * α₂ * (r / 8) * (s / 6)) =
      α₂ * r / (128 * K) := by
    field_simp; ring
  rw [e]; exact H.small

/-- `y₀ ≤ 3/(8κ)`. -/
theorem y_le (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    E / (2 * π * α₂ * (r / 8) * (s / 6)) ≤ 3 / (8 * (2 * π * K * s)) := by
  have := H.r_pos
  have := H.s_pos
  have := H.α₂_pos
  have := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  exact E_le_kappa H

theorem setup_of_avg (H : AvgHyp D r sbar s K α₁ α₂ E h f) (c : Sched) (hr : c.r = r)
    (hs : c.s = sbar + s) (ε : ℕ → ℝ) (hε0 : E ≤ ε 0) (m : ℕ)
    (hρ : ∀ i ≤ m, 0 < c.ρ i) (hρl : ∀ i ≤ m, 2 * c.ρ i < c.R i)
    (hσ : ∀ i ≤ m, 0 < c.σ i) (hσl : ∀ i ≤ m, 2 * c.σ i < c.S i)
    (hε : ∀ i ≤ m + 1, 0 ≤ ε i)
    (hsmall : ∀ i ≤ m, 1 * ε i / (2 * π * α₂ * c.ρ i * c.σ i) ≤ 1 / 4)
    (hstep : ∀ i ≤ m,
      (1 - 2 * (1 * ε i / (2 * π * α₂ * c.ρ i * c.σ i)))⁻¹ *
        (2 * 1 / (exp 1 * (2 * π * α₂) * c.ρ i * c.σ i) *
          (∑ j : Fin i, (1 / 2) * (c.ρ i / (c.R j - c.R i + c.ρ i) +
            c.σ i / (c.S j - c.S i + c.σ i)) * ε j + ε i) +
          exp (-(2 * π * K * c.σ i))) * ε i ≤ ε (i + 1)) :
    IterSetup (realBase D) c K α₁ α₂ h f ε m := by
  have hc := conv_data D r 0
  have hcr : polyNbhd (realBase D) c.r = KAM.actionNbhd D r := by rw [hr]; exact hc.1
  refine ⟨H.K_pos.le, H.α₂_pos, H.α_order, ?_, ?_, ?_, ?_, ?_, ?_, hρ, hρl, hσ, hσl, hε, hsmall,
    hstep⟩
  · rw [hcr]; exact H.holo
  · rw [hr, hs]; exact H.real_h
  · rw [hr, hs]; exact H.real_f
  · rw [hr, hs]; exact H.cls
  · rw [hr, hs]; exact H.bound.mono le_rfl le_rfl hε0
  · rw [hcr]; exact H.div

/-- The single doubled-loss step (`y₀ < e^{-κ/6}`): `ρ = r/4`, `σ = s/3`. -/
theorem goodSched_single (H : AvgHyp D r sbar s K α₁ α₂ E h f)
    (hB : E / (2 * π * α₂ * (r / 8) * (s / 6)) < Real.exp (-(2 * π * K * s) / 6)) :
    GoodSched D r sbar s K α₁ α₂ E h f := by
  have hK := H.K_pos
  have hs := H.s_pos
  have hr := H.r_pos
  have hα := H.α₂_pos
  have hπ := Real.pi_pos
  have hbud := H.budget
  have hE := H.E_nonneg
  have hsb := H.sbar_nonneg
  set κ : ℝ := 2 * π * K * s with hκ
  set q : ℝ := Real.exp (-κ / 6) with hq
  have hq0 : 0 < q := Real.exp_pos _
  let c : Sched := ⟨r, sbar + s, fun _ => r / 4, fun _ => s / 3⟩
  let ε : ℕ → ℝ := fun i => if i = 0 then E else q * E
  have hQ : 2 * π * α₂ * (r / 4) * (s / 3) = 4 * (2 * π * α₂ * (r / 8) * (s / 6)) := by ring
  have hy : E / (2 * π * α₂ * (r / 4) * (s / 3)) =
      E / (2 * π * α₂ * (r / 8) * (s / 6)) / 4 := by rw [hQ]; field_simp
  have hy3 := y_le H
  have hκ0 : 0 < κ := by linarith
  have h316 : 3 / (8 * κ) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq2 : q ≤ 1 / 2 := by
    have h1 : q ≤ Real.exp (-1) := Real.exp_le_exp.2 (by rw [neg_div]; linarith)
    have : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by have := exp_one_gt_27; linarith)
    linarith
  refine ⟨c, ε, 0, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine setup_of_avg H c rfl rfl ε (by simp [ε]) 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i _; show 0 < r / 4; positivity
    · intro i hi; obtain rfl : i = 0 := by omega
      show 2 * (r / 4) < r; linarith
    · intro i _; show 0 < s / 3; positivity
    · intro i hi; obtain rfl : i = 0 := by omega
      show 2 * (s / 3) < sbar + s; linarith
    · intro i hi
      rcases Nat.lt_or_ge i 1 with h0 | h1
      · obtain rfl : i = 0 := by omega
        simp [ε]; positivity
      · have : i = 1 := by omega
        subst this
        simp [ε]; positivity
    · intro i hi; obtain rfl : i = 0 := by omega
      show 1 * ε 0 / (2 * π * α₂ * (r / 4) * (s / 3)) ≤ 1 / 4
      simp only [ε, ite_true, one_mul]
      rw [hy]
      linarith
    · intro i hi; obtain rfl : i = 0 := by omega
      show (1 - 2 * (1 * ε 0 / (2 * π * α₂ * (r / 4) * (s / 3))))⁻¹ *
        (2 * 1 / (exp 1 * (2 * π * α₂) * (r / 4) * (s / 3)) *
          (∑ j : Fin 0, (1 / 2) * ((r / 4) / (c.R j - c.R 0 + r / 4) +
            (s / 3) / (c.S j - c.S 0 + s / 3)) * ε j + ε 0) +
          exp (-(2 * π * K * (s / 3)))) * ε 0 ≤ ε 1
      have e1 : exp 1 * (2 * π * α₂) * (r / 4) * (s / 3) =
          exp 1 * (2 * π * α₂ * (r / 4) * (s / 3)) := by ring
      have e2 : 2 * π * K * (s / 3) = κ / 3 := by rw [hκ]; ring
      have hx : Real.exp (-(κ / 3)) ≤ q / 2 := by
        have : Real.exp (-(κ / 3)) = q * q := by
          rw [hq, ← Real.exp_add]; congr 1; ring
        rw [this]; nlinarith
      simp only [ε, Finset.univ_eq_empty, Finset.sum_empty, ite_true, one_ne_zero, ite_false, e1, e2]
      have := step_single (Q := 2 * π * α₂ * (r / 4) * (s / 3)) (E := E) (q := q) (x := κ / 3)
        (by positivity) hE hq0.le (by rw [hy]; linarith) (by rw [hy]; linarith) hx
      simpa using this
  · show r / 2 ≤ r - 2 * (r / 4); linarith
  · show sbar + s / 6 ≤ sbar + s - 2 * (s / 3); linarith
  · have : ε (0 + 1) = q * E := by simp [ε]
    rw [this]
  · simp [ε]; positivity
  · have e0 : ε 0 = E := by simp [ε]
    rw [Finset.sum_range_one]
    show (2 * π * α₁) * s * (1 * ε 0 / (exp 1 * (2 * π * α₁) * (s / 3))) ≤ 3 * E
    rw [e0]
    have hα₁ : 0 < α₁ := lt_of_lt_of_le hα H.α_order
    have : (2 * π * α₁) * s * (1 * E / (exp 1 * (2 * π * α₁) * (s / 3))) = 3 * E / exp 1 := by
      field_simp
    rw [this, div_le_iff₀ (by have := exp_one_gt_27; linarith)]
    have := exp_one_gt_27
    nlinarith
  · have e0 : ε 0 = E := by simp [ε]
    rw [Finset.sum_range_one]
    show (2 * π * α₂) * s * (1 * ε 0 / (exp 1 * (2 * π * α₂) * (s / 3))) ≤ 3 * E
    rw [e0]
    have : (2 * π * α₂) * s * (1 * E / (exp 1 * (2 * π * α₂) * (s / 3))) = 3 * E / exp 1 := by
      field_simp
    rw [this, div_le_iff₀ (by have := exp_one_gt_27; linarith)]
    have := exp_one_gt_27
    nlinarith
  · have e0 : ε 0 = E := by simp [ε]
    rw [Finset.sum_range_one]
    show (2 * π * α₂) * r * (1 * ε 0 / (2 * π * α₂ * (r / 4))) ≤ 9 * E
    rw [e0]
    have : (2 * π * α₂) * r * (1 * E / (2 * π * α₂ * (r / 4))) = 4 * E := by
      field_simp
    rw [this]; linarith

end Common

end KAM.Planetary

end
