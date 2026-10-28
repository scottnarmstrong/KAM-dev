/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteMulti

/-!
# P Part 2: the `N`-step loss budget (`stepP:p2:nfb-N`, `stepP:p2:nfb-ind`, `stepP:p2:nfb-concl`)

`goodSched_multi` proves the schedule `multiSched` admissible when `e^{-κ/6} ≤ y₀` (Case A):
induction hypothesis `ε_{i+1} ≤ ε_i/4`, the final bound `ε_{N+1} ≤ e^{-κ/6} E`, the correction
bound `∑ εᵢ ≤ E/κ` and the displacement budgets `3E`, `3E`, `9E`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

theorem goodSched_multi {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : AvgHyp D r sbar s K α₁ α₂ E h f)
    (hA : Real.exp (-(2 * π * K * s) / 6) ≤ E / (2 * π * α₂ * (r / 8) * (s / 6))) :
    GoodSched D r sbar s K α₁ α₂ E h f := by
  have hK := H.K_pos
  have hs := H.s_pos
  have hr := H.r_pos
  have hα := H.α₂_pos
  have hπ := Real.pi_pos
  have hbud := H.budget
  have hE := H.E_nonneg
  have hsb := H.sbar_nonneg
  have hα₁ : 0 < α₁ := lt_of_lt_of_le hα H.α_order
  have hy3 := y_le H
  have hEκ := E_le_kappa H
  set κ : ℝ := 2 * π * K * s with hκ
  have hκ0 : 0 < κ := by linarith
  have hEP : E ≤ 2 * π * α₂ * r * s / (128 * κ) := by
    have e : 3 / (8 * κ) * (2 * π * α₂ * (r / 8) * (s / 6)) =
        2 * π * α₂ * r * s / (128 * κ) := by field_simp; ring
    rwa [e] at hEκ
  have h316 : 3 / (8 * κ) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq16 : Real.exp (-(κ / 6)) ≤ 1 / 16 := by
    rw [← neg_div]; exact hA.trans (hy3.trans h316)
  have hN1 := steps_pos hq16
  have hlt := steps_lt hκ0
  have hle := steps_le hκ0
  have hgt := steps_succ_gt (κ := κ)
  generalize ⌊κ / (12 * Real.log 2)⌋₊ = N at hN1 hlt hle hgt
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNκ : 8 * (N : ℝ) < κ := by linarith
  have hqE : (1 / 4 : ℝ) ^ (N + 1) < Real.exp (-(κ / 6)) := quarter_pow_lt hgt
  have hQ0 : ∀ l : ℕ, 0 < 2 * π * α₂ * (r / (8 * (N : ℝ))) * (s / (4 * (N : ℝ))) := fun _ => by
    positivity
  refine ⟨multiSched r (sbar + s) s N, multiEps E κ, N, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine setup_of_avg H (multiSched r (sbar + s) s N) rfl rfl (multiEps E κ)
      (by rw [multiEps_zero]) N ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i _
      rcases i with _ | l
      · rw [multi_ρ_zero]; positivity
      · rw [multi_ρ_succ]; positivity
    · intro i hi
      rcases i with _ | l
      · rw [multi_ρ_zero, multi_R_zero]; linarith
      · rw [multi_ρ_succ, multi_R_closed]
        have hl : (l : ℝ) + 1 ≤ N := by exact_mod_cast hi
        have : ((l : ℝ) + 1) * (r / (8 * N)) ≤ N * (r / (8 * N)) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        have e : (N : ℝ) * (r / (8 * N)) = r / 8 := by field_simp
        nlinarith
    · intro i _
      rcases i with _ | l
      · rw [multi_σ_zero]; positivity
      · rw [multi_σ_succ]; positivity
    · intro i hi
      rcases i with _ | l
      · rw [multi_σ_zero, multi_S_zero]; linarith
      · rw [multi_σ_succ, multi_S_closed]
        have hl : (l : ℝ) + 1 ≤ N := by exact_mod_cast hi
        have : ((l : ℝ) + 1) * (s / (4 * N)) ≤ N * (s / (4 * N)) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        have e : (N : ℝ) * (s / (4 * N)) = s / 4 := by field_simp
        nlinarith
    · intro i _
      exact multiEps_nonneg hE hκ0 i
    · intro i hi
      rcases i with _ | l
      · rw [multi_ρ_zero, multi_σ_zero, multiEps_zero]
        rw [one_mul]
        linarith
      · rw [multi_ρ_succ, multi_σ_succ]
        have := multi_eps_Q hr hs hα hκ0 hE hNr1 hNκ hEP l
        rw [one_mul, div_le_iff₀ (hQ0 l)]
        linarith [hQ0 l]
    · intro i hi
      rcases i with _ | l
      · rw [multi_ρ_zero, multi_σ_zero]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, multiEps_zero, multiEps_succ,
          pow_zero, mul_one]
        have e1 : exp 1 * (2 * π * α₂) * (r / 8) * (s / 6) =
            exp 1 * (2 * π * α₂ * (r / 8) * (s / 6)) := by ring
        have e2 : 2 * π * K * (s / 6) = κ / 6 := by rw [hκ]; ring
        rw [e1, e2]
        have := step_first (Q := 2 * π * α₂ * (r / 8) * (s / 6)) (E := E) (κ := κ)
          (q := Real.exp (-(κ / 6))) (by positivity) hE (by linarith) hy3 (Real.exp_pos _).le
          (by rw [← neg_div]; exact hA)
        simpa using this
      · have hst := multi_star (r := r) (S := sbar + s) (s := s) (N := N) (κ := κ) (E := E)
          hr hs hN0 hκ0 hE l
        simp only at hst
        have hstQ := multi_star_Q hr hs hα hκ0 hE hNr1 hNκ hEP
        have hδ := multi_eps_Q hr hs hα hκ0 hE hNr1 hNκ hEP l
        have e1 : exp 1 * (2 * π * α₂) * (multiSched r (sbar + s) s N).ρ (l + 1) *
            (multiSched r (sbar + s) s N).σ (l + 1) = exp 1 * (2 * π * α₂ *
              (multiSched r (sbar + s) s N).ρ (l + 1) * (multiSched r (sbar + s) s N).σ (l + 1)) := by
          ring
        have e2 : 2 * π * K * (multiSched r (sbar + s) s N).σ (l + 1) = κ / (4 * N) := by
          rw [multi_σ_succ, hκ]; field_simp
        rw [e1, e2]
        have hQc : 2 * π * α₂ * (multiSched r (sbar + s) s N).ρ (l + 1) *
            (multiSched r (sbar + s) s N).σ (l + 1) =
            2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) := by
          rw [multi_ρ_succ, multi_σ_succ]
        refine le_trans (step_big (Q := 2 * π * α₂ * (multiSched r (sbar + s) s N).ρ (l + 1) *
          (multiSched r (sbar + s) s N).σ (l + 1)) (x := κ / (4 * N))
          (by rw [hQc]; exact hQ0 l) (multiEps_nonneg hE hκ0 _) (by rw [hQc]; linarith)
          hst.1 (by rw [hQc]; linarith [hst.2]) (exp_step_le hN0 hle)) (le_of_eq ?_)
        rw [multiEps_succ, multiEps_succ]
        ring
  · rw [multi_R_closed]; apply le_of_eq; field_simp; ring
  · rw [multi_S_closed]; apply le_of_eq; field_simp; ring
  · rw [multiEps_succ]
    have h8 : 3 * E / (4 * κ) ≤ E / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : 3 * E / (4 * κ) * (1 / 4) ^ N ≤ E / 4 * (1 / 4) ^ N :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    have h9 : E / 4 * (1 / 4) ^ N = (1 / 4) ^ (N + 1) * E := by ring
    have h10 : (1 / 4 : ℝ) ^ (N + 1) * E ≤ Real.exp (-κ / 6) * E := by
      rw [neg_div]; exact mul_le_mul_of_nonneg_right hqE.le hE
    linarith
  · have := multi_tail_sum (n := N) hκ0 hE
    have e : 4 / 3 * (3 * E / (4 * κ)) = E / κ := by field_simp
    rw [e] at this; exact this
  · exact multi_disp_σ (by positivity) hs hκ0 hE hN1 hNκ.le r (sbar + s)
  · exact multi_disp_σ (by positivity) hs hκ0 hE hN1 hNκ.le r (sbar + s)
  · exact multi_disp_ρ (by positivity) hr hκ0 hE hN1 hNκ.le (sbar + s)

end KAM.Planetary

end
