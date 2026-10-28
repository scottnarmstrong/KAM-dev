/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteMulti
public import KAM.Planetary.Averaging.OscillatorFiniteSingle

/-!
# P Part 2: the `N`-step loss budget of oscillator averaging (`stepP:p2:oa-iter`, `stepP:p2:oa-concl`)

`oscGood_multi` proves the schedule `multiOSched` admissible when `e^{-κ/6} ≤ 2 b y₀` (Case A):
induction hypothesis `ε_{i+1} ≤ ε_i/4`, the final bound `ε_{N+1} ≤ e^{-κ/6} E`, the correction
bound `∑ εᵢ ≤ 400 b E²/(2π α d)` and the displacement budgets `3E`, `9E`, `9E`, `9E`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The left side of the step inequality of `OIter`. -/
def stepVal (c : OSched) (K α : ℝ) (m : ℕ) (ε : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 - 2 * exp 1 * (1 + (m : ℝ)) * ε i /
      (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)))⁻¹ *
    (2 * (1 + (m : ℝ)) / (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)) *
      (∑ j : Fin i, oscW c i j * ε j + ε i) + exp (-(2 * π * K * c.x.σ i))) * ε i

section Widths

variable {a S s N : ℝ}

theorem multi_width_ρ (ha : 0 < a) (hN : 1 ≤ N) {i : ℕ} (hi : (i : ℝ) ≤ N) :
    0 < (multiSched a S s N).ρ i ∧ 2 * (multiSched a S s N).ρ i < (multiSched a S s N).R i := by
  have hN0 : 0 < N := by linarith
  rcases i with _ | l
  · rw [multi_ρ_zero, multi_R_zero]; constructor <;> linarith
  · rw [multi_ρ_succ, multi_R_closed]
    have hl : (l : ℝ) + 1 ≤ N := by exact_mod_cast hi
    refine ⟨by positivity, ?_⟩
    have : ((l : ℝ) + 1) * (a / (8 * N)) ≤ N * (a / (8 * N)) :=
      mul_le_mul_of_nonneg_right hl (by positivity)
    have e : (N : ℝ) * (a / (8 * N)) = a / 8 := by field_simp
    nlinarith

theorem multi_width_σ (hs : 0 < s) (hN : 1 ≤ N) (hSs : s ≤ S) {i : ℕ} (hi : (i : ℝ) ≤ N) :
    0 < (multiSched a S s N).σ i ∧ 2 * (multiSched a S s N).σ i < (multiSched a S s N).S i := by
  have hN0 : 0 < N := by linarith
  rcases i with _ | l
  · rw [multi_σ_zero, multi_S_zero]; constructor <;> linarith
  · rw [multi_σ_succ, multi_S_closed]
    have hl : (l : ℝ) + 1 ≤ N := by exact_mod_cast hi
    refine ⟨by positivity, ?_⟩
    have : ((l : ℝ) + 1) * (s / (4 * N)) ≤ N * (s / (4 * N)) :=
      mul_le_mul_of_nonneg_right hl (by positivity)
    have e : (N : ℝ) * (s / (4 * N)) = s / 4 := by field_simp
    nlinarith

end Widths

section Lower

variable {r rp rq s N : ℝ}

/-- `d_i ≥ d / (64 N²)` for the later stages. -/
theorem multi_Q_lower (hr : 0 < r) (hs : 0 < s) (hrp : 0 < rp) (hrq : 0 < rq) (hN : 0 < N)
    (α : ℝ) (hα : 0 < α) :
    2 * π * α * min (r * s) (rp * rq) / (64 * N ^ 2) ≤
      2 * π * α * min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N))) := by
  have e1 : r / (8 * N) * (s / (4 * N)) = (r * s) / (32 * N ^ 2) := by field_simp; ring
  have e2 : rp / (8 * N) * (rq / (8 * N)) = (rp * rq) / (64 * N ^ 2) := by field_simp; ring
  have hπ := Real.pi_pos
  rw [e1, e2, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) (by positivity)
  · have := min_le_left (r * s) (rp * rq)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ N ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_pos hr hs).le this]
  · exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)

end Lower

section Multi

/-- The numerical data of Case A: positivity, the number of steps `N` and the smallness budget. -/
structure MultiData (r rp rq s K α E κ N : ℝ) (m : ℕ) : Prop where
  hr : 0 < r
  hrp : 0 < rp
  hrq : 0 < rq
  hs : 0 < s
  hα : 0 < α
  hE : 0 ≤ E
  hκ : κ = 2 * π * K * s
  hκ6 : 6 ≤ κ
  hN1 : 1 ≤ N
  hNκ : 8 * N < κ
  hle : N * (12 * Real.log 2) ≤ κ
  hEP : 4096 * (1 + (m : ℝ)) * E * κ ≤ 2 * π * α * min (r * s) (rp * rq)

section Stages

variable {r rp rq sbar s K α E κ N : ℝ} {m : ℕ}

theorem MultiData.hb (_M : MultiData r rp rq s K α E κ N m) : (1 : ℝ) ≤ 1 + (m : ℝ) := by
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem MultiData.hP (M : MultiData r rp rq s K α E κ N m) :
    0 < 2 * π * α * min (r * s) (rp * rq) := by
  have := M.hr; have := M.hrp; have := M.hrq; have := M.hs; have := M.hα
  have := Real.pi_pos
  have : 0 < min (r * s) (rp * rq) := lt_min (by positivity) (by positivity)
  positivity

theorem MultiData.hN0 (M : MultiData r rp rq s K α E κ N m) : 0 < N := by linarith [M.hN1]

theorem MultiData.hc0 (M : MultiData r rp rq s K α E κ N m) :
    0 ≤ firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq)) :=
  firstEps_nonneg (by linarith [M.hb]) M.hP.le

theorem MultiData.hc1 (M : MultiData r rp rq s K α E κ N m) :
    firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq)) ≤ 293 * E / (4096 * κ) :=
  firstEps_le M.hE M.hP (by linarith [M.hκ6]) M.hEP

theorem MultiData.hstage (M : MultiData r rp rq s K α E κ N m) (sbar : ℝ) {l : ℕ}
    (_hl : l + 1 ≤ N) :
    (1 + (m : ℝ)) * oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) (l + 1) /
      (2 * π * α * min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N)))) ≤ 1 / 1024 ∧
    (1 + (m : ℝ)) * ((∑ j : Fin (l + 1), oscW (multiOSched r rp rq (sbar + s) s N) (l + 1) j *
      oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) j) +
      oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) (l + 1)) /
      (2 * π * α * min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N)))) ≤ 1 / 32 := by
  have hc0 := M.hc0
  obtain ⟨w0, w1⟩ := multi_rsum (S := sbar + s) M.hr M.hrp M.hrq M.hs M.hN0 M.hE hc0 l
  refine multi_stage_num (κ := κ) M.hb M.hE M.hP M.hN1 M.hNκ M.hEP ?_ ?_ w1
  · exact multi_Q_lower M.hr M.hs M.hrp M.hrq M.hN0 α M.hα
  · rw [oEps_succ]
    exact mul_le_of_le_one_right hc0 (pow_le_one₀ (by norm_num) (by norm_num))

/-- `Q₀ ≥ P/64` and `b E / Q₀ ≤ 1/(64 κ)`. -/
theorem MultiData.first_facts (M : MultiData r rp rq s K α E κ N m) :
    0 < 2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) ∧
    2 * π * α * min (r * s) (rp * rq) / 64 ≤
      2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) ∧
    (1 + (m : ℝ)) * E / (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8))) ≤
      1 / (64 * κ) := by
  have hr := M.hr; have hrp := M.hrp; have hrq := M.hrq; have hs := M.hs; have hα := M.hα
  have hπ := Real.pi_pos
  have hP0 := M.hP
  have hb0 : 0 < 1 + (m : ℝ) := by linarith [M.hb]
  have hκ0 : 0 < κ := by linarith [M.hκ6]
  have hd0 : 0 < min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) :=
    lt_min (by positivity) (by positivity)
  have hQ0 : 0 < 2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) := by positivity
  have hdd : min (r * s) (rp * rq) / 64 ≤ min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) := by
    refine le_min ?_ ?_
    · have := min_le_left (r * s) (rp * rq); nlinarith
    · have := min_le_right (r * s) (rp * rq); nlinarith
  have hQP : 2 * π * α * min (r * s) (rp * rq) / 64 ≤
      2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) := by
    have := mul_le_mul_of_nonneg_left hdd (by positivity : (0 : ℝ) ≤ 2 * π * α)
    linarith
  refine ⟨hQ0, hQP, ?_⟩
  have h1 : (1 + (m : ℝ)) * E / (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8))) ≤
      64 * (1 + (m : ℝ)) * E / (2 * π * α * min (r * s) (rp * rq)) := by
    rw [div_le_div_iff₀ hQ0 hP0]
    have h2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).1 hQP
    have : 0 ≤ (1 + (m : ℝ)) * E := by have := M.hE; positivity
    nlinarith
  refine h1.trans ?_
  rw [div_le_div_iff₀ hP0 (by positivity)]
  have := M.hEP
  nlinarith

theorem MultiData.step_zero (M : MultiData r rp rq s K α E κ N m) (sbar : ℝ)
    (hA : Real.exp (-κ / 6) ≤ 2 * ((1 + (m : ℝ)) * E /
        (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8))))) :
    stepVal (multiOSched r rp rq (sbar + s) s N) K α m
      (oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq)))) 0 ≤
    oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) 1 := by
  obtain ⟨hQ0, hQP, ht⟩ := M.first_facts
  have hb0 : 0 < 1 + (m : ℝ) := by linarith [M.hb]
  unfold stepVal
  simp only [Finset.univ_eq_empty, Finset.sum_empty, multiOSched, multi_ρ_zero, multi_σ_zero,
    oEps_zero, oEps_succ, pow_zero, mul_one]
  have e2 : 2 * π * K * (s / 6) = κ / 6 := by rw [M.hκ]; ring
  rw [e2]
  have key := osc_step_first (Q := 2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)))
    (E := E) (b := 1 + (m : ℝ)) (q := Real.exp (-(κ / 6))) (κ := κ) hQ0 M.hE hb0.le
    M.hκ6 ht (Real.exp_pos _).le (by rw [← neg_div]; exact hA)
  exact key.trans (osc_first_le hQ0 M.hE hb0.le M.hP hQP)

theorem MultiData.Q_succ_pos (M : MultiData r rp rq s K α E κ N m) :
    0 < 2 * π * α * min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N))) :=
  lt_of_lt_of_le (by have := M.hP; have := M.hN0; positivity)
    (multi_Q_lower M.hr M.hs M.hrp M.hrq M.hN0 α M.hα)

theorem MultiData.step_succ (M : MultiData r rp rq s K α E κ N m) (sbar : ℝ) {l : ℕ}
    (hl : l + 1 ≤ N) :
    stepVal (multiOSched r rp rq (sbar + s) s N) K α m
      (oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq)))) (l + 1) ≤
    oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) (l + 2) := by
  have hb0 : 0 < 1 + (m : ℝ) := by linarith [M.hb]
  have hc0 := M.hc0
  have hN0 := M.hN0
  obtain ⟨w0, -⟩ := multi_rsum (S := sbar + s) M.hr M.hrp M.hrq M.hs hN0 M.hE hc0 l
  have eQ : min ((multiOSched r rp rq (sbar + s) s N).x.ρ (l + 1) *
        (multiOSched r rp rq (sbar + s) s N).x.σ (l + 1))
      ((multiOSched r rp rq (sbar + s) s N).p.ρ (l + 1) *
        (multiOSched r rp rq (sbar + s) s N).q.ρ (l + 1)) =
      min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N))) := by
    simp [multiOSched, multi_ρ_succ, multi_σ_succ]
  have eσ : (multiOSched r rp rq (sbar + s) s N).x.σ (l + 1) = s / (4 * N) := by
    simp [multiOSched, multi_σ_succ]
  have ex : 2 * π * K * (s / (4 * N)) = κ / (4 * N) := by rw [M.hκ]; field_simp
  unfold stepVal
  rw [eQ, eσ, ex]
  have key := osc_step_big
    (Q := 2 * π * α * min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N))))
    (δ := oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) (l + 1))
    (b := 1 + (m : ℝ))
    (st := ∑ j : Fin (l + 1), oscW (multiOSched r rp rq (sbar + s) s N) (l + 1) j *
      oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) j)
    (x := κ / (4 * N)) M.Q_succ_pos (oEps_nonneg M.hE hc0 _) hb0.le w0 (M.hstage sbar hl).1
    (M.hstage sbar hl).2 (exp_step_le hN0 M.hle)
  refine key.trans (le_of_eq ?_)
  rw [oEps_succ, oEps_succ]; ring

theorem MultiData.small (M : MultiData r rp rq s K α E κ N m) (sbar : ℝ) {i : ℕ} (hi : (i : ℝ) ≤ N) :
    oEps E (firstEps (1 + (m : ℝ)) E (2 * π * α * min (r * s) (rp * rq))) i ≤ (2 * π * α) *
      min ((multiOSched r rp rq (sbar + s) s N).x.ρ i * (multiOSched r rp rq (sbar + s) s N).x.σ i)
        ((multiOSched r rp rq (sbar + s) s N).p.ρ i * (multiOSched r rp rq (sbar + s) s N).q.ρ i) /
      (16 * (1 + (m : ℝ))) := by
  have hb0 : 0 < 1 + (m : ℝ) := by linarith [M.hb]
  rcases i with _ | l
  · obtain ⟨hQ0, hQP, -⟩ := M.first_facts
    simp only [multiOSched, multi_ρ_zero, multi_σ_zero, oEps_zero]
    rw [le_div_iff₀ (by positivity)]
    have h2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).1 hQP
    have : 0 ≤ (1 + (m : ℝ)) * E := by have := M.hE; positivity
    have := M.hEP
    have hκ := M.hκ6
    nlinarith
  · have hl : (l : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have eQ : min ((multiOSched r rp rq (sbar + s) s N).x.ρ (l + 1) *
          (multiOSched r rp rq (sbar + s) s N).x.σ (l + 1))
        ((multiOSched r rp rq (sbar + s) s N).p.ρ (l + 1) *
          (multiOSched r rp rq (sbar + s) s N).q.ρ (l + 1)) =
        min (r / (8 * N) * (s / (4 * N))) (rp / (8 * N) * (rq / (8 * N))) := by
      simp [multiOSched, multi_ρ_succ, multi_σ_succ]
    rw [eQ, le_div_iff₀ (by positivity)]
    have h1 := (div_le_iff₀ M.Q_succ_pos).1 (M.hstage sbar hl).1
    nlinarith [oEps_nonneg M.hE M.hc0 (l + 1)]

end Stages

end Multi

end KAM.Planetary

end
