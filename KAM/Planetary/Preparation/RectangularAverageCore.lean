/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Finite
public import KAM.Planetary.Preparation.RectangularAverageEps

/-!
# Rectangular averaging: the finite iteration over a complex base set (P11A-P4)

`aniso_avg` is the finite averaging iteration of `KAM.Planetary.nfb` over the complex base set
`Dc` (a closed polydisc of radii `r_j - r_*` about an arbitrary complex centre), with the
quadratic first-step bound of `stepP:p11:aa-quad`. The proofs of `nfb_core` and its schedule
lemmas (`FiniteSetup`, `FiniteCaseA`) are repeated for a base set `Dc` that is not the image of a
real set; the iteration data `Sched`, `IterSetup`, `StepConc` and their lemmas are those of
`Averaging/FiniteStep`, `FiniteChain`, `FiniteGen`, which are stated for an arbitrary `Dc`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

/-- Averaging premises over a complex base set `Dc` (the premises of `AvgHyp`). -/
structure P11AvgHyp {a b : ℕ} (Dc : Set (Fin (a + b) → ℂ)) (r sbar s K α₁ α₂ E : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  r_pos : 0 < r
  sbar_nonneg : 0 ≤ sbar
  s_pos : 0 < s
  K_pos : 0 < K
  budget : 6 ≤ 2 * π * K * s
  α₂_pos : 0 < α₂
  α_order : α₂ ≤ α₁
  E_nonneg : 0 ≤ E
  holo : DifferentiableOn ℂ h (polyNbhd Dc r)
  real_h : RealOn (Dom (a + b) Dc r (sbar + s)) (fun z => h z.2)
  real_f : RealOn (Dom (a + b) Dc r (sbar + s)) f
  cls : InClass Dc r (sbar + s) f
  bound : WBound Dc r (sbar + s) f E
  div : TwoDiv (polyNbhd Dc r) K α₁ α₂ 1 h
  small : E ≤ α₂ * r / (128 * K)

/-- A schedule meeting the `nfb` budget, with the linear and the quadratic bound of `g - f̂₀`. -/
def P11GoodSched (Dc : Set (Fin (a + b) → ℂ)) (r sbar s K α₁ α₂ E : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop :=
  ∃ (c : Sched) (ε : ℕ → ℝ) (m : ℕ),
    IterSetup Dc c K α₁ α₂ h f ε m ∧ c.r = r ∧ c.s = sbar + s ∧
    r / 2 ≤ c.R (m + 1) ∧ sbar + s / 6 ≤ c.S (m + 1) ∧
    ε (m + 1) ≤ Real.exp (-(2 * π * K * s) / 6) * E ∧
    (∑ j ∈ Finset.range m, ε (j + 1) ≤ E / (2 * π * K * s) ∧
      ∑ j ∈ Finset.range m, ε (j + 1) ≤ 128 * E ^ 2 / (2 * π * α₂ * r * s)) ∧
    (2 * π * α₁) * s * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (Real.exp 1 * (2 * π * α₁) * c.σ i) ≤ 3 * E ∧
    (2 * π * α₂) * s * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (Real.exp 1 * (2 * π * α₂) * c.σ i) ≤ 3 * E ∧
    (2 * π * α₂) * r * ∑ i ∈ Finset.range (m + 1),
      1 * ε i / (2 * π * α₂ * c.ρ i) ≤ 9 * E

section Common

variable {Dc : Set (Fin (a + b) → ℂ)} {r sbar s K α₁ α₂ E : ℝ} {h : (Fin (a + b) → ℂ) → ℂ}
  {f : CHam (a + b)}

theorem p11_E_le_kappa (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f) :
    E ≤ 3 / (8 * (2 * π * K * s)) * (2 * π * α₂ * (r / 8) * (s / 6)) := by
  have hK := H.K_pos
  have hs := H.s_pos
  have hπ := Real.pi_pos
  have e : 3 / (8 * (2 * π * K * s)) * (2 * π * α₂ * (r / 8) * (s / 6)) =
      α₂ * r / (128 * K) := by
    field_simp; ring
  rw [e]; exact H.small

theorem p11_y_le (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f) :
    E / (2 * π * α₂ * (r / 8) * (s / 6)) ≤ 3 / (8 * (2 * π * K * s)) := by
  have := H.r_pos
  have := H.s_pos
  have := H.α₂_pos
  have := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  exact p11_E_le_kappa H

theorem p11_setup_of_avg (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f) (c : Sched) (hr : c.r = r)
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
    IterSetup Dc c K α₁ α₂ h f ε m := by
  subst hr
  refine ⟨H.K_pos.le, H.α₂_pos, H.α_order, H.holo, ?_, ?_, ?_, ?_, H.div, hρ, hρl, hσ, hσl, hε,
    hsmall, hstep⟩
  · rw [hs]; exact H.real_h
  · rw [hs]; exact H.real_f
  · rw [hs]; exact H.cls
  · rw [hs]; exact H.bound.mono le_rfl le_rfl hε0

/-- The single doubled-loss step (`y₀ < e^{-κ/6}`): `ρ = r/4`, `σ = s/3`. -/
theorem p11_goodSched_single (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f)
    (hB : E / (2 * π * α₂ * (r / 8) * (s / 6)) < Real.exp (-(2 * π * K * s) / 6)) :
    P11GoodSched Dc r sbar s K α₁ α₂ E h f := by
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
  have hy3 := p11_y_le H
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
  · refine p11_setup_of_avg H c rfl rfl ε (by simp [ε]) 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      simp only [ε, Finset.univ_eq_empty, Finset.sum_empty, ite_true, one_ne_zero, ite_false,
        e1, e2]
      have := step_single (Q := 2 * π * α₂ * (r / 4) * (s / 3)) (E := E) (q := q) (x := κ / 3)
        (by positivity) hE hq0.le (by rw [hy]; linarith) (by rw [hy]; linarith) hx
      simpa using this
  · show r / 2 ≤ r - 2 * (r / 4); linarith
  · show sbar + s / 6 ≤ sbar + s - 2 * (s / 3); linarith
  · have : ε (0 + 1) = q * E := by simp [ε]
    rw [this]
  · exact ⟨by simp [ε]; positivity, by simp [ε]; positivity⟩
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

theorem p11_goodSched_multi {Dc : Set (Fin (a + b) → ℂ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f)
    (hA : Real.exp (-(2 * π * K * s) / 6) ≤ E / (2 * π * α₂ * (r / 8) * (s / 6))) :
    P11GoodSched Dc r sbar s K α₁ α₂ E h f := by
  have hK := H.K_pos
  have hs := H.s_pos
  have hr := H.r_pos
  have hα := H.α₂_pos
  have hπ := Real.pi_pos
  have hbud := H.budget
  have hE := H.E_nonneg
  have hsb := H.sbar_nonneg
  have hα₁ : 0 < α₁ := lt_of_lt_of_le hα H.α_order
  have hy3 := p11_y_le H
  have hEκ := p11_E_le_kappa H
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
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : ℝ, E₁ = 2 * (E / (2 * π * α₂ * (r / 8) * (s / 6))) * E :=
    ⟨_, rfl⟩
  have hE₁ : 0 ≤ E₁ := by rw [hE₁def]; positivity
  have hE₁κ : E₁ ≤ 3 * E / (4 * κ) := by
    rw [hE₁def]
    have h1 : 2 * (E / (2 * π * α₂ * (r / 8) * (s / 6))) * E ≤ 2 * (3 / (8 * κ)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
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
  refine ⟨multiSched r (sbar + s) s N, p11Eps E E₁, N, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine p11_setup_of_avg H (multiSched r (sbar + s) s N) rfl rfl (p11Eps E E₁)
      (by rw [p11Eps_zero]) N ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      exact p11Eps_nonneg hE hE₁ i
    · intro i hi
      rcases i with _ | l
      · rw [multi_ρ_zero, multi_σ_zero, p11Eps_zero]
        rw [one_mul]
        linarith
      · rw [multi_ρ_succ, multi_σ_succ]
        have := (p11Eps_le hE₁κ (l + 1)).trans (multi_eps_Q hr hs hα hκ0 hE hNr1 hNκ hEP l)
        rw [one_mul, div_le_iff₀ (hQ0 l)]
        linarith [hQ0 l]
    · intro i hi
      rcases i with _ | l
      · rw [multi_ρ_zero, multi_σ_zero]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, p11Eps_zero, p11Eps_succ,
          pow_zero, mul_one]
        have e1 : exp 1 * (2 * π * α₂) * (r / 8) * (s / 6) =
            exp 1 * (2 * π * α₂ * (r / 8) * (s / 6)) := by ring
        have e2 : 2 * π * K * (s / 6) = κ / 6 := by rw [hκ]; ring
        rw [e1, e2]
        have := p11_step_first_quad (Q := 2 * π * α₂ * (r / 8) * (s / 6)) (E := E) (κ := κ)
          (q := Real.exp (-(κ / 6))) (by positivity) hE (by linarith) hy3 (Real.exp_pos _).le
          (by rw [← neg_div]; exact hA)
        rw [hE₁def]
        simpa using this
      · have hst := p11_multi_star (r := r) (S := sbar + s) (s := s) (N := N) (κ := κ) (E := E)
          (E₁ := E₁) hr hs hN0 hκ0 hE hE₁ hE₁κ l
        simp only at hst
        have hstQ := multi_star_Q hr hs hα hκ0 hE hNr1 hNκ hEP
        have hδ := (p11Eps_le hE₁κ (l + 1)).trans (multi_eps_Q hr hs hα hκ0 hE hNr1 hNκ hEP l)
        have e1 : exp 1 * (2 * π * α₂) * (multiSched r (sbar + s) s N).ρ (l + 1) *
            (multiSched r (sbar + s) s N).σ (l + 1) = exp 1 * (2 * π * α₂ *
              (multiSched r (sbar + s) s N).ρ (l + 1) *
              (multiSched r (sbar + s) s N).σ (l + 1)) := by
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
          (by rw [hQc]; exact hQ0 l) (p11Eps_nonneg hE hE₁ _) (by rw [hQc]; linarith)
          hst.1 (by rw [hQc]; linarith [hst.2]) (exp_step_le hN0 hle)) (le_of_eq ?_)
        rw [p11Eps_succ, p11Eps_succ]
        ring
  · rw [multi_R_closed]; apply le_of_eq; field_simp; ring
  · rw [multi_S_closed]; apply le_of_eq; field_simp; ring
  · refine le_trans (p11Eps_le hE₁κ (N + 1)) ?_
    rw [multiEps_succ]
    have h8 : 3 * E / (4 * κ) ≤ E / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : 3 * E / (4 * κ) * (1 / 4) ^ N ≤ E / 4 * (1 / 4) ^ N :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    have h9 : E / 4 * (1 / 4) ^ N = (1 / 4) ^ (N + 1) * E := by ring
    have h10 : (1 / 4 : ℝ) ^ (N + 1) * E ≤ Real.exp (-κ / 6) * E := by
      rw [neg_div]; exact mul_le_mul_of_nonneg_right hqE.le hE
    linarith
  · have := p11_multi_tail_sum (E := E) hE₁ N
    refine ⟨?_, ?_⟩
    · have e : 4 / 3 * (3 * E / (4 * κ)) = E / κ := by field_simp
      rw [← e]
      exact this.trans (mul_le_mul_of_nonneg_left hE₁κ (by norm_num))
    · refine this.trans (le_of_eq ?_)
      rw [hE₁def]
      field_simp
      ring
  · exact p11_multi_disp_σ (by positivity) hs hE hE₁ hE₁κ hN1 hNκ.le r (sbar + s) hκ0
  · exact p11_multi_disp_σ (by positivity) hs hE hE₁ hE₁κ hN1 hNκ.le r (sbar + s) hκ0
  · exact p11_multi_disp_ρ (by positivity) hr hE hE₁ hE₁κ hN1 hNκ.le (sbar + s) hκ0

/-- A schedule for the hypotheses of the finite iteration exists. -/
theorem p11_goodSched_of_avg (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f) :
    P11GoodSched Dc r sbar s K α₁ α₂ E h f := by
  by_cases hcase : Real.exp (-(2 * π * K * s) / 6) ≤ E / (2 * π * α₂ * (r / 8) * (s / 6))
  · exact p11_goodSched_multi H hcase
  · exact p11_goodSched_single H (not_le.1 hcase)

/-- Joint witnesses of the finite iteration over `Dc`: all clauses of `nfb`, with the quadratic
bound of `g - f̂₀` of `stepP:p11:aa-quad`. -/
theorem p11_nfb_core {Dc : Set (Fin (a + b) → ℂ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : P11AvgHyp Dc r sbar s K α₁ α₂ E h f) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      let V := Dom (a + b) Dc (r / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧
      MapsTo Ψ V (Dom (a + b) Dc r (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (polyNbhd Dc (r / 2)) ∧
      RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
      (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
      WBound Dc (r / 2) (sbar + s / 6)
        (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (E / (2 * π * K * s)) ∧
      WBound Dc (r / 2) (sbar + s / 6)
        (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (128 * E ^ 2 / (2 * π * α₂ * r * s)) ∧
      InClass Dc (r / 2) (sbar + s / 6) fs ∧
      WBound Dc (r / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
      ∀ z ∈ V,
        (2 * π * α₁) * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E := by
  obtain ⟨c, ε, m, hS, hr, hs, hR, hSS, hε, ⟨hsum, hsumq⟩, hd1, hd2, hd3⟩ :=
    p11_goodSched_of_avg H
  have hπ := Real.pi_pos
  have hK := H.K_pos
  have hs0 := H.s_pos
  have hE := H.E_nonneg
  have hα₂ := H.α₂_pos
  have hr0 := H.r_pos
  have hsc : ∀ i ≤ m, StepConc Dc c K α₁ α₂ h f ε i := fun i hi =>
    step_conc hS hi fun j hj => inv_all hS (m + 1) le_rfl j (by omega)
  have hVsub : Dom (a + b) Dc (r / 2) (sbar + s / 6) ⊆ Sched.U Dc c (m + 1) :=
    Dom_mono hR hSS
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := finite_struct hS hsc
  have hid := finite_ident hS hsc
  have hdisp := finite_disp hS hsc
  obtain ⟨t1, t2⟩ := gen_tail hS
  have hcls := (hsc m le_rfl).cls
  refine ⟨c.Ψ Dc K h f m, c.gI Dc K h f m, c.F Dc K h f (m + 1), ?_⟩
  refine ⟨s1.mono hVsub, s2.mono hVsub, ?_, fun z hz => s4 z (hVsub hz), fun z hz k =>
    s5 k z (hVsub hz), fun x hx => s6 x (hVsub hx), ?_, fun x hx => gI_real hS hsc x (hVsub hx),
    fun x hx => (hsc m le_rfl).real_F x (hVsub hx), fun z hz => ?_, ?_, ?_, ?_, ?_,
    fun z hz => ?_⟩
  · rw [hr, hs] at s3; exact s3.mono_left hVsub
  · exact (gI_differentiable hS).mono (polyNbhd_mono hR)
  · rw [hid z (hVsub hz), G_eq_gI hS z (hVsub hz)]
  · exact t2.mono hR hSS hsum
  · exact t2.mono hR hSS hsumq
  · exact ⟨hcls.differentiableOn.mono (Dom_mono hR hSS),
      fun j z hz => hcls.periodic j z (Dom_mono hR hSS hz)⟩
  · exact (hsc m le_rfl).bound.mono hR hSS hε
  · obtain ⟨d1, d2, d3⟩ := hdisp z (hVsub hz)
    have hα₁ : 0 < α₁ := lt_of_lt_of_le H.α₂_pos H.α_order
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_left d1 (by positivity)).trans hd1
    · exact (mul_le_mul_of_nonneg_left d2 (by positivity)).trans hd2
    · exact (mul_le_mul_of_nonneg_left d3 (by positivity)).trans hd3

end Common

end KAM.Planetary

end
