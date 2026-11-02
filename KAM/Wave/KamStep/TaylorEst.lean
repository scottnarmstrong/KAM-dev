/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorScale
public import KAM.Wave.KamStep.TaylorOneVar
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Taylor estimates for the field (`bpW:w5:taylor` (iii), (iv), steps `t-disc`, `t-est`)

For a field `X` holomorphic on `D(s,r)` put `G(t,w) = T_t X(S_t w)` and
`taylorXR X w = ∑_{k ≤ 2} g_k(w)` with `g_k` the Taylor coefficients of `G(·, w)` at `t = 0`
(`taylorField`). Then, with `|X|_r ≤ ε` on `D(s,r)`: `taylorXR_bound` (`|X_R| ≤ 3ε`) and
`taylorXR_remainder` (for `w ∈ D(s, r')`, `ρ = r/r' > 1`: `|X w - X_R w|_{r'} ≤ ρ²ε/ρ³/(1-1/ρ)`).
-/

@[expose] public noncomputable section

open Metric Set

namespace KAM.Wave

/-- `G(t,w) = T_t X(S_t w)`. -/
def taylorG (X : KamPhase → KamPhase) (w : KamPhase) (t : ℂ) : KamPhase :=
  scaleT t (X (scaleS t w))

/-- The Taylor coefficient `g_k(w)` of `t ↦ G(t, w)`. -/
def taylorField (X : KamPhase → KamPhase) (w : KamPhase) (k : ℕ) : KamPhase :=
  ((k.factorial : ℂ)⁻¹) • iteratedDeriv k (taylorG X w) 0

/-- `X_R(w) = ∑_{k ≤ 2} g_k(w)`. -/
def taylorXR (X : KamPhase → KamPhase) (w : KamPhase) : KamPhase :=
  ∑ k ∈ Finset.range 3, taylorField X w k

/-- The identity map `KamPhase → StepPhase r'` as a continuous linear map. -/
def kamToStep (r' : ℝ) [Fact (0 < r')] : KamPhase →L[ℂ] StepPhase r' :=
  LinearMap.mkContinuous (LinearMap.id : KamPhase →ₗ[ℂ] StepPhase r')
    (1 + 1 / r' ^ 2 + 2 / r') fun W => by
      show kamNorm r' W ≤ _
      exact kamNorm_le_norm_kamPhase (Fact.out) W

theorem norm_kamToStep (r' : ℝ) [Fact (0 < r')] (W : KamPhase) : ‖kamToStep r' W‖ = kamNorm r' W :=
  rfl

theorem differentiableAt_scaleS (w : KamPhase) (t : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => scaleS t w) t := by
  unfold scaleS
  refine DifferentiableAt.prodMk (differentiableAt_const _) (DifferentiableAt.prodMk ?_
    (DifferentiableAt.prodMk ?_ ?_))
  · exact (differentiableAt_pow 2).smul_const _
  · exact differentiableAt_id.smul_const _
  · exact differentiableAt_id.smul_const _

theorem differentiableAt_scaleT {Y : ℂ → KamPhase} {t : ℂ} (hY : DifferentiableAt ℂ Y t) :
    DifferentiableAt ℂ (fun t : ℂ => scaleT t (Y t)) t := by
  unfold scaleT
  have h1 : DifferentiableAt ℂ (fun t => (Y t).1) t := differentiableAt_fst.comp t hY
  have h2 : DifferentiableAt ℂ (fun t => (Y t).2.1) t :=
    (differentiableAt_fst.comp t (differentiableAt_snd.comp t hY))
  have h3 : DifferentiableAt ℂ (fun t => (Y t).2.2.1) t := by
    have := differentiableAt_snd.comp t (differentiableAt_snd.comp t hY)
    exact differentiableAt_fst.comp t this
  have h4 : DifferentiableAt ℂ (fun t => (Y t).2.2.2) t := by
    have := differentiableAt_snd.comp t (differentiableAt_snd.comp t hY)
    exact differentiableAt_snd.comp t this
  exact DifferentiableAt.prodMk ((differentiableAt_pow 2).smul h1) (DifferentiableAt.prodMk h2
    (DifferentiableAt.prodMk (differentiableAt_id.smul h3) (differentiableAt_id.smul h4)))

section est

variable {X : KamPhase → KamPhase} {s r r' ε : ℝ} {w : KamPhase}

theorem differentiableOn_taylorG (hX : DifferentiableOn ℂ X (kamDomain s r)) (hr' : 0 < r')
    (hw : w ∈ kamDomain s r') : DifferentiableOn ℂ (taylorG X w) (ball 0 (r / r')) := by
  intro t ht
  have htn : ‖t‖ < r / r' := by simpa using ht
  have htr : ‖t‖ * r' < r := by rwa [lt_div_iff₀ hr'] at htn
  have hmem := scaleS_mem hr' htr hw
  have hXd := hX.differentiableAt ((kamDomain_isOpen s r).mem_nhds hmem)
  exact (differentiableAt_scaleT (hXd.comp t (differentiableAt_scaleS w t))).differentiableWithinAt

theorem norm_taylorG_le (hX_bd : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hr : 0 < r)
    (hr' : 0 < r') (hw : w ∈ kamDomain s r') {t : ℂ} (ht : t ∈ ball (0 : ℂ) (r / r')) :
    kamNorm r' (taylorG X w t) ≤ (r / r') ^ 2 * ε := by
  have htn : ‖t‖ < r / r' := by simpa using ht
  have htr : ‖t‖ * r' < r := by rwa [lt_div_iff₀ hr'] at htn
  have hmem := scaleS_mem hr' htr hw
  refine (kamNorm_scaleT_le hr hr' htn.le _).trans ?_
  exact mul_le_mul_of_nonneg_left (hX_bd _ hmem) (by positivity)

theorem taylorCoeff_kamToStep (r' : ℝ) [Fact (0 < r')] {g : ℂ → KamPhase}
    (hg : ContDiffAt ℂ ⊤ g 0) (k : ℕ) :
    taylorCoeff (fun t => kamToStep r' (g t)) k =
      kamToStep r' (((k.factorial : ℂ)⁻¹) • iteratedDeriv k g 0) := by
  unfold taylorCoeff
  rw [map_smul]
  congr 1
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have := (kamToStep r').iteratedFDeriv_comp_left hg (i := k) (by exact_mod_cast le_top)
  have h2 := congrArg (fun m => m (fun _ : Fin k => (1 : ℂ))) this
  simpa using h2 |> fun h => (show (fun t => kamToStep r' (g t)) = ⇑(kamToStep r') ∘ g from rfl) ▸ h

theorem contDiffAt_taylorG (hX : DifferentiableOn ℂ X (kamDomain s r)) (hr' : 0 < r')
    (hρ : 0 < r / r') (hw : w ∈ kamDomain s r') : ContDiffAt ℂ ⊤ (taylorG X w) 0 :=
  ((differentiableOn_taylorG hX hr' hw).contDiffOn isOpen_ball).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hρ))

variable (hX : DifferentiableOn ℂ X (kamDomain s r))
  (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hr : 0 < r) (hr' : 0 < r')
  (hw : w ∈ kamDomain s r')
include hX hb hr hr' hw

/-- `|g_k(w)|_{r'} ≤ ρ²ε/ρ^k`, `ρ = r/r'` (step `t-est`). -/
theorem norm_taylorField_le (k : ℕ) :
    kamNorm r' (taylorField X w k) ≤ (r / r') ^ 2 * ε / (r / r') ^ k := by
  have : Fact (0 < r') := ⟨hr'⟩
  have hρ : 0 < r / r' := by positivity
  have h := (norm_taylorCoeff_le (g := fun t => kamToStep r' (taylorG X w t)) hρ
      ((kamToStep r').differentiable.comp_differentiableOn (differentiableOn_taylorG hX hr' hw))
      (fun t ht => norm_taylorG_le hb hr hr' hw ht) k)
  rw [taylorCoeff_kamToStep r' (contDiffAt_taylorG hX hr' hρ hw)] at h
  exact h

end est

section final

variable {X : KamPhase → KamPhase} {s r r' ε : ℝ} {w : KamPhase}

/-- **Taylor estimate (iii)**: `|X_R(w)|_r ≤ 3ε` on `D(s,r)` (blueprint `bpW:w5:taylor` (iii),
step `t-est`). -/
theorem taylorXR_bound (hX : DifferentiableOn ℂ X (kamDomain s r))
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hr : 0 < r) (hw : w ∈ kamDomain s r) :
    kamNorm r (taylorXR X w) ≤ 3 * ε := by
  have hk : ∀ k, kamNorm r (taylorField X w k) ≤ ε := fun k => by
    have := norm_taylorField_le hX hb hr hr hw k
    rwa [div_self hr.ne', one_pow, one_pow, one_mul, div_one] at this
  unfold taylorXR
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have a1 := kamNorm_add_le hr (taylorField X w 0 + taylorField X w 1) (taylorField X w 2)
  have a2 := kamNorm_add_le hr (taylorField X w 0) (taylorField X w 1)
  linarith [hk 0, hk 1, hk 2]

/-- **Taylor estimate (iv)**: for `w ∈ D(s,r')` and `ρ = r/r' > 1`,
`|X(w) - X_R(w)|_{r'} ≤ ρ²ε/ρ³/(1-1/ρ)` (blueprint `bpW:w5:taylor` (iv), step `t-est`). -/
theorem taylorXR_remainder (hX : DifferentiableOn ℂ X (kamDomain s r))
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hr : 0 < r) (hr' : 0 < r')
    (hρ : 1 < r / r') (hw : w ∈ kamDomain s r') :
    kamNorm r' (X w - taylorXR X w) ≤
      (r / r') ^ 2 * ε / (r / r') ^ 3 / (1 - 1 / (r / r')) := by
  have : Fact (0 < r') := ⟨hr'⟩
  have hρ0 : 0 < r / r' := by linarith
  have h := norm_taylor_remainder_le (g := fun t => kamToStep r' (taylorG X w t)) hρ
    ((kamToStep r').differentiable.comp_differentiableOn (differentiableOn_taylorG hX hr' hw))
    (fun t ht => norm_taylorG_le hb hr hr' hw ht) (t := 1) (by simp)
  have hc := contDiffAt_taylorG hX hr' hρ0 hw
  have e : ∑ k ∈ Finset.range 3, (1 : ℂ) ^ k • taylorCoeff (fun t => kamToStep r' (taylorG X w t)) k
      = kamToStep r' (taylorXR X w) := by
    simp only [one_pow, one_smul, taylorCoeff_kamToStep r' hc, taylorXR, taylorField, map_sum]
  rw [e] at h
  have e1 : kamToStep r' (taylorG X w 1) = kamToStep r' (X w) := by simp [taylorG]
  rw [e1, ← map_sub] at h
  exact h

/-- `|W|_{r₁} ≤ (r₂/r₁)² |W|_{r₂}` for `0 < r₁ ≤ r₂`. -/
theorem kamNorm_le_ratio_sq {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) (W : KamPhase) :
    kamNorm r₁ W ≤ (r₂ / r₁) ^ 2 * kamNorm r₂ W := by
  have h2 : 0 < r₂ := h1.trans_le h12
  have hq : 1 ≤ r₂ / r₁ := by rw [le_div_iff₀ h1]; linarith
  have hq2 : 1 ≤ (r₂ / r₁) ^ 2 := one_le_pow₀ hq
  unfold kamNorm
  have e2 : ‖W.2.1‖ / r₁ ^ 2 = (r₂ / r₁) ^ 2 * (‖W.2.1‖ / r₂ ^ 2) := by field_simp
  have e3 : ‖W.2.2.1‖ / r₁ ≤ (r₂ / r₁) ^ 2 * (‖W.2.2.1‖ / r₂) := by
    have : (r₂ / r₁) ^ 2 * (‖W.2.2.1‖ / r₂) = (r₂ / r₁) * ‖W.2.2.1‖ / r₁ := by field_simp
    rw [this]; exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg W.2.2.1]) h1.le
  have e4 : ‖W.2.2.2‖ / r₁ ≤ (r₂ / r₁) ^ 2 * (‖W.2.2.2‖ / r₂) := by
    have : (r₂ / r₁) ^ 2 * (‖W.2.2.2‖ / r₂) = (r₂ / r₁) * ‖W.2.2.2‖ / r₁ := by field_simp
    rw [this]; exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg W.2.2.2]) h1.le
  rw [e2]
  nlinarith [norm_nonneg W.1, mul_le_mul_of_nonneg_right hq2 (norm_nonneg W.1)]

/-- **Taylor estimate (iv), numerical form**: for `0 < η ≤ 1/8`, `w ∈ D(s, 4ηr)`:
`|X(w) - X_R(w)|_{ηr} ≤ 128 η ε` (blueprint `bpW:w5:taylor` (iv)). -/
theorem taylorXR_remainder_128 {η : ℝ} (hX : DifferentiableOn ℂ X (kamDomain s r))
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hr : 0 < r) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hw : w ∈ kamDomain s (4 * η * r)) :
    kamNorm (η * r) (X w - taylorXR X w) ≤ 128 * η * ε := by
  have hr' : 0 < 4 * η * r := by positivity
  have hρe : r / (4 * η * r) = 1 / (4 * η) := by field_simp
  have hρ : 1 < r / (4 * η * r) := by
    rw [hρe, lt_div_iff₀ (by positivity)]; linarith
  have hwr : w ∈ kamDomain s r := by
    obtain ⟨h1, h2, h3⟩ := hw
    have hq : 4 * η * r ≤ r := by nlinarith
    refine ⟨h1, h2.trans_le ?_, h3.trans_le hq⟩
    nlinarith [sq_nonneg r]
  have hε : 0 ≤ ε := (kamNorm_nonneg hr.le _).trans (hb w hwr)
  have h := taylorXR_remainder hX hb hr hr' hρ hw
  rw [hρe] at h
  have h4 : 0 < 1 - 4 * η := by linarith
  have key : (1 / (4 * η)) ^ 2 * ε / (1 / (4 * η)) ^ 3 / (1 - 1 / (1 / (4 * η))) =
      4 * η * ε / (1 - 4 * η) := by field_simp
  rw [key, le_div_iff₀ h4] at h
  have h8 : 4 * η * ε ≤ 8 * η * ε * (1 - 4 * η) := by nlinarith [mul_nonneg hη.le hε]
  have hηr : 0 < η * r := mul_pos hη hr
  have hr1 := kamNorm_le_ratio_sq (r₁ := η * r) (r₂ := 4 * η * r) hηr (by nlinarith)
    (X w - taylorXR X w)
  have e4 : 4 * η * r / (η * r) = 4 := by field_simp
  rw [e4] at hr1
  have hfin : kamNorm (4 * η * r) (X w - taylorXR X w) ≤ 8 * η * ε := by
    exact le_of_mul_le_mul_right (by linarith) h4
  nlinarith

end final

end KAM.Wave
