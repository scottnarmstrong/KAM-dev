/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepBracket
public import KAM.Wave.KamStep.NewHamIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The commutator integral of `P_+` is a smoothing Hamiltonian (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepGfam t = (1-t) {N̂,F} + t {R,F}` (the brackets `{R(t),F}` of `R(t) = (1-t)N̂ + tR`) with
`G`-valued fields `stepZgfam` (Zeros of `Cauchy`-bounded size `O(εM_F/σ)`), and the conclusion of
`newHam_integral_smoothing` on `D_+ = D(s-5σ, ηr)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η M e₁ : ℝ} [Fact (0 < r)]

section fam

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
  (FT : HomTaylor_gen a p pb (s - σ))

/-- `{R(t), F}` as a function. -/
def stepGfam (t : ℝ) : StepPhase r → ℂ := fun z =>
  (1 - (t : ℂ)) * stepBrG ha hp hpb (homNhatTaylor_gen T) FT z + (t : ℂ) * stepBrG ha hp hpb T FT z

/-- The `G`-valued field of `{R(t), F}`. -/
def stepZgfam (t : ℝ) : StepPhase r → StepPhase r := fun z =>
  (1 - (t : ℂ)) • stepBrZ ha hp hpb (homNhatTaylor_gen T) FT z + (t : ℂ) • stepBrZ ha hp hpb T FT z

variable {ha hp hpb T FT}

theorem stepGfam_hasFDerivAt (hσ : 0 < σ) (hσs : 2 * σ < s) (t : ℝ) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    HasFDerivAt (stepGfam ha hp hpb T FT t)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepZgfam ha hp hpb T FT t z))) z := by
  have h1 := (stepBrG_hasFDerivAt (ha := ha) (hp := hp) (hpb := hpb) (TG := homNhatTaylor_gen T)
    (FT := FT) hσ hσs hz).const_mul (1 - (t : ℂ))
  have h2 := (stepBrG_hasFDerivAt (ha := ha) (hp := hp) (hpb := hpb) (TG := T) (FT := FT) hσ hσs
    hz).const_mul (t : ℂ)
  have h : HasFDerivAt (stepGfam ha hp hpb T FT t) _ z := h1.add h2
  refine h.congr_fderiv ?_
  ext W
  simp [stepZgfam, map_add, map_smul]

section bounds

variable (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσs : 2 * σ < s) {Mf : ℝ} (he₁ : 0 ≤ e₁) (hMf : 0 ≤ Mf)
  (hT : HomFieldBound_gen ha hp hpb r e₁ T)
  (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
  (hF : HomFieldBound_gen ha hp hpb r Mf FT)
include hσ hσ1 hσs he₁ hMf hT hTn hF

theorem stepZgfam_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (stepZgfam ha hp hpb T FT t) (stepDomain r (s - 2 * σ) (r / 2)) :=
  ((stepBrZ_differentiableOn (TG := homNhatTaylor_gen T) (FT := FT) ha hp hpb hσ hσs).const_smul
    (1 - (t : ℂ))).add
    ((stepBrZ_differentiableOn (TG := T) (FT := FT) ha hp hpb hσ hσs).const_smul (t : ℂ))

theorem norm_stepZgfam_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepZgfam ha hp hpb T FT t z‖ ≤ 8 * e₁ * Mf / σ := by
  have h1 := stepBrZ_norm_le (TG := homNhatTaylor_gen T) (FT := FT) ha hp hpb hσ hσ1 hσs
    (by linarith) hMf hTn hF hz
  have h2 := stepBrZ_norm_le (TG := T) (FT := FT) ha hp hpb hσ hσ1 hσs he₁ hMf hT hF hz
  unfold stepZgfam
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have a1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
    rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have a2 : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [a1, a2]
  have hS : 0 ≤ e₁ * Mf / σ := by positivity
  have : 4 * (2 * e₁) * Mf / σ = 8 * e₁ * Mf / σ := by ring
  rw [this] at h1
  have h3 : 4 * e₁ * Mf / σ ≤ 8 * e₁ * Mf / σ := by
    rw [div_le_div_iff_of_pos_right hσ]; nlinarith
  nlinarith [ht.1, ht.2, norm_nonneg (stepBrZ ha hp hpb (homNhatTaylor_gen T) FT z),
    norm_nonneg (stepBrZ ha hp hpb T FT z)]

theorem norm_stepZgfam_sub_le {t t' : ℝ} {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepZgfam ha hp hpb T FT t z - stepZgfam ha hp hpb T FT t' z‖ ≤
      12 * e₁ * Mf / σ * |t - t'| := by
  have h1 := stepBrZ_norm_le (TG := homNhatTaylor_gen T) (FT := FT) ha hp hpb hσ hσ1 hσs
    (by linarith) hMf hTn hF hz
  have h2 := stepBrZ_norm_le (TG := T) (FT := FT) ha hp hpb hσ hσ1 hσs he₁ hMf hT hF hz
  have e : stepZgfam ha hp hpb T FT t z - stepZgfam ha hp hpb T FT t' z =
      ((t - t' : ℝ) : ℂ) • (stepBrZ ha hp hpb T FT z - stepBrZ ha hp hpb (homNhatTaylor_gen T) FT z) := by
    unfold stepZgfam
    push_cast
    module
  rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have : ‖stepBrZ ha hp hpb T FT z - stepBrZ ha hp hpb (homNhatTaylor_gen T) FT z‖ ≤
      12 * e₁ * Mf / σ := by
    refine (norm_sub_le _ _).trans ?_
    have : 4 * (2 * e₁) * Mf / σ = 8 * e₁ * Mf / σ := by ring
    rw [this] at h1
    have h4 : 4 * e₁ * Mf / σ + 8 * e₁ * Mf / σ = 12 * e₁ * Mf / σ := by ring
    linarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _) |>.trans_eq (by ring)

theorem norm_stepGfam_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepGfam ha hp hpb T FT t z‖ ≤ 2 * ((4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf)) := by
  have h1 := norm_stepBrG_le (TG := homNhatTaylor_gen T) (FT := FT) ha hp hpb hσ hσs hTn hF hz
  have h2 := norm_stepBrG_le (TG := T) (FT := FT) ha hp hpb hσ hσs hT hF hz
  unfold stepGfam
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have a1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
    rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have a2 : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [a1, a2]
  have hc : 0 ≤ (4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf) := by positivity
  have : (4 * Real.pi + 1) * r ^ 2 * (2 * e₁ * Mf) = 2 * ((4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf)) := by
    ring
  rw [mul_assoc] at h1
  nlinarith [ht.1, ht.2, norm_nonneg (stepBrG ha hp hpb (homNhatTaylor_gen T) FT z),
    norm_nonneg (stepBrG ha hp hpb T FT z)]

end bounds

end fam

end KAM.Wave
