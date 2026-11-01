/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Phase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scalings `S_t`, `T_t` (`bpW:w5:taylor`, steps `t-scale`, `t-disc`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`S_t(θ,y,u,v) = (θ, t²y, tu, tv)` and `T_t(Θ,Y,U,V) = (t²Θ, Y, tU, tV)` on `KamPhase` (`t ∈ ℂ`).
`scaleS_mem`: if `w ∈ D(s, r')` and `|t| r' < r` then `S_t w ∈ D(s, r)` (the disc of radius
`ρ = r/r'` of step `t-disc`), and `kamNorm_scaleT_le`: `|T_t X|_{r'} ≤ ρ² |X|_r` for `|t| ≤ ρ`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `S_t(θ,y,u,v) = (θ, t²y, tu, tv)`. -/
def scaleS (t : ℂ) (w : KamPhase) : KamPhase :=
  (w.1, t ^ 2 • w.2.1, t • w.2.2.1, t • w.2.2.2)

/-- `T_t(Θ,Y,U,V) = (t²Θ, Y, tU, tV)`. -/
def scaleT (t : ℂ) (X : KamPhase) : KamPhase :=
  (t ^ 2 • X.1, X.2.1, t • X.2.2.1, t • X.2.2.2)

@[simp] theorem scaleS_one (w : KamPhase) : scaleS 1 w = w := by simp [scaleS]
@[simp] theorem scaleT_one (X : KamPhase) : scaleT 1 X = X := by simp [scaleT]

theorem scaleS_mem {s r r' : ℝ} {t : ℂ} (hr' : 0 < r') (htr : ‖t‖ * r' < r) {w : KamPhase}
    (hw : w ∈ kamDomain s r') : scaleS t w ∈ kamDomain s r := by
  obtain ⟨h1, h2, h3⟩ := hw
  have ht0 := norm_nonneg t
  refine ⟨h1, ?_, ?_⟩
  · show ‖t ^ 2 • w.2.1‖ < r ^ 2
    rw [norm_smul, norm_pow]
    have : ‖w.2.1‖ ≤ r' ^ 2 := h2.le
    have a : (‖t‖ * r') ^ 2 < r ^ 2 := pow_lt_pow_left₀ htr (by positivity) two_ne_zero
    have b : ‖t‖ ^ 2 * ‖w.2.1‖ ≤ ‖t‖ ^ 2 * r' ^ 2 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    rw [mul_pow] at a
    linarith
  · show ‖t • w.2.2.1‖ + ‖t • w.2.2.2‖ < r
    rw [norm_smul, norm_smul, ← mul_add]
    nlinarith [norm_nonneg w.2.2.1, norm_nonneg w.2.2.2]

/-- `|T_t X|_{r'} ≤ ρ² |X|_r` for `|t| ≤ ρ = r/r'`. -/
theorem kamNorm_scaleT_le {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {t : ℂ}
    (ht : ‖t‖ ≤ r / r') (X : KamPhase) :
    kamNorm r' (scaleT t X) ≤ (r / r') ^ 2 * kamNorm r X := by
  unfold kamNorm scaleT
  simp only [norm_smul, norm_pow]
  have ht0 := norm_nonneg t
  set ρ := r / r' with hρ
  have hρ0 : 0 < ρ := by positivity
  have e1 : ρ * r' = r := by rw [hρ]; field_simp
  have c1 : ‖t‖ ^ 2 * ‖X.1‖ ≤ ρ ^ 2 * ‖X.1‖ :=
    mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
  have c3 : ‖t‖ * ‖X.2.2.1‖ / r' ≤ ρ ^ 2 * (‖X.2.2.1‖ / r) := by
    have : ρ ^ 2 * (‖X.2.2.1‖ / r) = ρ * ‖X.2.2.1‖ / r' := by
      rw [hρ]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) hr'.le
  have c4 : ‖t‖ * ‖X.2.2.2‖ / r' ≤ ρ ^ 2 * (‖X.2.2.2‖ / r) := by
    have : ρ ^ 2 * (‖X.2.2.2‖ / r) = ρ * ‖X.2.2.2‖ / r' := by
      rw [hρ]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) hr'.le
  have c2 : ‖X.2.1‖ / r' ^ 2 = ρ ^ 2 * (‖X.2.1‖ / r ^ 2) := by
    rw [hρ]; field_simp
  rw [c2]
  nlinarith [c1, c3, c4]

end KAM.Wave
