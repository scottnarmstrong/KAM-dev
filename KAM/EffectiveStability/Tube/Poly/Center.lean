/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Defs
public import KAM.EffectiveStability.Tube.Chart.ShiftSymm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The tube centre is a gradient shift (T2-CONF, N5a)

For modes `(m₁, m₂, σ)` let `S(φ) = -Σ σ sin(m₁ φ₀ + m₂ φ₁)` (`gradPot`), the real form of the odd
`S = Σ i σ_m e^{i m·φ}`. N6's tube centre `B_k(φ) = Ī_k + Σ (-m_k σ) cos(m·φ)` (`tubeCenter`,
`m₃ = -m₁ - m₂`) is `Ī_k + ∂_{θ_k} S` with `∂_{θ_k} = fderiv · (phiOf (Pi.single k 1))`
(`tubeCenter_eq_gradient`). Hence N2's symmetry hypothesis `∂_{θ_i} B_l = ∂_{θ_l} B_i` holds
(`tubeCenter_symm`), and `B` is smooth (`contDiff_tubeCenter`) and `2π`-periodic in each angle
(`tubeCenter_add_two_pi`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Real

/-- The potential `S(φ) = -Σ σ sin(m₁ φ₀ + m₂ φ₁)`. -/
def gradPot (modes : List (ℤ × ℤ × ℚ)) (φ : Fin 2 → ℝ) : ℝ :=
  (modes.map fun x => -(x.2.2 : ℝ) * Real.sin (x.1 * φ 0 + x.2.1 * φ 1)).sum

/-- The phase `m₁ φ₀ + m₂ φ₁` as a linear functional. -/
def phaseCLM (m₁ m₂ : ℤ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (m₁ : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    (m₂ : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem hasFDerivAt_phase (m₁ m₂ : ℤ) (φ : Fin 2 → ℝ) :
    HasFDerivAt (fun φ : Fin 2 → ℝ => (m₁ : ℝ) * φ 0 + m₂ * φ 1) (phaseCLM m₁ m₂) φ :=
  ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) φ).const_mul (m₁ : ℝ)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) φ).const_mul (m₂ : ℝ))

/-- `phaseCLM m₁ m₂ (phiOf (Pi.single k 1)) = m_k` with `m₃ = -m₁ - m₂`. -/
theorem phaseCLM_phiOf_single (m₁ m₂ : ℤ) (k : Fin 3) :
    phaseCLM m₁ m₂ (phiOf (Pi.single k 1)) = (modeK m₁ m₂ k : ℝ) := by
  fin_cases k
  · simp [phaseCLM, phiOf, modeK]
  · simp [phaseCLM, phiOf, modeK]
  · simp [phaseCLM, phiOf, modeK]
    ring

theorem hasFDerivAt_gradPot (modes : List (ℤ × ℤ × ℚ)) (φ : Fin 2 → ℝ) :
    HasFDerivAt (gradPot modes)
      ((modes.map fun x => (-(x.2.2 : ℝ) * Real.cos (x.1 * φ 0 + x.2.1 * φ 1)) •
        phaseCLM x.1 x.2.1).sum) φ := by
  induction modes with
  | nil =>
    have h0 : gradPot [] = fun _ => (0 : ℝ) := by funext x; simp [gradPot]
    rw [h0]
    simpa using hasFDerivAt_const (0 : ℝ) φ
  | cons x l ih =>
    have heq : gradPot (x :: l) =
        fun φ => -(x.2.2 : ℝ) * Real.sin (x.1 * φ 0 + x.2.1 * φ 1) + gradPot l φ := by
      funext φ; simp [gradPot]
    rw [heq]
    simp only [List.map_cons, List.sum_cons]
    have h := ((hasFDerivAt_phase x.1 x.2.1 φ).sin).const_mul (-(x.2.2 : ℝ))
    refine (h.add ih).congr_fderiv ?_
    rw [smul_smul]

theorem clm_list_sum_apply {α : Type*} (l : List α) (F : α → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (v : Fin 2 → ℝ) : ((l.map F).sum) v = (l.map fun x => F x v).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    rfl

/-- **The tube centre is a gradient shift**: `B_k = Ī_k + ∂_{θ_k} S`. -/
theorem tubeCenter_eq_gradient (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) :
    (fun φ k => tubeCenter modes Ibar k φ) =
      fun φ k => (Ibar k : ℝ) + fderiv ℝ (gradPot modes) φ (phiOf (Pi.single k 1)) := by
  funext φ k
  rw [(hasFDerivAt_gradPot modes φ).fderiv, tubeCenter, clm_list_sum_apply]
  congr 2
  refine List.map_congr_left fun x _ => ?_
  rw [smul_apply, smul_eq_mul, phaseCLM_phiOf_single]
  ring

theorem contDiff_gradPot (modes : List (ℤ × ℤ × ℚ)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (gradPot modes) := by
  induction modes with
  | nil =>
    have h0 : gradPot [] = fun _ => (0 : ℝ) := by funext x; simp [gradPot]
    rw [h0]
    exact contDiff_const
  | cons x l ih =>
    have heq : gradPot (x :: l) =
        fun φ => -(x.2.2 : ℝ) * Real.sin (x.1 * φ 0 + x.2.1 * φ 1) + gradPot l φ := by
      funext φ; simp [gradPot]
    rw [heq]
    exact (contDiff_const.mul (Real.contDiff_sin.comp (by fun_prop))).add ih

/-- **N2's symmetry hypothesis** for the tube centre: `∂_{θ_i} B_l = ∂_{θ_l} B_i`. -/
theorem tubeCenter_symm (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (φ : Fin 2 → ℝ)
    (i l : Fin 3) :
    fderiv ℝ (fun φ k => tubeCenter modes Ibar k φ) φ (phiOf (Pi.single i 1)) l =
      fderiv ℝ (fun φ k => tubeCenter modes Ibar k φ) φ (phiOf (Pi.single l 1)) i :=
  shift_symm_of_gradient (c := fun k => (Ibar k : ℝ)) (contDiff_gradPot modes).contDiffAt
    (Filter.EventuallyEq.of_eq (tubeCenter_eq_gradient modes Ibar)) i l

theorem contDiff_tubeCenter (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun φ => tubeCenter modes Ibar k φ) := by
  unfold tubeCenter
  refine contDiff_const.add ?_
  induction modes with
  | nil => simpa using contDiff_const
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (contDiff_const.mul (Real.contDiff_cos.comp (by fun_prop))).add ih

theorem contDiff_tubeCenter_pi (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun φ k => tubeCenter modes Ibar k φ) :=
  contDiff_pi.2 fun k => contDiff_tubeCenter modes Ibar k

/-- The tube centre is `2π`-periodic in each reduced angle. -/
theorem tubeCenter_add_two_pi (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (φ : Fin 2 → ℝ)
    (m : Fin 2 → ℤ) :
    (fun k => tubeCenter modes Ibar k (φ + fun a => 2 * π * m a)) =
      fun k => tubeCenter modes Ibar k φ := by
  funext k
  unfold tubeCenter
  congr 2
  refine List.map_congr_left fun x _ => ?_
  have : (x.1 : ℝ) * (φ + fun a => 2 * π * m a) 0 + x.2.1 * (φ + fun a => 2 * π * m a) 1 =
      (x.1 * φ 0 + x.2.1 * φ 1) + ((x.1 * m 0 + x.2.1 * m 1 : ℤ) : ℝ) * (2 * π) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [this, Real.cos_add_int_mul_two_pi]

end KAM.EffectiveStability.Tube

end
