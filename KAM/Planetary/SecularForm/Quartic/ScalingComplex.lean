/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.ScalingReal
public import KAM.Planetary.SecularForm.AnalyticReal

/-!
# Secular form: the complexified integrand of the dimensionless pair average

Blueprint P, Part 8, `stepP:p8:q4-a`, complex part: the explicit integrand `qscG` of
`ScalingReal` complexified in the five parameters `(α, v₁, v₂)`, its holomorphy and joint
continuity where all branch conditions hold, and its agreement with `qscG` at real parameters.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The complex root `k = (1 - a² - b²)^{1/2}`. -/
def qscKC (a b : ℂ) : ℂ := (1 - a ^ 2 - b ^ 2) ^ (1 / 2 : ℂ)

/-- First coordinate of the complexified orbit vector, with `k` as a parameter. -/
def qscU0 (K a b : ℂ) (F : ℝ) : ℂ :=
  K * (Real.cos F : ℂ) - a + ((a * (Real.cos F : ℂ) + b * (Real.sin F : ℂ)) / (1 + K)) * a

/-- Second coordinate of the complexified orbit vector, with `k` as a parameter. -/
def qscU1 (K a b : ℂ) (F : ℝ) : ℂ :=
  K * (Real.sin F : ℂ) - b + ((a * (Real.cos F : ℂ) + b * (Real.sin F : ℂ)) / (1 + K)) * b

/-- The complexified squared separation, with the two roots as parameters. -/
def qscSepK (ζ : Fin 5 → ℂ) (K₁ K₂ : ℂ) (F₁ F₂ : ℝ) : ℂ :=
  (ζ 0 * qscU0 K₁ (ζ 1) (ζ 2) F₁ - qscU0 K₂ (ζ 3) (ζ 4) F₂) ^ 2 +
    (ζ 0 * qscU1 K₁ (ζ 1) (ζ 2) F₁ - qscU1 K₂ (ζ 3) (ζ 4) F₂) ^ 2

/-- The complexified integrand, with the two roots as parameters. -/
def qscIntK (ζ : Fin 5 → ℂ) (K₁ K₂ : ℂ) (F₁ F₂ : ℝ) : ℂ :=
  (qscSepK ζ K₁ K₂ F₁ F₂) ^ (-1 / 2 : ℂ) *
    (1 - (ζ 1 * (Real.cos F₁ : ℂ) + ζ 2 * (Real.sin F₁ : ℂ))) *
    (1 - (ζ 3 * (Real.cos F₂ : ℂ) + ζ 4 * (Real.sin F₂ : ℂ)))

/-- The complexified integrand. -/
def qscIntC (ζ : Fin 5 → ℂ) (F₁ F₂ : ℝ) : ℂ :=
  qscIntK ζ (qscKC (ζ 1) (ζ 2)) (qscKC (ζ 3) (ζ 4)) F₁ F₂

/-- The complexified squared separation. -/
def qscSep (ζ : Fin 5 → ℂ) (F₁ F₂ : ℝ) : ℂ :=
  qscSepK ζ (qscKC (ζ 1) (ζ 2)) (qscKC (ζ 3) (ζ 4)) F₁ F₂

/-- The branch conditions under which the complexified integrand is holomorphic. -/
def qscGood (ζ : Fin 5 → ℂ) (F₁ F₂ : ℝ) : Prop :=
  (1 - ζ 1 ^ 2 - ζ 2 ^ 2) ∈ Complex.slitPlane ∧ (1 - ζ 3 ^ 2 - ζ 4 ^ 2) ∈ Complex.slitPlane ∧
    1 + qscKC (ζ 1) (ζ 2) ≠ 0 ∧ 1 + qscKC (ζ 3) (ζ 4) ≠ 0 ∧ qscSep ζ F₁ F₂ ∈ Complex.slitPlane

theorem qsc_diffAt_K (F₁ F₂ : ℝ) {w : (Fin 5 → ℂ) × ℂ × ℂ} (h1 : 1 + w.2.1 ≠ 0)
    (h2 : 1 + w.2.2 ≠ 0) (hs : qscSepK w.1 w.2.1 w.2.2 F₁ F₂ ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun w : (Fin 5 → ℂ) × ℂ × ℂ => qscIntK w.1 w.2.1 w.2.2 F₁ F₂) w := by
  have hsep : DifferentiableAt ℂ (fun w : (Fin 5 → ℂ) × ℂ × ℂ =>
      qscSepK w.1 w.2.1 w.2.2 F₁ F₂) w := by
    unfold qscSepK qscU0 qscU1
    fun_prop (disch := assumption)
  unfold qscIntK
  refine DifferentiableAt.mul (DifferentiableAt.mul (hsep.cpow (differentiableAt_const _) hs) ?_) ?_
  · fun_prop
  · fun_prop

theorem qsc_diffAt_KC (F₁ F₂ : ℝ) {ζ : Fin 5 → ℂ} (h : qscGood ζ F₁ F₂) :
    DifferentiableAt ℂ (fun ζ : Fin 5 → ℂ => qscIntC ζ F₁ F₂) ζ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  have hK1 : DifferentiableAt ℂ (fun ζ : Fin 5 → ℂ => qscKC (ζ 1) (ζ 2)) ζ := by
    unfold qscKC
    exact DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) c1
  have hK2 : DifferentiableAt ℂ (fun ζ : Fin 5 → ℂ => qscKC (ζ 3) (ζ 4)) ζ := by
    unfold qscKC
    exact DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) c2
  have := qsc_diffAt_K F₁ F₂ (w := (ζ, qscKC (ζ 1) (ζ 2), qscKC (ζ 3) (ζ 4))) c3 c4 c5
  have hm : DifferentiableAt ℂ (fun ζ : Fin 5 → ℂ =>
      (ζ, qscKC (ζ 1) (ζ 2), qscKC (ζ 3) (ζ 4))) ζ :=
    differentiableAt_id.prodMk (hK1.prodMk hK2)
  have e : (fun ζ : Fin 5 → ℂ => qscIntC ζ F₁ F₂) =
      (fun w : (Fin 5 → ℂ) × ℂ × ℂ => qscIntK w.1 w.2.1 w.2.2 F₁ F₂) ∘
        (fun ζ : Fin 5 → ℂ => (ζ, qscKC (ζ 1) (ζ 2), qscKC (ζ 3) (ζ 4))) := by
    funext ζ; simp only [Function.comp_apply, qscIntC]
  rw [e]
  exact DifferentiableAt.comp ζ this hm

theorem qsc_contAt_sepK {w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ} (h1 : 1 + w.2.1 ≠ 0)
    (h2 : 1 + w.2.2.1 ≠ 0) :
    ContinuousAt (fun w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ =>
      qscSepK w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) w := by
  unfold qscSepK qscU0 qscU1
  fun_prop (disch := assumption)

theorem qsc_contAt_intK {w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ} (h1 : 1 + w.2.1 ≠ 0)
    (h2 : 1 + w.2.2.1 ≠ 0)
    (hs : qscSepK w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 ∈ Complex.slitPlane) :
    ContinuousAt (fun w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ =>
      qscIntK w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) w := by
  have hsep := qsc_contAt_sepK h1 h2
  unfold qscIntK
  refine ContinuousAt.mul (ContinuousAt.mul (hsep.cpow continuousAt_const hs) ?_) ?_
  · fun_prop
  · fun_prop

theorem qsc_contAt_kC {a b : ℂ} (h : 1 - a ^ 2 - b ^ 2 ∈ Complex.slitPlane) :
    ContinuousAt (fun x : ℂ × ℂ => qscKC x.1 x.2) (a, b) := by
  unfold qscKC
  exact ContinuousAt.cpow (by fun_prop) continuousAt_const h

theorem qsc_contAt_KC {ζ : Fin 5 → ℂ} {F₁ F₂ : ℝ} (h : qscGood ζ F₁ F₂) :
    ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscIntC p.1 p.2.1 p.2.2) (ζ, F₁, F₂) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  have hK1 : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscKC (p.1 1) (p.1 2)) (ζ, F₁, F₂) := by
    unfold qscKC
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const c1
  have hK2 : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscKC (p.1 3) (p.1 4)) (ζ, F₁, F₂) := by
    unfold qscKC
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const c2
  have := qsc_contAt_intK (w := (ζ, qscKC (ζ 1) (ζ 2), qscKC (ζ 3) (ζ 4), F₁, F₂)) c3 c4 c5
  have hm : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
      (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) (ζ, F₁, F₂) :=
    continuousAt_fst.prodMk (hK1.prodMk (hK2.prodMk
      (continuousAt_snd.fst.prodMk continuousAt_snd.snd)))
  have e : (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscIntC p.1 p.2.1 p.2.2) =
      (fun w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ =>
        qscIntK w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) ∘
        (fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
          (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) := by
    funext p; simp only [Function.comp_apply, qscIntC]
  rw [e]
  exact ContinuousAt.comp (f := fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
      (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) (x := (ζ, F₁, F₂)) this hm

theorem qsc_contAt_sep {ζ : Fin 5 → ℂ} {F₁ F₂ : ℝ} (c1 : 1 - ζ 1 ^ 2 - ζ 2 ^ 2 ∈ Complex.slitPlane)
    (c2 : 1 - ζ 3 ^ 2 - ζ 4 ^ 2 ∈ Complex.slitPlane) (c3 : 1 + qscKC (ζ 1) (ζ 2) ≠ 0)
    (c4 : 1 + qscKC (ζ 3) (ζ 4) ≠ 0) :
    ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscSep p.1 p.2.1 p.2.2) (ζ, F₁, F₂) := by
  have hK1 : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscKC (p.1 1) (p.1 2)) (ζ, F₁, F₂) := by
    unfold qscKC
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const c1
  have hK2 : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscKC (p.1 3) (p.1 4)) (ζ, F₁, F₂) := by
    unfold qscKC
    exact ContinuousAt.cpow (by fun_prop) continuousAt_const c2
  have := qsc_contAt_sepK (w := (ζ, qscKC (ζ 1) (ζ 2), qscKC (ζ 3) (ζ 4), F₁, F₂)) c3 c4
  have hm : ContinuousAt (fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
      (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) (ζ, F₁, F₂) :=
    continuousAt_fst.prodMk (hK1.prodMk (hK2.prodMk
      (continuousAt_snd.fst.prodMk continuousAt_snd.snd)))
  have e : (fun p : (Fin 5 → ℂ) × ℝ × ℝ => qscSep p.1 p.2.1 p.2.2) =
      (fun w : (Fin 5 → ℂ) × ℂ × ℂ × ℝ × ℝ =>
        qscSepK w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2) ∘
        (fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
          (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) := by
    funext p; simp only [Function.comp_apply, qscSep]
  rw [e]
  exact ContinuousAt.comp (f := fun p : (Fin 5 → ℂ) × ℝ × ℝ =>
      (p.1, qscKC (p.1 1) (p.1 2), qscKC (p.1 3) (p.1 4), p.2.1, p.2.2)) (x := (ζ, F₁, F₂)) this hm

/-- The real parameters as a point of `ℂ⁵`. -/
def qscEmb (y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Fin 5 → ℂ :=
  ![(y.1 : ℂ), (y.2.1 0 : ℝ), (y.2.1 1 : ℝ), (y.2.2 0 : ℝ), (y.2.2 1 : ℝ)]

theorem qsc_planeSq_lt {v : Fin 2 → ℝ} (hv : planeLength v < 1) : planeSq v < 1 := by
  have := planeLength_sq v
  nlinarith [planeLength_nonneg v]

theorem qsc_kC_real {v : Fin 2 → ℝ} (hv : planeLength v < 1) :
    qscKC (v 0 : ℝ) (v 1 : ℝ) = ((√(1 - planeSq v) : ℝ) : ℂ) := by
  have h0 : 0 ≤ 1 - planeSq v := by linarith [qsc_planeSq_lt hv]
  have h := Complex.ofReal_cpow h0 (1 / 2)
  have e : (1 - (v 0 : ℂ) ^ 2 - (v 1 : ℂ) ^ 2) = ((1 - planeSq v : ℝ) : ℂ) := by
    rw [qsc_planeSq_two]; push_cast; ring
  unfold qscKC
  rw [e, Real.sqrt_eq_rpow]
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; rfl] at h
  exact h.symm

theorem qsc_qscU_zero (v : Fin 2 → ℝ) (F : ℝ) :
    qscU v F 0 = √(1 - planeSq v) * Real.cos F - v 0 +
      ((v 0 * Real.cos F + v 1 * Real.sin F) / (1 + √(1 - planeSq v))) * v 0 := by
  simp [qscU, qsc_planeDot_two, orbitalUnit]
  rfl

theorem qsc_qscU_one (v : Fin 2 → ℝ) (F : ℝ) :
    qscU v F 1 = √(1 - planeSq v) * Real.sin F - v 1 +
      ((v 0 * Real.cos F + v 1 * Real.sin F) / (1 + √(1 - planeSq v))) * v 1 := by
  simp [qscU, qsc_planeDot_two, orbitalUnit]
  rfl

theorem qsc_sep_real {y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hy : y ∈ separatedDomain)
    (F₁ F₂ : ℝ) :
    qscSep (qscEmb y) F₁ F₂ = ((planeSq (y.1 • qscU y.2.1 F₁ - qscU y.2.2 F₂) : ℝ) : ℂ) := by
  have e1 : planeLength y.2.1 < 1 := by have := hy.2.2.1; linarith
  have e2 : planeLength y.2.2 < 1 := by have := hy.2.2.2.1; linarith
  have k1 := qsc_kC_real e1
  have k2 := qsc_kC_real e2
  have a0 : qscEmb y 0 = (y.1 : ℂ) := rfl
  have a1 : qscEmb y 1 = ((y.2.1 0 : ℝ) : ℂ) := rfl
  have a2 : qscEmb y 2 = ((y.2.1 1 : ℝ) : ℂ) := rfl
  have a3 : qscEmb y 3 = ((y.2.2 0 : ℝ) : ℂ) := rfl
  have a4 : qscEmb y 4 = ((y.2.2 1 : ℝ) : ℂ) := rfl
  simp only [qscSep, qscSepK, qscU0, qscU1, a0, a1, a2, a3, a4, k1, k2]
  rw [qsc_planeSq_two (y.1 • qscU y.2.1 F₁ - qscU y.2.2 F₂)]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, qsc_qscU_zero, qsc_qscU_one]
  push_cast
  ring

theorem qsc_good_real {y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hy : y ∈ separatedDomain)
    (F₁ F₂ : ℝ) : qscGood (qscEmb y) F₁ F₂ := by
  have e1 : planeLength y.2.1 < 1 := by have := hy.2.2.1; linarith
  have e2 : planeLength y.2.2 < 1 := by have := hy.2.2.2.1; linarith
  have k1 := qsc_kC_real e1
  have k2 := qsc_kC_real e2
  have q1 := qsc_planeSq_lt e1
  have q2 := qsc_planeSq_lt e2
  have r1 : (1 - (qscEmb y 1) ^ 2 - (qscEmb y 2) ^ 2) = ((1 - planeSq y.2.1 : ℝ) : ℂ) := by
    rw [show qscEmb y 1 = ((y.2.1 0 : ℝ) : ℂ) from rfl, show qscEmb y 2 = ((y.2.1 1 : ℝ) : ℂ) from rfl]
    rw [qsc_planeSq_two]; push_cast; ring
  have r2 : (1 - (qscEmb y 3) ^ 2 - (qscEmb y 4) ^ 2) = ((1 - planeSq y.2.2 : ℝ) : ℂ) := by
    rw [show qscEmb y 3 = ((y.2.2 0 : ℝ) : ℂ) from rfl, show qscEmb y 4 = ((y.2.2 1 : ℝ) : ℂ) from rfl]
    rw [qsc_planeSq_two]; push_cast; ring
  have a1 : qscEmb y 1 = ((y.2.1 0 : ℝ) : ℂ) := rfl
  have a2 : qscEmb y 2 = ((y.2.1 1 : ℝ) : ℂ) := rfl
  have a3 : qscEmb y 3 = ((y.2.2 0 : ℝ) : ℂ) := rfl
  have a4 : qscEmb y 4 = ((y.2.2 1 : ℝ) : ℂ) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [r1, Complex.ofReal_mem_slitPlane]; linarith
  · rw [r2, Complex.ofReal_mem_slitPlane]; linarith
  · rw [a1, a2, k1]
    have : 0 < 1 + √(1 - planeSq y.2.1) := by positivity
    exact_mod_cast this.ne'
  · rw [a3, a4, k2]
    have : 0 < 1 + √(1 - planeSq y.2.2) := by positivity
    exact_mod_cast this.ne'
  · rw [qsc_sep_real hy, Complex.ofReal_mem_slitPlane, ← planeLength_sq]
    have := qsc_sep_pos hy F₁ F₂
    positivity

theorem qsc_intC_real {y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hy : y ∈ separatedDomain)
    (F₁ F₂ : ℝ) : qscIntC (qscEmb y) F₁ F₂ = ((qscG y F₁ F₂ : ℝ) : ℂ) := by
  have e1 : planeLength y.2.1 < 1 := by have := hy.2.2.1; linarith
  have e2 : planeLength y.2.2 < 1 := by have := hy.2.2.2.1; linarith
  have k1 := qsc_kC_real e1
  have k2 := qsc_kC_real e2
  have hs := qsc_sep_real hy F₁ F₂
  have hs' : qscSepK (qscEmb y) (qscKC (qscEmb y 1) (qscEmb y 2))
      (qscKC (qscEmb y 3) (qscEmb y 4)) F₁ F₂ =
      ((planeSq (y.1 • qscU y.2.1 F₁ - qscU y.2.2 F₂) : ℝ) : ℂ) := hs
  unfold qscIntC qscIntK
  rw [hs']
  have a1 : qscEmb y 1 = ((y.2.1 0 : ℝ) : ℂ) := rfl
  have a2 : qscEmb y 2 = ((y.2.1 1 : ℝ) : ℂ) := rfl
  have a3 : qscEmb y 3 = ((y.2.2 0 : ℝ) : ℂ) := rfl
  have a4 : qscEmb y 4 = ((y.2.2 1 : ℝ) : ℂ) := rfl
  rw [cpow_planeSq, a1, a2, a3, a4]
  unfold qscG
  rw [keplerJac_eq, keplerJac_eq]
  push_cast
  ring

end SecularForm
end KAM.Planetary
end
