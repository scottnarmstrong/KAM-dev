/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageKey

/-!
# Slow averaging: the polar chart on the slow-stage domain (P11A-P7b)

Holomorphy of `p11PolarC` where `Re ρ̃ > 0`, membership of `p11PolarC z` in the fast domain,
reality of `p11PolarC` at real points, and 1-periodicity in all angles.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Dom

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Points whose oscillator actions have positive real part. -/
def p11RePos (n : ℕ) : Set (P11Phase (n + n)) := {z | ∀ i : Fin n, 0 < (z.2 (Fin.natAdd n i)).re}

theorem p11RePos_isOpen (n : ℕ) : IsOpen (p11RePos n) := by
  have : p11RePos n = ⋂ i : Fin n, {z : P11Phase (n + n) | 0 < (z.2 (Fin.natAdd n i)).re} := by
    ext z; simp [p11RePos]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))

theorem p11_sqrt_differentiableAt {a : ℂ} (ha : 0 < a.re) :
    DifferentiableAt ℂ Complex.sqrt a := by
  unfold Complex.sqrt
  exact (differentiableAt_id.cpow (differentiableAt_const _) (Or.inl ha))

theorem p11_polarC_differentiableOn : DifferentiableOn ℂ (p11PolarC (n := n)) (p11RePos n) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hs : ∀ i : Fin n, DifferentiableAt ℂ
      (fun w : P11Phase (n + n) => Complex.sqrt (w.2 (Fin.natAdd n i) / Real.pi)) z := by
    intro i
    have h1 : DifferentiableAt ℂ (fun w : P11Phase (n + n) => w.2 (Fin.natAdd n i) / Real.pi) z :=
      by fun_prop
    have h2 : 0 < (z.2 (Fin.natAdd n i) / Real.pi).re := by
      rw [Complex.div_ofReal_re]; exact div_pos (hz i) Real.pi_pos
    exact (p11_sqrt_differentiableAt h2).comp z h1
  refine DifferentiableAt.prodMk ?_ ?_
  · refine differentiableAt_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]
      exact (hs i).mul (by fun_prop)
  · refine differentiableAt_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; fun_prop
    · simp only [Fin.append_right]
      exact (hs i).mul (by fun_prop)

/-- Polar point of a point of the slow-stage domain is in the fast domain, with `‖Π‖ ≤ 4 √ε`. -/
theorem p11_polarC_mem (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hsm : 64 * eps < C.rz ^ 2) {z : P11Phase (n + n)}
    (hz1 : z.1 ∈ KAM.complexStrip (n + n) (C.sigma / 6))
    (hJ : ‖p11SlowJ z.2 - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2)
    (hρ : ‖p11SlowR z.2‖ < 3 * Real.pi * eps) :
    ‖p11PolPt z‖ ≤ 4 * Real.sqrt eps ∧ ‖p11PolPt z‖ < C.rz / 2 ∧
      p11PolarC z ∈ p11WorkingDom n C.J0 (C.sigma / 6) (p11s1 C eps / 2) (C.rz / 2) := by
  obtain ⟨-, -, -, -, -, hσ0, hσ1, hrz0, -⟩ := fast_consts hC
  have hpi := Real.pi_pos
  have he0 : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have he2 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have hzim : ∀ i : Fin n, |(z.1 (Fin.natAdd n i)).im| ≤ 1 / 8 := fun i =>
    (hz1 (Fin.natAdd n i)).le.trans (by linarith)
  have h1 := p11PolPt_norm_le z hzim
  have hs3 : Real.sqrt (‖p11SlowR z.2‖ / Real.pi) ≤ 2 * Real.sqrt eps := by
    have : ‖p11SlowR z.2‖ / Real.pi ≤ (2 * Real.sqrt eps) ^ 2 := by
      rw [div_le_iff₀ hpi]; nlinarith
    exact (Real.sqrt_le_left (by positivity)).2 this
  have hP : ‖p11PolPt z‖ ≤ 4 * Real.sqrt eps := by linarith
  have hPr : ‖p11PolPt z‖ < C.rz / 2 := by
    refine lt_of_le_of_lt hP ?_
    have : (4 * Real.sqrt eps) ^ 2 < (C.rz / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  refine ⟨hP, hPr, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [p11PolarC, Fin.append_left] using hz1 (Fin.castAdd n i)
  · have h : (fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) = p11SlowJ z.2 := by
      funext i; simp [p11PolarC, p11SlowJ]
    show ‖(fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) - _‖ < _
    rw [h]; exact hJ
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_left _ _ |>.trans' le_rfl) hPr
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_right _ _ |>.trans' le_rfl) hPr

end Dom

end KAM.Planetary

end
