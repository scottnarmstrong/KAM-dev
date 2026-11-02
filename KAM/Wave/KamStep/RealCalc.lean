/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reality of Hamiltonians and their derivatives (blueprint-W `bpW:w5:taylor` (i), "`R` is real")

A point of `KamPhase` is *real* (`StepReal`) if `Θ, Y ∈ ℝ²` and `U, V` have real coordinates.
`P` is real if `P w ∈ ℝ` at real `w ∈ V`. Then, at a real `w ∈ V`, `DP(w) c ∈ ℝ` and
`ϖ(DX(w) c, c') ∈ ℝ` for real directions `c, c'` (`stepSymp_field_im`, `stepSymp_dfield_im`):
derivatives of a real-valued function along real lines.
`stepAverage_im`: the torus average of a function real on the real torus is real.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- A point of `KamPhase` is **real**: `Θ, Y ∈ ℝ²`, `U, V` real sequences. -/
def StepReal (w : KamPhase) : Prop :=
  (∀ i, (w.1 i).im = 0) ∧ (∀ i, (w.2.1 i).im = 0) ∧ (∀ j, (w.2.2.1 j).im = 0) ∧
    ∀ j, (w.2.2.2 j).im = 0

/-- A real-valued-on-the-real-line function has a real derivative. -/
theorem im_deriv_eq_zero_of_real {g : ℂ → ℂ} {d : ℂ} (hg : HasDerivAt g d 0)
    (hr : ∀ᶠ t : ℝ in 𝓝 0, (g (t : ℂ)).im = 0) : d.im = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => g (t : ℂ)) d 0 := by
    have := hg.comp_ofReal (z := (0 : ℝ))
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (g (t : ℂ)).im) d.im 0 := by
    exact (Complex.imCLM.hasFDerivAt (x := g ((0 : ℝ) : ℂ))).comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => (g (t : ℂ)).im) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (hr.mono fun t ht => ht)
  exact h2.unique h3

theorem stepReal_line {w c : KamPhase} (hw : StepReal w) (hc : StepReal c) (t : ℝ) :
    StepReal (w + (t : ℂ) • c) := by
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨c1, c2, c3, c4⟩ := hc
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, w1 i, c1 i]; ring
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, w2 i, c2 i]; ring
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, lp.coeFn_add,
      lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, w3 j, c3 j]; ring
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, lp.coeFn_add,
      lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, w4 j, c4 j]; ring

/-- **First derivative of a real function along a real line is real.** -/
theorem fderiv_im_of_real {V : Set KamPhase} (hV : IsOpen V) {P : KamPhase → ℂ}
    (hP : DifferentiableOn ℂ P V) (hreal : ∀ w ∈ V, StepReal w → (P w).im = 0) {w c : KamPhase}
    (hw : w ∈ V) (hwr : StepReal w) (hcr : StepReal c) : (fderiv ℂ P w c).im = 0 := by
  have hPd : DifferentiableAt ℂ P w := hP.differentiableAt (hV.mem_nhds hw)
  have hline : HasDerivAt (fun t : ℂ => P (w + t • c)) (fderiv ℂ P w c) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => w + t • c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const c).const_add w
    have h2 : HasFDerivAt P (fderiv ℂ P w) (w + (0 : ℂ) • c) := by
      simpa using hPd.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  refine im_deriv_eq_zero_of_real hline ?_
  have hc : ContinuousAt (fun t : ℝ => w + (t : ℂ) • c) 0 := by fun_prop
  have hev : ∀ᶠ t : ℝ in 𝓝 0, w + (t : ℂ) • c ∈ V :=
    hc.eventually (hV.mem_nhds (by simpa using hw))
  filter_upwards [hev] with t ht
  exact hreal _ ht (stepReal_line hwr hcr t)

section field

variable (ha : 0 ≤ a) (hqq : 0 ≤ pb + p)

/-- `ϖ(X(w), c)` is real for real `w ∈ V` and real `c` when `P` is real. -/
theorem stepSymp_field_im {V : Set KamPhase} (hV : IsOpen V)
    (hP : IsSmoothing (p := p) ha hqq V P X) (hreal : ∀ w ∈ V, StepReal w → (P w).im = 0)
    {w c : KamPhase} (hw : w ∈ V) (hwr : StepReal w) (hcr : StepReal c) :
    (stepSymp (q := pb) (q' := p) ha hqq (X w) c).im = 0 := by
  rw [← hP.deriv_eq w hw c]
  exact fderiv_im_of_real hV hP.holoP hreal hw hwr hcr

/-- `ϖ(DX(w) c, c')` is real for real `w ∈ V` and real `c, c'` when `P` is real. -/
theorem stepSymp_dfield_im {V : Set KamPhase} (hV : IsOpen V)
    (hP : IsSmoothing (p := p) ha hqq V P X) (hreal : ∀ w ∈ V, StepReal w → (P w).im = 0)
    {w c c' : KamPhase} (hw : w ∈ V) (hwr : StepReal w) (hcr : StepReal c) (hcr' : StepReal c') :
    (stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w c) c').im = 0 := by
  have hXd : DifferentiableAt ℂ X w := hP.holoX.differentiableAt (hV.mem_nhds hw)
  have hline : HasDerivAt (fun t : ℂ => stepSymp (q := pb) (q' := p) ha hqq (X (w + t • c)) c')
      (stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w c) c') 0 := by
    have h1 : HasDerivAt (fun t : ℂ => w + t • c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const c).const_add w
    have h2 : HasFDerivAt X (fderiv ℂ X w) (w + (0 : ℂ) • c) := by
      simpa using hXd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt 0 h1
    have h4 := (sympK (q := pb) (q' := p) ha hqq).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h3
    have h5 := h4.clm_apply (hasDerivAt_const (0 : ℂ) c')
    have e0 : stepSymp (q := pb) (q' := p) ha hqq (X w) 0 = 0 := by simp [stepSymp]
    simpa [sympK_apply, e0] using h5
  refine im_deriv_eq_zero_of_real hline ?_
  have hc : ContinuousAt (fun t : ℝ => w + (t : ℂ) • c) 0 := by fun_prop
  have hev : ∀ᶠ t : ℝ in 𝓝 0, w + (t : ℂ) • c ∈ V :=
    hc.eventually (hV.mem_nhds (by simpa using hw))
  filter_upwards [hev] with t ht
  exact stepSymp_field_im ha hqq hV hP hreal ht (stepReal_line hwr hcr t) hcr'

end field

/-! ### Averages of real functions -/

/-- A continuous real-linear functional vanishing on the values of `f` vanishes on `∫ f`. -/
theorem integral_clm_eq_zero {α E : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (L : E →L[ℝ] ℝ) {f : α → E} (hf : ∀
        x, L (f x) = 0) :
    L (∫ x, f x ∂μ) = 0 := by
  by_cases hi : MeasureTheory.Integrable f μ
  · have := L.integral_comp_comm hi
    rw [← this]
    simp [hf]
  · rw [MeasureTheory.integral_undef hi]
    simp

end KAM.Wave
