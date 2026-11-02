/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorFieldRv
public import KAM.Wave.KamStep.HoloFderiv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Properties of a smoothing pair (blueprint-W `bpW:w5:taylor` step `t-comp`)

For a smoothing pair `(P, X)` on `D(s,r)`:
* `stepSymp_dX_symm`: `ϖ(DX(w) a, c) = ϖ(DX(w) c, a)` (symmetry of `D²P`);
* `stepField_periodic`: if `P` is `1`-periodic in the angles so is `X`, and so is `DX`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- The angle translation `τ_i = (e_i, 0, 0, 0)`. -/
def stepTau (i : Fin 2) : KamPhase := (Pi.single i 1, 0, 0, 0)

theorem kamDomain_add_tau {w : KamPhase} (hw : w ∈ kamDomain s r) (i : Fin 2) :
    w + stepTau i ∈ kamDomain s r := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun j => ?_, by simpa [stepTau] using h2, by simpa [stepTau] using h3⟩
  have : ((w + stepTau i).1 j).im = (w.1 j).im := by
    simp only [stepTau, Prod.fst_add, Pi.add_apply]
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  show |((w + stepTau i).1 j).im| < s
  rw [this]; exact h1 j

theorem fderiv_eq_sympK (ha : 0 ≤ a) (hqq : 0 ≤ pb + p)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X) {z : KamPhase}
    (hz : z ∈ kamDomain s r) :
    fderiv ℂ P z = sympK (q := pb) (q' := p) ha hqq (X z) :=
  ContinuousLinearMap.ext fun W => by rw [hP.deriv_eq z hz W]; rfl

/-- **Symmetry of the Hessian** (`D²P` symmetric): `ϖ(DX(w)a, c) = ϖ(DX(w)c, a)`. -/
theorem stepSymp_dX_symm (ha : 0 ≤ a) (hqq : 0 ≤ pb + p)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X) {w : KamPhase}
    (hw : w ∈ kamDomain s r) (u v : KamPhase) :
    stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w u) v =
      stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w v) u := by
  have hXd : DifferentiableAt ℂ X w :=
    hP.holoX.differentiableAt ((kamDomain_isOpen s r).mem_nhds hw)
  have hev : ∀ᶠ y in 𝓝 w, HasFDerivAt P (sympK (q := pb) (q' := p) ha hqq (X y)) y := by
    filter_upwards [(kamDomain_isOpen s r).mem_nhds hw] with y hy
    have hd : DifferentiableAt ℂ P y := hP.holoP.differentiableAt ((kamDomain_isOpen s r).mem_nhds
        hy)
    have := hd.hasFDerivAt
    rwa [fderiv_eq_sympK ha hqq hP hy] at this
  have hx : HasFDerivAt (fun y => sympK (q := pb) (q' := p) ha hqq (X y))
      ((sympK (q := pb) (q' := p) ha hqq).comp (fderiv ℂ X w)) w :=
    (sympK (q := pb) (q' := p) ha hqq).hasFDerivAt.comp w hXd.hasFDerivAt
  have := second_derivative_symmetric_of_eventually (𝕜 := ℂ) hev hx u v
  simpa [sympK_apply] using this

theorem stepField_periodic (ha : 0 ≤ a) (hqq : 0 ≤ pb + p)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) (i : Fin 2) {w : KamPhase}
    (hw : w ∈ kamDomain s r) : X (w + stepTau i) = X w := by
  have hwτ := kamDomain_add_tau hw i
  have hfd : fderiv ℂ P (w + stepTau i) = fderiv ℂ P w := by
    have h1 : fderiv ℂ (fun z => P (z + stepTau i)) w = fderiv ℂ P (w + stepTau i) :=
      fderiv_comp_add_right (stepTau i)
    have h2 : (fun z => P (z + stepTau i)) =ᶠ[𝓝 w] P := by
      filter_upwards [(kamDomain_isOpen s r).mem_nhds hw] with z hz using hper i z hz
    rw [← h1, h2.fderiv_eq]
  rw [fderiv_eq_sympK ha hqq hP hwτ, fderiv_eq_sympK ha hqq hP hw] at hfd
  have key : ∀ W, stepSymp (q := pb) (q' := p) ha hqq (X (w + stepTau i) - X w) W = 0 := fun W => by
    have := congrArg (fun L => L W) hfd
    simp only [sympK_apply] at this
    rw [stepSymp_sub_left, this, sub_self]
  exact sub_eq_zero.mp (stepSymp_nondeg (q := pb) (q' := p) ha hqq (fun W => key W))

theorem fderiv_field_periodic (ha : 0 ≤ a) (hqq : 0 ≤ pb + p)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) (i : Fin 2) {w : KamPhase}
    (hw : w ∈ kamDomain s r) : fderiv ℂ X (w + stepTau i) = fderiv ℂ X w := by
  have h1 : fderiv ℂ (fun z => X (z + stepTau i)) w = fderiv ℂ X (w + stepTau i) :=
    fderiv_comp_add_right (stepTau i)
  have h2 : (fun z => X (z + stepTau i)) =ᶠ[𝓝 w] X := by
    filter_upwards [(kamDomain_isOpen s r).mem_nhds hw] with z hz using
      stepField_periodic ha hqq hP hper i hz
  rw [← h1, h2.fderiv_eq]

end KAM.Wave
