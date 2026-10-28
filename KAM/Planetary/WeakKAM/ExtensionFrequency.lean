/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.ExtensionStage

/-! # P11B finite extension: the real frequency map

For a function `h` holomorphic on an open set `A ⊆ ℂⁿ`, the real frequency map `frequencyMap h` is
the real part of the complex gradient at real points of `A`, and is smooth on the real points of
`A`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionReal_single (i : Fin n) :
    selectionReal (Pi.single i (1 : ℝ) : SelectionR n) = (Pi.single i 1 : SelectionC n) := by
  funext j
  by_cases hj : j = i <;> simp [selectionReal, hj]

theorem selectionFrequencyMap_apply {h : SelectionC n → ℂ} {A : Set (SelectionC n)}
    (hA : IsOpen A) (hh : DifferentiableOn ℂ h A) {y : SelectionR n}
    (hy : selectionReal y ∈ A) (i : Fin n) :
    frequencyMap h y i = (fderiv ℂ h (selectionReal y) (Pi.single i 1)).re := by
  have hd : HasFDerivAt h (fderiv ℂ h (selectionReal y)) (selectionReal y) :=
    ((hh.differentiableAt (hA.mem_nhds hy))).hasFDerivAt
  have hL := (selectionRealLI n).toContinuousLinearMap.hasFDerivAt (x := y)
  have h1 := Complex.reCLM.hasFDerivAt.comp y
    ((hd.restrictScalars ℝ).comp y hL)
  have h2 := h1.fderiv
  have e1 : (fun J : Fin n → ℝ => (h fun j => (J j : ℂ)).re) =
      Complex.reCLM ∘ h ∘ selectionReal := rfl
  have e2 : (selectionRealLI n).toContinuousLinearMap (Pi.single i 1) = Pi.single i 1 :=
    selectionReal_single i
  unfold frequencyMap
  rw [e1, h2]
  show Complex.reCLM (fderiv ℂ h (selectionReal y)
    ((selectionRealLI n).toContinuousLinearMap (Pi.single i 1))) = _
  rw [e2]
  rfl

theorem selectionFrequencyMap_contDiffOn {h : SelectionC n → ℂ} {A : Set (SelectionC n)}
    (hA : IsOpen A) (hh : DifferentiableOn ℂ h A) (m : ℕ) :
    ContDiffOn ℝ m (frequencyMap h) {y | selectionReal y ∈ A} := by
  have hAn : AnalyticOnNhd ℂ h A := analyticOnNhd_of_differentiableOn hA hh
  have hfd : ContDiffOn ℝ m (fun z => fderiv ℂ h z) A :=
    hAn.fderiv.restrictScalars.contDiffOn_of_completeSpace
  have hcomp : ContDiffOn ℝ m (fun y => fderiv ℂ h (selectionReal y))
      {y | selectionReal y ∈ A} :=
    hfd.comp (selectionRealLI n).toContinuousLinearMap.contDiff.contDiffOn fun y hy => hy
  have hG : ContDiffOn ℝ m (fun y => fun i : Fin n =>
      (fderiv ℂ h (selectionReal y) (Pi.single i 1)).re) {y | selectionReal y ∈ A} := by
    refine contDiffOn_pi.2 fun i => ?_
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1 : SelectionC n)).restrictScalars ℝ
        ).contDiff.comp_contDiffOn hcomp)
  refine hG.congr fun y hy => ?_
  funext i
  exact selectionFrequencyMap_apply hA hh hy i

end KAM.Planetary
