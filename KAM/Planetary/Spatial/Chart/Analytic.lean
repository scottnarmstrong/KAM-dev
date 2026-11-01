/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Chart.Defs

/-!
# The regular spatial Poincare chart: analyticity and `2π`-periodicity

Package LP-SP-CHART, `LP:MAIN L17 (533–578)`, track LP, non-frozen. Item 4: `spatialPoincare ν`
is real analytic on (44) (the planar chart is analytic through `ξ = η = 0`, the rotation `R`
through `Z = 0`) and `2π`-periodic in `λ`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Matrix Real
open scoped ContDiff

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

private theorem an_fst (i : Fin 3) (w : Phase 3) :
    AnalyticAt ℝ (fun w : Phase 3 => w.1 i) w :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))).analyticAt w

private theorem an_snd (i : Fin 3) (w : Phase 3) :
    AnalyticAt ℝ (fun w : Phase 3 => w.2 i) w :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))).analyticAt w

theorem analyticAt_spatialAngMom (w : Phase 3) : AnalyticAt ℝ spatialAngMom w := by
  unfold spatialAngMom spatialGamma
  exact (an_snd 0 w).sub ((((an_fst 1 w).pow 2).add ((an_snd 1 w).pow 2)).div_const)

theorem analyticAt_spatialPlanar (w : Phase 3) : AnalyticAt ℝ spatialPlanar w := by
  have e : (⇑spatialPlanarCLM) = spatialPlanar := funext spatialPlanarCLM_apply
  rw [← e]; exact spatialPlanarCLM.analyticAt w

theorem analyticAt_spatialRot_apply {w : Phase 3} (hw : w ∈ spatialPoincareDom) (i j : Fin 3) :
    AnalyticAt ℝ (fun w' : Phase 3 => spatialRot w' i j) w := by
  have hf : AnalyticAt ℝ (fun w' : Phase 3 => (w'.2 2, w'.1 2, spatialAngMom w')) w :=
    (an_snd 2 w).prod ((an_fst 2 w).prod (analyticAt_spatialAngMom w))
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ × ℝ => incRotation p.1 p.2.1 p.2.2 i j)
    (f := fun w' : Phase 3 => (w'.2 2, w'.1 2, spatialAngMom w')) (x := w)
    (incRotation_analyticOn i j (w.2 2, w.1 2, spatialAngMom w) (spatial_mem_incCarrier hw)) hf

private theorem analyticAt_rot_embed {w : Phase 3} {M : Phase 3 → Matrix (Fin 3) (Fin 3) ℝ}
    {f : Phase 3 → Fin 2 → ℝ} (hM : ∀ i j, AnalyticAt ℝ (fun w' => M w' i j) w)
    (hf : AnalyticAt ℝ f w) : AnalyticAt ℝ (fun w' => M w' *ᵥ planarEmbed (f w')) w := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have h0 := analyticAt_pi_iff.1 hf 0
  have h1 := analyticAt_pi_iff.1 hf 1
  have e : (fun w' => (M w' *ᵥ planarEmbed (f w')) i) =
      fun w' => M w' i 0 * f w' 0 + M w' i 1 * f w' 1 := by
    funext w'; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, planarEmbed]
  rw [e]; exact ((hM i 0).mul h0).add ((hM i 1).mul h1)

/-- The planar chart composed with `spatialPlanar` is analytic on (44). -/
theorem analyticAt_poincare_spatialPlanar {ν : ℝ} (hν : 0 < ν) {w : Phase 3}
    (hw : w ∈ spatialPoincareDom) :
    AnalyticAt ℝ (fun w' : Phase 3 => poincare ν 1 (spatialPlanar w')) w :=
  (analyticOnNhd_poincare hν one_pos _ (spatialPlanar_mem hw)).comp (analyticAt_spatialPlanar w)

/-- Item 4: `spatialPoincare ν` is real analytic on (44). -/
theorem analyticOnNhd_spatialPoincare {ν : ℝ} (hν : 0 < ν) :
    AnalyticOnNhd ℝ (spatialPoincare ν) spatialPoincareDom := by
  intro w hw
  have hP := analyticAt_poincare_spatialPlanar hν hw
  have hM := analyticAt_spatialRot_apply hw
  have h1 : AnalyticAt ℝ (fun w' : Phase 3 => (poincare ν 1 (spatialPlanar w')).1) w :=
    analyticAt_fst.comp hP
  have h2 : AnalyticAt ℝ (fun w' : Phase 3 => (poincare ν 1 (spatialPlanar w')).2) w :=
    analyticAt_snd.comp hP
  exact (analyticAt_rot_embed hM h1).prod (analyticAt_rot_embed hM h2)

/-- The shift `λ ↦ λ + 2πk` of a chart point. -/
def spatialShift (k : ℤ) (w : Phase 3) : Phase 3 :=
  (![w.1 0 + 2 * π * k, w.1 1, w.1 2], w.2)

/-- Item 4: `2π`-periodicity in `λ`. -/
theorem spatialPoincare_periodic {ν : ℝ} (hν : 0 < ν) {w : Phase 3}
    (hw : w ∈ spatialPoincareDom) (k : ℤ) :
    spatialPoincare ν (spatialShift k w) = spatialPoincare ν w := by
  have hp := spatialPlanar_mem hw
  have h := poincare_periodic hν one_pos hp k
  have e : spatialPlanar (spatialShift k w) =
      (![(spatialPlanar w).1 0 + 2 * π * k, (spatialPlanar w).1 1], (spatialPlanar w).2) := by
    simp [spatialPlanar, spatialShift]
  have hR : spatialRot (spatialShift k w) = spatialRot w := by
    simp [spatialRot, spatialAngMom, spatialGamma, spatialShift]
  unfold spatialPoincare
  rw [e, h, hR]

theorem spatialShift_mem {w : Phase 3} (hw : w ∈ spatialPoincareDom) (k : ℤ) :
    spatialShift k w ∈ spatialPoincareDom := by
  refine ⟨hw.1, ?_⟩
  have := hw.2
  simpa [spatialShift, spatialGamma, spatialZ] using this

end KAM.Planetary.Spatial
