/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.PlanarAssembly.Boxes
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian

/-!
# Planar assembly: the total chart and the constant coupling family (Part 12)

Blueprint P, Part 12 (`bpP:p12:perturbation`, `bpP:p12:chart`): the total composition
`total_chart G m0 m T = poincareProd m (G m0) ∘ T` and the moving-Sun constant coupling family
`perturbation` on the existing total `fMov`; the conditional composition helpers
`chart_of_birkhoff` (analyticity and symplecticity of the composition) and
`chart_hamiltonian_of_preserves_fast` (the Hamiltonian identity for a fast-action preserving `T`).
No zero extension off the analytic domain is introduced.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function
open scoped BigOperators

namespace KAM.Planetary
open KAM KAM.Kepler

namespace PlanarAssembly

/-- No arbitrary zero extension: the existing total chart supplies a total composition. -/
def total_chart (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4) :
    Phase 4 → Phase 4 := poincareProd m (G * m0) ∘ T

/-- The moving-Sun constant coupling family, on the existing total fMov. -/
def perturbation (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4) :
    ℝ → Phase 4 → ℝ := fun _ z => fMov G m0 m (total_chart G m0 m T z)

/-- Conditional chart-composition helper, not a replacement for the source construction. -/
theorem chart_of_birkhoff {G m0 : ℝ} {m : Fin 2 → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {O : Set (Phase 4)}
    {T : Phase 4 → Phase 4} (hTan : AnalyticOnNhd ℝ T O)
    (hTs : IsSymplecticOn 1 T O) (hTm : MapsTo T O (poincareProdDom 2)) :
    AnalyticOnNhd ℝ (total_chart G m0 m T) O ∧
    IsSymplecticOn 1 (total_chart G m0 m T) O := by
  refine ⟨(analyticOnNhd_poincareProd hm hκ).comp hTan hTm, ?_⟩
  have h := IsSymplecticOn.comp hTs (poincareProd_symplectic hm hκ)
    (fun z hz => (hTan z hz).differentiableAt)
    (fun w hw => ((analyticOnNhd_poincareProd hm hκ) w hw).differentiableAt) hTm
  simpa [total_chart] using h

/-- Conditional Hamiltonian identity; fast-action preservation is supplied by 11b. -/
theorem chart_hamiltonian_of_preserves_fast {G m0 : ℝ} {m : Fin 2 → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {T : Phase 4 → Phase 4}
    {z : Phase 4} (hz : T z ∈ poincareProdDom 2)
    (hI : fast (a := 2) (b := 2) (T z).2 = (fast (a := 2) (b := 2) z.2 : Fin 2 → ℝ)) (μ : ℝ) :
    movingHamiltonian G m0 m μ (total_chart G m0 m T z) =
      degenerateHamiltonian (a := 2) (b := 2) (kepler_h (G * m0) m)
        (perturbation G m0 m T) μ z := by
  have hpc := product_chart (n := 2) (by norm_num) (G * m0) m hκ hm
  have h1 := movingHamiltonian_poincareProd (G := G) (m0 := m0) (μ := μ) hm hκ hz
  have h2 : hProd (G * m0) m (T z) = kepler_h (G * m0) m (fast (a := 2) (b := 2) z.2) := by
    rw [hpc.2.2.1 (T z), hI]
  unfold degenerateHamiltonian
  exact h1.trans (by rw [h2]; rfl)

end PlanarAssembly
end KAM.Planetary
end
