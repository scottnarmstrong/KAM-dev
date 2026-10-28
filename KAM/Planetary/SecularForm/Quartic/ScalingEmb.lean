/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.ScalingComplex

/-!
# Secular form: the real parameters inside `ℂ⁵`

The embedding `qscEmb` as a continuous real-linear map, and openness of `separatedDomain`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- `qscEmb` as a real-linear map. -/
def qscEmbLM : (ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) →ₗ[ℝ] (Fin 5 → ℂ) where
  toFun := qscEmb
  map_add' x y := by
    funext i; fin_cases i <;> simp [qscEmb]
  map_smul' c x := by
    funext i; fin_cases i <;> simp [qscEmb]

/-- `qscEmb` as a continuous real-linear map. -/
def qscEmbCLM : (ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) →L[ℝ] (Fin 5 → ℂ) :=
  LinearMap.toContinuousLinearMap qscEmbLM

theorem qscEmbCLM_apply (y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) : qscEmbCLM y = qscEmb y := rfl

theorem qsc_isOpen_separatedDomain : IsOpen separatedDomain := by
  have h1 : Continuous fun z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) => planeLength z.2.1 :=
    qsc_continuous_planeLength.comp (continuous_fst.comp continuous_snd)
  have h2 : Continuous fun z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) => planeLength z.2.2 :=
    qsc_continuous_planeLength.comp (continuous_snd.comp continuous_snd)
  have h3 : Continuous fun z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) => z.1 := continuous_fst
  unfold separatedDomain
  simp only [Set.ofPred_and]
  refine (isOpen_lt continuous_const h3).inter ((isOpen_lt h3 continuous_const).inter
    ((isOpen_lt h1 continuous_const).inter ((isOpen_lt h2 continuous_const).inter
    (isOpen_lt (by fun_prop) (by fun_prop)))))

end SecularForm
end KAM.Planetary
end
