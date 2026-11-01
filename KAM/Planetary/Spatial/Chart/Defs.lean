/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Chart
public import KAM.Planetary.Spatial.Rotation46

/-!
# The regular spatial Poincare chart for one body: definitions and well-definedness

Package LP-SP-CHART, `LP:MAIN L17 (533–578)`, track LP, non-frozen.

**Coordinates.** A point of the chart domain is `w : Phase 3 = (Fin 3 → ℝ) × (Fin 3 → ℝ)` with
`w.1 = (λ, ξ, v)` ("angle" slots) and `w.2 = (I, η, u)` ("action" slots). The repository's
`symplecticForm` on `Phase 3` is `dI ∧ dλ + dη ∧ dξ + du ∧ dv` for this slot order, which is
the form of MAIN (Lemma 17) for the planar chart in the repository convention
`(ξ, η) = (x, −y)` (see `KAM/Planetary/Poincare`) and the same `(u, v)` as in MAIN (46).

* `spatialPoincareDom` is (44): `I > 0` and `Γ + Z < I`.
* `spatialPoincare ν w = (R·(Q, 0), R·(P, 0))` is (46), with `(Q, P)` the planar chart
  `poincare ν 1` at `(λ, ξ; I, η)` and `R = incRotation u v G`, `G = I − Γ`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Matrix
open scoped ContDiff

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

/-- `Γ = (ξ² + η²)/2` of the chart point `w`. -/
def spatialGamma (w : Phase 3) : ℝ := (w.1 1 ^ 2 + w.2 1 ^ 2) / 2

/-- `Z = (u² + v²)/2` of the chart point `w`, with `u = w.2 2`, `v = w.1 2`. -/
def spatialZ (w : Phase 3) : ℝ := (w.2 2 ^ 2 + w.1 2 ^ 2) / 2

/-- `G = I − Γ`. -/
def spatialAngMom (w : Phase 3) : ℝ := w.2 0 - spatialGamma w

/-- The planar part `(λ, ξ; I, η)` of the chart point, as a point of `Phase 2`. -/
def spatialPlanar (w : Phase 3) : Phase 2 := (![w.1 0, w.1 1], ![w.2 0, w.2 1])

/-- The linear map `w ↦ (λ, ξ; I, η)` onto `Phase 2`, as a continuous linear map. -/
def spatialPlanarCLM : Phase 3 →L[ℝ] Phase 2 :=
  ContinuousLinearMap.prod
    ((ContinuousLinearMap.pi fun i : Fin 2 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i.castSucc).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))))
    ((ContinuousLinearMap.pi fun i : Fin 2 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i.castSucc).comp
        (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))))

lemma spatialPlanarCLM_apply (w : Phase 3) : spatialPlanarCLM w = spatialPlanar w := by
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [spatialPlanarCLM, spatialPlanar]

/-- MAIN (44): `I > 0` and `Γ + Z < I`. -/
def spatialPoincareDom : Set (Phase 3) :=
  {w | 0 < w.2 0 ∧ spatialGamma w + spatialZ w < w.2 0}

/-- The rotation `R = incRotation u v G` of (46) at the chart point `w`. -/
def spatialRot (w : Phase 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  incRotation (w.2 2) (w.1 2) (spatialAngMom w)

/-- MAIN (46), literally: `q = R·(Q, 0)`, `p = R·(P, 0)` with
`(Q, P) = poincare ν 1 (λ, ξ; I, η)`. -/
def spatialPoincare (ν : ℝ) (w : Phase 3) : Phase 3 :=
  (spatialRot w *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).1,
   spatialRot w *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).2)

/-- Kepler energy `|p|²/(2ν) − ν/|q|` of a spatial state (`κ = 1`, the planar convention
`energyMK ν 1`). -/
def spatialEnergy (ν : ℝ) (z : Phase 3) : ℝ :=
  (z.2 ⬝ᵥ z.2) / (2 * ν) - ν / Real.sqrt (z.1 ⬝ᵥ z.1)

/-- The negative-energy spatial states with `(q ⨯₃ p) ⬝ᵥ e₃ > 0` (the image of (44)). -/
def spatialRegion (ν : ℝ) : Set (Phase 3) :=
  {z | spatialEnergy ν z < 0 ∧ 0 < (z.1 ⨯₃ z.2) ⬝ᵥ e₃}

section Domain

variable {w : Phase 3}

lemma spatialGamma_nonneg (w : Phase 3) : 0 ≤ spatialGamma w := by
  unfold spatialGamma; positivity

lemma spatialZ_nonneg (w : Phase 3) : 0 ≤ spatialZ w := by
  unfold spatialZ; positivity

/-- Item 1: on (44), `G > 0`. -/
theorem spatialAngMom_pos (hw : w ∈ spatialPoincareDom) : 0 < spatialAngMom w := by
  have := spatialZ_nonneg w
  have := hw.2
  unfold spatialAngMom; linarith

/-- Item 1: on (44), `Z < G`. -/
theorem spatialZ_lt_angMom (hw : w ∈ spatialPoincareDom) : spatialZ w < spatialAngMom w := by
  have := hw.2
  unfold spatialAngMom; linarith

/-- Item 1: the carrier hypotheses of LP-SP-ROT in the form `(u² + v²)/2 < G`. -/
theorem spatial_carrier (hw : w ∈ spatialPoincareDom) :
    0 < spatialAngMom w ∧ (w.2 2 ^ 2 + w.1 2 ^ 2) / 2 < spatialAngMom w :=
  ⟨spatialAngMom_pos hw, spatialZ_lt_angMom hw⟩

/-- Item 1: `(u, v, G)` lies in the LP-SP-ROT carrier. -/
theorem spatial_mem_incCarrier (hw : w ∈ spatialPoincareDom) :
    (w.2 2, w.1 2, spatialAngMom w) ∈ incCarrier :=
  spatial_carrier hw

/-- Item 1: the planar point lies in `poincareDom`. -/
theorem spatialPlanar_mem (hw : w ∈ spatialPoincareDom) : spatialPlanar w ∈ poincareDom := by
  have hZ := spatialZ_nonneg w
  refine ⟨hw.1, ?_⟩
  have h : poincareGamma (spatialPlanar w) = spatialGamma w := by
    simp [poincareGamma, spatialPlanar, spatialGamma]
  show poincareGamma (spatialPlanar w) < w.2 0
  rw [h]; have := hw.2; linarith

theorem spatialPlanar_gamma (w : Phase 3) : poincareGamma (spatialPlanar w) = spatialGamma w := by
  simp [poincareGamma, spatialPlanar, spatialGamma]

theorem isOpen_spatialPoincareDom : IsOpen spatialPoincareDom := by
  have h1 : Continuous fun w : Phase 3 => w.2 0 := by fun_prop
  have h2 : Continuous fun w : Phase 3 => spatialGamma w + spatialZ w := by
    unfold spatialGamma spatialZ; fun_prop
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt h2 h1)

end Domain

end KAM.Planetary.Spatial
