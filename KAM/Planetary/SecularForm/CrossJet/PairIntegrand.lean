/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.CrossJet.Parametric
public import KAM.Planetary.SecularForm.CrossJet.Variation

/-!
# Cross jet: the pair integrand on the slice

Blueprint P, Part 8, `stepP:p8:qf-cross`: the integrand `-c/|q₁ - q₂|` of the literal pair average, as a function
of the two angles and the two slow parameters `ξ₁, ξ₂` (with `η = 0`), its open domain and analyticity.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm

/-- The two-planet block `(λ_k, ξ_k = s_k, Λ, η = 0)` read off the slice point `(t, y)`. -/
def sliceBlock (I : ℝ) (k : Fin 2) (p : Vec 2 × Vec 2) : Phase 2 :=
  (![p.1 k, p.2 k], ![I, 0])

theorem contDiff_sliceBlock (I : ℝ) (k : Fin 2) : ContDiff ℝ ω (sliceBlock I k) := by
  unfold sliceBlock
  refine ContDiff.prodMk ?_ contDiff_const
  rw [contDiff_pi]
  intro c
  fin_cases c
  · show ContDiff ℝ ω (fun x : Vec 2 × Vec 2 => x.1 k)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp (contDiff_fst (E := Vec 2) (F := Vec 2))
  · show ContDiff ℝ ω (fun x : Vec 2 × Vec 2 => x.2 k)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).contDiff.comp (contDiff_snd (E := Vec 2) (F := Vec 2))

/-- The pair integrand `-c/|q₁ - q₂|` along the slice. -/
def pairIntegrand (c m₁ m₂ κ I₁ I₂ : ℝ) (p : Vec 2 × Vec 2) : ℝ :=
  -c / planeLength ((poincare m₁ κ (sliceBlock I₁ 0 p)).1 - (poincare m₂ κ (sliceBlock I₂ 1 p)).1)

/-- Open set of slice points where both blocks are in the chart and the planets are apart. -/
def pairDom (m₁ m₂ κ I₁ I₂ : ℝ) : Set (Vec 2 × Vec 2) :=
  {p | sliceBlock I₁ 0 p ∈ poincareDom ∧ sliceBlock I₂ 1 p ∈ poincareDom ∧
    (poincare m₁ κ (sliceBlock I₁ 0 p)).1 - (poincare m₂ κ (sliceBlock I₂ 1 p)).1 ≠ 0}

theorem isOpen_pairDom {m₁ m₂ κ I₁ I₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hκ : 0 < κ) :
    IsOpen (pairDom m₁ m₂ κ I₁ I₂) := by
  have h1 : IsOpen ((sliceBlock I₁ 0) ⁻¹' poincareDom) :=
    isOpen_poincareDom.preimage (contDiff_sliceBlock I₁ 0).continuous
  have h2 : IsOpen ((sliceBlock I₂ 1) ⁻¹' poincareDom) :=
    isOpen_poincareDom.preimage (contDiff_sliceBlock I₂ 1).continuous
  have hcont : ContinuousOn (fun p => (poincare m₁ κ (sliceBlock I₁ 0 p)).1 -
      (poincare m₂ κ (sliceBlock I₂ 1 p)).1) ((sliceBlock I₁ 0) ⁻¹' poincareDom ∩
        (sliceBlock I₂ 1) ⁻¹' poincareDom) := by
    refine ContinuousOn.sub ?_ ?_
    · exact ((analyticOnNhd_poincare hm₁ hκ).continuousOn.comp
        (contDiff_sliceBlock I₁ 0).continuous.continuousOn (fun p hp => hp.1)).fst
    · exact ((analyticOnNhd_poincare hm₂ hκ).continuousOn.comp
        (contDiff_sliceBlock I₂ 1).continuous.continuousOn (fun p hp => hp.2)).fst
  have := hcont.isOpen_inter_preimage (h1.inter h2) (isOpen_ne (x := (0 : Fin 2 → ℝ)))
  convert this using 1
  ext p
  simp [pairDom, and_assoc]

theorem contDiffOn_pairIntegrand {c m₁ m₂ κ I₁ I₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hκ : 0 < κ) :
    ContDiffOn ℝ ω (pairIntegrand c m₁ m₂ κ I₁ I₂) (pairDom m₁ m₂ κ I₁ I₂) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hA : ContDiffAt ℝ ω (fun p => (poincare m₁ κ (sliceBlock I₁ 0 p)).1) p :=
    (((analyticOnNhd_poincare hm₁ hκ _ h1).contDiffAt).comp p
      (contDiff_sliceBlock I₁ 0).contDiffAt).fst
  have hB : ContDiffAt ℝ ω (fun p => (poincare m₂ κ (sliceBlock I₂ 1 p)).1) p :=
    (((analyticOnNhd_poincare hm₂ hκ _ h2).contDiffAt).comp p
      (contDiff_sliceBlock I₂ 1).contDiffAt).fst
  have hL := (analyticAt_planeLength h3).contDiffAt (n := ω)
  exact contDiffAt_const.div (ContDiffAt.comp (g := planeLength) p hL (hA.sub hB))
    (planeLength_pos_iff.mpr h3).ne'

end SecularForm
end KAM.Planetary
