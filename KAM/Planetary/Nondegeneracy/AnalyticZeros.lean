/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Nondegeneracy: zero sets of real-analytic functions

Blueprint P, Part 9-10 (`bpP:p10:rnd-def`, `bpP:p9:e-id`, `bpP:p10:generic`): the source definition
`rnd_def` of R-nondegeneracy, the measure-zero theorem `analytic_zero_null` for the zero set of a
real-analytic function on a connected open set that is not identically zero, and the finite
common-nonzero-locus statement `generic`.

The proof of `analytic_zero_null` is local.  Near a point where `f` is not identically zero the
Taylor series gives a chain of coordinate derivatives `∂_{i_k} ⋯ ∂_{i_1} f` that is nonzero at the
point; going down the chain, `Nondegeneracy.null_zero_of_dir` (isolated zeros along lines plus
Fubini) transfers measure-zero of the zero set from `∂_i g` to `g`.  Connectedness and the identity
theorem exclude local flatness, and second countability gives a countable cover.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
open TopologicalSpace
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm
variable {d m : ℕ}

/-- Source definition, not a package of consequences. -/
def rnd_def (B : Set (Vec d)) (ω : Vec d → Vec m) : Prop :=
  ∀ c : Vec m, c ≠ 0 → ∃ y ∈ B, ∑ i, c i*ω y i ≠ 0

/-! ### One variable -/

theorem countable_of_isolated {Z : Set ℝ}
    (h : ∀ t ∈ Z, ∃ U ∈ 𝓝 t, ∀ s ∈ U, s ∈ Z → s = t) : Z.Countable := by
  have : DiscreteTopology Z := by
    rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨t, ht⟩
    obtain ⟨U, hU, hU'⟩ := h t ht
    rw [isOpen_induced_iff]
    refine ⟨interior U, isOpen_interior, ?_⟩
    ext ⟨s, hs⟩
    simp only [mem_preimage, mem_singleton_iff, Subtype.mk.injEq]
    constructor
    · intro hs'
      exact hU' s (interior_subset hs') hs
    · rintro rfl
      exact mem_interior_iff_mem_nhds.2 hU
  exact Set.countable_coe_iff.1 (separableSpace_iff_countable.1 inferInstance)

theorem null_zero_of_deriv {A : Set ℝ} {G G' : ℝ → ℝ}
    (hG : ∀ t ∈ A, HasDerivAt G (G' t) t) (h0 : volume {t ∈ A | G' t = 0} = 0) :
    volume {t ∈ A | G t = 0} = 0 := by
  have hc : {t | t ∈ A ∧ G t = 0 ∧ G' t ≠ 0}.Countable := by
    apply countable_of_isolated
    rintro t ⟨htA, ht0, htd⟩
    have h0 := ((hG t htA).hasDerivWithinAt (s := univ)).tendsto_nhdsWithin_nhdsNE htd
    simp only [← compl_eq_univ_sdiff] at h0
    have h1 : ∀ᶠ z in 𝓝[≠] t, G z ≠ G t := h0.eventually eventually_mem_nhdsWithin
    rw [eventually_nhdsWithin_iff] at h1
    refine ⟨_, h1, ?_⟩
    rintro s hs ⟨_, hs0, _⟩
    by_contra hne
    exact hs hne (by rw [hs0, ht0])
  refine measure_mono_null ?_ (measure_union_null h0 (hc.measure_zero volume))
  intro t ⟨htA, ht0⟩
  by_cases hd : G' t = 0
  · exact Or.inl ⟨htA, hd⟩
  · exact Or.inr ⟨htA, ht0, hd⟩

/-! ### Fubini along a coordinate line -/

/-- The point of the coordinate line through `y` in direction `i` at parameter `t`. -/
abbrev lineAt (i : Fin (d+1)) (y : Vec d) (t : ℝ) : Vec (d+1) := Fin.insertNth i t y

theorem insertNth_eq_add (i : Fin (d+1)) (t : ℝ) (y : Vec d) :
    lineAt i y t = lineAt i y 0 + t • Pi.single i 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp

theorem volume_null_iff_lines (i : Fin (d+1)) {S : Set (Vec (d+1))} (hS : MeasurableSet S) :
    volume S = 0 ↔ ∀ᵐ y : Vec d ∂volume, volume {t : ℝ | lineAt i y t ∈ S} = 0 := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).symm
  have hP : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).symm ⁻¹' S) :=
    (MeasurableEquiv.measurable _) hS
  have h1 : volume S = (volume : Measure (ℝ × Vec d))
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).symm ⁻¹' S) :=
    (hmp.measure_preimage hS.nullMeasurableSet).symm
  rw [h1, show (volume : Measure (ℝ × Vec d)) = volume.prod volume from rfl,
    Measure.prod_apply_symm hP, lintegral_eq_zero_iff (measurable_measure_prodMk_right hP)]
  refine Iff.trans Iff.rfl (eventually_congr (Eventually.of_forall fun y => ?_))
  exact Iff.rfl

theorem measurableSet_zero_inter {V : Set (Vec d)} (hV : IsOpen V) {g : Vec d → ℝ}
    (hg : ContinuousOn g V) : MeasurableSet {x ∈ V | g x = 0} := by
  have : {x ∈ V | g x = 0} = V \ (V ∩ g ⁻¹' {0}ᶜ) := by
    ext x; simp
  rw [this]
  exact hV.measurableSet.diff (hg.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet

/-- If the directional derivative `∂_i g` has null zero set in an open `V`, so has `g`. -/
theorem null_zero_of_dir (i : Fin (d+1)) {V : Set (Vec (d+1))} (hV : IsOpen V)
    {g : Vec (d+1) → ℝ} (hg : AnalyticOnNhd ℝ g V)
    (h0 : volume {x ∈ V | fderiv ℝ g x (Pi.single i 1) = 0} = 0) :
    volume {x ∈ V | g x = 0} = 0 := by
  set h : Vec (d+1) → ℝ := fun x => fderiv ℝ g x (Pi.single i 1) with hh
  have hhan : AnalyticOnNhd ℝ h V := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Vec (d+1))).comp_analyticOnNhd hg.fderiv
  have hT := measurableSet_zero_inter hV hhan.continuousOn
  have hS := measurableSet_zero_inter hV hg.continuousOn
  rw [volume_null_iff_lines i hT] at h0
  rw [volume_null_iff_lines i hS]
  filter_upwards [h0] with y hy
  have hder : ∀ t ∈ {t : ℝ | lineAt i y t ∈ V},
      HasDerivAt (fun t => g (lineAt i y t)) (h (lineAt i y t)) t := by
    intro t ht
    have hin : HasDerivAt (fun t : ℝ => lineAt i y t) (Pi.single i 1) t := by
      have hfun : (fun t : ℝ => lineAt i y t) = fun t => lineAt i y 0 + t • Pi.single i 1 :=
        funext fun t => insertNth_eq_add i t y
      rw [hfun]
      simpa using ((hasDerivAt_id t).smul_const (Pi.single i (1:ℝ) : Vec (d+1))).const_add
        (lineAt i y 0)
    exact (hg _ ht).differentiableAt.hasFDerivAt.comp_hasDerivAt t hin
  exact null_zero_of_deriv hder hy

end Nondegeneracy
end KAM.Planetary
end
