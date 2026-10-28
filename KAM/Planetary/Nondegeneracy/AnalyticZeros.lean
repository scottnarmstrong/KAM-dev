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
  have hP : MeasurableSet
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).symm ⁻¹' S) :=
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
  have hhan : AnalyticOnNhd ℝ h V :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Vec (d+1))).comp_analyticOnNhd hg.fderiv
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

/-! ### Taylor chains and the local statement -/

theorem exists_coord_deriv_ne {g : Vec d → ℝ} {x : Vec d} (hg : AnalyticAt ℝ g x)
    (hnf : ¬ g =ᶠ[𝓝 x] 0) :
    ∃ k : ℕ, ∃ i : Fin k → Fin d,
      iteratedFDeriv ℝ k g x (fun j => Pi.single (i j) (1:ℝ)) ≠ 0 := by
  by_contra H
  push Not at H
  have hzero : ∀ k, iteratedFDeriv ℝ k g x = 0 := by
    intro k
    ext m
    have hm : m = fun j => ∑ l, m j l • (Pi.single l (1:ℝ) : Vec d) := by
      funext j; ext l; simp [Finset.sum_apply, Pi.single_apply]
    rw [hm, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, H k r, smul_zero]
  obtain ⟨p, r, hr⟩ := hg
  apply hnf
  filter_upwards [Metric.eball_mem_nhds x hr.r_pos] with z hz
  have hy : z - x ∈ Metric.eball (0 : Vec d) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, edist_comm] using hz
  have hs := hr.hasSum hy
  have hp : ∀ n, p n (fun _ => z - x) = 0 := by
    intro n
    have h1 := hr.factorial_smul (z - x) n
    rw [hzero n] at h1
    have h2 : (n.factorial : ℕ) • p n (fun _ => z - x) = 0 := by simpa using h1
    exact (smul_eq_zero.mp h2).resolve_left (Nat.factorial_ne_zero n)
  simp only [hp] at hs
  simpa using (hasSum_zero.unique hs).symm

theorem local_null : ∀ (k : ℕ) (g : Vec d → ℝ) (U : Set (Vec d)), IsOpen U →
    AnalyticOnNhd ℝ g U → ∀ x ∈ U, ∀ i : Fin k → Fin d,
    iteratedFDeriv ℝ k g x (fun j => Pi.single (i j) (1:ℝ)) ≠ 0 →
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ volume {y ∈ V | g y = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro g U hU hg x hx i hne
    have hgx : g x ≠ 0 := by simpa [iteratedFDeriv_zero_apply] using hne
    have hev : U ∩ {y | g y ≠ 0} ∈ 𝓝 x :=
      inter_mem (hU.mem_nhds hx) ((hg x hx).continuousAt.eventually_ne hgx)
    obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hev
    refine ⟨V, hVo, hxV, fun y hy => (hVs hy).1, ?_⟩
    refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := volume))
    exact absurd hy.2 (hVs hy.1).2
  | succ k ih =>
    intro g U hU hg x hx i hne
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by have := (i (Fin.last k)).pos; omega⟩
    set j := i (Fin.last k) with hj
    set h : Vec (d'+1) → ℝ := fun y => fderiv ℝ g y (Pi.single j (1:ℝ)) with hh
    have hhan : AnalyticOnNhd ℝ h U :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1:ℝ) : Vec (d'+1))).comp_analyticOnNhd
        hg.fderiv
    have key : iteratedFDeriv ℝ (k+1) g x (fun l => Pi.single (i l) (1:ℝ)) =
        iteratedFDeriv ℝ k h x (fun l : Fin k => Pi.single (i l.castSucc) (1:ℝ)) := by
      rw [iteratedFDeriv_succ_apply_right]
      have h3 := ContinuousLinearMap.iteratedFDeriv_comp_left
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1:ℝ) : Vec (d'+1)))
        (n := k) ((hg.fderiv x hx).contDiffAt) (i := k) le_rfl
      have h4 : h = (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1:ℝ) : Vec (d'+1))) ∘
          fderiv ℝ g := rfl
      rw [h4, h3]
      rfl
    obtain ⟨V, hVo, hxV, hVU, hVn⟩ := ih h U hU hhan x hx (fun l => i l.castSucc)
      (key ▸ hne)
    exact ⟨V, hVo, hxV, hVU, null_zero_of_dir j hVo (hg.mono hVU) hVn⟩

/-! ### The measure-zero theorem and `generic` -/

theorem analytic_zero_null {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Vec d → ℝ} (hf : AnalyticOnNhd ℝ f B) (hne : ∃ x ∈ B, f x ≠ 0) :
    volume {x ∈ B | f x = 0} = 0 := by
  have hloc : ∀ x ∈ B, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ B ∧ volume {y ∈ V | f y = 0} = 0 := by
    intro x hx
    have hnf : ¬ f =ᶠ[𝓝 x] 0 := by
      intro h
      obtain ⟨y, hy, hy0⟩ := hne
      exact hy0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hx h hy)
    obtain ⟨k, i, hki⟩ := exists_coord_deriv_ne (hf x hx) hnf
    exact local_null k f B hB hf x hx i hki
  choose! V hVo hxV hVB hVn using hloc
  obtain ⟨t, htB, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := B) (f := V)
    fun x hx => mem_nhdsWithin_of_mem_nhds ((hVo x hx).mem_nhds (hxV x hx))
  refine measure_mono_null (fun y hy => ?_)
    ((measure_biUnion_null_iff htc).2 fun x hx => hVn x (htB hx))
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov hy.1)
  exact mem_iUnion₂.2 ⟨x, hx, hyx, hy.2⟩

theorem generic {r : ℕ} {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Fin r → Vec d → ℝ} (hf : ∀ j, AnalyticOnNhd ℝ (f j) B)
    (hne : ∀ j, ∃ x ∈ B, f j x ≠ 0) :
    IsOpen {x ∈ B | ∀ j, f j x ≠ 0} ∧
    B ⊆ closure {x ∈ B | ∀ j, f j x ≠ 0} ∧
    volume {x ∈ B | ∃ j, f j x = 0} = 0 := by
  have hnull : volume {x ∈ B | ∃ j, f j x = 0} = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null fun j => analytic_zero_null hB hBc (hf j) (hne j))
    obtain ⟨j, hj⟩ := hx.2
    exact mem_iUnion.2 ⟨j, hx.1, hj⟩
  have hopen : IsOpen {x ∈ B | ∀ j, f j x ≠ 0} := by
    have : {x ∈ B | ∀ j, f j x ≠ 0} = B ∩ ⋂ j, (B ∩ f j ⁻¹' {0}ᶜ) :=
      Set.ext fun x => ⟨fun ⟨hx, h⟩ => ⟨hx, mem_iInter.2 fun j => ⟨hx, h j⟩⟩,
        fun ⟨hx, h⟩ => ⟨hx, fun j => (mem_iInter.1 h j).2⟩⟩
    rw [this]
    exact hB.inter (isOpen_iInter_of_finite fun j =>
      (hf j).continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton)
  refine ⟨hopen, fun x hx => ?_, hnull⟩
  rw [_root_.mem_closure_iff]
  intro W hW hxW
  by_contra hempty
  have hsub : W ∩ B ⊆ {x ∈ B | ∃ j, f j x = 0} := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    by_contra hall
    push Not at hall
    exact hempty ⟨y, hy.1, hy.2, hall⟩
  have := measure_mono_null hsub hnull
  exact (hW.inter hB).measure_pos volume ⟨x, hxW, hx⟩ |>.ne' this

end Nondegeneracy
end KAM.Planetary
end
