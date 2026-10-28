/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.LocalDependence
public import KAM.ODE.Maximal

/-!
# Local regularity of a family of maximal solutions, and its chaining (generic)

Helper module of `KAM.Nekhoroshev.Averaging.FlowRegular` (blueprint N Part 12, `bpN:p12:flow`,
`stepN:p12:fl-short`, `stepN:p12:fl-chain`).

For a `C¹` field `F` on an open set `W` of a finite-dimensional real space and a family `z x` of
maximal solutions through the points `x ∈ W`, `RegOn F W Tm Tp z J U` records that on the product
`J × U` the flow lies in the maximal intervals, is jointly continuous, has jointly continuous
`x`-derivative, and that this derivative solves the variational equation in time.

* `FlowChain.regOn_comp`: a local flow `y` (from `ext_dep`) composed with a regular map.
* `FlowChain.shift_sol`: time shift of a maximal solution by another solution.
* `FlowChain.regOn_extend`: extension of a regular time interval by one local-flow slab.
* `FlowChain.reg_forward`: regularity on a neighborhood of each point `(T, x)` with `T ≥ 0`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology
open KAM.ODE (IsSolutionIn IsMaximalSolution eIoo)

namespace KAM.Nekhoroshev.FlowChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Regularity of the family `z` of maximal solutions on `J × U`. -/
def RegOn (F : E → E) (W : Set E) (Tm Tp : E → EReal) (z : E → ℝ → E) (J : Set ℝ)
    (U : Set E) : Prop :=
  U ⊆ W ∧ (∀ x ∈ U, J ⊆ eIoo (Tm x) (Tp x)) ∧
    ContinuousOn (fun q : ℝ × E => z q.2 q.1) (J ×ˢ U) ∧
    ContinuousOn (fun q : ℝ × E => fderiv ℝ (fun y => z y q.1) q.2) (J ×ˢ U) ∧
    ∀ x ∈ U, ∀ s ∈ J, HasFDerivAt (fun y => z y s) (fderiv ℝ (fun y => z y s) x) x ∧
      HasDerivAt (fun u => fderiv ℝ (fun y => z y u) x)
        ((fderiv ℝ F (z x s)).comp (fderiv ℝ (fun y => z y s) x)) s

section Basic

variable {F : E → E} {W : Set E} {Tm Tp : E → EReal} {z : E → ℝ → E}

theorem RegOn.mono {J J' : Set ℝ} {U U' : Set E} (h : RegOn F W Tm Tp z J U) (hJ : J' ⊆ J)
    (hU : U' ⊆ U) : RegOn F W Tm Tp z J' U' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨hU.trans h1, fun x hx => hJ.trans (h2 x (hU hx)),
    h3.mono (prod_mono hJ hU), h4.mono (prod_mono hJ hU),
    fun x hx s hs => h5 x (hU hx) s (hJ hs)⟩

theorem RegOn.union {J₁ J₂ : Set ℝ} {U : Set E} (hU : IsOpen U) (hJ₁ : IsOpen J₁)
    (hJ₂ : IsOpen J₂) (h₁ : RegOn F W Tm Tp z J₁ U) (h₂ : RegOn F W Tm Tp z J₂ U) :
    RegOn F W Tm Tp z (J₁ ∪ J₂) U := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨a1, fun x hx => union_subset (a2 x hx) (b2 x hx), ?_, ?_, fun x hx s hs => ?_⟩
  · rw [union_prod]
    exact a3.union_of_isOpen b3 (hJ₁.prod hU) (hJ₂.prod hU)
  · rw [union_prod]
    exact a4.union_of_isOpen b4 (hJ₁.prod hU) (hJ₂.prod hU)
  · rcases hs with hs | hs
    · exact a5 x hx s hs
    · exact b5 x hx s hs

end Basic

section Comp

variable {F : E → E} {W : Set E} {Tm Tp : E → EReal} {z : E → ℝ → E}

/-- A local flow `y` composed with a regular map `g` (with derivative `g'`) gives `RegOn`. -/
theorem regOn_comp {U : Set E} (hU : IsOpen U) (hUW : U ⊆ W) {g : E → E} {g' : E → E →L[ℝ] E}
    (hg : ∀ x ∈ U, HasFDerivAt g (g' x) x) (hg' : ContinuousOn g' U) {x₀ : E} {a r : ℝ}
    {y : ℝ → E → E}
    (hyc : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Ioo (-a) a ×ˢ ball x₀ r))
    (hyd : ContinuousOn (fun p : ℝ × E => fderiv ℝ (y p.1) p.2) (Ioo (-a) a ×ˢ ball x₀ r))
    (hyF : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-a) a, HasFDerivAt (y t) (fderiv ℝ (y t) x) x)
    (hyt : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-a) a, HasDerivAt (fun τ => fderiv ℝ (y τ) x)
      ((fderiv ℝ F (y t x)).comp (fderiv ℝ (y t) x)) t)
    (hgb : ∀ x ∈ U, g x ∈ ball x₀ r) {T : ℝ}
    (hz : ∀ x ∈ U, ∀ u ∈ Ioo (T - a) (T + a), u ∈ eIoo (Tm x) (Tp x) ∧ z x u = y (u - T) (g x)) :
    RegOn F W Tm Tp z (Ioo (T - a) (T + a)) U := by
  have hm : ∀ u ∈ Ioo (T - a) (T + a), u - T ∈ Ioo (-a) a := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hev : ∀ x ∈ U, ∀ u ∈ Ioo (T - a) (T + a),
      (fun x' => z x' u) =ᶠ[𝓝 x] (y (u - T) ∘ g) := fun x hx u hu =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun x' hx' => (hz x' hx' u hu).2
  have hfd : ∀ x ∈ U, ∀ u ∈ Ioo (T - a) (T + a),
      HasFDerivAt (fun x' => z x' u)
        ((fderiv ℝ (y (u - T)) (g x)).comp (g' x)) x := fun x hx u hu =>
    (((hyF (g x) (hgb x hx) (u - T) (hm u hu)).comp x (hg x hx))).congr_of_eventuallyEq
      (hev x hx u hu)
  have hgc : ContinuousOn g U := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hmaps : MapsTo (fun q : ℝ × E => (q.1 - T, g q.2)) (Ioo (T - a) (T + a) ×ˢ U)
      (Ioo (-a) a ×ˢ ball x₀ r) := fun q hq => ⟨hm _ hq.1, hgb _ hq.2⟩
  have hcont : ContinuousOn (fun q : ℝ × E => (q.1 - T, g q.2))
      (Ioo (T - a) (T + a) ×ˢ U) :=
    ((continuous_fst.sub continuous_const).continuousOn).prodMk
      (hgc.comp continuous_snd.continuousOn fun q hq => hq.2)
  refine ⟨hUW, fun x hx u hu => (hz x hx u hu).1, ?_, ?_, fun x hx s hs => ?_⟩
  · refine (hyc.comp hcont hmaps).congr fun q hq => ?_
    exact (hz q.2 hq.2 q.1 hq.1).2
  · have h1 : ContinuousOn (fun q : ℝ × E => (fderiv ℝ (y (q.1 - T)) (g q.2)).comp (g' q.2))
        (Ioo (T - a) (T + a) ×ˢ U) :=
      (hyd.comp hcont hmaps).clm_comp
        (hg'.comp continuous_snd.continuousOn fun q hq => hq.2)
    refine h1.congr fun q hq => ?_
    exact (hfd q.2 hq.2 q.1 hq.1).fderiv
  · have hD : fderiv ℝ (fun y => z y s) x = (fderiv ℝ (y (s - T)) (g x)).comp (g' x) :=
      (hfd x hx s hs).fderiv
    refine ⟨by rw [hD]; exact hfd x hx s hs, ?_⟩
    have h2 := (hyt (g x) (hgb x hx) (s - T) (hm s hs)).comp_sub_const s T
    have h3 := h2.clm_comp (hasDerivAt_const s (g' x))
    simp only [ContinuousLinearMap.comp_zero, add_zero] at h3
    have h4 : (fun u => fderiv ℝ (fun y => z y u) x) =ᶠ[𝓝 s]
        fun u => (fderiv ℝ (y (u - T)) (g x)).comp (g' x) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hs.1 hs.2) fun u hu =>
        (hfd x hx u hu).fderiv
    refine (h3.congr_of_eventuallyEq h4).congr_deriv ?_
    rw [hD, (hz x hx s hs).2, ContinuousLinearMap.comp_assoc]

end Comp

end KAM.Nekhoroshev.FlowChain

end
