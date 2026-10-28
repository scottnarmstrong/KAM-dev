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

section Reverse

variable {F : E → E} {W : Set E} {Tm Tp : E → EReal} {z : E → ℝ → E}

theorem mem_eIoo_neg_iff {a b : EReal} {t : ℝ} : t ∈ eIoo (-b) (-a) ↔ -t ∈ eIoo a b := by
  simp only [KAM.ODE.mem_eIoo_iff, EReal.coe_neg]
  rw [EReal.neg_lt_comm, EReal.lt_neg_comm]
  exact and_comm

/-- Time reversal: regularity of the reversed family for `-F` gives regularity for `F`. -/
theorem RegOn.of_neg {J : Set ℝ} {U : Set E}
    (h : RegOn (fun x => -F x) W (fun x => -Tp x) (fun x => -Tm x) (fun x t => z x (-t)) J U) :
    RegOn F W Tm Tp z (Neg.neg ⁻¹' J) U := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hneg : ContinuousOn (fun q : ℝ × E => (-q.1, q.2)) ((Neg.neg ⁻¹' J) ×ˢ U) := by fun_prop
  have hmaps : MapsTo (fun q : ℝ × E => (-q.1, q.2)) ((Neg.neg ⁻¹' J) ×ˢ U) (J ×ˢ U) :=
    fun q hq => ⟨hq.1, hq.2⟩
  refine ⟨h1, fun x hx t ht => ?_, ?_, ?_, fun x hx s hs => ?_⟩
  · have := h2 x hx ht
    rw [mem_eIoo_neg_iff] at this
    simpa using this
  · refine (h3.comp hneg hmaps).congr fun q _ => ?_
    simp
  · refine (h4.comp hneg hmaps).congr fun q _ => ?_
    simp
  · obtain ⟨hd, ht⟩ := h5 x hx (-s) hs
    simp only [neg_neg] at hd ht
    refine ⟨hd, ?_⟩
    have h6 := ht.scomp s (hasDerivAt_neg s)
    simp only [neg_neg, Function.comp_def] at h6
    refine h6.congr_deriv ?_
    rw [fderiv_fun_neg]
    simp

end Reverse

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

section Shift

variable {F : E → E} {W : Set E}

/-- Time shift of a maximal solution by another solution: if `w` solves `ẋ = F x` on an open
interval `I ∋ 0` with `w 0 = z t₀`, then `t₀ + I` lies in the maximal interval and
`z (t₀ + σ) = w σ`. -/
theorem shift_sol (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W) {x : E} {Tm Tp : EReal}
    {z : ℝ → E} (hz : IsMaximalSolution F W x Tm Tp z) {t₀ : ℝ} (ht₀ : t₀ ∈ eIoo Tm Tp)
    {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {w : ℝ → E}
    (hw : IsSolutionIn F W I w) (hw0 : w 0 = z t₀) :
    ∀ σ ∈ I, t₀ + σ ∈ eIoo Tm Tp ∧ z (t₀ + σ) = w σ := by
  classical
  set J' : Set ℝ := (fun u => u + -t₀) ⁻¹' I with hJ'
  have hw' : IsSolutionIn F W J' (fun u => w (u + -t₀)) := KAM.ODE.gen_symmetry_shift hw (-t₀)
  have hJ'o : IsOpen J' := hI.preimage (continuous_id.add continuous_const)
  have hJ'c : J'.OrdConnected :=
    hIc.preimage_mono fun a b hab => add_le_add_left hab _
  have ht₀' : t₀ ∈ J' := by simpa [hJ'] using h0
  let y' : ℝ → E := fun u => if u ∈ eIoo Tm Tp then z u else w (u + -t₀)
  have e1 : EqOn y' z (eIoo Tm Tp) := fun u hu => by simp [y', hu]
  have e2 : EqOn y' (fun u => w (u + -t₀)) J' := fun u hu => by
    by_cases hm : u ∈ eIoo Tm Tp
    · have := KAM.ODE.gen_uniqueness_inter hW hF (KAM.ODE.ordConnected_eIoo Tm Tp) hJ'c
        (t₀ := t₀) ⟨ht₀, ht₀'⟩ hz.isSolution hw' (by simpa using hw0.symm) ⟨hm, hu⟩
      simp [y', hm, this]
    · simp [y', hm]
  have hsol : IsSolutionIn F W (eIoo Tm Tp ∪ J') y' :=
    IsSolutionIn.union_of_isOpen hz.isSolution hw' (KAM.ODE.isOpen_eIoo Tm Tp) hJ'o e1 e2
  have hconn : (eIoo Tm Tp ∪ J').OrdConnected := by
    rw [← isPreconnected_iff_ordConnected]
    exact (isPreconnected_iff_ordConnected.2 (KAM.ODE.ordConnected_eIoo Tm Tp)).union t₀ ht₀ ht₀'
      (isPreconnected_iff_ordConnected.2 hJ'c)
  obtain ⟨hsub, heq⟩ := hz.maximal _ y' hconn (Or.inl (KAM.ODE.zero_mem_eIoo hz))
    (by rw [e1 (KAM.ODE.zero_mem_eIoo hz)]; exact hz.init) hsol
  intro σ hσ
  have hσ' : t₀ + σ ∈ J' := by simpa [hJ'] using hσ
  refine ⟨hsub (Or.inr hσ'), ?_⟩
  have := heq (Or.inr hσ')
  rw [e2 hσ'] at this
  simpa using this.symm

end Shift

section Ftc

variable {F : E → E} {W : Set E} [CompleteSpace E]

/-- FTC for the Volterra equation: the `x`-derivative of a local flow solves the variational
equation in time. -/
theorem hasDerivAt_fderiv_volterra (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W) {a : ℝ} {p : E}
    {y : ℝ → E → E} (hsol : IsSolutionIn F W (Ioo (-a) a) (fun t => y t p))
    (hyd : ContinuousOn (fun τ => fderiv ℝ (y τ) p) (Ioo (-a) a))
    (heq : ∀ t ∈ Ioo (-a) a, fderiv ℝ (y t) p = ContinuousLinearMap.id ℝ E +
      ∫ u in (0 : ℝ)..t, (fderiv ℝ F (y u p)).comp (fderiv ℝ (y u) p))
    {t : ℝ} (ht : t ∈ Ioo (-a) a) :
    HasDerivAt (fun τ => fderiv ℝ (y τ) p)
      ((fderiv ℝ F (y t p)).comp (fderiv ℝ (y t) p)) t := by
  set G : ℝ → E →L[ℝ] E := fun u => (fderiv ℝ F (y u p)).comp (fderiv ℝ (y u) p) with hG
  have hDF : ContinuousOn (fderiv ℝ F) W := hF.continuousOn_fderiv_of_isOpen hW le_rfl
  have hGc : ContinuousOn G (Ioo (-a) a) :=
    (hDF.comp hsol.continuousOn fun u hu => (hsol u hu).1).clm_comp hyd
  have hmem : Ioo (-a) a ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hint : IntervalIntegrable G MeasureTheory.volume 0 t := by
    refine (hGc.mono ?_).intervalIntegrable
    have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
    exact ordConnected_Ioo.uIcc_subset h0 ht
  have hF' := intervalIntegral.integral_hasDerivAt_right hint
    (hGc.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hGc.continuousAt hmem)
  have := hF'.const_add (ContinuousLinearMap.id ℝ E)
  refine this.congr_of_eventuallyEq ?_
  exact Filter.eventuallyEq_of_mem hmem fun u hu => heq u hu

end Ftc

section Chain

variable [CompleteSpace E] [FiniteDimensional ℝ E] [ProperSpace E]
variable {F : E → E} {W : Set E} {Tm Tp : E → EReal} {z : E → ℝ → E}

/-- The output of `ext_dep`: a local flow on `(-a, a) × ball x₀ r`. -/
structure LocalFlow (F : E → E) (W : Set E) (x₀ : E) (a r : ℝ) (y : ℝ → E → E) : Prop where
  ha : 0 < a
  hr : 0 < r
  ball_sub : ball x₀ r ⊆ W
  cont : ContinuousOn (fun p : ℝ × E => y p.1 p.2) (Ioo (-a) a ×ˢ ball x₀ r)
  dcont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (y p.1) p.2) (Ioo (-a) a ×ˢ ball x₀ r)
  init : ∀ x ∈ ball x₀ r, y 0 x = x
  sol : ∀ x ∈ ball x₀ r, IsSolutionIn F W (Ioo (-a) a) (fun t => y t x)
  hasF : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-a) a, HasFDerivAt (y t) (fderiv ℝ (y t) x) x
  vol : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-a) a, fderiv ℝ (y t) x = ContinuousLinearMap.id ℝ E +
    ∫ u in (0 : ℝ)..t, (fderiv ℝ F (y u x)).comp (fderiv ℝ (y u) x)

theorem exists_localFlow (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W) {x₀ : E} (hx : x₀ ∈ W) :
    ∃ a r y, LocalFlow F W x₀ a r y := by
  obtain ⟨a, r, ha, hr, hb, y, h1, h2, h3⟩ := ext_dep hW hF hx
  exact ⟨a, r, y, ha, hr, hb, h1, h2, fun x hx => (h3 x hx).1, fun x hx => (h3 x hx).2.1,
    fun x hx t ht => ((h3 x hx).2.2 t ht).1, fun x hx t ht => ((h3 x hx).2.2 t ht).2⟩

omit [FiniteDimensional ℝ E] [ProperSpace E] in
theorem LocalFlow.deriv_t (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W) {x₀ : E} {a r : ℝ}
    {y : ℝ → E → E} (hl : LocalFlow F W x₀ a r y) :
    ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-a) a, HasDerivAt (fun τ => fderiv ℝ (y τ) x)
      ((fderiv ℝ F (y t x)).comp (fderiv ℝ (y t) x)) t := fun x hx _ ht =>
  hasDerivAt_fderiv_volterra hW hF (hl.sol x hx)
    (hl.dcont.comp (continuousOn_id.prodMk continuousOn_const)
      fun _ hu => ⟨hu, hx⟩) (hl.vol x hx) ht

variable (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
  (hmax : ∀ x ∈ W, IsMaximalSolution F W x (Tm x) (Tp x) (z x))
include hW hF hmax

omit [FiniteDimensional ℝ E] [ProperSpace E] in
/-- Extension of a regular time interval by one local-flow slab centered at `T₁`. -/
theorem regOn_extend {J₁ : Set ℝ} {U₁ : Set E} (hJ₁ : IsOpen J₁) (hU₁ : IsOpen U₁)
    (h₁ : RegOn F W Tm Tp z J₁ U₁) {T₁ : ℝ} (hT₁ : T₁ ∈ J₁) {x₁ : E} (hx₁ : x₁ ∈ U₁) {x₀ : E}
    {a r : ℝ} {y : ℝ → E → E} (hl : LocalFlow F W x₀ a r y)
    (hb : z x₁ T₁ ∈ ball x₀ r) :
    ∃ U₂, IsOpen U₂ ∧ x₁ ∈ U₂ ∧
      RegOn F W Tm Tp z (J₁ ∪ Ioo (T₁ - a) (T₁ + a)) U₂ := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
  have hcz : ContinuousOn (fun x => z x T₁) U₁ :=
    a3.comp (continuousOn_const.prodMk continuousOn_id) fun x hx => ⟨hT₁, hx⟩
  have hU₂ : IsOpen (U₁ ∩ (fun x => z x T₁) ⁻¹' ball x₀ r) :=
    hcz.isOpen_inter_preimage hU₁ isOpen_ball
  refine ⟨_, hU₂, ⟨hx₁, hb⟩, ?_⟩
  have hsub : U₁ ∩ (fun x => z x T₁) ⁻¹' ball x₀ r ⊆ U₁ := inter_subset_left
  have hJ₂ : RegOn F W Tm Tp z (Ioo (T₁ - a) (T₁ + a)) (U₁ ∩ (fun x => z x T₁) ⁻¹' ball x₀ r) := by
    refine regOn_comp hU₂ (hsub.trans a1) (g := fun x => z x T₁)
      (g' := fun x => fderiv ℝ (fun y => z y T₁) x)
      (fun x hx => (a5 x (hsub hx) T₁ hT₁).1)
      ((a4.comp (continuousOn_const.prodMk continuousOn_id)
        fun x hx => ⟨hT₁, hx⟩).mono hsub) hl.cont hl.dcont hl.hasF
      (hl.deriv_t hW hF) (fun x hx => hx.2) ?_
    intro x hx u hu
    have hxW : x ∈ W := a1 hx.1
    have := shift_sol hW hF (hmax x hxW) (a2 x hx.1 hT₁) (isOpen_Ioo (a := -a) (b := a))
      ordConnected_Ioo (I := Ioo (-a) a) ⟨by linarith [hl.ha], hl.ha⟩
      (w := fun t => y t (z x T₁)) (hl.sol _ hx.2) (by simpa using hl.init _ hx.2) (u - T₁)
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simpa using this
  exact RegOn.union hU₂ hJ₁ isOpen_Ioo (RegOn.mono ⟨a1, a2, a3, a4, a5⟩ subset_rfl hsub) hJ₂

/-- Regularity on an open time interval and open neighborhood, at a point `(T, x₁)` with `T ≥ 0`
of the flow domain (chaining local flows along the orbit arc `[0, T]`). -/
theorem reg_forward {x₁ : E} (hx₁ : x₁ ∈ W) {T : ℝ} (hT : 0 ≤ T)
    (hTm : T ∈ eIoo (Tm x₁) (Tp x₁)) :
    ∃ (J : Set ℝ) (U : Set E), IsOpen J ∧ IsOpen U ∧ T ∈ J ∧ x₁ ∈ U ∧
      RegOn F W Tm Tp z J U := by
  let S : Set ℝ := {T | 0 ≤ T ∧ ∃ (J : Set ℝ) (U : Set E), IsOpen J ∧ IsOpen U ∧
    Icc 0 T ⊆ J ∧ x₁ ∈ U ∧ RegOn F W Tm Tp z J U}
  have hS_mono : ∀ T ∈ S, ∀ T' ∈ Icc 0 T, T' ∈ S := by
    rintro T ⟨-, J, U, hJ, hU, hsub, hx, hR⟩ T' hT'
    exact ⟨hT'.1, J, U, hJ, hU, (Icc_subset_Icc_right hT'.2).trans hsub, hx, hR⟩
  have hS_eIoo : ∀ T₀ ≥ 0, T₀ ∈ eIoo (Tm x₁) (Tp x₁) → T₀ ∈ S := by
    intro T₀ hT₀ hT₀m
    by_contra hnot
    obtain ⟨a₀, r₀, y₀, hl₀⟩ := exists_localFlow hW hF hx₁
    have h0S : (0 : ℝ) ∈ S := by
      refine ⟨le_rfl, Ioo (0 - a₀) (0 + a₀), ball x₁ r₀, isOpen_Ioo, isOpen_ball, ?_,
        mem_ball_self hl₀.hr, ?_⟩
      · intro u hu
        rw [Icc_self, mem_singleton_iff] at hu
        subst hu
        exact ⟨by linarith [hl₀.ha], by linarith [hl₀.ha]⟩
      · refine regOn_comp isOpen_ball hl₀.ball_sub (g := id)
          (g' := fun _ => ContinuousLinearMap.id ℝ E)
          (fun x _ => hasFDerivAt_id x) continuousOn_const hl₀.cont hl₀.dcont hl₀.hasF
          (hl₀.deriv_t hW hF) (fun x hx => hx) (T := 0) ?_
        intro x hx u hu
        have hxW : x ∈ W := hl₀.ball_sub hx
        have := shift_sol hW hF (hmax x hxW) (t₀ := 0) (KAM.ODE.zero_mem_eIoo (hmax x hxW))
          (isOpen_Ioo (a := -a₀) (b := a₀)) ordConnected_Ioo (I := Ioo (-a₀) a₀)
          ⟨by linarith [hl₀.ha], hl₀.ha⟩ (w := fun t => y₀ t x) (hl₀.sol x hx)
          (by rw [hl₀.init x hx, (hmax x hxW).init]) (u - 0)
          ⟨by linarith [hu.1], by linarith [hu.2]⟩
        simpa using this
    set A : Set ℝ := S ∩ Icc 0 T₀ with hA
    have hAne : A.Nonempty := ⟨0, h0S, le_rfl, hT₀⟩
    have hAbdd : BddAbove A := ⟨T₀, fun u hu => hu.2.2⟩
    set s := sSup A with hs
    have hs0 : 0 ≤ s := le_csSup hAbdd ⟨h0S, le_rfl, hT₀⟩
    have hsT : s ≤ T₀ := csSup_le hAne fun u hu => hu.2.2
    have hsm : s ∈ eIoo (Tm x₁) (Tp x₁) :=
      (KAM.ODE.ordConnected_eIoo _ _).out (KAM.ODE.zero_mem_eIoo (hmax x₁ hx₁)) hT₀m ⟨hs0, hsT⟩
    have hsol := (hmax x₁ hx₁).isSolution s hsm
    obtain ⟨a, r, y, hl⟩ := exists_localFlow hW hF hsol.1
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hsol.2.continuousAt r hl.hr
    obtain ⟨T₁, ⟨hT₁S, hT₁0, hT₁T⟩, hT₁lt⟩ :=
      exists_lt_of_lt_csSup hAne (show s - min δ (a / 4) < s by
        have : 0 < min δ (a / 4) := lt_min hδ (by linarith [hl.ha])
        linarith)
    have hT₁s : T₁ ≤ s := le_csSup hAbdd ⟨hT₁S, hT₁0, hT₁T⟩
    have hmin1 : min δ (a / 4) ≤ δ := min_le_left _ _
    have hmin2 : min δ (a / 4) ≤ a / 4 := min_le_right _ _
    have hdist : dist T₁ s < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    obtain ⟨-, J₁, U₁, hJ₁, hU₁, hsub, hx₁U, hR⟩ := hT₁S
    obtain ⟨U₂, hU₂, hx₂, hR₂⟩ := regOn_extend hW hF hmax hJ₁ hU₁ hR
      (hsub ⟨hT₁0, le_rfl⟩) hx₁U hl (hδb hdist)
    have hT₂S : T₁ + a / 2 ∈ S := by
      refine ⟨by linarith [hl.ha], J₁ ∪ Ioo (T₁ - a) (T₁ + a), U₂, hJ₁.union isOpen_Ioo, hU₂, ?_,
        hx₂, hR₂⟩
      intro u hu
      by_cases hu1 : u ≤ T₁
      · exact Or.inl (hsub ⟨hu.1, hu1⟩)
      · exact Or.inr ⟨by linarith [hu.1, hl.ha], by linarith [hu.2, hl.ha]⟩
    by_cases hle : T₁ + a / 2 ≤ T₀
    · have := le_csSup hAbdd ⟨hT₂S, by linarith [hl.ha], hle⟩
      linarith [hl.ha]
    · exact hnot (hS_mono _ hT₂S T₀ ⟨hT₀, (not_le.1 hle).le⟩)
  obtain ⟨-, J, U, hJ, hU, hsub, hx, hR⟩ := hS_eIoo T hT hTm
  exact ⟨J, U, hJ, hU, hsub ⟨hT, le_rfl⟩, hx, hR⟩

/-- Regularity on a neighborhood of every point of the flow domain (both time signs). -/
theorem reg_all {x : E} (hx : x ∈ W) {t : ℝ} (ht : t ∈ eIoo (Tm x) (Tp x)) :
    ∃ (J : Set ℝ) (U : Set E), IsOpen J ∧ IsOpen U ∧ t ∈ J ∧ x ∈ U ∧
      RegOn F W Tm Tp z J U := by
  rcases le_or_gt 0 t with h0 | h0
  · exact reg_forward hW hF hmax hx h0 ht
  · have hmax' : ∀ x ∈ W, IsMaximalSolution (fun x => -F x) W x (-Tp x) (-Tm x)
        (fun s => z x (-s)) := fun x hx => (hmax x hx).neg
    obtain ⟨J, U, hJ, hU, htJ, hxU, hR⟩ := reg_forward (z := fun x s => z x (-s)) hW hF.neg hmax'
      hx (T := -t) (by linarith) (mem_eIoo_neg_iff.2 (by simpa using ht))
    exact ⟨Neg.neg ⁻¹' J, U, hJ.preimage continuous_neg, hU, by simpa using htJ, hxU, hR.of_neg⟩

end Chain

end KAM.Nekhoroshev.FlowChain

end
