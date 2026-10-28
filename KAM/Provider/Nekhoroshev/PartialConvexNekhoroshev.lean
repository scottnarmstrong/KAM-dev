/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Block
public import KAM.Nekhoroshev.Partial.Threshold
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn

/-!
# Provider for the frozen theorem `KAM.Nekhoroshev.partialConvex_nekhoroshev`

The proof of `KAM.Nekhoroshev.partialConvex_nekhoroshev` is assembled here as
`KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`, from graph predecessors and approved external
inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other
than the anchor may import it.

Assembly (`bpN:p0:partial`, steps `final-*` of blueprint-N Part 11c): an empty `G` is vacuous;
otherwise `threshold` fixes `μ₀` before `μ, P, C, z, t`, the orbit is converted by `theta`
(`orbit`), the field is identified on the block domain by `domain_field`, and `block` applies, to
the time-reversed orbit when the definite sign is `-1`.
-/

@[expose] public section

open Set

namespace KAM.Provider.Nekhoroshev

open KAM.Nekhoroshev

/-- The slow pair of the converted point is the frozen slow pair. -/
theorem slowPair_theta {n k : ℕ} (w : KAM.Planetary.Phase (n + k)) :
    slowPair (theta w) = (KAM.Planetary.slow (a := n) w.1, KAM.Planetary.slow (a := n) w.2) := by
  ext i
  · exact theta_slowq w i
  · exact theta_slowp w i

/-- The fast action of the converted point is the frozen fast action. -/
theorem fastAction_theta {n k : ℕ} (w : KAM.Planetary.Phase (n + k)) :
    fastAction (theta w) = KAM.Planetary.fast (b := k) w.2 := by
  funext i
  exact theta_fast w i

/-- Shrinking the radius of an inner core enlarges it. -/
theorem innerCore_mono {E : Type*} [NormedAddCommGroup E] {U : Set E} {d d' : ℝ} (hd : d' ≤ d)
    {x : E} (hx : x ∈ innerCore U d) : x ∈ innerCore U d' :=
  ⟨hx.1, (Metric.closedBall_subset_closedBall hd).trans hx.2⟩

theorem partialConvex_nekhoroshev
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (G G' : Set (Fin n → ℝ)) (D : Set (KAM.Planetary.Phase k))
    (hG : IsOpen G) (hGc : Convex ℝ G)
    (hG' : IsOpen G') (hGc' : Convex ℝ G') (hD : IsOpen D)
    (ρ g m Mcomplex : ℝ) (hρ : 0 < ρ) (hMc : 0 < Mcomplex)
    (hcollar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G')
    (h : (Fin n → ℂ) → ℂ)
    (hhol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ))
    (hC2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ))
    (hreal : ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ → (h (fun i => (I i : ℂ))).im = 0)
    (hHess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mcomplex)
    (hdef : HasDefiniteFastPart G' ρ g m h) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
      ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
      IsPartialPerturbation G' D ρ P → ∀ C : ℝ, 0 < C →
      ∀ z : ℝ → KAM.Planetary.Phase (n + k),
      IsSolutionOn
        (KAM.Planetary.degenerateHamiltonian (realPart h)
          (fun _ w => (P (complexifyPhase w)).re) μ)
        {I | KAM.Planetary.fast (b := k) I ∈ G} (Set.Icc 0 C) z →
      KAM.Planetary.fast (b := k) (z 0).2 ∈ innerCore G (μ ^ partialDriftExponent n) →
      ∀ t ∈ Set.Icc 0
        (min C (μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)))),
      (∀ u ∈ Set.Icc 0 t,
        (KAM.Planetary.slow (a := n) (z u).1, KAM.Planetary.slow (a := n) (z u).2)
          ∈ innerCore D (μ ^ partialDriftExponent n)) →
      ‖KAM.Planetary.fast (b := k) (z t).2 - KAM.Planetary.fast (b := k) (z 0).2‖
        ≤ μ ^ partialDriftExponent n / 2 := by
  classical
  -- final-empty: with `G = ∅` the initial inner-core membership is impossible.
  rcases G.eq_empty_or_nonempty with hGe | hne
  · refine ⟨1, one_pos, fun μ _ _ P _ C _ z _ hz0 => ?_⟩
    have h0 := hz0.1
    rw [hGe] at h0
    exact absurd h0 (Set.notMem_empty _)
  -- final-data: the frozen premises, and the sign of the definite fast Hessian.
  let a : PartialData n k :=
    { G := G, G' := G', D := D, ρ := ρ, g := g, m := m, Mc := Mcomplex, h := h,
      hn := hn, hk := hk, hG := hG, hGc := hGc, hG' := hG', hGc' := hGc', hD := hD,
      hρ := hρ, hMc := hMc, collar := hcollar, hol := hhol, C2 := hC2, real := hreal,
      Hess := hHess, definite := hdef }
  obtain ⟨hg, hm, -, σ, hσpm, hσI⟩ := a.definite
  have hσ : DefiniteSign a σ := ⟨hσpm, hσI⟩
  -- final-mu: the threshold depends only on the data.
  obtain ⟨μ0, hμ0, hthr⟩ := threshold a hne
  refine ⟨μ0, hμ0, fun μ hμ hμμ0 P hP C hC z hz hz0 t ht hslow => ?_⟩
  obtain ⟨hε, hd, hκ, hSL, hdrift, htime⟩ := hthr μ hμ hμμ0
  have hdpos : 0 < (constants a).d μ := Real.rpow_pos_of_pos hμ _
  have hr0 : 0 < (constants a).r0 := lt_min (half_pos hρ) (div_pos (mul_pos (by norm_num) hg) hm)
  set Ic := KAM.Planetary.fast (b := k) (z 0).2 with hIc_def
  have hIc : Ic ∈ a.G := hz0.1
  -- final-given: the queried time lies in `[0, C]` and below the block time.
  have ht0 : 0 ≤ t := ht.1
  have htC : t ≤ C := ht.2.trans (min_le_left _ _)
  have htT : t ≤ (constants a).blockTime μ := (ht.2.trans (min_le_right _ _)).trans htime
  -- final-orbit: the converted orbit solves the weighted system.
  set H := KAM.Planetary.degenerateHamiltonian (realPart h)
    (fun _ w => (P (complexifyPhase w)).re) μ with hH
  have horb : ∀ u ∈ Icc 0 C, HasDerivAt (theta ∘ z)
      (realWfield (2*Real.pi) (converted H) (theta (z u))) u := fun u hu =>
    (orbit H z u (hz u hu).2.1).1 (hz u hu).2.2
  have hfield := domain_field a hμ hσ hIc hr0 le_rfl hd P hP
  have hslow' : ∀ u ∈ Icc 0 t, slowPair (theta (z u)) ∈ innerCore a.D ((constants a).d μ) :=
    fun u hu => by rw [slowPair_theta]; exact hslow u hu
  have hx0 : slowPair (theta (z 0)) ∈ innerCore a.D (3*(constants a).d μ/4) :=
    innerCore_mono (by linarith) (hslow' 0 ⟨le_rfl, ht0⟩)
  -- final-drift: the block bound is below half the slow margin.
  suffices hfin : ‖fastAction (theta (z t)) - Ic‖ ≤ (constants a).R0/(2*(constants a).K μ) by
    rw [fastAction_theta] at hfin
    exact hfin.trans hdrift
  -- final-sign
  rcases hσpm with rfl | rfl
  · refine block a hne hμ hσ hε hd hκ hSL P hP hIc
      (fun w => (1:ℝ) • realWfield (2*Real.pi) (converted H) w) hfield
      (J := Icc 0 C) ordConnected_Icc ⟨le_rfl, hC.le⟩ (y := theta ∘ z)
      (fun u hu => by simpa only [one_smul, Function.comp_apply] using horb u hu)
      (fastAction_theta (z 0)) hx0
      (t1 := t) ⟨ht0, htC⟩ (by rwa [abs_of_nonneg ht0]) ?_ t right_mem_uIcc
    intro u hu
    rw [uIcc_of_le ht0] at hu
    exact hslow' u hu
  · have hyb : ∀ u ∈ Icc (-C) 0, HasDerivAt (fun u => theta (z (-u)))
        ((-1:ℝ) • realWfield (2*Real.pi) (converted H) (theta (z (-u)))) u := by
      intro u hu
      have hu' : -u ∈ Icc 0 C := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      exact (horb (-u) hu').scomp u (hasDerivAt_neg u)
    have h0 : theta (z (-0)) = theta (z 0) := by rw [neg_zero]
    have hfin := block a hne hμ hσ hε hd hκ hSL P hP hIc
      (fun w => (-1:ℝ) • realWfield (2*Real.pi) (converted H) w) hfield
      (J := Icc (-C) 0) ordConnected_Icc ⟨by linarith, le_rfl⟩ (y := fun u => theta (z (-u)))
      hyb (by rw [h0]; exact fastAction_theta (z 0)) (by rw [h0]; exact hx0)
      (t1 := -t) ⟨by linarith, by linarith⟩ (by rwa [abs_neg, abs_of_nonneg ht0]) ?_ (-t)
      right_mem_uIcc
    · simpa only [neg_neg] using hfin
    intro u hu
    rw [uIcc_of_ge (by linarith)] at hu
    have hu' : -u ∈ Icc 0 t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa only [neg_neg] using hslow' (-u) hu'

end KAM.Provider.Nekhoroshev

end
