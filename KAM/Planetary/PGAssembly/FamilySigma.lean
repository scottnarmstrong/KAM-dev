/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FamilyAux

/-!
# P Part 5: sigma compactness of the parameter set (`bpP:p5:torus-conv`)

`pgD0` is the intersection of an open set (the fast and slow action boxes) with a closed set
(the inner-core, the Diophantine conditions on the fast and the full frequencies), hence sigma
compact. The full frequency is the real frequency of `kamH`, continuous on a tube around the
action domain by holomorphy.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FAM.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

theorem fam_isSigmaCompact_inter {m : ℕ} {O C : Set (Fin m → ℝ)} (hO : IsOpen O)
    (hC : IsClosed C) : IsSigmaCompact (O ∩ C) := by
  have : LocallyCompactSpace O := hO.locallyCompactSpace
  have hs : SigmaCompactSpace O := inferInstance
  obtain ⟨K, hK, hcov⟩ := SigmaCompactSpace.exists_compact_covering (X := O)
  refine ⟨fun n => (Subtype.val '' (K n)) ∩ C, fun n => ?_, ?_⟩
  · exact ((hK n).image continuous_subtype_val).inter_right hC
  · ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨n, ⟨y, hy, rfl⟩, hc⟩
      exact ⟨y.2, hc⟩
    · rintro ⟨hx, hc⟩
      have : (⟨x, hx⟩ : O) ∈ ⋃ n, K n := by rw [hcov]; trivial
      obtain ⟨n, hn⟩ := mem_iUnion.1 this
      exact ⟨n, ⟨_, hn, rfl⟩, hc⟩

theorem fam_isClosed_forall {ι X : Type*} [TopologicalSpace X] {P : ι → X → Prop}
    (h : ∀ i, IsClosed {x | P i x}) : IsClosed {x | ∀ i, P i x} := by
  have : {x | ∀ i, P i x} = ⋂ i, {x | P i x} := by ext; simp
  rw [this]; exact isClosed_iInter h

theorem fam_isClosed_imp {X : Type*} [TopologicalSpace X] (A : Prop) {B : X → Prop}
    (h : A → IsClosed {x | B x}) : IsClosed {x | A → B x} := by
  by_cases hA : A
  · simpa [hA] using h hA
  · simp [hA]

theorem fam_isClosed_twoScale (a b : ℕ) (g1 g2 t : ℝ) :
    IsClosed (twoScaleDiophantine a b g1 g2 t) := by
  unfold twoScaleDiophantine
  have hc : ∀ (k : Fin (a+b) → ℤ) (c : ℝ),
      IsClosed {ω : Fin (a+b) → ℝ | c / (∑ i, |(k i:ℝ)|)^t ≤ |∑ i, (k i:ℝ) * ω i|} := fun k c =>
    isClosed_le continuous_const
      (by fun_prop : Continuous fun ω : Fin (a+b) → ℝ => |∑ i, (k i:ℝ) * ω i|)
  refine IsClosed.inter (fam_isClosed_forall fun k => ?_) (fam_isClosed_forall fun k => ?_)
  · exact fam_isClosed_imp _ fun _ => hc k g1
  · exact fam_isClosed_imp _ fun _ => fam_isClosed_imp _ fun _ => hc k g2

theorem fam_isClosed_dio (n : ℕ) (γ τ : ℝ) :
    IsClosed {ω : Fin n → ℝ | KAM.IsDiophantine γ τ ω} := by
  refine fam_isClosed_forall fun k => fam_isClosed_imp _ fun _ => ?_
  exact isClosed_le continuous_const
    (by fun_prop : Continuous fun ω : Fin n → ℝ => |∑ i, (k i:ℝ) * ω i|)

theorem fam_continuousOn_realFreq (h : admissible d (pgRstar d) r mu) :
    ContinuousOn (realFreq (kamH d mu))
      (realNbhd (pgActionDomain d r mu) (params d r mu).rho) := by
  have hO := isOpen_actionNbhd (pgActionDomain d r mu) (params d r mu).rho
  have hfd : ContinuousOn (fderiv ℂ (kamH d mu))
      (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :=
    (KAM.differentiableOn_fderiv_of_isOpen hO (kamH_differentiableOn h)).continuousOn
  have hmaps : MapsTo (KAM.realInclusion (a+b))
      (realNbhd (pgActionDomain d r mu) (params d r mu).rho)
      (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) := by
    rintro J ⟨y, hy, hd⟩
    refine mem_actionNbhd_iff.2 ⟨y, hy, ?_⟩
    rw [← map_sub, KAM.norm_realInclusion, ← dist_eq_norm]
    exact hd
  refine continuousOn_pi.2 fun i => ?_
  have h1 : ContinuousOn (fun I : Fin (a+b) → ℝ => fderiv ℂ (kamH d mu) (KAM.realInclusion (a+b) I)
      (Pi.single i 1)) (realNbhd (pgActionDomain d r mu) (params d r mu).rho) :=
    (hfd.comp (KAM.realInclusion (a+b)).continuous.continuousOn hmaps).clm_apply continuousOn_const
  exact Complex.continuous_re.comp_continuousOn h1

theorem fam_isSigmaCompact_D0 (h : admissible d (pgRstar d) r mu) :
    IsSigmaCompact (pgD0 d r mu) := by
  obtain ⟨-, -, -, hD⟩ := pg_kam_dictionary d r mu h
  obtain ⟨-, -, -, hl1, -⟩ := kh_dyn h
  have hρ : 0 < (params d r mu).rho := by
    show 0 < (params d r mu).l1 / 2; linarith
  -- fast Diophantine condition
  have hfd : ContinuousOn (fastFrequency d.H0) d.V := by
    refine continuousOn_pi.2 fun i => ?_
    have han : AnalyticOnNhd ℝ d.H0 d.V := d.hfreq.1.mono (subset_closure.trans d.hVW)
    exact (han.fderiv.continuousOn).clm_apply continuousOn_const
  obtain ⟨u1, hu1, hu1e⟩ := continuousOn_iff_isClosed.1 hfd
    {ω | KAM.IsDiophantine (params d r mu).gammaBar (pgTau a b) ω}
    (fam_isClosed_dio _ _ _)
  obtain ⟨u2, hu2, hu2e⟩ := continuousOn_iff_isClosed.1 (fam_continuousOn_realFreq h)
    (twoScaleDiophantine a b (pgKamScale d r mu).γ₁ (pgKamScale d r mu).γ₂
      (pgKamScale d r mu).τ) (fam_isClosed_twoScale _ _ _ _ _)
  have hcl1 : IsClosed {I : Fin a → ℝ | ∀ J ∈ frontier d.V, Real.sqrt r ≤ dist I J} := by
    have : {I : Fin a → ℝ | ∀ J ∈ frontier d.V, Real.sqrt r ≤ dist I J} =
        ⋂ J ∈ frontier d.V, {I | Real.sqrt r ≤ dist I J} := by ext; simp
    rw [this]
    exact isClosed_biInter fun J _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hbf : Continuous (fun J : Fin (a+b) → ℝ => blockFast J) := by
    unfold blockFast; fun_prop
  have hbs : Continuous (fun J : Fin (a+b) → ℝ => blockSlow J) := by
    unfold blockSlow; fun_prop
  have hO1 : IsOpen {J : Fin (a+b) → ℝ | blockFast J ∈ d.V ∧
      blockSlow J ∈ actionShell b (params d r mu).l1 (params d r mu).l2top} := by
    refine IsOpen.inter (d.hV.preimage hbf) ?_
    exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage hbs
  have hCl : IsClosed ((fun J => blockFast J) ⁻¹' ({I | ∀ J ∈ frontier d.V, Real.sqrt r ≤ dist I J} ∩ u1)
      ∩ u2) := (((hcl1.inter hu1).preimage hbf)).inter hu2
  convert fam_isSigmaCompact_inter hO1 hCl using 1
  rw [← hD]
  ext J
  have hDsub : J ∈ pgActionDomain d r mu → J ∈ realNbhd (pgActionDomain d r mu)
      (params d r mu).rho := fun hJ => ⟨J, hJ, by simpa using hρ⟩
  constructor
  · rintro ⟨hJ, hg⟩
    have hJ' := hJ
    obtain ⟨⟨⟨hV, hin⟩, hdio⟩, hshell⟩ := hJ'
    have e1 : blockFast J ∈ u1 := by
      have : blockFast J ∈ (fastFrequency d.H0) ⁻¹' {ω | KAM.IsDiophantine
          (params d r mu).gammaBar (pgTau a b) ω} ∩ d.V := ⟨hdio, hV⟩
      rw [hu1e] at this; exact this.1
    have e2 : J ∈ u2 := by
      have : J ∈ (realFreq (kamH d mu)) ⁻¹' _ ∩ realNbhd (pgActionDomain d r mu)
          (params d r mu).rho := ⟨hg, hDsub hJ⟩
      rw [hu2e] at this; exact this.1
    exact ⟨⟨hV, hshell⟩, ⟨⟨hin, e1⟩, e2⟩⟩
  · rintro ⟨⟨hV, hshell⟩, ⟨⟨hin, e1⟩, e2⟩⟩
    have hdio : blockFast J ∈ {I : Fin a → ℝ |
        KAM.IsDiophantine (params d r mu).gammaBar (pgTau a b) (fastFrequency d.H0 I)} := by
      have : blockFast J ∈ u1 ∩ d.V := ⟨e1, hV⟩
      rw [← hu1e] at this; exact this.1
    have hJ : J ∈ pgActionDomain d r mu := ⟨⟨⟨hV, hin⟩, hdio⟩, hshell⟩
    refine ⟨hJ, ?_⟩
    have : J ∈ u2 ∩ realNbhd (pgActionDomain d r mu) (params d r mu).rho := ⟨e2, hDsub hJ⟩
    rw [← hu2e] at this; exact this.1

end KAM.Planetary

end
