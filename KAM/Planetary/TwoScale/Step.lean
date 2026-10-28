/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepDp
public import KAM.Planetary.TwoScale.StepDisp
public import KAM.Planetary.TwoScale.Lipschitz

/-!
# Two-scale KAM: one step (`bpP:p3:step`)

The one-step lemma of Proposition 3 of the source (P3a): averaging at scale `R = ρ̂`, the new
Hamiltonian `h₊ = h + g`, the injectivity of its frequency map on `D_{R/8}`, the map
`ĩ₊ = ω₊⁻¹ ∘ ω₀`, the new base set `D₊ = ĩ₊(D)` and the next `KamHyp`. The statement is that of
`P23Signatures.lean`; the proof assembles the sub-steps `StepFreq`, `StepNonres`, `StepAvg`,
`StepConst`, `StepHess`, `StepHess2`, `StepInj`, `StepIhat`, `StepReal`, `StepDisp`, `StepNext`,
`StepDp` (nodes `st-nonres` .. `st-quad`). Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- P3 step: Ψ is retained on the large averaging domain; Ψ+ is its restriction,
represented by the SAME total function. All statements name their own domain. -/
theorem step {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f)
    (hD : ∀ I ∈ D, realFreq h I ∈ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ)
      (fs : CHam (a + b)) (Dp : Set (Fin (a + b) → ℝ))
      (ihat : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      let hp := fun I => h I + g I
      let R := rhoHat p
      let V := coefficientDom D (R / 2) (sbar + p.s / 6)
      KamHyp Dp sbar (nextScale p) hp fs ∧
      Dp ⊆ realTube D (R / 16) ∧
      KAM.actionNbhd Dp (R / 16) ⊆ KAM.actionNbhd D (R / 8) ∧
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (coefficientDom D R (sbar + p.s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (R / 2)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 2), ‖g I‖ ≤ 5 / 4 * p.E) ∧
      (∀ z ∈ coefficientDom Dp (R / 16) (sbar + p.s / 12),
        h (Ψ z).2 + f (Ψ z) = hp z.2 + fs z) ∧
      Set.InjOn (freq hp) (KAM.actionNbhd D (R / 8)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 4),
        ‖fderiv ℂ (freq hp) I‖ ≤ 2 * p.M ∧
        (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq hp) I v)‖ ≤ 2 * p.Mhat * ‖v‖) ∧
        ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
          (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq hp) I ∧
          ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ 2 * p.Mbar ∧
          (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ 2 * p.Mbar₁ * ‖v‖) ∧
          (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ 2 * p.Mbar₂ * ‖v‖)) ∧
      realFreq hp '' Dp = realFreq h '' D ∧
      DifferentiableOn ℂ ihat (KAM.actionNbhd D (R / 16)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 16),
        ihat I ∈ KAM.actionNbhd D (R / 8) ∧ freq hp (ihat I) = freq h I ∧
        ‖firstBlock (b := b) (ihat I - I)‖ ≤ 10 * (p.Mbar₁ / p.Mbar) * eHat p * R ∧
        ‖lastBlock (a := a) (ihat I - I)‖ ≤ 10 * (p.Mbar₂ / p.Mbar) * eHat p * R) ∧
      Dp = (fun I => fun j => (ihat (KAM.realInclusion (a + b) I) j).re) '' D ∧
      (∀ I ∈ D, ∀ J ∈ D,
        ‖(ihat (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
          (ihat (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
            640 * (a + b) * eHat p * ‖I - J‖) ∧
      (∀ z ∈ V,
        ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 / 4 * (p.Mhat / p.M) * eHat p * R ∧
        ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 / 4 * eHat p * R ∧
        2 * π * ‖(Ψ z).1 - z.1‖ ≤ 3 / 4 * eHat p * p.s) ∧
      rhoHat (nextScale p) ≥ R / (2 * (24 : ℝ) ^ (p.τ + 1)) ∧
      cutoff (nextScale p) ≤ 24 * cutoff p ∧
      eHat (nextScale p) ≤ (8 / 9) * (4 * p.s) ^ (2 * (p.τ + 1)) * eHat p ^ 2 ∧
      eHat (nextScale p) < eHat p ^ 2 := by
  have hR := H.R_pos
  have hs := H.positive.2.1
  have hE := H.positive.2.2.2.1
  have hRρ := H.R_le_ρ
  have hw := H.widths
  -- averaging at scale `R = ρ̂`
  obtain ⟨Ψ, g, fs, hΨd, hΨi, hΨm, hΨs, hΨp, hΨr, hgd, hgr, hfsr, hid, hgf, hfsc, hfsb, hdisp⟩ :=
    avg (H.avgHyp hD) H.small_avg.1
  have hMb := H.positive.2.2.2.2.2.2.1
  have hMb₁ := H.positive.2.2.2.2.2.2.2.1
  have hMb₂ := H.positive.2.2.2.2.2.2.2.2
  have h0 := H.eHat_nonneg
  have hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E := by
    intro I hI
    have hmem : I ∈ polyNbhd (realBase D) p.ρ := by
      rw [(conv_data D p.ρ 0).1]; exact actionNbhd_mono (by linarith) hI
    have h0' := norm_coeff_zero_le H.f_bound hmem
    have h1 := (hgf I hI).1
    calc ‖g I‖ = ‖(g I - coeff f I 0) + coeff f I 0‖ := by congr 1; ring
      _ ≤ ‖g I - coeff f I 0‖ + ‖coeff f I 0‖ := norm_add_le _ _
      _ ≤ 5 / 4 * p.E := by linarith
  obtain ⟨ihat, hihd, hih⟩ := H.ihat_exists hgd hgb
  have hih' : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      ihat I ∈ Metric.ball I (rhoHat p / 16) ∧ freq (fun J => h J + g J) (ihat I) = freq h I :=
    fun I hI => ⟨(hih I hI).1, (hih I hI).2.1⟩
  have hreal : ∀ I ∈ D, ∀ i, (ihat (KAM.realInclusion (a + b) I) i).im = 0 :=
    fun I hI i => H.ihat_real hgd hgb hgr hih' hI i
  have hcmem : ∀ I ∈ D, KAM.realInclusion (a + b) I ∈ KAM.actionNbhd D (rhoHat p / 16) :=
    fun I hI => mem_actionNbhd_of_mem (by positivity) hI
  have hball : ∀ I ∈ D, ihat (KAM.realInclusion (a + b) I) ∈
      Metric.ball (KAM.realInclusion (a + b) I) (rhoHat p / 16) :=
    fun I hI => (hih _ (hcmem I hI)).1
  have hsub1 := dp_subset_tube hreal hball
  have hsub8 : KAM.actionNbhd ((fun I => fun j => (ihat (KAM.realInclusion (a + b) I) j).re) '' D)
      (rhoHat p / 16) ⊆ KAM.actionNbhd D (rhoHat p / 8) := by
    have := dp_nbhd_subset (r' := rhoHat p / 16) hsub1
    rwa [show rhoHat p / 16 + rhoHat p / 16 = rhoHat p / 8 by ring] at this
  have hsub2 := hsub8.trans (actionNbhd_mono (by linarith : rhoHat p / 8 ≤ rhoHat p / 2))
  have hnext := H.next_hyp hgd hgb hgr hfsr hfsc hfsb hsub8
  refine ⟨Ψ, g, fs,
    (fun I => fun j => (ihat (KAM.realInclusion (a + b) I) j).re) '' D, ihat, ?_⟩
  intro hp R V
  refine ⟨hnext, hsub1, hsub8, hΨd, hΨi, hΨm, hΨs, hΨp, hΨr, hgd, hgb, ?_, H.freq_inj hgd hgb,
    H.hessian_next hgd hgb, ?_, hihd, ?_, rfl, ?_, ?_, rhoHat_next_ge H, cutoff_next_le H,
    eHat_next_le H, eHat_next_lt H⟩
  · intro z hz
    exact hid z (coefficientDom_mono hsub2 (by linarith) hz)
  · exact dp_freq_image hreal fun I hI => (hih _ (hcmem I hI)).2.1
  · intro I hI
    have hb := (hih I hI).1
    refine ⟨?_, (hih I hI).2.1, ?_, ?_⟩
    · have := ball_subset_actionNbhd hI hb
      rwa [show rhoHat p / 16 + rhoHat p / 16 = rhoHat p / 8 by ring] at this
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      exact ((hih I hI).2.2.2.1 i).trans (H.ihat_const hMb₁.le)
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      exact ((hih I hI).2.2.2.2 i).trans (H.ihat_const hMb₂.le)
  · intro I hI J hJ
    have hΔ : DifferentiableOn ℂ (fun z => ihat z - z) (KAM.actionNbhd D (rhoHat p / 16)) :=
      hihd.sub differentiableOn_id
    have hAnn : 0 ≤ 10 * eHat p * rhoHat p := by positivity
    have hb : ∀ z ∈ KAM.actionNbhd D (rhoHat p / 16), ‖ihat z - z‖ ≤ 10 * eHat p * rhoHat p := by
      intro z hz
      refine (pi_norm_le_iff_of_nonneg hAnn).2 fun j => ?_
      refine ((hih z hz).2.2.1 j).trans ((H.ihat_const hMb.le).trans_eq ?_)
      rw [div_self hMb.ne']; ring
    have := lip_sup (S := D) (r := rhoHat p / 16) (A := 10 * eHat p * rhoHat p) (by positivity)
      hAnn hΔ hb I hI J hJ
    refine this.trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  · intro z hz
    obtain ⟨d1, d2, d3⟩ := hdisp z hz
    exact ⟨H.disp_first (norm_nonneg _) d1, H.disp_last (norm_nonneg _) d2,
      H.disp_theta (norm_nonneg _) d3⟩

end KAM.Planetary

end
