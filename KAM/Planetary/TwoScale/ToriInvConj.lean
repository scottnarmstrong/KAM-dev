/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvStage

/-!
# Two-scale KAM: conjugation of the fields and bounded derivative (`stepP:p3:inv-conj`,
`stepP:p3:inv-dphi`)

On the real half-radius stage domain `𝒟_j × ℝⁿ` (open) the real stage map `ψ_j = psiR (Φ j)` is
differentiable, `X_H ∘ ψ_j = Dψ_j · X_{H_j}` (`conj_field`, from `real_symplectic_conjugation` and
the proved conjugacy `H ∘ Φ_j = h_j + f_j`), and `‖Dψ_j‖ ≤ 1 + κ₁κ₂/10` uniformly in `j`
(`psiR_fderiv_bound`), from the proved rescaled Lipschitz bound `‖Φ_j − id‖ ≤ 768 n Ê₀` and the
comparison of the rescaled norm with the max norm. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

theorem isOpen_phaseTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : IsOpen (phaseTube D r) :=
  isOpen_univ.prod ((isOpen_actionNbhd' D r).preimage (KAM.realInclusion n).continuous)

/-- The real stage map is differentiable on the real half-radius stage domain, with the
restriction of the complex derivative. -/
theorem PsiSteps.psiR_hasFDerivAt (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ)
    {x : Phase (a + b)} (hx : x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) :
    HasFDerivAt (psiR (Φ j)) ((KAM.realPartCLM₂ (a + b)).comp
      (((fderiv ℂ (Φ j) (KAM.realInclusion₂ (a + b) x)).restrictScalars ℝ).comp
        (KAM.realInclusion₂ (a + b)))) x := by
  have hz := P.incl_mem_stage j hx
  have hd : DifferentiableAt ℂ (Φ j) (KAM.realInclusion₂ (a + b) x) :=
    (P.phi_diff j).differentiableAt ((isOpen_coefficientDom _ _ _).mem_nhds hz)
  have h2 : HasFDerivAt (fun y => Φ j (KAM.realInclusion₂ (a + b) y))
      (((fderiv ℂ (Φ j) (KAM.realInclusion₂ (a + b) x)).restrictScalars ℝ).comp
        (KAM.realInclusion₂ (a + b))) x :=
    (hd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ (a + b)).hasFDerivAt
  exact (KAM.realPartCLM₂ (a + b)).hasFDerivAt.comp x h2

/-- `h ∘ snd + f` is holomorphic on the stage-`0` domain. -/
theorem kam_G_diff (H : KamHyp D sbar p h f) :
    DifferentiableOn ℂ (fun z : CPhase (a + b) => h z.2 + f z)
      (coefficientDom D p.ρ (sbar + p.s)) := by
  have hmemW : ∀ z ∈ coefficientDom D p.ρ (sbar + p.s), z.2 ∈ KAM.actionNbhd D p.ρ :=
    fun z hz => by rw [(conv_data D p.ρ (sbar + p.s)).2] at hz; exact hz.2
  exact (H.holo.comp differentiable_snd.differentiableOn hmemW).add H.f_class.differentiableOn

/-- `h ∘ snd + f` is real at the real points of the stage-`0` domain. -/
theorem kam_G_real (H : KamHyp D sbar p h f) (x : Phase (a + b))
    (hx : KAM.realInclusion₂ (a + b) x ∈ coefficientDom D p.ρ (sbar + p.s)) :
    ((fun z : CPhase (a + b) => h z.2 + f z) (KAM.realInclusion₂ (a + b) x)).im = 0 := by
  have h1 := H.real_h x hx
  have h2 := H.real_f x hx
  simp only [Complex.add_im]
  simp only at h1
  rw [h1, h2, add_zero]

/-- `stepP:p3:inv-conj` on the real half-radius stage domain: `X_H ∘ ψ_j = Dψ_j · X_{H_j}`. -/
theorem conj_field (H : KamHyp D sbar p h f) (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    (Q : StageSteps D sbar p h f Ds hs fs Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) :
    KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re)
      (psiR (Φ j) x) =
    fderiv ℝ (psiR (Φ j)) x (KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (hs j (KAM.realInclusion (a + b) z.2) + fs j (KAM.realInclusion₂ (a + b) z)).re) x) := by
  set V := coefficientDom (Ds j) (seq p j).ρ (sbar + (seq p j).s) with hV
  have hVo : IsOpen V := isOpen_coefficientDom _ _ _
  have himg : Φ j '' V ⊆ coefficientDom D p.ρ (sbar + p.s) := (Q.maps j).image_subset
  have hconj := real_symplectic_conjugation (G := fun z : CPhase (a + b) => h z.2 + f z) hVo
    (P.phi_diff j) ((kam_G_diff H).mono himg) (Q.symp j) (P.phi_real j)
    (fun y hy => kam_G_real H y (himg hy)) x (P.incl_mem_stage j hx)
  have hev : (fun y : Phase (a + b) => ((fun z : CPhase (a + b) => h z.2 + f z)
      (KAM.realInclusion₂ (a + b) (KAM.realPartCLM₂ (a + b)
        (Φ j (KAM.realInclusion₂ (a + b) y))))).re) =ᶠ[𝓝 x]
      fun y => (hs j (KAM.realInclusion (a + b) y.2) + fs j (KAM.realInclusion₂ (a + b) y)).re := by
    filter_upwards [(isOpen_phaseTube (Ds j) ((seq p j).ρ / 2)).mem_nhds hx] with y hy
    have e2 : KAM.realInclusion₂ (a + b) (KAM.realPartCLM₂ (a + b)
        (Φ j (KAM.realInclusion₂ (a + b) y))) = Φ j (KAM.realInclusion₂ (a + b) y) :=
      P.phi_real_pt j hy
    rw [e2]
    exact congrArg Complex.re (Q.conj j _ (P.incl_mem_stage j hy))
  have hH : KAM.hamiltonianVectorField (fun y : Phase (a + b) => ((fun z : CPhase (a + b) =>
      h z.2 + f z) (KAM.realInclusion₂ (a + b) (KAM.realPartCLM₂ (a + b)
        (Φ j (KAM.realInclusion₂ (a + b) y))))).re) x =
      KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (hs j (KAM.realInclusion (a + b) z.2) + fs j (KAM.realInclusion₂ (a + b) z)).re) x := by
    simp only [KAM.hamiltonianVectorField, hev.fderiv_eq]
  exact hconj.trans (congrArg (fderiv ℝ (psiR (Φ j)) x) hH)

end KAM.Planetary

end
