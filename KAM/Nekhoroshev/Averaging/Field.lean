/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Setting
public import KAM.Strip.Averages

/-!
# Part N12: field bounds and zero average (`bpN:p12:fbounds`, `bpN:p12:averaged`)

`fbounds` (steps `fb-poly`, `fb-cauchy`, `fb-real`): on `avgDomain`, the real partial fields
`avgA`, `avgB` of `Re (f ∘ ι)` are bounded by `2 / s` (Cauchy on the polydisc of radius `s / 2`),
and the Hamiltonian vector field of `avgH h f ε` is `(ω(I) + ε B, ε A)`.
`averaged`: the angle average of `avgA f (·, I)` over the unit cube vanishes (periodicity).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- The real part of `f` along the real inclusion. -/
private def avgF (f : AvgComplexPhase n → ℂ) (y : AvgPhase n) : ℝ :=
  (f (KAM.realInclusion₂ n y)).re

private theorem iota_mem (d : AveragingData n R s h f) {z : AvgPhase n} (hz : z ∈ Wdom n R s) :
    KAM.realInclusion₂ n z ∈ complexDomain n R s := by
  rw [← realInclusion₂_preimage_complexDomain d.hR d.hs] at hz
  exact hz

private theorem fDiff (d : AveragingData n R s h f) :
    DifferentiableOn ℂ f (complexDomain n R s) := d.hf.2.1

private theorem contDiffOn_avgF (d : AveragingData n R s h f) :
    ContDiffOn ℝ 1 (avgF f) (Wdom n R s) := by
  have hreg := (KAM.holomorphic_regularity_of_finiteDimensional (isOpen_complexDomain R s)
    (fDiff d)).2.2.1
  have hr := (hreg.restrict_scalars ℝ).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  exact Complex.reCLM.contDiff.comp_contDiffOn
    (hr.comp (KAM.realInclusion₂ n).contDiff.contDiffOn fun _ hz => iota_mem d hz)

private theorem hasFDerivAt_avgF (d : AveragingData n R s h f) {z : AvgPhase n}
    (hz : z ∈ Wdom n R s) :
    HasFDerivAt (avgF f)
      (Complex.reCLM.comp (((fderiv ℂ f (KAM.realInclusion₂ n z)).restrictScalars ℝ).comp
        (KAM.realInclusion₂ n))) z := by
  have hfd : DifferentiableAt ℂ f (KAM.realInclusion₂ n z) :=
    (fDiff d).differentiableAt ((isOpen_complexDomain R s).mem_nhds (iota_mem d hz))
  exact Complex.reCLM.hasFDerivAt.comp z
    ((hfd.hasFDerivAt.restrictScalars ℝ).comp z (KAM.realInclusion₂ n).hasFDerivAt)

private theorem fderiv_avgF_apply (d : AveragingData n R s h f) {z : AvgPhase n}
    (hz : z ∈ Wdom n R s) (v : AvgPhase n) :
    fderiv ℝ (avgF f) z v = (fderiv ℂ f (KAM.realInclusion₂ n z) (KAM.realInclusion₂ n v)).re := by
  rw [(hasFDerivAt_avgF d hz).fderiv]
  rfl

/-- `fb-cauchy`: the Cauchy estimate on the polydisc of radius `s / 2`. -/
private theorem norm_fderiv_le (d : AveragingData n R s h f) {z : AvgPhase n}
    (hz : z ∈ avgDomain n R) : ‖fderiv ℂ f (KAM.realInclusion₂ n z)‖ ≤ 2 / s := by
  have hs := d.hs
  have hball : closedBall (KAM.realInclusion₂ n z) (s / 2) ⊆ complexDomain n R s := by
    intro w hw
    have hw' : ‖w - KAM.realInclusion₂ n z‖ ≤ s / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    refine ⟨?_, z.2, hz.2, ?_⟩
    · have h1 : w.1 ∈ closedBall (KAM.realInclusion n z.1) (s / 2) := by
        rw [mem_closedBall, dist_eq_norm]
        exact (norm_fst_le _).trans hw'
      refine KAM.closedBall_subset_complexStrip (ρ := s) (δ := s / 2) ?_ h1
      intro i
      simp only [KAM.realInclusion_apply, Complex.ofReal_im, abs_zero]
      linarith
    · calc ‖w.2 - KAM.realInclusion n z.2‖ ≤ s / 2 := (norm_snd_le _).trans hw'
        _ < s := by linarith
  have := KAM.norm_fderiv_le_of_closedBall (isOpen_complexDomain R s) (fDiff d)
    (z := KAM.realInclusion₂ n z) (δ := s / 2) (A := 1) (by linarith) hball
    (fun w hw => by simpa using d.hf.2.2.2.2.2 w hw)
  convert this using 1
  field_simp

private theorem abs_fderiv_avgF_le (d : AveragingData n R s h f) {z : AvgPhase n}
    (hz : z ∈ avgDomain n R) {v : AvgPhase n} (hv : ‖v‖ ≤ 1) :
    |fderiv ℝ (avgF f) z v| ≤ 2 / s := by
  have hW := avgDomain_subset_Wdom d hz
  rw [fderiv_avgF_apply d hW]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine ((fderiv ℂ f _).le_opNorm _).trans ?_
  rw [KAM.norm_realInclusion₂]
  calc _ ≤ 2 / s * 1 := mul_le_mul (norm_fderiv_le d hz) hv (norm_nonneg _) (by have := d.hs; positivity)
    _ = 2 / s := mul_one _

private theorem norm_single_prod_fst (j : Fin n) : ‖((Pi.single j (1 : ℝ), 0) : AvgPhase n)‖ ≤ 1 := by
  simp [Prod.norm_def, Pi.norm_single]

private theorem norm_single_prod_snd (j : Fin n) : ‖((0, Pi.single j (1 : ℝ)) : AvgPhase n)‖ ≤ 1 := by
  simp [Prod.norm_def, Pi.norm_single]

private theorem avgA_apply (z : AvgPhase n) (j : Fin n) :
    avgA f z j = -fderiv ℝ (avgF f) z (Pi.single j 1, 0) := rfl

private theorem avgB_apply (z : AvgPhase n) (j : Fin n) :
    avgB f z j = fderiv ℝ (avgF f) z (0, Pi.single j 1) := rfl

private theorem freq_apply (I : Fin n → ℝ) (j : Fin n) :
    KAM.frequencyMap h I j = fderiv ℝ (realPart h) I (Pi.single j 1) := rfl

/-- `fb-real`: the perturbed Hamiltonian is `Re h + ε Re f` along the real inclusion. -/
private theorem avgH_eq (ε : ℝ) :
    avgH h f ε = fun y => realPart h y.2 + ε * avgF f y := by
  funext y
  show (h _ + (ε : ℂ) * f _).re = _
  rw [Complex.add_re, Complex.re_ofReal_mul]
  rfl

theorem fbounds (d : AveragingData n R s h f) :
    ∀ z ∈ avgDomain n R, ‖avgA f z‖ ≤ 2 / s ∧ ‖avgB f z‖ ≤ 2 / s ∧
      ∀ ε : ℝ, KAM.hamiltonianVectorField (avgH h f ε) z =
        (KAM.frequencyMap h z.2 + ε • avgB f z, ε • avgA f z) := by
  intro z hz
  have hW := avgDomain_subset_Wdom d hz
  have hs0 : 0 ≤ 2 / s := by have := d.hs; positivity
  refine ⟨?_, ?_, fun ε => ?_⟩
  · refine (pi_norm_le_iff_of_nonneg hs0).2 fun j => ?_
    rw [avgA_apply, Real.norm_eq_abs, abs_neg]
    exact abs_fderiv_avgF_le d hz (norm_single_prod_fst j)
  · refine (pi_norm_le_iff_of_nonneg hs0).2 fun j => ?_
    rw [avgB_apply, Real.norm_eq_abs]
    exact abs_fderiv_avgF_le d hz (norm_single_prod_snd j)
  · have hz2 : z.2 ∈ realActionDomain n R s := by
      rw [realActionDomain_eq d.hR d.hs]; exact hW.2
    have hg : DifferentiableAt ℝ (realPart h) z.2 :=
      ((d.hh.2.2.2.2.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_realActionDomain d.hR d.hs).mem_nhds hz2))
    have hH : HasFDerivAt (avgH h f ε)
        ((fderiv ℝ (realPart h) z.2).comp (ContinuousLinearMap.snd ℝ _ _) +
          ε • fderiv ℝ (avgF f) z) z := by
      rw [avgH_eq]
      exact (hg.hasFDerivAt.comp z (hasFDerivAt_snd)).add
        (((hasFDerivAt_avgF d hW).const_smul ε).congr_fderiv (by rw [(hasFDerivAt_avgF d hW).fderiv]))
    ext j
    · simp [KAM.hamiltonianVectorField, hH.fderiv, avgB_apply, freq_apply]
    · simp [KAM.hamiltonianVectorField, hH.fderiv, avgA_apply]

end KAM.Nekhoroshev

end
