/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingRem

/-!
# P Part 5: Fourier and pointwise bounds of the physical remainder (`stepP:p5:av-R1`)

Conjugation by the normalization turns the P2 flat coefficients of `R` into the torus
coefficients of `avgRem R` (a factor `2π`, the same Fourier modes and width `w/6`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem unnormalize_assemble (I θ : Fin a → ℂ) (p q : Fin b → ℂ) :
    pgOscUnnormalize (assembleComplex I θ p q) =
      assembleComplex I ((2*Real.pi:ℂ)⁻¹ • θ) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • p)
        ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • q) := by
  simp only [pgOscUnnormalize, assembleComplex, blockFast_append, blockSlow_append]

theorem torusCoeff_avgRem (R : CHam (a+b)) (I : Fin a → ℂ) (x : PGComplexPhase b)
    (k : Fin a → ℤ) :
    KAM.torusCoeff (fun θ : Fin a → ℝ => avgRem R
      (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ) x.2 x.1)) k =
      (2*Real.pi:ℂ) * KAM.Weighted.coeff (oscFunction R)
        (Fin.append I (Fin.append ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2)
          ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1))) k := by
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  unfold KAM.Weighted.coeff
  rw [KAM.torusCoeffW_complex, ← torusCoeff_const_mul]
  congr 1
  funext θ
  simp only [avgRem, oscFunction, Function.comp]
  rw [show (fun j => (θ j : ℂ)) = KAM.realInclusion a θ from rfl, oscUnpack_flat,
    unnormalize_assemble, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem modeWeight_osc_sixth (d : PGData a b) (k : Fin a → ℤ) :
    KAM.Weighted.modeWeight (pgOscWidth d/6) k =
      Real.exp (pgWidth d/6 * KAM.Fourier.modeSize k) := by
  unfold KAM.Weighted.modeWeight pgOscWidth
  have := Real.pi_pos
  congr 1
  field_simp

theorem avg_rem_fourier (h : admissible d (pgRstar d) r mu) {R : CHam (a+b)}
    (hb : oscBound (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R (avgB d r mu))
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2))
    {x : PGComplexPhase b} (hx : ‖x‖ < pgOscRadius d/2) :
    KAM.Fourier.SummableWeighted (pgWidth d/6)
      (KAM.torusCoeff (fun θ : Fin a → ℝ => avgRem R
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ) x.2 x.1))) ∧
    KAM.Fourier.weightedNorm (pgWidth d/6)
      (KAM.torusCoeff (fun θ : Fin a → ℝ => avgRem R
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ) x.2 x.1))) ≤
      2 * (pgAnalytic d).LP * mu * r ^ 5 := by
  have hs := sqrt_two_pi_pos
  have hpi := Real.pi_pos
  have hε : ∀ v : Fin b → ℂ, ‖v‖ < pgOscRadius d/2 →
      ‖(Real.sqrt (2*Real.pi):ℂ)⁻¹ • v‖ < pgOscEpsilon d/2 := by
    intro v hv
    have e : ((Real.sqrt (2*Real.pi):ℂ))⁻¹ = (((Real.sqrt (2*Real.pi))⁻¹ : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e, norm_real_smul_lt_iff (inv_pos.2 hs)]
    unfold pgOscEpsilon
    have : pgOscRadius d / Real.sqrt (2*Real.pi) / 2 / (Real.sqrt (2*Real.pi))⁻¹ =
        pgOscRadius d / 2 := by field_simp
    rw [this]; exact hv
  have hx1 : ‖x.1‖ < pgOscRadius d/2 := (norm_fst_le x).trans_lt hx
  have hx2 : ‖x.2‖ < pgOscRadius d/2 := (norm_snd_le x).trans_lt hx
  have hmem : Fin.append I (Fin.append ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2)
      ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1)) ∈ oscParams (m := b) (checkedCore d r mu)
        ((params d r mu).rhoBar/2) (pgOscEpsilon d/2) (pgOscEpsilon d/2) := by
    refine ⟨?_, ?_, ?_⟩
    · rwa [show firstBlock (b := b+b) (Fin.append I (Fin.append ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2)
        ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1))) = I from blockFast_append _ _]
    · rw [show firstBlock (b := b) (lastBlock (a := a) (Fin.append I (Fin.append
        ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1)))) =
        (Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2 by
          show blockFast (blockSlow _) = _
          rw [blockSlow_append, blockFast_append]]
      exact hε _ hx2
    · rw [show lastBlock (a := b) (lastBlock (a := a) (Fin.append I (Fin.append
        ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1)))) =
        (Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1 by
          show blockSlow (blockSlow _) = _
          rw [blockSlow_append, blockSlow_append]]
      exact hε _ hx1
  obtain ⟨hS, hle⟩ := hb _ hmem
  have hc : ∀ k, ‖KAM.torusCoeff (fun θ : Fin a → ℝ => avgRem R
        (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a θ) x.2 x.1)) k‖ *
        Real.exp (pgWidth d/6 * KAM.Fourier.modeSize k) =
      2*Real.pi * (‖KAM.Weighted.coeff (oscFunction R) (Fin.append I (Fin.append
        ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.2) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • x.1))) k‖ *
        KAM.Weighted.modeWeight (pgOscWidth d/6) k) := by
    intro k
    rw [torusCoeff_avgRem, modeWeight_osc_sixth, norm_mul]
    have : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by
      simpa [abs_of_pos hpi] using Complex.norm_real (2*Real.pi)
    rw [this]; ring
  refine ⟨?_, ?_⟩
  · unfold KAM.Fourier.SummableWeighted
    simp_rw [hc]
    exact hS.mul_left _
  · unfold KAM.Fourier.weightedNorm
    simp_rw [hc]
    rw [tsum_mul_left]
    refine le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) ?_
    have := two_pi_avgB_le h
    linarith

theorem avg_rem_pointwise (h : admissible d (pgRstar d) r mu) {R : CHam (a+b)}
    (hcls : oscClass (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R)
    (hb : oscBound (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R (avgB d r mu)) :
    ∀ z ∈ averagingDomain d r mu, ‖avgRem R z‖ ≤ 2 * (pgAnalytic d).LP * mu * r ^ 5 := by
  intro z hz
  have hy := (mem_averagingDomain_iff h).1 hz
  have hP := isOpen_oscParams (m := b) (checkedCore d r mu) ((params d r mu).rhoBar/2)
    (pgOscEpsilon d/2) (pgOscEpsilon d/2)
  have := norm_le_of_wsum hP hcls.flat hb (oscPack (pgOscUnnormalize z)) hy
  rw [oscFunction, Function.comp, s_osc_data] at this
  unfold avgRem
  have hpi := Real.pi_pos
  rw [norm_mul]
  have h2 : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by
    simpa [abs_of_pos hpi] using Complex.norm_real (2*Real.pi)
  rw [h2]
  have := two_pi_avgB_le h
  nlinarith [mul_le_mul_of_nonneg_left ‹‖R (pgOscUnnormalize z)‖ ≤ avgB d r mu›
    (by positivity : (0:ℝ) ≤ 2*Real.pi)]

end KAM.Planetary

end
