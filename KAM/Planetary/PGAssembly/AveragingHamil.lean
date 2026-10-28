/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingConj

/-!
# P Part 5: the Hamiltonian identity of the averaging record (`stepP:p5:av-id`)

Multiplying the P2 identity by `2π` turns `h∘Ψ + μ P(Ψ)` into `H̃₀ + mu P̃` along the physical map;
the zero Fourier coefficient is the actual `complexAverage` (`pg_osc_zero`), which is the sum of
the integrable jet polynomial and the Birkhoff remainder by definition of `pgRemainder`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ} {Ψ : CPhase (a+b) → CPhase (a+b)}
  {R : CHam (a+b)}

theorem avgV_subset_zero_dom (h : admissible d (pgRstar d) r mu) :
    avgV d r mu ⊆ oscDom (closure d.V) ((pgExtension d).delta/2) (pgOscEpsilon d)
      (pgOscEpsilon d) (pgOscWidth d) := by
  intro y hy
  obtain ⟨y1, y2, y3, y4⟩ := mem_oscDom_pg.1 hy
  have he : 0 < pgOscEpsilon d := by unfold pgOscEpsilon; have := pgOscRadius_pos d; positivity
  have hw : 0 < pgOscWidth d := by unfold pgOscWidth; have := pgWidth_pos d; positivity
  refine mem_oscDom_pg.2 ⟨pgAv_strip_mono (by linarith) y1, ?_, y3.trans (by linarith),
    y4.trans (by linarith)⟩
  have := actionNbhd_checkedCore_le h (s := (params d r mu).rhoBar/2)
    (t := (pgExtension d).delta/2)
    (by linarith [av_rhoBar_lt_delta h, (pgExtension d).delta_pos]) y2
  exact this

theorem blockSlow_unnormalize_fst (z : CPhase (a+b)) :
    blockSlow (pgOscUnnormalize z).1 = (Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.1 :=
  pgAv_blockSlow_append _ _

theorem blockSlow_unnormalize_snd (z : CPhase (a+b)) :
    blockSlow (pgOscUnnormalize z).2 = (Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.2 :=
  pgAv_blockSlow_append _ _

theorem blockFast_unnormalize_snd (z : CPhase (a+b)) :
    blockFast (pgOscUnnormalize z).2 = blockFast z.2 := pgAv_blockFast_append _ _

theorem avg_hamil (h : admissible d (pgRstar d) r mu)
    (hm : ∀ z ∈ avgV d r mu,
      pgOscH d (firstBlock (b := b) (Ψ z).2) + (pgOscE d mu : ℂ) * pgOscP d mu (Ψ z) =
        pgOscH d (firstBlock (b := b) z.2) + (pgOscE d mu : ℂ) *
          KAM.Weighted.coeff (oscFunction (pgOscP d mu)) (oscPack z).2 0 + R z) :
    ∀ z ∈ averagingDomain d r mu,
      (pgExtension d).H0 (blockFast (pgAvPsi Ψ z).2) + mu * (pgExtension d).P mu (pgAvPsi Ψ z) =
        complexIntegrable d mu (Fin.append (blockFast z.2)
          (fun j => ((blockSlow z.1 j)^2 + (blockSlow z.2 j)^2)/2)) +
        mu * pgRemainder d mu (blockFast z.2) (blockSlow z.1, blockSlow z.2) + avgRem R z := by
  intro z hz
  have hy := (mem_averagingDomain_iff h).1 hz
  have hm' : pgOscH d (blockFast (Ψ (pgOscUnnormalize z)).2) + (pgOscE d mu : ℂ) *
      pgOscP d mu (Ψ (pgOscUnnormalize z)) = pgOscH d (blockFast (pgOscUnnormalize z).2) +
      (pgOscE d mu : ℂ) * KAM.Weighted.coeff (oscFunction (pgOscP d mu))
        (oscPack (pgOscUnnormalize z)).2 0 + R (pgOscUnnormalize z) := hm _ hy
  have hzero := pg_osc_zero d mu (av_mu_mem h) _ (avgV_subset_zero_dom h hy)
  have hpi := Real.pi_pos
  have hLP := pgAnalytic_LP_ge_one d
  have hLP' : ((pgAnalytic d).LP : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (pgAnalytic d).LP ≠ 0)
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hs : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := by
    exact_mod_cast sqrt_two_pi_pos.ne'
  have e1 : (Real.sqrt (2*Real.pi):ℂ) • blockSlow (pgOscUnnormalize z).1 = blockSlow z.1 := by
    rw [blockSlow_unnormalize_fst, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have e2 : (Real.sqrt (2*Real.pi):ℂ) • blockSlow (pgOscUnnormalize z).2 = blockSlow z.2 := by
    rw [blockSlow_unnormalize_snd, smul_smul, mul_inv_cancel₀ hs, one_smul]
  rw [hzero, e1, e2, blockFast_unnormalize_snd] at hm'
  have hjet : complexAverage d mu (blockFast z.2) (blockSlow z.1, blockSlow z.2) =
      jetPolynomial d mu (Fin.append (blockFast z.2)
        (fun j => ((blockSlow z.1 j)^2 + (blockSlow z.2 j)^2)/2)) +
      pgRemainder d mu (blockFast z.2) (blockSlow z.1, blockSlow z.2) := by
    unfold pgRemainder; ring
  rw [hjet] at hm'
  unfold complexIntegrable
  rw [pgAv_blockFast_append]
  simp only [pgAvPsi, avgRem, blockFast_normalize_snd]
  simp only [pgOscH, pgOscP, pgOscE, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat] at hm'
  field_simp at hm'
  field_simp
  linear_combination hm'

end KAM.Planetary

end
