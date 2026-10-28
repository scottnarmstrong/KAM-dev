/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyInvJac

/-!
# P Part 5: row-wise bounds for the derivative of the complex frequency map (`stepP:p5:fi-inv`)

For `mu ∈ (0, muStar]` and `J` in the analytic domain, any derivative `T0` of `complexFrequency`
satisfies the four estimates of `freq_inj`: `‖T0‖ ≤ C_U`, `‖v‖ ≤ (C_U/mu) ‖T0 v‖`, the fast block
of `T0⁻¹` is `O(1)` and the slow block of `T0` is `O(mu)` (`jacobian_bounds`). The proof estimates
the two block rows of `T0 v = w` against the constants of `PGAnalyticSpec` (`inv_apriori`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem norm_row_le {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X →L[ℂ] X →L[ℂ] ℂ) (E : Fin n → X) (hE : ∀ k, ‖E k‖ ≤ 1) (u : X) :
    ‖fun k => H u (E k)‖ ≤ ‖H‖ * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  calc ‖H u (E k)‖ ≤ ‖H u‖ * ‖E k‖ := (H u).le_opNorm _
    _ ≤ (‖H‖ * ‖u‖) * 1 := by
        gcongr
        · exact H.le_opNorm u
        · exact hE k
    _ = ‖H‖ * ‖u‖ := mul_one _

theorem norm_embFast_single (k : Fin a) : ‖embFast a b (Pi.single k 1)‖ ≤ 1 :=
  norm_embFast_single_le k

theorem norm_embSlow_single (k : Fin b) : ‖embSlow a b (Pi.single k (1 : ℂ))‖ ≤ 1 :=
  (norm_embSlow_le _).trans (norm_single_le_one_fin k)

theorem norm_real_smul_le (mu : ℝ) (hmu : 0 ≤ mu) {n : ℕ} (z : Fin n → ℂ) :
    ‖(mu : ℂ) • z‖ = mu * ‖z‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu]

theorem pgCU_ge (p : PGAnalytic) :
    p.M0 + p.AN + 1 ≤ pgCU p ∧ 4 * (p.AN + 1) ^ 2 * p.LB / p.c0 + 4 ≤ pgCU p ∧
      8 * p.LB + 4 ≤ pgCU p :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- Row-wise bounds for any derivative of the complex frequency map. -/
theorem jacobian_bounds (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 (pgAnalytic d).muStar)
    {J : Fin (a + b) → ℂ} (hJ : J ∈ analyticDomain d (pgAnalytic d))
    {T0 : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)}
    (hT0 : HasFDerivAt (complexFrequency d mu) T0 J) :
    (∀ v, ‖T0 v‖ ≤ pgCU (pgAnalytic d) * ‖v‖) ∧
    (∀ v, ‖v‖ ≤ pgCU (pgAnalytic d) / mu * ‖T0 v‖) ∧
    (∀ v, ‖blockFast v‖ ≤ pgCU (pgAnalytic d) * ‖T0 v‖) ∧
    (∀ v, ‖blockSlow (T0 v)‖ ≤ pgCU (pgAnalytic d) * mu * ‖v‖) := by
  have hspec := pgAnalytic_spec d
  have hCU := pgCU_ge (pgAnalytic d)
  set p := pgAnalytic d with hp
  obtain ⟨hρ0, hρδ, hc0, hM0, hAN, hLN, hLB, hμ0, hμ1, hμ2, -, -, -, -, -, -, e3, e4, -, hLNAN, -,
    hlow, hup, -, -, hpoly, hbeta, -⟩ := hspec
  have hδ := (pgExtension d).delta_pos
  have hmu0 : 0 < mu := hmu.1
  have hmuμ : mu ≤ p.muStar := hmu.2
  have hmu1 : mu ≤ 1 := hmuμ.trans hμ1
  have hAN0 : 0 ≤ p.AN := by linarith
  have hmu' : mu ∈ Icc 0 d.mu0 := ⟨hmu0.le, hmuμ.trans hμ2⟩
  have hI : blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho := hJ.1
  have hI2 : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) :=
    mem_actionNbhd_mono (by linarith) hI
  have hξ : ‖blockSlow J‖ < 1 := hJ.2
  have hJe : (Fin.append (blockFast J) (blockSlow J) : Fin (a + b) → ℂ) = J :=
    Fin.append_castAdd_natAdd
  have hH : ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ p.AN :=
    (hpoly mu hmu' J ⟨hI, by linarith⟩).2.2
  have hcF : DifferentiableAt ℂ (complexFast d) (blockFast J) :=
    (differentiableOn_complexFast d).differentiableAt ((isOpen_actionNbhd _ _).mem_nhds
      (mem_actionNbhd_mono (by linarith) hI))
  have hJcup : ‖fderiv ℂ (complexFast d) (blockFast J)‖ ≤ p.M0 :=
    hup _ (mem_actionNbhd_mono (by linarith) hI)
  have hJclow : ∀ u, p.c0 * ‖u‖ ≤ ‖fderiv ℂ (complexFast d) (blockFast J) u‖ :=
    lower_of_hasFDerivAt (isOpen_actionNbhd _ _) hlow hI hcF.hasFDerivAt
  have h3 : mu * p.AN ≤ p.c0 / 2 :=
    (mul_le_mul_of_nonneg_right hmuμ (by linarith)).trans e3
  have h4 : 4 * mu * p.AN ^ 2 * p.LB ≤ p.c0 := by
    have : 4 * mu * p.AN ^ 2 * p.LB ≤ 4 * p.muStar * p.AN ^ 2 * p.LB := by gcongr
    exact this.trans e4
  have hfast := jac_fast_eq d hmu' hI2 hT0
  have hslow := jac_slow_eq d hmu' hI2 hT0
  have hss := jac_slow_slow d hmu' hI2
  set H := fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J with hHdef
  set Jc := fderiv ℂ (complexFast d) (blockFast J) with hJcdef
  have hrowF : ∀ u, ‖fun k : Fin a => H u (embFast a b (Pi.single k 1))‖ ≤ p.AN * ‖u‖ :=
    fun u => (norm_row_le H _ (fun k => norm_embFast_single k) u).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hrowS : ∀ u, ‖fun k : Fin b => H u (embSlow a b (Pi.single k 1))‖ ≤ p.AN * ‖u‖ :=
    fun u => (norm_row_le H _ (fun k => norm_embSlow_single k) u).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hmuAN : mu * p.AN ≤ pgCU p * mu := by nlinarith [hCU.1, hM0]
  have hUp : ∀ v, ‖T0 v‖ ≤ pgCU p * ‖v‖ := by
    intro v
    have hfv : ‖blockFast (T0 v)‖ ≤ (p.M0 + p.AN) * ‖v‖ := by
      rw [hfast v]
      calc _ ≤ ‖Jc (blockFast v)‖ + ‖(mu : ℂ) • fun k : Fin a =>
            H v (embFast a b (Pi.single k 1))‖ := norm_add_le _ _
        _ ≤ p.M0 * ‖v‖ + mu * (p.AN * ‖v‖) := by
          rw [norm_real_smul_le mu hmu0.le]
          gcongr
          · exact (Jc.le_opNorm _).trans (mul_le_mul hJcup (norm_blockFast_le_norm v)
              (norm_nonneg _) (by linarith))
          · exact hrowF v
        _ ≤ (p.M0 + p.AN) * ‖v‖ := by
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hmu1) hAN0) (norm_nonneg v)]
    have hsv : ‖blockSlow (T0 v)‖ ≤ p.AN * ‖v‖ := by
      rw [hslow v, norm_real_smul_le mu hmu0.le]
      calc mu * ‖fun k : Fin b => H v (embSlow a b (Pi.single k 1))‖ ≤ mu * (p.AN * ‖v‖) := by
            gcongr; exact hrowS v
        _ ≤ p.AN * ‖v‖ := by
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hmu1) hAN0) (norm_nonneg v)]
    refine (norm_le_max_blocks _).trans (max_le ?_ ?_)
    · exact hfv.trans (mul_le_mul_of_nonneg_right (by linarith [hCU.1]) (norm_nonneg _))
    · exact hsv.trans (mul_le_mul_of_nonneg_right (by linarith [hCU.1]) (norm_nonneg _))
  have hSlow : ∀ v, ‖blockSlow (T0 v)‖ ≤ pgCU p * mu * ‖v‖ := by
    intro v
    rw [hslow v, norm_real_smul_le mu hmu0.le]
    calc mu * ‖fun k : Fin b => H v (embSlow a b (Pi.single k 1))‖ ≤ mu * (p.AN * ‖v‖) := by
          gcongr; exact hrowS v
      _ = (mu * p.AN) * ‖v‖ := by ring
      _ ≤ pgCU p * mu * ‖v‖ := mul_le_mul_of_nonneg_right hmuAN (norm_nonneg _)
  have hMain : ∀ v, ‖blockFast v‖ ≤ pgCU p * ‖T0 v‖ ∧ ‖v‖ ≤ pgCU p / mu * ‖T0 v‖ := by
    intro v
    have hv : v = embFast a b (blockFast v) + embSlow a b (blockSlow v) :=
      eq_embFast_add_embSlow v
    have hHv : ∀ e : Fin (a + b) → ℂ, H v e = H (embFast a b (blockFast v)) e +
        H (embSlow a b (blockSlow v)) e := by
      intro e
      conv_lhs => rw [hv]
      simp only [map_add, add_apply]
    set x := blockFast v with hx
    set y := blockSlow v with hy
    set w := T0 v with hw
    set A1 : Fin a → ℂ := fun k => H (embFast a b x) (embFast a b (Pi.single k 1)) with hA1
    set B1 : Fin a → ℂ := fun k => H (embSlow a b y) (embFast a b (Pi.single k 1)) with hB1
    set C1 : Fin b → ℂ := fun k => H (embFast a b x) (embSlow a b (Pi.single k 1)) with hC1
    have hfv : blockFast w = Jc x + (mu : ℂ) • (A1 + B1) := by
      rw [hw, hfast v]
      congr 2
      funext k
      simp only [Pi.add_apply, hA1, hB1, hHv]
    have hsv : blockSlow w = (mu : ℂ) • (C1 + (jetBeta d mu (blockFast J)).mulVec y) := by
      rw [hw, hslow v, ← hss y]
      congr 1
      funext k
      simp only [Pi.add_apply, hC1, hHv]
    have hA1n : ‖A1‖ ≤ p.AN * ‖x‖ := (hrowF _).trans
      (mul_le_mul_of_nonneg_left (norm_embFast_le _) hAN0)
    have hB1n : ‖B1‖ ≤ p.AN * ‖y‖ := (hrowF _).trans
      (mul_le_mul_of_nonneg_left (norm_embSlow_le _) hAN0)
    have hC1n : ‖C1‖ ≤ p.AN * ‖x‖ := (hrowS _).trans
      (mul_le_mul_of_nonneg_left (norm_embFast_le _) hAN0)
    have h1 : p.c0 * ‖x‖ ≤ ‖blockFast w‖ + mu * p.AN * ‖x‖ + mu * p.AN * ‖y‖ := by
      have hJx : Jc x = blockFast w - (mu : ℂ) • (A1 + B1) := by rw [hfv]; abel
      calc p.c0 * ‖x‖ ≤ ‖Jc x‖ := hJclow x
        _ ≤ ‖blockFast w‖ + mu * ‖A1 + B1‖ := by
          rw [hJx, ← norm_real_smul_le mu hmu0.le]; exact norm_sub_le _ _
        _ ≤ ‖blockFast w‖ + mu * (p.AN * ‖x‖ + p.AN * ‖y‖) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add hA1n hB1n)
        _ = _ := by ring
    have h2 : mu * ‖y‖ ≤ p.LB * (‖blockSlow w‖ + mu * p.AN * ‖x‖) := by
      have hβy : (mu : ℂ) • (jetBeta d mu (blockFast J)).mulVec y =
          blockSlow w - (mu : ℂ) • C1 := by rw [hsv, smul_add]; abel
      have hn : mu * ‖(jetBeta d mu (blockFast J)).mulVec y‖ ≤
          ‖blockSlow w‖ + mu * (p.AN * ‖x‖) := by
        rw [← norm_real_smul_le mu hmu0.le, hβy]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_real_smul_le mu hmu0.le]
        gcongr
      calc mu * ‖y‖ ≤ mu * (p.LB * ‖(jetBeta d mu (blockFast J)).mulVec y‖) := by
            gcongr; exact hbeta mu hmu' _ hI y
        _ = p.LB * (mu * ‖(jetBeta d mu (blockFast J)).mulVec y‖) := by ring
        _ ≤ p.LB * (‖blockSlow w‖ + mu * (p.AN * ‖x‖)) := by gcongr
        _ = _ := by ring
    obtain ⟨hX, hY⟩ := inv_apriori hmu0 hc0 hAN hLB h3 h4 (norm_nonneg x) (norm_nonneg _) h1 h2
    have hW : max ‖blockFast w‖ ‖blockSlow w‖ ≤ ‖w‖ :=
      max_le (norm_blockFast_le_norm w) (norm_blockSlow_le_norm w)
    have hW0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hCU0 : 0 ≤ pgCU p := by linarith [hCU.1, hM0, hAN]
    have hXc : ‖x‖ ≤ pgCU p * ‖w‖ := hX.trans (mul_le_mul hCU.2.1 hW (le_max_of_le_left
      (norm_nonneg _)) hCU0)
    refine ⟨hXc, ?_⟩
    have hYc : ‖y‖ ≤ pgCU p / mu * ‖w‖ := by
      have : (8 * p.LB + 4) / mu * max ‖blockFast w‖ ‖blockSlow w‖ ≤ pgCU p / mu * ‖w‖ :=
        mul_le_mul (div_le_div_of_nonneg_right hCU.2.2 hmu0.le) hW
          (le_max_of_le_left (norm_nonneg _)) (div_nonneg hCU0 hmu0.le)
      exact hY.trans this
    refine (norm_le_max_blocks v).trans (max_le ?_ hYc)
    refine hXc.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hmu0]
    have : 0 ≤ pgCU p * ‖w‖ := mul_nonneg hCU0 hW0
    nlinarith
  exact ⟨hUp, fun v => (hMain v).2, fun v => (hMain v).1, hSlow⟩

end KAM.Planetary

end
