/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Weighted.Parametric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Real preimages of a near-identity map on the extended phase space (`bpN:p11:preimage`)

A holomorphic `Ψ` on `Dom n b.base R s`, real at real points, with displacement bounded by
`(dθ, dI, dx)` on the angles, the fast actions and the slow pair, hits every real `y` with
`fastAction y = b.Ic` and `λ • slowPair y ∈ b.S`, provided `max (dθ/σ, dI/ρ, dx/ρ) ≤ 1/4`.
The proof is Banach's fixed-point theorem for `u ↦ y - G(u)` on the closed `ν`-ball of radius
`κ` about `y`, in the gauge `diag(σ⁻¹, ρ⁻¹)` that turns `ν` into the Pi norm; the contraction
constant `1/2` is `general_cauchy` on the complex ball of radius `1/2` (an open ball).
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

private def preGaugeC (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) : EC n k ≃L[ℂ] EC n k :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((σ : ℂ)⁻¹) (by simpa using hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((ρ : ℂ)⁻¹) (by simpa using hρ.ne')))

private def preGaugeR (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) : ER n k ≃L[ℝ] ER n k :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 σ⁻¹ (inv_ne_zero hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ρ⁻¹ (inv_ne_zero hρ.ne')))

private theorem norm_preGaugeC {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (z : EC n k) :
    ‖preGaugeC ρ σ hρ hσ z‖ = max (‖z.1‖ / σ) (‖z.2‖ / ρ) := by
  simp [preGaugeC, Prod.norm_def, norm_smul, abs_of_pos hρ, abs_of_pos hσ, div_eq_inv_mul]

private theorem preGaugeC_symm {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (w : EC n k) :
    (preGaugeC ρ σ hρ hσ).symm w = ((σ : ℂ) • w.1, (ρ : ℂ) • w.2) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  ext i <;> simp [preGaugeC, hρ.ne', hσ.ne']

private theorem preGaugeC_extCx {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (u : ER n k) :
    preGaugeC ρ σ hρ hσ (extCx u) = extCx (preGaugeR ρ σ hρ hσ u) := by
  ext i <;> simp [preGaugeC, preGaugeR, extCx]

private theorem extCx_eq_pair (z : ER n k) :
    extCx z = (KAM.realInclusion n z.1, KAM.realInclusion (n+(k+k)) z.2) := by
  ext i <;> simp [extCx]

private theorem extCx_sub (a b : ER n k) : extCx (a - b) = extCx a - extCx b := by
  ext i <;> simp [extCx]

private theorem norm_extCx (z : ER n k) : ‖extCx z‖ = ‖z‖ := by
  rw [extCx_eq_pair, Prod.norm_def, Prod.norm_def, KAM.norm_realInclusion,
    KAM.norm_realInclusion]

/-- The real points of `EC n k` as a continuous `ℝ`-linear map. -/
private def preCxCLM (n k : ℕ) : ER n k →L[ℝ] EC n k :=
  (KAM.realInclusion n).prodMap (KAM.realInclusion (n+(k+k)))

private theorem preCxCLM_apply (z : ER n k) : preCxCLM n k z = extCx z := (extCx_eq_pair z).symm

/-- The real part as a continuous `ℝ`-linear map. -/
private def preReCLM (n k : ℕ) : EC n k →L[ℝ] ER n k :=
  (KAM.realPartCLM n).prodMap (KAM.realPartCLM (n+(k+k)))

private theorem preReCLM_apply (z : EC n k) : preReCLM n k z = extRe z := rfl

private theorem preReCLM_extCx (z : ER n k) : preReCLM n k (extCx z) = z := by
  ext i <;> simp [preReCLM_apply, extRe, extCx]

private theorem norm_preReCLM_le (v : EC n k) : ‖preReCLM n k v‖ ≤ ‖v‖ := by
  show ‖(KAM.realPartCLM n v.1, KAM.realPartCLM (n+(k+k)) v.2)‖ ≤ ‖v‖
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le_max (KAM.norm_realPartCLM_le _) (KAM.norm_realPartCLM_le _)

private theorem norm_snd_sub_le (a b : EC n k) :
    ‖a.2 - b.2‖ ≤ max ‖fastAction a - fastAction b‖ ‖slowPair a - slowPair b‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine le_max_of_le_left ?_
    simpa [fastAction] using norm_le_pi_norm (fastAction a - fastAction b) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine le_max_of_le_right ?_
      have h := norm_le_pi_norm (slowPair a - slowPair b).1 l
      refine le_trans ?_ (h.trans (le_max_left _ _))
      simp [slowPair]
    · refine le_max_of_le_right ?_
      have h := norm_le_pi_norm (slowPair a - slowPair b).2 l
      refine le_trans ?_ (h.trans (le_max_right _ _))
      simp [slowPair]

private theorem fastAction_extCx (y : ER n k) :
    fastAction (extCx y) = KAM.realInclusion n (fastAction y) := by
  ext i; simp [fastAction, extCx]

private theorem norm_fastAction_extCx_sub (x y : ER n k) :
    ‖fastAction (extCx y) - fastAction (extCx x)‖ = ‖fastAction y - fastAction x‖ := by
  rw [fastAction_extCx, fastAction_extCx, ← map_sub, KAM.norm_realInclusion]

private theorem norm_slowPair_extCx_sub (x y : ER n k) :
    ‖slowPair (extCx y) - slowPair (extCx x)‖ = ‖slowPair y - slowPair x‖ := by
  have h : slowPair (extCx y) - slowPair (extCx x) =
      (KAM.realInclusion k ((slowPair y - slowPair x).1),
        KAM.realInclusion k ((slowPair y - slowPair x).2)) := by
    ext i <;> simp [slowPair, extCx]
  rw [h, Prod.norm_def, Prod.norm_def, KAM.norm_realInclusion, KAM.norm_realInclusion]

/-- A real point with the prescribed fast action and a slow pair in `λ⁻¹ S` lies on the base. -/
private theorem extCx_snd_mem_base (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w)
    {y : ER n k} (hI : fastAction y = b.Ic) (hS : b.lam • slowPair y ∈ b.S) :
    (extCx y).2 ∈ b.base := by
  have hlam : b.lam ≠ 0 := (div_pos hbw hbR).ne'
  refine ⟨b.lam • slowPair y, hS, ?_⟩
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have := congrFun hI j
    simp [extCx, Fin.append_left, ← this, fastAction]
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp [extCx, Fin.append_right, Fin.append_left, slowPair, hlam]
    · simp only [extCx, Fin.append_right, slowPair, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      have hc : (b.lam : ℂ) ≠ 0 := by exact_mod_cast hlam
      push_cast
      field_simp

/-- Points `W⁻¹ w` with `w` within `1/2` of `W ι u`, for `u` within `1/4` (scaled) of the real
point `y` on the base, lie in `Dom n b.base R s`. -/
private theorem symm_mem_Dom (b : PartialBlock n k) {R s ρ σ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hσ : 0 < σ) (hσs : σ ≤ 2 * s) {y : ER n k} (hy : (extCx y).2 ∈ b.base)
    {u : ER n k} (hu : ‖u - preGaugeR ρ σ hρ hσ y‖ ≤ 1 / 4)
    {w : EC n k} (hw : ‖w - extCx u‖ < 1 / 2) :
    (preGaugeC ρ σ hρ hσ).symm w ∈ Dom n b.base R s := by
  have hw1 : ‖w.1 - (extCx u).1‖ < 1 / 2 :=
    lt_of_le_of_lt (by simpa using norm_fst_le (w - extCx u)) hw
  have hw2 : ‖w.2 - (extCx u).2‖ < 1 / 2 :=
    lt_of_le_of_lt (by simpa using norm_snd_le (w - extCx u)) hw
  have hu2 : ‖u.2 - ρ⁻¹ • y.2‖ ≤ 1 / 4 :=
    le_trans (by simpa [preGaugeR] using norm_snd_le (u - preGaugeR ρ σ hρ hσ y)) hu
  rw [preGaugeC_symm]
  refine ⟨fun i => ?_, (extCx y).2, hy, ?_⟩
  · have h1 : |((σ : ℂ) • w.1 i).im| ≤ σ * ‖w.1 - (extCx u).1‖ := by
      have : ((σ : ℂ) • w.1 i).im = ((σ : ℂ) • (w.1 i - (extCx u).1 i)).im := by
        simp [extCx]
      rw [this]
      calc _ ≤ ‖(σ : ℂ) • (w.1 i - (extCx u).1 i)‖ := Complex.abs_im_le_norm _
        _ = σ * ‖w.1 i - (extCx u).1 i‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
        _ ≤ σ * ‖w.1 - (extCx u).1‖ := by
          gcongr
          exact norm_le_pi_norm (w.1 - (extCx u).1) i
    have h3 : σ * ‖w.1 - (extCx u).1‖ < s := by nlinarith
    exact lt_of_le_of_lt h1 h3
  · have h4 : ((ρ : ℂ) • w.2) - (extCx y).2 =
        (ρ : ℂ) • (w.2 - (extCx u).2) +
          (ρ : ℂ) • KAM.realInclusion (n+(k+k)) (u.2 - ρ⁻¹ • y.2) := by
      have hne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      ext i
      simp [extCx]
      field_simp
      ring
    show ‖(ρ : ℂ) • w.2 - (extCx y).2‖ < R
    rw [h4]
    calc _ ≤ ‖(ρ : ℂ) • (w.2 - (extCx u).2)‖ +
          ‖(ρ : ℂ) • KAM.realInclusion (n+(k+k)) (u.2 - ρ⁻¹ • y.2)‖ := norm_add_le _ _
      _ = ρ * ‖w.2 - (extCx u).2‖ + ρ * ‖u.2 - ρ⁻¹ • y.2‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          KAM.norm_realInclusion]
      _ < R := by nlinarith

/-- `bpN:p11:preimage`: real preimages of a near-identity map. -/
theorem preimage (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w)
    {R s dθ dI dx ρ σ : ℝ} {Ψ : EC n k → EC n k}
    (hΨ : DifferentiableOn ℂ Ψ (Dom n b.base R s))
    (hr : ∀ y : ER n k, extCx y ∈ Dom n b.base R s → extCx (reExtMap Ψ y) = Ψ (extCx y))
    (hb : ∀ z ∈ Dom n b.base R s,
      ‖(Ψ z).1-z.1‖ ≤ dθ ∧ ‖fastAction (Ψ z)-fastAction z‖ ≤ dI ∧
        ‖slowPair (Ψ z)-slowPair z‖ ≤ dx)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hσ : 0 < σ) (hσs : σ ≤ 2*s)
    (hsmall : max (dθ/σ) (max (dI/ρ) (dx/ρ)) ≤ 1/4) :
    ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom R, Ψ (extCx x) = extCx y ∧
        ‖x.1-y.1‖ ≤ dθ ∧ ‖fastAction x-b.Ic‖ ≤ dI ∧ ‖slowPair x-slowPair y‖ ≤ dx := by
  intro y hI hS
  have hs : 0 < s := by linarith
  have hyb : (extCx y).2 ∈ b.base := extCx_snd_mem_base b hbR hbw hI hS
  have hyD : extCx y ∈ Dom n b.base R s :=
    ⟨KAM.ofReal_mem_complexStrip hs y.1, (extCx y).2, hyb, by simpa using (hρ.trans_le hρR)⟩
  obtain ⟨h1, h2, h3⟩ := hb _ hyD
  have hdθ : 0 ≤ dθ := (norm_nonneg _).trans h1
  have hdI : 0 ≤ dI := (norm_nonneg _).trans h2
  have hdx : 0 ≤ dx := (norm_nonneg _).trans h3
  set W := preGaugeC ρ σ hρ hσ (n := n) (k := k) with hW
  set Wr := preGaugeR ρ σ hρ hσ (n := n) (k := k) with hWr
  set κ := max (dθ / σ) (max (dI / ρ) (dx / ρ)) with hκdef
  have hκ0 : 0 ≤ κ := le_max_of_le_left (div_nonneg hdθ hσ.le)
  set G : EC n k → EC n k := fun w => W (Ψ (W.symm w) - W.symm w) with hG
  set U : Set (EC n k) := W.symm ⁻¹' Dom n b.base R s with hU
  have hUo : IsOpen U := (isOpen_Dom _ _ _).preimage W.symm.continuous
  have hGd : DifferentiableOn ℂ G U := by
    intro w hw
    have h1 : DifferentiableAt ℂ Ψ (W.symm w) :=
      (hΨ _ hw).differentiableAt ((isOpen_Dom _ _ _).mem_nhds hw)
    exact (W.differentiableAt.comp w
      ((h1.comp w W.symm.differentiableAt).sub W.symm.differentiableAt)).differentiableWithinAt
  have hGb : ∀ w ∈ U, ‖G w‖ ≤ κ := by
    intro w hw
    show ‖W (Ψ (W.symm w) - W.symm w)‖ ≤ κ
    obtain ⟨a1, a2, a3⟩ := hb _ hw
    rw [hW, norm_preGaugeC]
    refine max_le (le_max_of_le_left ?_) (le_max_of_le_right ?_)
    · exact div_le_div_of_nonneg_right (by simpa using a1) hσ.le
    · rw [max_div_div_right hρ.le]
      exact div_le_div_of_nonneg_right (le_trans (by simpa using norm_snd_sub_le _ _)
        (max_le_max a2 a3)) hρ.le
  have hball : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ball (extCx u) (1 / 2) ⊆ U :=
    fun u hu w hw =>
      symm_mem_Dom b hρ hρR hσ hσs hyb hu (by simpa [mem_ball, dist_eq_norm] using hw)
  have hmemU : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → extCx u ∈ U :=
    fun u hu => hball u hu (mem_ball_self (by norm_num))
  set ψ : ER n k → ER n k := fun u => preReCLM n k (G (extCx u)) with hψ
  set L : ER n k → ER n k →L[ℝ] ER n k := fun u => (preReCLM n k).comp
      (((fderiv ℂ G (extCx u)).restrictScalars ℝ).comp (preCxCLM n k)) with hL
  have hψd : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → HasFDerivAt ψ (L u) u := by
    intro u hu
    have hGd' : DifferentiableAt ℂ G (extCx u) :=
      hGd.differentiableAt (hUo.mem_nhds (hmemU u hu))
    have hc : HasFDerivAt (fun v => extCx v) (preCxCLM n k) u := by
      have : (fun v : ER n k => extCx v) = preCxCLM n k :=
        funext fun v => (preCxCLM_apply v).symm
      rw [this]; exact (preCxCLM n k).hasFDerivAt
    have hG' : HasFDerivAt G (fderiv ℂ G (extCx u)) (extCx u) := hGd'.hasFDerivAt
    exact (preReCLM n k).hasFDerivAt.comp u ((hG'.restrictScalars ℝ).comp u hc)
  have hLb : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ‖L u‖ ≤ 2 * κ := by
    intro u hu
    have hc : ‖fderiv ℂ G (extCx u)‖ ≤ κ / (1 / 2) :=
      general_cauchy (by norm_num) (hGd.mono (hball u hu))
        (fun a ha => hGb a (hball u hu ha))
    have hc' : ‖fderiv ℂ G (extCx u)‖ ≤ 2 * κ := by linarith
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
    calc ‖L u e‖ ≤ ‖fderiv ℂ G (extCx u) (extCx e)‖ := by
          show ‖preReCLM n k (fderiv ℂ G (extCx u) (preCxCLM n k e))‖ ≤ _
          rw [preCxCLM_apply]
          exact norm_preReCLM_le _
      _ ≤ ‖fderiv ℂ G (extCx u)‖ * ‖extCx e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * κ * ‖e‖ := by
          rw [norm_extCx]
          gcongr
  have hψb : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ‖ψ u‖ ≤ κ := fun u hu =>
    (norm_preReCLM_le _).trans (hGb _ (hmemU u hu))
  set X : Set (ER n k) := closedBall (Wr y) κ with hX
  have hXq : ∀ u ∈ X, ‖u - Wr y‖ ≤ 1 / 4 := fun u hu =>
    (by simpa [hX, dist_eq_norm] using hu : ‖u - Wr y‖ ≤ κ).trans hsmall
  set T : ER n k → ER n k := fun u => Wr y - ψ u with hT
  have hmaps : MapsTo T X X := fun u hu => by
    simpa [hX, hT, dist_eq_norm] using hψb u (hXq u hu)
  have hlip : ∀ u ∈ X, ∀ u' ∈ X, ‖ψ u - ψ u'‖ ≤ 1 / 2 * ‖u - u'‖ := by
    intro u hu u' hu'
    exact (convex_closedBall (Wr y) κ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := ψ) (f' := L) (C := 1 / 2) (fun v hv => (hψd v (hXq v hv)).hasFDerivWithinAt)
      (fun v hv => (hLb v (hXq v hv)).trans (by linarith)) hu' hu
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict T X X) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm, hT]
    have h := hlip b.1 b.2 a.1 a.2
    have e1 : Wr y - ψ a.1 - (Wr y - ψ b.1) = ψ b.1 - ψ a.1 := by abel
    rw [e1, norm_sub_rev a.1 b.1] at *
    push_cast
    exact h
  obtain ⟨u, huX, hfix, -⟩ := ContractingWith.exists_fixedPoint' (isClosed_closedBall.isComplete)
    hmaps hcontr (mem_closedBall_self hκ0) (edist_ne_top _ _)
  have hu4 := hXq u huX
  set x := Wr.symm u with hx
  have hsymm : W.symm (extCx u) = extCx x := by
    rw [ContinuousLinearEquiv.symm_apply_eq, hW, preGaugeC_extCx]
    show extCx u = extCx (Wr x)
    rw [hx, Wr.apply_symm_apply]
  have hxD : extCx x ∈ Dom n b.base R s := by
    have := hmemU u hu4
    simpa only [hU, mem_preimage, hsymm] using this
  set z := reExtMap Ψ x with hz
  have hzx : extCx z = Ψ (extCx x) := hr x hxD
  have hψu : ψ u = Wr (z - x) := by
    have h1 : G (extCx u) = extCx (Wr (z - x)) := by
      show W (Ψ (W.symm (extCx u)) - W.symm (extCx u)) = _
      rw [hsymm, ← hzx, ← extCx_sub, hW, preGaugeC_extCx]
    show preReCLM n k (G (extCx u)) = _
    rw [h1, preReCLM_extCx]
  have h2 : Wr (y - (z - x)) = Wr x := by
    rw [map_sub, ← hψu, hx, Wr.apply_symm_apply]
    exact hfix
  have h3 : y - (z - x) = x := Wr.injective h2
  have hzy : z = y := by
    have h4 : y - z + x = 0 + x :=
      calc y - z + x = y - (z - x) := by abel
        _ = x := h3
        _ = 0 + x := (zero_add x).symm
    exact (sub_eq_zero.1 (add_right_cancel h4)).symm
  have hΨx : Ψ (extCx x) = extCx y := by rw [← hzx, hzy]
  obtain ⟨c1, c2, c3⟩ := hb _ hxD
  rw [hΨx] at c1 c2 c3
  refine ⟨x, ?_, hΨx, ?_, ?_, ?_⟩
  · exact ⟨KAM.ofReal_mem_complexStrip one_pos x.1, hxD.2⟩
  · have : ‖(extCx y).1 - (extCx x).1‖ = ‖y.1 - x.1‖ := by
      rw [extCx_eq_pair, extCx_eq_pair, ← map_sub, KAM.norm_realInclusion]
    rw [this, norm_sub_rev] at c1
    exact c1
  · rw [norm_fastAction_extCx_sub, hI, norm_sub_rev] at c2
    exact c2
  · rw [norm_slowPair_extCx_sub, norm_sub_rev] at c3
    exact c3

end KAM.Nekhoroshev

end
