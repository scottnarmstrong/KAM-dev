/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.AmountSetup
public import KAM.Planetary.Preparation.PreparedM

/-!
# The amount lemma (P11A-P8e, `bpP:p11:amount`)

The signed `amount`: the chosen prepared data `p11PreparedData D nu eps c3` satisfies
`P11PreparedFullSpec` and the scalar amount of `p11PreparedFreqR` on the prepared box is at
least `(1/2) eps^(mu+2) beta`. It follows from `prepared` and `amount_transfer`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Smooth

variable {n : ℕ}

/-- `checkW` is smooth on the ball of radius `5/4`: it is the rescaled real prepared frequency. -/
theorem p11_amt_chk_contDiff {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (heps : 0 < eps) (h5 : 5 * eps ≤ p11s2 (p11SecularData D) nu eps)
    (hs2 : 0 ≤ p11s2 (p11SecularData D) nu eps)
    (hA : P11SlowSpecOf (p11SecularData D) (p11FastData D eps) nu eps (p11SlowConstant D nu)
      (p11SlowData D nu eps)) (hσ : 0 < (p11SecularData D).sigma)
    (hQ : P11PreparedSpec D nu eps c Q) (k : ℕ) :
    ContDiffOn ℝ k Q.checkW (Metric.ball 0 (5 / 4)) := by
  obtain ⟨⟨hform, -⟩, -, -, -, -, -, -, -, -, -, hfr, -⟩ := hQ
  have hN : ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
      ((p11SlowData D nu eps).h0 (p11Rescale (p11SecularData D).J0 eps (0, I)).2 +
        (p11SlowData D nu eps).g2 (p11Rescale (p11SecularData D).J0 eps (0, I)).2) /
          (eps : ℂ) := fun I hI =>
    (hform (0, I) ⟨fun i => by simpa using div_pos hσ (by norm_num : (0 : ℝ) < 72), hI⟩).1
  have hWd := p11_pd_freq_diff (C := p11SecularData D) heps h5 hs2 hA hN
  have hcd := p11_pd_contdiff (p11_freq_isOpen_actionNbhd _ _) hWd k
  have hsub : Metric.ball (0 : P11Vec (n + n)) (5 / 4) ⊆
      KAM.realInclusion (n + n) ⁻¹' KAM.actionNbhd (p11PreparedBox n) 1 := fun y hy =>
    p11_prep_ball_mem (le_of_lt (mem_ball_zero_iff.1 hy))
  have hcd' := hcd.mono hsub
  have hg : ContDiffOn ℝ k (fun y : P11Vec (n + n) => (Fin.append
      (fun j : Fin n => p11PreparedFreqR Q y (Fin.castAdd n j))
      (fun j : Fin n => eps⁻¹ * p11PreparedFreqR Q y (Fin.natAdd n j)) : P11Vec (n + n)))
      (Metric.ball 0 (5 / 4)) := by
    refine contDiffOn_pi.2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using contDiffOn_pi.1 hcd' (Fin.castAdd n j)
    · simp only [Fin.append_right]
      exact contDiffOn_const.mul (contDiffOn_pi.1 hcd' (Fin.natAdd n j))
  refine hg.congr fun y hy => ?_
  have h := hfr y (le_of_lt (mem_ball_zero_iff.1 hy))
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have := congrFun h (Fin.castAdd n j)
    simp only [Fin.append_left] at this ⊢
    exact this.symm
  · have := congrFun h (Fin.natAdd n j)
    simp only [Fin.append_right] at this ⊢
    rw [this]
    field_simp

end Smooth

theorem amount {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ epsA c3 : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c3 ∧
    ∀ eps, 0 < eps → eps ≤ epsA →
      let Q := p11PreparedData D nu eps c3
      P11PreparedFullSpec D nu eps c3 Q ∧
      (1/2 : ℝ)*eps^((p11PatchData D).mu+2)*(p11PatchData D).beta ≤
        index_def 2 (p11PatchData D).mu (p11PreparedFreqR Q) (p11PreparedBox n) := by
  have hCF : P11SecularFullSpec D (p11SecularData D) := (holo_chart D).choose_spec
  have hC := hCF.1
  have hn : 1 ≤ n := by have := D.n_ge; omega
  obtain ⟨eps3, c3, he3, he31, hc31, hmain⟩ := prepared D hnu
  obtain ⟨e0, he0, he01, hsmall⟩ := p11_prep_small D hnu
  have hP : P11PatchSpec D (p11PatchData D) := (p11_patch D).choose_spec
  obtain ⟨-, -, hVo, -, hKc, hKne, hKV, -, -, -, hbpos, hvanal, -, hbeta, -⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, hJ0, -⟩ := id hC
  obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hJ0)
  have hvar : ContDiffOn ℝ (p11PatchData D).mu (p11PatchData D).varpi (p11PatchData D).V :=
    hvanal.contDiffOn hVo.uniqueDiffOn
  obtain ⟨L1, hL1, hjetL⟩ := p11_amt_jet_bound (k := (p11PatchData D).mu) hn hVo hKc hKV hvar
  obtain ⟨-, hτ0, -, -, -, -, -, -, -, -⟩ := fast_consts hC
  set mu := (p11PatchData D).mu with hmu
  set beta := (p11PatchData D).beta with hbeta_def
  set Qe : ℝ := 5 * (p11SecularData D).tau + 2 +
    ((p11SecularData D).tau + 1) * ((mu : ℝ) + 1) with hQe
  have hQe0 : 0 ≤ Qe := by
    have : (0 : ℝ) ≤ mu := Nat.cast_nonneg _
    rw [hQe]; positivity
  have hM0 : 0 ≤ c3 * 2 ^ (mu + 1) * (2 * L1 + 1) / beta := by
    have : 0 ≤ c3 := by linarith
    positivity
  obtain ⟨e2, he2, hX⟩ := p11_prep_eventually_le hM0 hQe0
  refine ⟨min eps3 (min e2 (min r0 e0)), c3, lt_min he3 (lt_min he2 (lt_min hr0 he0)),
    lt_of_le_of_lt (min_le_left _ _) he31, hc31, fun eps heps hle => ?_⟩
  have hle3 := hle.trans (min_le_left _ _)
  have hle2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hler := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle0 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he1 : eps ≤ 1 := hle3.trans he31.le
  obtain ⟨h5, hθ1, hex⟩ := hmain eps heps hle3
  obtain ⟨hεM, hzs, -, hF, hS, -⟩ := hsmall eps heps hle0
  have hQ : P11PreparedFullSpec D nu eps c3 (p11PreparedData D nu eps c3) := by
    unfold p11PreparedData
    rw [dif_pos hex]
    exact hex.choose_spec
  intro Q
  refine ⟨hQ, ?_⟩
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have hs2 : 0 ≤ p11s2 (p11SecularData D) nu eps := by linarith
  have hσ : 0 < (p11SecularData D).sigma := (fast_consts hC).2.2.2.2.2.1
  have hWd : ContDiffOn ℝ mu Q.checkW (Metric.ball 0 (5 / 4)) :=
    p11_amt_chk_contDiff heps h5 hs2 hS hσ hQ.1 mu
  set R := p11HalfCube n with hR
  have himgK : (fun r => (p11SecularData D).J0 + eps • r) '' R ⊆ (p11PatchData D).K := by
    rintro _ ⟨r, hr, rfl⟩
    refine hball ?_
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg heps.le]
    nlinarith [p11HalfCube_norm hr]
  have himgne : ((fun r => (p11SecularData D).J0 + eps • r) '' R).Nonempty :=
    p11HalfCube_nonempty.image _
  have hX' := hX eps heps hle2
  have hXn : 0 ≤ eps * Real.log (1 / eps) ^ Qe :=
    mul_nonneg heps.le (Real.rpow_nonneg (by linarith) _)
  set X := eps * Real.log (1 / eps) ^ Qe with hXdef
  have hth : c3 * eps * Real.log (1 / eps) ^ Qe = c3 * X := by rw [hXdef]; ring
  have hsm : (2 : ℝ) ^ mu * (c3 * eps * Real.log (1 / eps) ^ Qe) *
      (2 * L1 + c3 * eps * Real.log (1 / eps) ^ Qe) ≤ beta / 2 := by
    rw [hth]
    have h1 : c3 * X * (2 ^ (mu + 1) * (2 * L1 + 1)) ≤ beta := by
      have h2 : c3 * 2 ^ (mu + 1) * (2 * L1 + 1) / beta * X ≤ 1 := hX'
      rw [div_mul_eq_mul_div, div_le_one hbpos] at h2
      nlinarith
    have hθ : c3 * X ≤ 1 := by rw [← hth]; exact hθ1
    have hθ0 : 0 ≤ c3 * X := mul_nonneg (by linarith) hXn
    have hp : (0 : ℝ) < 2 ^ mu := by positivity
    calc (2 : ℝ) ^ mu * (c3 * X) * (2 * L1 + c3 * X)
        ≤ 2 ^ mu * (c3 * X) * (2 * L1 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (c3 * X * (2 ^ (mu + 1) * (2 * L1 + 1))) / 2 := by rw [pow_succ]; ring
      _ ≤ beta / 2 := by linarith
  have hθnn : 0 ≤ c3 * eps * Real.log (1 / eps) ^ Qe :=
    mul_nonneg (mul_nonneg (by linarith) heps.le) (Real.rpow_nonneg (by linarith) _)
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hfr, -⟩, -⟩ := id hQ
  have key := amount_transfer hn (U := Metric.ball 0 (5 / 4)) Metric.isOpen_ball hWd
    (p11SecularData D).J0 heps he1 (Rho := R) p11HalfCube_compact p11HalfCube_nonempty
    (fun r hr ρ hρ => by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (p11_amt_append_norm hr hρ) (by norm_num))
    hVo (himgK.trans hKV) hvar hL1 hθnn
    (p11_amt_jet_mono himgK hjetL)
    (fun ρ hρ => p11_amt_jet_mono (fun J hJ => by
        obtain ⟨r, hr, rfl⟩ := hJ
        show ‖(p11SecularData D).J0 + eps • r - (p11SecularData D).J0‖ < _
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg heps.le]
        nlinarith [p11HalfCube_norm hr])
      (hQ.2.2.1 ρ (lt_of_le_of_lt (p11HalfCube_norm hρ) (by norm_num))))
    ((hbeta).trans (index_def_anti (by omega : 1 ≤ n + n) 2 mu (p11PatchData D).varpi himgK
      himgne))
    hsm (K := p11PreparedBox n) ⟨0, fun _ _ => ⟨by norm_num, by norm_num⟩⟩
    (fun y hy => p11_amt_box_halfCube hy)
  have hKU : p11PreparedBox n ⊆ Metric.ball (0 : P11Vec (n + n)) (5 / 4) := fun y hy => by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_)
      (by norm_num : (1 / 2 : ℝ) < 5 / 4)
    have := hy i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hcongr := index_def_congr Metric.isOpen_ball hKU
    (w := fun y => p11DiagVec eps (Q.checkW y)) (w' := p11PreparedFreqR Q)
    (fun y hy => (hfr y (le_of_lt (mem_ball_zero_iff.1 hy))).symm) 2 mu
  rw [← hcongr]
  exact key

end KAM.Planetary

end
