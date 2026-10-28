/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import KAM.Canonical.Setting
public import KAM.Nekhoroshev.Stability.Setting
public import KAM.Weighted.Parametric

/-!
# Real preimages of a near-identity map (`bpN:p7:preimage`, `bpN:p7:preimage-nfl`)

A holomorphic map `Ψ` of `𝒟_{r',s'}`, real at real points, with displacement `Ψ - id` bounded by
`(dθ, dI)` and `max (dθ/σ', dI/ϱ') ≤ 1/4`, hits every real point `y ∈ ℝⁿ × D`. The proof is Banach's
fixed-point theorem for `x ↦ y - (Ψ - id)(x)` on the closed ball `{ν(x - y) ≤ κ}` of the scaled
norm `ν`, in the coordinates `u = W x` of the gauge `scaleCLE`, so that `ν` is the Pi sup norm;
the contraction constant `1/2` is the Cauchy estimate on the complex `ν`-ball of radius `1/2`.
-/

public noncomputable section

open Set Metric Function
open scoped NNReal

namespace KAM.Stability

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {n : ℕ}

/-- The real gauge `diag(σ⁻¹, ϱ⁻¹)` (real counterpart of `scaleCLE`). -/
private def realScale (ϱ σ : ℝ) (hϱ : 0 < ϱ) (hσ : 0 < σ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 σ⁻¹ (inv_ne_zero hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ϱ⁻¹ (inv_ne_zero hϱ.ne')))

private theorem scaleCLE_realInclusion₂ {ϱ σ : ℝ} (hϱ : 0 < ϱ) (hσ : 0 < σ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    scaleCLE ϱ σ hϱ hσ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n (realScale ϱ σ hϱ hσ x) := by
  ext i <;> simp [scaleCLE, realScale]

private theorem scaleCLE_symm_apply {ϱ σ : ℝ} (hϱ : 0 < ϱ) (hσ : 0 < σ)
    (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    (scaleCLE ϱ σ hϱ hσ).symm w = ((σ : ℂ) • w.1, (ϱ : ℂ) • w.2) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  ext i <;> simp [scaleCLE, hϱ.ne', hσ.ne']

/-- Points `W⁻¹ w` with `w` within `1/2` of `W ι x`, for `x` within `1/4` (scaled) of a real point
`y` with `y.2 ∈ D`, lie in `𝒟_{r',s'}`. -/
private theorem symm_mem_Dom {D : Set (Fin n → ℝ)} {r' s' ϱ' σ' : ℝ} (hϱ' : 0 < ϱ') (hϱr : ϱ' ≤ r')
    (hσ' : 0 < σ') (hσs : σ' ≤ 2 * s') {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y.2 ∈ D)
    {u : (Fin n → ℝ) × (Fin n → ℝ)} (hu : ‖u - realScale ϱ' σ' hϱ' hσ' y‖ ≤ 1 / 4)
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : ‖w - KAM.realInclusion₂ n u‖ < 1 / 2) :
    (scaleCLE ϱ' σ' hϱ' hσ').symm w ∈ Dom n (cpx D) r' s' := by
  have hw1 : ‖w.1 - KAM.realInclusion n u.1‖ < 1 / 2 :=
    lt_of_le_of_lt (by simpa using norm_fst_le (w - KAM.realInclusion₂ n u)) hw
  have hw2 : ‖w.2 - KAM.realInclusion n u.2‖ < 1 / 2 :=
    lt_of_le_of_lt (by simpa using norm_snd_le (w - KAM.realInclusion₂ n u)) hw
  have hu2 : ‖u.2 - ϱ'⁻¹ • y.2‖ ≤ 1 / 4 :=
    le_trans (by simpa [realScale] using norm_snd_le (u - realScale ϱ' σ' hϱ' hσ' y)) hu
  rw [scaleCLE_symm_apply]
  refine ⟨fun i => ?_, KAM.realInclusion n y.2, ⟨y.2, hy, rfl⟩, ?_⟩
  · have h1 : |((σ' : ℂ) • w.1 i).im| ≤ σ' * ‖w.1 - KAM.realInclusion n u.1‖ := by
      have : ((σ' : ℂ) • w.1 i).im = ((σ' : ℂ) • (w.1 i - KAM.realInclusion n u.1 i)).im := by
        simp
      rw [this]
      calc _ ≤ ‖(σ' : ℂ) • (w.1 i - KAM.realInclusion n u.1 i)‖ := Complex.abs_im_le_norm _
        _ = σ' * ‖w.1 i - KAM.realInclusion n u.1 i‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hσ'.le]
        _ ≤ σ' * ‖w.1 - KAM.realInclusion n u.1‖ := by
          gcongr
          exact norm_le_pi_norm (w.1 - KAM.realInclusion n u.1) i
    have h3 : σ' * ‖w.1 - KAM.realInclusion n u.1‖ < s' := by nlinarith
    exact lt_of_le_of_lt h1 h3
  · have h4 : ((ϱ' : ℂ) • w.2) - KAM.realInclusion n y.2 =
        (ϱ' : ℂ) • (w.2 - KAM.realInclusion n u.2) +
          (ϱ' : ℂ) • KAM.realInclusion n (u.2 - ϱ'⁻¹ • y.2) := by
      have hne : (ϱ' : ℂ) ≠ 0 := by exact_mod_cast hϱ'.ne'
      ext i
      simp
      field_simp
      ring
    show ‖(ϱ' : ℂ) • w.2 - KAM.realInclusion n y.2‖ < r'
    rw [h4]
    calc _ ≤ ‖(ϱ' : ℂ) • (w.2 - KAM.realInclusion n u.2)‖ +
          ‖(ϱ' : ℂ) • KAM.realInclusion n (u.2 - ϱ'⁻¹ • y.2)‖ := norm_add_le _ _
      _ = ϱ' * ‖w.2 - KAM.realInclusion n u.2‖ + ϱ' * ‖u.2 - ϱ'⁻¹ • y.2‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hϱ'.le,
          KAM.norm_realInclusion]
      _ < r' := by nlinarith

private theorem norm_realPartCLM₂_le (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖KAM.realPartCLM₂ n v‖ ≤ ‖v‖ := by
  simp only [KAM.realPartCLM₂_apply, Prod.norm_def]
  exact max_le_max (KAM.norm_realPartCLM_le _) (KAM.norm_realPartCLM_le _)

theorem preimage {D : Set (Fin n → ℝ)} {r' s' dθ dI ϱ' σ' : ℝ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hθ : ∀ z ∈ Dom n (cpx D) r' s', ‖(Ψ z).1 - z.1‖ ≤ dθ)
    (hI : ∀ z ∈ Dom n (cpx D) r' s', ‖(Ψ z).2 - z.2‖ ≤ dI)
    (hϱ' : 0 < ϱ') (hϱr : ϱ' ≤ r') (hσ' : 0 < σ') (hσs : σ' ≤ 2 * s')
    (hκ : max (dθ / σ') (dI / ϱ') ≤ 1 / 4) :
    ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D r',
      Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y ∧ ‖x.1 - y.1‖ ≤ dθ ∧ ‖x.2 - y.2‖ ≤ dI :=
  by
  intro y hy
  have hs' : 0 < s' := by linarith
  have hyD : KAM.realInclusion₂ n y ∈ Dom n (cpx D) r' s' :=
    (realInclusion₂_mem_Dom_iff D hs' y).2 ⟨trivial, y.2, hy, by simpa using (hϱ'.trans_le hϱr)⟩
  have hdθ : 0 ≤ dθ := (norm_nonneg _).trans (hθ _ hyD)
  have hdI : 0 ≤ dI := (norm_nonneg _).trans (hI _ hyD)
  set W := scaleCLE ϱ' σ' hϱ' hσ' with hW
  set Wr := realScale (n := n) ϱ' σ' hϱ' hσ' with hWr
  set κ := max (dθ / σ') (dI / ϱ') with hκdef
  have hκ0 : 0 ≤ κ := le_max_of_le_left (div_nonneg hdθ hσ'.le)
  set G : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
    fun w => W (Ψ (W.symm w) - W.symm w) with hG
  set U : Set ((Fin n → ℂ) × (Fin n → ℂ)) := W.symm ⁻¹' Dom n (cpx D) r' s' with hU
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
    rw [hW, norm_scaleCLE, scaledNorm]
    exact max_le_max (div_le_div_of_nonneg_right (hθ _ hw) hσ'.le)
      (div_le_div_of_nonneg_right (hI _ hw) hϱ'.le)
  have hball : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ball (KAM.realInclusion₂ n u) (1 / 2) ⊆ U :=
    fun u hu w hw => symm_mem_Dom hϱ' hϱr hσ' hσs hy hu (by simpa [mem_ball, dist_eq_norm] using hw)
  have hmemU : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → KAM.realInclusion₂ n u ∈ U :=
    fun u hu => hball u hu (mem_ball_self (by norm_num))
  set ψ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun u => KAM.realPartCLM₂ n (G (KAM.realInclusion₂ n u)) with hψ
  set L : (Fin n → ℝ) × (Fin n → ℝ) → ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))
    := fun u => (KAM.realPartCLM₂ n).comp
      (((fderiv ℂ G (KAM.realInclusion₂ n u)).restrictScalars ℝ).comp (KAM.realInclusion₂ n))
    with hL
  have hψd : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → HasFDerivAt ψ (L u) u := by
    intro u hu
    have hGd' : DifferentiableAt ℂ G (KAM.realInclusion₂ n u) :=
      hGd.differentiableAt (hUo.mem_nhds (hmemU u hu))
    exact (KAM.realPartCLM₂ n).hasFDerivAt.comp u
      ((hGd'.hasFDerivAt.restrictScalars ℝ).comp u (KAM.realInclusion₂ n).hasFDerivAt)
  have hLb : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ‖L u‖ ≤ 2 * κ := by
    intro u hu
    have hc : ‖fderiv ℂ G (KAM.realInclusion₂ n u)‖ ≤ κ / (1 / 2) :=
      general_cauchy (by norm_num) (hGd.mono (hball u hu))
        (fun a ha => hGb a (hball u hu ha))
    have hc' : ‖fderiv ℂ G (KAM.realInclusion₂ n u)‖ ≤ 2 * κ := by linarith
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
    calc ‖L u e‖ ≤ ‖fderiv ℂ G (KAM.realInclusion₂ n u) (KAM.realInclusion₂ n e)‖ :=
          norm_realPartCLM₂_le _
      _ ≤ ‖fderiv ℂ G (KAM.realInclusion₂ n u)‖ * ‖KAM.realInclusion₂ n e‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * κ * ‖e‖ := by
          rw [KAM.norm_realInclusion₂]
          gcongr
  have hψb : ∀ u, ‖u - Wr y‖ ≤ 1 / 4 → ‖ψ u‖ ≤ κ := fun u hu =>
    (norm_realPartCLM₂_le _).trans (hGb _ (hmemU u hu))
  set X : Set ((Fin n → ℝ) × (Fin n → ℝ)) := closedBall (Wr y) κ with hX
  have hXq : ∀ u ∈ X, ‖u - Wr y‖ ≤ 1 / 4 := fun u hu =>
    (by simpa [hX, dist_eq_norm] using hu : ‖u - Wr y‖ ≤ κ).trans hκ
  set T : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) := fun u => Wr y - ψ u with hT
  have hmaps : MapsTo T X X := fun u hu => by
    simpa [hX, hT, dist_eq_norm] using hψb u (hXq u hu)
  have hlip : ∀ u ∈ X, ∀ u' ∈ X, ‖ψ u - ψ u'‖ ≤ 1 / 2 * ‖u - u'‖ := by
    intro u hu u' hu'
    have := (convex_closedBall (Wr y) κ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := ψ) (f' := L) (C := 1 / 2) (fun v hv => (hψd v (hXq v hv)).hasFDerivWithinAt)
      (fun v hv => (hLb v (hXq v hv)).trans (by linarith)) hu' hu
    exact this
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
  have hsymm : W.symm (KAM.realInclusion₂ n u) = KAM.realInclusion₂ n x := by
    rw [ContinuousLinearEquiv.symm_apply_eq, hW, scaleCLE_realInclusion₂]
    show KAM.realInclusion₂ n u = KAM.realInclusion₂ n (Wr x)
    rw [hx, Wr.apply_symm_apply]
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' := by
    have := hmemU u hu4
    simpa only [hU, mem_preimage, hsymm] using this
  obtain ⟨z, hz⟩ := hΨreal x hxD
  have hψu : ψ u = Wr (z - x) := by
    have h1 : G (KAM.realInclusion₂ n u) = KAM.realInclusion₂ n (Wr (z - x)) := by
      show W (Ψ (W.symm (KAM.realInclusion₂ n u)) - W.symm (KAM.realInclusion₂ n u)) = _
      rw [hsymm, ← hz, ← map_sub, hW, scaleCLE_realInclusion₂]
    show KAM.realPartCLM₂ n (G (KAM.realInclusion₂ n u)) = _
    rw [h1, KAM.realPartCLM₂_realInclusion₂]
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
  have hΨx : Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y := by rw [← hz, hzy]
  refine ⟨x, (realInclusion₂_mem_Dom_iff D hs' x).1 hxD, hΨx, ?_, ?_⟩
  · have h := hθ _ hxD
    rw [hΨx] at h
    simpa [← map_sub, KAM.norm_realInclusion, norm_sub_rev] using h
  · have h := hI _ hxD
    rw [hΨx] at h
    simpa [← map_sub, KAM.norm_realInclusion, norm_sub_rev] using h

/-- `bpN:p7:preimage-nfl`: for any `Ψ` with the conclusions of `normal_form` (hypothesis (i), `κ ≥ 6`,
reality), every `y ∈ ℝⁿ × D` has a real preimage in `W_{r/2}`. Stated on the conclusions so that it is
applied to the witness of `normal_form`. -/
theorem preimage_nfl {D : Set (Fin n → ℝ)} {r s K α p ε : ℝ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hr : 0 < r) (hs : 0 < s) (hε0 : 0 ≤ ε)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hii : 6 ≤ 2 * Real.pi * K * s)
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) (r / 2) (s / 6)))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) (r / 2) (s / 6) →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hdisp : ∀ z ∈ Dom n (cpx D) (r / 2) (s / 6), ‖(Ψ z).2 - z.2‖ ≤ conjExp p * K * ε / α ∧
      ‖(Ψ z).1 - z.1‖ ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r)) :
    ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D (r / 2),
      Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y ∧
      ‖x.2 - y.2‖ ≤ conjExp p * K * ε / α ∧ conjExp p * K * ε / α ≤ r / 2 ^ 7 := by
  have hq : 0 < conjExp p := by
    unfold conjExp
    exact div_pos (by linarith) (by linarith)
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : ε * (2 ^ 7 * conjExp p * K) ≤ α * r := by
    have e : 1 / (2 ^ 7 * conjExp p) * (α * r / K) = α * r / (2 ^ 7 * conjExp p * K) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at hi
    exact hi
  have hdI : conjExp p * K * ε / α ≤ r / 2 ^ 7 := by
    rw [div_le_iff₀ hα]
    linarith
  have hqε : 0 ≤ conjExp p * ε := mul_nonneg hq.le hε0
  have hdθ : 10 * conjExp p * ε / (2 * Real.pi * α * r) / (s / 3) ≤ 30 / 768 := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have h2 : 0 ≤ 2 * Real.pi * s := by positivity
    have h3 : 0 ≤ α * r - ε * (2 ^ 7 * conjExp p * K) := by linarith
    have h4 : 0 ≤ 2 * Real.pi * K * s - 6 := by linarith
    nlinarith [mul_nonneg h2 h3, mul_nonneg hqε h4]
  intro y hy
  obtain ⟨x, hx, hΨx, -, hxI⟩ := preimage (D := D) (r' := r / 2) (s' := s / 6)
    (dθ := 10 * conjExp p * ε / (2 * Real.pi * α * r)) (dI := conjExp p * K * ε / α)
    (ϱ' := r / 2) (σ' := s / 3) hΨ hΨreal (fun z hz => (hdisp z hz).2) (fun z hz => (hdisp z hz).1)
    (by positivity) le_rfl (by positivity) (by linarith)
    (max_le (hdθ.trans (by norm_num)) (by
      rw [div_le_iff₀ (by positivity)]; linarith)) y hy
  exact ⟨x, hx, hΨx, hxI, hdI⟩

end KAM.Stability

end
