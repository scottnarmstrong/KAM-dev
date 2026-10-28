/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.AffineFlowGauge

/-!
# Affine flow: trajectories and the simple form (P11A-C6)

`stepP:p11a:af-simple`: the angle component of the flow does not depend on the action
(uniqueness for `θ' = p1 θ`), and the action component is affine in the initial action
(affine combinations of trajectories are trajectories; uniqueness of the flow of
`bpN:p5:flow`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {r s sigma A : ℝ}

/-- The angle component of a trajectory solves `θ' = p1 θ` in the strip. -/
theorem fst_solution (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Canonical.gaugeInterior (affineGauge H) (KAM.Weighted.Dom n {0} s (r-sigma))
      (1/2)) :
    KAM.ODE.IsSolutionIn p1 (KAM.complexStrip n (r-sigma)) (Icc (-1) 1)
      (fun t => (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).1) := by
  intro t ht
  obtain ⟨h1, h2⟩ := (KAM.Canonical.flow_a (smallField H) hz).2.1 t ht
  have hs := (mem_Dom_iff _).1 h1
  refine ⟨hs.1, ?_⟩
  have := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt t h2
  simpa [Function.comp_def, field_fst H (strip_sub_sigma_subset H hs.1)] using this

theorem contDiffOn_p1 (H : P11AffineHyp p0 p1 r s sigma A) :
    ContDiffOn ℝ 1 p1 (KAM.complexStrip n (r-sigma)) := by
  have hhol : DifferentiableOn ℂ p1 (KAM.complexStrip n (r-sigma)) :=
    H.hol1.mono (strip_sub_sigma_subset H)
  have := (KAM.holomorphic_regularity_of_finiteDimensional (KAM.isOpen_complexStrip n _)
    hhol).2.2.1
  exact (this.restrict_scalars ℝ).of_le (by simp)

/-- The angle component of the flow does not depend on the action. -/
theorem flow_fst_indep (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).1 =
      (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t (z.1, 0)).1 := by
  have hz0 : (z.1, (0 : P11CVec n)) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
    rw [mem_Dom_iff] at hz ⊢
    exact ⟨hz.1, by simpa using by linarith [H.s_pos]⟩
  have hu := KAM.ODE.gen_uniqueness (KAM.isOpen_complexStrip n _) (contDiffOn_p1 H)
    (isPreconnected_Icc.ordConnected) (t₀ := 0) (by simp : (0:ℝ) ∈ Icc (-1:ℝ) 1)
    (fst_solution H (U_sub_half H hz)) (fst_solution H (U_sub_half H hz0))
    (by
      have a := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz)).1
      have b := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz0)).1
      simp only [a, b])
  exact hu ht

/-- Affine combinations (with the same angle) of trajectories are trajectories. -/
theorem flow_affine_comb (H : P11AffineHyp p0 p1 r s sigma A) {θ η : P11CVec n}
    (hz : (θ, η) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t (θ, c • η) =
      ((KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
          (KAM.Weighted.Dom n {0} s (r-sigma)) t (θ, η)).1,
        (1-c) • (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
          (KAM.Weighted.Dom n {0} s (r-sigma)) t (θ, 0)).2 +
        c • (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
          (KAM.Weighted.Dom n {0} s (r-sigma)) t (θ, η)).2) := by
  set F := KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) with hF
  set Ω : Set (P11Phase n) := KAM.Weighted.Dom n {0} s (r-sigma) with hΩ
  set G := KAM.Canonical.flow F Ω with hG
  have hz' := (mem_Dom_iff _).1 hz
  have hz0 : ((θ, (0 : P11CVec n))) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
    rw [mem_Dom_iff]
    exact ⟨hz'.1, by simpa using by linarith [H.s_pos]⟩
  have hzc : ((θ, c • η)) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
    rw [mem_Dom_iff]
    refine ⟨hz'.1, ?_⟩
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have := hz'.2
    simp only at this
    nlinarith [norm_nonneg η]
  set δ : ℝ → P11Phase n := fun t => ((G t (θ, η)).1, (1-c) • (G t (θ, 0)).2 + c • (G t (θ, η)).2)
    with hδ
  have hsol : KAM.ODE.IsSolutionIn F Ω (Icc (-1) 1) δ := by
    intro t ht
    obtain ⟨h1, d1⟩ := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz)).2.1 t ht
    obtain ⟨h0, d0⟩ := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz0)).2.1 t ht
    have hθ : (G t (θ, 0)).1 = (G t (θ, η)).1 := (flow_fst_indep H hz ht).symm
    beta_reduce at h1 d1 h0 d0
    simp only [← hG, ← hF, ← hΩ] at h1 d1 h0 d0
    have m1 := (mem_Dom_iff _).1 h1
    have m0 := (mem_Dom_iff _).1 h0
    have hs1 := strip_sub_sigma_subset H m1.1
    have hmem : δ t ∈ Ω := by
      rw [hΩ, mem_Dom_iff]
      refine ⟨m1.1, ?_⟩
      show ‖(1-c) • (G t (θ, 0)).2 + c • (G t (θ, η)).2‖ < s
      calc ‖(1-c) • (G t (θ, 0)).2 + c • (G t (θ, η)).2‖
          ≤ ‖(1-c) • (G t (θ, 0)).2‖ + ‖c • (G t (θ, η)).2‖ := norm_add_le _ _
        _ = (1-c) * ‖(G t (θ, 0)).2‖ + c * ‖(G t (θ, η)).2‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0,
            abs_of_nonneg (sub_nonneg.2 hc1)]
        _ < s := by
          rcases le_total ‖(G t (θ, 0)).2‖ ‖(G t (θ, η)).2‖ with h | h <;>
            nlinarith [m1.2, m0.2, norm_nonneg (G t (θ, 0)).2, norm_nonneg (G t (θ, η)).2]
    refine ⟨hmem, ?_⟩
    have e1 : HasDerivAt (fun t => (G t (θ, η)).1) (F (G t (θ, η))).1 t :=
      by simpa [Function.comp_def] using
        (hasFDerivAt_fst (𝕜 := ℝ) (p := G t (θ, η))).comp_hasDerivAt t d1
    have e2 : HasDerivAt (fun t => (G t (θ, η)).2) (F (G t (θ, η))).2 t :=
      by simpa [Function.comp_def] using
        (hasFDerivAt_snd (𝕜 := ℝ) (p := G t (θ, η))).comp_hasDerivAt t d1
    have e3 : HasDerivAt (fun t => (G t (θ, 0)).2) (F (G t (θ, 0))).2 t :=
      by simpa [Function.comp_def] using
        (hasFDerivAt_snd (𝕜 := ℝ) (p := G t (θ, 0))).comp_hasDerivAt t d0
    have e4 := (e3.const_smul (1-c)).add (e2.const_smul c)
    have e5 := e1.prodMk e4
    refine e5.congr_deriv ?_
    have h0' : (G t (θ, 0)).1 ∈ KAM.complexStrip n r := strip_sub_sigma_subset H (by rw [hθ]; exact m1.1)
    refine Prod.ext ?_ ?_
    · show (F (G t (θ, η))).1 = (F (δ t)).1
      rw [field_fst H hs1, field_fst H (by simpa using hs1)]
    · funext i
      show (1-c) • (F (G t (θ, 0))).2 i + c • (F (G t (θ, η))).2 i = (F (δ t)).2 i
      rw [hF, field_snd H h0', field_snd H hs1, field_snd H (by simpa using hs1), hθ]
      simp only [Complex.real_smul, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      simp only [δ, Pi.add_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_sub,
        Complex.ofReal_one, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, mul_left_comm]
      ring
  have hδ0 : δ 0 = (θ, c • η) := by
    have a : G 0 (θ, η) = (θ, η) := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz)).1
    have b : G 0 (θ, 0) = (θ, 0) := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hz0)).1
    simp only [δ, a, b, smul_zero, zero_add]
  have hu := (KAM.Canonical.flow_a (smallField H) (U_sub_half H hzc)).2.2.1 (Icc (-1) 1)
    isPreconnected_Icc.ordConnected (by simp) δ hsol hδ0 t ⟨ht, ht⟩
  exact hu.symm

/-- The simple-form data of the time-one map. -/
def affTheta (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n) (r s sigma : ℝ)
    (θ : P11CVec n) : P11CVec n := (p11Flow (p11Affine p0 p1) r s sigma 1 (θ, 0)).1

def affV (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n) (r s sigma : ℝ)
    (θ : P11CVec n) : P11CVec n := (p11Flow (p11Affine p0 p1) r s sigma 1 (θ, 0)).2

def affM (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n) (r s sigma : ℝ)
    (θ : P11CVec n) : P11CVec n →L[ℂ] P11CVec n :=
  fderiv ℂ (fun η => (p11Flow (p11Affine p0 p1) r s sigma 1 (θ, η)).2) 0

theorem flow_differentiableAt (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    DifferentiableAt ℂ (p11Flow (p11Affine p0 p1) r s sigma t) z :=
  (((KAM.Canonical.flow_b (smallField H)).2.1 t ht).differentiableAt
    ((KAM.Canonical.isOpen_gaugeInterior (smallField H).isOpen _ _).mem_nhds (U_sub_half H hz)))

theorem flow_fst_eq (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) :
    (p11Flow (p11Affine p0 p1) r s sigma 1 z).1 = affTheta p0 p1 r s sigma z.1 :=
  flow_fst_indep H hz ⟨by norm_num, le_rfl⟩

theorem flow_snd_affine (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) :
    (p11Flow (p11Affine p0 p1) r s sigma 1 z).2 =
      affM p0 p1 r s sigma z.1 z.2 + affV p0 p1 r s sigma z.1 := by
  obtain ⟨θ, η⟩ := z
  simp only at hz ⊢
  set f : P11CVec n → P11CVec n := fun η' => (p11Flow (p11Affine p0 p1) r s sigma 1 (θ, η')).2
    with hf
  have hz0 : ((θ, (0 : P11CVec n))) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
    rw [mem_Dom_iff] at hz ⊢
    exact ⟨hz.1, by simpa using by linarith [H.s_pos]⟩
  have hdiff : DifferentiableAt ℂ f 0 := by
    have hGd := flow_differentiableAt H hz0 (t := 1) ⟨by norm_num, le_rfl⟩
    have hpair : DifferentiableAt ℂ (fun η' : P11CVec n => ((θ : P11CVec n), η')) 0 :=
      (differentiableAt_const _).prodMk differentiableAt_id
    exact differentiableAt_snd.comp (0 : P11CVec n) (hGd.comp (0 : P11CVec n) hpair)
  have hfd := hdiff.hasFDerivAt
  have hline : HasDerivAt (fun c : ℝ => c • η) η 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const η
  have hf' : HasFDerivAt f (fderiv ℂ f 0) ((fun c : ℝ => c • η) 0) := by simpa using hfd
  have hg : HasDerivAt (fun c : ℝ => f (c • η)) (fderiv ℂ f 0 η) 0 := by
    have := (hf'.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hline
    exact this
  have haff : ∀ c ∈ Icc (0 : ℝ) 1, f (c • η) = f 0 + c • (f η - f 0) := by
    intro c hc
    have := flow_affine_comb H hz hc.1 hc.2 (t := 1) ⟨by norm_num, le_rfl⟩
    have h2 := congrArg Prod.snd this
    simp only [hf, p11Flow]
    rw [h2]
    simp only [sub_smul, one_smul, smul_sub, smul_zero]
    module
  have hd2 : HasDerivWithinAt (fun c : ℝ => f (c • η)) (f η - f 0) (Icc 0 1) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).smul_const (f η - f 0)).const_add (f 0)).hasDerivWithinAt
      (s := Icc (0 : ℝ) 1)
    simp only [id, one_smul] at this
    exact this.congr haff (haff 0 ⟨le_rfl, zero_le_one⟩)
  have hM : fderiv ℂ f 0 η = f η - f 0 :=
    (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩).eq_deriv _ hg.hasDerivWithinAt hd2
  show f η = fderiv ℂ f 0 η + _
  rw [hM]
  simp [affV, hf]

theorem affTheta_differentiableAt (H : P11AffineHyp p0 p1 r s sigma A) {θ : P11CVec n}
    (hz : (θ, (0 : P11CVec n)) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) :
    DifferentiableAt ℂ (affTheta p0 p1 r s sigma) θ := by
  have hGd := flow_differentiableAt H hz (t := 1) ⟨by norm_num, le_rfl⟩
  have hpair : DifferentiableAt ℂ (fun θ' : P11CVec n => (θ', (0 : P11CVec n))) θ :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  exact differentiableAt_fst.comp θ (hGd.comp θ hpair)

theorem zero_mem_U (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) :
    (z.1, (0 : P11CVec n)) ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2) := by
  rw [mem_Dom_iff] at hz ⊢
  exact ⟨hz.1, by simpa using by linarith [H.s_pos]⟩

/-- The angle part of `DΦ` only sees the angle part of the increment. -/
theorem fderiv_flow_fst (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) (u : P11Phase n) :
    (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z u).1 =
      fderiv ℂ (affTheta p0 p1 r s sigma) z.1 u.1 := by
  have hGz := (flow_differentiableAt H hz (t := 1) ⟨by norm_num, le_rfl⟩).hasFDerivAt
  have hΘ := (affTheta_differentiableAt H (zero_mem_U H hz)).hasFDerivAt
  have h1 : HasFDerivAt (fun w => (p11Flow (p11Affine p0 p1) r s sigma 1 w).1)
      ((ContinuousLinearMap.fst ℂ _ _).comp (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z))
      z := hasFDerivAt_fst.comp z hGz
  have h2 : HasFDerivAt (fun w : P11Phase n => affTheta p0 p1 r s sigma w.1)
      ((fderiv ℂ (affTheta p0 p1 r s sigma) z.1).comp (ContinuousLinearMap.fst ℂ _ _)) z :=
    hΘ.comp z hasFDerivAt_fst
  have heq : (fun w : P11Phase n => affTheta p0 p1 r s sigma w.1) =ᶠ[nhds z]
      (fun w => (p11Flow (p11Affine p0 p1) r s sigma 1 w).1) := by
    filter_upwards [(KAM.Weighted.isOpen_Dom (n := n) (m := n) {0} (3*s/4) (r-3*sigma/2)).mem_nhds
      hz] with w hw
    exact (flow_fst_eq H hw).symm
  have h3 := h2.congr_of_eventuallyEq heq.symm
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this

/-- `DΦ(0, b) = (0, M b)`. -/
theorem fderiv_flow_eta (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) (b : P11CVec n) :
    fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z (0, b) = (0, affM p0 p1 r s sigma z.1 b) := by
  have hGz := (flow_differentiableAt H hz (t := 1) ⟨by norm_num, le_rfl⟩).hasFDerivAt
  have h1 := fderiv_flow_fst H hz (0, b)
  simp only [map_zero] at h1
  refine Prod.ext h1 ?_
  have hℓ : HasDerivAt (fun t : ℂ => z + t • ((0 : P11CVec n), b)) ((0 : P11CVec n), b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const ((0 : P11CVec n), b)).const_add z
  have hG' : HasFDerivAt (p11Flow (p11Affine p0 p1) r s sigma 1)
      (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z)
      (z + (0 : ℂ) • ((0 : P11CVec n), b)) := by simpa using hGz
  have hcomp := hG'.comp_hasDerivAt (0 : ℂ) hℓ
  have hl2 : HasDerivAt (fun t : ℂ => z.2 + t • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const b).const_add z.2
  have hM : HasDerivAt (fun t : ℂ => affM p0 p1 r s sigma z.1 (z.2 + t • b) +
      affV p0 p1 r s sigma z.1) (affM p0 p1 r s sigma z.1 b) 0 := by
    have := ((affM p0 p1 r s sigma z.1).hasFDerivAt (x := z.2 + (0 : ℂ) • b)).comp_hasDerivAt
      (0 : ℂ) hl2
    exact this.add_const _
  have hk := (hasDerivAt_const (0 : ℂ) (affTheta p0 p1 r s sigma z.1)).prodMk hM
  have hev : (fun t : ℂ => (affTheta p0 p1 r s sigma z.1, affM p0 p1 r s sigma z.1 (z.2 + t • b) +
      affV p0 p1 r s sigma z.1)) =ᶠ[nhds 0]
      ((p11Flow (p11Affine p0 p1) r s sigma 1) ∘ fun t : ℂ => z + t • ((0 : P11CVec n), b)) := by
    have hcont : ContinuousAt (fun t : ℂ => z + t • ((0 : P11CVec n), b)) 0 := hℓ.continuousAt
    filter_upwards [hcont.eventually_mem
      ((KAM.Weighted.isOpen_Dom (n := n) (m := n) {0} (3*s/4) (r-3*sigma/2)).mem_nhds
        (by simpa using hz))] with t ht
    refine Prod.ext ?_ ?_
    · have := flow_fst_eq H ht
      simpa using this.symm
    · have := flow_snd_affine H ht
      simpa using this.symm
  have := hcomp.unique (hk.congr_of_eventuallyEq hev.symm)
  exact (congrArg Prod.snd this)

/-- `Dθ^T`-type duality: `(DΘ a) · (M b) = a · b`. -/
theorem aff_duality (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) (a b : P11CVec n) :
    (∑ i, (fderiv ℂ (affTheta p0 p1 r s sigma) z.1 a) i * (affM p0 p1 r s sigma z.1 b) i) =
      ∑ i, a i * b i := by
  have hφ : DifferentiableOn ℂ (p11Affine p0 p1) (KAM.Weighted.Dom n {0} s (r-sigma)) :=
    (differentiableOn_p11Affine H).mono (by
      intro w hw
      rw [mem_Dom_iff] at hw
      exact ⟨strip_sub_sigma_subset H hw.1, trivial⟩)
  have hs := KAM.Canonical.flow_symplFormC hφ (smallField H) (U_sub_half H hz)
    (t := 1) ⟨by norm_num, le_rfl⟩ (a, 0) (0, b)
  have e1 := fderiv_flow_fst H hz (a, 0)
  have e2 := fderiv_flow_eta H hz b
  change KAM.Canonical.symplFormC (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z (a, 0))
    (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z (0, b)) = _ at hs
  rw [e2] at hs
  simp only [KAM.Canonical.symplFormC, e1, mul_zero, zero_sub, Pi.zero_apply, Finset.sum_neg_distrib,
    zero_mul, neg_inj] at hs
  simpa [mul_comm] using hs

end KAM.Planetary

end
