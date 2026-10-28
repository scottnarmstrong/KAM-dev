/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
public import KAM.Nekhoroshev.Partial.Domain
import KAM.Strip.Bridges
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Part 11 (N11-E3): the real/complex Hessian bridge and the signed Hessian bounds

`realPart_hessian_apply` identifies the real Hessian of `realPart h` at a real point with the
real part of the complex Hessian of a holomorphic `h`; `FastConvex.toRealFastConvex` restricts the
complex upper Hessian bound to the real slice; `hessian_at_sign` and `hessian` give the signed
convexity data of `signedH`-type Hamiltonians `σ h / (2π)` (stated for the scaled function
`σ h/(2π)` (`signedH`) at the selected source sign).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`, lemma `bpN:p11:hessian`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open KAM.Weighted
open scoped Topology

namespace KAM.Nekhoroshev

variable {n k : ℕ}

private theorem hessHelper_real_fderiv {F : (Fin n → ℂ) → ℂ} {J : Fin n → ℝ}
    (hF : DifferentiableAt ℂ F (KAM.realInclusion n J)) (v : Fin n → ℝ) :
    fderiv ℝ (fun I : Fin n → ℝ => (F (KAM.realInclusion n I)).re) J v =
      (fderiv ℂ F (KAM.realInclusion n J) (KAM.realInclusion n v)).re := by
  have h2 : HasFDerivAt (fun y => F (KAM.realInclusion n y))
      (((fderiv ℂ F (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n)) J :=
    (hF.hasFDerivAt.restrictScalars ℝ).comp J (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (F (KAM.realInclusion n y)).re)
      (Complex.reCLM.comp
        (((fderiv ℂ F (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n))) J :=
    Complex.reCLM.hasFDerivAt.comp J h2
  rw [h3.fderiv]
  rfl

private theorem hessHelper_contDiffAt {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {F : (Fin n → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F Ω) {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ Ω) :
    ContDiffAt ℝ 2 (fun J : Fin n → ℝ => (F (KAM.realInclusion n J)).re) I := by
  have h1 : ContDiffAt ℂ 2 F (KAM.realInclusion n I) :=
    ((KAM.holomorphic_regularity_of_finiteDimensional hΩ hF).2.2.1.contDiffAt
      (hΩ.mem_nhds hI)).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 F (KAM.realInclusion n I) := h1.restrict_scalars ℝ
  have h3 := h2.comp I (KAM.realInclusion n).contDiff.contDiffAt
  exact Complex.reCLM.contDiff.contDiffAt.comp I h3

/-- For `h` holomorphic on an open set containing the real point `I`, the real Hessian of
`realPart h` is the real part of the complex Hessian on real vectors. -/
theorem realPart_hessian_apply {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h Ω) {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ Ω)
    (u v : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (realPart h)) I u v =
      (fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (KAM.realInclusion n u)
        (KAM.realInclusion n v)).re := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hΩ hh
  have hcd : ContDiffAt ℝ 2 (realPart h) I := hessHelper_contDiffAt hΩ hh hI
  have hdd : DifferentiableAt ℝ (fderiv ℝ (realPart h)) I :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : (fun J => fderiv ℝ (realPart h) J v) =ᶠ[𝓝 I]
      fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n v)).re := by
    have hopen : ∀ᶠ J in 𝓝 I, KAM.realInclusion n J ∈ Ω :=
      (KAM.realInclusion n).continuous.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hI)
    filter_upwards [hopen] with J hJ
    exact hessHelper_real_fderiv (hh.differentiableAt (hΩ.mem_nhds hJ)) v
  have hdh : DifferentiableAt ℂ (fderiv ℂ h) (KAM.realInclusion n I) :=
    (hreg.1).differentiableAt (hΩ.mem_nhds hI)
  have hd1 : HasFDerivAt (fun J => fderiv ℝ (realPart h) J v)
      ((fderiv ℝ (fderiv ℝ (realPart h)) I).flip v) I := by
    have := hdd.hasFDerivAt.clm_apply (hasFDerivAt_const v I)
    simpa using this
  have hF' : DifferentiableAt ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n v))
      (KAM.realInclusion n I) :=
    hdh.clm_apply (differentiableAt_const _)
  have h2 := hessHelper_real_fderiv hF' u
  have h3 : fderiv ℝ (fun J => fderiv ℝ (realPart h) J v) I u =
      fderiv ℝ (fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n v)).re) I u := by
    rw [hev.fderiv_eq]
  have h4 : fderiv ℝ (fun J => fderiv ℝ (realPart h) J v) I u =
      fderiv ℝ (fderiv ℝ (realPart h)) I u v := by
    rw [hd1.fderiv]; rfl
  have h5 : fderiv ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n v)) (KAM.realInclusion n I)
      (KAM.realInclusion n u) =
      fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (KAM.realInclusion n u)
        (KAM.realInclusion n v) := by
    have := hdh.hasFDerivAt.clm_apply (hasFDerivAt_const (KAM.realInclusion n v)
      (KAM.realInclusion n I))
    rw [this.fderiv]
    simp
  rw [← h4, h3]
  exact h2.trans (by rw [h5])

private theorem hessHelper_sq_euclid {𝕜 : Type*} [RCLike 𝕜] (x : Fin n → 𝕜) :
    euclid x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem hessHelper_euclid_mono {𝕜 𝕝 : Type*} [RCLike 𝕜] [RCLike 𝕝] {x : Fin n → 𝕜}
    {y : Fin n → 𝕝} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : euclid x ≤ euclid y :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => by gcongr; exact h i)

private theorem hessHelper_euclid_real (v : Fin n → ℝ) :
    euclid (KAM.realInclusion n v) = euclid v := by
  simp [euclid, Complex.norm_real]

private theorem hessHelper_euclid_mul (c : ℂ) (x : Fin n → ℂ) :
    euclid (fun i => c * x i) = ‖c‖ * euclid x := by
  unfold euclid
  have : ∀ i, ‖c * x i‖ ^ 2 = ‖c‖ ^ 2 * ‖x i‖ ^ 2 := fun i => by rw [norm_mul]; ring
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private theorem hessHelper_single_norm (i : Fin n) : ‖(Pi.single i (1:ℂ) : Fin n → ℂ)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- The `2→2` bound of a symmetric-type bilinear form controls its Euclidean column norm. -/
private theorem hessHelper_hess_bound (Q : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) {M : ℝ}
    (hQ : ‖Q‖ ≤ M) (v : Fin n → ℂ) :
    euclid (fun i => Q (Pi.single i 1) v) ≤ M * euclid v := by
  set w : Fin n → ℂ := fun i => Q (Pi.single i 1) v with hw
  set S := euclid w with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hM : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg Q).trans hQ
  set u : Fin n → ℂ := fun i => starRingEnd ℂ (w i) with hu
  have hexp : Q u v = ∑ i, u i * w i := by
    have : u = ∑ i, u i • (Pi.single i (1:ℂ) : Fin n → ℂ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [hw, map_sum]
  have hsum : Q u v = (S ^ 2 : ℝ) := by
    rw [hexp, hessHelper_sq_euclid]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hu, Complex.conj_mul']
  have hu_le : ‖u‖ ≤ S := by
    refine (norm_le_euclid u).1.trans (hessHelper_euclid_mono fun i => ?_)
    simp [hu]
  have hv_le : ‖v‖ ≤ euclid v := (norm_le_euclid v).1
  have hbound : S ^ 2 ≤ M * euclid v * S := by
    have h1 : ‖Q u v‖ ≤ ‖Q‖ * ‖u‖ * ‖v‖ := Q.le_opNorm₂ u v
    rw [hsum, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h1
    calc S ^ 2 ≤ ‖Q‖ * ‖u‖ * ‖v‖ := h1
      _ ≤ M * S * euclid v := by gcongr
      _ = M * euclid v * S := by ring
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hM (Real.sqrt_nonneg _)
  · nlinarith

/-- Restrict the complex Hessian bound to the real slice; no extra source premise. -/
theorem FastConvex.toRealFastConvex {Ic : Fin n → ℝ} {R m M : ℝ}
    {h : (Fin n → ℂ) → ℂ} (hh : FastConvex Ic R m M h) :
    RealFastConvex Ic R m M h := by
  refine ⟨hh.m_pos, hh.m_le, hh.hol, hh.real, hh.convex, ?_⟩
  intro I hI v
  have hmem : KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R :=
    ⟨KAM.realInclusion n Ic, rfl, by
      rw [← map_sub, KAM.norm_realInclusion]; exact hI⟩
  have hbr := realPart_hessian_apply (isOpen_polyNbhd _ R) hh.hol hmem
  have hes : ∀ i, (fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1)) v =
      (fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (Pi.single i 1)
        (KAM.realInclusion n v)).re := fun i => by
    have e : KAM.realInclusion n (Pi.single i (1:ℝ)) = Pi.single i (1:ℂ) := by
      funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hbr, e]
  have key := hh.hessian (KAM.realInclusion n I) hmem (KAM.realInclusion n v)
  calc euclid (fun i => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) v)
      ≤ euclid (fun i => fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (Pi.single i 1)
          (KAM.realInclusion n v)) := by
        refine hessHelper_euclid_mono fun i => ?_
        rw [hes i, Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
    _ ≤ M * euclid (KAM.realInclusion n v) := key
    _ = M * euclid v := by rw [hessHelper_euclid_real]

private theorem signedH_eq_smul (a : PartialData n k) (σ : ℝ) :
    signedH a σ = (((σ:ℂ) / (2*(Real.pi:ℂ))) • a.h) := by
  funext I
  simp only [signedH, Pi.smul_apply, smul_eq_mul]
  ring

private theorem realPart_signedH (a : PartialData n k) (σ : ℝ) :
    realPart (signedH a σ) = (σ/(2*Real.pi)) • realPart a.h := by
  funext I
  have : signedH a σ (fun i => (I i : ℂ)) =
      ((σ/(2*Real.pi):ℝ):ℂ) * a.h (fun i => (I i : ℂ)) := by
    simp only [signedH]; push_cast; ring
  simp only [realPart, this, Complex.re_ofReal_mul, Pi.smul_apply, smul_eq_mul]

private theorem hessian_signed (a : PartialData n k) (σ : ℝ) (I v : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (realPart (signedH a σ))) I v v =
      (σ/(2*Real.pi)) * fderiv ℝ (fderiv ℝ (realPart a.h)) I v v := by
  rw [realPart_signedH, fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (σ/(2*Real.pi))
    (f := realPart a.h), fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (σ/(2*Real.pi))
    (f := fderiv ℝ (realPart a.h))]
  rfl

private theorem frequencyMap_signed (a : PartialData n k) (σ : ℝ) (I : Fin n → ℝ) :
    KAM.frequencyMap (signedH a σ) I = (σ/(2*Real.pi)) • KAM.frequencyMap a.h I := by
  funext i
  have e : (fun J : Fin n → ℝ => (signedH a σ (fun j => (J j : ℂ))).re) =
      realPart (signedH a σ) := rfl
  have e2 : (fun J : Fin n → ℝ => (a.h (fun j => (J j : ℂ))).re) = realPart a.h := rfl
  simp only [KAM.frequencyMap, e, e2, realPart_signedH, fderiv_const_smul_field,
    Pi.smul_apply]
  rfl

private theorem r0_le_half (a : PartialData n k) : (constants a).r0 ≤ a.ρ / 2 :=
  min_le_left _ _

private theorem realBall_mem {Ic : Fin n → ℝ} {R : ℝ} {I : Fin n → ℝ}
    (hI : ‖I - Ic‖ < R) :
    KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R :=
  ⟨KAM.realInclusion n Ic, rfl, by rw [← map_sub, KAM.norm_realInclusion]; exact hI⟩

private theorem pos_of_definite (a : PartialData n k) : 0 < a.m := by
  obtain ⟨_, hm, _⟩ := a.definite
  exact hm

/-- Every real point of a block ball (radius ≤ `r0`) lies in the real slice of `G'_ρ`. -/
private theorem realBall_actionNbhd (a : PartialData n k) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G)
    {R : ℝ} (hRR : R ≤ (constants a).r0) {I : Fin n → ℝ} (hI : ‖I - Ic‖ < R) :
    KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ :=
  polyNbhd_realBall_subset a hIc ((hRR.trans (r0_le_half a)).trans (by linarith [a.hρ]))
    (realBall_mem hI)

/-- The selected frozen definiteness witness is retained for assembly. -/
theorem hessian_at_sign (a : PartialData n k) (hne : a.G.Nonempty) {σ : ℝ}
    (hσ : DefiniteSign a σ) :
    a.m ≤ a.Mc ∧ ∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
      FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ) := by
  have hm := pos_of_definite a
  have hπ := Real.pi_pos
  have hρ := a.hρ
  have hOpen : IsOpen (KAM.actionNbhd a.G' a.ρ) := by
    rw [actionNbhd_eq_polyNbhd]; exact isOpen_polyNbhd _ _
  have hmM : a.m ≤ a.Mc := by
    obtain ⟨Ic, hIc⟩ := hne
    have hn : 0 < n := by have := a.hn; omega
    have hI : KAM.realInclusion n Ic ∈ KAM.actionNbhd a.G' a.ρ :=
      ⟨Ic, a.collar Ic hIc (mem_closedBall_self hρ.le), by
        rw [show KAM.realInclusion n Ic = fun i => (Ic i:ℂ) from rfl, sub_self, norm_zero]
        exact hρ⟩
    set i0 : Fin n := ⟨0, hn⟩
    set v : Fin n → ℝ := Pi.single i0 1
    have h1 := (hσ.2 Ic hI).2 v
    have hsum : ∑ i, (v i)^2 = 1 := by simp [v, Pi.single_apply]
    rw [hsum] at h1
    have hQ := realPart_hessian_apply hOpen a.hol hI v v
    have hbd : |fderiv ℝ (fderiv ℝ (realPart a.h)) Ic v v| ≤ a.Mc := by
      rw [hQ, ← Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      have := (fderiv ℂ (fderiv ℂ a.h) (KAM.realInclusion n Ic)).le_opNorm₂
        (KAM.realInclusion n v) (KAM.realInclusion n v)
      refine this.trans ?_
      have hv : ‖KAM.realInclusion n v‖ ≤ 1 := by
        rw [KAM.norm_realInclusion]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
          by_cases hj : j = i0
          · subst hj; simp [v]
          · simp [v, hj]
      calc ‖fderiv ℂ (fderiv ℂ a.h) (KAM.realInclusion n Ic)‖ *
            ‖KAM.realInclusion n v‖ * ‖KAM.realInclusion n v‖
          ≤ a.Mc * 1 * 1 := by
            have hM0 : 0 ≤ a.Mc := le_trans (ContinuousLinearMap.opNorm_nonneg _) (a.Hess _ hI)
            have h1 := a.Hess _ hI
            gcongr
        _ = a.Mc := by ring
    rcases hσ.1 with rfl | rfl
    · linarith [(abs_le.1 hbd).2]
    · linarith [(abs_le.1 hbd).1]
  refine ⟨hmM, fun Ic hIc R hR hRR => ?_⟩
  have hRρ : R ≤ a.ρ := (hRR.trans (r0_le_half a)).trans (by linarith)
  have hsub := polyNbhd_realBall_subset a hIc hRρ
  have hπ' : (0:ℝ) < 2*Real.pi := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PartialConstants.m1, constants]; positivity
  · simp only [PartialConstants.m1, PartialConstants.M1, constants]
    exact div_le_div_of_nonneg_right hmM hπ'.le
  · rw [signedH_eq_smul]
    exact (a.hol.mono hsub).const_smul _
  · intro I hI
    have hx : signedH a σ (KAM.realInclusion n I) =
        ((σ/(2*Real.pi):ℝ):ℂ) * a.h (KAM.realInclusion n I) := by
      simp only [signedH]; push_cast; ring
    rw [hx, Complex.im_ofReal_mul, a.real I (hsub hI), mul_zero]
  · intro I hI v
    have h1 := (hσ.2 I (realBall_actionNbhd a hIc hRR hI)).2 v
    have hS : euclid v ^ 2 = ∑ i, (v i)^2 := by
      rw [hessHelper_sq_euclid]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    rw [hessian_signed, hS]
    simp only [PartialConstants.m1, constants]
    have h2 := div_le_div_of_nonneg_right h1 hπ'.le
    have e1 : a.m / (2*Real.pi) * ∑ i, (v i)^2 = (a.m * ∑ i, (v i)^2) / (2*Real.pi) := by ring
    have e2 : σ / (2*Real.pi) * fderiv ℝ (fderiv ℝ (realPart a.h)) I v v =
        (σ * fderiv ℝ (fderiv ℝ (realPart a.h)) I v v) / (2*Real.pi) := by ring
    rw [e1, e2]; exact h2
  · intro I hI v
    have hIa := hsub hI
    have hd2 : fderiv ℂ (fderiv ℂ (signedH a σ)) I =
        (((σ:ℂ) / (2*(Real.pi:ℂ))) • fderiv ℂ (fderiv ℂ a.h)) I := by
      rw [signedH_eq_smul, fderiv_const_smul_field (𝕜 := ℂ) (R := ℂ) (((σ:ℂ) / (2*(Real.pi:ℂ))))
        (f := a.h), fderiv_const_smul_field (𝕜 := ℂ) (R := ℂ) (((σ:ℂ) / (2*(Real.pi:ℂ))))
        (f := fderiv ℂ a.h)]
    have hnorm : ‖((σ:ℂ) / (2*(Real.pi:ℂ)))‖ = 1 / (2*Real.pi) := by
      have h2 : ‖(2*(Real.pi:ℂ))‖ = 2*Real.pi := by
        simp
      rw [norm_div, h2, Complex.norm_real, Real.norm_eq_abs]
      rcases hσ.1 with rfl | rfl <;> simp
    have hcol : ∀ i, fderiv ℂ (fderiv ℂ (signedH a σ)) I (Pi.single i 1) v =
        ((σ:ℂ) / (2*(Real.pi:ℂ))) * fderiv ℂ (fderiv ℂ a.h) I (Pi.single i 1) v := fun i => by
      rw [hd2]; rfl
    have hb := hessHelper_hess_bound (fderiv ℂ (fderiv ℂ a.h) I) (M := a.Mc) (a.Hess I hIa) v
    simp only [hcol]
    rw [hessHelper_euclid_mul, hnorm]
    simp only [PartialConstants.M1, constants]
    calc 1 / (2*Real.pi) * euclid (fun i => fderiv ℂ (fderiv ℂ a.h) I (Pi.single i 1) v)
        ≤ 1 / (2*Real.pi) * (a.Mc * euclid v) := by gcongr
      _ = a.Mc / (2*Real.pi) * euclid v := by ring

theorem hessian (a : PartialData n k) (hne : a.G.Nonempty) :
    a.m ≤ a.Mc ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
        FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ)) ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
        (constants a).g1 ≤ ‖KAM.frequencyMap (signedH a σ) I‖) := by
  obtain ⟨_, _, _, σ, hσ, hdef⟩ := a.definite
  have hDS : DefiniteSign a σ := ⟨hσ, hdef⟩
  obtain ⟨hmM, hfc⟩ := hessian_at_sign a hne hDS
  refine ⟨hmM, σ, hσ, hfc, fun I hI => ?_⟩
  have hπ' : (0:ℝ) < 2*Real.pi := by positivity
  rw [frequencyMap_signed, norm_smul, Real.norm_eq_abs]
  have hab : |σ / (2*Real.pi)| = 1 / (2*Real.pi) := by
    rw [abs_div, abs_of_pos hπ']
    rcases hσ with rfl | rfl <;> simp
  rw [hab]
  have := (hDS.2 I hI).1
  simp only [PartialConstants.g1, constants]
  calc a.g / (2*Real.pi) = 1 / (2*Real.pi) * a.g := by ring
    _ ≤ 1 / (2*Real.pi) * ‖KAM.frequencyMap a.h I‖ := by gcongr

end KAM.Nekhoroshev

end
