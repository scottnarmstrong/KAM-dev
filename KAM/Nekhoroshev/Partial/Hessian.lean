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
    · simp [Pi.single_apply, h]

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
    simp only [hu, Complex.conj_mul', Complex.ofReal_pow]
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
      · simp [Pi.single_apply, hj]
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

end KAM.Nekhoroshev

end
