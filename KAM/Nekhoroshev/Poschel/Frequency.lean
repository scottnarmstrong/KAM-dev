/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Poschel.Setting
public import KAM.Nekhoroshev.Poschel.Elementary
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Strip.Bridges
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Nekhoroshev.Defs.RealPart

/-!
# Local regularity and exact frequency maxima (`bpN:p9:omega0`, `bpN:p9:m-le-M`)

Local real regularity of `realPart h` and `frequencyMap h` on `U_{r0} P` (independent of any
global action ball), the off-graph lemma `m_le_M`, and the guarded frequency balls
`FrequencyBall` with the exact attained maximum `FrequencyBall.maximum`, `frequency_maximum`,
`omega0_radius`, `omega0Ball` and `omega0`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

section Core

variable {P : Set (Fin n → ℝ)} {r0 s : ℝ} {h : (Fin n → ℂ) → ℂ}

private theorem realInclusion_mem_polyNbhd'' {I : Fin n → ℝ} (hI : I ∈ realNbhd P r0) :
    KAM.realInclusion n I ∈ polyNbhd (cpx P) r0 := by
  obtain ⟨J', hJ', hlt⟩ := hI
  exact ⟨KAM.realInclusion n J', ⟨J', hJ', rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩

private theorem im_eq_zero_of_realOn (hs : 0 < s)
    (hreal : RealOn (Dom n (cpx P) r0 s) (fun w => h w.2)) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd P r0) : (h (KAM.realInclusion n I)).im = 0 := by
  have hmem : KAM.realInclusion₂ n ((0 : Fin n → ℝ), I) ∈ Dom n (cpx P) r0 s :=
    (realInclusion₂_mem_Dom_iff P hs _).2 ⟨mem_univ _, hI⟩
  simpa using hreal _ hmem

private theorem euclid_ofReal (x : Fin n → ℝ) : euclid (fun i => (x i : ℂ)) = euclid x := by
  simp [euclid]

private theorem euclid_sq_real (x : Fin n → ℝ) : euclid x ^ 2 = ∑ i, x i ^ 2 := by
  unfold euclid
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

private theorem contDiffOn_realPart (hD : DifferentiableOn ℂ h (polyNbhd (cpx P) r0)) :
    ContDiffOn ℝ 2 (realPart h) (realNbhd P r0) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_polyNbhd (cpx P) r0) hD
  have h1 : ContDiffOn ℝ ∞ h (polyNbhd (cpx P) r0) := hreg.2.2.1.restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun I : Fin n → ℝ => h (KAM.realInclusion n I)) (realNbhd P r0) :=
    h1.comp (KAM.realInclusion n).contDiff.contDiffOn fun _ hI => realInclusion_mem_polyNbhd'' hI
  exact (Complex.reCLM.contDiff.comp_contDiffOn h2).of_le
    ((by norm_num : (2 : WithTop ℕ∞) ≤ 2).trans (WithTop.coe_le_coe.2 le_top))

/-- `Re g` of a function holomorphic on `V_{r0} P` and real on the real points of `U_{r0} P` is
differentiable at those points, with `D (Re g) e = D g (ι e)`. -/
private theorem real_fderiv {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (polyNbhd (cpx P) r0))
    (hreal : ∀ I ∈ realNbhd P r0, (g (KAM.realInclusion n I)).im = 0) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd P r0) :
    DifferentiableAt ℝ (realPart g) I ∧ ∀ e : Fin n → ℝ,
      ((fderiv ℝ (realPart g) I e : ℝ) : ℂ) =
        fderiv ℂ g (KAM.realInclusion n I) (KAM.realInclusion n e) := by
  have hU := isOpen_polyNbhd (cpx P) r0
  have hgd : DifferentiableAt ℂ g (KAM.realInclusion n I) :=
    hg.differentiableAt (hU.mem_nhds (realInclusion_mem_polyNbhd'' hI))
  have h2 : HasFDerivAt (fun y => g (KAM.realInclusion n y))
      (((fderiv ℂ g (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n)) I :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp I (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt (realPart g) (Complex.reCLM.comp
      (((fderiv ℂ g (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n))) I :=
    Complex.reCLM.hasFDerivAt.comp I h2
  refine ⟨h3.differentiableAt, fun e => ?_⟩
  have hev : (fun y => g (KAM.realInclusion n y)) =ᶠ[𝓝 I] fun y => ((realPart g y : ℝ) : ℂ) := by
    filter_upwards [(isOpen_realNbhd P r0).mem_nhds hI] with y hy
    exact Complex.ext (by rw [Complex.ofReal_re]; rfl)
      ((hreal y hy).trans (Complex.ofReal_im _).symm)
  have h5 : HasFDerivAt (fun y => ((realPart g y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (realPart g) I)) I :=
    Complex.ofRealCLM.hasFDerivAt.comp I h3.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  simpa using (congrArg (fun L => L e) h6).symm

/-- The frequency map is real on `U_{r0} P`: its entries are the complex first derivatives. -/
private theorem freq_eq (hD : DifferentiableOn ℂ h (polyNbhd (cpx P) r0))
    (hreal : ∀ I ∈ realNbhd P r0, (h (KAM.realInclusion n I)).im = 0) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd P r0) (i : Fin n) :
    ((KAM.frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (KAM.realInclusion n I) (Pi.single i 1) := by
  have h1 := (real_fderiv hD hreal hI).2 (Pi.single i 1)
  rw [KAM.realInclusion_single] at h1
  exact h1

/-- The derivative of the frequency map on `U_{r0} P`, with complex and real Hessian formulas. -/
private theorem freq_deriv (hD : DifferentiableOn ℂ h (polyNbhd (cpx P) r0))
    (hreal : ∀ I ∈ realNbhd P r0, (h (KAM.realInclusion n I)).im = 0) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd P r0) :
    ∃ L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasFDerivAt (KAM.frequencyMap h) L I ∧
      (∀ v i, ((L v i : ℝ) : ℂ) = fderiv ℂ (fun J => fderiv ℂ h J (KAM.realInclusion n v))
        (KAM.realInclusion n I) (Pi.single i 1)) ∧
      (∀ v i, L v i = fderiv ℝ (fderiv ℝ (realPart h)) I v (Pi.single i 1)) := by
  have hU := isOpen_polyNbhd (cpx P) r0
  have hdf : DifferentiableOn ℂ (fderiv ℂ h) (polyNbhd (cpx P) r0) :=
    (KAM.holomorphic_regularity hU hD).1
  have hg : ∀ i : Fin n, DifferentiableOn ℂ (fun x => fderiv ℂ h x (Pi.single i 1))
      (polyNbhd (cpx P) r0) := fun i => hdf.clm_apply (differentiableOn_const _)
  have hgreal : ∀ i : Fin n, ∀ J ∈ realNbhd P r0,
      ((fun x => fderiv ℂ h x (Pi.single i 1)) (KAM.realInclusion n J)).im = 0 := by
    intro i J hJ
    show (fderiv ℂ h (KAM.realInclusion n J) (Pi.single i 1)).im = 0
    rw [← freq_eq hD hreal hJ i]
    exact Complex.ofReal_im _
  have hdiff : ∀ i : Fin n, DifferentiableAt ℝ
      (realPart (fun x => fderiv ℂ h x (Pi.single i 1))) I := fun i =>
    (real_fderiv (hg i) (hgreal i) hI).1
  have hev : ∀ i : Fin n, (fun J => KAM.frequencyMap h J i) =ᶠ[𝓝 I]
      realPart (fun x => fderiv ℂ h x (Pi.single i 1)) := by
    intro i
    filter_upwards [(isOpen_realNbhd P r0).mem_nhds hI] with J hJ
    have := freq_eq hD hreal hJ i
    show KAM.frequencyMap h J i = (fderiv ℂ h (KAM.realInclusion n J) (Pi.single i 1)).re
    rw [← this, Complex.ofReal_re]
  have hcomp : ∀ i : Fin n, HasFDerivAt (fun J => KAM.frequencyMap h J i)
      (fderiv ℝ (realPart (fun x => fderiv ℂ h x (Pi.single i 1))) I) I := fun i =>
    ((hdiff i).hasFDerivAt).congr_of_eventuallyEq (hev i)
  have hR2 : DifferentiableAt ℝ (fderiv ℝ (realPart h)) I := by
    have hc := contDiffOn_realPart hD
    have hca : ContDiffAt ℝ 2 (realPart h) I := hc.contDiffAt ((isOpen_realNbhd P r0).mem_nhds hI)
    exact (hca.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨ContinuousLinearMap.pi fun i =>
    fderiv ℝ (realPart (fun x => fderiv ℂ h x (Pi.single i 1))) I, hasFDerivAt_pi.2 hcomp,
    fun v i => ?_, fun v i => ?_⟩
  · have h1 := (real_fderiv (hg i) (hgreal i) hI).2 v
    have h2 := fderiv_apply_comm_of_differentiableOn hU hD (realInclusion_mem_polyNbhd'' hI)
      (KAM.realInclusion n v) (Pi.single i 1)
    simp only [ContinuousLinearMap.pi_apply]
    rw [h1, h2]
  · have h1 := (hcomp i).fderiv
    have h2 : fderiv ℝ (fun J => KAM.frequencyMap h J i) I v =
        fderiv ℝ (fderiv ℝ (realPart h)) I v (Pi.single i 1) := by
      have : (fun J => KAM.frequencyMap h J i) = fun J => fderiv ℝ (realPart h) J (Pi.single i 1) :=
        rfl
      rw [this, fderiv_clm_apply hR2 (differentiableAt_const _)]
      simp
    simp only [ContinuousLinearMap.pi_apply]
    rw [h1] at h2
    exact h2

/-- Euclidean bound for the derivative of the frequency map from the complex Hessian bound. -/
private theorem freq_bound {M : ℝ}
    (hess : ∀ I ∈ polyNbhd (cpx P) r0, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v)
    {I : Fin n → ℝ} (hI : I ∈ realNbhd P r0) (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hL : ∀ v i, ((L v i : ℝ) : ℂ) = fderiv ℂ (fun J => fderiv ℂ h J (KAM.realInclusion n v))
        (KAM.realInclusion n I) (Pi.single i 1)) (v : Fin n → ℝ) :
    euclid (L v) ≤ M * euclid v := by
  have h1 := hess _ (realInclusion_mem_polyNbhd'' hI) (KAM.realInclusion n v)
  have h2 : (fun i => fderiv ℂ (fun J => fderiv ℂ h J (KAM.realInclusion n v))
      (KAM.realInclusion n I) (Pi.single i 1)) = fun i => ((L v i : ℝ) : ℂ) :=
    funext fun i => (hL v i).symm
  rw [h2, euclid_ofReal] at h1
  have h3 : euclid (KAM.realInclusion n v) = euclid v := euclid_ofReal v
  rwa [h3] at h1

/-- The real Hessian quadratic form is `v ⬝ᵥ L v`. -/
private theorem hessR_eq_dot {I : Fin n → ℝ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hL : ∀ v i, L v i = fderiv ℝ (fderiv ℝ (realPart h)) I v (Pi.single i 1)) (v : Fin n → ℝ) :
    hessR (realPart h) I v v = v ⬝ᵥ L v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : hessR (realPart h) I v v =
      fderiv ℝ (fderiv ℝ (realPart h)) I v (∑ i, v i • (Pi.single i 1 : Fin n → ℝ)) :=
    congrArg (fderiv ℝ (fderiv ℝ (realPart h)) I v) hv
  rw [h1, map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hL]

end Core

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- Automatic m ≤ M: assumes neither m ≤ M nor positivity of m or M; ell may be zero. -/
theorem m_le_M (hn : 2 ≤ n) (hP : P.Nonempty) (hr : 0 < r0) (hs : 0 < s)
    (hell : 0 ≤ ell) (hh : DifferentiableOn ℂ h (polyNbhd (cpx P) r0))
    (hreal : RealOn (Dom n (cpx P) r0 s) (fun w => h w.2))
    (hess : ∀ I ∈ polyNbhd (cpx P) r0, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v)
    (hqc : IsQuasiConvex (realNbhd P r0) h ell m) : m ≤ M := by
  obtain ⟨I, hIP⟩ := hP
  have hI : I ∈ realNbhd P r0 := ⟨I, hIP, by simpa using hr⟩
  have hre : ∀ J ∈ realNbhd P r0, (h (KAM.realInclusion n J)).im = 0 := fun J hJ =>
    im_eq_zero_of_realOn hs hreal hJ
  obtain ⟨L, -, hLc, hLr⟩ := freq_deriv hh hre hI
  let w0 := KAM.frequencyMap h I
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨ξ, hξ0, hξ⟩ : ∃ ξ : Fin n → ℝ, ξ ≠ 0 ∧ w0 ⬝ᵥ ξ = 0 := by
    by_cases h0 : w0 i0 = 0
    · refine ⟨Pi.single i0 1, fun h => ?_, by simp [h0]⟩
      have := congrFun h i0
      simp at this
    · refine ⟨w0 i1 • Pi.single i0 1 - w0 i0 • Pi.single i1 1, fun h => ?_, ?_⟩
      · have := congrFun h i1
        simp [hi.symm] at this
        exact h0 this
      · simp [dotProduct_sub, dotProduct_smul]
        ring
  have hE : 0 < euclid ξ ^ 2 := by
    rw [euclid_sq_real]
    refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ?_
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hξ0
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hj⟩
  have hEn : 0 ≤ euclid ξ := Real.sqrt_nonneg _
  rcases hqc I hI ξ with hlt | hge
  · rw [hξ, abs_zero] at hlt
    exact absurd hlt (not_lt.2 (mul_nonneg hell hEn))
  · have hb := freq_bound hess hI L hLc ξ
    have hq := hessR_eq_dot L hLr ξ
    have hd : ξ ⬝ᵥ L ξ ≤ euclid ξ * euclid (L ξ) :=
      (le_abs_self _).trans (abs_dot_le_euclid ξ (L ξ))
    have h4 : m * euclid ξ ^ 2 ≤ M * euclid ξ ^ 2 := by
      calc m * euclid ξ ^ 2 ≤ hessR (realPart h) I ξ ξ := hge
        _ = ξ ⬝ᵥ L ξ := hq
        _ ≤ euclid ξ * euclid (L ξ) := hd
        _ ≤ euclid ξ * (M * euclid ξ) := by gcongr
        _ = M * euclid ξ ^ 2 := by ring
    exact le_of_mul_le_mul_right h4 hE

/-- Local real regularity, independent of global action-ball hypotheses of Part 1. -/
theorem local_real_regularity (S : Theorem1Setting P r0 s m M ell h f) :
    ContDiffOn ℝ 2 (realPart h) (realNbhd P r0) ∧
    ContinuousOn (KAM.frequencyMap h) (realNbhd P r0) ∧
    (∀ I ∈ realNbhd P r0, ∀ v : Fin n → ℝ,
      KAM.realInclusion n (fderiv ℝ (KAM.frequencyMap h) I v) =
        fun i => fderiv ℂ (fun J => fderiv ℂ h J (KAM.realInclusion n v))
          (KAM.realInclusion n I) (Pi.single i 1)) := by
  have hre : ∀ J ∈ realNbhd P r0, (h (KAM.realInclusion n J)).im = 0 := fun J hJ =>
    im_eq_zero_of_realOn S.hs S.real hJ
  refine ⟨contDiffOn_realPart S.holo, fun I hI => ?_, fun I hI v => ?_⟩
  · obtain ⟨L, hL, -⟩ := freq_deriv S.holo hre hI
    exact hL.differentiableAt.continuousAt.continuousWithinAt
  · obtain ⟨L, hL, hLc, -⟩ := freq_deriv S.holo hre hI
    rw [hL.fderiv]
    ext i
    exact hLc v i

/-- Supremum is used only on this guarded domain: a compact nonempty ball inside U_r0 P. -/
structure FrequencyBall (S : Theorem1Setting P r0 s m M ell h f) where
  center : Fin n → ℝ
  mem : center ∈ P
  radius : ℝ
  nonneg : 0 ≤ radius
  lt : radius < r0

def FrequencyBall.points {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) :
    Set (Fin n → ℝ) := {I | euclid (I - B.center) ≤ B.radius}

def FrequencyBall.maximum {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) : ℝ :=
  sSup ((fun I => euclid (KAM.frequencyMap h I)) '' B.points)

/-- Euclidean mean value inequality for the frequency map along a segment in `U_{r0} P`. -/
private theorem freq_lip (S : Theorem1Setting P r0 s m M ell h f) {c I : Fin n → ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (I - c) ∈ realNbhd P r0) :
    euclid (KAM.frequencyMap h I) ≤ euclid (KAM.frequencyMap h c) + M * euclid (I - c) := by
  have hre : ∀ J ∈ realNbhd P r0, (h (KAM.realInclusion n J)).im = 0 := fun J hJ =>
    im_eq_zero_of_realOn S.hs S.real hJ
  have hM0 : 0 ≤ M := (S.hm.le).trans S.hmM
  set F : Fin n → ℝ := KAM.frequencyMap h I - KAM.frequencyMap h c with hFdef
  have hE0 : 0 ≤ euclid F := Real.sqrt_nonneg _
  have hmain : euclid F ≤ M * euclid (I - c) := by
    rcases hE0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg hM0 (Real.sqrt_nonneg _)
    set pt : ℝ → Fin n → ℝ := fun t => c + t • (I - c) with hpt
    have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
        (fun t => ∑ i, F i * KAM.frequencyMap h (pt t) i)
        (∑ i, F i * (fderiv ℝ (KAM.frequencyMap h) (pt t) (I - c)) i) t := by
      intro t ht
      obtain ⟨L, hL, -⟩ := freq_deriv S.holo hre (hseg t ht)
      have hp : HasDerivAt pt (I - c) t := by
        exact (((hasDerivAt_id t).smul_const (I - c)).const_add c).congr_deriv (one_smul _ _)
      have h1 := hL.comp_hasDerivAt t hp
      rw [hL.fderiv]
      refine HasDerivAt.fun_sum fun i _ => ?_
      exact (hasDerivAt_pi.1 h1 i).const_mul (F i)
    have hcont : ContinuousOn (fun t => ∑ i, F i * KAM.frequencyMap h (pt t) i) (Icc 0 1) :=
      fun t ht => (hder t ht).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope
      (fun t => ∑ i, F i * KAM.frequencyMap h (pt t) i)
      (fun t => ∑ i, F i * (fderiv ℝ (KAM.frequencyMap h) (pt t) (I - c)) i) zero_lt_one hcont
      (fun t ht => hder t ⟨ht.1.le, ht.2.le⟩)
    have hg1 : ∑ i, F i * KAM.frequencyMap h (pt 1) i = ∑ i, F i * KAM.frequencyMap h I i := by
      simp [hpt]
    have hg0 : ∑ i, F i * KAM.frequencyMap h (pt 0) i = ∑ i, F i * KAM.frequencyMap h c i := by
      simp [hpt]
    have hsq : euclid F ^ 2 = ∑ i, F i * (KAM.frequencyMap h I i - KAM.frequencyMap h c i) := by
      rw [euclid_sq_real]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sq]; rfl
    have hslope : ∑ i, F i * (fderiv ℝ (KAM.frequencyMap h) (pt ξ) (I - c)) i = euclid F ^ 2 := by
      rw [hξd, hg1, hg0, sub_zero, div_one, hsq, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨L, hL, hLc, -⟩ := freq_deriv S.holo hre (hseg ξ ⟨hξ.1.le, hξ.2.le⟩)
    have hb := freq_bound S.hess (hseg ξ ⟨hξ.1.le, hξ.2.le⟩) L hLc (I - c)
    rw [hL.fderiv] at hslope
    have hd : ∑ i, F i * L (I - c) i ≤ euclid F * euclid (L (I - c)) :=
      (le_abs_self _).trans (abs_dot_le_euclid F (L (I - c)))
    have h2 : euclid F * euclid F ≤ euclid F * (M * euclid (I - c)) := by
      calc euclid F * euclid F = euclid F ^ 2 := (sq _).symm
        _ = _ := hslope.symm
        _ ≤ euclid F * euclid (L (I - c)) := hd
        _ ≤ _ := by gcongr
    exact le_of_mul_le_mul_left h2 hpos
  calc euclid (KAM.frequencyMap h I)
      = euclid (KAM.frequencyMap h c + F) := by rw [hFdef]; congr 1; abel
    _ ≤ euclid (KAM.frequencyMap h c) + euclid F := isActionNorm_euclid.add_le _ _
    _ ≤ _ := by gcongr

theorem frequency_maximum {S : Theorem1Setting P r0 s m M ell h f} (B : FrequencyBall S) :
    B.points ⊆ realNbhd P r0 ∧ IsCompact B.points ∧ B.points.Nonempty ∧
    (∃ I ∈ B.points, B.maximum = euclid (KAM.frequencyMap h I)) ∧
    (∀ I ∈ B.points, euclid (KAM.frequencyMap h I) ≤ B.maximum) ∧
    euclid (KAM.frequencyMap h B.center) ≤ B.maximum ∧
    B.maximum ≤ euclid (KAM.frequencyMap h B.center) + M * B.radius := by
  have hM0 : 0 ≤ M := (S.hm.le).trans S.hmM
  have hsub : B.points ⊆ realNbhd P r0 := by
    intro I hI
    exact ⟨B.center, B.mem, lt_of_le_of_lt (((norm_le_euclid (I - B.center)).1).trans hI) B.lt⟩
  have hcl : IsClosed B.points :=
    isClosed_le (isActionNorm_euclid.continuous.comp (continuous_id.sub continuous_const))
      continuous_const
  have hbd : Bornology.IsBounded B.points := by
    refine (Metric.isBounded_closedBall (x := B.center) (r := B.radius)).subset fun I hI => ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact ((norm_le_euclid (I - B.center)).1).trans hI
  have hcomp : IsCompact B.points := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hc0 : B.center ∈ B.points := by
    show euclid (B.center - B.center) ≤ B.radius
    rw [sub_self, isActionNorm_euclid.map_zero]
    exact B.nonneg
  have hcont : ContinuousOn (fun I => euclid (KAM.frequencyMap h I)) B.points :=
    isActionNorm_euclid.continuous.comp_continuousOn
      ((local_real_regularity S).2.1.mono hsub)
  obtain ⟨I1, hI1, hmax⟩ := hcomp.exists_isMaxOn ⟨B.center, hc0⟩ hcont
  have hgr : IsGreatest ((fun I => euclid (KAM.frequencyMap h I)) '' B.points)
      (euclid (KAM.frequencyMap h I1)) :=
    ⟨mem_image_of_mem _ hI1, by rintro _ ⟨x, hx, rfl⟩; exact isMaxOn_iff.1 hmax x hx⟩
  have hmx : B.maximum = euclid (KAM.frequencyMap h I1) := hgr.csSup_eq
  have hle : ∀ I ∈ B.points, euclid (KAM.frequencyMap h I) ≤ B.maximum := fun I hI => by
    rw [hmx]; exact isMaxOn_iff.1 hmax I hI
  refine ⟨hsub, hcomp, ⟨B.center, hc0⟩, ⟨I1, hI1, hmx⟩, hle, hle _ hc0, ?_⟩
  rw [hmx]
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, B.center + t • (I1 - B.center) ∈ realNbhd P r0 := by
    intro t ht
    refine hsub ?_
    show euclid (B.center + t • (I1 - B.center) - B.center) ≤ B.radius
    rw [add_sub_cancel_left, isActionNorm_euclid.smul, abs_of_nonneg ht.1]
    calc t * euclid (I1 - B.center) ≤ 1 * B.radius :=
          mul_le_mul ht.2 hI1 (Real.sqrt_nonneg _) zero_le_one
      _ = B.radius := one_mul _
  calc euclid (KAM.frequencyMap h I1)
      ≤ euclid (KAM.frequencyMap h B.center) + M * euclid (I1 - B.center) := freq_lip S hseg
    _ ≤ _ := by gcongr; exact hI1

theorem omega0_radius (S : Theorem1Setting P r0 s m M ell h f) :
    0 ≤ r0 / thmA m M ∧ r0 / thmA m M < r0 := by
  have hA : 11 ≤ thmA m M := by
    unfold thmA
    rw [mul_div_assoc]
    have : 1 ≤ M / m := (one_le_div S.hm).2 S.hmM
    linarith
  have hA0 : 0 < thmA m M := by linarith
  refine ⟨div_nonneg S.hr0.le hA0.le, ?_⟩
  rw [div_lt_iff₀ hA0]
  nlinarith [S.hr0]

def omega0Ball (S : Theorem1Setting P r0 s m M ell h f)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) : FrequencyBall S :=
  ⟨I0, hI, r0 / thmA m M, (omega0_radius S).1, (omega0_radius S).2⟩

theorem omega0 (S : Theorem1Setting P r0 s m M ell h f)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) :
    let B := omega0Ball S I0 hI
    B.points ⊆ realNbhd P r0 ∧
    (∃ I ∈ B.points, B.maximum = euclid (KAM.frequencyMap h I)) ∧
    (∀ I ∈ B.points, euclid (KAM.frequencyMap h I) ≤ B.maximum) ∧
    euclid (KAM.frequencyMap h I0) ≤ B.maximum ∧
    B.maximum ≤ euclid (KAM.frequencyMap h I0) + M * r0 / thmA m M := by
  intro B
  obtain ⟨h1, -, -, h4, h5, h6, h7⟩ := frequency_maximum B
  refine ⟨h1, h4, h5, h6, ?_⟩
  have : B.radius = r0 / thmA m M := rfl
  rw [this] at h7
  rwa [← mul_div_assoc] at h7

end Theorem1

end KAM.Nekhoroshev

end
