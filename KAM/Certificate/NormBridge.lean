/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.PhaseBasis
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Norms on `ℂⁿ × ℂⁿ` from partial derivatives

Bridges between the row-sum bounds computed by the certificate checker (sums of norms of partial
derivatives along the phase basis) and the operator norms used by the iso-energetic a-posteriori
theorem: `‖Dƒ‖ ≤ ∑ₐ ‖∂ₐ ƒ‖`, the analogue for second derivatives, `X_H` in partials, and the
row-sum bounds for `DX_H` and `D²X_H`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

open KAM.Torus

variable {n : ℕ}

/-- Expansion of a vector in the phase basis. -/
theorem sum_sumVec_smul_phaseBasis (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    ∑ a : Fin n ⊕ Fin n, sumVec n v a • phaseBasis a = v := by
  apply (sumVec n).injective
  rw [map_sum]
  simp only [phaseBasis, map_smul, LinearEquiv.apply_symm_apply]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem norm_sumVec_apply_le (v : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    ‖sumVec n v a‖ ≤ ‖v‖ := by
  rw [← norm_sumVec]
  exact norm_le_pi_norm (sumVec n v) a

/-- Operator norm on `ℂⁿ × ℂⁿ` bounded by the sum over the phase basis. -/
theorem norm_clm_le_sum_phaseBasis {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] G) :
    ‖L‖ ≤ ∑ a : Fin n ⊕ Fin n, ‖L (phaseBasis a)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  conv_lhs => rw [← sum_sumVec_smul_phaseBasis v]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul (le_refl _) (norm_sumVec_apply_le v a) (norm_nonneg _) (norm_nonneg _)

theorem norm_fderiv_le_sum_partials {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖fderiv ℂ f z‖ ≤ ∑ a : Fin n ⊕ Fin n, ‖fderiv ℂ f z (phaseBasis a)‖ :=
  norm_clm_le_sum_phaseBasis _

/-- A continuous bilinear form on `ℂⁿ × ℂⁿ` is bounded by its values on the phase basis. -/
theorem norm_cmm_two_le_sum_phaseBasis
    (M : ((Fin n → ℂ) × (Fin n → ℂ)) [×2]→L[ℂ] ℂ) :
    ‖M‖ ≤ ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ‖M ![phaseBasis a, phaseBasis b]‖ := by
  have h1 : ‖M‖ = ‖M.curryLeft‖ := (M.curryLeft_norm).symm
  rw [h1]
  refine (norm_clm_le_sum_phaseBasis _).trans (Finset.sum_le_sum fun a _ => ?_)
  set N := M.curryLeft (phaseBasis a)
  have h2 : ‖N‖ = ‖(continuousMultilinearCurryFin1 ℂ ((Fin n → ℂ) × (Fin n → ℂ)) ℂ) N‖ :=
    ((continuousMultilinearCurryFin1 ℂ _ ℂ).norm_map N).symm
  rw [h2]
  refine (norm_clm_le_sum_phaseBasis _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  simp only [continuousMultilinearCurryFin1_apply, N, ContinuousMultilinearMap.curryLeft_apply]
  congr 2
  funext i; fin_cases i <;> rfl

theorem norm_iteratedFDeriv_two_le_sum_partials
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖iteratedFDeriv ℂ 2 f z‖ ≤
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
        ‖iteratedFDeriv ℂ 2 f z ![phaseBasis a, phaseBasis b]‖ :=
  norm_cmm_two_le_sum_phaseBasis _

theorem phaseBasis_inl (j : Fin n) : phaseBasis (.inl j) = (Pi.single j 1, 0) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · by_cases h : i = j <;> simp [phaseBasis, sumVec, h]
  · simp [phaseBasis, sumVec]

/-- `X_H` in partials: `(X_H)_{inl i} = ∂_{inr i} H`, `(X_H)_{inr i} = -∂_{inl i} H`. -/
theorem hamiltonianVectorFieldℂ_sumVec (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) a =
      Sum.elim (fun i => fderiv ℂ H z (phaseBasis (.inr i)))
        (fun i => -fderiv ℂ H z (phaseBasis (.inl i))) a := by
  rcases a with i | i <;>
    simp [hamiltonianVectorFieldℂ, sumVec_apply, phaseBasis_inr, phaseBasis_inl]

/-- Sign of the coordinate `a` of `X_H`. -/
def hamSign (a : Fin n ⊕ Fin n) : ℂ := Sum.elim (fun _ => 1) (fun _ => -1) a

theorem norm_hamSign (a : Fin n ⊕ Fin n) : ‖hamSign a‖ = 1 := by
  rcases a with i | i <;> simp [hamSign]

theorem sumVec_hamiltonianVectorFieldℂ_swap (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) a = hamSign a * fderiv ℂ H z (phaseBasis a.swap) := by
  rw [hamiltonianVectorFieldℂ_sumVec]
  rcases a with i | i <;> simp [hamSign]

theorem hamiltonianVectorFieldℂ_eq_symm (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    hamiltonianVectorFieldℂ H =
      fun w => (sumVecIso n).symm (fun a => hamSign a * fderiv ℂ H w (phaseBasis a.swap)) := by
  funext w
  apply (sumVecIso n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sumVecIso_apply]
  funext a
  exact sumVec_hamiltonianVectorFieldℂ_swap H w a

theorem sumVec_fderiv_hamiltonianVectorFieldℂ {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : ContDiffAt ℂ 2 H w) (v : (Fin n → ℂ) × (Fin n → ℂ))
    (a : Fin n ⊕ Fin n) :
    sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ H) w v) a =
      hamSign a * fderiv ℂ (fderiv ℂ H) w v (phaseBasis a.swap) := by
  have hd : DifferentiableAt ℂ (fderiv ℂ H) w :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : HasFDerivAt (fun w a => hamSign a * fderiv ℂ H w (phaseBasis a.swap))
      (ContinuousLinearMap.pi fun a => hamSign a •
        (ContinuousLinearMap.apply ℂ ℂ (phaseBasis a.swap)).comp (fderiv ℂ (fderiv ℂ H) w)) w := by
    refine hasFDerivAt_pi'.2 fun a => ?_
    exact (((ContinuousLinearMap.apply ℂ ℂ (phaseBasis a.swap)).hasFDerivAt.comp w
      hd.hasFDerivAt)).const_mul (hamSign a)
  have hX := ((sumVecIso n).symm.toContinuousLinearEquiv.hasFDerivAt.comp w hG)
  have hfun : hamiltonianVectorFieldℂ H = ⇑(sumVecIso n).symm.toContinuousLinearEquiv ∘
      fun w a => hamSign a * fderiv ℂ H w (phaseBasis a.swap) :=
    hamiltonianVectorFieldℂ_eq_symm H
  rw [hfun, hX.fderiv]
  exact congrFun ((sumVecIso n).apply_symm_apply _) a

/-- Row-sum bound for `DX_H` from second partials; local `C²` (division, O2). `1 ≤ n` makes the
row-sum premise nonvacuous, hence `0 ≤ B` (at `n = 0` the statement fails for `B < 0`, audit 2
F8); the checker derives it from `StaticFacts.hn : 2 ≤ n`. -/
theorem norm_fderiv_hamiltonianVectorFieldℂ_le (hn : 1 ≤ n)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 2 H z) {B : ℝ}
    (hB : ∀ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
      ‖iteratedFDeriv ℂ 2 H z ![phaseBasis (Sum.swap a), phaseBasis b]‖ ≤ B) :
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ B := by
  have hB0 : 0 ≤ B :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hB (.inl ⟨0, hn⟩))
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun v => ?_
  rw [← norm_sumVec]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  rw [sumVec_fderiv_hamiltonianVectorFieldℂ hH, norm_mul, norm_hamSign, one_mul]
  set e := phaseBasis a.swap
  rw [(hH.isSymmSndFDerivAt (by simp)).eq v e]
  set L := fderiv ℂ (fderiv ℂ H) z e
  have h1 : ‖L‖ ≤ B := by
    refine (norm_clm_le_sum_phaseBasis L).trans (le_trans (le_of_eq ?_) (hB a))
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [iteratedFDeriv_two_apply]
    rfl
  exact (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

theorem iteratedFDeriv_three_apply (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z u v e : (Fin n → ℂ) × (Fin n → ℂ)) :
    iteratedFDeriv ℂ 3 H z ![u, v, e] = fderiv ℂ (fderiv ℂ (fderiv ℂ H)) z u v e := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

theorem iteratedFDeriv_three_swap_first {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 3 H z) (u v e : (Fin n → ℂ) × (Fin n → ℂ)) :
    iteratedFDeriv ℂ 3 H z ![u, v, e] = iteratedFDeriv ℂ 3 H z ![v, u, e] := by
  have h2 : ContDiffAt ℂ 2 (fderiv ℂ H) z := hH.fderiv_right (m := 2) (by norm_num)
  rw [iteratedFDeriv_three_apply, iteratedFDeriv_three_apply,
    (h2.isSymmSndFDerivAt (by simp)).eq u v]

theorem iteratedFDeriv_three_swap_last {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 3 H z) (u v e : (Fin n → ℂ) × (Fin n → ℂ)) :
    iteratedFDeriv ℂ 3 H z ![u, v, e] = iteratedFDeriv ℂ 3 H z ![u, e, v] := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ 2 H) z :=
    hH.differentiableAt_iteratedFDeriv (by norm_num)
  have key : ∀ v e : (Fin n → ℂ) × (Fin n → ℂ), iteratedFDeriv ℂ 3 H z ![u, v, e] =
      fderiv ℂ (fun y => iteratedFDeriv ℂ 2 H y ![v, e]) z u := fun v e =>
    hd.iteratedFDeriv_succ_apply_left' (m := ![u, v, e])
  rw [key, key]
  have hev : (fun y => iteratedFDeriv ℂ 2 H y ![v, e]) =ᶠ[nhds z]
      fun y => iteratedFDeriv ℂ 2 H y ![e, v] := by
    filter_upwards [hH.eventually (by simp)] with y hy
    have hy2 : ContDiffAt ℂ 2 H y := hy.of_le (by norm_num)
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
      (hy2.isSymmSndFDerivAt (by simp)).eq]
    rfl
  rw [hev.fderiv_eq]

theorem iteratedFDeriv_three_rotate {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hH : ContDiffAt ℂ 3 H z) (u v e : (Fin n → ℂ) × (Fin n → ℂ)) :
    iteratedFDeriv ℂ 3 H z ![u, v, e] = iteratedFDeriv ℂ 3 H z ![e, u, v] := by
  rw [iteratedFDeriv_three_swap_last hH u v e, iteratedFDeriv_three_swap_first hH u e v]

/-- Bound for `D²X_H` from third partials; local `C³`; `1 ≤ n` as above (F8). -/
theorem norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le (hn : 1 ≤ n)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hH : ContDiffAt ℂ 3 H z)
    {B : ℝ} (hB : ∀ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ c : Fin n ⊕ Fin n,
      ‖iteratedFDeriv ℂ 3 H z ![phaseBasis (Sum.swap a), phaseBasis b, phaseBasis c]‖ ≤ B) :
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ B := by
  have hB0 : 0 ≤ B :=
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _).trans
      (hB (.inl ⟨0, hn⟩))
  set Y : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n ⊕ Fin n → ℂ) :=
    fun w a => hamSign a * fderiv ℂ H w (phaseBasis a.swap) with hY
  have hXY : (sumVecIso n) ∘ hamiltonianVectorFieldℂ H = Y := by
    funext w
    rw [Function.comp_apply, hamiltonianVectorFieldℂ_eq_symm, LinearIsometryEquiv.apply_symm_apply]
  rw [← (sumVecIso n).norm_iteratedFDeriv_comp_left, hXY]
  have h2 : ContDiffAt ℂ 2 (fderiv ℂ H) z := hH.fderiv_right (m := 2) (by norm_num)
  have hYc : ContDiffAt ℂ 2 Y z := by
    refine contDiffAt_pi.2 fun a => ?_
    exact contDiffAt_const.mul
      ((ContinuousLinearMap.apply ℂ ℂ (phaseBasis a.swap)).contDiff.contDiffAt.comp z h2)
  refine ContinuousMultilinearMap.opNorm_le_bound hB0 fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  set e := phaseBasis a.swap
  have hcoord : iteratedFDeriv ℂ 2 Y z m a = hamSign a * iteratedFDeriv ℂ 3 H z ![m 0, m 1, e] := by
    have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin n => ℂ) a
      ).iteratedFDeriv_comp_left hYc (le_refl 2)
    have h3 : (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin n => ℂ) a) ∘ Y =
        (hamSign a • ContinuousLinearMap.apply ℂ ℂ e) ∘ fderiv ℂ H := by
      funext w; simp [hY, e]
    rw [h3] at h1
    have h4 := (hamSign a • ContinuousLinearMap.apply ℂ ℂ e).iteratedFDeriv_comp_left h2
      (le_refl 2)
    have h5 := congrArg (fun T => T m) (h1.symm.trans h4)
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.proj_apply] at h5
    rw [h5, iteratedFDeriv_two_apply, iteratedFDeriv_three_apply]
    simp [e]
  rw [hcoord, norm_mul, norm_hamSign, one_mul,
    iteratedFDeriv_three_rotate hH, Fin.prod_univ_two]
  set Q : ((Fin n → ℂ) × (Fin n → ℂ)) [×2]→L[ℂ] ℂ := fderiv ℂ (iteratedFDeriv ℂ 2 H) z e
  have hQ : iteratedFDeriv ℂ 3 H z ![e, m 0, m 1] = Q ![m 0, m 1] := rfl
  have hQb : ∀ b c : Fin n ⊕ Fin n,
      ‖Q ![phaseBasis b, phaseBasis c]‖ =
        ‖iteratedFDeriv ℂ 3 H z ![e, phaseBasis b, phaseBasis c]‖ :=
    fun b c => by rw [← show iteratedFDeriv ℂ 3 H z ![e, phaseBasis b, phaseBasis c] =
      Q ![phaseBasis b, phaseBasis c] from rfl]
  have hQn : ‖Q‖ ≤ B := by
    refine (norm_cmm_two_le_sum_phaseBasis Q).trans (le_trans (le_of_eq ?_) (hB a))
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hQb b c
  rw [hQ]
  refine (Q.le_opNorm _).trans ?_
  rw [Fin.prod_univ_two]
  exact mul_le_mul_of_nonneg_right hQn (by positivity)

end KAM.Certificate

end
