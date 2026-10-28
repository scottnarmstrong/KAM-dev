/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import KAM.Nekhoroshev.QuasiConvex
public import KAM.Nekhoroshev.QcZero.Kernel

/-!
# Derivative of the isoenergetic map in coordinates

Blueprint `bpN:p2:qc-deriv` and steps `qd-first`, `qd-freq`, `qd-sym`, `qd-prod`: for `h` with
`Re h` of class `C²` on an open set `U` and `I ∈ U`, the map
`(I, λ) ↦ (Re h I, λ ∇h(I))` has derivative `bordered_map ν(I) (D²h(I)) λ` at `(I, λ)`,
where `D²h(I)` is the coordinate matrix of the real Hessian (symmetric by Schwarz).
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

open scoped ContDiff

variable {n : ℕ}

/-- Coordinate matrix of the real Hessian; not the complex Hessian of Part 1. -/
def real_hessian_matrix (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) (Pi.single j 1)

private lemma freq_eq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) :
    KAM.frequencyMap h I = fun i => fderiv ℝ (realPart h) I (Pi.single i 1) := rfl

private lemma contDiffAt_real {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ 2 (realPart h) U) {I : Fin n → ℝ} (hI : I ∈ U) :
    ContDiffAt ℝ 2 (realPart h) I :=
  hh.contDiffAt (hU.mem_nhds hI)

private lemma hasFDerivAt_freq {g : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} (hg : ContDiffAt ℝ 2 g I) :
    HasFDerivAt (fun J : Fin n → ℝ => fun i => fderiv ℝ g J (Pi.single i 1))
      (ContinuousLinearMap.pi fun i =>
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).comp
          (fderiv ℝ (fderiv ℝ g) I)) I := by
  have hdg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) I) I :=
    ((ContDiffAt.fderiv_right hg (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [hasFDerivAt_pi]
  intro i
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).hasFDerivAt.comp I hdg

private lemma hasFDerivAt_first {g : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} (lam : ℝ)
    (hg : ContDiffAt ℝ 2 g I) :
    HasFDerivAt (fun p : (Fin n → ℝ) × ℝ => g p.1)
      ((fderiv ℝ g I).comp (ContinuousLinearMap.fst ℝ _ _)) (I, lam) :=
  (hg.differentiableAt (by norm_num)).hasFDerivAt.comp (I, lam) hasFDerivAt_fst

private lemma hasFDerivAt_prod {g : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} (lam : ℝ)
    (hg : ContDiffAt ℝ 2 g I) :
    HasFDerivAt (fun p : (Fin n → ℝ) × ℝ =>
        p.2 • (fun i => fderiv ℝ g p.1 (Pi.single i 1)))
      (lam • ((ContinuousLinearMap.pi fun i =>
          (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).comp
            (fderiv ℝ (fderiv ℝ g) I)).comp (ContinuousLinearMap.fst ℝ _ _)) +
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight
          (fun i => fderiv ℝ g I (Pi.single i 1))) (I, lam) := by
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin n → ℝ) (F := ℝ) (p := (I, lam))).smul
    ((hasFDerivAt_freq hg).comp (I, lam)
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Fin n → ℝ) (F := ℝ) (p := (I, lam))))
  exact h2

private lemma sym_hess {g : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} (hg : ContDiffAt ℝ 2 g I)
    (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ g) I v w = fderiv ℝ (fderiv ℝ g) I w v :=
  (hg.isSymmSndFDerivAt (by simp)) v w

private lemma hess_apply {g : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} (hg : ContDiffAt ℝ 2 g I)
    (v : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fderiv ℝ g) I v (Pi.single i 1) =
      ∑ j, fderiv ℝ (fderiv ℝ g) I (Pi.single i 1) (Pi.single j 1) * v j := by
  rw [sym_hess hg v, clm_apply_eq_sum (fderiv ℝ (fderiv ℝ g) I (Pi.single i 1)) v]

section Derivative
variable {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
variable (hU : IsOpen U) (hh : ContDiffOn ℝ 2 (realPart h) U)
variable {I : Fin n → ℝ} (hI : I ∈ U)
include hU hh hI

theorem qd_first (lam : ℝ) :
    DifferentiableAt ℝ (fun p : (Fin n → ℝ) × ℝ => realPart h p.1) (I, lam) ∧
    ∀ v u, fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => realPart h p.1) (I, lam) (v, u) =
      ∑ i, KAM.frequencyMap h I i * v i := by
  have hd := hasFDerivAt_first lam (contDiffAt_real hU hh hI)
  refine ⟨hd.differentiableAt, fun v u => ?_⟩
  rw [hd.fderiv]
  simpa [freq_eq] using clm_apply_eq_sum (fderiv ℝ (realPart h) I) v

theorem qd_freq : ContDiffOn ℝ 1 (KAM.frequencyMap h) U ∧
    DifferentiableAt ℝ (KAM.frequencyMap h) I ∧
    ∀ v i, fderiv ℝ (KAM.frequencyMap h) I v i =
      fderiv ℝ (fderiv ℝ (realPart h)) I v (Pi.single i 1) := by
  have hd := hasFDerivAt_freq (contDiffAt_real hU hh hI)
  have hfun : KAM.frequencyMap h =
      fun J : Fin n → ℝ => fun i => fderiv ℝ (realPart h) J (Pi.single i 1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun, contDiffOn_pi]
    intro i
    exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).contDiff.comp_contDiffOn
      (hh.fderiv_of_isOpen hU (m := 1) (by norm_num))
  · rw [hfun]; exact hd.differentiableAt
  · intro v i
    rw [hfun, hd.fderiv]
    rfl

theorem qd_sym :
    (∀ i j, real_hessian_matrix h I i j = real_hessian_matrix h I j i) ∧
    (∀ v, fderiv ℝ (KAM.frequencyMap h) I v =
      fun i => ∑ j, real_hessian_matrix h I i j * v j) ∧
    ∀ v, (∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j) =
      fderiv ℝ (fderiv ℝ (realPart h)) I v v := by
  have hg := contDiffAt_real hU hh hI
  refine ⟨fun i j => sym_hess hg _ _, fun v => ?_, fun v => ?_⟩
  · funext i
    rw [(qd_freq hU hh hI).2.2 v i]
    exact hess_apply hg v i
  · rw [clm_apply_eq_sum (fderiv ℝ (fderiv ℝ (realPart h)) I v) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hess_apply hg v i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [real_hessian_matrix]
    ring

theorem qd_prod (lam : ℝ) :
    DifferentiableAt ℝ (fun p : (Fin n → ℝ) × ℝ => p.2 • KAM.frequencyMap h p.1)
      (I, lam) ∧
    ∀ v u, fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => p.2 • KAM.frequencyMap h p.1)
      (I, lam) (v, u) = u • KAM.frequencyMap h I +
        lam • (fun i => ∑ j, real_hessian_matrix h I i j * v j) := by
  have hg := contDiffAt_real hU hh hI
  have hd := hasFDerivAt_prod lam hg
  refine ⟨hd.differentiableAt, fun v u => ?_⟩
  change fderiv ℝ (fun p : (Fin n → ℝ) × ℝ =>
    p.2 • (fun i => fderiv ℝ (realPart h) p.1 (Pi.single i 1))) (I, lam) (v, u) = _
  rw [hd.fderiv, add_comm]
  ext i
  have := hess_apply hg v i
  simp [freq_eq, this, real_hessian_matrix]

theorem qc_deriv (lam : ℝ) :
    HasFDerivAt (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1))
      (bordered_map (KAM.frequencyMap h I) (real_hessian_matrix h I) lam) (I, lam) := by
  have hg := contDiffAt_real hU hh hI
  refine ((hasFDerivAt_first lam hg).prodMk (hasFDerivAt_prod lam hg)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ⟨v, u⟩ => ?_
  rw [bordered_map_apply]
  refine Prod.ext ?_ ?_
  · have := (qd_first hU hh hI lam).2 v u
    rw [(hasFDerivAt_first lam hg).fderiv] at this
    simpa using this
  · have := (qd_prod hU hh hI lam).2 v u
    rw [show (fun p : (Fin n → ℝ) × ℝ => p.2 • KAM.frequencyMap h p.1) =
      (fun p : (Fin n → ℝ) × ℝ => p.2 • (fun i => fderiv ℝ (realPart h) p.1 (Pi.single i 1)))
      from rfl, (hasFDerivAt_prod lam hg).fderiv] at this
    simpa using this
end Derivative

end KAM.Nekhoroshev
