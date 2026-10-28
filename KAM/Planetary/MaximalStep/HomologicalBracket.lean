/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Setting
public import KAM.Planetary.MaximalStep.Basic

/-!
# The bracket sign bridge (P11A-C5, `stepP:p11a:hm-bracket`)

For the normal form `N = h + ω·η` and the affine generating function `p0(θ) + p1(θ)·η`, the
existing Poisson bracket is `{N, φ} = -(ω·∂_θ p0 + (ω·∂_θ p1)·η)`, independently of any equation
solved by `p0, p1`.

`p11Affine` is shared with `P11A-C6` (`AffineFlowBasic`), which defines it with the same body; the
merge keeps one copy.
-/

@[expose] public noncomputable section
open Set
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Affine generating function in the existing Hamiltonian carrier. -/
def p11Affine {n : ℕ} (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n)
    (z : P11Phase n) : ℂ := p0 z.1+∑ i, p1 z.1 i*z.2 i

/-- Sign bridge for the existing frozen field and Poisson bracket, independent of any solving equation. -/
theorem p11_normal_affine_bracket {n : ℕ} (h : ℂ) (w : P11CVec n)
    {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {z : P11Phase n}
    (h0 : DifferentiableAt ℂ p0 z.1) (h1 : DifferentiableAt ℂ p1 z.1) :
    KAM.Canonical.poissonBracket (fun z : P11Phase n => h+∑ i, w i*z.2 i) (p11Affine p0 p1) z=
      -(fderiv ℂ p0 z.1 w+∑ i, fderiv ℂ p1 z.1 w i*z.2 i) := by
  have hproj : ∀ j : Fin n, HasFDerivAt (fun z : P11Phase n => z.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ (P11CVec n) (P11CVec n))) z :=
    fun j => (hasFDerivAt_apply (𝕜 := ℂ) j z.2).comp z (hasFDerivAt_snd (𝕜 := ℂ))
  have hu : HasFDerivAt (fun z : P11Phase n => h+∑ i, w i*z.2 i)
      (∑ i, w i • ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℂ (P11CVec n) (P11CVec n)))) z := by
    refine (HasFDerivAt.fun_add (hasFDerivAt_const h z)
      (HasFDerivAt.fun_sum fun i _ => (hproj i).const_mul (w i))).congr_fderiv (zero_add _)
  have hp0 : HasFDerivAt (fun z : P11Phase n => p0 z.1)
      ((fderiv ℂ p0 z.1).comp (ContinuousLinearMap.fst ℂ (P11CVec n) (P11CVec n))) z :=
    h0.hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℂ))
  have hp1 : ∀ j, HasFDerivAt (fun z : P11Phase n => p1 z.1 j)
      (((ContinuousLinearMap.proj j).comp (fderiv ℂ p1 z.1)).comp
        (ContinuousLinearMap.fst ℂ (P11CVec n) (P11CVec n))) z := fun j => by
    have h2 : HasFDerivAt (fun x : P11CVec n => p1 x j)
        ((ContinuousLinearMap.proj j).comp (fderiv ℂ p1 z.1)) z.1 :=
      (hasFDerivAt_apply (𝕜 := ℂ) j (p1 z.1)).comp z.1 h1.hasFDerivAt
    exact h2.comp z (hasFDerivAt_fst (𝕜 := ℂ))
  have hv : HasFDerivAt (p11Affine p0 p1)
      ((fderiv ℂ p0 z.1).comp (ContinuousLinearMap.fst ℂ (P11CVec n) (P11CVec n)) +
        ∑ j, (p1 z.1 j • ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.snd ℂ (P11CVec n) (P11CVec n))) +
          z.2 j • (((ContinuousLinearMap.proj j).comp (fderiv ℂ p1 z.1)).comp
            (ContinuousLinearMap.fst ℂ (P11CVec n) (P11CVec n))))) z := by
    refine HasFDerivAt.fun_add hp0 ?_
    exact HasFDerivAt.fun_sum fun j _ => (hp1 j).mul (hproj j)
  unfold KAM.Canonical.poissonBracket
  rw [hu.fderiv, hv.fderiv]
  simp
  have hw : w = ∑ x, w x • (Pi.single x 1 : P11CVec n) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e0 : fderiv ℂ p0 z.1 w = ∑ x, w x * fderiv ℂ p0 z.1 (Pi.single x 1) := by
    conv_lhs => rw [hw]
    simp [map_sum, map_smul]
  have e1 : ∀ i, fderiv ℂ p1 z.1 w i = ∑ x, w x * fderiv ℂ p1 z.1 (Pi.single x 1) i := fun i => by
    conv_lhs => rw [hw]
    simp [map_sum, map_smul, Finset.sum_apply]
  have e2 : ∀ x : Fin n, (∑ i, w i * (Pi.single x 1 : P11CVec n) i) = w x := fun x => by
    simp [Pi.single_apply]
  simp only [e2, e0, e1, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i x => w x * (fderiv ℂ p1 z.1 (Pi.single x 1)) i * z.2 i)]
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

end KAM.Planetary
