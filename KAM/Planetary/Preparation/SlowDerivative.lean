/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowData
public import KAM.Planetary.Preparation.SlowCauchy
public import KAM.Planetary.Preparation.SlowMean

/-!
# Slow averaging: derivatives of `h₀` (P11A-P7c, `stepP:p11:as-nr` inputs)

For `W I = C.C J + ∑ Ωᵢ(J)/(2π) ρᵢ + Z I` (the bracket of the secular formula of `h₀`):
the coordinate derivative of `W` in an action direction is bounded by Cauchy from a sup bound
of `W` on a polydisc, and its derivative in a `ρ`-direction is `Ωₐ(J)/(2π) + ∂_{ρₐ} Z`.
Together with `h₀ = C.h ∘ J + ε W` they give the pairing `k · ∂h₀` in each block.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section SlowDerivative

variable {n : ℕ}

/-- The bracket `C + ∑ Ω ρ/(2π) + Z` of the secular formula for `h₀`. -/
def p11SlowW (C : P11SecularData n) (Z : P11CVec (n+n) → ℂ) (I : P11CVec (n+n)) : ℂ :=
  C.C (fun i : Fin n => I (Fin.castAdd n i))+
    (∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i/(2*Real.pi)*
      I (Fin.natAdd n i))+Z I

/-- The action block of a joint action vector, as a continuous linear map. -/
def p11Jproj (n : ℕ) : P11CVec (n+n) →L[ℂ] P11CVec n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd n i)

theorem p11Jproj_apply (I : P11CVec (n+n)) :
    p11Jproj n I = fun i : Fin n => I (Fin.castAdd n i) := rfl

theorem p11Jproj_single_cast (a : Fin n) :
    p11Jproj n (Pi.single (Fin.castAdd n a) 1) = Pi.single a 1 := by
  funext i
  simp only [p11Jproj_apply, Pi.single_apply]
  simp [Fin.castAdd_inj]

theorem p11Jproj_single_nat (a : Fin n) :
    p11Jproj n (Pi.single (Fin.natAdd n a) 1) = 0 := by
  funext i
  simp only [p11Jproj_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h
  · have := congrArg Fin.val h
    simp at this
    omega
  · rfl

theorem hasFDerivAt_Jf (I : P11CVec (n+n)) :
    HasFDerivAt (fun x : P11CVec (n+n) => fun i : Fin n => x (Fin.castAdd n i))
      (p11Jproj n) I :=
  (p11Jproj n).hasFDerivAt

/-- Chain rule through the action block. -/
theorem fderiv_comp_Jf {ψ : P11CVec n → ℂ} {I : P11CVec (n+n)}
    (hψ : DifferentiableAt ℂ ψ (fun i : Fin n => I (Fin.castAdd n i))) (e : P11CVec (n+n)) :
    fderiv ℂ (fun x : P11CVec (n+n) => ψ (fun i : Fin n => x (Fin.castAdd n i))) I e =
      fderiv ℂ ψ (fun i : Fin n => I (Fin.castAdd n i)) (p11Jproj n e) := by
  have := hψ.hasFDerivAt.comp I (hasFDerivAt_Jf I)
  exact congrArg (fun L => L e) this.fderiv

end SlowDerivative

end KAM.Planetary

end
