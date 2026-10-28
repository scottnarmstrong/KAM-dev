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

/-- The `ρ`-direction derivative of the bracket: `Ωₐ(J)/(2π) + ∂_{ρₐ} Z`. -/
theorem fderiv_slowW_nat {C : P11SecularData n} {Z : P11CVec (n+n) → ℂ} {I : P11CVec (n+n)}
    (hCd : DifferentiableAt ℂ C.C (fun i : Fin n => I (Fin.castAdd n i)))
    (hOd : DifferentiableAt ℂ C.Omega (fun i : Fin n => I (Fin.castAdd n i)))
    (hZ : DifferentiableAt ℂ Z I) (a : Fin n) :
    fderiv ℂ (p11SlowW C Z) I (Pi.single (Fin.natAdd n a) 1) =
      C.Omega (fun j : Fin n => I (Fin.castAdd n j)) a/(2*Real.pi)+
        fderiv ℂ Z I (Pi.single (Fin.natAdd n a) 1) := by
  have hA : HasFDerivAt (fun x : P11CVec (n+n) => C.C (fun i : Fin n => x (Fin.castAdd n i)))
      ((fderiv ℂ C.C (fun i : Fin n => I (Fin.castAdd n i))).comp (p11Jproj n)) I :=
    hCd.hasFDerivAt.comp I (hasFDerivAt_Jf I)
  have hB : ∀ i ∈ Finset.univ, HasFDerivAt
      (fun x : P11CVec (n+n) => C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i/(2*Real.pi)*
        x (Fin.natAdd n i))
      ((C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i/(2*Real.pi)) •
        (ContinuousLinearMap.proj (Fin.natAdd n i) : P11CVec (n+n) →L[ℂ] ℂ) +
        (I (Fin.natAdd n i)) • ((2*Real.pi : ℂ)⁻¹ •
          ((fderiv ℂ (fun J : P11CVec n => C.Omega J i)
            (fun j : Fin n => I (Fin.castAdd n j))).comp (p11Jproj n)))) I := by
    intro i _
    have h1 : HasFDerivAt (fun J : P11CVec n => C.Omega J i)
        (fderiv ℂ (fun J : P11CVec n => C.Omega J i) (fun j : Fin n => I (Fin.castAdd n j)))
        (fun j : Fin n => I (Fin.castAdd n j)) :=
      (differentiableAt_pi.1 hOd i).hasFDerivAt
    have h1' : HasFDerivAt (fun x : P11CVec (n+n) =>
        C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i)
        ((fderiv ℂ (fun J : P11CVec n => C.Omega J i)
          (fun j : Fin n => I (Fin.castAdd n j))).comp (p11Jproj n)) I :=
      HasFDerivAt.comp (f := fun x : P11CVec (n+n) => fun j : Fin n => x (Fin.castAdd n j))
        (g := fun J : P11CVec n => C.Omega J i) I h1 (hasFDerivAt_Jf I)
    have h2 : HasFDerivAt (fun x : P11CVec (n+n) =>
        C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i/(2*Real.pi))
        ((2*Real.pi : ℂ)⁻¹ • ((fderiv ℂ (fun J : P11CVec n => C.Omega J i)
          (fun j : Fin n => I (Fin.castAdd n j))).comp (p11Jproj n))) I := by
      convert h1'.const_smul ((2*Real.pi : ℂ)⁻¹) using 1
      funext x
      simp [div_eq_inv_mul]
    have h3 : HasFDerivAt (fun x : P11CVec (n+n) => x (Fin.natAdd n i))
        (ContinuousLinearMap.proj (Fin.natAdd n i) : P11CVec (n+n) →L[ℂ] ℂ) I :=
      (ContinuousLinearMap.proj (Fin.natAdd n i) : P11CVec (n+n) →L[ℂ] ℂ).hasFDerivAt
    exact h2.mul h3
  have hS := HasFDerivAt.sum hB
  have hW := (hA.add hS).add hZ.hasFDerivAt
  have hfun : p11SlowW C Z = ((fun x : P11CVec (n+n) =>
      C.C (fun i : Fin n => x (Fin.castAdd n i))) +
      ∑ i : Fin n, fun x : P11CVec (n+n) =>
        C.Omega (fun j : Fin n => x (Fin.castAdd n j)) i/(2*Real.pi)*x (Fin.natAdd n i)) + Z := by
    funext x
    simp [p11SlowW, Finset.sum_apply]
  rw [hfun, hW.fderiv]
  have h0 : p11Jproj n (Pi.single (a.addNat n) 1) = 0 := by
    simpa only [Fin.natAdd_eq_addNat] using p11Jproj_single_nat a
  simp [h0, Pi.single_apply]

/-- The action block of a mode vector. -/
theorem p11dotC_split (k : Fin (n+n) → ℤ) (v : P11CVec (n+n)) :
    p11dotC k v = p11dotC (fun i : Fin n => k (Fin.castAdd n i))
      (fun i : Fin n => v (Fin.castAdd n i)) +
      p11dotC (fun i : Fin n => k (Fin.natAdd n i)) (fun i : Fin n => v (Fin.natAdd n i)) := by
  unfold p11dotC
  rw [Fin.sum_univ_add]

/-- `k · ∂h₀ = k₁ · ω(J) + ε k · ∂W` when `h₀ = h ∘ J + ε W` near `I`. -/
theorem p11_slow_dotC_split {C : P11SecularData n} {Z h0 : P11CVec (n+n) → ℂ} {eps : ℝ}
    {I : P11CVec (n+n)}
    (hEv : h0 =ᶠ[nhds I] fun x : P11CVec (n+n) =>
      C.h (fun i : Fin n => x (Fin.castAdd n i))+eps*p11SlowW C Z x)
    (hh : DifferentiableAt ℂ C.h (fun i : Fin n => I (Fin.castAdd n i)))
    (hW : DifferentiableAt ℂ (p11SlowW C Z) I)
    (hω : C.omega (fun i : Fin n => I (Fin.castAdd n i)) =
      fun i => fderiv ℂ C.h (fun i : Fin n => I (Fin.castAdd n i)) (Pi.single i 1))
    (k : Fin (n+n) → ℤ) :
    p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1)) =
      p11dotC (fun i : Fin n => k (Fin.castAdd n i)) (C.omega (fun i : Fin n => I (Fin.castAdd n i)))+
        eps*p11dotC k (fun i => fderiv ℂ (p11SlowW C Z) I (Pi.single i 1)) := by
  have hd : ∀ e, fderiv ℂ h0 I e = fderiv ℂ C.h (fun i : Fin n => I (Fin.castAdd n i))
      (p11Jproj n e)+eps*fderiv ℂ (p11SlowW C Z) I e := by
    intro e
    rw [hEv.fderiv_eq]
    have h1 : HasFDerivAt (fun x : P11CVec (n+n) => C.h (fun i : Fin n => x (Fin.castAdd n i)))
        ((fderiv ℂ C.h (fun i : Fin n => I (Fin.castAdd n i))).comp (p11Jproj n)) I :=
      hh.hasFDerivAt.comp I (hasFDerivAt_Jf I)
    have h2 := h1.add (hW.hasFDerivAt.const_mul eps)
    have h3 := congrArg (fun L => L e) h2.fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at h3
    exact h3
  have hs : ∀ j : Fin (n+n), (k j : ℂ) * fderiv ℂ h0 I (Pi.single j 1) =
      (k j : ℂ) * fderiv ℂ C.h (fun i : Fin n => I (Fin.castAdd n i))
        (p11Jproj n (Pi.single j 1)) +
      eps*((k j : ℂ) * fderiv ℂ (p11SlowW C Z) I (Pi.single j 1)) := by
    intro j; rw [hd]; ring
  unfold p11dotC
  rw [Finset.sum_congr rfl fun j _ => hs j, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Fin.sum_univ_add]
  simp only [p11Jproj_single_nat, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [p11Jproj_single_cast, hω]

variable {N : ℕ}

/-- Cauchy bound for a coordinate derivative of a scalar holomorphic function on a polydisc. -/
theorem p11_scalar_step_bound {U : Set (P11CVec N)} (hU : IsOpen U) {W : P11CVec N → ℂ}
    (hW : DifferentiableOn ℂ W U) {I : P11CVec N} {R M : ℝ} (hR : 0 < R)
    (hcl : closedBall I R ⊆ U) (hM : ∀ y ∈ closedBall I R, ‖W y‖ ≤ M) (i : Fin N) :
    ‖fderiv ℂ W I (Pi.single i 1)‖ ≤ M/R := by
  have hg : DifferentiableOn ℂ (fun x : P11CVec N => (fun _ : Fin 1 => W x)) U :=
    differentiableOn_pi.2 fun _ => hW
  have hb := p11Step_iterate_bound hU hg hR hcl ∅ i (by simp)
    (B := M) (fun y _ hy => by
      have hy' : y ∈ closedBall I R := by
        rw [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hR.le]
        intro j
        simpa using hy j (by simp)
      have := hM y hy'
      refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans this)).2 fun _ => this)
    1 I (by simp) (fun j _ => by simp [hR.le])
  have hdi : DifferentiableAt ℂ W I := hW.differentiableAt (hU.mem_nhds (hcl (mem_closedBall_self hR.le)))
  have hf : fderiv ℂ (fun x : P11CVec N => (fun _ : Fin 1 => W x)) I (Pi.single i 1) =
      fun _ => fderiv ℂ W I (Pi.single i 1) := by
    rw [fderiv_pi (fun _ => hdi)]
    rfl
  simp only [Function.iterate_one, p11Step, hf, Nat.factorial_one, Nat.cast_one, one_mul,
    pow_one] at hb
  have h0 : ‖fderiv ℂ W I (Pi.single i 1)‖ ≤ ‖fun _ : Fin 1 => fderiv ℂ W I (Pi.single i 1)‖ :=
    norm_le_pi_norm (fun _ : Fin 1 => fderiv ℂ W I (Pi.single i 1)) 0
  exact h0.trans hb

/-- The embedding `ρ ↦ (0, ρ)` of the angle-momentum block, as a continuous linear map. -/
def p11appR (n : ℕ) : P11CVec n →L[ℂ] P11CVec (n+n) :=
  ContinuousLinearMap.pi fun j : Fin (n+n) =>
    Fin.addCases (motive := fun _ => P11CVec n →L[ℂ] ℂ) (fun _ => 0)
      (fun a => ContinuousLinearMap.proj a) j

theorem p11appR_apply (ρ : P11CVec n) :
    p11appR n ρ = Fin.append (0 : P11CVec n) ρ := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · simp [p11appR, Fin.append_left]
  · rw [Fin.append_right]
    show p11appR n ρ (Fin.natAdd n a) = ρ a
    rw [p11appR, ContinuousLinearMap.pi_apply, Fin.addCases_right]
    rfl

theorem append_eq_add (J ρ : P11CVec n) :
    (Fin.append J ρ : P11CVec (n+n)) = Fin.append J 0 + p11appR n ρ := by
  rw [p11appR_apply]
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;> simp [Fin.append_left]

theorem p11appR_single (a : Fin n) :
    p11appR n (Pi.single a 1) = Pi.single (Fin.natAdd n a) 1 := by
  rw [p11appR_apply]
  funext j
  refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · simp only [Fin.append_left, Pi.zero_apply, Pi.single_apply]
    rw [eq_comm]
    split_ifs with h
    · have := congrArg Fin.val h
      simp at this
      omega
    · rfl
  · simp [Fin.append_right, Pi.single_apply, Fin.natAdd_inj]

/-- The `ρ`-slice derivative of `Z` is the `natAdd` coordinate derivative. -/
theorem fderiv_append_slice {Z : P11CVec (n+n) → ℂ} {J ρ : P11CVec n}
    (hZ : DifferentiableAt ℂ Z (Fin.append J ρ)) (a : Fin n) :
    fderiv ℂ (fun ρ : P11CVec n => Z (Fin.append J ρ)) ρ (Pi.single a 1) =
      fderiv ℂ Z (Fin.append J ρ) (Pi.single (Fin.natAdd n a) 1) := by
  have hφ : HasFDerivAt (fun ρ : P11CVec n => (Fin.append J ρ : P11CVec (n+n)))
      (p11appR n) ρ := by
    have h := (p11appR n).hasFDerivAt (x := ρ)
    have h2 := h.const_add (Fin.append J (0 : P11CVec n) : P11CVec (n+n))
    convert h2 using 1
    funext x
    exact append_eq_add J x
  have := hZ.hasFDerivAt.comp ρ hφ
  have h3 := congrArg (fun L => L (Pi.single a 1)) this.fderiv
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at h3
  rw [p11appR_single] at h3
  exact h3

end SlowDerivative

end KAM.Planetary

end
