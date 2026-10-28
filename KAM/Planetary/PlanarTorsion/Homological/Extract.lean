/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters

/-!
# Planar quartic torsion: coefficient extraction for quartic forms

Blueprint P, Part 11b (`bpP:p11b:homological`, step `ho-def`): a degree-four homogeneous
polynomial function of the phase `z` is a finite combination of the quartic monomials, and a
combination of the monomials with analytic coefficients is a `QuarticFamily`.  These are the
bookkeeping steps that turn the finite sum defining `p11c_chi` into a `QuarticFamily`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Polynomial
open scoped Polynomial

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

/-- The coordinate vector `(x₀, y₀, x₁, y₁)` of a phase point, as a complex vector. -/
def quarticVec (z : Phase 2) : Fin 4 → ℂ :=
  ![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)]

lemma quarticVec_smul (t : ℝ) (z : Phase 2) : quarticVec (t • z) = (t : ℂ) • quarticVec z := by
  ext i; fin_cases i <;> simp [quarticVec]

/-- Evaluating the monomial exponent product against the coordinate vector. -/
lemma quarticVec_prod (a : Fin 4 → Fin 5) (z : Phase 2) :
    ∏ i, quarticVec z i ^ (a i).val = (p11c_monomial (fun i => (a i).val) z : ℂ) := by
  simp [Fin.prod_univ_four, quarticVec, p11c_monomial]

/-- A degree-four homogeneous polynomial function is a finite combination of the quartic
monomials, with constant complex coefficients. -/
lemma quartic_extract (f : Phase 2 → ℂ) (P : MvPolynomial (Fin 4) ℂ)
    (hP : ∀ z, f z = MvPolynomial.eval (quarticVec z) P)
    (hh : ∀ (z : Phase 2) (t : ℝ), f (t • z) = (t : ℂ) ^ 4 * f z) :
    ∃ c : (Fin 4 → Fin 5) → ℂ, ∀ z, f z =
      ∑ a ∈ charIdx, c a * (p11c_monomial (fun i => (a i).val) z : ℂ) := by
  let φ : (Fin 4 → Fin 5) → (Fin 4 →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm
    (fun i => (a i).val)
  have hφ : Function.Injective φ := by
    intro a b h
    funext i
    apply Fin.ext
    have := congrArg (fun d : Fin 4 →₀ ℕ => d i) h
    simpa [φ] using this
  refine ⟨fun a => P.coeff (φ a), fun z => ?_⟩
  set v := quarticVec z with hv
  let Q : ℂ[X] := ∑ d ∈ P.support,
    C (P.coeff d * ∏ i, v i ^ d i) * X ^ (∑ i, d i)
  have hQ : ∀ t : ℝ, Q.eval (t : ℂ) = (t : ℂ) ^ 4 * f z := by
    intro t
    rw [← hh z t, hP, quarticVec_smul, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X, Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hv]
    ring
  let R : ℂ[X] := Q - C (f z) * X ^ 4
  have hR : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun t : ℝ => (t : ℂ))
      Complex.ofReal_injective fun t => ?_
    simp [R, hQ]; ring
  have h4 : R.coeff 4 = 0 := by rw [hR]; simp
  simp only [R, coeff_sub, Q, finsetSum_coeff, coeff_C_mul_X_pow] at h4
  have h5 : f z = ∑ d ∈ P.support.filter (fun d => ∑ i, d i = 4),
      P.coeff d * ∏ i, v i ^ d i := by
    rw [Finset.sum_filter]
    have : (∑ d ∈ P.support, if 4 = ∑ i, d i then
        P.coeff d * ∏ i, v i ^ d i else 0) = f z := by
      simpa [sub_eq_zero] using h4
    rw [← this]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [eq_comm]
  rw [h5]
  have himg : ∑ a ∈ charIdx, P.coeff (φ a) * (p11c_monomial (fun i => (a i).val) z : ℂ)
      = ∑ d ∈ charIdx.image φ, P.coeff d * ∏ i, v i ^ d i := by
    rw [Finset.sum_image fun a _ b _ h => hφ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← quarticVec_prod]
    simp [φ, hv]
  rw [himg]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_image]
    have hle : ∀ i, d i < 5 := fun i => by
      have := Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    refine ⟨fun i => ⟨d i, hle i⟩, ?_, ?_⟩
    · simp [charIdx, hd.2]
    · ext i; simp [φ]
  · intro d hd hnd
    rw [Finset.mem_image] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    have hs : ∑ i, φ a i = 4 := by
      simpa [charIdx, φ] using ha
    have : φ a ∉ P.support := fun h => hnd (Finset.mem_filter.2 ⟨h, hs⟩)
    simp [MvPolynomial.notMem_support_iff.1 this]

/-- A combination of the quartic monomials with analytic coefficients is a quartic family. -/
lemma quartic_of_coeffs {O : Set (Fin 2 → ℝ)} (R : (Fin 4 → Fin 5) → (Fin 2 → ℝ) → ℝ)
    (hR : ∀ b, AnalyticOnNhd ℝ (R b) O) :
    ∃ A : QuarticFamily O, ∀ I z, A.eval I z =
      ∑ b ∈ charIdx, R b I * p11c_monomial (fun i => (b i).val) z := by
  have han : ∀ (b : Fin 4 → Fin 5) (β : Fin 4 → ℕ),
      AnalyticOnNhd ℝ (fun I => if (fun i => (b i).val) = β then R b I else 0) O := by
    intro b β
    by_cases h : (fun i => (b i).val) = β
    · simpa only [h, ite_true] using hR b
    · simp only [h, ite_false]; exact fun _ _ => analyticAt_const
  refine ⟨⟨fun β I => ∑ b ∈ charIdx, if (fun i => (b i).val) = β then R b I else 0,
    fun β => Finset.analyticOnNhd_fun_sum _ fun b _ => han b β⟩, fun I z => ?_⟩
  show ∑ a ∈ charIdx, (∑ b ∈ charIdx, if (fun i => (b i).val) = (fun i => (a i).val) then
      R b I else 0) * p11c_monomial (fun i => (a i).val) z = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  have := charIdx_single (fun i => (b i).val) ⟨b, hb, rfl⟩ (R b I)
    (fun t => p11c_monomial t z)
  simp_rw [eq_comm (a := fun i => (b i).val)] at this ⊢
  exact this

end KAM.Planetary

end
