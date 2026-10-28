/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Cutoff
public import KAM.Planetary.MaximalStep.Homological

/-!
# Coefficients of the cutoff (P11A-C8, `stepP:p11a:cs-cutoff`)

The cutoff `R_* = p11Cutoff T R` is affine in the action: `R_* = R_{*0} + R_{*1} · η` with
`R_{*0} = T_T [R(·, 0)]` and `R_{*1,i} = T_T [∂_{η_i} R(·, 0)]`. This file proves the affine
decomposition for parameters in `B` (the decomposition cannot hold for `b ∉ B`, where `R` is
unconstrained), the angle-class, trigonometric-polynomial and sup-norm facts consumed by
`homological_maximal`, and reality of the coefficients.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

/-- The zeroth-order coefficient family `R(θ, 0, b)`. -/
def stepF0 (R : P11Family n → ℂ) (u : P11CVec n × P11CVec n) : ℂ := R ((u.1, 0), u.2)

/-- The first-order coefficient family `∂_{η_i} R(θ, 0, b)`. -/
def stepF1 (R : P11Family n → ℂ) (i : Fin n) (u : P11CVec n × P11CVec n) : ℂ :=
  fderiv ℂ (fun η => R ((u.1, η), u.2)) 0 (Pi.single i 1)

theorem coeff_add_sum {b : P11CVec n} {f : P11CVec n × P11CVec n → ℂ}
    {g : Fin n → P11CVec n × P11CVec n → ℂ} (c : Fin n → ℂ)
    (hf : Continuous fun x : Fin n → ℝ => f (fun j => (x j : ℂ), b))
    (hg : ∀ i, Continuous fun x : Fin n → ℝ => g i (fun j => (x j : ℂ), b)) (k : Fin n → ℤ) :
    KAM.Weighted.coeff (fun u => f u + ∑ i, c i * g i u) b k =
      KAM.Weighted.coeff f b k + ∑ i, c i * KAM.Weighted.coeff (g i) b k := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
  have hint : ∀ f' : P11CVec n × P11CVec n → ℂ,
      Continuous (fun x : Fin n → ℝ => f' (fun j => (x j : ℂ), b)) →
      IntegrableOn (fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
        f' (fun j => (x j : ℂ), b)) (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1) :=
    fun f' h => KAM.integrableOn_unitCube_of_continuous (hchar.smul h)
  unfold KAM.Weighted.coeff KAM.torusCoeffW KAM.torusAverage
  have e : (fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
      (f (fun j => (x j : ℂ), b) + ∑ i, c i * g i (fun j => (x j : ℂ), b))) =
      fun x => KAM.character (-k) (fun j => (x j : ℂ)) • f (fun j => (x j : ℂ), b) +
        ∑ i, c i * (KAM.character (-k) (fun j => (x j : ℂ)) • g i (fun j => (x j : ℂ), b)) := by
    funext x
    simp only [smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [e]
  rw [integral_add (hint f hf) (integrable_finset_sum _ fun i _ =>
    (hint (g i) (hg i)).const_mul (c i)), integral_finset_sum _ fun i _ =>
    (hint (g i) (hg i)).const_mul (c i)]
  simp only [integral_const_mul]

theorem truncate_add_sum {T : ℝ} {b : P11CVec n} {f : P11CVec n × P11CVec n → ℂ}
    {g : Fin n → P11CVec n × P11CVec n → ℂ} (c : Fin n → ℂ)
    (hf : Continuous fun x : Fin n → ℝ => f (fun j => (x j : ℂ), b))
    (hg : ∀ i, Continuous fun x : Fin n → ℝ => g i (fun j => (x j : ℂ), b)) (θ : P11CVec n) :
    KAM.Weighted.truncate T (fun u => f u + ∑ i, c i * g i u) (θ, b) =
      KAM.Weighted.truncate T f (θ, b) + ∑ i, c i * KAM.Weighted.truncate T (g i) (θ, b) := by
  have hco : ∀ k, hmCut T (fun u => f u + ∑ i, c i * g i u) b k =
      hmCut T f b k + ∑ i, c i * hmCut T (g i) b k := by
    intro k
    by_cases h : KAM.Fourier.modeSize k ≤ T
    · simp only [hmCut, h, ite_true]
      exact coeff_add_sum c hf hg k
    · simp [hmCut, h]
  simp only [truncate_eq]
  rw [fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk),
    fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk)]
  have hg' : ∀ i, KAM.fourierSum (hmCut T (g i) b) θ =
      ∑ k ∈ hmModes n T, hmCut T (g i) b k * KAM.character k θ := fun i =>
    fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk) θ
  simp only [hg', hco, add_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring)

end KAM.Planetary

end
