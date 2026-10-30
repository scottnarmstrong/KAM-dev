/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The vertex inequality for exponentials of linear forms

For `|y_i| ≤ ρ` and real `a`, `exp(-Σ a_i y_i)` is a convex combination of the vertex values
`exp(ρ Σ a_i σ_i)`, `σ ∈ {±1}ⁿ`, with the product weights `Λ_σ(y) = Π_i (1 - σ_i y_i/ρ)/2`.
Consequently a nonnegative combination of such exponentials is at most its maximum over the
vertices (`vertex_sum_le`). This is the convexity argument of design study §2.1 (P1).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp

open Finset

/-- `±1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The vertex weight in one coordinate. -/
def lam1 (ρ t : ℝ) (b : Bool) : ℝ := (1 - sgn b * t / ρ) / 2

theorem lam1_nonneg {ρ t : ℝ} (hρ : 0 < ρ) (ht : |t| ≤ ρ) (b : Bool) : 0 ≤ lam1 ρ t b := by
  have h := abs_le.mp ht
  have h1 : t / ρ ≤ 1 := by rw [div_le_one hρ]; exact h.2
  have h2 : -1 ≤ t / ρ := by rw [le_div_iff₀ hρ]; linarith [h.1]
  unfold lam1 sgn
  cases b <;> simp [neg_div] <;> linarith

theorem lam1_sum (ρ t : ℝ) : lam1 ρ t true + lam1 ρ t false = 1 := by
  unfold lam1 sgn; simp; ring

/-- One coordinate: `exp(-a y) ≤ Σ_b λ_b exp(ρ a σ_b)`. -/
theorem exp_le_vertex1 {ρ : ℝ} (hρ : 0 < ρ) (a t : ℝ) (ht : |t| ≤ ρ) :
    Real.exp (-(a * t)) ≤ lam1 ρ t true * Real.exp (ρ * (a * sgn true)) +
      lam1 ρ t false * Real.exp (ρ * (a * sgn false)) := by
  have h0t := lam1_nonneg hρ ht true
  have h0f := lam1_nonneg hρ ht false
  have hs := lam1_sum ρ t
  have hconv := convexOn_exp.2 (Set.mem_univ (ρ * (a * sgn true)))
    (Set.mem_univ (ρ * (a * sgn false))) h0t h0f hs
  have hpt : lam1 ρ t true • (ρ * (a * sgn true)) + lam1 ρ t false • (ρ * (a * sgn false)) =
      -(a * t) := by
    unfold lam1 sgn
    simp only [smul_eq_mul, if_true]
    simp
    field_simp
    ring
  rw [hpt] at hconv
  simpa [smul_eq_mul] using hconv

/-- The weights of all vertices sum to one. -/
theorem prod_lam_sum {n : ℕ} (ρ : ℝ) (y : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, ∏ i, lam1 ρ (y i) (σ i) = 1 := by
  have := Finset.prod_univ_sum (fun i : Fin n => (Finset.univ : Finset Bool))
    (fun i b => lam1 ρ (y i) b)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [lam1_sum]

/-- `exp(-Σ a_i y_i) ≤ Σ_σ Λ_σ(y) exp(ρ Σ a_i σ_i)`. -/
theorem exp_le_vertex {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (a y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ ρ) :
    Real.exp (-∑ i, a i * y i) ≤
      ∑ σ : Fin n → Bool, (∏ i, lam1 ρ (y i) (σ i)) *
        Real.exp (ρ * ∑ i, a i * sgn (σ i)) := by
  have hprod : Real.exp (-∑ i, a i * y i) = ∏ i, Real.exp (-(a i * y i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have hle : ∏ i, Real.exp (-(a i * y i)) ≤
      ∏ i, ∑ b : Bool, lam1 ρ (y i) b * Real.exp (ρ * (a i * sgn b)) := by
    refine Finset.prod_le_prod₀ (fun i _ => Real.exp_nonneg _) (fun i _ => ?_)
    rw [Fintype.sum_bool]
    exact exp_le_vertex1 hρ (a i) (y i) (hy i)
  have hexp := Finset.prod_univ_sum (fun i : Fin n => (Finset.univ : Finset Bool))
    (fun i b => lam1 ρ (y i) b * Real.exp (ρ * (a i * sgn b)))
  rw [Fintype.piFinset_univ] at hexp
  rw [hprod]
  refine hle.trans (hexp.le.trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- A nonnegative combination of exponentials is bounded by its largest vertex value, in the form
needed for certified bounds: if every vertex sum is at most `B`, so is the value at `y`. -/
theorem vertex_sum_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ j, 0 ≤ c j) (a : ι → Fin n → ℝ) (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ ρ) {B : ℝ}
    (hB : ∀ σ : Fin n → Bool, ∑ j ∈ s, c j * Real.exp (ρ * ∑ i, a j i * sgn (σ i)) ≤ B) :
    ∑ j ∈ s, c j * Real.exp (-∑ i, a j i * y i) ≤ B := by
  have h1 : ∀ j, c j * Real.exp (-∑ i, a j i * y i) ≤ ∑ σ : Fin n → Bool,
      (∏ i, lam1 ρ (y i) (σ i)) * (c j * Real.exp (ρ * ∑ i, a j i * sgn (σ i))) := fun j => by
    have := mul_le_mul_of_nonneg_left (exp_le_vertex hρ (a j) y hy) (hc j)
    refine this.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ j ∈ s, c j * Real.exp (-∑ i, a j i * y i)
      ≤ ∑ j ∈ s, ∑ σ : Fin n → Bool, (∏ i, lam1 ρ (y i) (σ i)) *
          (c j * Real.exp (ρ * ∑ i, a j i * sgn (σ i))) := Finset.sum_le_sum fun j _ => h1 j
    _ = ∑ σ : Fin n → Bool, (∏ i, lam1 ρ (y i) (σ i)) *
          ∑ j ∈ s, c j * Real.exp (ρ * ∑ i, a j i * sgn (σ i)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
    _ ≤ ∑ σ : Fin n → Bool, (∏ i, lam1 ρ (y i) (σ i)) * B := by
        refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hB σ) ?_
        exact Finset.prod_nonneg fun i _ => lam1_nonneg hρ (hy i) _
    _ = B := by rw [← Finset.sum_mul, prod_lam_sum, one_mul]

end KAM.CertificateSharp
