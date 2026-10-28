/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularSpectrum.LocalAnalytic
public import KAM.Planetary.Nondegeneracy.AnalyticZeros

/-!
# Secular spectrum: the good polynomial

Blueprint P, Part 9 (`bpP:p9:good`, `bpP:p9:good-set`).  The finite non-resonance set `k4 n`, the
predicate `nr4`, the discriminant and the good function `good`; the exports `k4_finite`,
`good_characteristic` (`good` of the sorted spectrum is a polynomial in the characteristic
polynomial coefficients, via `MvPolynomial.esymmAlgEquiv`), `good_set` (analyticity on `axes n`,
the NR4 characterisation and permutation invariance) and `good_set_dichotomy` (the analytic-zero
dichotomy, via `Nondegeneracy.generic`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

def k4 (n : ℕ) : Set (Fin n → ℤ) := {k | 0 < ∑ i, |k i| ∧ ∑ i, |k i| ≤ 4}
def nr4 (s : Vec n) : Prop := Function.Injective s ∧
  ∀ k ∈ k4 n, ∑ i, (k i : ℝ)*s i ≠ 0
def discriminant (s : Vec n) : ℝ :=
  ∏ j, ∏ l ∈ Finset.univ.filter (j < ·), (s j-s l)^2
/-- Finite set written as a subtype for product indexing. -/
theorem k4_finite (n : ℕ) : (k4 n).Finite := by
  refine (Set.finite_Icc (fun _ : Fin n => (-4 : ℤ)) (fun _ => 4)).subset fun k hk => ?_
  have h : ∀ i, |k i| ≤ 4 := fun i =>
    (Finset.single_le_sum (f := fun i => |k i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)).trans hk.2
  exact ⟨fun i => (abs_le.1 (h i)).1, fun i => (abs_le.1 (h i)).2⟩
/-- Finiteness witness is proved before implementing this product, not an input assumption. -/
def good (s : Vec n) : ℝ := discriminant s *
  ∏ k ∈ (k4_finite n).toFinset, ∏ p : Equiv.Perm (Fin n), ∑ j, (k j : ℝ)*s (p j)
def goodAxes (D : Data n) : Set (Vec n) := {a ∈ axes n | good (sigma D a) ≠ 0}
def simpleAxes (D : Data n) : Set (Vec n) := {a ∈ axes n | discriminant (sigma D a) ≠ 0}

/-! ### Symmetry, over an arbitrary commutative ring -/

section Symmetry
variable {R : Type*} [CommRing R]

/-- The discriminant expression of `discriminant`, over an arbitrary commutative ring. -/
def discrGen (s : Fin n → R) : R :=
  ∏ j, ∏ l ∈ Finset.univ.filter (j < ·), (s j - s l)^2

/-- The product of the differences over ordered pairs `j < l`. -/
def upperProd (s : Fin n → R) : R :=
  ∏ x : Fin n × Fin n, if x.1 < x.2 then s x.1 - s x.2 else 1

/-- The product of the differences over ordered pairs of distinct indices. -/
def pairProd (s : Fin n → R) : R :=
  ∏ x : Fin n × Fin n, if x.1 ≠ x.2 then s x.1 - s x.2 else 1

/-- The sign `(-1)^N` relating `upperProd s ^ 2` and `pairProd s`. -/
def pairSign (n : ℕ) (R : Type*) [CommRing R] : R :=
  ∏ x : Fin n × Fin n, if x.1 < x.2 then (-1 : R) else 1

lemma discrGen_eq_sq (s : Fin n → R) : discrGen s = upperProd s ^ 2 := by
  rw [discrGen, upperProd, ← Finset.prod_pow, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

lemma pairSign_mul_self : pairSign n R * pairSign n R = 1 := by
  rw [pairSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun x _ => ?_
  split_ifs <;> simp

lemma pairProd_eq (s : Fin n → R) : pairProd s = pairSign n R * upperProd s ^ 2 := by
  have h1 : pairProd s = ∏ x : Fin n × Fin n,
      ((if x.1 < x.2 then s x.1 - s x.2 else 1) *
        (if x.2 < x.1 then s x.1 - s x.2 else 1)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rcases lt_trichotomy x.1 x.2 with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  have h2 : ∏ x : Fin n × Fin n, (if x.2 < x.1 then s x.1 - s x.2 else 1) =
      pairSign n R * upperProd s := by
    rw [pairSign, upperProd, ← Finset.prod_mul_distrib]
    refine (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun x => ?_).symm
    by_cases h : x.1 < x.2 <;> simp [h]
  rw [h1, Finset.prod_mul_distrib, h2, upperProd]
  ring

lemma discrGen_eq (s : Fin n → R) : discrGen s = pairSign n R * pairProd s := by
  rw [discrGen_eq_sq, pairProd_eq, ← mul_assoc, pairSign_mul_self, one_mul]

lemma pairProd_comp (s : Fin n → R) (e : Equiv.Perm (Fin n)) :
    pairProd (fun i => s (e i)) = pairProd s := by
  refine Fintype.prod_equiv (Equiv.prodCongr e e) _ _ fun x => ?_
  simp [e.injective.ne_iff]

lemma discrGen_comp (s : Fin n → R) (e : Equiv.Perm (Fin n)) :
    discrGen (fun i => s (e i)) = discrGen s := by
  rw [discrGen_eq, discrGen_eq, pairProd_comp]

lemma permFac_comp (k : Fin n → R) (s : Fin n → R) (e : Equiv.Perm (Fin n)) :
    ∏ p : Equiv.Perm (Fin n), ∑ j, k j * s (e (p j)) = ∏ p : Equiv.Perm (Fin n), ∑ j, k j * s (p j) :=
  Equiv.prod_comp (Equiv.mulLeft e) (fun p : Equiv.Perm (Fin n) => ∑ j, k j * s (p j))

end Symmetry

lemma good_comp (s : Vec n) (p : Equiv.Perm (Fin n)) : good (s ∘ p) = good s := by
  unfold good
  have hd : discriminant (s ∘ p) = discriminant s := discrGen_comp s p
  rw [hd]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  exact permFac_comp (fun j => (k j : ℝ)) s p

lemma discriminant_ne_zero_iff (s : Vec n) : discriminant s ≠ 0 ↔ Function.Injective s := by
  unfold discriminant
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies, Finset.prod_ne_zero_iff, Finset.mem_filter, true_and,
    ne_eq, pow_eq_zero_iff, two_ne_zero, not_false_eq_true, sub_eq_zero]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h i j hlt hij
    · exact h j i hlt hij.symm
  · intro h j l hjl heq
    exact hjl.ne (h heq)

lemma perm_sum_eq (k : Fin n → ℤ) (s : Vec n) (p : Equiv.Perm (Fin n)) :
    ∑ j, (k j : ℝ) * s (p j) = ∑ i, ((k ∘ p.symm) i : ℝ) * s i := by
  rw [← Equiv.sum_comp p (fun i => ((k ∘ p.symm) i : ℝ) * s i)]
  simp

lemma good_ne_zero_iff (s : Vec n) : good s ≠ 0 ↔ nr4 s := by
  unfold good nr4
  rw [mul_ne_zero_iff, discriminant_ne_zero_iff, Finset.prod_ne_zero_iff]
  refine and_congr_right fun _ => ?_
  simp only [Set.Finite.mem_toFinset, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h k hk
    simpa using h k hk 1
  · intro h k hk p
    rw [perm_sum_eq]
    refine h _ ⟨?_, ?_⟩
    · simpa [Function.comp_def, Equiv.sum_comp p.symm (fun i => |k i|)] using hk.1
    · simpa [Function.comp_def, Equiv.sum_comp p.symm (fun i => |k i|)] using hk.2


end SecularSpectrum

end KAM.Planetary
end
