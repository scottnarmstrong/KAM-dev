/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.GoodPolynomial

/-!
# Good axes: non-resonance of a perturbed bordered spectrum

Blueprint P, Part 10 (`stepP:p10:gp-nr`): if `σ` is within `e` of `(δ, 0)`, `δ` is non-resonant to
order four with gap `κ₀ > 4 e`, and the last entry of `σ` is negative, then `σ` is non-resonant to
order four.  The finite-minimum lemma `exists_gap` supplies `κ₀`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- A positive function on a finite set is bounded below by a positive constant. -/
lemma exists_gap {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ S, κ ≤ f x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨κ, hκ, h⟩ := ih fun x hx => hf x (Finset.mem_insert_of_mem hx)
    refine ⟨min κ (f a), lt_min hκ (hf a (Finset.mem_insert_self a S)), fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h x hx)

/-- `nr4` from the vanishing conditions on `k4`. -/
lemma nr4_of_forall {s : Vec n} (h : ∀ k ∈ k4 n, ∑ i, (k i : ℝ) * s i ≠ 0) : nr4 s := by
  refine ⟨fun i j hij => ?_, h⟩
  by_contra hne
  have hk : ∀ x, ((Pi.single i 1 - Pi.single j 1 : Fin n → ℤ) x) =
      (if x = i then 1 else 0) - (if x = j then 1 else 0) := fun x => by
    simp [Pi.single_apply]
  have hsum : ∑ x, |(Pi.single i 1 - Pi.single j 1 : Fin n → ℤ) x| = 2 := by
    rw [Finset.sum_eq_add i j hne]
    · simp [hk, Ne.symm hne, hne]
    · intro c _ hc
      simp [hk, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro h; exact absurd (Finset.mem_univ j) h
  refine h (Pi.single i 1 - Pi.single j 1) ⟨by rw [hsum]; norm_num, by rw [hsum]; norm_num⟩ ?_
  simp only [hk, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  simp [ite_mul, hij]

/-- `stepP:p10:gp-nr`. -/
lemma nr4_perturb {δ : Vec n} {σ : Vec (n+1)} {e κ0 : ℝ} (he : 0 ≤ e) (hκ : 4 * e < κ0)
    (hδ : ∀ k ∈ k4 n, κ0 ≤ |∑ i, (k i : ℝ) * δ i|)
    (hσ : ∀ i, |σ i - (Fin.snoc δ (0 : ℝ) : Vec (n+1)) i| ≤ e) (hneg : σ (Fin.last n) < 0) :
    nr4 σ := by
  refine nr4_of_forall fun k hk => ?_
  have hk2 : ∑ i, |(k i : ℝ)| ≤ 4 := by
    have : ((∑ i, |k i| : ℤ) : ℝ) ≤ 4 := by exact_mod_cast hk.2
    simpa [Int.cast_sum, Int.cast_abs] using this
  have hsum : ∑ i, |(k i : ℝ)| = ∑ l : Fin n, |(k l.castSucc : ℝ)| + |(k (Fin.last n) : ℝ)| :=
    Fin.sum_univ_castSucc _
  have hlast : |σ (Fin.last n)| ≤ e := by simpa using hσ (Fin.last n)
  rw [Fin.sum_univ_castSucc]
  by_cases hz : ∀ l : Fin n, k l.castSucc = 0
  · have hkl : k (Fin.last n) ≠ 0 := fun h0 => by
      have := hk.1
      rw [Fin.sum_univ_castSucc] at this
      simp [hz, h0] at this
    simp only [hz, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
    exact mul_ne_zero (by exact_mod_cast hkl) hneg.ne
  · push Not at hz
    obtain ⟨l0, hl0⟩ := hz
    set kh : Fin n → ℤ := fun l => k l.castSucc with hkh
    have hkh4 : kh ∈ k4 n := by
      have hpos : 0 < ∑ l, |kh l| :=
        Finset.sum_pos' (fun l _ => abs_nonneg _) ⟨l0, Finset.mem_univ _, abs_pos.2 hl0⟩
      refine ⟨hpos, ?_⟩
      have : ((∑ l, |kh l| : ℤ) : ℝ) ≤ 4 := by
        have h1 : ((∑ l, |kh l| : ℤ) : ℝ) = ∑ l : Fin n, |(k l.castSucc : ℝ)| := by
          simp [hkh, Int.cast_sum, Int.cast_abs]
        rw [h1]
        linarith [abs_nonneg (k (Fin.last n) : ℝ)]
      exact_mod_cast this
    have hd := hδ kh hkh4
    have hsum0 : ∑ l : Fin n, |(kh l : ℝ)| = ∑ l : Fin n, |(k l.castSucc : ℝ)| := rfl
    have hdiff : |(∑ l : Fin n, (k l.castSucc : ℝ) * σ l.castSucc + (k (Fin.last n) : ℝ) *
        σ (Fin.last n)) - ∑ l, (kh l : ℝ) * δ l| ≤ 4 * e := by
      have e1 : (∑ l : Fin n, (k l.castSucc : ℝ) * σ l.castSucc + (k (Fin.last n) : ℝ) *
          σ (Fin.last n)) - ∑ l, (kh l : ℝ) * δ l =
          ∑ l : Fin n, (kh l : ℝ) * (σ l.castSucc - δ l) + (k (Fin.last n) : ℝ) *
            σ (Fin.last n) := by
        rw [← sub_eq_zero]
        simp only [hkh, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have h1 : |∑ l : Fin n, (kh l : ℝ) * (σ l.castSucc - δ l)| ≤
          ∑ l : Fin n, |(kh l : ℝ)| * e := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        simpa using hσ l.castSucc
      have h2 : |(k (Fin.last n) : ℝ) * σ (Fin.last n)| ≤ |(k (Fin.last n) : ℝ)| * e := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlast (abs_nonneg _)
      rw [← Finset.sum_mul] at h1
      nlinarith
    intro h0
    rw [h0, zero_sub, abs_neg] at hdiff
    linarith

end Nondegeneracy
end KAM.Planetary
end
