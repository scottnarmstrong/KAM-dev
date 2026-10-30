/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Rüssmann's counting lemma

A finite family of reals, pairwise `s`-separated and all of absolute value at least `t₀ > 0`,
satisfies `∑ x⁻² ≤ 2 (t₀⁻² + (s t₀)⁻¹)` (`KAM.sum_inv_sq_le_of_separated`). For positive points the
minimal element is removed inductively, using that the remaining points are at least `t + s`
and `(t+s)⁻² + (s (t+s))⁻¹ ≤ (s t)⁻¹`; the two signs are treated separately.
-/

public noncomputable section

namespace KAM

/-- Positive separated points: `∑ x⁻² ≤ t₀⁻² + (s t₀)⁻¹`. -/
theorem sum_inv_sq_le_of_separated_pos {s : ℝ} (hs : 0 < s) (T : Finset ℝ) :
    ∀ t₀ : ℝ, 0 < t₀ → (∀ x ∈ T, t₀ ≤ x) → (∀ x ∈ T, ∀ y ∈ T, x ≠ y → s ≤ |x - y|) →
      ∑ x ∈ T, (x ^ 2)⁻¹ ≤ (t₀ ^ 2)⁻¹ + 1 / (s * t₀) := by
  induction T using Finset.induction_on_min with
  | empty =>
    intro t₀ ht _ _
    simp only [Finset.sum_empty]
    positivity
  | insert a T hlt ih =>
    intro t₀ ht hge hsep
    have haT : a ∉ T := fun h => lt_irrefl _ (hlt a h)
    have ha : t₀ ≤ a := hge a (Finset.mem_insert_self _ _)
    have ha0 : 0 < a := lt_of_lt_of_le ht ha
    have hgeT : ∀ x ∈ T, a + s ≤ x := fun x hx => by
      have h1 := hsep x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)
        (hlt x hx).ne'
      rw [abs_of_pos (sub_pos.mpr (hlt x hx))] at h1
      linarith
    have h2 := ih (a + s) (by linarith) hgeT fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    rw [Finset.sum_insert haT]
    have key : ((a + s) ^ 2)⁻¹ + 1 / (s * (a + s)) ≤ 1 / (s * a) := by
      have hsa : 0 < a + s := by linarith
      rw [inv_eq_one_div, div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hs ha0, mul_pos (mul_pos hs ha0) hsa, mul_pos hs hsa,
        mul_pos (mul_pos hs hs) ha0, mul_pos (mul_pos hs hs) hsa]
    have h3 : 1 / (s * a) ≤ 1 / (s * t₀) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ha hs.le)
    have h4 : (a ^ 2)⁻¹ ≤ (t₀ ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ ht.le ha 2)
    linarith

/-- **Rüssmann's counting lemma** for finite sets of reals, pairwise `s`-separated, all of absolute
value at least `t₀`. -/
theorem sum_inv_sq_le_of_separated {s t₀ : ℝ} (hs : 0 < s) (ht : 0 < t₀) (T : Finset ℝ)
    (hge : ∀ x ∈ T, t₀ ≤ |x|) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → s ≤ |x - y|) :
    ∑ x ∈ T, (x ^ 2)⁻¹ ≤ 2 * ((t₀ ^ 2)⁻¹ + 1 / (s * t₀)) := by
  classical
  set P := T.filter (0 < ·) with hP
  set N := (T.filter (· < 0)).image (fun x => -x) with hN
  have hsplit : ∑ x ∈ T, (x ^ 2)⁻¹ ≤ ∑ x ∈ P, (x ^ 2)⁻¹ + ∑ x ∈ N, (x ^ 2)⁻¹ := by
    rw [hN, Finset.sum_image (fun x _ y _ h => neg_injective h)]
    have : ∑ x ∈ T, (x ^ 2)⁻¹ = ∑ x ∈ T.filter (0 < ·), (x ^ 2)⁻¹ +
        ∑ x ∈ T.filter (¬ 0 < ·), (x ^ 2)⁻¹ := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [this]
    refine add_le_add le_rfl (le_of_eq ?_)
    refine Finset.sum_congr ?_ fun x _ => by simp
    ext x
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨hx, lt_of_le_of_ne hx0 fun h => ?_⟩
      have := hge x hx
      rw [h, abs_zero] at this
      linarith
    · exact fun ⟨hx, h⟩ => ⟨hx, h.le⟩
  have hPb := sum_inv_sq_le_of_separated_pos hs P t₀ ht
    (fun x hx => by
      have hx' := Finset.mem_filter.mp hx
      have := hge x hx'.1
      rwa [abs_of_pos hx'.2] at this)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hNb := sum_inv_sq_le_of_separated_pos hs N t₀ ht
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hy' := Finset.mem_filter.mp hy
      have := hge y hy'.1
      rwa [abs_of_neg hy'.2] at this)
    (fun x hx y hy hxy => by
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      have := hsep x' (Finset.mem_filter.mp hx').1 y' (Finset.mem_filter.mp hy').1
        fun h => hxy (by rw [h])
      rwa [show -x' - -y' = -(x' - y') by ring, abs_neg])
  linarith

end KAM

end
