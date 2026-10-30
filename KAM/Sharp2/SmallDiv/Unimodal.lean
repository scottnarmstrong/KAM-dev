/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Sums of unimodal functions against integrals

`sum_range_le_integral_add` : if `f ≥ 0` on `[0, ∞)` is continuous, nondecreasing on `[0, c]`,
nonincreasing on `[c, ∞)` and integrable on `(0, ∞)`, then for every `L`
`∑_{i<L} f(i) ≤ ∫_{(0,∞)} f + f(c)`. Used for `f(t) = t^p e^{-βt}` in
`bp:p2s2sd:abel` (sum bounded by the Gamma integral plus the maximum).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace KAM.Sharp2

theorem sum_range_le_integral_add {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) (hcont : ContinuousOn f (Ici 0))
    (hmono : MonotoneOn f (Icc 0 c)) (hanti : AntitoneOn f (Ici c))
    (hint : IntegrableOn f (Ioi 0)) (L : ℕ) :
    ∑ i ∈ Finset.range L, f i ≤ (∫ t in Ioi (0 : ℝ), f t) + f c := by
  have hii : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable f volume a b := fun a b ha hb =>
    (hcont.mono fun t ht => by
      rcases ht with ht
      exact (le_min ha hb).trans (by simpa [Set.uIcc] using ht.1)).intervalIntegrable
  have hI : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, f t ≤ ∫ t in Ioi (0 : ℝ), f t := fun T hT => by
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => hf0 t ht.le))
      Ioc_subset_Ioi_self.eventuallySubset
  have hfc : 0 ≤ f c := hf0 c hc
  set m : ℕ := ⌊c⌋₊ with hm
  have hmc : (m : ℝ) ≤ c := Nat.floor_le hc
  have hcm : c < m + 1 := Nat.lt_floor_add_one c
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the monotone part
  have hA : ∀ a : ℕ, a ≤ m → ∑ i ∈ Finset.range a, f i ≤ ∫ t in (0 : ℝ)..a, f t := fun a ha => by
    have := MonotoneOn.sum_le_integral (f := f) (x₀ := 0) (a := a)
      (hmono.mono fun t ht => ⟨ht.1, ht.2.trans (by simpa using (Nat.cast_le.mpr ha).trans hmc)⟩)
    simpa using this
  by_cases hL : L ≤ m
  · exact ((hA L hL).trans (hI L (Nat.cast_nonneg L))).trans (le_add_of_nonneg_right hfc)
  · push Not at hL
    have hmfc : f m ≤ f c := hmono ⟨hm0, hmc⟩ ⟨hc, le_rfl⟩ hmc
    by_cases hL1 : L = m + 1
    · subst hL1
      rw [Finset.sum_range_succ]
      have := hA m le_rfl
      have := hI m hm0
      linarith
    · obtain ⟨a, rfl⟩ : ∃ a, L = m + 2 + a := ⟨L - (m + 2), by omega⟩
      rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ]
      -- the antitone tail
      have hT : ∑ j ∈ Finset.range a, f ((m + 2 : ℕ) + j : ℕ) ≤
          ∫ t in ((m : ℝ) + 1)..(m + 1 + a), f t := by
        have := AntitoneOn.sum_le_integral (f := f) (x₀ := (m : ℝ) + 1) (a := a)
          (hanti.mono fun t ht => le_trans hcm.le ht.1)
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) this
        congr 1
        push_cast
        ring
      -- the middle
      have hB : f m + f (m + 1 : ℕ) ≤ f c + ∫ t in (m : ℝ)..(m + 1), f t := by
        have hmin : ∀ t ∈ Icc (m : ℝ) (m + 1), min (f m) (f (m + 1 : ℕ)) ≤ f t := by
          intro t ht
          by_cases htc : t ≤ c
          · exact (min_le_left _ _).trans (hmono ⟨hm0, hmc⟩ ⟨hm0.trans ht.1, htc⟩ ht.1)
          · push Not at htc
            refine (min_le_right _ _).trans ?_
            exact hanti (Set.mem_Ici.mpr htc.le) (Set.mem_Ici.mpr (by push_cast; exact hcm.le))
              (by push_cast; exact ht.2)
        have hint2 : min (f m) (f (m + 1 : ℕ)) * 1 ≤ ∫ t in (m : ℝ)..(m + 1), f t := by
          have := intervalIntegral.integral_mono_on (by linarith : (m : ℝ) ≤ m + 1)
            (intervalIntegrable_const (c := min (f m) (f (m + 1 : ℕ))))
            (hii m (m + 1) hm0 (by linarith)) hmin
          simpa using this
        have hmx : f m + f (m + 1 : ℕ) = min (f m) (f (m + 1 : ℕ)) + max (f m) (f (m + 1 : ℕ)) := by
          rw [min_add_max]
        have hmax : max (f m) (f (m + 1 : ℕ)) ≤ f c := by
          refine max_le hmfc ?_
          exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by push_cast; exact hcm.le)) (by push_cast; exact hcm.le)
        linarith
      have h01 := intervalIntegral.integral_add_adjacent_intervals (hii 0 m le_rfl hm0)
        (hii m (m + 1) hm0 (by linarith))
      have h02 := intervalIntegral.integral_add_adjacent_intervals
        (hii 0 (m + 1) le_rfl (by linarith)) (hii (m + 1) (m + 1 + a) (by linarith) (by positivity))
      have hI2 := hI (m + 1 + a) (by positivity)
      have hA2 := hA m le_rfl
      push_cast at hB hT ⊢
      linarith

end KAM.Sharp2

end
