/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneF
public import KAM.Wave.Homological.LemmaOneBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex conjugation and the multiplier solve (`bpW:w4:lemma1` (i), step *Reality*)

* `homCoeff_conj`: if `v = \\bar u` at real points then `\\hat v_k = \\overline{\\hat u_{-k}}`;
* `homSolve_conj_real`: for scalar multipliers with `m'_k = \\overline{m_{-k}}`, at real points
  `\\overline{𝒮_m u} = 𝒮_{m'} v` whenever `v = \\bar u` there.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM MeasureTheory
open scoped ComplexConjugate

theorem homConj_character_real (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    starRingEnd ℂ (character k (fun j => (x j : ℂ))) = character (-k) (fun j => (x j : ℂ)) := by
  unfold character
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat,
    Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem homCoeff_conj {u v : (Fin 2 → ℂ) → ℂ}
    (hv : ∀ x : Fin 2 → ℝ, v (fun j => (x j : ℂ)) = starRingEnd ℂ (u (fun j => (x j : ℂ))))
    (k : Fin 2 → ℤ) : homCoeff v k = starRingEnd ℂ (homCoeff u (-k)) := by
  unfold homCoeff torusCoeffW torusAverage
  rw [← integral_conj]
  congr 1
  funext x
  simp only [smul_eq_mul, map_mul, hv x, Complex.conj_conj, neg_neg]
  rw [homConj_character_real k x]

theorem homSolve_conj_real {u v : (Fin 2 → ℂ) → ℂ}
    (hv : ∀ x : Fin 2 → ℝ, v (fun j => (x j : ℂ)) = starRingEnd ℂ (u (fun j => (x j : ℂ))))
    (m m' : (Fin 2 → ℤ) → ℂ) (hm' : ∀ k, m' k = starRingEnd ℂ (m (-k))) (x : Fin 2 → ℝ) :
    starRingEnd ℂ (homSolve (fun k => m k • ContinuousLinearMap.id ℂ ℂ) u (fun j => (x j : ℂ))) =
      homSolve (fun k => m' k • ContinuousLinearMap.id ℂ ℂ) v (fun j => (x j : ℂ)) := by
  unfold homSolve fourierSumVec
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin 2 → ℤ)).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, map_mul, homConj_character_real, neg_neg]
  rw [hm' k, homCoeff_conj hv k]

theorem conj_homInv (δ : ℝ) : starRingEnd ℂ (homInv δ) = homInv (-δ) := by
  unfold homInv
  rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  congr 1
  ring

theorem homPairZ_neg (k : Fin 2 → ℤ) (v : Fin 2 → ℝ) : homPairZ (-k) v = -homPairZ k v := by
  unfold homPairZ
  simp [Finset.sum_neg_distrib]

theorem homMultA0_conj (w : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    starRingEnd ℂ (homMultA0 w (-k)) = homMultA0 w k := by
  unfold homMultA0
  by_cases hk : k = 0
  · simp [hk]
  · have : -k ≠ 0 := neg_ne_zero.mpr hk
    rw [if_neg this, if_neg hk, conj_homInv]
    unfold homDelta0
    rw [homPairZ_neg]; simp

theorem homMultDp_conj (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) :
    starRingEnd ℂ (homMultDp w W (-k) j) = homMultDm w W k j := by
  unfold homMultDp homMultDm
  rw [conj_homInv]
  unfold homDeltaPlus homDeltaMinus
  rw [homPairZ_neg]; congr 1; ring

theorem homMultDm_conj (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) :
    starRingEnd ℂ (homMultDm w W (-k) j) = homMultDp w W k j := by
  unfold homMultDp homMultDm
  rw [conj_homInv]
  unfold homDeltaPlus homDeltaMinus
  rw [homPairZ_neg]; congr 1; ring

theorem homDP_conj (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    starRingEnd ℂ (homDP w W (-k) i j) = homDP' w W k i j := by
  unfold homDP homDP'
  rw [conj_homInv]
  unfold homDeltaP homDeltaP'
  rw [homPairZ_neg]; congr 1; ring

theorem homDP'_conj (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    starRingEnd ℂ (homDP' w W (-k) i j) = homDP w W k i j := by
  unfold homDP homDP'
  rw [conj_homInv]
  unfold homDeltaP homDeltaP'
  rw [homPairZ_neg]; congr 1; ring

theorem homDQ_conj (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    starRingEnd ℂ (homDQ w W (-k) i j) = homDQ w W k j i := by
  unfold homDQ
  by_cases h : k = 0 ∧ j = i
  · have h' : -k = 0 ∧ i = j := ⟨by simp [h.1], h.2.symm⟩
    rw [if_pos h', if_pos h]; simp
  · have h' : ¬ (-k = 0 ∧ i = j) := fun hh => h ⟨neg_eq_zero.mp hh.1, hh.2.symm⟩
    rw [if_neg h', if_neg h, conj_homInv]
    unfold homDeltaQ
    rw [homPairZ_neg]; congr 1; ring

end KAM.Wave
