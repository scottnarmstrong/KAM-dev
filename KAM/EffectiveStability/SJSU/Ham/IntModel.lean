/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Rot
public import KAM.EffectiveStability.SJSU.Model.SJSU18O2
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `SJSU18-O2` as an integer polynomial, by degree (T2-CONF, N5a)

Every coefficient `c` of `sjsu18O2Terms` has `c · 10^E ∈ ℤ` (`sjsuTerms_ok`, kernel), so
`sjsu18O2 x = Re (10^{-E} Σ_d C_d(z, z̄))` with the integer polynomials `C_d` of degree `d` in `z`
(`sjsu18O2_eq_intChunks`), `z_j = (ξ_j - i η_j)/√2`. The rows of degree `d` are kept as chunks of at
most 256 rows of the six data parts (`sjsuIntChunks d`), which bounds the kernel's nesting when
`composeLin` groups them.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer row of a model row: the exponents `(a, a')` of `(z, z̄)` and `c · 10^E`. -/
def toIntRow (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ) : (Mon × Mon) × ℤ :=
  (((t.1, t.2.2.1, t.2.2.2.2.1), (t.2.1, t.2.2.2.1, t.2.2.2.2.2.1)),
    (t.2.2.2.2.2.2 * 10 ^ sjsuE).num)

/-- Split a list into blocks of at most `256` (the last block takes the rest after `k` blocks). -/
def blocks256 {α : Type*} : ℕ → List α → List (List α)
  | 0, l => [l]
  | k + 1, l => l.take 256 :: blocks256 k (l.drop 256)

theorem flatten_blocks256 {α : Type*} : ∀ (k : ℕ) (l : List α), (blocks256 k l).flatten = l
  | 0, l => by simp [blocks256]
  | k + 1, l => by simp [blocks256, flatten_blocks256 k, List.take_append_drop]

/-- The six data parts. -/
def sjsuParts : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)) :=
  [sjsu18O2Part0, sjsu18O2Part1, sjsu18O2Part2, sjsu18O2Part3, sjsu18O2Part4, sjsu18O2Part5]

theorem flatten_sjsuParts : sjsuParts.flatten = sjsu18O2Terms := by
  simp [sjsuParts, sjsu18O2Terms]

/-- The integer rows of `z`-degree `d`, in chunks of at most 256 rows. -/
def sjsuIntChunks (d : ℕ) : List (List ((Mon × Mon) × ℤ)) :=
  (sjsuParts.flatMap (blocks256 5)).map fun P => (P.map toIntRow).filter fun e => Mon.deg e.1.1 == d

/-- Every coefficient is an integer multiple of `10^{-E}`, and every `z`-degree is below `10`. -/
theorem sjsuTerms_ok : sjsu18O2Terms.all (fun t =>
    (t.2.2.2.2.2.2 * 10 ^ sjsuE).den == 1 && Mon.deg (toIntRow t).1.1 < 10) = true := by
  decide +kernel

/-- The summand of `sjsu18O2`. -/
def sjsuSummand (z : Fin 3 → ℂ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ) : ℂ :=
  ((t.2.2.2.2.2.2 : ℚ) : ℂ) * z 0 ^ t.1 * star (z 0) ^ t.2.1 * z 1 ^ t.2.2.1 *
    star (z 1) ^ t.2.2.2.1 * z 2 ^ t.2.2.2.2.1 * star (z 2) ^ t.2.2.2.2.2.1

theorem sjsuSummand_eq (z : Fin 3 → ℂ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)
    (ht : (t.2.2.2.2.2.2 * 10 ^ sjsuE).den = 1) :
    sjsuSummand z t = ((10 : ℂ) ^ sjsuE)⁻¹ *
      (((toIntRow t).2 : ℂ) *
        (mon (toIntRow t).1.1 z * mon (toIntRow t).1.2 (fun k => star (z k)))) := by
  have hq : ((t.2.2.2.2.2.2 * 10 ^ sjsuE).num : ℚ) = t.2.2.2.2.2.2 * 10 ^ sjsuE := by
    exact_mod_cast Rat.coe_int_num_of_den_eq_one ht
  have hc : ((t.2.2.2.2.2.2 : ℚ) : ℂ) =
      ((10 : ℂ) ^ sjsuE)⁻¹ * (((t.2.2.2.2.2.2 * 10 ^ sjsuE).num : ℤ) : ℂ) := by
    have : (((t.2.2.2.2.2.2 * 10 ^ sjsuE).num : ℤ) : ℂ) =
        (((t.2.2.2.2.2.2 * 10 ^ sjsuE : ℚ)) : ℂ) := by
      rw [← hq]; push_cast; rfl
    rw [this]
    push_cast
    field_simp
  simp only [sjsuSummand, toIntRow, mon]
  rw [hc]
  ring

/-- The sum over a row list with integral coefficients. -/
theorem sum_sjsuSummand (z : Fin 3 → ℂ) :
    ∀ l : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ), (∀ t ∈ l, (t.2.2.2.2.2.2 * 10 ^ sjsuE).den = 1) →
      (l.map (sjsuSummand z)).sum =
        ((10 : ℂ) ^ sjsuE)⁻¹ * bevalAt (l.map toIntRow) z (fun k => star (z k))
  | [], _ => by simp
  | t :: l, h => by
    rw [List.map_cons, List.sum_cons, sum_sjsuSummand z l (fun t ht => h t (by simp [ht])),
      sjsuSummand_eq z t (h t (by simp)), List.map_cons, bevalAt_cons, mul_add]

/-- Splitting a term list by the `z`-degree. -/
theorem bevalAt_eq_sum_filter_deg {R : Type*} [CommRing R] (w v : Fin 3 → R) :
    ∀ L : List ((Mon × Mon) × ℤ), (∀ e ∈ L, Mon.deg e.1.1 < 10) →
      bevalAt L w v = ∑ d ∈ Finset.range 10, bevalAt (L.filter fun e => Mon.deg e.1.1 == d) w v
  | [], _ => by simp
  | e :: L, h => by
    rw [bevalAt_cons, bevalAt_eq_sum_filter_deg w v L (fun e he => h e (by simp [he]))]
    have he : Mon.deg e.1.1 ∈ Finset.range 10 := Finset.mem_range.2 (h e (by simp))
    simp only [List.filter_cons]
    rw [← Finset.add_sum_erase _ _ he, ← Finset.add_sum_erase _ _ he, ← add_assoc]
    congr 1
    · simp [bevalAt_cons]
    · refine Finset.sum_congr rfl fun d hd => ?_
      have : (Mon.deg e.1.1 == d) = false := by
        simpa using (Finset.ne_of_mem_erase hd).symm
      simp [this]

theorem flatten_sjsuIntChunks (d : ℕ) :
    (sjsuIntChunks d).flatten =
      (sjsu18O2Terms.map toIntRow).filter fun e => Mon.deg e.1.1 == d := by
  have h1 : ∀ L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)),
      (L.map fun P => (P.map toIntRow).filter fun e => Mon.deg e.1.1 == d).flatten =
        (L.flatten.map toIntRow).filter fun e => Mon.deg e.1.1 == d := by
    intro L
    induction L with
    | nil => rfl
    | cons P L ih => simp [ih, List.filter_append]
  have h2 : ∀ L : List (List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)),
      (L.flatMap (blocks256 5)).flatten = L.flatten := by
    intro L
    induction L with
    | nil => rfl
    | cons P L ih => simp [List.flatMap_cons, ih, flatten_blocks256]
  rw [sjsuIntChunks, h1, h2, flatten_sjsuParts]

end KAM.EffectiveStability.SJSU

end
