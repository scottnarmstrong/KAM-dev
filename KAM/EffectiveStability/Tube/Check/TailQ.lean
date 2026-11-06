/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.TailRem
public import KAM.EffectiveStability.Tube.Witness.HalfPow

/-!
# Rational slot tables and tail sums for the remainder budget (T2-CONF, N9 (C))

The computable side of `hRem_bounds_rows`. For rational `b_min`, `b_max`, `r` and `s = n/2`:

* `slotHatQ`, `slotHatDuQ`, `slotHatPQ`: the hats of `TailMaj` in `ℚ`
  (`gbR q m = Π_{i<m}(q - i)/m!`, N4's `gbinom_ratCast`); `slotHat_ratCast` etc. identify their
  casts with the real hats;
* `tailQ G L`: a tail sum over `Fin 3` as a triple range sum in `ℚ`; `tailSum_ratCast` identifies
  its cast with N4's `tailSum`, also for `Function.update`d families (`updQ`).

The tables themselves are short-decimal literals checked against the hats in the kernel (the
instance); a table computed inside a tail sum would be re-evaluated at every term.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

/-- `binom(q, m) = Π_{i<m} (q - i) / m!` in `ℚ`. -/
def gbR (q : ℚ) (m : ℕ) : ℚ := (∏ i ∈ range m, (q - i)) / m.factorial

theorem gbR_cast (q : ℚ) (m : ℕ) : ((gbR q m : ℚ) : ℝ) = gbinom (q : ℝ) m :=
  (gbinom_ratCast q m).symm

/-- The rational `slotHat` at `s = n/2`. -/
def slotHatQ (L : ℕ) (bmin bmax r : ℚ) (n m : ℕ) : ℚ :=
  if m ≤ L then |gbR ((n : ℚ) / 2) m| * (r / bmin) ^ m
  else |gbR ((n : ℚ) / 2) (L + 1)| * (r / (bmin - r)) ^ (L + 1) * ((bmax + r) / bmax) ^ 9

/-- The rational `slotHatDu` at `s = n/2`. -/
def slotHatDuQ (L : ℕ) (bmin bmax r : ℚ) (n m : ℕ) : ℚ :=
  if m ≤ L then (m : ℚ) * |gbR ((n : ℚ) / 2) m| * r ^ (m - 1) / bmin ^ m
  else |(n : ℚ) / 2| * |gbR ((n : ℚ) / 2 - 1) L| * r ^ L / (bmin - r) ^ (L + 1) *
    ((bmax + r) / bmax) ^ 9

/-- The rational `slotHatP` at `s = n/2`. -/
def slotHatPQ (L : ℕ) (bmin bmax r : ℚ) (n m : ℕ) : ℚ :=
  if m ≤ L then |(n : ℚ) / 2| * |gbR ((n : ℚ) / 2 - 1) m| * r ^ m / bmin ^ (m + 1)
  else |(n : ℚ) / 2| * |gbR ((n : ℚ) / 2 - 1) (L + 1)| * r ^ (L + 1) / (bmin - r) ^ (L + 2) *
    ((bmax + r) / bmax) ^ 9

section Cast

variable (L : ℕ) (bmin bmax r : ℚ) (n m : ℕ)

theorem half_cast : ((n : ℝ) / 2) = (((n : ℚ) / 2 : ℚ) : ℝ) := by push_cast; ring

theorem half_sub_one_cast : ((n : ℝ) / 2 - 1) = (((n : ℚ) / 2 - 1 : ℚ) : ℝ) := by push_cast; ring

theorem slotHat_ratCast :
    slotHat ((n : ℝ) / 2) L bmin bmax r m = ((slotHatQ L bmin bmax r n m : ℚ) : ℝ) := by
  unfold slotHat slotHatQ
  rw [half_cast n]
  split_ifs <;> push_cast [gbR_cast] <;> ring

theorem slotHatDu_ratCast :
    slotHatDu ((n : ℝ) / 2) L bmin bmax r m = ((slotHatDuQ L bmin bmax r n m : ℚ) : ℝ) := by
  unfold slotHatDu slotHatDuQ
  rw [half_sub_one_cast n, half_cast n]
  split_ifs <;> push_cast [gbR_cast] <;> ring

theorem slotHatP_ratCast :
    slotHatP ((n : ℝ) / 2) L bmin bmax r m = ((slotHatPQ L bmin bmax r n m : ℚ) : ℝ) := by
  unfold slotHatP slotHatPQ
  rw [half_sub_one_cast n, half_cast n]
  split_ifs <;> push_cast [gbR_cast] <;> ring

end Cast

/-! ### Tail sums in `ℚ` -/

/-- A tail sum over `Fin 3` as a triple range sum in `ℚ`. -/
def tailQ (G : Fin 3 → ℕ → ℚ) (L : ℕ) : ℚ :=
  ∑ a ∈ range (L + 2), ∑ b ∈ range (L + 2), ∑ c ∈ range (L + 2),
    if L < a + b + c then G 0 a * G 1 b * G 2 c else 0

theorem tailSum_ratCast (G : Fin 3 → ℕ → ℚ) (L : ℕ) :
    tailSum (fun j m => ((G j m : ℚ) : ℝ)) L = ((tailQ G L : ℚ) : ℝ) := by
  rw [tailSum_fin3, tailQ]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- A slot family with slot `i` replaced, in `ℚ`. -/
def updQ (G : Fin 3 → ℕ → ℚ) (i : Fin 3) (H : ℕ → ℚ) : Fin 3 → ℕ → ℚ :=
  fun j m => if j = i then H m else G j m

theorem update_ratCast (G : Fin 3 → ℕ → ℚ) (i : Fin 3) (H : ℕ → ℚ) :
    Function.update (fun j m => ((G j m : ℚ) : ℝ)) i (fun m => ((H m : ℚ) : ℝ)) =
      fun j m => ((updQ G i H j m : ℚ) : ℝ) := by
  funext j m
  by_cases h : j = i
  · subst h; simp [updQ]
  · simp [updQ, h]

end KAM.EffectiveStability.Tube

end
