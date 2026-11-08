/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Witness.BinomialProdDeriv

/-!
# Factored majorants of N4's binomial slots (T2-CONF, N9 (C), the remainder budget)

N4's slot majorants (`slotMaj`, `slotMajDu`, and `|s| · slotMaj (s - 1)` in `remBoundPhi`) contain
real powers `x^{s - m}` with `x ∈ [b_min, b_max]`. For `0 ≤ s ≤ 9` they factor as `b_max^s · hat`,
where the `hat`s involve only natural powers and the ratio `ρ = ((b_max + r)/b_max)^9`:

* `slotMaj_le_hat`: `slotMaj s L b_min b_max r m ≤ b_max^s · slotHat s L b_min b_max r m`;
* `slotMajDu_le_hat`, `slotMajP_le_hat`: the same for the `u`- and the `φ`-derivative slots.

So the remainder budgets of a term `T_n Π_j (B_j + u_j)^{n_j/2}` are `Π_j b_max,j^{n_j/2}` times
`tailSum`s of `n`-uniform tables (`tailSum_mul_slots`, `tailSum_update_mul_slots`).
`tailSum_fin3` writes a `tailSum` over `Fin 3` as a triple range sum (for kernel evaluation).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset Real

/-! ### Real powers -/

/-- `max(a^{s-k}, b^{s-k}) ≤ b^s / a^k` for `0 < a ≤ b`, `s ≥ 0`. -/
theorem max_rpow_sub_le {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) (k : ℕ) :
    max (a ^ (s - k)) (b ^ (s - k)) ≤ b ^ s / a ^ k := by
  have hb : 0 < b := ha.trans_le hab
  rw [Real.rpow_sub ha, Real.rpow_sub hb, Real.rpow_natCast, Real.rpow_natCast]
  have hak : 0 < a ^ k := pow_pos ha k
  refine max_le ?_ ?_
  · exact div_le_div_of_nonneg_right (Real.rpow_le_rpow ha.le hab hs) hak.le
  · exact div_le_div₀ (Real.rpow_nonneg hb.le s) le_rfl hak (pow_le_pow_left₀ ha.le hab k)

/-- `(b + r)^s ≤ b^s ((b + r)/b)^9` for `b > 0`, `r ≥ 0`, `s ≤ 9`. -/
theorem rpow_add_le_mul_ratio {b r s : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (hs9 : s ≤ 9) :
    (b + r) ^ s ≤ b ^ s * ((b + r) / b) ^ 9 := by
  have h1 : 1 ≤ (b + r) / b := by rw [le_div_iff₀ hb]; linarith
  have e : (b + r) ^ s = b ^ s * ((b + r) / b) ^ s := by
    rw [← Real.mul_rpow hb.le (by positivity)]
    congr 1
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hb.le s)
  have := Real.rpow_le_rpow_of_exponent_le h1 hs9
  rwa [show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this

/-- The remainder-slot power:
`max((b_min - r)^{s-k}, (b_max + r)^{s-k}) ≤ b_max^s ρ / (b_min - r)^k`. -/
theorem max_rpow_sub_le_rem {bmin bmax r s : ℝ} (hr0 : 0 ≤ r) (hr : r < bmin) (hb : bmin ≤ bmax)
    (hs0 : 0 ≤ s) (hs9 : s ≤ 9) (k : ℕ) :
    max ((bmin - r) ^ (s - k)) ((bmax + r) ^ (s - k)) ≤
      bmax ^ s * ((bmax + r) / bmax) ^ 9 / (bmin - r) ^ k := by
  have ha : 0 < bmin - r := by linarith
  have hbmax : 0 < bmax := by linarith
  refine (max_rpow_sub_le ha (by linarith) hs0 k).trans ?_
  exact div_le_div_of_nonneg_right (rpow_add_le_mul_ratio hbmax hr0 hs9)
    (pow_pos ha k).le

/-! ### The hats -/

/-- `slotMaj / b_max^s`, bounded: `|binom(s,m)| (r/b_min)^m` for `m ≤ L`, else the remainder
slot. -/
def slotHat (s : ℝ) (L : ℕ) (bmin bmax r : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then |gbinom s m| * (r / bmin) ^ m
  else |gbinom s (L + 1)| * (r / (bmin - r)) ^ (L + 1) * ((bmax + r) / bmax) ^ 9

/-- `slotMajDu / b_max^s`, bounded. -/
def slotHatDu (s : ℝ) (L : ℕ) (bmin bmax r : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then (m : ℝ) * |gbinom s m| * r ^ (m - 1) / bmin ^ m
  else |s| * |gbinom (s - 1) L| * r ^ L / (bmin - r) ^ (L + 1) * ((bmax + r) / bmax) ^ 9

/-- `|s| slotMaj (s - 1) / b_max^s`, bounded (the slot of `remBoundPhi`). -/
def slotHatP (s : ℝ) (L : ℕ) (bmin bmax r : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then |s| * |gbinom (s - 1) m| * r ^ m / bmin ^ (m + 1)
  else |s| * |gbinom (s - 1) (L + 1)| * r ^ (L + 1) / (bmin - r) ^ (L + 2) *
    ((bmax + r) / bmax) ^ 9

section Hats

variable {s bmin bmax r : ℝ} {L : ℕ}

theorem slotMaj_le_hat (hr0 : 0 ≤ r) (hr : r < bmin) (hb : bmin ≤ bmax) (hs0 : 0 ≤ s)
    (hs9 : s ≤ 9) (m : ℕ) :
    slotMaj s L bmin bmax r m ≤ bmax ^ s * slotHat s L bmin bmax r m := by
  have hbmin : 0 < bmin := lt_of_le_of_lt hr0 hr
  have hbs : 0 ≤ bmax ^ s := Real.rpow_nonneg (by linarith) s
  unfold slotMaj slotHat
  split_ifs with hm
  · have h := max_rpow_sub_le hbmin hb hs0 m
    calc |gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m)) * r ^ m
        ≤ |gbinom s m| * (bmax ^ s / bmin ^ m) * r ^ m := by gcongr
      _ = bmax ^ s * (|gbinom s m| * (r / bmin) ^ m) := by
          rw [div_pow]; field_simp
  · have h := max_rpow_sub_le_rem hr0 hr hb hs0 hs9 (L + 1)
    have ha : 0 < bmin - r := by linarith
    calc |gbinom s (L + 1)| * max ((bmin - r) ^ (s - ((L + 1 : ℕ) : ℝ)))
          ((bmax + r) ^ (s - ((L + 1 : ℕ) : ℝ))) * r ^ (L + 1)
        ≤ |gbinom s (L + 1)| * (bmax ^ s * ((bmax + r) / bmax) ^ 9 / (bmin - r) ^ (L + 1)) *
            r ^ (L + 1) := by gcongr
      _ = bmax ^ s * (|gbinom s (L + 1)| * (r / (bmin - r)) ^ (L + 1) *
            ((bmax + r) / bmax) ^ 9) := by
          have key : ∀ A g x c : ℝ, g * (x * c / A ^ (L + 1)) * r ^ (L + 1) =
              x * (g * (r / A) ^ (L + 1) * c) := by
            intro A g x c; rw [div_pow]; ring
          exact key _ _ _ _

theorem slotMajDu_le_hat (hr0 : 0 ≤ r) (hr : r < bmin) (hb : bmin ≤ bmax) (hs0 : 0 ≤ s)
    (hs9 : s ≤ 9) (m : ℕ) :
    slotMajDu s L bmin bmax r m ≤ bmax ^ s * slotHatDu s L bmin bmax r m := by
  have hbmin : 0 < bmin := lt_of_le_of_lt hr0 hr
  unfold slotMajDu slotHatDu
  split_ifs with hm
  · have h := max_rpow_sub_le hbmin hb hs0 m
    calc (m : ℝ) * |gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m)) * r ^ (m - 1)
        ≤ (m : ℝ) * |gbinom s m| * (bmax ^ s / bmin ^ m) * r ^ (m - 1) := by gcongr
      _ = bmax ^ s * ((m : ℝ) * |gbinom s m| * r ^ (m - 1) / bmin ^ m) := by ring
  · have e : s - 1 - (L : ℝ) = s - ((L + 1 : ℕ) : ℝ) := by push_cast; ring
    have h := max_rpow_sub_le_rem hr0 hr hb hs0 hs9 (L + 1)
    rw [e]
    calc |s| * (|gbinom (s - 1) L| * max ((bmin - r) ^ (s - ((L + 1 : ℕ) : ℝ)))
          ((bmax + r) ^ (s - ((L + 1 : ℕ) : ℝ))) * r ^ L)
        ≤ |s| * (|gbinom (s - 1) L| * (bmax ^ s * ((bmax + r) / bmax) ^ 9 /
            (bmin - r) ^ (L + 1)) * r ^ L) := by gcongr
      _ = bmax ^ s * (|s| * |gbinom (s - 1) L| * r ^ L / (bmin - r) ^ (L + 1) *
            ((bmax + r) / bmax) ^ 9) := by ring

theorem slotMajP_le_hat (hr0 : 0 ≤ r) (hr : r < bmin) (hb : bmin ≤ bmax) (hs0 : 0 ≤ s)
    (hs9 : s ≤ 9) (m : ℕ) :
    |s| * slotMaj (s - 1) L bmin bmax r m ≤ bmax ^ s * slotHatP s L bmin bmax r m := by
  have hbmin : 0 < bmin := lt_of_le_of_lt hr0 hr
  unfold slotMaj slotHatP
  split_ifs with hm
  · have e : s - 1 - (m : ℝ) = s - ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have h := max_rpow_sub_le hbmin hb hs0 (m + 1)
    rw [e]
    calc |s| * (|gbinom (s - 1) m| * max (bmin ^ (s - ((m + 1 : ℕ) : ℝ)))
          (bmax ^ (s - ((m + 1 : ℕ) : ℝ))) * r ^ m)
        ≤ |s| * (|gbinom (s - 1) m| * (bmax ^ s / bmin ^ (m + 1)) * r ^ m) := by gcongr
      _ = bmax ^ s * (|s| * |gbinom (s - 1) m| * r ^ m / bmin ^ (m + 1)) := by ring
  · have e : s - 1 - ((L + 1 : ℕ) : ℝ) = s - ((L + 2 : ℕ) : ℝ) := by push_cast; ring
    have h := max_rpow_sub_le_rem hr0 hr hb hs0 hs9 (L + 2)
    rw [e]
    calc |s| * (|gbinom (s - 1) (L + 1)| * max ((bmin - r) ^ (s - ((L + 2 : ℕ) : ℝ)))
          ((bmax + r) ^ (s - ((L + 2 : ℕ) : ℝ))) * r ^ (L + 1))
        ≤ |s| * (|gbinom (s - 1) (L + 1)| * (bmax ^ s * ((bmax + r) / bmax) ^ 9 /
            (bmin - r) ^ (L + 2)) * r ^ (L + 1)) := by gcongr
      _ = bmax ^ s * (|s| * |gbinom (s - 1) (L + 1)| * r ^ (L + 1) / (bmin - r) ^ (L + 2) *
            ((bmax + r) / bmax) ^ 9) := by ring

end Hats

/-! ### Tail sums -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A slotwise factor comes out of a tail sum. -/
theorem tailSum_mul_slots (c : ι → ℝ) (G : ι → ℕ → ℝ) (L : ℕ) :
    tailSum (fun j m => c j * G j m) L = (∏ j, c j) * tailSum G L := by
  simp only [tailSum, Finset.mul_sum, prod_mul_distrib]

theorem tailSum_update_mul_slots (c : ι → ℝ) (G : ι → ℕ → ℝ) (i : ι) (H : ℕ → ℝ) (L : ℕ) :
    tailSum (Function.update (fun j m => c j * G j m) i (fun m => c i * H m)) L =
      (∏ j, c j) * tailSum (Function.update G i H) L := by
  rw [← tailSum_mul_slots]
  congr 1
  funext j m
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- A tail sum over `Fin 3` as a triple range sum. -/
theorem tailSum_fin3 (G : Fin 3 → ℕ → ℝ) (L : ℕ) :
    tailSum G L = ∑ a ∈ range (L + 2), ∑ b ∈ range (L + 2), ∑ c ∈ range (L + 2),
      if L < a + b + c then G 0 a * G 1 b * G 2 c else 0 := by
  have hpi : ∀ F : (Fin 3 → ℕ) → ℝ, ∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => range (L + 2)), F p =
      ∑ a ∈ range (L + 2), ∑ b ∈ range (L + 2), ∑ c ∈ range (L + 2), F ![a, b, c] := by
    intro F
    rw [← Finset.sum_product', ← Finset.sum_product']
    refine Finset.sum_nbij' (fun p => ((p 0, p 1), p 2)) (fun t => ![t.1.1, t.1.2, t.2])
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Fintype.mem_piFinset] at hp
      simp [mem_product, hp 0, hp 1, hp 2]
    · intro t ht
      simp only [mem_product] at ht
      simp only [Fintype.mem_piFinset]
      intro j; fin_cases j <;> simp [ht.1.1, ht.1.2, ht.2]
    · intro p _; ext j; fin_cases j <;> rfl
    · intro t _; rfl
    · intro p _
      congr 1; ext j; fin_cases j <;> rfl
  have htail : tailSet (Fin 3) L = (Fintype.piFinset fun _ : Fin 3 => range (L + 2)).filter
      fun p => L < ∑ j, p j := by
    ext p
    simp only [tailSet, truncSet, mem_sdiff, mem_filter, Fintype.mem_piFinset, mem_range, not_and,
      not_le]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h
      push Not at h
      exact absurd (h2 (fun j => by
        have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_univ j)
        omega)) (not_lt.2 h)
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => h2⟩
  rw [tailSum, htail, Finset.sum_filter, hpi]
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

end KAM.EffectiveStability.Tube

end
