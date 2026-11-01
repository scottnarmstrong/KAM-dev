/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieMain

/-!
# Numerical lemmas for the `𝔚⁺`-estimates of the flow (blueprint-W `bpW:w3:flow` (iii))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

Real-number and Banach-space-valued summation lemmas, independent of the Lie series itself:
`lie_geom_bound`, `lie_geom_bound_D`, `lie_tail_one`, `lie_tail_two` (the tails
`Σ_{k ≥ 1} z_k` with `‖z_k‖ ≤ q^k ‖w‖` resp. `(2k+1) q^k`), `lie_step_A`, `lie_step_B` (the
step of the recursion for sums over `a + b + c = k` of vectors, resp. of operators) and
`lie_perx_D` (the three-term algebra of the derivative step).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

section Numeric

variable {C : ℝ}

theorem lie_geom_bound (t r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (k : ℕ) :
    |t| ^ k * (birkLieM k * C ^ k * r ^ (2 * k + 1)) ≤ (2 * |t| * C * r ^ 2) ^ k * r := by
  have hm := birkLieM_le_pow k
  have h0 := birkLieM_nonneg k
  calc |t| ^ k * (birkLieM k * C ^ k * r ^ (2 * k + 1))
      ≤ |t| ^ k * (2 ^ k * C ^ k * r ^ (2 * k + 1)) := by gcongr
    _ = (2 * |t| * C * r ^ 2) ^ k * r := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring

theorem lie_geom_bound_D (t r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (k : ℕ) :
    |t| ^ k * ((2 * k + 1) * birkLieM k * C ^ k * r ^ (2 * k)) ≤
      (2 * k + 1) * (2 * |t| * C * r ^ 2) ^ k := by
  have hm := birkLieM_le_pow k
  have h0 := birkLieM_nonneg k
  calc |t| ^ k * ((2 * k + 1) * birkLieM k * C ^ k * r ^ (2 * k))
      ≤ |t| ^ k * ((2 * k + 1) * 2 ^ k * C ^ k * r ^ (2 * k)) := by gcongr
    _ = (2 * k + 1) * (2 * |t| * C * r ^ 2) ^ k := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring

variable {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]

theorem lie_tail_one {z : ℕ → G} (t r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hq : 2 * |t| * C * r ^ 2 ≤ 1 / 10)
    (hz : ∀ k : ℕ, ‖z (k + 1)‖ ≤ (2 * |t| * C * r ^ 2) ^ (k + 1) * r) :
    Summable (fun k => z (k + 1)) ∧ ‖∑' k, z (k + 1)‖ ≤ 3 * |t| * C * r ^ 3 := by
  have h0 : 0 ≤ 2 * |t| * C * r ^ 2 := by positivity
  have hg := summable_geometric_of_lt_one h0 (by linarith)
  have hg1 : Summable fun k : ℕ => (2 * |t| * C * r ^ 2) ^ (k + 1) * r :=
    ((summable_nat_add_iff (f := fun k : ℕ => (2 * |t| * C * r ^ 2) ^ k) 1).2 hg).mul_right _
  have hs1n : Summable fun k => ‖z (k + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hz hg1
  refine ⟨hs1n.of_norm, ?_⟩
  refine (norm_tsum_le_tsum_norm hs1n).trans ?_
  refine (Summable.tsum_le_tsum hz hs1n hg1).trans ?_
  rw [tsum_mul_right]
  have := (geom_sums _ h0 hq).2.1
  calc (∑' k : ℕ, (2 * |t| * C * r ^ 2) ^ (k + 1)) * r
      ≤ 10 / 9 * (2 * |t| * C * r ^ 2) * r := mul_le_mul_of_nonneg_right this hr
    _ ≤ 3 * |t| * C * r ^ 3 := by
      have : 0 ≤ |t| * C * r ^ 3 := by positivity
      nlinarith

theorem lie_tail_two {z : ℕ → G} (t r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hq : 2 * |t| * C * r ^ 2 ≤ 1 / 10)
    (hz : ∀ k : ℕ, ‖z (k + 1)‖ ≤
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * |t| * C * r ^ 2) ^ (k + 1)) :
    Summable (fun k => z (k + 1)) ∧ ‖∑' k, z (k + 1)‖ ≤ 10 * |t| * C * r ^ 2 := by
  have h0 : 0 ≤ 2 * |t| * C * r ^ 2 := by positivity
  have hq1 : 2 * |t| * C * r ^ 2 < 1 := by linarith
  have hsum : Summable fun k : ℕ => (2 * ((k + 1 : ℕ) : ℝ) + 1) *
      (2 * |t| * C * r ^ 2) ^ (k + 1) := by
    have hs : Summable fun k : ℕ => ((k : ℝ)) * (2 * |t| * C * r ^ 2) ^ k := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1
        (r := 2 * |t| * C * r ^ 2) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hq1)
    have hg : Summable fun k : ℕ => (2 * |t| * C * r ^ 2) ^ k :=
      summable_geometric_of_lt_one h0 hq1
    have h' := (summable_nat_add_iff 1).2 ((hs.mul_left 2).add hg)
    refine h'.congr fun k => ?_
    push_cast; ring
  have hs1n : Summable fun k => ‖z (k + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hz hsum
  refine ⟨hs1n.of_norm, ?_⟩
  refine (norm_tsum_le_tsum_norm hs1n).trans ?_
  refine (Summable.tsum_le_tsum hz hs1n hsum).trans ?_
  refine ((geom_sums _ h0 hq).2.2).trans ?_
  nlinarith

end Numeric

section Steps

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem norm_one_div_succ (k : ℕ) : ‖((1 : ℂ) / ((k : ℂ) + 1))‖ = 1 / ((k : ℝ) + 1) := by
  rw [norm_div, norm_one]
  congr 1
  have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem lie_step_A (k : ℕ) (C r : ℝ) (Y : (Fin 3 → ℕ) → G)
    (hY : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 k, ‖Y x‖ ≤
      C ^ (k + 1) * r ^ (2 * k + 3) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2))) :
    ‖((1 : ℂ) / ((k : ℂ) + 1)) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, Y x‖ ≤
      birkLieM (k + 1) * C ^ (k + 1) * r ^ (2 * k + 3) := by
  rw [norm_smul, norm_one_div_succ]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hY))
    (by positivity)).trans ?_
  rw [← mul_sum, ← birkLieM_succ' k]
  refine le_of_eq ?_
  field_simp

theorem lie_step_B (k : ℕ) (C r : ℝ) (Y : (Fin 3 → ℕ) → G)
    (hY : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 k, ‖Y x‖ ≤
      (2 * (k : ℝ) + 3) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2)) :
    ‖((1 : ℂ) / ((k : ℂ) + 1)) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, Y x‖ ≤
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * birkLieM (k + 1) * C ^ (k + 1) * r ^ (2 * (k + 1)) := by
  rw [norm_smul, norm_one_div_succ]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hY))
    (by positivity)).trans ?_
  rw [← sum_mul, ← sum_mul, ← mul_sum, ← birkLieM_succ' k]
  refine le_of_eq ?_
  push_cast
  rw [show 2 * (k + 1) = 2 * k + 2 by ring]
  field_simp
  ring

theorem lie_perx_D (k : ℕ) (x : Fin 3 → ℕ) (hx : x 0 + x 1 + x 2 = k)
    (C r a0 a1 a2 d0 d1 d2 : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (ua0 : a0 ≤ birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0 + 1))
    (ua1 : a1 ≤ birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1 + 1))
    (ua2 : a2 ≤ birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2 + 1))
    (ud0 : d0 ≤ (2 * (x 0 : ℝ) + 1) * birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0))
    (ud1 : d1 ≤ (2 * (x 1 : ℝ) + 1) * birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1))
    (ud2 : d2 ≤ (2 * (x 2 : ℝ) + 1) * birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2)) :
    C * (a1 * a2) * d0 + C * (a0 * a2) * d1 + C * (a0 * a1) * d2 ≤
      (2 * (k : ℝ) + 3) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2) := by
  have m0 := birkLieM_nonneg (x 0)
  have m1 := birkLieM_nonneg (x 1)
  have m2 := birkLieM_nonneg (x 2)
  have pC : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
    rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
  have pr0 : r ^ (2 * k + 2) = r ^ (2 * x 0) * r ^ (2 * x 1 + 1) * r ^ (2 * x 2 + 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have pr1 : r ^ (2 * k + 2) = r ^ (2 * x 0 + 1) * r ^ (2 * x 1) * r ^ (2 * x 2 + 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have pr2 : r ^ (2 * k + 2) = r ^ (2 * x 0 + 1) * r ^ (2 * x 1 + 1) * r ^ (2 * x 2) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have t0 : C * (a1 * a2) * d0 ≤
      (2 * (x 0 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2) := by
    rw [pC, pr0]
    calc _ ≤ C * ((birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1 + 1)) *
          (birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2 + 1))) *
          ((2 * (x 0 : ℝ) + 1) * birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0)) := by gcongr
      _ = _ := by ring
  have t1 : C * (a0 * a2) * d1 ≤
      (2 * (x 1 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2) := by
    rw [pC, pr1]
    calc _ ≤ C * ((birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0 + 1)) *
          (birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2 + 1))) *
          ((2 * (x 1 : ℝ) + 1) * birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1)) := by gcongr
      _ = _ := by ring
  have t2 : C * (a0 * a1) * d2 ≤
      (2 * (x 2 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2) := by
    rw [pC, pr2]
    calc _ ≤ C * ((birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0 + 1)) *
          (birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1 + 1))) *
          ((2 * (x 2 : ℝ) + 1) * birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2)) := by gcongr
      _ = _ := by ring
  have hs : ((x 0 : ℝ)) + x 1 + x 2 = k := by exact_mod_cast hx
  calc _ ≤ _ := add_le_add (add_le_add t0 t1) t2
    _ = (2 * (k : ℝ) + 3) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
        C ^ (k + 1) * r ^ (2 * k + 2) := by
      have : (2 * (x 0 : ℝ) + 1) + (2 * (x 1 : ℝ) + 1) + (2 * (x 2 : ℝ) + 1) =
        2 * (k : ℝ) + 3 := by linarith
      rw [← this]; ring

end Steps

end KAM.Wave

end
