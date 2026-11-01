/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Count

/-!
# W7: real-number estimates for the zone sums (blueprint `bpW:w7:prep`, `bpW:w7:iter`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

The real-power estimates behind the choices of `j₀`: for `u = α̂/A_k ∈ (0, 1/27]` and
`J₀ = ⌈u^{-4/11}⌉` (resp. `⌈u^{-1/3}⌉`), bounds on `u J₀^{3/4}`, `J₀^{-2}`, `J₀`, `J₀^{-1/2}`; and
the comparison `|k|^e ≤ A_k^s` for `e ≤ 24 s`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

theorem pow_le_kAk_rpow {k : Fin 2 → ℤ} (hk : k ≠ 0) {e : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (he : (e : ℝ) ≤ 24 * s) : kAbs k ^ e ≤ kAk k ^ s := by
  have h1 := one_le_kAbs hk
  have h2 : kAbs k ^ (24 * s) ≤ kAk k ^ s := by
    have : kAbs k ^ (24 * s) = (kAbs k ^ 24) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (kAbs_pow_le_kAk k) hs
  calc kAbs k ^ e = kAbs k ^ (e : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ kAbs k ^ (24 * s) := Real.rpow_le_rpow_of_exponent_le h1 he
    _ ≤ _ := h2

theorem rpow_two_three_quarter_le : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 9 / 4 := by
  by_contra h
  push Not at h
  have h4 : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  rw [h4] at this
  norm_num at this

/-- `u ≤ 1/27` gives `u^{-p} ≥ 3` for `p ∈ [1/3, 4/11]`... in the two cases used. -/
theorem three_le_rpow_neg {u p : ℝ} (hu : 0 < u) (hu27 : u ≤ 1 / 27) (hp : 1 / 3 ≤ p) :
    3 ≤ u ^ (-p) := by
  have h1 : (1 / 27 : ℝ) ^ (-p) ≤ u ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hu hu27 (by linarith)
  refine le_trans ?_ h1
  have h27 : (1 / 27 : ℝ) = (3 : ℝ) ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [h27, ← Real.rpow_mul (by norm_num)]
  have : (3 : ℝ) ^ (1 : ℝ) ≤ 3 ^ (-(3 : ℝ) * -p) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  simpa using this

/-- Preparatory zones: the sum over `j` of the thresholds (blueprint `bpW:w7:prep`). -/
theorem prep_real_bound {u : ℝ} (hu : 0 < u) (hu27 : u ≤ 1 / 27) {aκ : ℝ} (haκ : 0 ≤ aκ)
    (J0 : ℕ) (hJ0 : J0 = ⌈u ^ (-(4 / 11 : ℝ))⌉₊) :
    3 ≤ J0 ∧
      u * (∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ)) +
        (J0 : ℝ) ^ (-(1 / 4 : ℝ))) + aκ * (J0 : ℝ) ^ (-(2 : ℝ)) ≤ (3 + aκ) * u ^ (8 / 11 : ℝ) := by
  set X : ℝ := u ^ (-(4 / 11 : ℝ)) with hX
  have hX3 : 3 ≤ X := three_le_rpow_neg hu hu27 (by norm_num)
  have hXpos : 0 < X := by linarith
  have hJX : X ≤ (J0 : ℝ) := by rw [hJ0]; exact Nat.le_ceil _
  have hJ2X : (J0 : ℝ) ≤ 2 * X := by
    rw [hJ0]
    have := Nat.ceil_lt_add_one hXpos.le
    linarith
  have hJ3 : 3 ≤ J0 := by
    have : (3 : ℝ) ≤ J0 := hX3.trans hJX
    exact_mod_cast this
  refine ⟨hJ3, ?_⟩
  have hJpos : (0 : ℝ) < J0 := by linarith
  -- the sum of the thresholds
  have hsum : ∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ)) +
      (J0 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 4 / 3 * (J0 : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : ∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ)) ≤
        ∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 1) ^ (-(1 / 4 : ℝ)) :=
      Finset.sum_le_sum fun j _ => Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith) (by norm_num)
    have h2 : (J0 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (((J0 - 3 : ℕ) : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
      have : ((J0 - 3 : ℕ) : ℝ) = (J0 : ℝ) - 3 := by
        rw [Nat.cast_sub hJ3]; norm_num
      rw [this]; linarith
    have h3 := sum_rpow_neg_quarter_le (J0 - 3 + 1)
    rw [Finset.sum_range_succ] at h3
    have h4 : ((J0 - 3 + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ (J0 : ℝ) ^ (3 / 4 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have : ((J0 - 3 + 1 : ℕ) : ℝ) = (J0 : ℝ) - 2 := by
        rw [Nat.cast_add, Nat.cast_sub hJ3]; push_cast; ring
      rw [this]; linarith
    linarith
  have hu0 := hu.le
  have hJ34 : u * (J0 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (3 / 4 : ℝ) * u ^ (8 / 11 : ℝ) := by
    have h1 : (J0 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 * X) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow hJpos.le hJ2X (by norm_num)
    rw [Real.mul_rpow (by norm_num) hXpos.le] at h1
    have h2 : X ^ (3 / 4 : ℝ) = u ^ (-(3 / 11 : ℝ)) := by
      rw [hX, ← Real.rpow_mul hu.le]; norm_num
    have h3 : u * u ^ (-(3 / 11 : ℝ)) = u ^ (8 / 11 : ℝ) := by
      have : u * u ^ (-(3 / 11 : ℝ)) = u ^ (1 : ℝ) * u ^ (-(3 / 11 : ℝ)) := by rw [Real.rpow_one]
      rw [this, ← Real.rpow_add hu]; norm_num
    calc u * (J0 : ℝ) ^ (3 / 4 : ℝ) ≤ u * (2 ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hu0
      _ = 2 ^ (3 / 4 : ℝ) * (u * u ^ (-(3 / 11 : ℝ))) := by rw [h2]; ring
      _ = _ := by rw [h3]
  have hJm2 : (J0 : ℝ) ^ (-(2 : ℝ)) ≤ u ^ (8 / 11 : ℝ) := by
    have h1 : (J0 : ℝ) ^ (-(2 : ℝ)) ≤ X ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hXpos hJX (by norm_num)
    have h2 : X ^ (-(2 : ℝ)) = u ^ (8 / 11 : ℝ) := by
      rw [hX, ← Real.rpow_mul hu.le]; norm_num
    rw [h2] at h1; exact h1
  have hc : 4 / 3 * (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 := by
    have := rpow_two_three_quarter_le; linarith
  have hupos : 0 ≤ u ^ (8 / 11 : ℝ) := Real.rpow_nonneg hu0 _
  calc u * (∑ j ∈ Finset.range (J0 - 3), ((j : ℝ) + 3) ^ (-(1 / 4 : ℝ)) +
        (J0 : ℝ) ^ (-(1 / 4 : ℝ))) + aκ * (J0 : ℝ) ^ (-(2 : ℝ))
      ≤ u * (4 / 3 * (J0 : ℝ) ^ (3 / 4 : ℝ)) + aκ * u ^ (8 / 11 : ℝ) := by
        gcongr
    _ = 4 / 3 * (u * (J0 : ℝ) ^ (3 / 4 : ℝ)) + aκ * u ^ (8 / 11 : ℝ) := by ring
    _ ≤ 4 / 3 * (2 ^ (3 / 4 : ℝ) * u ^ (8 / 11 : ℝ)) + aκ * u ^ (8 / 11 : ℝ) := by gcongr
    _ ≤ (3 + aκ) * u ^ (8 / 11 : ℝ) := by nlinarith

/-- Iteration zones: the choice `J₀ = ⌈u^{-1/3}⌉` (blueprint `bpW:w7:iter`). -/
theorem iter_real_bound {u : ℝ} (hu : 0 < u) (hu27 : u ≤ 1 / 27) (J0 : ℕ)
    (hJ0 : J0 = ⌈u ^ (-(1 / 3 : ℝ))⌉₊) :
    3 ≤ J0 ∧ (J0 : ℝ) * u ≤ 2 * u ^ (2 / 3 : ℝ) ∧ (J0 : ℝ) ^ (-(2 : ℝ)) ≤ u ^ (2 / 3 : ℝ) ∧
      (J0 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ u ^ (1 / 6 : ℝ) := by
  set X : ℝ := u ^ (-(1 / 3 : ℝ)) with hX
  have hX3 : 3 ≤ X := three_le_rpow_neg hu hu27 (by norm_num)
  have hXpos : 0 < X := by linarith
  have hJX : X ≤ (J0 : ℝ) := by rw [hJ0]; exact Nat.le_ceil _
  have hJ2X : (J0 : ℝ) ≤ 2 * X := by
    rw [hJ0]
    have := Nat.ceil_lt_add_one hXpos.le
    linarith
  have hJ3 : 3 ≤ J0 := by
    have : (3 : ℝ) ≤ J0 := hX3.trans hJX
    exact_mod_cast this
  have hJpos : (0 : ℝ) < J0 := by linarith
  have hu0 := hu.le
  refine ⟨hJ3, ?_, ?_, ?_⟩
  · have h3 : u * X = u ^ (2 / 3 : ℝ) := by
      have : u * X = u ^ (1 : ℝ) * u ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one, hX]
      rw [this, ← Real.rpow_add hu]; norm_num
    calc (J0 : ℝ) * u ≤ 2 * X * u := by gcongr
      _ = 2 * (u * X) := by ring
      _ = _ := by rw [h3]
  · have h1 : (J0 : ℝ) ^ (-(2 : ℝ)) ≤ X ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hXpos hJX (by norm_num)
    have h2 : X ^ (-(2 : ℝ)) = u ^ (2 / 3 : ℝ) := by
      rw [hX, ← Real.rpow_mul hu.le]; norm_num
    rw [h2] at h1; exact h1
  · have h1 : (J0 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ X ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hXpos hJX (by norm_num)
    have h2 : X ^ (-(1 / 2 : ℝ)) = u ^ (1 / 6 : ℝ) := by
      rw [hX, ← Real.rpow_mul hu.le]; norm_num
    rw [h2] at h1; exact h1

end KAM.Wave

end
