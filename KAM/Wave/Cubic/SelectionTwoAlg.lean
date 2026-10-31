/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionTwoFinal

/-!
# Trilinearity and symmetry of the two-sided `T_c` (blueprint `bpW:w1:selection`, last sentence)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

Additivity and homogeneity in each slot of `KAM.Wave.waveSelSumZ` / `KAM.Wave.waveSelTwo`
(`waveSelSumZ_add_left`, …, `waveSelTwo_smul_left`, …), and symmetry when `c` is symmetric in its
first three indices (`waveSelSumZ_swap_left_mid`, `waveSelSumZ_swap_mid_right`,
`waveSelTwo_swap_*`).
The additivity statements assume summability of the guarded terms, which is supplied for every
`l ≠ 0` by `waveSel_twoSided`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The guarded term of `waveSelSumZ`. -/
def waveSelTermZ (c : ℤ → ℤ → ℤ → ℤ → ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) (t : ℤ × ℤ × ℤ) : ℂ :=
  if t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 then
    c t.1 t.2.1 t.2.2 l * (w t.1 * (w' t.2.1 * w'' t.2.2)) else 0

lemma waveSelSumZ_eq_tsum (c : ℤ → ℤ → ℤ → ℤ → ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) :
    waveSelSumZ c w w' w'' l = ∑' t, waveSelTermZ c w w' w'' l t := rfl

variable (c : ℤ → ℤ → ℤ → ℤ → ℂ) (l : ℤ)

theorem waveSelSumZ_smul_left (r : ℂ) (w w' w'' : ℤ → ℂ) :
    waveSelSumZ c (fun j => r * w j) w' w'' l = r * waveSelSumZ c w w' w'' l := by
  unfold waveSelSumZ
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  split_ifs <;> ring

theorem waveSelSumZ_smul_mid (r : ℂ) (w w' w'' : ℤ → ℂ) :
    waveSelSumZ c w (fun j => r * w' j) w'' l = r * waveSelSumZ c w w' w'' l := by
  unfold waveSelSumZ
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  split_ifs <;> ring

theorem waveSelSumZ_smul_right (r : ℂ) (w w' w'' : ℤ → ℂ) :
    waveSelSumZ c w w' (fun j => r * w'' j) l = r * waveSelSumZ c w w' w'' l := by
  unfold waveSelSumZ
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  split_ifs <;> ring

theorem waveSelSumZ_add_left (w v w' w'' : ℤ → ℂ)
    (hw : Summable (waveSelTermZ c w w' w'' l)) (hv : Summable (waveSelTermZ c v w' w'' l)) :
    waveSelSumZ c (fun j => w j + v j) w' w'' l =
      waveSelSumZ c w w' w'' l + waveSelSumZ c v w' w'' l := by
  rw [waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, ← Summable.tsum_add hw hv]
  refine tsum_congr fun t => ?_
  simp only [waveSelTermZ]
  split_ifs <;> ring

theorem waveSelSumZ_add_mid (w w' v w'' : ℤ → ℂ)
    (hw : Summable (waveSelTermZ c w w' w'' l)) (hv : Summable (waveSelTermZ c w v w'' l)) :
    waveSelSumZ c w (fun j => w' j + v j) w'' l =
      waveSelSumZ c w w' w'' l + waveSelSumZ c w v w'' l := by
  rw [waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, ← Summable.tsum_add hw hv]
  refine tsum_congr fun t => ?_
  simp only [waveSelTermZ]
  split_ifs <;> ring

theorem waveSelSumZ_add_right (w w' w'' v : ℤ → ℂ)
    (hw : Summable (waveSelTermZ c w w' w'' l)) (hv : Summable (waveSelTermZ c w w' v l)) :
    waveSelSumZ c w w' (fun j => w'' j + v j) l =
      waveSelSumZ c w w' w'' l + waveSelSumZ c w w' v l := by
  rw [waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, waveSelSumZ_eq_tsum, ← Summable.tsum_add hw hv]
  refine tsum_congr fun t => ?_
  simp only [waveSelTermZ]
  split_ifs <;> ring

/-- Symmetry in the first two arguments when `c` is symmetric in its first two indices. -/
theorem waveSelSumZ_swap_left_mid (hc : ∀ i j k l, c i j k l = c j i k l) (w w' w'' : ℤ → ℂ) :
    waveSelSumZ c w w' w'' l = waveSelSumZ c w' w w'' l := by
  unfold waveSelSumZ
  let e : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [hc t.2.1 t.1]
  by_cases h : t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0
  · rw [if_pos ⟨h.2.1, h.1, h.2.2⟩, if_pos h]; ring
  · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2⟩), if_neg h]

/-- Symmetry in the last two arguments when `c` is symmetric in its second and third indices. -/
theorem waveSelSumZ_swap_mid_right (hc : ∀ i j k l, c i j k l = c i k j l) (w w' w'' : ℤ → ℂ) :
    waveSelSumZ c w w' w'' l = waveSelSumZ c w w'' w' l := by
  unfold waveSelSumZ
  let e : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [hc t.1 t.2.2]
  by_cases h : t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0
  · rw [if_pos ⟨h.1, h.2.2, h.2.1⟩, if_pos h]; ring
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩), if_neg h]

theorem waveSelTwo_smul_left (r : ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) :
    waveSelTwo c (fun j => r * w j) w' w'' l = r * waveSelTwo c w w' w'' l := by
  unfold waveSelTwo
  split_ifs
  · simp
  · exact waveSelSumZ_smul_left c l r w w' w''

theorem waveSelTwo_smul_mid (r : ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) :
    waveSelTwo c w (fun j => r * w' j) w'' l = r * waveSelTwo c w w' w'' l := by
  unfold waveSelTwo
  split_ifs
  · simp
  · exact waveSelSumZ_smul_mid c l r w w' w''

theorem waveSelTwo_smul_right (r : ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) :
    waveSelTwo c w w' (fun j => r * w'' j) l = r * waveSelTwo c w w' w'' l := by
  unfold waveSelTwo
  split_ifs
  · simp
  · exact waveSelSumZ_smul_right c l r w w' w''

theorem waveSelTwo_add_left (w v w' w'' : ℤ → ℂ) (l : ℤ)
    (hw : l ≠ 0 → Summable (waveSelTermZ c w w' w'' l))
    (hv : l ≠ 0 → Summable (waveSelTermZ c v w' w'' l)) :
    waveSelTwo c (fun j => w j + v j) w' w'' l =
      waveSelTwo c w w' w'' l + waveSelTwo c v w' w'' l := by
  unfold waveSelTwo
  by_cases h : l = 0
  · simp [h]
  · simp only [h, if_false]; exact waveSelSumZ_add_left c l w v w' w'' (hw h) (hv h)

theorem waveSelTwo_add_mid (w w' v w'' : ℤ → ℂ) (l : ℤ)
    (hw : l ≠ 0 → Summable (waveSelTermZ c w w' w'' l))
    (hv : l ≠ 0 → Summable (waveSelTermZ c w v w'' l)) :
    waveSelTwo c w (fun j => w' j + v j) w'' l =
      waveSelTwo c w w' w'' l + waveSelTwo c w v w'' l := by
  unfold waveSelTwo
  by_cases h : l = 0
  · simp [h]
  · simp only [h, if_false]; exact waveSelSumZ_add_mid c l w w' v w'' (hw h) (hv h)

theorem waveSelTwo_add_right (w w' w'' v : ℤ → ℂ) (l : ℤ)
    (hw : l ≠ 0 → Summable (waveSelTermZ c w w' w'' l))
    (hv : l ≠ 0 → Summable (waveSelTermZ c w w' v l)) :
    waveSelTwo c w w' (fun j => w'' j + v j) l =
      waveSelTwo c w w' w'' l + waveSelTwo c w w' v l := by
  unfold waveSelTwo
  by_cases h : l = 0
  · simp [h]
  · simp only [h, if_false]; exact waveSelSumZ_add_right c l w w' w'' v (hw h) (hv h)

theorem waveSelTwo_swap_left_mid (hc : ∀ i j k l, c i j k l = c j i k l) (w w' w'' : ℤ → ℂ)
    (l : ℤ) : waveSelTwo c w w' w'' l = waveSelTwo c w' w w'' l := by
  unfold waveSelTwo
  split_ifs
  · rfl
  · exact waveSelSumZ_swap_left_mid c l hc w w' w''

theorem waveSelTwo_swap_mid_right (hc : ∀ i j k l, c i j k l = c i k j l) (w w' w'' : ℤ → ℂ)
    (l : ℤ) : waveSelTwo c w w' w'' l = waveSelTwo c w w'' w' l := by
  unfold waveSelTwo
  split_ifs
  · rfl
  · exact waveSelSumZ_swap_mid_right c l hc w w' w''

/-- Symmetry in the outer arguments when `c` is symmetric in its first three indices. -/
theorem waveSelTwo_swap_left_right (hc12 : ∀ i j k l, c i j k l = c j i k l)
    (hc23 : ∀ i j k l, c i j k l = c i k j l) (w w' w'' : ℤ → ℂ) (l : ℤ) :
    waveSelTwo c w w' w'' l = waveSelTwo c w'' w' w l := by
  rw [waveSelTwo_swap_left_mid c hc12, waveSelTwo_swap_mid_right c hc23,
    waveSelTwo_swap_left_mid c hc12]

end KAM.Wave

end
