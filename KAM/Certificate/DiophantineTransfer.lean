/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.QuadraticDiophantine

/-!
# Diophantine transfer along an integer change of the index

If `T` maps nonzero integer vectors to nonzero integer vectors, preserves the small divisor and
satisfies `|T k|₁ ≤ C |k|₁`, then Diophantine constants transfer with `γ ↦ γ / C ^ τ`. With
`T k = ![k 0, k 1 - k 0]` and `C = 2` this moves the lunar bounds to the rotated frame
`(ν - 1, 1)` (owner ruling O5).
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

/-- Diophantine transfer along an integer change of the index: if every nonzero `k` has a nonzero
image `T k` with the same small divisor against `ω` and `|T k|₁ ≤ C |k|₁`, then `ω'` is
`(γ / C ^ τ, τ)`-Diophantine. -/
theorem isDiophantine_of_index_map {n m : ℕ} {γ τ C : ℝ} {ω : Fin n → ℝ} {ω' : Fin m → ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) (hC : 0 < C)
    (T : (Fin m → ℤ) → (Fin n → ℤ)) (hT : ∀ k, k ≠ 0 → T k ≠ 0)
    (hdot : ∀ k, ∑ i, (T k i : ℝ) * ω i = ∑ j, (k j : ℝ) * ω' j)
    (hnorm : ∀ k, ∑ i, |(T k i : ℝ)| ≤ C * ∑ j, |(k j : ℝ)|) :
    IsDiophantine (γ / C ^ τ) τ ω' := by
  intro k hk
  have h1 := hω (T k) (hT k hk)
  rw [hdot k] at h1
  refine le_trans ?_ h1
  have hpos : 0 < ∑ i, |(T k i : ℝ)| := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hT k hk)
    have : 0 < |(T k i : ℝ)| := abs_pos.mpr (by exact_mod_cast hi)
    exact lt_of_lt_of_le this
      (Finset.single_le_sum (f := fun i => |(T k i : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hle := hnorm k
  have hpow : (∑ i, |(T k i : ℝ)|) ^ τ ≤ (C * ∑ j, |(k j : ℝ)|) ^ τ :=
    Real.rpow_le_rpow hpos.le hle hτ
  have hS : 0 ≤ ∑ j, |(k j : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.mul_rpow hC.le hS] at hpow
  rw [div_div]
  exact div_le_div_of_nonneg_left hγ (Real.rpow_pos_of_pos hpos _) hpow

/-- The index map `k ↦ (k₀, k₁ - k₀)` of the rotation `Q₁ = q - φ`, `Q₂ = φ`. -/
private def rotIdx (k : Fin 2 → ℤ) : Fin 2 → ℤ := ![k 0, k 1 - k 0]

private lemma rot_transfer {x γ : ℝ} (hγ : 0 ≤ γ) (h : IsDiophantine γ 1 ![x, 1]) :
    IsDiophantine (γ / 2) 1 ![x - 1, 1] := by
  have := isDiophantine_of_index_map (τ := 1) (C := 2) (ω' := ![x - 1, 1]) h hγ zero_le_one two_pos
    rotIdx
    (fun k hk => by
      intro h0
      apply hk
      have a := congrFun h0 0
      have b := congrFun h0 1
      simp only [rotIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at a b
      ext i
      fin_cases i <;> simp <;> omega)
    (fun k => by
      simp only [rotIdx, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring)
    (fun k => by
      simp only [rotIdx, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      have h1 := abs_sub (k 1 : ℝ) (k 0 : ℝ)
      have := abs_nonneg (k 0 : ℝ)
      have := abs_nonneg (k 1 : ℝ)
      linarith)
  simpa using this

private lemma rot_half {x γ : ℝ} (hγ : 0 ≤ γ) (h : IsDiophantine γ 1 ![x / 2, 1 / 2]) :
    IsDiophantine (γ / 2) 1 ![(x - 1) / 2, 1 / 2] := by
  have := isDiophantine_of_index_map (τ := 1) (C := 2) (ω' := ![(x - 1) / 2, 1 / 2]) h hγ
    zero_le_one two_pos rotIdx
    (fun k hk => by
      intro h0
      apply hk
      have a := congrFun h0 0
      have b := congrFun h0 1
      simp only [rotIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at a b
      ext i
      fin_cases i <;> simp <;> omega)
    (fun k => by
      simp only [rotIdx, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring)
    (fun k => by
      simp only [rotIdx, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      have h1 := abs_sub (k 1 : ℝ) (k 0 : ℝ)
      have := abs_nonneg (k 0 : ℝ)
      have := abs_nonneg (k 1 : ℝ)
      linarith)
  simpa using this

/-- The rotated lunar frequency `(ν₋ - 1, 1)` (owner ruling O5). -/
theorem lunarNuMinus_rot_isDiophantine : IsDiophantine (1 / 42) 1 ![lunarNuMinus - 1, 1] := by
  have := rot_transfer (by norm_num) lunarNuMinus_isDiophantine
  norm_num at this ⊢
  exact this

/-- The rotated lunar frequency `(ν₊ - 1, 1)` (owner ruling O5). -/
theorem lunarNuPlus_rot_isDiophantine : IsDiophantine (1 / 42) 1 ![lunarNuPlus - 1, 1] := by
  have := rot_transfer (by norm_num) lunarNuPlus_isDiophantine
  norm_num at this ⊢
  exact this

/-- The rotated isoenergetic reference vector `((ν₋ - 1)/2, 1/2)`. -/
theorem lunarNuMinus_rot_half_isDiophantine :
    IsDiophantine (1 / 84) 1 ![(lunarNuMinus - 1) / 2, 1 / 2] := by
  have := rot_half (by norm_num) lunarNuMinus_half_isDiophantine
  norm_num at this ⊢
  exact this

/-- The rotated isoenergetic reference vector `((ν₊ - 1)/2, 1/2)`. -/
theorem lunarNuPlus_rot_half_isDiophantine :
    IsDiophantine (1 / 84) 1 ![(lunarNuPlus - 1) / 2, 1 / 2] := by
  have := rot_half (by norm_num) lunarNuPlus_half_isDiophantine
  norm_num at this ⊢
  exact this

end KAM.Certificate
