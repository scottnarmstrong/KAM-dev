/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Recon2.Functionals

/-!
# The force identity in frozen form (blueprint `bpW:w2:force`)

Infrastructure used by several nodes; the dependency graph is still being built. Blueprint label
`bpW:w2:force` (milestone W2).

For `y ∈ ℓ²` the series `Σ_lin = Σ √λ_j λ_j κ(y)_j φ_j` and `Σ_cub = Σ √λ_j 𝒢(y)_j φ_j` converge
absolutely (`KAM.Wave.reconWave_force_summable_lin`, `KAM.Wave.reconWave_force_summable_cub`),
`Σ_lin = -D² y + m D⁰ y` on `ℝ` (`KAM.Wave.reconWave_force_lin`) and `Σ_cub = U_m(y)³` on `[0, π]`
(`KAM.Wave.reconWave_force_cub`, from `KAM.Wave.wave_force_identity`). The bundled statement is
`KAM.Wave.reconWave_force`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

lemma lam_sq_eq (m : ℝ) (hm : 0 < m) (j : ℕ+) : lam m hm j ^ 2 = (j : ℝ) ^ 2 + m := by
  unfold lam; rw [Real.sq_sqrt (by positivity)]

/-- Termwise form of `Σ_lin = -D² + m D⁰`. -/
lemma reconWave_lin_term (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) (j : ℕ+) :
    Real.sqrt (lam m hm j) * (lam m hm j * coeff y j) * sineMode j x =
      -(-(coeff y j / Real.sqrt (lam m hm j) *
        (Real.sqrt (2 / π) * (j : ℝ) ^ 2 * Real.sin (j * x)))) +
        m * (coeff y j / Real.sqrt (lam m hm j) * sineMode j x) := by
  have hs := wave_sqrt_lam_pos m hm j
  have h2 := sqrt_lam_sq m hm j
  have h4 : (j : ℝ) ^ 2 + m = (Real.sqrt (lam m hm j) ^ 2) ^ 2 := by
    rw [h2, lam_sq_eq m hm j]
  unfold sineMode
  set s := Real.sqrt (lam m hm j) with hsdef
  have hj2 : (j : ℝ) ^ 2 = (s ^ 2) ^ 2 - m := by linarith
  rw [← h2, hj2]
  field_simp
  ring

theorem reconWave_force_summable_lin (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |Real.sqrt (lam m hm j) * (lam m hm j * coeff y j) * sineMode j x| := by
  have h1 := summable_abs_reconUxx_terms m hm y x
  have h2 := (summable_abs_reconU_terms m hm y x).mul_left |m|
  refine (h1.add h2).of_nonneg_of_le (fun _ => abs_nonneg _) fun j => ?_
  rw [reconWave_lin_term, ← abs_neg (-(coeff y j / Real.sqrt (lam m hm j) *
        (Real.sqrt (2 / π) * (j : ℝ) ^ 2 * Real.sin (j * x))))]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]

theorem reconWave_force_summable_cub (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |Real.sqrt (lam m hm j) * cubicGrad m hm y j * sineMode j x| := by
  have hc := summable_abs_sqrtLam_waveCubic m hm (waveEll_coeff y)
  have := summable_abs_waveSineSeries (k := 0)
    (c := fun l : ℕ+ => Real.sqrt (lam m hm l) * waveCubic m hm (coeff y) l)
    (by simpa using hc) x
  simpa only [sineModeIter_zero, cubicGrad_eq_waveCubic] using this

/-- Linear part of the force identity (blueprint `bpW:w2:force` (i)): for every `x ∈ ℝ`. -/
theorem reconWave_force_lin (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    ∑' j : ℕ+, Real.sqrt (lam m hm j) * (lam m hm j * coeff y j) * sineMode j x =
      -reconUxx m hm y x + m * reconU m hm y x := by
  simp_rw [reconWave_lin_term]
  rw [Summable.tsum_add (summable_abs_reconUxx_terms m hm y x).of_abs.neg
    ((summable_abs_reconU_terms m hm y x).of_abs.mul_left m), tsum_neg, tsum_mul_left]
  rfl

/-- Cubic part of the force identity (blueprint `bpW:w2:force` (ii)): for `x ∈ [0, π]`. -/
theorem reconWave_force_cub (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) {x : ℝ}
    (hx : x ∈ Set.Icc 0 π) :
    ∑' j : ℕ+, Real.sqrt (lam m hm j) * cubicGrad m hm y j * sineMode j x =
      reconU m hm y x ^ 3 := by
  have h := wave_force_identity m hm (waveEll_coeff y) x hx
  rw [← reconU_eq_waveU] at h
  rw [h]
  unfold waveSineSeries
  refine tsum_congr fun j => ?_
  rw [sineModeIter_zero, cubicGrad_eq_waveCubic]

/-- **Force identity in frozen form** (blueprint `bpW:w2:force`). -/
theorem reconWave_force (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    (∀ x : ℝ, Summable fun j : ℕ+ =>
        |Real.sqrt (lam m hm j) * (lam m hm j * coeff y j) * sineMode j x|) ∧
      (∀ x : ℝ, Summable fun j : ℕ+ =>
        |Real.sqrt (lam m hm j) * cubicGrad m hm y j * sineMode j x|) ∧
      (∀ x : ℝ, ∑' j : ℕ+, Real.sqrt (lam m hm j) * (lam m hm j * coeff y j) * sineMode j x =
        -reconUxx m hm y x + m * reconU m hm y x) ∧
      ∀ x ∈ Set.Icc 0 π, ∑' j : ℕ+, Real.sqrt (lam m hm j) * cubicGrad m hm y j * sineMode j x =
        reconU m hm y x ^ 3 :=
  ⟨reconWave_force_summable_lin m hm y, reconWave_force_summable_cub m hm y,
    reconWave_force_lin m hm y, fun _ hx => reconWave_force_cub m hm y hx⟩

end KAM.Wave

end
