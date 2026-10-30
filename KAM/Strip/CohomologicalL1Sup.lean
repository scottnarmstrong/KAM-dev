/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalSumSeries
public import KAM.Strip.FourierBasic
public import KAM.Strip.FourierSeries
public import KAM.Diophantine.Cohomological
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The sup-over-modes constant of the weighted ℓ¹ cohomological estimate

In weighted ℓ¹ coefficient norms the cohomological equation needs no lattice counting: the
solution `û_k = ĝ_k/(2πi k·ω)` satisfies `|û_k| e^{2π(r-δ)|k|₁} ≤ Γ_∞(ω, δ) |ĝ_k| e^{2πr|k|₁}` with

`Γ_∞(ω, δ) = sup_{k≠0} e^{-2πδ|k|₁} / (2π |k·ω|)` (`KAM.smallDivisorSup`).

* `KAM.smallDivisorSupTerm`, `KAM.smallDivisorSup` (a `⨆` of nonnegative terms, `0` at `k = 0`);
  `KAM.bddAbove_smallDivisorSupTerm`, `KAM.smallDivisorSupTerm_le_smallDivisorSup`,
  `KAM.smallDivisorSup_le_of_forall` (the characterization used by certificates).
* Comparisons: `KAM.smallDivisorSup_le_solveBound`, `Γ_∞ ≤ (2πγ)⁻¹ (τ/(2πeδ))^τ` (the generic
  Diophantine bound of the repository, `KAM.Diophantine.solveBound`; in the units
  `c = Γ_∞ γ δ^τ` it is `(2π)⁻¹ (τ/(2πe))^τ`, `1/(4π²e)` at `τ = 1`), and
  `KAM.smallDivisorSup_le_sqrt_sum`: `Γ_∞(ω, δ) ≤ (2π)⁻¹ S(ω, 2δ)^{1/2} ≤ (2π)⁻¹ S(ω, δ)^{1/2}` with
  `S = KAM.smallDivisorSum` (SHARP-L2).
* `KAM.summableWeighted_solve_sup`: the coefficient estimate
  `‖solve ω a‖_{s - 2πδ} ≤ Γ_∞(ω, δ) ‖a‖_s`.
* The bridge `KAM.eq_fourierSum_of_summableWeighted` and
  `KAM.norm_le_weightedNorm_of_summableWeighted`:
  a holomorphic `1`-periodic map on `T_ρ` whose coefficients are summable at radius `2πρ` is its
  Fourier series there, and is bounded by its weighted ℓ¹ norm.
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- The term `e^{-2πδ|k|₁} / (2π |k·ω|)` of `Γ_∞`, `0` at `k = 0`. -/
@[expose] def smallDivisorSupTerm (ω : Fin n → ℝ) (δ : ℝ) (k : Fin n → ℤ) : ℝ :=
  if k = 0 then 0 else
    Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
      (2 * Real.pi * |Diophantine.frequencyDot ω k|)

/-- `Γ_∞(ω, δ) = sup_{k≠0} e^{-2πδ|k|₁} / (2π |k·ω|)`. -/
@[expose] def smallDivisorSup (ω : Fin n → ℝ) (δ : ℝ) : ℝ := ⨆ k, smallDivisorSupTerm ω δ k

theorem smallDivisorSupTerm_nonneg (ω : Fin n → ℝ) (δ : ℝ) (k : Fin n → ℤ) :
    0 ≤ smallDivisorSupTerm ω δ k := by
  unfold smallDivisorSupTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem smallDivisorSupTerm_of_ne {ω : Fin n → ℝ} {δ : ℝ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    smallDivisorSupTerm ω δ k = Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
      (2 * Real.pi * |Diophantine.frequencyDot ω k|) := by
  simp only [smallDivisorSupTerm, hk, ↓reduceIte]

theorem smallDivisorSup_nonneg (ω : Fin n → ℝ) (δ : ℝ) : 0 ≤ smallDivisorSup ω δ :=
  Real.iSup_nonneg (smallDivisorSupTerm_nonneg ω δ)

/-- Below a bound `B ≥ 0` of every term `k ≠ 0`. -/
theorem smallDivisorSup_le_of_forall {ω : Fin n → ℝ} {δ B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k : Fin n → ℤ, k ≠ 0 → Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
      (2 * Real.pi * |Diophantine.frequencyDot ω k|) ≤ B) :
    smallDivisorSup ω δ ≤ B := by
  refine ciSup_le fun k => ?_
  by_cases hk : k = 0
  · simp only [smallDivisorSupTerm, hk, ↓reduceIte]
    exact hB0
  · rw [smallDivisorSupTerm_of_ne hk]
    exact hB k hk

section Diophantine

variable {ω : Fin n → ℝ} {γ τ δ : ℝ}

/-- Each term is at most the generic Diophantine bound `(2πγ)⁻¹ (τ/(2πeδ))^τ`. -/
theorem smallDivisorSupTerm_le_solveBound (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (k : Fin n → ℤ) :
    smallDivisorSupTerm ω δ k ≤ Diophantine.solveBound γ τ (2 * Real.pi * δ) := by
  by_cases hk : k = 0
  · simp only [smallDivisorSupTerm, hk, ↓reduceIte]
    exact Diophantine.solveBound_nonneg hγ hτ (by positivity)
  rw [smallDivisorSupTerm_of_ne hk]
  have hm : 0 < Fourier.modeSize k := by
    rw [modeSize_eq_modeNat]
    exact_mod_cast modeNat_pos hk
  have hmτ : 0 < Fourier.modeSize k ^ τ := Real.rpow_pos_of_pos hm τ
  have hd := hω k hk
  have hdpos : 0 < |Diophantine.frequencyDot ω k| := lt_of_lt_of_le (div_pos hγ hmτ) hd
  have h1 : 1 / |Diophantine.frequencyDot ω k| ≤ Fourier.modeSize k ^ τ / γ := by
    rw [div_le_div_iff₀ hdpos hγ, one_mul]
    rw [div_le_iff₀ hmτ] at hd
    linarith
  have h2 := Fourier.rpow_mul_exp_neg_le (x := Fourier.modeSize k) (τ := τ)
    (δ := 2 * Real.pi * δ) hm.le hτ (by positivity)
  calc Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
        (2 * Real.pi * |Diophantine.frequencyDot ω k|)
      = (2 * Real.pi)⁻¹ * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) *
          (1 / |Diophantine.frequencyDot ω k|) := by
        field_simp
    _ ≤ (2 * Real.pi)⁻¹ * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) *
          (Fourier.modeSize k ^ τ / γ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / (2 * Real.pi * γ)) *
          (Fourier.modeSize k ^ τ * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k)) := by
        field_simp
    _ ≤ (1 / (2 * Real.pi * γ)) * (τ / (Real.exp 1 * (2 * Real.pi * δ))) ^ τ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Diophantine.solveBound γ τ (2 * Real.pi * δ) := rfl

theorem bddAbove_smallDivisorSupTerm (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) : BddAbove (Set.range (smallDivisorSupTerm ω δ)) :=
  ⟨_, Set.forall_mem_range.2 (smallDivisorSupTerm_le_solveBound hω hγ hτ hδ)⟩

theorem smallDivisorSupTerm_le_smallDivisorSup (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (k : Fin n → ℤ) :
    smallDivisorSupTerm ω δ k ≤ smallDivisorSup ω δ :=
  le_ciSup (bddAbove_smallDivisorSupTerm hω hγ hτ hδ) k

/-- **Comparison with the generic bound.** `Γ_∞(ω, δ) ≤ (2πγ)⁻¹ (τ/(2πeδ))^τ`. -/
theorem smallDivisorSup_le_solveBound (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    smallDivisorSup ω δ ≤ Diophantine.solveBound γ τ (2 * Real.pi * δ) :=
  ciSup_le (smallDivisorSupTerm_le_solveBound hω hγ hτ hδ)

/-- `S(ω, δ')` decreases in `δ'`. -/
theorem smallDivisorSum_anti (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) {δ' : ℝ} (hδδ' : δ ≤ δ') : smallDivisorSum ω δ' ≤ smallDivisorSum ω δ := by
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_smallDivisorTerm hω hγ hτ
    (hδ.trans_le hδδ')) (summable_smallDivisorTerm hω hγ hτ hδ)
  by_cases hk : k = 0
  · simp [smallDivisorTerm, hk]
  · rw [smallDivisorTerm_of_ne hk, smallDivisorTerm_of_ne hk]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h := mul_nonneg (mul_nonneg Real.pi_pos.le (Fourier.modeSize_nonneg k))
      (sub_nonneg.mpr hδδ')
    nlinarith [h]

/-- **Comparison with SHARP-L2.** `Γ_∞(ω, δ) ≤ (2π)⁻¹ S(ω, 2δ)^{1/2} ≤ (2π)⁻¹ S(ω, δ)^{1/2}`: each
term of `Γ_∞` is `(2π)⁻¹` times the square root of a term of `S(ω, 2δ)`. -/
theorem smallDivisorSup_le_sqrt_sum (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    smallDivisorSup ω δ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (smallDivisorSum ω (2 * δ)) ∧
      (2 * Real.pi)⁻¹ * Real.sqrt (smallDivisorSum ω (2 * δ)) ≤
        (2 * Real.pi)⁻¹ * Real.sqrt (smallDivisorSum ω δ) := by
  refine ⟨ciSup_le fun k => ?_, mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (smallDivisorSum_anti hω hγ hτ hδ (by linarith))) (by positivity)⟩
  by_cases hk : k = 0
  · simp only [smallDivisorSupTerm, hk, ↓reduceIte]
    positivity
  rw [smallDivisorSupTerm_of_ne hk]
  set d := |Diophantine.frequencyDot ω k| with hd
  set e := Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) with he
  have hsq : (e / d) ^ 2 = smallDivisorTerm ω (2 * δ) k := by
    rw [smallDivisorTerm_of_ne hk, div_pow, hd, sq_abs, he, ← Real.exp_nat_mul, div_eq_inv_mul]
    congr 2
    push_cast
    ring
  have hterm : smallDivisorTerm ω (2 * δ) k ≤ smallDivisorSum ω (2 * δ) := by
    have := sum_le_smallDivisorSum hω hγ hτ (by linarith : 0 < 2 * δ) {k}
    simpa using this
  calc e / (2 * Real.pi * d) = (2 * Real.pi)⁻¹ * (e / d) := by
        rw [mul_comm (2 * Real.pi) d, ← div_div, div_eq_inv_mul]
    _ = (2 * Real.pi)⁻¹ * Real.sqrt (smallDivisorTerm ω (2 * δ) k) := by
        rw [← hsq, Real.sqrt_sq (by positivity)]
    _ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (smallDivisorSum ω (2 * δ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hterm) (by positivity)

/-! ### The coefficient estimate -/

/-- Pointwise: `|ŝ_k| e^{(s-2πδ)|k|₁} ≤ Γ_∞ |a_k| e^{s|k|₁}` for `ŝ = solve ω a`. -/
theorem solve_weight_le_sup (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (a : (Fin n → ℤ) → ℂ) (s : ℝ) (k : Fin n → ℤ) :
    ‖Diophantine.solve ω a k‖ * Real.exp ((s - 2 * Real.pi * δ) * Fourier.modeSize k) ≤
      smallDivisorSup ω δ * (‖a k‖ * Real.exp (s * Fourier.modeSize k)) := by
  by_cases hk : k = 0
  · subst hk
    simp only [Diophantine.solve_zero_mode, norm_zero, zero_mul]
    exact mul_nonneg (smallDivisorSup_nonneg ω δ) (by positivity)
  have hΓ := smallDivisorSupTerm_le_smallDivisorSup hω hγ hτ hδ k
  rw [smallDivisorSupTerm_of_ne hk] at hΓ
  have hn : ‖Diophantine.solve ω a k‖ =
      ‖a k‖ / (2 * Real.pi * |Diophantine.frequencyDot ω k|) := by
    simp only [Diophantine.solve, hk, ↓reduceIte, norm_div, Diophantine.norm_flowMultiplier]
  have hexp : Real.exp ((s - 2 * Real.pi * δ) * Fourier.modeSize k) =
      Real.exp (s * Fourier.modeSize k) *
        Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hn, hexp]
  calc ‖a k‖ / (2 * Real.pi * |Diophantine.frequencyDot ω k|) *
        (Real.exp (s * Fourier.modeSize k) *
          Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k))
      = Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
          (2 * Real.pi * |Diophantine.frequencyDot ω k|) *
          (‖a k‖ * Real.exp (s * Fourier.modeSize k)) := by ring
    _ ≤ smallDivisorSup ω δ * (‖a k‖ * Real.exp (s * Fourier.modeSize k)) :=
        mul_le_mul_of_nonneg_right hΓ (by positivity)

/-- **The weighted ℓ¹ coefficient estimate.** `‖solve ω a‖_{s - 2πδ} ≤ Γ_∞(ω, δ) ‖a‖_s`. -/
theorem summableWeighted_solve_sup (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted s a) :
    Fourier.SummableWeighted (s - 2 * Real.pi * δ) (Diophantine.solve ω a) ∧
      Fourier.weightedNorm (s - 2 * Real.pi * δ) (Diophantine.solve ω a) ≤
        smallDivisorSup ω δ * Fourier.weightedNorm s a := by
  have hle := solve_weight_le_sup hω hγ hτ hδ a s
  have hsum : Fourier.SummableWeighted (s - 2 * Real.pi * δ) (Diophantine.solve ω a) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (ha.mul_left _)
  refine ⟨hsum, ?_⟩
  calc Fourier.weightedNorm (s - 2 * Real.pi * δ) (Diophantine.solve ω a)
      ≤ ∑' k, smallDivisorSup ω δ * (‖a k‖ * Real.exp (s * Fourier.modeSize k)) :=
        Summable.tsum_le_tsum hle hsum (ha.mul_left _)
    _ = smallDivisorSup ω δ * Fourier.weightedNorm s a := tsum_mul_left

end Diophantine

/-! ### The bridge between holomorphic maps and their coefficients -/

/-- A holomorphic `1`-periodic map on `T_ρ` whose torus coefficients are summable at radius `2πρ`
is its Fourier series on `T_ρ`. -/
theorem eq_fourierSum_of_summableWeighted {ρ : ℝ} (hρ : 0 < ρ) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hs : Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => u fun j => (x j : ℂ))) :
    ∀ θ ∈ complexStrip n ρ, u θ = fourierSum (torusCoeff fun x => u fun j => (x j : ℂ)) θ := by
  set a := torusCoeff fun x => u fun j => (x j : ℂ) with ha
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hcu : Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous hL fun x => ofReal_mem_complexStrip hρ x
  have hF := differentiableOn_fourierSum hs
  have hcF : Continuous fun x : Fin n → ℝ => fourierSum a fun j => (x j : ℂ) :=
    hF.continuousOn.comp_continuous hL fun x => ofReal_mem_complexStrip hρ x
  have h0 := eq_zero_of_torusCoeff_holomorphic hρ (v := fun z => u z - fourierSum a z)
    (hu.sub hF) (fun i z hz => by
      show u (z + Pi.single i 1) - fourierSum a (z + Pi.single i 1) = u z - fourierSum a z
      rw [hp i z hz, fourierSum_add_single])
    (fun k => by
      rw [torusCoeff_sub hcu hcF, torusCoeff_fourierSum hρ.le hs, ha, sub_self])
  intro θ hθ
  exact sub_eq_zero.mp (h0 θ hθ)

/-- ... and is bounded there by its weighted ℓ¹ norm. -/
theorem norm_le_weightedNorm_of_summableWeighted {ρ : ℝ} (hρ : 0 < ρ) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hs : Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => u fun j => (x j : ℂ))) :
    ∀ θ ∈ complexStrip n ρ, ‖u θ‖ ≤
      Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => u fun j => (x j : ℂ)) :=
  fun θ hθ => by
    rw [eq_fourierSum_of_summableWeighted hρ hu hp hs θ hθ]
    exact norm_fourierSum_le hs hθ

end KAM

end
