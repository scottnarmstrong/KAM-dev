/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Fourier.Derivative
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# The scale choice (37) and the exponential horizon

Package LP-NRS, `LP:MAIN L13 (444–458)` with `LP:MAIN L12 (381–428)` for the shape of `K`;
track LP, non-frozen.  Amendments N6 (stopped radius `r = D₀ √μ`, improvement to `r/2`) and N4
((35) is not a dependency) are respected.

Pure scalar arithmetic: for the Lemma-13 route with `p = 2` (`conjExp 2 = 2`) the numeric premises
of
`KAM.Nekhoroshev.ExtNFHyp` (`divisor_size`, `slow`, `cutoff`) and of `KAM.Nekhoroshev.nonresonant`
(`hsmall`, and the time bound `s r/(5 ε) exp(2π K s/6)`) hold for all `0 < μ ≤ μ₀`, with the
exponent `a = 1/(2(τ+1))`.

* `scaleExponent`, `scaledCutoff`, `stoppedRadius`, `divisorGap`, `perturbSize`: the data
  `a`, `K μ`, `r μ`, `α μ`, `ε μ`.
* `lp_scale_choice`: the scale theorem (items (a)–(g)).
* `diophantine_to_period_one`: the radian to period-one conversion of `LP:MAIN (5)` at the centre.
* `scaleExponent_planar`: `τ = n - 1/2` gives `a = 1/(2n+1)`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Real

/-- The exponent `a = 1/(2(τ+1))` (`LP:MAIN L12 (32)`). -/
def scaleExponent (τ : ℝ) : ℝ := 1 / (2 * (τ + 1))

/-- The cutoff `K μ = ⌊κ μ^{-a}⌋` as a real number (`LP:MAIN L13 (37)`). -/
def scaledCutoff (κ τ μ : ℝ) : ℝ := (⌊κ * μ ^ (-scaleExponent τ)⌋₊ : ℝ)

/-- The stopped radius `r μ = D₀ √μ` (`LP:MAIN L13`, amendment N6). -/
def stoppedRadius (D₀ μ : ℝ) : ℝ := D₀ * √μ

/-- The divisor lower bound `α μ = γ/(2π) K^{-τ}` (`LP:MAIN L13`). -/
def divisorGap (γ τ κ μ : ℝ) : ℝ := γ / (2 * π) * scaledCutoff κ τ μ ^ (-τ)

/-- The perturbation size `ε μ = M₂ μ` (`LP:MAIN L13`). -/
def perturbSize (M₂ μ : ℝ) : ℝ := M₂ * μ

section Arithmetic

variable {τ : ℝ}

/-- `(μ^{-a})^{τ+1} √μ = 1`, from `a (τ+1) = 1/2`. -/
theorem rpow_neg_scale_mul_sqrt (hτ : 0 < τ) {μ : ℝ} (hμ : 0 < μ) :
    (μ ^ (-scaleExponent τ)) ^ (τ + 1) * √μ = 1 := by
  rw [← Real.rpow_mul hμ.le, Real.sqrt_eq_rpow, ← Real.rpow_add hμ]
  have h : -scaleExponent τ * (τ + 1) + 1 / 2 = 0 := by
    have : τ + 1 ≠ 0 := by linarith
    unfold scaleExponent
    field_simp
    ring
  rw [h, Real.rpow_zero]

/-- `K^{τ+1} √μ ≤ κ^{τ+1}` for the floor cutoff. -/
theorem cutoff_rpow_mul_sqrt_le (hτ : 0 < τ) {κ : ℝ} (hκ : 0 < κ) {μ : ℝ} (hμ : 0 < μ) :
    scaledCutoff κ τ μ ^ (τ + 1) * √μ ≤ κ ^ (τ + 1) := by
  have hX : 0 ≤ κ * μ ^ (-scaleExponent τ) := by positivity
  have hK0 : 0 ≤ scaledCutoff κ τ μ := Nat.cast_nonneg _
  have hKX : scaledCutoff κ τ μ ≤ κ * μ ^ (-scaleExponent τ) := Nat.floor_le hX
  have h1 : scaledCutoff κ τ μ ^ (τ + 1) ≤ (κ * μ ^ (-scaleExponent τ)) ^ (τ + 1) :=
    Real.rpow_le_rpow hK0 hKX (by linarith)
  rw [Real.mul_rpow hκ.le (by positivity)] at h1
  calc scaledCutoff κ τ μ ^ (τ + 1) * √μ
      ≤ (κ ^ (τ + 1) * (μ ^ (-scaleExponent τ)) ^ (τ + 1)) * √μ :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = κ ^ (τ + 1) := by
        rw [mul_assoc, rpow_neg_scale_mul_sqrt hτ hμ, mul_one]

/-- Lower bounds for the floor cutoff once `2 ≤ κ μ^{-a}`. -/
theorem scaledCutoff_lower {κ τ μ : ℝ} (hX : 2 ≤ κ * μ ^ (-scaleExponent τ)) :
    1 ≤ scaledCutoff κ τ μ ∧ κ * μ ^ (-scaleExponent τ) / 2 ≤ scaledCutoff κ τ μ := by
  have h := Nat.lt_floor_add_one (κ * μ ^ (-scaleExponent τ))
  unfold scaledCutoff
  constructor <;> linarith

end Arithmetic

/-- Existence of `κ` satisfying the two smallness conditions of `LP:MAIN L13` before (37). -/
theorem exists_scale_kappa {γ τ L M₂ D₀ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hL : 0 ≤ L)
    (hM : 0 < M₂) (hD : 0 < D₀) :
    ∃ κ : ℝ, 0 < κ ∧ L * D₀ * κ ^ (τ + 1) ≤ γ / (4 * π) ∧
      M₂ * κ ^ (τ + 1) ≤ γ * D₀ / (512 * π) := by
  have hπ := Real.pi_pos
  set m1 : ℝ := γ / (4 * π * (L * D₀ + 1)) with hm1
  set m2 : ℝ := γ * D₀ / (512 * π * (M₂ + 1)) with hm2
  have hLD : 0 ≤ L * D₀ := by positivity
  have hm1pos : 0 < m1 := by positivity
  have hm2pos : 0 < m2 := by positivity
  set m : ℝ := min m1 m2 with hm
  have hmpos : 0 < m := lt_min hm1pos hm2pos
  have hq : 0 < τ + 1 := by linarith
  refine ⟨m ^ (1 / (τ + 1)), by positivity, ?_, ?_⟩
  · have hk : (m ^ (1 / (τ + 1))) ^ (τ + 1) = m := by
      rw [← Real.rpow_mul hmpos.le, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
    rw [hk]
    have e1 : m1 * (L * D₀ + 1) = γ / (4 * π) := by
      rw [hm1]; field_simp
    calc L * D₀ * m ≤ L * D₀ * m1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hLD
      _ ≤ (L * D₀ + 1) * m1 := by nlinarith
      _ = γ / (4 * π) := by rw [mul_comm, e1]
  · have hk : (m ^ (1 / (τ + 1))) ^ (τ + 1) = m := by
      rw [← Real.rpow_mul hmpos.le, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
    rw [hk]
    have e2 : m2 * (M₂ + 1) = γ * D₀ / (512 * π) := by
      rw [hm2]; field_simp
    calc M₂ * m ≤ M₂ * m2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      _ ≤ (M₂ + 1) * m2 := by nlinarith
      _ = γ * D₀ / (512 * π) := by rw [mul_comm, e2]

/-- **The scale theorem** (`LP:MAIN L13 (444–458)`, (37) and the choice of `κ₁`, `μ₀`; `p = 2`).
`κ, μ₀, c, T₀` depend only on the data, never on `μ`. -/
theorem lp_scale_choice {γ τ L M₂ D₀ s w ρ : ℝ} {k : ℕ} (hγ : 0 < γ) (hτ : 0 < τ) (hL : 0 ≤ L)
    (hM : 0 < M₂) (hD : 0 < D₀) (hs : 0 < s) (hw : 0 < w) (hρ : 0 < ρ) (hk : 1 ≤ k) :
    ∃ κ μ₀ c T₀ : ℝ, 0 < κ ∧ 0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
        (1 ≤ scaledCutoff κ τ μ ∧
          κ * μ ^ (-scaleExponent τ) / 2 ≤ scaledCutoff κ τ μ ∧
          scaledCutoff κ τ μ ≤ κ * μ ^ (-scaleExponent τ)) ∧
        scaledCutoff κ τ μ * L * stoppedRadius D₀ μ ≤ divisorGap γ τ κ μ / 2 ∧
        perturbSize M₂ μ ≤ divisorGap γ τ κ μ * stoppedRadius D₀ μ /
          (2 ^ 7 * KAM.NormalForm.conjExp 2 * scaledCutoff κ τ μ) ∧
        64 * π * k * s * stoppedRadius D₀ μ ≤ w ^ 2 ∧
        6 ≤ 2 * π * scaledCutoff κ τ μ * s ∧
        stoppedRadius D₀ μ ≤ ρ ∧
        T₀ * Real.exp (c * μ ^ (-scaleExponent τ)) ≤
          s * stoppedRadius D₀ μ / (5 * perturbSize M₂ μ) *
            Real.exp (2 * π * scaledCutoff κ τ μ * s / 6) := by
  have hπ := Real.pi_pos
  obtain ⟨κ, hκ, hκ1, hκ2⟩ := exists_scale_kappa hγ hτ hL hM hD
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < scaleExponent τ := by unfold scaleExponent; apply div_pos one_pos; linarith
  set E : ℝ := 2 + 6 / (π * s) with hE
  have hEpos : 0 < E := by positivity
  have h6 : 0 < 6 / (π * s) := by positivity
  have hE2 : 2 ≤ E := by rw [hE]; linarith
  set B : ℝ := w ^ 2 / (64 * π * k * s * D₀) with hB
  have hBpos : 0 < B := by positivity
  refine ⟨κ, min 1 (min ((κ / E) ^ (2 * (τ + 1))) (min (B ^ 2) ((ρ / D₀) ^ 2))),
    π * s * κ / 6, s * D₀ / (5 * M₂), hκ, by positivity, by positivity, by positivity, ?_⟩
  intro μ hμ hμ₀
  have hμ1 : μ ≤ 1 := hμ₀.trans (min_le_left _ _)
  have hμ2 : μ ≤ (κ / E) ^ (2 * (τ + 1)) := hμ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμ3 : μ ≤ B ^ 2 :=
    hμ₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμ4 : μ ≤ (ρ / D₀) ^ 2 :=
    hμ₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsq : 0 < √μ := Real.sqrt_pos.mpr hμ
  -- the lower bound `E ≤ κ μ^{-a}`
  have hXE : E ≤ κ * μ ^ (-scaleExponent τ) := by
    have h1 : μ ^ scaleExponent τ ≤ κ / E := by
      calc μ ^ scaleExponent τ ≤ ((κ / E) ^ (2 * (τ + 1))) ^ scaleExponent τ :=
            Real.rpow_le_rpow hμ.le hμ2 ha.le
        _ = κ / E := by
            rw [← Real.rpow_mul (by positivity)]
            have : 2 * (τ + 1) * scaleExponent τ = 1 := by
              have : τ + 1 ≠ 0 := by linarith
              unfold scaleExponent; field_simp
            rw [this, Real.rpow_one]
    rw [Real.rpow_neg hμ.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hEpos] at h1
    linarith
  obtain ⟨hK1, hK2⟩ := scaledCutoff_lower (hE2.trans hXE)
  have hKX : scaledCutoff κ τ μ ≤ κ * μ ^ (-scaleExponent τ) :=
    Nat.floor_le (by positivity)
  have hKpos : 0 < scaledCutoff κ τ μ := by linarith
  have hpow := cutoff_rpow_mul_sqrt_le hτ hκ hμ
  have hP : 0 < scaledCutoff κ τ μ ^ τ := by positivity
  have hKq : scaledCutoff κ τ μ ^ (τ + 1) = scaledCutoff κ τ μ ^ τ * scaledCutoff κ τ μ :=
    Real.rpow_add_one hKpos.ne' τ
  have hgap : divisorGap γ τ κ μ = γ / (2 * π) / scaledCutoff κ τ μ ^ τ := by
    unfold divisorGap; rw [Real.rpow_neg hKpos.le]; ring
  refine ⟨⟨hK1, hK2, hKX⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (b)
    rw [hgap, stoppedRadius, div_div, le_div_iff₀ (by positivity)]
    have e : scaledCutoff κ τ μ * L * (D₀ * √μ) * (scaledCutoff κ τ μ ^ τ * 2) =
        (scaledCutoff κ τ μ ^ (τ + 1) * √μ) * (L * D₀) * 2 := by
      rw [hKq]; ring
    rw [e]
    have h1 : (scaledCutoff κ τ μ ^ (τ + 1) * √μ) * (L * D₀) * 2 ≤ κ ^ (τ + 1) * (L * D₀) * 2 := by
      gcongr
    have h2 : γ / (4 * π) * 2 = γ / (2 * π) := by field_simp; ring
    calc _ ≤ κ ^ (τ + 1) * (L * D₀) * 2 := h1
      _ = (L * D₀ * κ ^ (τ + 1)) * 2 := by ring
      _ ≤ γ / (4 * π) * 2 := by gcongr
      _ = γ / (2 * π) := h2
  · -- (c)
    have hc2 : KAM.NormalForm.conjExp 2 = 2 := by unfold KAM.NormalForm.conjExp; norm_num
    rw [hc2, hgap, stoppedRadius, perturbSize, div_mul_eq_mul_div, div_div,
      le_div_iff₀ (by positivity)]
    have hmu : μ = √μ * √μ := (Real.mul_self_sqrt hμ.le).symm
    have e : M₂ * μ * (scaledCutoff κ τ μ ^ τ * (2 ^ 7 * 2 * scaledCutoff κ τ μ)) =
        256 * M₂ * √μ * (scaledCutoff κ τ μ ^ (τ + 1) * √μ) := by
      rw [hKq]; nth_rewrite 1 [hmu]; ring
    rw [e]
    have hk2 : M₂ * κ ^ (τ + 1) ≤ γ * D₀ / (512 * π) := hκ2
    calc 256 * M₂ * √μ * (scaledCutoff κ τ μ ^ (τ + 1) * √μ)
        ≤ 256 * M₂ * √μ * κ ^ (τ + 1) := by gcongr
      _ = (M₂ * κ ^ (τ + 1)) * (256 * √μ) := by ring
      _ ≤ γ * D₀ / (512 * π) * (256 * √μ) := by gcongr
      _ = γ / (2 * π) * (D₀ * √μ) := by field_simp; ring
  · -- (d)
    have hsq3 : √μ ≤ B := by
      calc √μ ≤ √(B ^ 2) := Real.sqrt_le_sqrt hμ3
        _ = B := Real.sqrt_sq hBpos.le
    rw [stoppedRadius]
    have hBw : 64 * π * k * s * D₀ * B = w ^ 2 := by
      rw [hB]; field_simp
    calc 64 * π * k * s * (D₀ * √μ) = 64 * π * k * s * D₀ * √μ := by ring
      _ ≤ 64 * π * k * s * D₀ * B := by gcongr
      _ = w ^ 2 := hBw
  · -- (e)
    have h1 : π * s * E ≤ π * s * (κ * μ ^ (-scaleExponent τ)) := by gcongr
    have h2 : π * s * E = 2 * π * s + 6 := by rw [hE]; field_simp
    have h3 : 2 * π * s * (κ * μ ^ (-scaleExponent τ) / 2) ≤ 2 * π * s * scaledCutoff κ τ μ := by
      gcongr
    have h4 : 0 < 2 * π * s := by positivity
    nlinarith
  · -- (f)
    have hsq4 : √μ ≤ ρ / D₀ := by
      calc √μ ≤ √((ρ / D₀) ^ 2) := Real.sqrt_le_sqrt hμ4
        _ = ρ / D₀ := Real.sqrt_sq (by positivity)
    rw [stoppedRadius]
    rw [le_div_iff₀ hD] at hsq4
    linarith
  · -- (g)
    have hexp : Real.exp (π * s * κ / 6 * μ ^ (-scaleExponent τ)) ≤
        Real.exp (2 * π * scaledCutoff κ τ μ * s / 6) := by
      apply Real.exp_le_exp.mpr
      have h3 : 2 * π * s * (κ * μ ^ (-scaleExponent τ) / 2) ≤ 2 * π * s * scaledCutoff κ τ μ := by
        gcongr
      have : π * s * κ / 6 * μ ^ (-scaleExponent τ) =
          2 * π * s * (κ * μ ^ (-scaleExponent τ) / 2) / 6 := by ring
      rw [this]
      have : 2 * π * scaledCutoff κ τ μ * s / 6 = 2 * π * s * scaledCutoff κ τ μ / 6 := by ring
      rw [this]
      linarith
    have hsqle : μ ≤ √μ := by
      rw [Real.le_sqrt' hμ]
      nlinarith
    have hT : s * D₀ / (5 * M₂) ≤ s * stoppedRadius D₀ μ / (5 * perturbSize M₂ μ) := by
      rw [stoppedRadius, perturbSize, le_div_iff₀ (by positivity)]
      have : s * D₀ / (5 * M₂) * (5 * (M₂ * μ)) = s * D₀ * μ := by field_simp
      rw [this]
      have : 0 < s * D₀ := by positivity
      nlinarith
    exact mul_le_mul hT hexp (Real.exp_pos _).le (by unfold stoppedRadius perturbSize; positivity)

/-- **Diophantine to period-one nonresonance at the centre** (`LP:MAIN (5)`, radian to period-one
frequencies `ω/(2π)`).  The mode size is the `ℓ¹` size `KAM.Fourier.modeSize`, the same one used by
`KAM.NormalForm.zBall`. -/
theorem diophantine_to_period_one {n : ℕ} {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (ω : Fin n → ℝ)
    (hdio : ∀ k : Fin n → ℤ, k ≠ 0 →
      γ * KAM.Fourier.modeSize k ^ (-τ) ≤ |∑ i, (k i : ℝ) * ω i|)
    {K : ℝ} (hK : 1 ≤ K) {k : Fin n → ℤ} (hk : k ≠ 0) (hkK : KAM.Fourier.modeSize k ≤ K) :
    γ / (2 * π) * K ^ (-τ) ≤ |∑ i, (k i : ℝ) * (ω i / (2 * π))| := by
  have hπ := Real.pi_pos
  have hm1 : 1 ≤ KAM.Fourier.modeSize k := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
      have := Int.one_le_abs hi
      exact_mod_cast this
    calc (1 : ℝ) ≤ |(k i : ℝ)| := h1
      _ ≤ KAM.Fourier.modeSize k :=
        Finset.single_le_sum (f := fun j => |(k j : ℝ)|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
  have hmpos : 0 < KAM.Fourier.modeSize k := by linarith
  have hKneg : K ^ (-τ) ≤ KAM.Fourier.modeSize k ^ (-τ) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hmpos.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hmpos.le hkK hτ)
  have hdot : ∑ i, (k i : ℝ) * (ω i / (2 * π)) = (∑ i, (k i : ℝ) * ω i) / (2 * π) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdot, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc γ / (2 * π) * K ^ (-τ) ≤ γ / (2 * π) * KAM.Fourier.modeSize k ^ (-τ) := by gcongr
    _ = γ * KAM.Fourier.modeSize k ^ (-τ) / (2 * π) := by ring
    _ ≤ |∑ i, (k i : ℝ) * ω i| / (2 * π) := by gcongr; exact hdio k hk

/-- **Exponent corollary**: for `τ = n - 1/2`, `a = 1/(2n+1)`. -/
theorem scaleExponent_planar (n : ℕ) {τ : ℝ} (hτ : τ = (n : ℝ) - 1 / 2) :
    scaleExponent τ = 1 / (2 * (n : ℝ) + 1) := by
  unfold scaleExponent
  rw [hτ]
  congr 1
  ring

end KAM.Planetary.StrongAMD
