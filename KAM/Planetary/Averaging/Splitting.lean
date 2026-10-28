/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Direct
public import KAM.Canonical.TransformSeries
public import KAM.Canonical.Adjoint

/-!
# P Part 2: splitting of the generating function and componentwise displacement (`bpP:p2:split`)

`firstGen` is the part `φ⁽¹⁾` of `homGen K {0} h f` supported on the modes with `k₁ ≠ 0`;
`directMap` is the time-one map of `homGen K {0} h f`, i.e. the N `iterMap` with `Λ = {0}`.
`split` follows the three source steps: the coefficient bounds (`stepP:p2:sp-coef`), the
field bounds on `𝒟_{r-ρ,s-σ}` (`stepP:p2:sp-field`), and the mean value inequality along the
trajectory (`stepP:p2:sp-int`). Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-10.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def firstGen {a b : ℕ} (K : ℝ) (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : CHam (a + b) :=
  projMode {k | firstBlock (b := b) k ≠ 0} (homGen K {0} h f)

def directMap {n : ℕ} (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam n) : CPhase n → CPhase n :=
  flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f)) (Dom n D (r - ρ) (s - σ)) 1

section Coefficients

variable {n : ℕ}

private theorem finite_zBall' (K : ℝ) : (zBall n K).Finite := by
  refine (KAM.modeCutoff n ⌈K⌉₊).finite_toSet.subset fun k hk => ?_
  have hk' : KAM.Fourier.modeSize k ≤ K := hk
  exact KAM.mem_modeCutoff.2 (hk'.trans (Nat.le_ceil K))

/-- The coefficient `1_{Z_K \ {0}}(k) f̂ₖ(I)/(2πi k·ω(I))` of `homGen K {0} h f`. -/
private def genC (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (k : Fin n → ℤ) (I : Fin n → ℂ) : ℂ :=
  (zBall n K \ {0}).indicator
    (fun k => coeff f I k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (freq h I))) k

private theorem homGen_eq_series (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) :
    homGen K {0} h f = fourierSeries (genC K h f) := by
  funext z
  unfold homGen fourierSeries genC
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ zBall n K \ {0} <;> simp [hk]

private theorem summable_genC (K s : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (I : Fin n → ℂ) :
    Summable fun k => ‖genC K h f k I‖ * modeWeight s k := by
  refine summable_of_ne_finset_zero (s := (finite_zBall' (n := n) K).toFinset) fun k hk => ?_
  have : k ∉ zBall n K \ {0} := fun h' => hk (by simpa using h'.1)
  simp [genC, this]

private theorem coeff_homGen {s : ℝ} (hs : 0 < s) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n)
    (I : Fin n → ℂ) (k : Fin n → ℤ) : coeff (homGen K {0} h f) I k = genC K h f k I := by
  rw [homGen_eq_series]
  exact KAM.torusCoeff_fourierSum hs.le (summable_genC K s h f I) k

private theorem norm_div_divisor_le {c d : ℂ} {α q : ℝ} (hα : 0 < α) (hq : 1 ≤ q)
    (hd : α / q ≤ ‖d‖) :
    ‖c / (2 * (Real.pi : ℂ) * Complex.I * d)‖ ≤ q / (2 * Real.pi * α) * ‖c‖ := by
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < ‖d‖ := lt_of_lt_of_le (div_pos hα hq0) hd
  have hn : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * d‖ = 2 * Real.pi * ‖d‖ := by
    simp [abs_of_pos Real.pi_pos]
  rw [norm_div, hn]
  have hπ := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have h1 : α ≤ q * ‖d‖ := by
    have := (div_le_iff₀ hq0).1 hd
    linarith
  have : q / (2 * Real.pi * α) * ‖c‖ * (2 * Real.pi * ‖d‖) = ‖c‖ * (q * ‖d‖ / α) := by
    field_simp
  rw [this]
  have h5 : 1 ≤ q * ‖d‖ / α := by rwa [le_div_iff₀ hα, one_mul]
  nlinarith [norm_nonneg c]

end Coefficients

section Split

variable {a b : ℕ} {D : Set (Fin (a + b) → ℂ)} {r s K α₁ α₂ q δ : ℝ}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- `stepP:p2:sp-coef`, class and weighted bound of `φ⁽¹⁾`. -/
theorem firstGen_class_bound (H : DirectHyp D r s K α₂ q δ {0} h f) (hα : α₂ ≤ α₁)
    (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h) :
    InClass D r s (firstGen K h f) ∧ WBound D r s (firstGen K h f) (q * δ / (2 * π * α₁)) := by
  obtain ⟨c1, c2, -⟩ := direct H
  obtain ⟨p1, p2, p3, -⟩ := projections H.s_pos c1 c2 {k : Fin (a + b) → ℤ | firstBlock (b := b) k ≠ 0}
  refine ⟨p1, fun I hI => ?_⟩
  have hα₁ : 0 < α₁ := lt_of_lt_of_le H.α_pos hα
  have hc0 : 0 ≤ q / (2 * π * α₁) := by
    have := H.q_ge
    have := Real.pi_pos
    positivity
  have hle : ∀ k, ‖coeff (firstGen K h f) I k‖ * modeWeight s k ≤
      q / (2 * π * α₁) * (‖coeff f I k‖ * modeWeight s k) := fun k => by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    show ‖coeff (projMode _ (homGen K {0} h f)) I k‖ ≤ _
    rw [p2 I hI k]
    by_cases hk : k ∈ {k : Fin (a + b) → ℤ | firstBlock (b := b) k ≠ 0}
    · rw [Set.indicator_of_mem hk, coeff_homGen H.s_pos]
      by_cases hZ : k ∈ zBall (a + b) K \ {0}
      · simp only [genC, Set.indicator_of_mem hZ]
        have hk' : ¬ firstBlock (b := b) k = 0 := hk
        have hk0 : k ≠ 0 := fun h0 => hk' (by subst h0; rfl)
        have hdk := hd I hI k hk0 hZ.1
        simp only [hk', ↓reduceIte] at hdk
        exact norm_div_divisor_le hα₁ H.q_ge hdk
      · simp only [genC, Set.indicator_of_notMem hZ, norm_zero]
        exact mul_nonneg hc0 (norm_nonneg _)
    · rw [Set.indicator_of_notMem hk, norm_zero]
      exact mul_nonneg hc0 (norm_nonneg _)
  obtain ⟨h1, h2⟩ := H.bound I hI
  have h1' : Summable fun k => q / (2 * π * α₁) * (‖coeff f I k‖ * modeWeight s k) := h1.mul_left _
  have hs' : Summable (fun k => ‖coeff (firstGen K h f) I k‖ * modeWeight s k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hle h1'
  refine ⟨hs', (hs'.tsum_le_tsum hle h1').trans ?_⟩
  rw [tsum_mul_left]
  calc q / (2 * π * α₁) * ∑' k, ‖coeff f I k‖ * modeWeight s k
      ≤ q / (2 * π * α₁) * δ := mul_le_mul_of_nonneg_left h2 hc0
    _ = q * δ / (2 * π * α₁) := by ring

end Split

end KAM.Planetary

end
