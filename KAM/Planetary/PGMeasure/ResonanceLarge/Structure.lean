/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PG.Setting

/-!
# P Part 4: structure of the large modes `𝒦_B` (`stepP:p4:dm-Bstruct`)

For an integer vector `k = (k₁, k₂)` write `|k|₁` for its `ℓ¹` norm and `‖k₁‖`, `‖k₂‖` for the max
norms of its blocks. The *large modes* are those with `k₁ ≠ 0` and `μ Λ_N Λ_g |k|₁ > ‖k₁‖/2`
(the complement of `𝒦_A`). `large_mode_structure` proves `|k|₁ > (2 μ Λ_N Λ_g)⁻¹`,
`|k₂|₁ > M |k₁|₁` with `M = 2 b Λ_N L_β`, hence `|k|₁ < 2 b ‖k₂‖` and
`Λ_N |k₁|₁ ≤ ‖k₂‖/(2 L_β)`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Planetary

variable {a b : ℕ}

/-- The fast block of an integer vector, as a real vector. -/
def kFast (k : Fin (a+b) → ℤ) : Fin a → ℝ := fun i => (k (Fin.castAdd b i) : ℝ)

/-- The slow block of an integer vector, as a real vector. -/
def kSlow (k : Fin (a+b) → ℤ) : Fin b → ℝ := fun i => (k (Fin.natAdd a i) : ℝ)

/-- The `ℓ¹` norm `|k|₁` as a real number. -/
def l1 (k : Fin (a+b) → ℤ) : ℝ := ∑ i, |(k i : ℝ)|

/-- The large modes: `k₁ ≠ 0` and `μ Λ_N Λ_g |k|₁ > ‖k₁‖/2`. -/
def largeModes (a b : ℕ) (mu LN Lg : ℝ) : Set (Fin (a+b) → ℤ) :=
  {k | blockFast k ≠ 0 ∧ ‖kFast k‖/2 < mu*LN*Lg*l1 k}

theorem l1_split (k : Fin (a+b) → ℤ) :
    l1 k = ∑ i, |kFast k i| + ∑ i, |kSlow k i| := by
  unfold l1 kFast kSlow
  exact Fin.sum_univ_add (fun i => |(k i : ℝ)|)

theorem sum_abs_le_mul_norm {n : ℕ} (v : Fin n → ℝ) : ∑ i, |v i| ≤ n * ‖v‖ := by
  calc ∑ i, |v i| ≤ ∑ _i : Fin n, ‖v‖ :=
        sum_le_sum fun i _ => by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    _ = n * ‖v‖ := by simp

theorem l1_nonneg (k : Fin (a+b) → ℤ) : 0 ≤ l1 k := sum_nonneg fun _ _ => abs_nonneg _

theorem one_le_norm_kFast {k : Fin (a+b) → ℤ} (hk : blockFast k ≠ 0) : 1 ≤ ‖kFast k‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k (Fin.castAdd b i) : ℝ)| := by
    have : (1 : ℤ) ≤ |k (Fin.castAdd b i)| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (by simpa [kFast, Real.norm_eq_abs] using norm_le_pi_norm (kFast k) i)

/-- Structure of the large modes (`stepP:p4:dm-Bstruct`, (i), (ii) and consequences). -/
theorem large_mode_structure {mu LN LB Lg : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmu : 0 < mu) (hLN : 1 ≤ LN) (hLB : 1 ≤ LB) (hLg : 1 ≤ Lg)
    (hsmall : mu ≤ (2*(1+2*b*LN*LB)*a*LN*Lg)⁻¹) {k : Fin (a+b) → ℤ}
    (hk : k ∈ largeModes a b mu LN Lg) :
    1 < 2*mu*LN*Lg*l1 k ∧ (2*b*LN*LB) * ∑ i, |kFast k i| < ∑ i, |kSlow k i| ∧
      l1 k < 2*b*‖kSlow k‖ ∧ LN * ∑ i, |kFast k i| ≤ ‖kSlow k‖/(2*LB) := by
  obtain ⟨hk1, hlarge⟩ := hk
  have h1 := one_le_norm_kFast hk1
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hM : 2 ≤ 2*(b:ℝ)*LN*LB := by
    have : (1:ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [mul_le_mul hLN hLB zero_le_one (by linarith : (0:ℝ) ≤ LN)]
  have hpos : 0 < 2*(1+2*(b:ℝ)*LN*LB)*a*LN*Lg := by positivity
  have hl1 := l1_split k
  have hF := sum_abs_le_mul_norm (kFast k)
  have hS := sum_abs_le_mul_norm (kSlow k)
  have hSn : 0 ≤ ∑ i, |kSlow k i| := sum_nonneg fun _ _ => abs_nonneg _
  have hFn : 0 ≤ ∑ i, |kFast k i| := sum_nonneg fun _ _ => abs_nonneg _
  have hii : (2*b*LN*LB) * ∑ i, |kFast k i| < ∑ i, |kSlow k i| := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    have hl : l1 k ≤ (1 + 2*b*LN*LB) * (a * ‖kFast k‖) := by
      rw [hl1]; nlinarith
    have hmu' : mu * (2*(1+2*b*LN*LB)*a*LN*Lg) ≤ 1 := by
      calc mu * (2*(1+2*b*LN*LB)*a*LN*Lg) ≤ (2*(1+2*b*LN*LB)*a*LN*Lg)⁻¹ *
            (2*(1+2*b*LN*LB)*a*LN*Lg) := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have : mu*LN*Lg*l1 k ≤ ‖kFast k‖/2 := by
      have hn : 0 ≤ ‖kFast k‖ := norm_nonneg _
      calc mu*LN*Lg*l1 k ≤ mu*LN*Lg*((1 + 2*b*LN*LB) * (a * ‖kFast k‖)) := by gcongr
        _ = (mu * (2*(1+2*b*LN*LB)*a*LN*Lg)) * (‖kFast k‖/2) := by ring
        _ ≤ 1 * (‖kFast k‖/2) := by gcongr
        _ = _ := one_mul _
    linarith
  have hSpos : 0 < ∑ i, |kSlow k i| := by nlinarith
  have hnS : 0 < ‖kSlow k‖ := by
    by_contra hc
    have : ‖kSlow k‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [this] at hS; linarith
  refine ⟨by nlinarith, hii, ?_, ?_⟩
  · have hF2 : 2 * ∑ i, |kFast k i| ≤ ∑ i, |kSlow k i| := by nlinarith
    rw [hl1]; nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have hF3 : (2*b*LN*LB) * ∑ i, |kFast k i| ≤ b * ‖kSlow k‖ := by nlinarith
    nlinarith

end KAM.Planetary

end
