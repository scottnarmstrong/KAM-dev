/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Bracket
public import KAM.Canonical.Setting
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Iterated brackets in the weighted norm (`bpN:p5:adjoint`)

Blueprint-N Part 5, Lemma B.5 (iterated brackets).  For `φ ∈ O(r', s')`,
`u ∈ O(r, s)` with bounds `Φ`, `U` and losses `ρ < r`, `σ < s`, `r + ρ ≤ r'`, `s + σ ≤ s'`:
`|ad_φ^h u|_{r-ρ,s-σ} ≤ (2h²/(eρσ))^h (h!/(2h)!) Φ^h U`, hence
`|ad_φ^h u / h!|_{r-ρ,s-σ} ≤ (e η/4)^h U` with `η = 2Φ/(ρσ)`.

The proof splits the loss into `h` steps `κ = ρ/h`, `λ = σ/h` and applies `wbound_bracket`
(with `{ad^{i} u, φ} = -{φ, ad^{i} u}`) at each step; the product of the step constants is
`(2h²Φ/(eρσ))^h / ∏(h+1+k) = (2h²Φ/(eρσ))^h h!/(2h)!`.
-/

@[expose] public noncomputable section

open Set Metric Finset

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ}

/-! ### Scalar multiples in the weighted norm -/

theorem coeff_const_mul (c : ℂ) (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (I : Fin n → ℂ)
    (k : Fin n → ℤ) : coeff (fun z => c * u z) I k = c * coeff u I k := by
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  have : ∀ x : Fin n → ℝ, KAM.character (-k) (fun j => (x j : ℂ)) •
      (c * u (fun j => (x j : ℂ), I)) =
      c * (KAM.character (-k) (fun j => (x j : ℂ)) • u (fun j => (x j : ℂ), I)) := by
    intro x
    simp only [smul_eq_mul]
    ring
  simp_rw [this]
  exact MeasureTheory.integral_const_mul c _

theorem inClass_const_mul {D : Set (Fin n → ℂ)} {r s : ℝ} (c : ℂ)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u) :
    InClass D r s (fun z => c * u z) :=
  ⟨hu.differentiableOn.const_mul c, fun j z hz => by simp only [hu.periodic j z hz]⟩

theorem wbound_const_mul {D : Set (Fin n → ℂ)} {r s M : ℝ} (c : ℂ)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : WBound D r s u M) :
    WBound D r s (fun z => c * u z) (‖c‖ * M) := by
  intro I hI
  obtain ⟨h1, h2⟩ := hu I hI
  have hw : wsum (fun z => c * u z) s I = ‖c‖ * wsum u s I := by
    unfold wsum
    simp_rw [coeff_const_mul, norm_mul, mul_assoc]
    exact tsum_mul_left
  refine ⟨?_, ?_⟩
  · unfold WSummable at h1 ⊢
    simp_rw [coeff_const_mul, norm_mul, mul_assoc]
    exact h1.mul_left _
  · rw [hw]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/-! ### The one-step estimate -/

theorem adPow_succ_eq_neg (φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (i : ℕ) :
    adPow φ (i + 1) u = fun z => (-1 : ℂ) * poissonBracket φ (adPow φ i u) z := by
  funext z
  rw [adPow, poissonBracket_antisymm]
  ring

/-- The constant of one step of `wbound_bracket` is at most `2h²/(e ρ σ (h+1+i))`. -/
theorem step_const_le {r r' s s' ρ σ : ℝ} {h i : ℕ} (hρ : 0 < ρ) (hσ : 0 < σ) (hh : 1 ≤ h)
    (hr : r + ρ ≤ r') (hs : s + σ ≤ s') :
    1 / Real.exp 1 * (1 / ((r' - (r - i * (ρ / h)) + ρ / h) * (σ / h)) +
        1 / ((s' - (s - i * (σ / h)) + σ / h) * (ρ / h))) ≤
      2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ * ((h : ℝ) + 1 + i)) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hκ : 0 < ρ / h := by positivity
  have hl : 0 < σ / h := by positivity
  have hhi : (0 : ℝ) < h + 1 + i := by positivity
  have hA : ((h : ℝ) + 1 + i) * (ρ / h) ≤ r' - (r - i * (ρ / h)) + ρ / h := by
    have : (h : ℝ) * (ρ / h) = ρ := by field_simp
    nlinarith
  have hB : ((h : ℝ) + 1 + i) * (σ / h) ≤ s' - (s - i * (σ / h)) + σ / h := by
    have : (h : ℝ) * (σ / h) = σ := by field_simp
    nlinarith
  have h1 : 1 / ((r' - (r - i * (ρ / h)) + ρ / h) * (σ / h)) ≤
      1 / (((h : ℝ) + 1 + i) * (ρ / h) * (σ / h)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hA hl.le)
  have h2 : 1 / ((s' - (s - i * (σ / h)) + σ / h) * (ρ / h)) ≤
      1 / (((h : ℝ) + 1 + i) * (σ / h) * (ρ / h)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hB hκ.le)
  have h3 : 1 / (((h : ℝ) + 1 + i) * (ρ / h) * (σ / h)) =
      (h : ℝ) ^ 2 / (((h : ℝ) + 1 + i) * ρ * σ) := by field_simp
  have h4 : 1 / (((h : ℝ) + 1 + i) * (σ / h) * (ρ / h)) =
      (h : ℝ) ^ 2 / (((h : ℝ) + 1 + i) * ρ * σ) := by field_simp
  have h5 : 1 / Real.exp 1 * ((h : ℝ) ^ 2 / (((h : ℝ) + 1 + i) * ρ * σ) +
      (h : ℝ) ^ 2 / (((h : ℝ) + 1 + i) * ρ * σ)) =
      2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ * ((h : ℝ) + 1 + i)) := by field_simp; ring
  rw [← h5]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact add_le_add (h1.trans_eq h3) (h2.trans_eq h4)

/-! ### The induction -/

/-- The step constants `q k = 2h²Φ/(eρσ(h+1+k))`. -/
def stepConst (Φ ρ σ : ℝ) (h k : ℕ) : ℝ :=
  2 * (h : ℝ) ^ 2 * Φ / (Real.exp 1 * ρ * σ * ((h : ℝ) + 1 + k))

theorem stepConst_nonneg {Φ ρ σ : ℝ} (hΦ : 0 ≤ Φ) (hρ : 0 < ρ) (hσ : 0 < σ) (h k : ℕ) :
    0 ≤ stepConst Φ ρ σ h k := by
  unfold stepConst
  have := Real.exp_pos 1
  positivity

theorem adjoint_induction {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ}
    {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : InClass D r' s' φ) (hu : InClass D r s u)
    (hbφ : WBound D r' s' φ Φ) (hbu : WBound D r s u U) (hΦ : 0 ≤ Φ) (hU : 0 ≤ U)
    (hρ : 0 < ρ) (hσ : 0 < σ) (hρr : ρ < r) (hσs : σ < s) (hr : r + ρ ≤ r') (hs : s + σ ≤ s')
    {h : ℕ} (hh : 1 ≤ h) :
    ∀ i : ℕ, i ≤ h →
      InClass D (r - i * (ρ / h)) (s - i * (σ / h)) (adPow φ i u) ∧
      WBound D (r - i * (ρ / h)) (s - i * (σ / h)) (adPow φ i u)
        ((∏ k ∈ range i, stepConst Φ ρ σ h k) * U) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hκ : 0 < ρ / h := by positivity
  have hl : 0 < σ / h := by positivity
  intro i
  induction i with
  | zero => intro _; simpa [adPow] using ⟨hu, hbu⟩
  | succ i ih =>
    intro hi
    obtain ⟨hc, hb⟩ := ih (by omega)
    have hi' : ((i : ℝ) + 1) ≤ h := by exact_mod_cast hi
    have hρh : (h : ℝ) * (ρ / h) = ρ := by field_simp
    have hσh : (h : ℝ) * (σ / h) = σ := by field_simp
    have hκr : ρ / h < r - i * (ρ / h) := by nlinarith
    have hlσ : σ / h < s - i * (σ / h) := by nlinarith
    obtain ⟨hc', hb'⟩ := wbound_bracket hφ hc hbφ hb hκ hκr hl hlσ
      (by nlinarith) (by nlinarith)
    have hK := step_const_le (r := r) (r' := r') (s := s) (s' := s') hρ hσ hh hr hs (i := i)
    have hnn : 0 ≤ Φ * ((∏ k ∈ range i, stepConst Φ ρ σ h k) * U) :=
      mul_nonneg hΦ (mul_nonneg (prod_nonneg fun k _ => stepConst_nonneg hΦ hρ hσ h k) hU)
    have e1 : r - ((i + 1 : ℕ) : ℝ) * (ρ / h) = r - i * (ρ / h) - ρ / h := by push_cast; ring
    have e2 : s - ((i + 1 : ℕ) : ℝ) * (σ / h) = s - i * (σ / h) - σ / h := by push_cast; ring
    rw [e1, e2, adPow_succ_eq_neg]
    refine ⟨inClass_const_mul _ hc', ?_⟩
    refine (wbound_const_mul (-1) hb').mono le_rfl le_rfl ?_
    rw [norm_neg, norm_one, one_mul, prod_range_succ]
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_right hK hnn) (le_of_eq ?_))
    · ring
    · unfold stepConst; ring

/-! ### The product and Stirling-type estimates -/

theorem prod_stepConst {Φ ρ σ : ℝ} (h : ℕ) :
    ∏ k ∈ range h, stepConst Φ ρ σ h k =
      (2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ)) ^ h * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) *
        Φ ^ h := by
  have hfac : (h.factorial : ℝ) * ∏ k ∈ range h, ((h : ℝ) + 1 + k) = ((2 * h).factorial : ℝ) := by
    have := Nat.factorial_mul_ascFactorial h h
    rw [Nat.ascFactorial_eq_prod_range] at this
    have h2 : (2 * h).factorial = h.factorial * ∏ k ∈ range h, (h + 1 + k) := by
      rw [two_mul]; exact this.symm
    rw [h2]; push_cast; ring_nf
  have hpos : (0 : ℝ) < ∏ k ∈ range h, ((h : ℝ) + 1 + k) :=
    prod_pos fun k _ => by positivity
  have hf0 : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have hdiv : (h.factorial : ℝ) / ((2 * h).factorial : ℝ) =
      1 / ∏ k ∈ range h, ((h : ℝ) + 1 + k) := by
    rw [← hfac]; field_simp
  rw [hdiv]
  unfold stepConst
  have : ∀ k ∈ range h, 2 * (h : ℝ) ^ 2 * Φ / (Real.exp 1 * ρ * σ * ((h : ℝ) + 1 + k)) =
      (2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ) * Φ) * (1 / ((h : ℝ) + 1 + k)) := by
    intro k _
    field_simp
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_range, mul_pow]
  simp only [one_div, prod_inv_distrib]
  ring

theorem factorial_ge (N : ℕ) : ((N : ℝ) / Real.exp 1) ^ N ≤ (N.factorial : ℝ) := by
  have := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (by positivity) N
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf] at this
  have e : Real.exp (N : ℝ) = Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul]; simp
  rw [e] at this
  rw [div_pow, div_le_iff₀ (by positivity)]
  linarith

/-- The numerical comparison of the two bounds of `adjoint_bound`. -/
theorem final_estimate {Φ ρ σ U : ℝ} (hΦ : 0 ≤ Φ) (hU : 0 ≤ U) (hρ : 0 < ρ) (hσ : 0 < σ)
    {h : ℕ} (hh : 1 ≤ h) :
    ((h.factorial : ℝ))⁻¹ *
        ((2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ)) ^ h
          * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) *
          Φ ^ h * U) ≤
      (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ h * U := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hf0 : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have hf2 : (0 : ℝ) < (2 * h).factorial := by exact_mod_cast (2 * h).factorial_pos
  set X : ℝ := 2 * (h : ℝ) ^ 2 * Φ / (Real.exp 1 * ρ * σ) with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : ((h.factorial : ℝ))⁻¹ *
        ((2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ)) ^ h
          * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) *
          Φ ^ h * U) = X ^ h * (1 / ((2 * h).factorial : ℝ)) * U := by
    simp only [hX, div_pow, mul_pow]
    field_simp
  have h2 : Real.exp 1 * (2 * Φ / (ρ * σ)) / 4 = X * (Real.exp 1 / (2 * h)) ^ 2 := by
    rw [hX]; field_simp; ring
  have h3 : 1 / ((2 * h).factorial : ℝ) ≤ (Real.exp 1 / (2 * h)) ^ (2 * h) := by
    have := factorial_ge (2 * h)
    push_cast at this
    have h4 := one_div_le_one_div_of_le (by positivity) this
    rwa [div_pow, one_div_div, ← div_pow] at h4
  rw [h1, h2, mul_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hU

/-- `bpN:p5:adjoint` (`Canonical/Adjoint.lean`). -/
theorem adjoint_bound {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ}
    {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : InClass D r' s' φ) (hu : InClass D r s u)
    (hbφ : WBound D r' s' φ Φ) (hbu : WBound D r s u U) (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ)
    (hσs : σ < s) (hr : r + ρ ≤ r') (hs : s + σ ≤ s') {h : ℕ} (hh : 1 ≤ h) :
    InClass D (r - ρ) (s - σ) (adPow φ h u) ∧
    WBound D (r - ρ) (s - σ) (adPow φ h u)
      ((2 * (h : ℝ) ^ 2 / (Real.exp 1 * ρ * σ)) ^ h
        * ((h.factorial : ℝ) / ((2 * h).factorial : ℝ)) *
        Φ ^ h * U) ∧
    WBound D (r - ρ) (s - σ) (fun z => ((h.factorial : ℂ)⁻¹) * adPow φ h u z)
      ((Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ h * U) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hρh : (h : ℝ) * (ρ / h) = ρ := by field_simp
  have hσh : (h : ℝ) * (σ / h) = σ := by field_simp
  by_cases hD : D.Nonempty
  · obtain ⟨I', hI'⟩ := hD
    have hI1 : I' ∈ polyNbhd D r := ⟨I', hI', by simpa using hρr.trans' hρ⟩
    have hI2 : I' ∈ polyNbhd D r' := polyNbhd_mono (by linarith) hI1
    have hΦ : 0 ≤ Φ := (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans
      (hbφ I' hI2).2
    have hU : 0 ≤ U := (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans
      (hbu I' hI1).2
    obtain ⟨hc, hb⟩ := adjoint_induction hφ hu hbφ hbu hΦ hU hρ hσ hρr hσs hr hs hh h le_rfl
    rw [hρh, hσh, prod_stepConst] at *
    refine ⟨hc, hb, ?_⟩
    refine (wbound_const_mul _ hb).mono le_rfl le_rfl ?_
    rw [norm_inv, Complex.norm_natCast]
    exact final_estimate hΦ hU hρ hσ hh
  · have hD' : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hD
    have hvac : ∀ (x : ℝ), polyNbhd D x = ∅ := fun x => by
      ext I; simp [polyNbhd, hD']
    have hvac' : ∀ (x y : ℝ) (w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (M : ℝ), WBound D x y w M :=
      fun x y w M I hI => by rw [hvac] at hI; exact absurd hI (Set.notMem_empty _)
    obtain ⟨hc, -⟩ := adjoint_induction hφ hu (hvac' _ _ _ 0)
      (hvac' _ _ _ 0) le_rfl le_rfl hρ hσ hρr
      hσs hr hs hh h le_rfl
    rw [hρh, hσh] at hc
    exact ⟨hc, hvac' _ _ _ _, hvac' _ _ _ _⟩

end KAM.Canonical
