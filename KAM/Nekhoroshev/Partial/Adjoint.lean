/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Bracket
import Mathlib.Analysis.Complex.ExponentialBounds
import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Iterated brackets (`bpN:p11:adjoint`, Part 11, package N11-E2)

`adjoint`: for `φ ∈ 𝒪^e_{R',s'}`, `u ∈ 𝒪^e_{R,s}` with `R+ρ ≤ R'`, `s+σ ≤ s'` and `(SL)_{ρ,σ}`,
`ad^j_φ u ∈ 𝒪^e_{R-ρ,s-σ}` and `(1/j!) |ad^j_φ u|_{R-ρ,s-σ} ≤ (e² η/8)^j |u|_{R,s}` with
`η = 2|φ|/(ρσ)`.

The proof follows the source: with `κ = ρ/j`, `λ = σ/j`, `R_i = R - iκ`, `s_i = s - iλ`
(`ad-setup`), the extended bracket estimate gives `|ad^i u|_{R_i,s_i} ≤ |φ| |ad^{i-1} u| /
((j+i)κλ)` (`ad-step`, the lemma `ad_step`), the product of the `j` factors is
`(V/(κλ))^j j!/(2j)!` (`ad-prod`) and `(2j)! ≥ (2j/e)^{2j}` finishes.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

/-! ### A scalar multiple of a bounded class function -/

private theorem continuous_slice' {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s) (hu : InClass D r s u) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) : Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

private theorem wbound_adjoint_const_mul {m : ℕ} {D : Set (Fin m → ℂ)} {r s M : ℝ}
    {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (a : ℂ) (hs : 0 < s) (hf : InClass D r s f)
    (hb : WBound D r s f M) : WBound D r s (fun z => a * f z) (‖a‖ * M) := by
  intro I hI
  have hc : Continuous fun x : Fin n → ℝ => f (fun l => (x l : ℂ), I) :=
    continuous_slice' hs hf hI
  have hcoeff : ∀ k, coeff (fun z => a * f z) I k = a * coeff f I k := fun k => by
    have := KAM.torusCoeff_finset_sum_mul (Finset.univ : Finset Unit)
      (f := fun _ => fun x : Fin n → ℝ => f (fun l => (x l : ℂ), I)) (fun _ => hc)
      (fun _ => a) k
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    exact this
  obtain ⟨h1, h2⟩ := hb I hI
  have hterm : ∀ k, ‖coeff (fun z => a * f z) I k‖ * modeWeight s k =
      ‖a‖ * (‖coeff f I k‖ * modeWeight s k) := fun k => by
    rw [hcoeff, norm_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, hterm] using h1.mul_left ‖a‖
  · unfold wsum
    simp only [hterm]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/-! ### One step -/

private theorem step_const {c κ l m R0 R ρ s0 s σ : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) (hl : 0 < l)
    (hm : 0 < m) (h1 : R0 - R + ρ = κ) (h2 : s0 - s + σ = l) (hρ' : m * κ ≤ ρ)
    (hσ' : m * l ≤ σ) (hSL : 16 * k * c * l ≤ κ) :
    (Real.exp 1)⁻¹ * (1 / ((R0 - R + ρ) * σ) + 1 / ((s0 - s + σ) * ρ)) +
      2 * k * c / ((R0 - R + ρ) * ρ) ≤ 1 / (m * κ * l) := by
  rw [h1, h2]
  have hρp : 0 < ρ := lt_of_lt_of_le (by positivity) hρ'
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ'
  have hX : 0 < 1 / (m * κ * l) := by positivity
  have t1 : 1 / (κ * σ) ≤ 1 / (m * κ * l) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left hσ' hκ.le]
  have t2 : 1 / (l * ρ) ≤ 1 / (m * κ * l) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left hρ' hl.le]
  have t3 : 2 * k * c / (κ * ρ) ≤ (1 / 8) * (1 / (m * κ * l)) := by
    rw [div_le_iff₀ (by positivity)]
    have h : (1 / 8) * (1 / (m * κ * l)) * (κ * ρ) = ρ / (8 * m * l) := by field_simp
    rw [h, le_div_iff₀ (by positivity)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := mul_le_mul_of_nonneg_left hρ' (mul_nonneg (mul_nonneg hk hc) hl.le)
    nlinarith
  have hinv : (Real.exp 1)⁻¹ ≤ 3 / 8 := by
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hsum := add_le_add t1 t2
  have hmul := mul_le_mul hinv hsum (add_pos (one_div_pos.2 (by positivity))
    (one_div_pos.2 (by positivity))).le (by norm_num)
  nlinarith

private theorem ad_step (b : PartialBlock n k) {R' s' R0 s0 R1 s1 κ l m U V : ℝ}
    {φ v : EC n k → ℂ} (hR1 : 0 < R1) (hs1 : 0 < s1) (hκ : 0 < κ) (hl : 0 < l) (hm : 0 < m)
    (hR : R0 - R1 = κ) (hs : s0 - s1 = l) (hR' : m * κ ≤ R' - R1) (hs' : m * l ≤ s' - s1)
    (hSL : 16 * k * b.c * l ≤ κ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hφ : InClass b.base R' s' φ) (hφb : WBound b.base R' s' φ V)
    (hv : InClass b.base R0 s0 v) (hvb : WBound b.base R0 s0 v U) :
    InClass b.base R1 s1 (extBracket b.c v φ) ∧
      WBound b.base R1 s1 (extBracket b.c v φ) (1 / (m * κ * l) * U * V) := by
  have hc : 0 ≤ b.c := div_nonneg (by positivity) (sq_nonneg _)
  have hρ : 0 < R' - R1 := lt_of_lt_of_le (by positivity) hR'
  have hσ : 0 < s' - s1 := lt_of_lt_of_le (by positivity) hs'
  obtain ⟨hcl, hwb⟩ := bracket b hρ (by linarith) hσ (by linarith) (R0 := R0) (s0 := s0)
    (by linarith) (by linarith) hv hφ hU hV hvb hφb
  rw [sub_sub_cancel, sub_sub_cancel] at hcl hwb
  refine ⟨hcl, hwb.mono le_rfl le_rfl ?_⟩
  have hK := step_const (k := k) hc hκ hl hm (R0 := R0) (R := R') (ρ := R' - R1) (s0 := s0)
    (s := s') (σ := s' - s1) (by linarith) (by linarith) hR' hs' hSL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hU) hV

/-! ### The iteration -/

private theorem ad_iter (b : PartialBlock n k) {R' s' R s ρ σ U V : ℝ} {φ u : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hRR : R + ρ ≤ R') (hss : s + σ ≤ s') (hSL : slowLoss b.c ρ σ k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : InClass b.base R' s' φ) (hu : InClass b.base R s u)
    (hφb : WBound b.base R' s' φ V) (hub : WBound b.base R s u U) (j : ℕ) (hj : 1 ≤ j) :
    ∀ i : ℕ, i ≤ j →
      InClass b.base (R - i * (ρ / j)) (s - i * (σ / j)) (extAd b.c φ i u) ∧
      WBound b.base (R - i * (ρ / j)) (s - i * (σ / j)) (extAd b.c φ i u)
        ((V / ((ρ / j) * (σ / j))) ^ i * ((j.factorial : ℝ) / (j + i).factorial) * U) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hκ : 0 < ρ / j := by positivity
  have hl : 0 < σ / j := by positivity
  have hSL' : 16 * k * b.c * (σ / j) ≤ ρ / j := by
    unfold slowLoss at hSL
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hSL hj0.le
  intro i
  induction i with
  | zero =>
    intro _
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    simp only [extAd, Nat.cast_zero, zero_mul, sub_zero, pow_zero, Nat.add_zero]
    rw [one_mul, div_self hf, one_mul]
    exact ⟨hu, hub⟩
  | succ i ih =>
    intro hi
    obtain ⟨hic, hib⟩ := ih (by omega)
    have hi1 : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hi
    have hmulle : ((i + 1 : ℕ) : ℝ) * (ρ / j) ≤ ρ := by
      calc ((i + 1 : ℕ) : ℝ) * (ρ / j) ≤ j * (ρ / j) :=
            mul_le_mul_of_nonneg_right hi1 hκ.le
        _ = ρ := by field_simp
    have hmulle' : ((i + 1 : ℕ) : ℝ) * (σ / j) ≤ σ := by
      calc ((i + 1 : ℕ) : ℝ) * (σ / j) ≤ j * (σ / j) :=
            mul_le_mul_of_nonneg_right hi1 hl.le
        _ = σ := by field_simp
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hρj : (j : ℝ) * (ρ / j) = ρ := by field_simp
    have hσj : (j : ℝ) * (σ / j) = σ := by field_simp
    have hUi : 0 ≤ (V / ((ρ / j) * (σ / j))) ^ i * ((j.factorial : ℝ) / (j + i).factorial) * U :=
      by positivity
    have hm : (0 : ℝ) < j + i + 1 := by positivity
    have hstep := ad_step b (R' := R') (s' := s') (R0 := R - i * (ρ / j))
      (s0 := s - i * (σ / j)) (R1 := R - ((i + 1 : ℕ) : ℝ) * (ρ / j))
      (s1 := s - ((i + 1 : ℕ) : ℝ) * (σ / j)) (κ := ρ / j) (l := σ / j)
      (m := (j : ℝ) + i + 1) (by linarith) (by linarith) hκ hl hm
      (by push_cast; ring) (by push_cast; ring) (by push_cast at hmulle ⊢; linarith [hρj])
      (by push_cast at hmulle' ⊢; linarith [hσj]) hSL' hUi hV hφ hφb hic hib
    refine ⟨hstep.1, hstep.2.mono le_rfl le_rfl (le_of_eq ?_)⟩
    have hfac : ((j + (i + 1)).factorial : ℝ) = ((j + i).factorial : ℝ) * ((j : ℝ) + i + 1) := by
      rw [← add_assoc, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, pow_succ]
    have hf1 : ((j + i).factorial : ℝ) ≠ 0 := by positivity
    have hκl : (ρ / j) * (σ / j) ≠ 0 := by positivity
    field_simp

/-! ### The factorial estimate -/

private theorem factorial_est (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (j ^ 2 * x) ^ j / ((2 * j).factorial : ℝ) ≤ (Real.exp 1 ^ 2 * x / 4) ^ j := by
  have h := Real.pow_div_factorial_le_exp ((2 * j : ℕ) : ℝ) (by positivity) (2 * j)
  have hf : (0 : ℝ) < ((2 * j).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hf] at h ⊢
  have e1 : Real.exp ((2 * j : ℕ) : ℝ) = (Real.exp 1 ^ 2) ^ j := by
    rw [← pow_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have e2 : (((2 * j : ℕ) : ℝ)) ^ (2 * j) = 4 ^ j * ((j : ℝ) ^ 2) ^ j := by
    push_cast
    rw [mul_pow, pow_mul, pow_mul]
    norm_num
  rw [e1, e2] at h
  have e3 : (Real.exp 1 ^ 2 * x / 4) ^ j * ((2 * j).factorial : ℝ) =
      x ^ j * (((Real.exp 1 ^ 2) ^ j * ((2 * j).factorial : ℝ)) / 4 ^ j) := by
    rw [div_pow, mul_pow]
    field_simp
  rw [e3, mul_pow]
  have h4 : ((j : ℝ) ^ 2) ^ j ≤ ((Real.exp 1 ^ 2) ^ j * ((2 * j).factorial : ℝ)) / 4 ^ j := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ((j : ℝ) ^ 2) ^ j * x ^ j = x ^ j * ((j : ℝ) ^ 2) ^ j := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (pow_nonneg hx j)

theorem adjoint (b : PartialBlock n k) {R' s' R s ρ σ U V : ℝ} {φ u : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hRR : R+ρ ≤ R') (hss : s+σ ≤ s') (hSL : slowLoss b.c ρ σ k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : InClass b.base R' s' φ) (hu : InClass b.base R s u)
    (hφb : WBound b.base R' s' φ V) (hub : WBound b.base R s u U) (j : ℕ) (hj : 1 ≤ j) :
    InClass b.base (R-ρ) (s-σ) (extAd b.c φ j u) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z)
      ((Real.exp 1^2*(2*V/(ρ*σ))/8)^j*U) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  obtain ⟨hic, hib⟩ := ad_iter b hρ hρR hσ hσs hRR hss hSL hU hV hφ hu hφb hub j hj j le_rfl
  have eR : R - (j : ℝ) * (ρ / j) = R - ρ := by field_simp
  have es : s - (j : ℝ) * (σ / j) = s - σ := by field_simp
  rw [eR, es] at hic hib
  have hs : 0 < s - σ := sub_pos.2 hσs
  refine ⟨hic, ?_⟩
  have hw := wbound_adjoint_const_mul ((j.factorial : ℂ)⁻¹) hs hic hib
  refine hw.mono le_rfl le_rfl ?_
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hnorm : ‖((j.factorial : ℂ)⁻¹)‖ = ((j.factorial : ℝ))⁻¹ := by
    rw [norm_inv]
    simp
  rw [hnorm]
  have hx : 0 ≤ V / (ρ * σ) := by positivity
  have hfe := factorial_est j (V / (ρ * σ)) hx
  have hfac : ((j + j).factorial : ℝ) = ((2 * j).factorial : ℝ) := by rw [two_mul]
  rw [hfac]
  have hkl : V / ((ρ / j) * (σ / j)) = j ^ 2 * (V / (ρ * σ)) := by
    field_simp
  have hrhs : Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8 = Real.exp 1 ^ 2 * (V / (ρ * σ)) / 4 := by
    field_simp
    ring
  rw [hrhs, hkl]
  have h2j : (0 : ℝ) < ((2 * j).factorial : ℝ) := by positivity
  calc ((j.factorial : ℝ))⁻¹ * ((j ^ 2 * (V / (ρ * σ))) ^ j * ((j.factorial : ℝ) /
        ((2 * j).factorial : ℝ)) * U)
      = ((j ^ 2 * (V / (ρ * σ))) ^ j / ((2 * j).factorial : ℝ)) * U := by
        field_simp
    _ ≤ (Real.exp 1 ^ 2 * (V / (ρ * σ)) / 4) ^ j * U :=
        mul_le_mul_of_nonneg_right hfe hU

end KAM.Nekhoroshev

end
