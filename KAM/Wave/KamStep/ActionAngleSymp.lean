/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleDeriv
public import KAM.Wave.Birkhoff.Omega
public import KAM.Wave.Birkhoff.HamClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The action–angle substitution is symplectic (blueprint-W `bpW:w5:action-angle` (iii))

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (iii), step `a-der` (the form).

* `birkOmegaMix a q q' W W' = i Σ_l sgn(l) W_l W'_{-l}` (actual coordinates of `W ∈ 𝔚^q`,
  `W' ∈ 𝔚^{q'}`), the form `Ω` of `bpW:w3:omega` between two weights; summable for `q + q' ≥ 0`
  (`summable_birkOmegaMix`); `birkOmega_eq_birkOmegaMix` (equal weights) and
  `birkOmegaPlus_eq_birkOmegaMix` (`Ω(ιX, v)`, `X ∈ 𝔚^{p+1}`).
* `birk_tsum_tan_nor`: a sum over `ℤ ∖ {0}` is the tangential part `|l| ≤ 2` plus the normal part
  `|l| = j + 2`.
* `aaDer_symp`: `Ω(D𝒜_ξ(w) W, D𝒜_ξ(w) W') = ϖ(W, W')` for `W ∈ 𝒫^q`, `W' ∈ 𝒫^{q'}`, `q + q' ≥ 0`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-- The form `Ω(W, W') = i Σ_l sgn(l) W_l W'_{-l}` for `W ∈ 𝔚^q`, `W' ∈ 𝔚^{q'}` (`bpW:w3:omega`). -/
def birkOmegaMix (a q q' : ℝ) (y y' : BirkSpace) : ℂ :=
  I * ∑' l, birkSgn l * birkCoord a q y l * birkCoord a q' y' (birkNeg l)

theorem birkOmega_eq_birkOmegaMix {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    birkOmega ha hr y y' = birkOmegaMix a r r y y' := rfl

theorem birkOmegaPlus_eq_birkOmegaMix {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (X v : BirkSpace) :
    birkOmegaPlus a p ha hp X v = birkOmegaMix a (p + 1) p X v := by
  rw [birkOmegaPlus, birkOmega_apply, birkOmegaMix]
  congr 1
  refine tsum_congr fun l => ?_
  rw [birkCoord_birkEmbed]

theorem one_le_ellWeight_mul {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (j : ℕ+) :
    1 ≤ ellWeight a q j * ellWeight a q' j := by
  unfold ellWeight
  have hJ : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast j.pos
  have h1 : (1 : ℝ) ≤ (j : ℝ) ^ (q + q') := Real.one_le_rpow hJ hqq'
  have h2 : (1 : ℝ) ≤ Real.exp (2 * a * (j : ℝ)) := Real.one_le_exp (by positivity)
  have e : (j : ℝ) ^ q * Real.exp (a * j) * ((j : ℝ) ^ q' * Real.exp (a * j)) =
      (j : ℝ) ^ (q + q') * Real.exp (2 * a * j) := by
    rw [Real.rpow_add (by linarith), show 2 * a * (j : ℝ) = a * j + a * j by ring, Real.exp_add]
    ring
  rw [e]
  nlinarith

theorem norm_birkOmegaMix_term_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q')
    (y y' : BirkSpace) (l : BirkIdx) :
    ‖birkSgn l * birkCoord a q y l * birkCoord a q' y' (birkNeg l)‖ ≤ ‖y l‖ * ‖y' (birkNeg l)‖ := by
  have h1 := one_le_ellWeight_mul ha hqq' l.2
  have hw1 := ellWeight_pos a q l.2
  have hw2 := ellWeight_pos a q' l.2
  simp only [birkCoord, norm_mul, norm_div, norm_birkSgn, one_mul, birkNeg_snd]
  rw [RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_pos hw1, abs_of_pos hw2, div_mul_div_comm]
  rw [div_le_iff₀ (by positivity)]
  exact le_mul_of_one_le_right (by positivity) h1

theorem summable_birkOmegaMix {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (y y' : BirkSpace) :
    Summable fun l => birkSgn l * birkCoord a q y l * birkCoord a q' y' (birkNeg l) :=
  Summable.of_norm_bounded (birkPair_summable y y').1 (norm_birkOmegaMix_term_le ha hqq' y y')

/-! ### Splitting sums over `ℤ ∖ {0}` -/

theorem aa_hasSum_pnat (g : ℕ+ → ℂ) (hg : Summable g) :
    HasSum g (g 1 + g 2 + ∑' j : ℕ+, g (j + 2)) := by
  classical
  set g' : ℕ+ → ℂ := fun J => if (J : ℕ) ≤ 2 then 0 else g J with hg'
  set h : ℕ+ → ℂ := fun J => if (J : ℕ) ≤ 2 then g J else 0 with hh
  have hsplit : g = g' + h := funext fun J => by
    simp only [hg', hh, Pi.add_apply]; split_ifs <;> simp
  have h1 : HasSum (g' ∘ fun j : ℕ+ => j + 2) (∑' j : ℕ+, g (j + 2)) := by
    have : (g' ∘ fun j : ℕ+ => j + 2) = fun j => g (j + 2) := funext fun j => by
      have : ¬ (((j + 2 : ℕ+) : ℕ) ≤ 2) := by rw [PNat.add_coe]; simp
      simp only [Function.comp_apply, hg', this, ite_false]
    rw [this]
    have hs : Summable (g ∘ fun j : ℕ+ => j + 2) := hg.comp_injective aaIdx_injective
    exact hs.hasSum
  have h2 : HasSum g' (∑' j : ℕ+, g (j + 2)) := by
    refine (Function.Injective.hasSum_iff aaIdx_injective fun J hJ => ?_).1 h1
    simp only [hg']
    by_cases hJ2 : (J : ℕ) ≤ 2
    · simp [hJ2]
    · exact absurd ⟨Nat.toPNat ((J : ℕ) - 2) (by omega), pnat_sub_two_add_two J (by omega)⟩ hJ
  have h3 : HasSum h (g 1 + g 2) := by
    have : HasSum h (∑ J ∈ ({1, 2} : Finset ℕ+), h J) :=
      hasSum_sum_of_ne_finset_zero (f := h) (s := {1, 2}) fun J hJ => by
      simp only [hh]
      rw [ite_eq_right_iff]
      intro hJ2
      exfalso
      apply hJ
      have : (J : ℕ) = 1 ∨ (J : ℕ) = 2 := by have := J.pos; omega
      rcases this with h | h
      · simp [PNat.coe_eq_one_iff.1 h]
      · have : J = 2 := PNat.eq h
        simp [this]
    rw [Finset.sum_pair (by decide)] at this
    simpa [hh] using this
  have h4 := h2.add h3
  have e : (fun b => g' b + h b) = g := by rw [hsplit]; rfl
  rw [e, add_comm] at h4
  exact h4

/-- A summable sum over `ℤ ∖ {0}` splits into the tangential modes `±1, ±2` and the normal modes
`±(j + 2)`. -/
theorem birk_tsum_tan_nor (f : BirkIdx → ℂ) (hf : Summable f) :
    ∑' l, f l = ∑ i : Fin 2, ∑ b : Bool, f (b, modeIdx i) +
      ∑ b : Bool, ∑' j : ℕ+, f (b, j + 2) := by
  rw [birk_tsum_split hf]
  have ht := ((aa_hasSum_pnat (fun j => f (true, j))
    (hf.comp_injective (Prod.mk_right_injective true))).tsum_eq)
  have hf' := ((aa_hasSum_pnat (fun j => f (false, j))
    (hf.comp_injective (Prod.mk_right_injective false))).tsum_eq)
  rw [ht, hf', Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  have h0 : modeIdx (0 : Fin 2) = 1 := rfl
  have h1 : modeIdx (1 : Fin 2) = 2 := rfl
  rw [h0, h1]
  ring

/-! ### The symplectic identity -/

theorem birkCoord_aaDer_tan (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (b : Bool) (i : Fin 2) :
    birkCoord a q (aaDer a q ξ w W) (b, modeIdx i) = aaDerTanL ξ w b i W := by
  rw [birkCoord, aaDer_tan]
  exact mul_div_cancel_left₀ _ (ellWeight_cast_ne_zero (K := ℂ) a q (modeIdx i))

theorem birkCoord_aaDer_nor_true (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (j : ℕ+) :
    birkCoord a q (aaDer a q ξ w W) (true, j + 2) =
      (W.2.2.1 j + I * W.2.2.2 j) / birkSqrt2 / (homWt a q j : ℂ) := by
  rw [birkCoord, aaDer_nor_true]; rfl

theorem birkCoord_aaDer_nor_false (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (j : ℕ+) :
    birkCoord a q (aaDer a q ξ w W) (false, j + 2) =
      (W.2.2.1 j - I * W.2.2.2 j) / birkSqrt2 / (homWt a q j : ℂ) := by
  rw [birkCoord, aaDer_nor_false]; rfl

theorem stepPairCLM_eq_tsum {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c z : HomL2) :
    stepPairCLM ha hqq' c z = ∑' j : ℕ+, stepWinv a q q' j * c j * z j := rfl

/-- The normal pairing in `(z, \bar z)` form: `i (z \bar z' - \bar z z') = u v' - v u'`. -/
theorem aa_normal_pair (U V U' V' ω ω' : ℂ) (hω : ω ≠ 0) (hω' : ω' ≠ 0) :
    I * ((1 : ℂ) * ((U + I * V) / birkSqrt2 / ω) * ((U' - I * V') / birkSqrt2 / ω') +
        (-1 : ℂ) * ((U - I * V) / birkSqrt2 / ω) * ((U' + I * V') / birkSqrt2 / ω')) =
      (ω * ω')⁻¹ * U * V' - (ω * ω')⁻¹ * V * U' := by
  have h2 := birkSqrt2_ne
  have hs2 := birkSqrt2_sq
  field_simp
  linear_combination (-2 * (U * V' - V * U')) * Complex.I_sq + (-(U * V' - V * U')) * hs2

/-- **`D𝒜_ξ(w)` is symplectic** (`bpW:w5:action-angle` (iii)):
`Ω(D𝒜 W, D𝒜 W') = ϖ(W, W')` for `W ∈ 𝒫^q`, `W' ∈ 𝒫^{q'}`, `q + q' ≥ 0`. -/
theorem aaDer_symp {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) (W W' : KamPhase) :
    birkOmegaMix a q q' (aaDer a q ξ w W) (aaDer a q' ξ w W') =
      stepSymp (q := q) (q' := q') ha hqq' W W' := by
  have hsum := summable_birkOmegaMix ha hqq' (aaDer a q ξ w W) (aaDer a q' ξ w W')
  rw [birkOmegaMix, birk_tsum_tan_nor _ hsum, mul_add]
  have hT : ∀ b : Bool, Summable fun j : ℕ+ => birkSgn (b, j + 2) *
      birkCoord a q (aaDer a q ξ w W) (b, j + 2) *
        birkCoord a q' (aaDer a q' ξ w W') (birkNeg (b, j + 2)) := fun b =>
    hsum.comp_injective (f := fun l => birkSgn l * birkCoord a q (aaDer a q ξ w W) l *
      birkCoord a q' (aaDer a q' ξ w W') (birkNeg l))
      ((Prod.mk_right_injective b).comp aaIdx_injective)
  rw [Fintype.sum_bool, ← (hT true).tsum_add (hT false), ← tsum_mul_left]
  unfold stepSymp
  rw [stepPairCLM_eq_tsum, stepPairCLM_eq_tsum]
  have hA : Summable fun j : ℕ+ => stepWinv a q q' j * W.2.2.1 j * W'.2.2.2 j := by
    refine Summable.of_norm_bounded (homL2_pair_le W.2.2.1 W'.2.2.2).1 (fun j => ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_stepWinv_le ha hqq' j)
  have hB : Summable fun j : ℕ+ => stepWinv a q q' j * W.2.2.2 j * W'.2.2.1 j := by
    refine Summable.of_norm_bounded (homL2_pair_le W.2.2.2 W'.2.2.1).1 (fun j => ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_stepWinv_le ha hqq' j)
  have hnor : ∀ j : ℕ+, I * (birkSgn (true, j + 2) *
      birkCoord a q (aaDer a q ξ w W) (true, j + 2) *
        birkCoord a q' (aaDer a q' ξ w W') (birkNeg (true, j + 2)) +
      birkSgn (false, j + 2) * birkCoord a q (aaDer a q ξ w W) (false, j + 2) *
        birkCoord a q' (aaDer a q' ξ w W') (birkNeg (false, j + 2))) =
      stepWinv a q q' j * W.2.2.1 j * W'.2.2.2 j - stepWinv a q q' j * W.2.2.2 j * W'.2.2.1 j :=
        fun j => by
    have hω : (homWt a q j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos a q j).ne'
    have hω' : (homWt a q' j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos a q' j).ne'
    simp only [birkNeg, Bool.not_true, Bool.not_false, birkSgn_true, birkSgn_false,
      birkCoord_aaDer_nor_true, birkCoord_aaDer_nor_false]
    rw [aa_normal_pair _ _ _ _ _ _ hω hω', stepWinv]
    push_cast
    ring
  rw [tsum_congr hnor, hA.tsum_sub hB, add_sub_assoc]
  congr 1
  -- the tangential part
  simp only [Fin.sum_univ_two, Fintype.sum_bool, birkNeg, Bool.not_true, Bool.not_false,
    birkSgn_true, birkSgn_false, birkCoord_aaDer_tan, aaDerTanL_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hs0 := aaS_ne_zero (hw 0)
  have hs1 := aaS_ne_zero (hw 1)
  have hE0 := aaE_mul w 0
  have hE1 := aaE_mul w 1
  have hEf0 : aaE w false 0 = (aaE w true 0)⁻¹ := eq_inv_of_mul_eq_one_right hE0
  have hEf1 : aaE w false 1 = (aaE w true 1)⁻¹ := eq_inv_of_mul_eq_one_right hE1
  have hE0' := aaE_ne_zero w true 0
  have hE1' := aaE_ne_zero w true 1
  rw [hEf0, hEf1]
  field_simp
  linear_combination (8 * aaS ξ w 0 ^ 2 * aaS ξ w 1 ^ 2 * Real.pi *
    (W.2.1 0 * W'.1 0 - W.1 0 * W'.2.1 0 + W.2.1 1 * W'.1 1 - W.1 1 * W'.2.1 1)) * Complex.I_sq

end KAM.Wave

end
