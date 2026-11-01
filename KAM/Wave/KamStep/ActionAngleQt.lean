/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleNormal
public import KAM.Wave.KamStep.RealNField
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The polynomial part `Q̃` and its field (blueprint-W `bpW:w5:action-angle` (v), step `a-field`)

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (v) (the field of `Q̃`).

With `c_j = 3/(2πλ_{j+2})` (`aaCoefC`) and `S(w) = Σ_j c_j z_j \bar z_j` (`aaSfun`, a bounded
quadratic
form `½(B(u,u) + B(v,v))`, `aaBq`), `Q̃ = ½⟨Ay,y⟩ + ⟨b,y⟩ S` (`aaQt_eq`). Its field, in
`p_+ = p+1`-representatives (`aaXQt`), is
`X_{Q̃} = ((Ay + b S)/(2π), 0, ⟨b,y⟩ β v, -⟨b,y⟩ β u)` with `β_j = c_j (j+2)` the weight-`(p+1)`
multiplier of `3/(2πλ_{j+2})` (`aaCoefE`, `|β_j| ≤ 3/(2π)`), i.e. the blueprint's
`(\frac1{2π}(Ay + β'), 0, βv, -βu)`. `aaQt_hasFDerivAt`, `aaQt_field`:
`DQ̃(w) W = ϖ_{p+1,p}(X_{Q̃}(w), W)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

variable (m : ℝ) (hm : 0 < m)

/-- `c_j = 3/(2πλ_{j+2})`. -/
def aaCoefC (j : ℕ+) : ℂ := 3 / (2 * Real.pi * lam m hm (j + 2))

/-- `d_j = c_j / ω_{a,p}(j+2)²`. -/
def aaCoefD (a p : ℝ) (j : ℕ+) : ℂ := aaCoefC m hm j / (homWt a p j : ℂ) ^ 2

/-- `β_j = c_j (j+2)`. -/
def aaCoefE (j : ℕ+) : ℂ := aaCoefC m hm j * ((j : ℂ) + 2)

variable {m hm}

theorem aaCoefC_eq_real (j : ℕ+) :
    aaCoefC m hm j = ((3 / (2 * Real.pi * lam m hm (j + 2)) : ℝ) : ℂ) := by
  unfold aaCoefC; push_cast; ring

theorem norm_aaCoefC_le (j : ℕ+) : ‖aaCoefC m hm j‖ ≤ 1 := by
  have hl := aa_one_le_lam (m := m) (hm := hm) (j + 2)
  have hpi := Real.pi_gt_three
  rw [aaCoefC_eq_real, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_le_one (by positivity)]
  nlinarith

theorem norm_aaCoefE_le (j : ℕ+) : ‖aaCoefE m hm j‖ ≤ 3 / (2 * Real.pi) := by
  have hl : ((j + 2 : ℕ+) : ℝ) < lam m hm (j + 2) := by
    unfold lam
    rw [Real.lt_sqrt (by positivity)]
    linarith [sq_nonneg (((j + 2 : ℕ+) : ℝ)), hm]
  have hJ : ((j + 2 : ℕ+) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  have hpi := Real.pi_pos
  have hj0 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hl0 : 0 < lam m hm (j + 2) := lam_pnat_pos hm _
  unfold aaCoefE
  rw [aaCoefC_eq_real, show ((j : ℂ) + 2) = (((j : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hJ] at hl
  nlinarith

theorem norm_aaCoefD_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (j : ℕ+) :
    ‖aaCoefD m hm a p j‖ ≤ 1 := by
  have h1 : 1 ≤ homWt a p j * homWt a p j := one_le_homWt_mul ha (by linarith) j
  have h0 : 0 < homWt a p j := homWt_pos a p j
  unfold aaCoefD
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0,
    div_le_one (by positivity)]
  calc ‖aaCoefC m hm j‖ ≤ 1 := norm_aaCoefC_le j
    _ ≤ homWt a p j ^ 2 := by nlinarith

variable (m hm)

/-- The bounded symmetric form `B(x, x') = Σ_j d_j x_j x'_j` (representatives at `p`). -/
def aaBq {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ :=
  homPairL2.comp (weightedDiagCLM (aaCoefD m hm a p) (norm_aaCoefD_le ha hp))

/-- `S(w) = ½(B(u,u) + B(v,v)) = Σ_j c_j z_j \bar z_j`. -/
def aaSfun {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) : ℂ :=
  1 / 2 * (aaBq m hm ha hp w.2.2.1 w.2.2.1 + aaBq m hm ha hp w.2.2.2 w.2.2.2)

/-- The multiplier `β = diag(c_j (j+2))`. -/
def aaDiagE : HomOp := weightedDiagCLM (aaCoefE m hm) norm_aaCoefE_le

/-- **The field of `Q̃`** (`p+1`-representatives): `((Ay + bS)/(2π), 0, ⟨b,y⟩ β v, -⟨b,y⟩ β u)`. -/
def aaXQt {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) : KamPhase :=
  (fun i => (2 * Real.pi : ℂ)⁻¹ * (∑ i' : Fin 2, (actionA m hm i i' : ℂ) * w.2.1 i' +
      aaSfun m hm ha hp w / (lamTan m hm i : ℂ)), 0,
    aaBdot m hm w.2.1 • aaDiagE m hm w.2.2.2, -(aaBdot m hm w.2.1 • aaDiagE m hm w.2.2.1))

variable {m hm}

theorem aaBq_apply {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (x x' : HomL2) :
    aaBq m hm ha hp x x' = ∑' j : ℕ+, aaCoefD m hm a p j * x j * x' j := rfl

theorem aaBq_comm {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (x x' : HomL2) :
    aaBq m hm ha hp x x' = aaBq m hm ha hp x' x := by
  rw [aaBq_apply, aaBq_apply]
  exact tsum_congr fun j => by ring

theorem aaZZ_eq (a p : ℝ) (w : KamPhase) (j : ℕ+) :
    aaZZ a p w j = (w.2.2.1 j * w.2.2.1 j + w.2.2.2 j * w.2.2.2 j) / 2 / (homWt a p j : ℂ) ^ 2 := by
  unfold aaZZ
  rw [stepZ_apply', stepZb_apply']
  have h2 := birkSqrt2_ne
  have hs2 := birkSqrt2_sq
  congr 1
  field_simp
  linear_combination (-(w.2.2.1 j * w.2.2.1 j + w.2.2.2 j * w.2.2.2 j)) * hs2 -
    (w.2.2.2 j * w.2.2.2 j * 2) * Complex.I_sq

theorem aaSfun_eq {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) :
    ∑' j : ℕ+, aaCoefC m hm j * aaZZ a p w j = aaSfun m hm ha hp w := by
  have hu : Summable fun j : ℕ+ => aaCoefD m hm a p j * w.2.2.1 j * w.2.2.1 j := by
    refine Summable.of_norm_bounded (homL2_pair_le w.2.2.1 w.2.2.1).1 fun j => ?_
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_aaCoefD_le ha hp j)
  have hv : Summable fun j : ℕ+ => aaCoefD m hm a p j * w.2.2.2 j * w.2.2.2 j := by
    refine Summable.of_norm_bounded (homL2_pair_le w.2.2.2 w.2.2.2).1 fun j => ?_
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_aaCoefD_le ha hp j)
  rw [aaSfun, aaBq_apply, aaBq_apply, ← hu.tsum_add hv, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [aaZZ_eq, aaCoefD]
  have h0 : (homWt a p j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos a p j).ne'
  field_simp

theorem aaQt_eq {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) :
    aaQt m hm a p w = 1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
      (w.2.1 i * w.2.1 i') + aaBdot m hm w.2.1 * aaSfun m hm ha hp w := by
  unfold aaQt
  congr 1
  rw [← aaSfun_eq ha hp, ← tsum_mul_left]
  exact tsum_congr fun j => by rw [aaCoefC]; ring

/-! ### The derivative of `Q̃` -/

/-- The projections of `KamPhase`. -/
abbrev aaPrY : KamPhase →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
    (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))

abbrev aaPrU : KamPhase →L[ℂ] HomL2 :=
  (ContinuousLinearMap.fst ℂ HomL2 HomL2).comp
    ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
      (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))

abbrev aaPrV : KamPhase →L[ℂ] HomL2 :=
  (ContinuousLinearMap.snd ℂ HomL2 HomL2).comp
    ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
      (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))

theorem hasFDerivAt_aaSfun {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) :
    HasFDerivAt (aaSfun m hm ha hp)
      ((1 / 2 : ℂ) • ((aaBq m hm ha hp).precompR KamPhase w.2.2.1 aaPrU +
          (aaBq m hm ha hp).precompL KamPhase aaPrU w.2.2.1 +
        ((aaBq m hm ha hp).precompR KamPhase w.2.2.2 aaPrV +
          (aaBq m hm ha hp).precompL KamPhase aaPrV w.2.2.2))) w := by
  have hU := (aaBq m hm ha hp).hasFDerivAt_of_bilinear (aaPrU.hasFDerivAt (x := w))
    (aaPrU.hasFDerivAt (x := w))
  have hV := (aaBq m hm ha hp).hasFDerivAt_of_bilinear (aaPrV.hasFDerivAt (x := w))
    (aaPrV.hasFDerivAt (x := w))
  exact (hU.add hV).const_smul (1 / 2 : ℂ)

theorem aaSfun_deriv_apply {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w W : KamPhase) :
    fderiv ℂ (aaSfun m hm ha hp) w W =
      aaBq m hm ha hp w.2.2.1 W.2.2.1 + aaBq m hm ha hp w.2.2.2 W.2.2.2 := by
  rw [(hasFDerivAt_aaSfun ha hp w).fderiv]
  change (1 / 2 : ℂ) * (aaBq m hm ha hp w.2.2.1 W.2.2.1 + aaBq m hm ha hp W.2.2.1 w.2.2.1 +
    (aaBq m hm ha hp w.2.2.2 W.2.2.2 + aaBq m hm ha hp W.2.2.2 w.2.2.2)) = _
  rw [aaBq_comm ha hp W.2.2.1, aaBq_comm ha hp W.2.2.2]
  ring

theorem homWt_succ_eq (a p : ℝ) (j : ℕ+) : homWt a (p + 1) j = ((j : ℝ) + 2) * homWt a p j := by
  have h := homWt_pred_div a (p + 1) j
  rw [show p + 1 - 1 = p by ring] at h
  have h0 := (homWt_pos a (p + 1) j).ne'
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  field_simp at h
  linarith

theorem stepPairCLM_aaDiagE {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hqq : 0 ≤ (p + 1) + p)
    (x x' : HomL2) :
    stepPairCLM (q := p + 1) (q' := p) ha hqq (aaDiagE m hm x) x' = aaBq m hm ha hp x x' := by
  rw [stepPairCLM_eq_tsum, aaBq_apply]
  refine tsum_congr fun j => ?_
  simp only [aaDiagE, weightedDiagCLM_apply, stepWinv, aaCoefD, aaCoefE, homWt_succ_eq]
  have h0 : (homWt a p j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos a p j).ne'
  have hj : ((j : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp

/-- **`DQ̃(w) W = ϖ_{p+1,p}(X_{Q̃}(w), W)`** (`bpW:w5:action-angle` (v), step `a-field`). -/
theorem aaQt_hasFDerivAt {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : KamPhase) :
    HasFDerivAt (aaQt m hm a p) (fderiv ℂ (aaQt m hm a p) w) w ∧
      ∀ W, fderiv ℂ (aaQt m hm a p) w W =
        stepSymp (q := p + 1) (q' := p) ha (by linarith) (aaXQt m hm ha hp w) W := by
  have hY : ∀ i : Fin 2, HasFDerivAt (fun w : KamPhase => w.2.1 i)
      ((ContinuousLinearMap.proj i).comp aaPrY) w := fun i =>
    ((ContinuousLinearMap.proj i).comp aaPrY).hasFDerivAt
  have hF0 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => HasFDerivAt.fun_sum
    (u := Finset.univ) fun i' _ => ((hY i).mul (hY i')).const_mul (actionA m hm i i' : ℂ)
  have hF1 := hF0.const_mul (1 / 2 : ℂ)
  have hF2 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hY i).mul_const ((lamTan m hm i : ℂ)⁻¹)
  have hSd : HasFDerivAt (aaSfun m hm ha hp) (fderiv ℂ (aaSfun m hm ha hp) w) w :=
    (hasFDerivAt_aaSfun ha hp w).differentiableAt.hasFDerivAt
  have hQ0 := hF1.add (hF2.mul hSd)
  have hQ : HasFDerivAt (aaQt m hm a p) _ w := hQ0.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w' => by
      rw [aaQt_eq ha hp w', aaBdot]
      simp [div_eq_mul_inv])
  refine ⟨hQ.differentiableAt.hasFDerivAt, fun W => ?_⟩
  rw [hQ.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, aaSfun_deriv_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  unfold stepSymp aaXQt
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, map_smul, map_neg,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
    stepPairCLM_aaDiagE ha hp]
  simp only [aaBdot, Fin.sum_univ_two]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have h01 := actionA_symm (m := m) (hm := hm) 1 0
  have hl0 : (lam m hm (modeIdx (0 : Fin 2)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (lam_pnat_pos hm _).ne'
  have hl1 : (lam m hm (modeIdx (1 : Fin 2)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (lam_pnat_pos hm _).ne'
  rw [lamTan_eq_lam, lamTan_eq_lam, h01]
  field_simp
  ring

end KAM.Wave

end
