/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleField
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The initial perturbation: the size of `X_P`
(blueprint-W `bpW:w5:initial`, steps `i-q`, `i-g`, `i-k`)

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:initial`, steps `i-q`, `i-g`, `i-k`.

At `a = p = 1` (fields in `p+1 = 2`-representatives), for `w ∈ D(s,r)`, `s ≤ 1/8`:
* `kamNorm_aaXQt_le`: `|X_{Q̃}(w)|_{2,r} ≤ r²` (step `i-q`);
* `kamNorm_aaDerInv_normal_le`: `|D𝒜⁻¹ V|_{2,r} ≤ 2‖V‖₊/r` for `V` with zero tangential part (step
  `i-g`);
* `kamNorm_aaDerInv_le`: `|D𝒜_ζ(w)⁻¹ V|_{2,r} ≤ ‖V‖₊ (3/r + 2√(t+r²)/r²)` when
  `Re(ζ_i + y_i) ≥ r²`, `|ζ_i + y_i| ≤ t + r²` (step `i-k`);
* `kamNorm_aaXP_le`: `|X_{P_ζ}(w)|_{2,r} ≤ ε_in` (`aaEpsIn`) for `ζ` with `|ζ|_∞ ≤ t`,
  `Re ζ_i ≥ 2r²`, `c_A(t+r²) < ρ₁²`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-- `ε_in = (1 + 2C_*) r² + C'_K (c_A(t+r²))^{5/2} (3/r + 2√(t+r²)/r²)`, `C'_K = 66 C_* C_F`. -/
def aaEpsIn (m r t : ℝ) : ℝ :=
  (1 + 2 * waveCubicConst 1) * r ^ 2 + 66 * waveCubicConst 1 * birkCF m 1 *
    (aaCA * (t + r ^ 2)) ^ ((5 : ℝ) / 2) * (3 / r + 2 * Real.sqrt (t + r ^ 2) / r ^ 2)

/-! ### Elementary bounds -/

theorem norm_aaE_le {s r : ℝ} {w : KamPhase} (hw : w ∈ kamDomain s r) (b : Bool) (i : Fin 2) :
    ‖aaE w b i‖ ≤ Real.exp (2 * Real.pi * s) := by
  unfold aaE
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hs := hw.1 i
  have hpi := Real.pi_pos
  cases b <;> simp [birkSgn, Complex.mul_re] <;> nlinarith [abs_lt.1 hs]

theorem exp_two_pi_mul_le {s : ℝ} (hs : s ≤ 1 / 8) : Real.exp (2 * Real.pi * s) ≤ Real.exp 1 := by
  refine Real.exp_le_exp.2 ?_
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

theorem norm_aaS_sq (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) :
    ‖aaS ξ w i‖ ^ 2 = ‖ξ i + w.2.1 i‖ := by
  rw [← norm_pow]; unfold aaS; rw [aaSqrt_sq]

theorem le_norm_aaS {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2} {r : ℝ} (hr : 0 < r)
    (h : r ^ 2 ≤ (ξ i + w.2.1 i).re) : r ≤ ‖aaS ξ w i‖ := by
  have h1 := norm_aaS_sq ξ w i
  have h2 : (ξ i + w.2.1 i).re ≤ ‖ξ i + w.2.1 i‖ := Complex.re_le_norm _
  nlinarith [norm_nonneg (aaS ξ w i)]

theorem norm_aaS_le {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2} {T : ℝ}
    (h : ‖ξ i + w.2.1 i‖ ≤ T) : ‖aaS ξ w i‖ ≤ Real.sqrt T := by
  rw [← Real.sqrt_sq (norm_nonneg (aaS ξ w i)), norm_aaS_sq]
  exact Real.sqrt_le_sqrt h

theorem norm_apply_le_lp (V : BirkSpace) (l : BirkIdx) : ‖V l‖ ≤ ‖V‖ :=
  lp.norm_apply_le_norm (by norm_num) V l

theorem exp_one_le_ellWeight_two (i : Fin 2) : Real.exp 1 ≤ ellWeight 1 2 (modeIdx i) := by
  unfold ellWeight
  have hj : (1 : ℝ) ≤ ((modeIdx i : ℕ+) : ℝ) := by exact_mod_cast (modeIdx i).pos
  have h1 : (1 : ℝ) ≤ ((modeIdx i : ℕ+) : ℝ) ^ (2 : ℝ) := Real.one_le_rpow hj (by norm_num)
  have h2 : Real.exp 1 ≤ Real.exp (1 * ((modeIdx i : ℕ+) : ℝ)) := Real.exp_le_exp.2 (by linarith)
  calc Real.exp 1 = 1 * Real.exp 1 := by ring
    _ ≤ _ := mul_le_mul h1 h2 (Real.exp_pos 1).le (by positivity)

/-! ### The normal part of `D𝒜⁻¹` -/

theorem norm_aaDerInv_normal_le (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) :
    ‖(aaDerInv a q ξ w V).2.2.1‖ + ‖(aaDerInv a q ξ w V).2.2.2‖ ≤ 2 * ‖V‖ := by
  rw [aaDerInv_eq]
  have hu : ‖aaUnshift (birkZinv V).1‖ ≤ ‖V‖ :=
    ((aaUnshift.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]; exact (aaUnshift.le_opNorm x).trans (by
          have : ‖aaUnshift‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
          nlinarith [norm_nonneg x])))).trans
      ((norm_fst_le (birkZinv V)).trans (norm_birkZinv_le V))
  have hv : ‖aaUnshift (birkZinv V).2‖ ≤ ‖V‖ :=
    ((aaUnshift.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (LinearMap.mkContinuous_norm_le _ zero_le_one _))).trans
      ((norm_snd_le (birkZinv V)).trans (norm_birkZinv_le V))
  linarith

/-- **Step `i-g`**: `|D𝒜⁻¹ V|_{q,r} ≤ 2‖V‖/r` for `V` with zero tangential part. -/
theorem kamNorm_aaDerInv_normal_le {a q r : ℝ} (hr : 0 < r) (ξ : Fin 2 → ℂ) (w : KamPhase)
    (V : BirkSpace) (htan : ∀ (b : Bool) (i : Fin 2), V (b, modeIdx i) = 0) :
    kamNorm r (aaDerInv a q ξ w V) ≤ 2 * ‖V‖ / r := by
  have hθ : (aaDerInv a q ξ w V).1 = 0 := funext fun i => by
    rw [aaDerInv_theta, htan, htan]; simp
  have hy : (aaDerInv a q ξ w V).2.1 = 0 := funext fun i => by
    rw [aaDerInv_y, htan, htan]; simp
  have hn := norm_aaDerInv_normal_le a q ξ w V
  unfold kamNorm
  simp only [hθ, hy, norm_zero, zero_div, zero_add]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hn hr.le

/-! ### The full `D𝒜⁻¹` at `a = 1`, `q = 2` -/

/-- **Step `i-k`**: `|D𝒜_ζ(w)⁻¹ V|_{2,r} ≤ ‖V‖₊ (3/r + 2√(t+r²)/r²)`. -/
theorem kamNorm_aaDerInv_le {s r T : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r) (ζ : Fin 2 → ℂ)
    {w : KamPhase} (hw : w ∈ kamDomain s r) (hre : ∀ i, r ^ 2 ≤ (ζ i + w.2.1 i).re)
    (hT : ∀ i, ‖ζ i + w.2.1 i‖ ≤ T) (V : BirkSpace) :
    kamNorm r (aaDerInv 1 2 ζ w V) ≤ ‖V‖ * (3 / r + 2 * Real.sqrt T / r ^ 2) := by
  have hE : ∀ b i, ‖aaE w b i‖ ≤ Real.exp 1 := fun b i =>
    (norm_aaE_le hw b i).trans (exp_two_pi_mul_le hs)
  have he := Real.exp_pos 1
  have hpi := Real.pi_gt_three
  have hV0 := norm_nonneg V
  -- `|Θ| ≤ ‖V‖/r`
  have hθ : ‖(aaDerInv 1 2 ζ w V).1‖ ≤ ‖V‖ / r := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [aaDerInv_theta, norm_div]
    have hs := le_norm_aaS hr (hre i)
    have hω := exp_one_le_ellWeight_two i
    have hnum : ‖V (false, modeIdx i) * aaE w true i - V (true, modeIdx i) * aaE w false i‖ ≤
        2 * ‖V‖ * Real.exp 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 := mul_le_mul (norm_apply_le_lp V (false, modeIdx i)) (hE true i) (norm_nonneg _) hV0
      have h2 := mul_le_mul (norm_apply_le_lp V (true, modeIdx i)) (hE false i) (norm_nonneg _) hV0
      linarith
    have hden : 4 * Real.pi * r * Real.exp 1 ≤
        ‖4 * (Real.pi : ℂ) * I * aaS ζ w i * (ellWeight 1 2 (modeIdx i) : ℂ)‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_of_pos (ellWeight_pos 1 2 _)]
      norm_num
      have : 0 ≤ Real.pi * r := by positivity
      calc 4 * Real.pi * r * Real.exp 1 = 4 * Real.pi * (r * Real.exp 1) := by ring
        _ ≤ 4 * Real.pi * (‖aaS ζ w i‖ * ellWeight 1 2 (modeIdx i)) := by gcongr
        _ = _ := by ring
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hden) hr]
    calc ‖V (false, modeIdx i) * aaE w true i - V (true, modeIdx i) * aaE w false i‖ * r
        ≤ 2 * ‖V‖ * Real.exp 1 * r := by gcongr
      _ ≤ ‖V‖ * (4 * Real.pi * r * Real.exp 1) := by
          have : 0 ≤ ‖V‖ * Real.exp 1 * r * (4 * Real.pi - 2) :=
            mul_nonneg (by positivity) (by linarith)
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hden hV0
  -- `|Y| ≤ 2√T ‖V‖`
  have hy : ‖(aaDerInv 1 2 ζ w V).2.1‖ ≤ 2 * Real.sqrt T * ‖V‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [aaDerInv_y, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ellWeight_pos 1 2 _)]
    have hs := norm_aaS_le (hT i)
    have hω := exp_one_le_ellWeight_two i
    have hsum : ‖V (true, modeIdx i) * aaE w false i + V (false, modeIdx i) * aaE w true i‖ ≤
        2 * ‖V‖ * Real.exp 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 := mul_le_mul (norm_apply_le_lp V (true, modeIdx i)) (hE false i) (norm_nonneg _) hV0
      have h2 := mul_le_mul (norm_apply_le_lp V (false, modeIdx i)) (hE true i) (norm_nonneg _) hV0
      linarith
    rw [div_le_iff₀ (ellWeight_pos 1 2 _)]
    calc ‖aaS ζ w i‖ * ‖V (true, modeIdx i) * aaE w false i + V (false, modeIdx i) * aaE w true i‖
        ≤ Real.sqrt T * (2 * ‖V‖ * Real.exp 1) :=
          mul_le_mul hs hsum (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt T * ‖V‖ * ellWeight 1 2 (modeIdx i) := by
          have := Real.sqrt_nonneg T
          nlinarith [mul_nonneg (mul_nonneg this hV0) (sub_nonneg.2 hω)]
  have hn := norm_aaDerInv_normal_le 1 2 ζ w V
  unfold kamNorm
  have hr2 : 0 < r ^ 2 := by positivity
  have e1 : ‖(aaDerInv 1 2 ζ w V).2.1‖ / r ^ 2 ≤ 2 * Real.sqrt T * ‖V‖ / r ^ 2 :=
    div_le_div_of_nonneg_right hy hr2.le
  have e2 : ‖(aaDerInv 1 2 ζ w V).2.2.1‖ / r + ‖(aaDerInv 1 2 ζ w V).2.2.2‖ / r ≤ 2 * ‖V‖ / r := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hn hr.le
  have : ‖V‖ * (3 / r + 2 * Real.sqrt T / r ^ 2) =
      ‖V‖ / r + 2 * Real.sqrt T * ‖V‖ / r ^ 2 + 2 * ‖V‖ / r := by ring
  rw [this]
  linarith

/-! ### Step `i-q`: the polynomial part -/

theorem actionA_le {m : ℝ} {hm : 0 < m} (i i' : Fin 2) : actionA m hm i i' ≤ 3 / (2 * Real.pi) := by
  have hl : ∀ i : Fin 2, 1 ≤ lamTan m hm i := fun i => aa_one_le_lam _
  have hpi := Real.pi_pos
  have hl0 : 0 < lamTan m hm i := lt_of_lt_of_le one_pos (hl i)
  have hl1 : 0 < lamTan m hm i' := lt_of_lt_of_le one_pos (hl i')
  unfold actionA
  split_ifs
  · have h1 : 1 ≤ lamTan m hm i ^ 2 := by nlinarith [hl i]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have h1 : 1 ≤ lamTan m hm i * lamTan m hm i' := by nlinarith [hl i, hl i']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem norm_aaCoefD_le' {m : ℝ} {hm : 0 < m} {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (j : ℕ+) :
    ‖aaCoefD m hm a p j‖ ≤ 1 / (2 * Real.pi) := by
  have h1 : 1 ≤ homWt a p j * homWt a p j := one_le_homWt_mul ha (by linarith) j
  have h0 : 0 < homWt a p j := homWt_pos a p j
  have hl : (3 : ℝ) ≤ lam m hm (j + 2) := by
    have h := one_le_lam_div_pnat hm (j + 2)
    have hJ : (3 : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
      push_cast; linarith
    rw [le_div_iff₀ (by linarith), one_mul] at h
    linarith
  have hpi := Real.pi_pos
  unfold aaCoefD
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0, aaCoefC_eq_real,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hc : 3 / (2 * Real.pi * lam m hm (j + 2)) ≤ 1 / (2 * Real.pi) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : 3 / (2 * Real.pi * lam m hm (j + 2)) / homWt a p j ^ 2 ≤
      3 / (2 * Real.pi * lam m hm (j + 2)) :=
    div_le_self (by positivity) (by nlinarith)
  linarith

theorem norm_aaBq_self_le {m : ℝ} {hm : 0 < m} {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (x : HomL2) :
    ‖aaBq m hm ha hp x x‖ ≤ 1 / (2 * Real.pi) * ‖x‖ ^ 2 := by
  have hd : ‖weightedDiagCLM (aaCoefD m hm a p) (norm_aaCoefD_le ha hp)‖ ≤ 1 / (2 * Real.pi) :=
    norm_diagCLM_le' _ _ (norm_aaCoefD_le' ha hp)
  show ‖homPairF (weightedDiagCLM (aaCoefD m hm a p) (norm_aaCoefD_le ha hp) x) x‖ ≤ _
  refine (norm_homPairF_le _ _).trans ?_
  rw [one_mul, sq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (((ContinuousLinearMap.le_opNorm _ x)).trans
    (mul_le_mul_of_nonneg_right hd (norm_nonneg x))) (norm_nonneg x)

theorem lamTan_two_le {m : ℝ} {hm : 0 < m} : (2 : ℝ) ≤ lamTan m hm 1 := by
  have h := one_le_lam_div_pnat hm 2
  rw [le_div_iff₀ (by norm_num), one_mul] at h
  exact_mod_cast h

theorem norm_aaBdot_le {m : ℝ} {hm : 0 < m} (y : Fin 2 → ℂ) :
    ‖aaBdot m hm y‖ ≤ 3 / 2 * ‖y‖ := by
  have h0 : (1 : ℝ) ≤ lamTan m hm 0 := aa_one_le_lam _
  have h1 := lamTan_two_le (m := m) (hm := hm)
  have hy0 := norm_le_pi_norm y 0
  have hy1 := norm_le_pi_norm y 1
  unfold aaBdot
  rw [Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
  have e0 : ‖y 0‖ / lamTan m hm 0 ≤ ‖y‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (y 0)]
  have e1 : ‖y 1‖ / lamTan m hm 1 ≤ ‖y‖ / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [norm_nonneg (y 1)]
  linarith

/-- **Step `i-q`**: `|X_{Q̃}(w)|_{2,r} ≤ r²` on `D(s,r)` (`a = p = 1`). -/
theorem kamNorm_aaXQt_le {m : ℝ} {hm : 0 < m} {s r : ℝ} (hr : 0 < r) {w : KamPhase}
    (hw : w ∈ kamDomain s r) :
    kamNorm r (aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w) ≤ r ^ 2 := by
  obtain ⟨-, hy, huv⟩ := hw
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have hu0 := norm_nonneg w.2.2.1
  have hv0 := norm_nonneg w.2.2.2
  have hy0 := norm_nonneg w.2.1
  -- `|S| ≤ r²/(4π)`
  have hS : ‖aaSfun m hm zero_le_one zero_le_one w‖ ≤ r ^ 2 / (4 * Real.pi) := by
    have h1 := norm_aaBq_self_le (m := m) (hm := hm) zero_le_one zero_le_one w.2.2.1
    have h2 := norm_aaBq_self_le (m := m) (hm := hm) zero_le_one zero_le_one w.2.2.2
    unfold aaSfun
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h3 := norm_add_le (aaBq m hm zero_le_one zero_le_one w.2.2.1 w.2.2.1)
      (aaBq m hm zero_le_one zero_le_one w.2.2.2 w.2.2.2)
    have h4 : ‖w.2.2.1‖ ^ 2 + ‖w.2.2.2‖ ^ 2 ≤ r ^ 2 := by nlinarith
    have h5 : 1 / (2 * Real.pi) * ‖w.2.2.1‖ ^ 2 + 1 / (2 * Real.pi) * ‖w.2.2.2‖ ^ 2 ≤
        1 / (2 * Real.pi) * r ^ 2 := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have : r ^ 2 / (4 * Real.pi) = 1 / 2 * (1 / (2 * Real.pi) * r ^ 2) := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by norm_num)
  -- `|Θ| ≤ (13/(8π²)) r²`
  have hθ : ‖(aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).1‖ ≤
      13 / (8 * Real.pi ^ 2) * r ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [aaXQt]
    rw [norm_mul, norm_inv, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
    have hA : ‖∑ i' : Fin 2, (actionA m hm i i' : ℂ) * w.2.1 i'‖ ≤ 3 / Real.pi * r ^ 2 := by
      rw [Fin.sum_univ_two]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (actionA_pos m hm _ _), abs_of_pos (actionA_pos m hm _ _)]
      have e0 := mul_le_mul (actionA_le (m := m) (hm := hm) i 0)
        ((norm_le_pi_norm w.2.1 0).trans hy.le) (norm_nonneg _) (by positivity)
      have e1 := mul_le_mul (actionA_le (m := m) (hm := hm) i 1)
        ((norm_le_pi_norm w.2.1 1).trans hy.le) (norm_nonneg _) (by positivity)
      have : 3 / (2 * Real.pi) * r ^ 2 + 3 / (2 * Real.pi) * r ^ 2 = 3 / Real.pi * r ^ 2 := by
        field_simp; ring
      linarith
    have hSl : ‖aaSfun m hm zero_le_one zero_le_one w / (lamTan m hm i : ℂ)‖ ≤
        r ^ 2 / (4 * Real.pi) := by
      have hl : (1 : ℝ) ≤ lamTan m hm i := aa_one_le_lam _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
        div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (aaSfun m hm zero_le_one zero_le_one w)]
    have hsum := (norm_add_le _ _).trans (add_le_add hA hSl)
    calc (2 * Real.pi)⁻¹ * ‖∑ i' : Fin 2, (actionA m hm i i' : ℂ) * w.2.1 i' +
          aaSfun m hm zero_le_one zero_le_one w / (lamTan m hm i : ℂ)‖
        ≤ (2 * Real.pi)⁻¹ * (3 / Real.pi * r ^ 2 + r ^ 2 / (4 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 13 / (8 * Real.pi ^ 2) * r ^ 2 := by field_simp; ring
  -- the normal part
  have hE : ‖aaDiagE m hm‖ ≤ 3 / (2 * Real.pi) := norm_diagCLM_le _ _
  have hb := (norm_aaBdot_le (m := m) (hm := hm) w.2.1).trans
    (mul_le_mul_of_nonneg_left hy.le (by norm_num))
  have hUV : ‖(aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).2.2.1‖ +
      ‖(aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).2.2.2‖ ≤
        9 / (4 * Real.pi) * r ^ 2 * r := by
    simp only [aaXQt, norm_neg, norm_smul]
    have e1 : ‖aaDiagE m hm w.2.2.2‖ ≤ 3 / (2 * Real.pi) * ‖w.2.2.2‖ :=
      ((aaDiagE m hm).le_opNorm _).trans (mul_le_mul_of_nonneg_right hE hv0)
    have e2 : ‖aaDiagE m hm w.2.2.1‖ ≤ 3 / (2 * Real.pi) * ‖w.2.2.1‖ :=
      ((aaDiagE m hm).le_opNorm _).trans (mul_le_mul_of_nonneg_right hE hu0)
    have hbn := norm_nonneg (aaBdot m hm w.2.1)
    calc ‖aaBdot m hm w.2.1‖ * ‖aaDiagE m hm w.2.2.2‖ + ‖aaBdot m hm w.2.1‖ * ‖aaDiagE m hm w.2.2.1‖
        ≤ 3 / 2 * r ^ 2 * (3 / (2 * Real.pi) * ‖w.2.2.2‖) +
          3 / 2 * r ^ 2 * (3 / (2 * Real.pi) * ‖w.2.2.1‖) := by
          gcongr
      _ = 9 / (4 * Real.pi) * r ^ 2 * (‖w.2.2.1‖ + ‖w.2.2.2‖) := by field_simp; ring
      _ ≤ 9 / (4 * Real.pi) * r ^ 2 * r := by gcongr
  unfold kamNorm
  have hY : (aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).2.1 = 0 := rfl
  rw [hY, norm_zero, zero_div, add_zero, add_assoc, ← add_div]
  have hdiv : (‖(aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).2.2.1‖ +
      ‖(aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w).2.2.2‖) / r ≤
        9 / (4 * Real.pi) * r ^ 2 := by
    rw [div_le_iff₀ hr]; linarith
  have hc : 13 / (8 * Real.pi ^ 2) + 9 / (4 * Real.pi) ≤ 1 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_one (by positivity)]
    nlinarith
  nlinarith

/-! ### Steps `i-g`, `i-k` and the total -/

theorem birkNormalPart_aaMap (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) :
    birkNormalPart (aaMap a p ξ w) = aaNormal w := by
  ext ⟨b, J⟩
  rw [birkNormalPart_apply]
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · have h : ¬ 3 ≤ ((modeIdx i : ℕ+) : ℕ) := by simp [modeIdx]; have := i.is_lt; omega
    simp [birkNormalMul, h, aaNormal_tan]
  · have h : 3 ≤ ((j + 2 : ℕ+) : ℕ) := by rw [PNat.add_coe]; simp; exact j.pos
    simp only [birkNormalMul, h, ite_true, one_mul, aaMap, lp.coeFn_add, Pi.add_apply,
      aaTan_nor, zero_add]

theorem rpow_five_halves_of_sq_lt {x X : ℝ} (hx : 0 ≤ x) (h : x ^ 2 < X) :
    x ^ 5 ≤ X ^ ((5 : ℝ) / 2) := by
  have hX : 0 ≤ X := le_of_lt (lt_of_le_of_lt (sq_nonneg x) h)
  have hs : x ≤ Real.sqrt X := Real.le_sqrt_of_sq_le h.le
  have e : X ^ ((5 : ℝ) / 2) = Real.sqrt X ^ 5 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
  rw [e]
  exact pow_le_pow_left₀ hx hs 5

/-- **`|X_{P_ζ}(w)|_{2,r} ≤ ε_in`** (`bpW:w5:initial`, steps `i-q`, `i-g`, `i-k`) for
`|ζ|_∞ ≤ t`, `Re ζ_i ≥ 2r²`, `c_A(t+r²) < ρ₁²`, `w ∈ D(s,r)`, `s ≤ 1/8`. -/
theorem kamNorm_aaXP_le (m : ℝ) (hm : 0 < m) {s r t : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r)
    (ht : 0 < t) (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) (ζ : Fin 2 → ℂ) (hζ : ‖ζ‖ ≤ t)
    (hre : ∀ i, 2 * r ^ 2 ≤ (ζ i).re) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    kamNorm r (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ζ w) ≤
      aaEpsIn m r t := by
  have hp : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have ha : (0 : ℝ) ≤ 1 := zero_le_one
  obtain ⟨hpos, hnorm⟩ := aaMap_domain hs hr ht ζ hζ hre hw
  have hB := aaMap_mem_birkBall1 m hm hs hr ht hρ₁ ζ hζ hre hw
  have hC := waveCubicConst_nonneg (p := 1)
  have hCF := birkCF_pos m hm hp
  -- `X_{G^{nor}}`
  set XG := birkHamNorX m hm ha hp (aaMap 1 1 ζ w) with hXG
  have hXGt : ∀ (b : Bool) (i : Fin 2), XG (b, modeIdx i) = 0 := fun b i =>
    birkQuartX_tangential m hm ha hp _ _ (by simp [modeIdx]; have := i.is_lt; omega)
  have hXGn : ‖XG‖ ≤ waveCubicConst 1 * r ^ 3 := by
    rw [hXG, birkHamNorX, birkQuartX_normal, birkNormalPart_aaMap]
    refine (norm_birkQuartX_le m hm ha hp _ _).trans ?_
    have h1 := (aaNormal_norm_le w).trans hw.2.2.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 3) hC
  -- `X_K`
  set XK := aaXKext m hm ha hp (aaMap 1 1 ζ w) with hXK
  have hXKn : ‖XK‖ ≤ 66 * waveCubicConst 1 * birkCF m 1 * (aaCA * (t + r ^ 2)) ^ ((5 : ℝ) / 2) := by
    rw [hXK]
    simp only [aaXKext, hB, dite_true]
    refine (norm_birkXK_le (m := m) (hm := hm) (ha := ha) (hp := hp) _).trans ?_
    exact mul_le_mul_of_nonneg_left (rpow_five_halves_of_sq_lt (norm_nonneg _) hnorm)
      (by positivity)
  have hreT : ∀ i, r ^ 2 ≤ (ζ i + w.2.1 i).re := fun i => (hpos i).le
  have hT : ∀ i, ‖ζ i + w.2.1 i‖ ≤ t + r ^ 2 := fun i =>
    (norm_add_le _ _).trans (add_le_add ((norm_le_pi_norm ζ i).trans hζ)
      ((norm_le_pi_norm w.2.1 i).trans hw.2.1.le))
  have e2 : (1 : ℝ) + 1 = 2 := by norm_num
  have hQ := kamNorm_aaXQt_le (m := m) (hm := hm) hr hw
  have hGb : kamNorm r (aaDerInv 1 (1 + 1) ζ w XG) ≤ 2 * (waveCubicConst 1 * r ^ 3) / r := by
    refine (kamNorm_aaDerInv_normal_le hr ζ w XG hXGt).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hr.le
  have hKb : kamNorm r (aaDerInv 1 (1 + 1) ζ w XK) ≤
      66 * waveCubicConst 1 * birkCF m 1 * (aaCA * (t + r ^ 2)) ^ ((5 : ℝ) / 2) *
        (3 / r + 2 * Real.sqrt (t + r ^ 2) / r ^ 2) := by
    rw [e2]
    refine (kamNorm_aaDerInv_le hs hr ζ hw hreT hT XK).trans ?_
    exact mul_le_mul_of_nonneg_right hXKn (by positivity)
  have hsum : kamNorm r (aaXP m hm (zero_le_one' ℝ) hp ζ w) ≤
      kamNorm r (aaXQt m hm (a := 1) (p := 1) zero_le_one zero_le_one w) +
        (kamNorm r (aaDerInv 1 (1 + 1) ζ w XG) + kamNorm r (aaDerInv 1 (1 + 1) ζ w XK)) := by
    unfold aaXP
    rw [map_add]
    exact (kamNorm_add_le hr _ _).trans (add_le_add le_rfl (kamNorm_add_le hr _ _))
  have hG' : 2 * (waveCubicConst 1 * r ^ 3) / r = 2 * waveCubicConst 1 * r ^ 2 := by
    field_simp
  rw [hG'] at hGb
  exact hsum.trans ((add_le_add hQ (add_le_add hGb hKb)).trans (le_of_eq (by unfold aaEpsIn; ring)))

end KAM.Wave

end
