/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Diag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Complex rotations and the real linear flow (blueprint-W `bpW:w1:diag` (iii), (iv))

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

* (iii) `rotCLM m hm t`: the representative `R_t = D_μ`, `μ_j = e^{-iλ_j t}`, on `ℓ²_ℂ`:
  `norm_rotCLM`, `rotCLM_add`, `continuous_rotCLM_apply`.
* (iv) `flowCLM m hm t`: the real flow `L_t` on `ℓ² × ℓ²` (the representative of `E_{a,p}`; the
  weights
  are real and cancel, `coeffW_flow_fst`): `norm_sq_flowCLM`, `norm_flowCLM_apply_le`,
  `flowCLM_add`, `hasDerivAt_flow_fst`, `hasDerivAt_flow_snd`.

The last sentence of (iv) ("in the complex coordinates of Definition `bpW:w0:z`, `L_t` is `R_t`")
needs
the complex coordinates `z = (q + ip)/√2` and is not part of this module.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m)

/-! ### Complex rotations -/

/-- The rotation multiplier `e^{-iλ_j t}`. -/
def rotMu (m : ℝ) (hm : 0 < m) (j : ℕ+) (t : ℝ) : ℂ :=
  Complex.exp (((-(lam m hm j * t) : ℝ) : ℂ) * Complex.I)

theorem norm_rotMu (j : ℕ+) (t : ℝ) : ‖rotMu m hm j t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_rotMu (j : ℕ+) : Continuous (rotMu m hm j) := by
  unfold rotMu; fun_prop

/-- **Rotation** `R_t` (blueprint `bpW:w1:diag` (iii)). -/
def rotCLM (m : ℝ) (hm : 0 < m) (t : ℝ) :
    lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  diagCLM (fun j => rotMu m hm j t) (M := 1) (fun j => (norm_rotMu hm j t).le)

@[simp] theorem rotCLM_apply (t : ℝ) (y : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) :
    rotCLM m hm t y j = rotMu m hm j t * y j := rfl

/-- `bpW:w1:diag` (iii): `R_t` is a linear isometry. -/
theorem norm_rotCLM (t : ℝ) (y : lp (fun _ : ℕ+ => ℂ) 2) : ‖rotCLM m hm t y‖ = ‖y‖ :=
  norm_diagCLM_apply_of_norm_eq_one _ _ (fun j => norm_rotMu hm j t) y

/-- `bpW:w1:diag` (iii): `R_{t+s} = R_t R_s`. -/
theorem rotCLM_add (t s : ℝ) (y : lp (fun _ : ℕ+ => ℂ) 2) :
    rotCLM m hm (t + s) y = rotCLM m hm t (rotCLM m hm s y) := by
  ext j
  simp only [rotCLM_apply, rotMu, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem rotCLM_zero (y : lp (fun _ : ℕ+ => ℂ) 2) : rotCLM m hm 0 y = y := by
  ext j; simp [rotMu]

/-- `bpW:w1:diag` (iii): `t ↦ R_t z` is continuous. -/
theorem continuous_rotCLM_apply (y : lp (fun _ : ℕ+ => ℂ) 2) :
    Continuous fun t => rotCLM m hm t y := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ t, ‖rotCLM m hm t y - rotCLM m hm s y‖ ^ 2 =
      ∑' j : ℕ+, ‖rotMu m hm j t - rotMu m hm j s‖ ^ 2 * ‖y j‖ ^ 2 := fun t => by
    refine ((lp_two_hasSum_sq _).tsum_eq).symm.trans (tsum_congr fun j => ?_)
    simp [← sub_mul, mul_pow]
  have hlim : Tendsto (fun t => ∑' j : ℕ+, ‖rotMu m hm j t - rotMu m hm j s‖ ^ 2 * ‖y j‖ ^ 2)
      (𝓝 s) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 s)
      (f := fun (t : ℝ) (j : ℕ+) => ‖rotMu m hm j t - rotMu m hm j s‖ ^ 2 * ‖y j‖ ^ 2)
      (g := fun _ => 0) (bound := fun j => 4 * ‖y j‖ ^ 2)
      ((lp_two_hasSum_sq y).summable.mul_left 4)
      (fun j => by
        have hc : Continuous fun t => ‖rotMu m hm j t - rotMu m hm j s‖ ^ 2 * ‖y j‖ ^ 2 :=
          ((continuous_rotMu hm j).sub continuous_const).norm.pow 2 |>.mul continuous_const
        simpa using hc.tendsto s)
      (Eventually.of_forall fun t j => by
        have h2 : ‖rotMu m hm j t - rotMu m hm j s‖ ≤ 2 := by
          calc _ ≤ ‖rotMu m hm j t‖ + ‖rotMu m hm j s‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_rotMu, norm_rotMu]; norm_num
        rw [Real.norm_of_nonneg (by positivity)]
        have : ‖rotMu m hm j t - rotMu m hm j s‖ ^ 2 ≤ 4 := by
          nlinarith [norm_nonneg (rotMu m hm j t - rotMu m hm j s)]
        nlinarith [sq_nonneg ‖y j‖])
    simpa using this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun t => ?_
  simp only [Function.comp_apply, ← hsq]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### The real linear flow -/

/-- The cosine multiplier `cos(λ_j t)`. -/
def cosCLM (m : ℝ) (hm : 0 < m) (t : ℝ) :
    lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  diagCLM (fun j => Real.cos (lam m hm j * t)) (M := 1) (fun j => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The sine multiplier `sin(λ_j t)`. -/
def sinCLM (m : ℝ) (hm : 0 < m) (t : ℝ) :
    lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  diagCLM (fun j => Real.sin (lam m hm j * t)) (M := 1) (fun j => by
    rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)

/-- **Real linear flow** `L_t(q, p) = (cos(λt) q + sin(λt) p, -sin(λt) q + cos(λt) p)`
(blueprint `bpW:w1:diag` (iv)), on the carrier `ℓ² × ℓ²` (the representative of `E_{a,p}`). -/
def flowCLM (m : ℝ) (hm : 0 < m) (t : ℝ) :
    (lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) →L[ℝ]
      (lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :=
  let fst := ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)
  let snd := ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)
  ContinuousLinearMap.prod ((cosCLM m hm t).comp fst + (sinCLM m hm t).comp snd)
    ((cosCLM m hm t).comp snd - (sinCLM m hm t).comp fst)

theorem flowCLM_fst_apply (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    (flowCLM m hm t z).1 j =
      Real.cos (lam m hm j * t) * z.1 j + Real.sin (lam m hm j * t) * z.2 j :=
  rfl

theorem flowCLM_snd_apply (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    (flowCLM m hm t z).2 j =
      -(Real.sin (lam m hm j * t) * z.1 j) + Real.cos (lam m hm j * t) * z.2 j := by
  simp only [flowCLM, cosCLM, sinCLM]
  show Real.cos (lam m hm j * t) * z.2 j - Real.sin (lam m hm j * t) * z.1 j = _
  ring

/-- `bpW:w1:diag` (iv): `L_t` preserves `‖q‖² + ‖p‖²`. -/
theorem norm_sq_flowCLM (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    ‖(flowCLM m hm t z).1‖ ^ 2 + ‖(flowCLM m hm t z).2‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  refine ((lp_two_hasSum_sq (flowCLM m hm t z).1).add
    (lp_two_hasSum_sq (flowCLM m hm t z).2)).unique ?_
  have : (fun j => ‖(flowCLM m hm t z).1 j‖ ^ 2 + ‖(flowCLM m hm t z).2 j‖ ^ 2) =
      fun j => ‖z.1 j‖ ^ 2 + ‖z.2 j‖ ^ 2 := by
    funext j
    rw [flowCLM_fst_apply, flowCLM_snd_apply, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (lam m hm j * t)]
  rw [this]
  exact (lp_two_hasSum_sq z.1).add (lp_two_hasSum_sq z.2)

/-- `bpW:w1:diag` (iv): `‖L_t z‖_E ≤ √2 ‖z‖_E`. -/
theorem norm_flowCLM_apply_le (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    ‖flowCLM m hm t z‖ ≤ Real.sqrt 2 * ‖z‖ := by
  have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have key := norm_sq_flowCLM hm t z
  have h0 : 0 ≤ Real.sqrt 2 * ‖z‖ := by positivity
  have hsq : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [Prod.norm_def, max_le_iff]
  constructor
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 ?_
    rw [hsq]; nlinarith [sq_nonneg ‖(flowCLM m hm t z).2‖, norm_nonneg z.1, norm_nonneg z.2,
      norm_nonneg z]
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 ?_
    rw [hsq]; nlinarith [sq_nonneg ‖(flowCLM m hm t z).1‖, norm_nonneg z.1, norm_nonneg z.2,
      norm_nonneg z]

/-- `bpW:w1:diag` (iv): `L_{t+s} = L_t L_s`. -/
theorem flowCLM_add (t s : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    flowCLM m hm (t + s) z = flowCLM m hm t (flowCLM m hm s z) := by
  refine Prod.ext ?_ ?_ <;> ext j
  · simp only [flowCLM_fst_apply, flowCLM_snd_apply, mul_add, Real.cos_add, Real.sin_add]
    ring
  · simp only [flowCLM_fst_apply, flowCLM_snd_apply, mul_add, Real.cos_add, Real.sin_add]
    ring

theorem flowCLM_zero (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    flowCLM m hm 0 z = z := by
  refine Prod.ext ?_ ?_ <;> ext j <;> simp [flowCLM_fst_apply, flowCLM_snd_apply]

/-- `bpW:w1:diag` (iv): every coordinate solves `q̇_j = λ_j p_j`. -/
theorem hasDerivAt_flow_fst (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) (t : ℝ) :
    HasDerivAt (fun s => (flowCLM m hm s z).1 j) (lam m hm j * (flowCLM m hm t z).2 j) t := by
  have hl : HasDerivAt (fun s : ℝ => lam m hm j * s) (lam m hm j) t := by
    simpa using (hasDerivAt_id' t).const_mul (lam m hm j)
  have h := ((hl.cos.mul_const (z.1 j)).add (hl.sin.mul_const (z.2 j)))
  simp only [flowCLM_fst_apply, flowCLM_snd_apply]
  convert h using 1
  ring

/-- `bpW:w1:diag` (iv): every coordinate solves `ṗ_j = -λ_j q_j`. -/
theorem hasDerivAt_flow_snd (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) (t : ℝ) :
    HasDerivAt (fun s => (flowCLM m hm s z).2 j) (-(lam m hm j * (flowCLM m hm t z).1 j)) t := by
  have hl : HasDerivAt (fun s : ℝ => lam m hm j * s) (lam m hm j) t := by
    simpa using (hasDerivAt_id' t).const_mul (lam m hm j)
  have h := ((hl.sin.mul_const (z.1 j)).neg.add (hl.cos.mul_const (z.2 j)))
  simp only [flowCLM_fst_apply, flowCLM_snd_apply]
  convert h using 1
  ring

/-- The weights cancel: in the coordinates `κ_{a,p}` the flow is the same rotation. -/
theorem coeffW_flow_fst (a p : ℝ) (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2)
    (j : ℕ+) :
    coeffW a p (flowCLM m hm t z).1 j =
      Real.cos (lam m hm j * t) * coeffW a p z.1 j +
        Real.sin (lam m hm j * t) * coeffW a p z.2 j := by
  simp only [coeffW_apply, flowCLM_fst_apply, RCLike.ofReal_real_eq_id, id]
  ring

theorem coeffW_flow_snd (a p : ℝ) (t : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2)
    (j : ℕ+) :
    coeffW a p (flowCLM m hm t z).2 j =
      -(Real.sin (lam m hm j * t) * coeffW a p z.1 j) +
        Real.cos (lam m hm j * t) * coeffW a p z.2 j := by
  simp only [coeffW_apply, flowCLM_snd_apply, RCLike.ofReal_real_eq_id, id]
  ring

/-- In weighted coordinates `κ_{a,p}`, `q̇_j = λ_j p_j`. -/
theorem hasDerivAt_coeffW_flow_fst (a p : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2)
    (j : ℕ+) (t : ℝ) :
    HasDerivAt (fun s => coeffW a p (flowCLM m hm s z).1 j)
      (lam m hm j * coeffW a p (flowCLM m hm t z).2 j) t := by
  have := (hasDerivAt_flow_fst hm z j t).div_const (ellWeight a p j)
  simp only [coeffW_apply, RCLike.ofReal_real_eq_id, id]
  convert this using 1
  ring

/-- In weighted coordinates `κ_{a,p}`, `ṗ_j = -λ_j q_j`. -/
theorem hasDerivAt_coeffW_flow_snd (a p : ℝ) (z : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2)
    (j : ℕ+) (t : ℝ) :
    HasDerivAt (fun s => coeffW a p (flowCLM m hm s z).2 j)
      (-(lam m hm j * coeffW a p (flowCLM m hm t z).1 j)) t := by
  have := (hasDerivAt_flow_snd hm z j t).div_const (ellWeight a p j)
  simp only [coeffW_apply, RCLike.ofReal_real_eq_id, id]
  convert this using 1
  ring

end KAM.Wave

end
