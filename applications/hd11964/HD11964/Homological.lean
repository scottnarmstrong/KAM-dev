/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.ChiSmooth
public import KAM.Application.LambdaDrift.LieRemainderChart
public import KAM.Application.LambdaDrift.LieCalculus

/-!
# The order-2 homological equation (HD11964-CHI, piece 2)

For the Kepler part `h = hProd 1 ν` (a function of `Λ` alone, `ω = ∂h/∂Λ = keplerFreq ν`):

* `pb_hProd`: `{a, h} = Σ_i ω_i ∂_{λ_i} a`.
* `pb_chiStar_hProd` (2a), **the homological equation**: `{χ*, h} = Π_S P` on an open
  angle-saturated set of the chart domain where `P` is smooth and no divisor vanishes.
* `chartCoeff_sub_projS` (2b): for a symmetric `S ∌ 0`, `(1 - Π_S) P` has no Fourier modes in `S`.
* `residual₁_tail` (2c): with `χ₁ = χ*(P)`, `r₁ = P - Π_S P`, a pure tail.
* `residual₂_tail` (2d): with `G₂ = {P - ½ Π_S P, χ₁}` and `χ₂ = χ*(G₂)`, `r₂ = G₂ - Π_S G₂`, a
  pure tail.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Application.LambdaDrift ComplexConjugate
open scoped Real ContDiff

namespace HD11964.Cover

/-- The Kepler frequencies `ω_i(Λ) = ν_i³/Λ_i³ = ∂h/∂Λ_i` of `h = hProd 1 ν`. -/
def keplerFreq (ν : Fin 2 → ℝ) (Λ : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => ν i ^ 3 / Λ i ^ 3

/-! ### Lines and the Kepler part -/

/-- A derivative along `v` is the derivative along the line `t ↦ w + t v`. -/
theorem fderiv_eq_deriv_line {f : Phase (2 + 2) → ℝ} {w : Phase (2 + 2)} (v : Phase (2 + 2))
    (hf : DifferentiableAt ℝ f w) : fderiv ℝ f w v = deriv (fun t : ℝ => f (w + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  exact ((hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)).deriv).symm

theorem differentiableAt_fast_snd (i : Fin 2) :
    Differentiable ℝ fun w : Phase (2 + 2) => fast w.2 i :=
  ((contDiff_coord (Fin.castAdd 2 i)).comp contDiff_snd).differentiable (by simp)

/-- The Kepler part is differentiable where the actions do not vanish. -/
theorem differentiableAt_hProd (ν : Fin 2 → ℝ) {w : Phase (2 + 2)} (hΛ : ∀ i, fast w.2 i ≠ 0) :
    DifferentiableAt ℝ (hProd 1 ν) w := by
  show DifferentiableAt ℝ (fun y : Phase (2 + 2) => -∑ i, (1 : ℝ) ^ 2 * ν i ^ 3 /
    (2 * fast y.2 i ^ 2)) w
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 2)), DifferentiableAt ℝ
      (fun y : Phase (2 + 2) => (1 : ℝ) ^ 2 * ν i ^ 3 / (2 * fast y.2 i ^ 2)) w := by
    intro i _
    have hc : DifferentiableAt ℝ (fun _ : Phase (2 + 2) => (1 : ℝ) ^ 2 * ν i ^ 3) w :=
      differentiableAt_const _
    have hd : DifferentiableAt ℝ (fun y : Phase (2 + 2) => 2 * fast y.2 i ^ 2) w :=
      ((differentiableAt_fast_snd i w).pow 2).const_mul 2
    have h' := hc.fun_mul (hd.fun_inv (mul_ne_zero two_ne_zero (pow_ne_zero 2 (hΛ i))))
    simpa [div_eq_mul_inv] using h'
  exact (DifferentiableAt.fun_sum h).neg

/-- `h` along the action line `w + t (0, e_k)`. -/
theorem hasDerivAt_hProd_line (ν : Fin 2 → ℝ) {w : Phase (2 + 2)} (hΛ : ∀ i, fast w.2 i ≠ 0)
    (k : Fin (2 + 2)) :
    HasDerivAt (fun t : ℝ =>
        hProd 1 ν (w + t • ((0 : Fin (2 + 2) → ℝ), (Pi.single k 1 : Fin (2 + 2) → ℝ))))
      (∑ i, ν i ^ 3 / fast w.2 i ^ 3 * (Pi.single k (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.castAdd 2 i))
      0 := by
  set δ : Fin 2 → ℝ := fun i => (Pi.single k (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.castAdd 2 i)
  have e : (fun t : ℝ =>
      hProd 1 ν (w + t • ((0 : Fin (2 + 2) → ℝ), (Pi.single k 1 : Fin (2 + 2) → ℝ)))) =
      fun t => -∑ i, 1 ^ 2 * ν i ^ 3 / (2 * (fast w.2 i + t * δ i) ^ 2) := by
    funext t
    simp [hProd, fast, δ]
  rw [e]
  have hd : ∀ i, HasDerivAt (fun t : ℝ => 1 ^ 2 * ν i ^ 3 / (2 * (fast w.2 i + t * δ i) ^ 2))
      (-(ν i ^ 3 / fast w.2 i ^ 3 * δ i)) 0 := by
    intro i
    have hg : HasDerivAt (fun t : ℝ => 2 * (fast w.2 i + t * δ i) ^ 2)
        (2 * ((2 : ℕ) * (fast w.2 i + 0 * δ i) ^ (2 - 1) * (1 * δ i))) 0 :=
      ((((hasDerivAt_id (0 : ℝ)).mul_const (δ i)).const_add (fast w.2 i)).pow 2).const_mul 2
    have hq := (hasDerivAt_const (0 : ℝ) (1 ^ 2 * ν i ^ 3)).div hg (by
      simp [hΛ i])
    convert hq using 1
    have h0 : fast w.2 i ≠ 0 := hΛ i
    norm_num
    field_simp
  convert (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => hd i).neg using 1
  simp only [Finset.sum_neg_distrib, neg_neg, δ]

/-- `∂h/∂(w.2 k) = Σ_i ω_i [k = i]`. -/
theorem fderiv_hProd_action (ν : Fin 2 → ℝ) {w : Phase (2 + 2)} (hΛ : ∀ i, fast w.2 i ≠ 0)
    (k : Fin (2 + 2)) :
    fderiv ℝ (hProd 1 ν) w ((0 : Fin (2 + 2) → ℝ), (Pi.single k 1 : Fin (2 + 2) → ℝ)) =
      ∑ i, ν i ^ 3 / fast w.2 i ^ 3 *
        (Pi.single k (1 : ℝ) : Fin (2 + 2) → ℝ) (Fin.castAdd 2 i) := by
  rw [fderiv_eq_deriv_line _ (differentiableAt_hProd ν hΛ)]
  exact (hasDerivAt_hProd_line ν hΛ k).deriv

/-- **The bracket with the Kepler part**: `{a, h} = Σ_i ω_i ∂_{λ_i} a`. -/
theorem pb_hProd (ν : Fin 2 → ℝ) (a : Phase (2 + 2) → ℝ) {w : Phase (2 + 2)}
    (hΛ : ∀ i, fast w.2 i ≠ 0) :
    pb a (hProd 1 ν) w =
      ∑ i, keplerFreq ν (fast w.2) i * fderiv ℝ a w (angleDir (Fin.castAdd 2 i)) := by
  rw [pb_eq_sum]
  have h0 : ∀ k : Fin (2 + 2), fderiv ℝ (hProd 1 ν) w (Pi.single k 1, 0) = 0 :=
    fun k => fderiv_hProd_angleDir ν k w
  simp only [h0, mul_zero, sub_zero, fderiv_hProd_action ν hΛ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, keplerFreq, angleDir]
  ring

/-! ### `χ*` along an angle -/

theorem add_angleDir_snd (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) :
    (w + t • angleDir (Fin.castAdd 2 i)).2 = w.2 := by
  simp [angleDir]

theorem slow_add_angleDir_fst (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) :
    slow (w + t • angleDir (Fin.castAdd 2 i)).1 = slow w.1 := by
  funext j
  simp [angleDir, slow, Pi.single_apply]
  intro h
  have h1 := congrArg Fin.val h
  simp at h1
  have := i.isLt
  omega

theorem fast_add_angleDir_fst (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) (j : Fin 2) :
    fast (w + t • angleDir (Fin.castAdd 2 i)).1 j = fast w.1 j + t * if j = i then 1 else 0 := by
  have hiff : (Fin.castAdd 2 j = Fin.castAdd 2 i) ↔ j = i := by simp [Fin.ext_iff]
  simp [angleDir, fast, Pi.single_apply, hiff]

theorem withAngles_add_angleDir (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) (lam : Fin 2 → ℝ) :
    withAngles (w + t • angleDir (Fin.castAdd 2 i)) lam = withAngles w lam := by
  simp only [withAngles, add_angleDir_snd, slow_add_angleDir_fst]

theorem chartCoeff_add_angleDir (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2))
    (i : Fin 2) (t : ℝ) :
    chartCoeff P k (w + t • angleDir (Fin.castAdd 2 i)) = chartCoeff P k w := by
  simp only [chartCoeff, withAngles_add_angleDir]

theorem charE_add_angleDir (k : Fin 2 → ℤ) (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) :
    charE k (fun j => ((fast (w + t • angleDir (Fin.castAdd 2 i)).1 j / (2 * π) : ℝ) : ℂ)) =
      charE k (fun j => ((fast w.1 j / (2 * π) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (k i : ℂ) * t) := by
  simp only [charE, ← Complex.exp_add, fast_add_angleDir_fst]
  congr 1
  simp only [Fin.sum_univ_two]
  fin_cases i <;> simp <;> field_simp <;> ring

/-- The summands of `χ*` at `w`. -/
def chiTerm (frq : (Fin 2 → ℝ) → Fin 2 → ℝ) (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2))
    (k : Fin 2 → ℤ) : ℂ :=
  chartCoeff P k w * (Complex.I * ∑ j, (k j : ℂ) * frq (fast w.2) j)⁻¹ *
    charE k (fun j => ((fast w.1 j / (2 * π) : ℝ) : ℂ))

theorem chiStar_line (S : Finset (Fin 2 → ℤ)) (frq : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) :
    chiStar S frq P (w + t • angleDir (Fin.castAdd 2 i)) =
      (∑ k ∈ S, chiTerm frq P w k * Complex.exp (Complex.I * (k i : ℂ) * t)).re := by
  unfold chiStar chiTerm
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartCoeff_add_angleDir, add_angleDir_snd, charE_add_angleDir]
  ring

/-- **The angle derivative of `χ*`**: `∂_{λ_i} χ* = Re Σ_k (summand) · i k_i`. -/
theorem fderiv_chiStar_angleDir {S : Finset (Fin 2 → ℤ)} {frq : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {P : Phase (2 + 2) → ℝ} {w : Phase (2 + 2)} (hd : DifferentiableAt ℝ (chiStar S frq P) w)
    (i : Fin 2) :
    fderiv ℝ (chiStar S frq P) w (angleDir (Fin.castAdd 2 i)) =
      (∑ k ∈ S, chiTerm frq P w k * (Complex.I * (k i : ℂ))).re := by
  rw [fderiv_eq_deriv_line _ hd]
  simp_rw [chiStar_line]
  have hterm : ∀ k ∈ S, HasDerivAt (fun t : ℝ => chiTerm frq P w k *
      Complex.exp (Complex.I * (k i : ℂ) * t)) (chiTerm frq P w k * (Complex.I * (k i : ℂ))) 0 := by
    intro k _
    have hl : HasDerivAt (fun t : ℝ => Complex.I * (k i : ℂ) * (t : ℂ))
        (Complex.I * (k i : ℂ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (k i : ℂ))
    simpa using hl.cexp.const_mul (chiTerm frq P w k)
  have hsum := HasDerivAt.fun_sum hterm
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hsum).deriv
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  exact h

/-! ### (2a) The homological equation -/

theorem fast_ne_zero_of_mem_dom {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2) (i : Fin 2) :
    fast w.2 i ≠ 0 := by
  have h := (hw i).1
  have h0 : (planetBlock w i).2 0 = fast w.2 i := by simp [planetBlock]
  rw [h0] at h
  exact h.ne'

theorem contDiffAt_keplerFreq (ν : Fin 2 → ℝ) {Λ : Fin 2 → ℝ} (hΛ : ∀ i, Λ i ≠ 0) :
    ContDiffAt ℝ ∞ (keplerFreq ν) Λ :=
  contDiffAt_pi.2 fun i =>
    contDiffAt_const.div ((contDiff_coord i).contDiffAt.pow 3) (pow_ne_zero 3 (hΛ i))

/-- **The homological equation** (2a): `{χ*, h} = Π_S P`. -/
theorem pb_chiStar_hProd {ν : Fin 2 → ℝ} {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) (hdom : U ⊆ poincareProdDom 2) {S : Finset (Fin 2 → ℤ)}
    {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) (hS : IsModeSet S (keplerFreq ν) U) :
    ∀ w ∈ U, pb (chiStar S (keplerFreq ν) P) (hProd 1 ν) w = projS S P w := by
  have hdiv := hS.2.2
  intro w hw
  have hΛ := fast_ne_zero_of_mem_dom (hdom hw)
  have hsmooth := contDiffOn_chiStar hU hsat hP
    (fun y hy => contDiffAt_keplerFreq ν (fast_ne_zero_of_mem_dom (hdom hy))) hS
  have hd : DifferentiableAt ℝ (chiStar S (keplerFreq ν) P) w :=
    (hsmooth.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
  rw [pb_hProd ν _ hΛ]
  simp only [fderiv_chiStar_angleDir hd]
  -- `Σ_i ω_i Re(Σ_k c_k (i k_i)) = Re Σ_k c_k (i k·ω)`, and `(i k·ω)⁻¹ (i k·ω) = 1`
  have hre : ∀ (r : ℝ) (z : ℂ), r * z.re = ((r : ℂ) * z).re := fun r z => by simp
  simp only [hre, ← Complex.re_sum]
  unfold projS
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hne : Complex.I * ∑ j, (k j : ℂ) * (keplerFreq ν (fast w.2) j : ℂ) ≠ 0 := by
    have hc : (∑ j, (k j : ℂ) * (keplerFreq ν (fast w.2) j : ℂ)) =
        ((∑ j, (k j : ℝ) * keplerFreq ν (fast w.2) j : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hdiv k hk w hw))
  have hsum : ∑ i, (keplerFreq ν (fast w.2) i : ℂ) * (chiTerm (keplerFreq ν) P w k *
      (Complex.I * (k i : ℂ))) = chiTerm (keplerFreq ν) P w k *
        (Complex.I * ∑ j, (k j : ℂ) * (keplerFreq ν (fast w.2) j : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  have hne' : (∑ j, (k j : ℂ) * (keplerFreq ν (fast w.2) j : ℂ)) ≠ 0 := right_ne_zero_of_mul hne
  unfold chiTerm
  field_simp

/-! ### (2b) `(1 - Π_S) P` is a pure tail -/

/-- Interval integrals commute with complex conjugation. -/
theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- A chart function at `w`, as a function of kamx-hd-layer's angles `θ` (real parts used). -/
def chartFun (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2)) :
    (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ :=
  fun θ _ => (P (withAngles w (fun i => 2 * π * (θ i).re)) : ℂ)

theorem chartCoeff_eq_fourierCoeff2 (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2)) :
    chartCoeff P k w = fourierCoeff2 (chartFun P w) k 0 := by
  unfold chartCoeff fourierCoeff2 chartFun
  refine intervalIntegral.integral_congr fun t₀ _ => intervalIntegral.integral_congr fun t₁ _ => ?_
  congr 4
  funext i
  fin_cases i <;> simp

theorem continuous_chartFun {U : Set (Phase (2 + 2))} (hsat : IsAngleSaturated U)
    {P : Phase (2 + 2) → ℝ} (hP : ContinuousOn P U) {w : Phase (2 + 2)} (hw : w ∈ U) :
    Continuous fun t : Fin 2 → ℝ => chartFun P w (fun i => (t i : ℂ)) 0 := by
  unfold chartFun
  simp only [Complex.ofReal_re]
  have hΦ : Continuous fun t : Fin 2 → ℝ => withAngles w fun i => 2 * π * t i :=
    contDiff_withAngles.continuous.comp (continuous_const.prodMk
      (continuous_pi fun i => continuous_const.mul (continuous_apply i)))
  exact Complex.continuous_ofReal.comp
    (hP.comp_continuous hΦ fun t => hsat w hw _)

/-- The Fourier coefficients of a real function are conjugate-symmetric. -/
theorem chartCoeff_neg (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2)) :
    chartCoeff P (-k) w = conj (chartCoeff P k w) := by
  unfold chartCoeff
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t₀ _ => ?_
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t₁ _ => ?_
  simp only [map_mul, Complex.conj_ofReal, charE, ← Complex.exp_conj, neg_neg, Pi.neg_apply]
  congr 2
  simp [Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- With `S` symmetric, `Σ_{k ∈ S} c_k e(k·t)` is real at real `t`. -/
theorem projSum_real (S : Finset (Fin 2 → ℤ)) (hS : ∀ k ∈ S, -k ∈ S) (P : Phase (2 + 2) → ℝ)
    (w : Phase (2 + 2)) (t : Fin 2 → ℝ) :
    (((∑ k ∈ S, chartCoeff P k w * charE k (fun i => (t i : ℂ))).re : ℝ) : ℂ) =
      ∑ k ∈ S, chartCoeff P k w * charE k (fun i => (t i : ℂ)) := by
  set z := ∑ k ∈ S, chartCoeff P k w * charE k (fun i => (t i : ℂ))
  have hconj : conj z = z := by
    simp only [z, map_sum, map_mul]
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) (fun k hk => hS k hk)
      (fun k hk => hS k hk) (fun k _ => neg_neg k) (fun k _ => neg_neg k) fun k _ => ?_
    rw [chartCoeff_neg]
    congr 1
    simp only [charE, ← Complex.exp_conj]
    congr 1
    simp [Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  exact Complex.conj_eq_iff_re.mp hconj

/-- The projection at real angles, as a Taylor × Fourier polynomial with constant coefficients. -/
def projPoly (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2)) : TFPoly :=
  Finsupp.onFinset S (fun k => if k ∈ S then MvPolynomial.C (chartCoeff P k w) else 0)
    fun k hk => by
      by_contra h
      exact hk (by simp [h])

theorem projPoly_eval (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ) (w : Phase (2 + 2))
    (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) :
    (projPoly S P w).eval θ u = ∑ k ∈ S, chartCoeff P k w * charE k θ := by
  unfold TFPoly.eval
  rw [Finsupp.sum_of_support_subset (projPoly S P w) (s := S)
    (by unfold projPoly; exact Finsupp.support_onFinset_subset) _ (fun k _ => by simp)]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [projPoly, Finsupp.onFinset_apply, hk]

/-- **`(1 - Π_S) P` is a pure tail** (2b): for a symmetric `S ∌ 0`, its Fourier coefficients
vanish on `S`. -/
theorem chartCoeff_sub_projS {U : Set (Phase (2 + 2))} (hsat : IsAngleSaturated U)
    {S : Finset (Fin 2 → ℤ)} {P : Phase (2 + 2) → ℝ} (hP : ContinuousOn P U)
    (hS : ∀ k ∈ S, -k ∈ S) :
    ∀ k ∈ S, ∀ w ∈ U, chartCoeff (fun y => P y - projS S P y) k w = 0 := by
  intro k hk w hw
  -- `Π_S P` at the angles `2πt` is the polynomial `projPoly`
  have hproj : ∀ θ : Fin 2 → ℂ, (∀ i, (θ i).im = 0) →
      chartFun (projS S P) w θ 0 = (projPoly S P w).eval θ 0 := by
    intro θ hθ
    have hθ' : θ = fun i => ((θ i).re : ℂ) := by
      funext i
      exact Complex.ext (by simp) (by simp [hθ i])
    rw [projPoly_eval]
    unfold chartFun projS
    simp only [chartCoeff_withAngles, withAngles_fst_fast]
    have harg : (fun i => ((2 * π * (θ i).re / (2 * π) : ℝ) : ℂ)) = fun i => ((θ i).re : ℂ) := by
      funext i
      congr 1
      field_simp
    rw [harg, projSum_real S hS P w (fun i => (θ i).re), ← hθ']
  have hc1 := chartCoeff_eq_fourierCoeff2 P k w
  have hc2 : chartCoeff (projS S P) k w = chartCoeff P k w := by
    rw [chartCoeff_eq_fourierCoeff2]
    have hcongr : fourierCoeff2 (chartFun (projS S P) w) k 0 =
        fourierCoeff2 (fun θ u => (projPoly S P w).eval θ u) k 0 := by
      unfold fourierCoeff2
      refine intervalIntegral.integral_congr fun t₀ _ =>
        intervalIntegral.integral_congr fun t₁ _ => ?_
      simp only
      rw [hproj _ (fun i => by fin_cases i <;> simp)]
    rw [hcongr, fourierCoeff2_eval]
    simp [projPoly, Finsupp.onFinset_apply, hk]
  have hcontP := continuous_chartFun hsat hP hw
  have hcontQ : Continuous fun t : Fin 2 → ℝ => chartFun (projS S P) w (fun i => (t i : ℂ)) 0 := by
    have e : (fun t : Fin 2 → ℝ => chartFun (projS S P) w (fun i => (t i : ℂ)) 0) =
        fun t => (projPoly S P w).eval (fun i => (t i : ℂ)) 0 := by
      funext t
      exact hproj _ fun i => by simp
    rw [e]
    simp only [projPoly_eval, charE, Fin.sum_univ_two]
    fun_prop
  have hdiff : chartCoeff (fun y => P y - projS S P y) k w =
      fourierCoeff2 (chartFun P w) k 0 - fourierCoeff2 (chartFun (projS S P) w) k 0 := by
    rw [fourierCoeff2_sub hcontP hcontQ, chartCoeff_eq_fourierCoeff2]
    unfold chartFun
    push_cast
    rfl
  rw [hdiff, ← hc1, ← chartCoeff_eq_fourierCoeff2, hc2, sub_self]

/-! ### (2c), (2d) The residuals -/

/-- **`r₁` is the tail** (2c): with `χ₁ = χ*(P)`, `residual₁ = P - Π_S P` on `U`, and its Fourier
coefficients on a symmetric `S` vanish. -/
theorem residual₁_tail {ν : Fin 2 → ℝ} {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) (hdom : U ⊆ poincareProdDom 2) {S : Finset (Fin 2 → ℤ)}
    {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) (hS : IsModeSet S (keplerFreq ν) U) :
    (∀ w ∈ U, residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P) w = P w - projS S P w) ∧
    ∀ k ∈ S, ∀ w ∈ U,
      chartCoeff (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)) k w = 0 := by
  have h1 : ∀ w ∈ U, residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P) w =
      P w - projS S P w := fun w hw => by
    rw [residual₁, pb_chiStar_hProd hU hsat hdom hP hS w hw]
  refine ⟨h1, fun k hk w hw => ?_⟩
  rw [show chartCoeff (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)) k w =
      chartCoeff (fun y => P y - projS S P y) k w by
    unfold chartCoeff
    refine intervalIntegral.integral_congr fun t₀ _ =>
      intervalIntegral.integral_congr fun t₁ _ => ?_
    simp only
    rw [h1 _ (hsat w hw _)]]
  exact chartCoeff_sub_projS hsat hP.continuousOn hS.1 k hk w hw

/-- **The order-2 part of `r₂` is the tail of `G₂`** (2d): with `χ₁ = χ*(P)`,
`G₂ = {P - ½ Π_S P, χ₁}` and `χ₂ = χ*(G₂)`, `residual₂ = G₂ - Π_S G₂` on `U`, and its Fourier
coefficients on a symmetric `S` vanish. -/
theorem residual₂_tail {ν : Fin 2 → ℝ} {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) (hdom : U ⊆ poincareProdDom 2) {S : Finset (Fin 2 → ℤ)}
    {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) (hS : IsModeSet S (keplerFreq ν) U) :
    let χ₁ := chiStar S (keplerFreq ν) P
    let G₂ := pb (fun y => P y - projS S P y / 2) χ₁
    let χ₂ := chiStar S (keplerFreq ν) G₂
    (∀ w ∈ U, residual₂ (hProd 1 ν) P χ₁ χ₂ w = G₂ w - projS S G₂ w) ∧
    ∀ k ∈ S, ∀ w ∈ U, chartCoeff (residual₂ (hProd 1 ν) P χ₁ χ₂) k w = 0 := by
  intro χ₁ G₂ χ₂
  have hfrq : ∀ w ∈ U, ContDiffAt ℝ ∞ (keplerFreq ν) (fast w.2) := fun w hw =>
    contDiffAt_keplerFreq ν (fast_ne_zero_of_mem_dom (hdom hw))
  have hχ₁ : ContDiffOn ℝ ∞ χ₁ U := contDiffOn_chiStar hU hsat hP hfrq hS
  have hA : ContDiffOn ℝ ∞ (fun y => P y - projS S P y / 2) U :=
    hP.sub ((contDiffOn_projS hU hsat S hP).div_const 2)
  have hG₂ : ContDiffOn ℝ ∞ G₂ U := fun y hy =>
    (contDiffAt_pb (hA.contDiffAt (hU.mem_nhds hy)) (hχ₁.contDiffAt (hU.mem_nhds hy)))
      |>.contDiffWithinAt
  have h2 : ∀ w ∈ U, residual₂ (hProd 1 ν) P χ₁ χ₂ w = G₂ w - projS S G₂ w := by
    intro w hw
    have heq : (fun z => P z - pb χ₁ (hProd 1 ν) z / 2) =ᶠ[𝓝 w]
        fun y => P y - projS S P y / 2 := by
      filter_upwards [hU.mem_nhds hw] with z hz
      rw [pb_chiStar_hProd hU hsat hdom hP hS z hz]
    have hpb : pb (fun z => P z - pb χ₁ (hProd 1 ν) z / 2) χ₁ w = G₂ w := by
      show fderiv ℝ _ w _ = fderiv ℝ _ w _
      rw [heq.fderiv_eq]
    rw [residual₂, hpb, pb_chiStar_hProd hU hsat hdom hG₂ hS w hw]
  refine ⟨h2, fun k hk w hw => ?_⟩
  rw [show chartCoeff (residual₂ (hProd 1 ν) P χ₁ χ₂) k w =
      chartCoeff (fun y => G₂ y - projS S G₂ y) k w by
    unfold chartCoeff
    refine intervalIntegral.integral_congr fun t₀ _ =>
      intervalIntegral.integral_congr fun t₁ _ => ?_
    simp only
    rw [h2 _ (hsat w hw _)]]
  exact chartCoeff_sub_projS hsat hG₂.continuousOn hS.1 k hk w hw

end HD11964.Cover

end
