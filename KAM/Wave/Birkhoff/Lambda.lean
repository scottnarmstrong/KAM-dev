/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Forms
public import KAM.Wave.Cubic.HamHamiltonian

/-!
# The linear part `Λ` (blueprint-W `bpW:w3:Lambda`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:Lambda`.

`birkLambda m hm ha hp y = Σ_{j≥1} λ_j w_j w_{-j}` (`w = birkCoord a p y`), `a ≥ 0`, `p ≥ 1/2`:

* `birkLamBil`, `birkLambda`, `norm_birkLambda_le` (`|Λ(w)| ≤ √(1+m) ‖w‖²`), analytic
  (`birkLambda_analyticOnNhd`);
* `birkLambda_birkZ`: `Λ(𝒵x) = ½ Σ_j λ_j (q_j² + p_j²)`;
* `hasFDerivAt_birkLambda`: `DΛ(w)v = Σ_{l≠0} λ_{|l|} w_{-l} v_l`;
* `birkXLam`: the linear field `X_Λ(w)_l = -i λ'_l w_l`, bounded `𝔚^+ → 𝔚` with norm `≤ √(1+m)`
  (`norm_birkXLam_le`), `birkLambda_field`: `DΛ(ι y) v = Ω(X_Λ y, v)`, and
  `not_exists_birkXLam_bounded`: `X_Λ` does not map `𝔚` into itself.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

theorem birk_weight_succ (a p : ℝ) (j : ℕ+) :
    ellWeight a (p + 1) j = (j : ℝ) * ellWeight a p j := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  unfold ellWeight
  rw [Real.rpow_add_one hj.ne']
  ring

/-- `λ_j w_j w'_{-j} = σ_j y_j y'_{-j}` with `σ_j = λ_j / ω_{a,p}(j)²` (`waveSigma`). -/
theorem birk_lam_mul_coord (a p : ℝ) (y y' : BirkSpace) (j : ℕ+) :
    (lam m hm j : ℂ) * birkCoord a p y (true, j) * birkCoord a p y' (false, j) =
      (waveSigma m hm a p j : ℂ) * y (true, j) * y' (false, j) := by
  have h : (ellWeight a p j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a p j)
  simp only [birkCoord, waveSigma]
  push_cast
  have h2 : (ellWeight a p j : ℂ) ^ 2 * ((ellWeight a p j : ℂ)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h]; simp
  field_simp
  linear_combination ((lam m hm j : ℂ) * y (true, j) * y' (false, j)) * h2

theorem birk_tsum_sq_split (y : BirkSpace) :
    ∑' j : ℕ+, ‖y (true, j)‖ ^ 2 + ∑' j : ℕ+, ‖y (false, j)‖ ^ 2 = ‖y‖ ^ 2 := by
  have h := lp_two_hasSum_sq y
  rw [← birk_tsum_split h.summable, h.tsum_eq]

theorem birk_tsum_sq_true_le (y : BirkSpace) : ∑' j : ℕ+, ‖y (true, j)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have hb := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq y).summable
  rw [← birk_tsum_sq_split y]
  exact le_add_of_nonneg_right (tsum_nonneg fun _ => by positivity)

theorem birk_tsum_sq_false_le (y : BirkSpace) : ∑' j : ℕ+, ‖y (false, j)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [← birk_tsum_sq_split y]
  exact le_add_of_nonneg_left (tsum_nonneg fun _ => by positivity)

/-- Cauchy–Schwarz for the `(true, j)`/`(false, j)` pairing. -/
theorem birkHalf_summable (y y' : BirkSpace) :
    Summable (fun j : ℕ+ => ‖y (true, j)‖ * ‖y' (false, j)‖) ∧
      ∑' j : ℕ+, ‖y (true, j)‖ * ‖y' (false, j)‖ ≤ ‖y‖ * ‖y'‖ := by
  have hb := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq y).summable
  have hb' := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq y').summable
  have h := waveCauchySchwarz_tsum (f := fun j : ℕ+ => ‖y (true, j)‖)
    (g := fun j : ℕ+ => ‖y' (false, j)‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    hb.1 hb'.2
  refine ⟨h.1, h.2.trans ?_⟩
  have e1 : Real.sqrt (∑' j : ℕ+, ‖y (true, j)‖ ^ 2) ≤ ‖y‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, birk_tsum_sq_true_le y⟩
  have e2 : Real.sqrt (∑' j : ℕ+, ‖y' (false, j)‖ ^ 2) ≤ ‖y'‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, birk_tsum_sq_false_le y'⟩
  exact mul_le_mul e1 e2 (Real.sqrt_nonneg _) (norm_nonneg _)

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The term `σ_j y_j y'_{-j}` of the bilinear form `Λ(y, y')`. -/
def birkLamTerm (a p : ℝ) (y y' : BirkSpace) (j : ℕ+) : ℂ :=
  (waveSigma m hm a p j : ℂ) * y (true, j) * y' (false, j)

include ha hp in
theorem norm_birkLamTerm_le (y y' : BirkSpace) (j : ℕ+) :
    ‖birkLamTerm m hm a p y y' j‖ ≤ Real.sqrt (1 + m) * (‖y (true, j)‖ * ‖y' (false, j)‖) := by
  unfold birkLamTerm
  rw [norm_mul, norm_mul, Complex.norm_real, ← mul_assoc]
  have := waveSigma_norm_le m hm ha hp j
  gcongr

include ha hp in
theorem summable_birkLamTerm (y y' : BirkSpace) : Summable (birkLamTerm m hm a p y y') :=
  Summable.of_norm_bounded ((birkHalf_summable y y').1.mul_left _)
    (norm_birkLamTerm_le m hm ha hp y y')

/-- The bounded bilinear form `Λ(y, y') = Σ_{j ≥ 1} λ_j w_j w'_{-j}` on `𝔚`. -/
def birkLamBil : BirkSpace →L[ℂ] BirkSpace →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun y y' => ∑' j, birkLamTerm m hm a p y y' j)
      (fun y₁ y₂ y' => by
        rw [← (summable_birkLamTerm m hm ha hp y₁ y').tsum_add (summable_birkLamTerm m hm ha hp y₂ y')]
        exact tsum_congr fun j => by simp only [birkLamTerm]; simp; ring)
      (fun c y y' => by
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun j => by simp only [birkLamTerm]; simp; ring)
      (fun y y₁ y₂ => by
        rw [← (summable_birkLamTerm m hm ha hp y y₁).tsum_add (summable_birkLamTerm m hm ha hp y y₂)]
        exact tsum_congr fun j => by simp only [birkLamTerm]; simp; ring)
      (fun c y y' => by
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun j => by simp only [birkLamTerm]; simp; ring))
    (Real.sqrt (1 + m)) (fun y y' => by
      show ‖∑' j, birkLamTerm m hm a p y y' j‖ ≤ Real.sqrt (1 + m) * ‖y‖ * ‖y'‖
      calc ‖∑' j, birkLamTerm m hm a p y y' j‖
          ≤ ∑' j, ‖birkLamTerm m hm a p y y' j‖ :=
            norm_tsum_le_tsum_norm (summable_birkLamTerm m hm ha hp y y').norm
        _ ≤ ∑' j : ℕ+, Real.sqrt (1 + m) * (‖y (true, j)‖ * ‖y' (false, j)‖) :=
            Summable.tsum_le_tsum (norm_birkLamTerm_le m hm ha hp y y')
              (summable_birkLamTerm m hm ha hp y y').norm
              ((birkHalf_summable y y').1.mul_left _)
        _ = Real.sqrt (1 + m) * ∑' j : ℕ+, ‖y (true, j)‖ * ‖y' (false, j)‖ := tsum_mul_left
        _ ≤ Real.sqrt (1 + m) * (‖y‖ * ‖y'‖) := by
            gcongr; exact (birkHalf_summable y y').2
        _ = Real.sqrt (1 + m) * ‖y‖ * ‖y'‖ := by ring)

theorem birkLamBil_apply (y y' : BirkSpace) :
    birkLamBil m hm ha hp y y' = ∑' j, birkLamTerm m hm a p y y' j := rfl

/-- (`bpW:w3:Lambda`) `Λ(w) = Σ_{j ≥ 1} λ_j w_j w_{-j}`. -/
def birkLambda (y : BirkSpace) : ℂ := birkLamBil m hm ha hp y y

theorem birkLambda_eq (y : BirkSpace) :
    birkLambda m hm ha hp y =
      ∑' j : ℕ+, (lam m hm j : ℂ) * birkCoord a p y (true, j) * birkCoord a p y (false, j) := by
  rw [birkLambda, birkLamBil_apply]
  exact tsum_congr fun j => (birk_lam_mul_coord m hm a p y y j).symm

/-- (`bpW:w3:Lambda`) `|Λ(w)| ≤ √(1+m) ‖w‖²`. -/
theorem norm_birkLambda_le (y : BirkSpace) :
    ‖birkLambda m hm ha hp y‖ ≤ Real.sqrt (1 + m) * ‖y‖ ^ 2 := by
  have hn : ‖birkLamBil m hm ha hp‖ ≤ Real.sqrt (1 + m) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y' => ?_
    rw [birkLamBil_apply]
    calc ‖∑' j, birkLamTerm m hm a p y y' j‖
        ≤ ∑' j, ‖birkLamTerm m hm a p y y' j‖ :=
          norm_tsum_le_tsum_norm (summable_birkLamTerm m hm ha hp y y').norm
      _ ≤ ∑' j : ℕ+, Real.sqrt (1 + m) * (‖y (true, j)‖ * ‖y' (false, j)‖) :=
          Summable.tsum_le_tsum (norm_birkLamTerm_le m hm ha hp y y')
            (summable_birkLamTerm m hm ha hp y y').norm ((birkHalf_summable y y').1.mul_left _)
      _ = Real.sqrt (1 + m) * ∑' j : ℕ+, ‖y (true, j)‖ * ‖y' (false, j)‖ := tsum_mul_left
      _ ≤ Real.sqrt (1 + m) * (‖y‖ * ‖y'‖) := by gcongr; exact (birkHalf_summable y y').2
      _ = _ := by ring
  rw [birkLambda]
  calc ‖birkLamBil m hm ha hp y y‖ ≤ ‖birkLamBil m hm ha hp y‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖birkLamBil m hm ha hp‖ * ‖y‖) * ‖y‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Real.sqrt (1 + m) * ‖y‖) * ‖y‖ := by gcongr
    _ = _ := by ring

theorem birkLambda_analyticOnNhd : AnalyticOnNhd ℂ (birkLambda m hm ha hp) Set.univ := by
  intro y _
  have hd : AnalyticAt ℂ (fun y : BirkSpace => (y, y)) y :=
    AnalyticAt.prod ((ContinuousLinearMap.id ℂ BirkSpace).analyticAt y)
      ((ContinuousLinearMap.id ℂ BirkSpace).analyticAt y)
  have hb := (birkLamBil m hm ha hp).analyticAt_bilinear (y, y)
  exact AnalyticAt.comp (g := fun z : BirkSpace × BirkSpace => birkLamBil m hm ha hp z.1 z.2)
    (f := fun y : BirkSpace => (y, y)) hb hd

/-- (`bpW:w3:Lambda`) `Λ(𝒵x) = ½ Σ_j λ_j (q_j² + p_j²)`. -/
theorem birkLambda_birkZ (x : WaveSpaceK ℂ) :
    birkLambda m hm ha hp (birkZ x) =
      ∑' j : ℕ+, (lam m hm j : ℂ) * ((coeffW a p x.1 j ^ 2 + coeffW a p x.2 j ^ 2) / 2) := by
  rw [birkLambda_eq]
  refine tsum_congr fun j => ?_
  rw [mul_assoc, birkCoord_mul_birkZ]

/-! ### The derivative and the Hamiltonian field -/

include ha hp in
theorem hasFDerivAt_birkLambda (y : BirkSpace) :
    HasFDerivAt (birkLambda m hm ha hp)
      (birkLamBil m hm ha hp y + (birkLamBil m hm ha hp).flip y) y := by
  have hid := (ContinuousLinearMap.id ℂ BirkSpace).hasFDerivAt (x := y)
  have hB := (birkLamBil m hm ha hp).hasFDerivAt_of_bilinear hid hid
  refine hB.congr_fderiv ?_
  ext v
  simp

theorem birkLambda_term_eq (a p : ℝ) (y v : BirkSpace) (l : BirkIdx) :
    (lam m hm l.2 : ℂ) * birkCoord a p y (birkNeg l) * birkCoord a p v l =
      (waveSigma m hm a p l.2 : ℂ) * y (birkNeg l) * v l := by
  have h : (ellWeight a p l.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a p l.2)
  simp only [birkCoord, waveSigma, birkNeg_snd]
  push_cast
  have h2 : (ellWeight a p l.2 : ℂ) ^ 2 * ((ellWeight a p l.2 : ℂ)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h]; simp
  field_simp
  linear_combination ((lam m hm l.2 : ℂ) * y (birkNeg l) * v l) * h2

include ha hp in
theorem summable_birkLambda_term (y v : BirkSpace) :
    Summable fun l : BirkIdx => (lam m hm l.2 : ℂ) * birkCoord a p y (birkNeg l) * birkCoord a p v l := by
  refine Summable.of_norm_bounded
    ((birkPair_summable v y).1.mul_left (Real.sqrt (1 + m))) fun l => ?_
  rw [birkLambda_term_eq, norm_mul, norm_mul, Complex.norm_real]
  have := waveSigma_norm_le m hm ha hp l.2
  calc ‖waveSigma m hm a p l.2‖ * ‖y (birkNeg l)‖ * ‖v l‖
      ≤ Real.sqrt (1 + m) * ‖y (birkNeg l)‖ * ‖v l‖ := by gcongr
    _ = _ := by ring

include ha hp in
/-- (`bpW:w3:Lambda`) `DΛ(w) v = Σ_{l≠0} λ_{|l|} w_{-l} v_l`. -/
theorem fderiv_birkLambda_apply (y v : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) y v =
      ∑' l : BirkIdx, (lam m hm l.2 : ℂ) * birkCoord a p y (birkNeg l) * birkCoord a p v l := by
  rw [(hasFDerivAt_birkLambda m hm ha hp y).fderiv]
  have hs := summable_birkLambda_term m hm ha hp y v
  rw [birk_tsum_split hs]
  have h1 : Summable fun j : ℕ+ => birkLamTerm m hm a p v y j := summable_birkLamTerm m hm ha hp v y
  have h2 : Summable fun j : ℕ+ => birkLamTerm m hm a p y v j := summable_birkLamTerm m hm ha hp y v
  have e1 : ∀ j : ℕ+, (lam m hm (true, j).2 : ℂ) * birkCoord a p y (birkNeg (true, j)) *
      birkCoord a p v (true, j) = birkLamTerm m hm a p v y j := fun j => by
    rw [birkLambda_term_eq]; simp [birkLamTerm, birkNeg]; ring
  have e2 : ∀ j : ℕ+, (lam m hm (false, j).2 : ℂ) * birkCoord a p y (birkNeg (false, j)) *
      birkCoord a p v (false, j) = birkLamTerm m hm a p y v j := fun j => by
    rw [birkLambda_term_eq]; simp [birkLamTerm, birkNeg]
  simp only [e1, e2]
  simp only [add_apply, ContinuousLinearMap.flip_apply, birkLamBil_apply]
  ring

/-- (`bpW:w3:Lambda`) The linear field `X_Λ`, `X_Λ(w)_l = -i λ'_l w_l` for `w ∈ 𝔚^+`
(input read at weight `p + 1`, output at weight `p`). -/
def birkXLam : BirkSpace →L[ℂ] BirkSpace :=
  lpDiagCLM (fun l : BirkIdx => -Complex.I * birkSgn l * ((lamRatio m hm 1 l.2 : ℝ) : ℂ))
    (M := Real.sqrt (1 + m)) (Real.sqrt_nonneg _) (fun l => by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, norm_birkSgn, one_mul, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lamRatio_pos hm 1 l.2)]
      unfold lamRatio
      rw [Real.rpow_one]
      exact lam_div_pnat_le hm l.2)

@[simp] theorem birkXLam_apply (y : BirkSpace) (l : BirkIdx) :
    birkXLam m hm y l = -Complex.I * birkSgn l * ((lamRatio m hm 1 l.2 : ℝ) : ℂ) * y l := rfl

/-- (`bpW:w3:Lambda`) `‖X_Λ‖ ≤ √(1+m)` as an operator `𝔚^+ → 𝔚`. -/
theorem norm_birkXLam_le : ‖birkXLam m hm‖ ≤ Real.sqrt (1 + m) :=
  norm_lpDiagCLM_le _ _ _

/-- (`bpW:w3:Lambda`) `X_Λ(w)_l = -i sgn(l) λ_{|l|} w_l` in the actual coordinates
(`w ∈ 𝔚^+` read at weight `p + 1`, the value at weight `p`). -/
theorem birkCoord_birkXLam (a p : ℝ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a p (birkXLam m hm y) l =
      -Complex.I * birkSgn l * (lam m hm l.2 : ℂ) * birkCoord a (p + 1) y l := by
  have hw := birk_weight_succ a p l.2
  have h : (ellWeight a p l.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a p l.2)
  have hj : ((l.2 : ℕ+) : ℂ) ≠ 0 := by exact_mod_cast l.2.ne_zero
  simp only [birkCoord, birkXLam_apply, lamRatio, Real.rpow_one, hw]
  push_cast
  field_simp

include ha hp in
/-- (`bpW:w3:Lambda`) For `y ∈ 𝔚^+`: `DΛ(ι y) v = Ω(X_Λ(y), v)`. -/
theorem birkLambda_field (y v : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) (birkEmbed a (p + 1) p (by linarith) y) v =
      birkOmega ha (by linarith : (0 : ℝ) ≤ p) (birkXLam m hm y) v := by
  rw [fderiv_birkLambda_apply m hm ha hp, birkOmega_apply]
  have hs := (summable_birkLambda_term m hm ha hp (birkEmbed a (p + 1) p (by linarith) y) v)
  rw [← birkNegEquiv.tsum_eq] 
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [birkNegEquiv, Equiv.coe_fn_mk, birkNeg_birkNeg, birkNeg_snd,
    birkCoord_birkXLam, birkCoord_birkEmbed]
  have := birkSgn_mul_self l
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((lam m hm l.2 : ℂ) * birkCoord a (p + 1) y l * birkCoord a p v (birkNeg l)) * hI +
    ((lam m hm l.2 : ℂ) * birkCoord a (p + 1) y l * birkCoord a p v (birkNeg l) *
      (Complex.I * Complex.I)) * this

omit ha hp in
/-- (`bpW:w3:Lambda`) `X_Λ` does not map `𝔚` into itself: there is no bounded operator on `𝔚` with
the coordinates `-i sgn(l) λ_{|l|} w_l`. -/
theorem not_exists_birkXLam_bounded :
    ¬ ∃ T : BirkSpace →L[ℂ] BirkSpace, ∀ (y : BirkSpace) (l : BirkIdx),
      birkCoord a p (T y) l = -Complex.I * birkSgn l * (lam m hm l.2 : ℂ) * birkCoord a p y l := by
  rintro ⟨T, hT⟩
  refine not_exists_lpDiag_of_unbounded (μ := fun l : BirkIdx => -Complex.I * birkSgn l * (lam m hm l.2 : ℂ))
    (fun B => ?_) ⟨T, fun y l => ?_⟩
  · refine ⟨(true, (⟨⌈B⌉₊ + 1, Nat.succ_pos _⟩ : ℕ+)), ?_⟩
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, norm_birkSgn, one_mul, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le (by positivity)
        (pnat_le_lam hm _))]
    refine lt_of_lt_of_le ?_ (pnat_le_lam hm _)
    simp only [PNat.mk_coe]
    push_cast
    linarith [Nat.le_ceil B]
  · have h := hT y l
    have hw := ellWeight_cast_ne_zero (K := ℂ) a p l.2
    simp only [birkCoord] at h
    rw [div_eq_iff hw] at h
    rw [h]
    field_simp

end

end KAM.Wave

end
