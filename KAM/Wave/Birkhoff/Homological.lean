/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.HomSum

/-!
# The homological identity (blueprint-W `bpW:w3:homological`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-DIVISOR-F, blueprint label `bpW:w3:homological`.

`birk_homological`: for every `w ∈ 𝔚`, `DΛ(w) X_F(w) = Z'(w) = Ḡ(w) - G^{tan}(w)` (with `X_F(w) ∈ 𝔚⁺`
embedded in `𝔚`); `birk_homological'`: `G + DΛ·X_F = Ḡ + G^{nor}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- `δ_x f_x = -(c̄_x - c^{tan}_x)`: the divided coefficient times the divisor is the resonant
difference. -/
theorem birk_delta_mul_fx (x : Fin 4 → BirkIdx) :
    ((birkDivisor m hm x * birkFx m hm x : ℝ) : ℂ) = -(birkCoefBar m hm x - birkCoefTan m hm x) := by
  classical
  unfold birkFx birkCoefBar birkCoefTan birkQuartCoefOn birkBarSet
  by_cases hT : x ∈ birkTanSet
  · by_cases hP : birkPaired x
    · have h0 := birkPaired_divisor_eq_zero m hm x hP
      simp [hT, hP, h0]
    · by_cases hg : birkG m hm x = 0
      · simp [hT, hP, hg]
      · have := birk_divisor_bound_tan m hm x hT hg hP
        have hd : birkDivisor m hm x ≠ 0 := by
          intro h0; rw [h0] at this; simp at this
          have hs : 0 < birkDeltaStar m := by unfold birkDeltaStar; positivity
          linarith
        have hdc : ((birkDivisor m hm x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd
        simp [hT, hP, hg, hd]
        field_simp
  · simp [hT]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- The coordinates of `X_F(w)` (actual coordinates at weight `p + 1`). -/
theorem birkCoord_birkXF (w : BirkSpace) (l : BirkIdx) :
    birkCoord a (p + 1) (birkDiagField (birkFgrad m hm ha hp) w) l =
      (4 : ℂ) * ((birkDeltaStar m : ℂ)⁻¹ * ((-Complex.I * birkSgn l / 16) *
        ∑' y : Fin 3 → BirkIdx, birkFcoef m hm ![y 0, y 1, y 2, birkNeg l] *
          ∏ t, birkCoord a p w (y t))) := by
  unfold birkDiagField birkFgrad
  rw [birkCoord_smul]
  simp only [ContinuousMultilinearMap.smul_apply]
  rw [birkCoord_smul, birkCoord_birkGradML m hm ha hp (birkFcoef_isCoef m hm).bound]
  push_cast; ring

/-- The summand `H(x) = λ'_{x₄} f_x ∏_t w_{x_t}`. -/
def birkHterm (a p : ℝ) (w : BirkSpace) (x : Fin 4 → BirkIdx) : ℂ :=
  ((birkLam m hm (x 3) * birkFx m hm x : ℝ) : ℂ) * ∏ t, birkCoord a p w (x t)

include ha hp in
theorem summable_birkHterm (w : BirkSpace) : Summable (birkHterm m hm a p w) := by
  have hs := summable_birkLamQuartTerm m hm ha hp (birkFcoef_isCoef m hm).bound w
  have hd := birkDeltaStar_pos m hm
  refine Summable.of_norm_bounded (hs.mul_left (birkDeltaStar m)⁻¹) fun x => ?_
  have e1 : ‖birkFcoef m hm x‖ = birkDeltaStar m * |birkFx m hm x| := by
    unfold birkFcoef
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hd]
  have key : ∀ q : BirkIdx, |birkLam m hm q| = lam m hm q.2 := by
    rintro ⟨b, j⟩
    have := wave_lam_pos m hm j
    cases b <;> simp [birkLam, abs_of_pos this]
  have e2 := key (x 3)
  unfold birkHterm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, e2]
  have e3 : ‖(lam m hm (x 3).2 : ℂ) * (birkFcoef m hm x * birkAtom a p x (fun _ => w))‖ =
      lam m hm (x 3).2 * (birkDeltaStar m * |birkFx m hm x| * ‖∏ t, birkCoord a p w (x t)‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wave_lam_pos m hm _), norm_mul,
      e1, birkAtom_apply]
  rw [e3]
  have hl := wave_lam_pos m hm (x 3).2
  field_simp
  exact le_of_eq (by ring)

/-- The term with the divisor split off at position `t`. -/
def birkHtermAt (a p : ℝ) (w : BirkSpace) (t : Fin 4) (x : Fin 4 → BirkIdx) : ℂ :=
  ((birkLam m hm (x t) * birkFx m hm x : ℝ) : ℂ) * ∏ u, birkCoord a p w (x u)

theorem birkHtermAt_swap (a p : ℝ) (w : BirkSpace) (t : Fin 4) (x : Fin 4 → BirkIdx) :
    birkHtermAt m hm a p w 3 (fun i => x (Equiv.swap t 3 i)) = birkHtermAt m hm a p w t x := by
  unfold birkHtermAt
  rw [birkFx_perm m hm (Equiv.swap t 3) x]
  simp only [Equiv.swap_apply_right]
  congr 1
  exact Equiv.prod_comp (Equiv.swap t 3) (fun u => birkCoord a p w (x u))

include ha hp in
theorem birkHtermAt_tsum (w : BirkSpace) (t : Fin 4) :
    ∑' x, birkHtermAt m hm a p w t x = ∑' x, birkHterm m hm a p w x := by
  have h := (Equiv.arrowCongr (Equiv.swap t 3) (Equiv.refl BirkIdx)).tsum_eq
    (fun x => birkHtermAt m hm a p w 3 x)
  have hdef : birkHterm m hm a p w = birkHtermAt m hm a p w 3 := rfl
  rw [hdef, ← h]
  refine tsum_congr fun x => ?_
  have := birkHtermAt_swap m hm a p w t x
  simpa [Equiv.arrowCongr, Function.comp_def] using this.symm

include ha hp in
theorem summable_birkHtermAt (w : BirkSpace) (t : Fin 4) : Summable (birkHtermAt m hm a p w t) := by
  have h := summable_birkHterm m hm ha hp w
  have h2 := (Equiv.arrowCongr (Equiv.swap t 3) (Equiv.refl BirkIdx)).summable_iff
    (f := fun x => birkHtermAt m hm a p w 3 x) |>.2 h
  refine h2.congr fun x => ?_
  have := birkHtermAt_swap m hm a p w t x
  simpa [Equiv.arrowCongr, Function.comp_def] using this

include ha hp in
/-- Symmetrization (Euler identity): `4 Σ_x λ'_{x₄} f_x w_x = Σ_x δ_x f_x w_x`. -/
theorem birk_euler (w : BirkSpace) :
    (4 : ℂ) * ∑' x, birkHterm m hm a p w x =
      ∑' x : Fin 4 → BirkIdx, ((birkDivisor m hm x * birkFx m hm x : ℝ) : ℂ) *
        ∏ t, birkCoord a p w (x t) := by
  have e : ∀ x : Fin 4 → BirkIdx, ((birkDivisor m hm x * birkFx m hm x : ℝ) : ℂ) *
      ∏ t, birkCoord a p w (x t) = ∑ t : Fin 4, birkHtermAt m hm a p w t x := fun x => by
    simp only [birkDivisor, Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, birkHtermAt]
  simp only [e]
  rw [Summable.tsum_finsetSum (fun t _ => summable_birkHtermAt m hm ha hp w t)]
  simp only [birkHtermAt_tsum m hm ha hp w, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

theorem birkLam_cast (q : BirkIdx) :
    ((birkLam m hm q : ℝ) : ℂ) = birkSgn q * (lam m hm q.2 : ℂ) := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkLam, birkSgn]

include ha hp in
/-- `DΛ(w) X_F(w) = -(1/4) Σ_x λ'_{x₄} f_x w_x`. -/
theorem birk_DLam_XF (w : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) w (birkEmbed a (p + 1) p (by linarith)
        (birkDiagField (birkFgrad m hm ha hp) w)) =
      (-(1 / 4) : ℂ) * ∑' x, birkHterm m hm a p w x := by
  rw [fderiv_birkLambda_apply m hm ha hp]
  simp only [birkCoord_birkEmbed, birkCoord_birkXF m hm ha hp]
  rw [← birkNegEquiv.tsum_eq]
  have hd : ((birkDeltaStar m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (birkDeltaStar_pos m hm).ne'
  have hT : ∀ r : BirkIdx, (lam m hm (birkNegEquiv r).2 : ℂ) * birkCoord a p w (birkNeg (birkNegEquiv r)) *
      ((4 : ℂ) * ((birkDeltaStar m : ℂ)⁻¹ * ((-Complex.I * birkSgn (birkNegEquiv r) / 16) *
        ∑' y : Fin 3 → BirkIdx, birkFcoef m hm ![y 0, y 1, y 2, birkNeg (birkNegEquiv r)] *
          ∏ t, birkCoord a p w (y t)))) =
      ∑' y : Fin 3 → BirkIdx, (-(1 / 4) : ℂ) * birkHterm m hm a p w (birkSplit4 (r, y)) := by
    intro r
    simp only [birkNegEquiv, Equiv.coe_fn_mk, birkNeg_birkNeg, birkNeg_snd]
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun y => ?_
    unfold birkHterm birkFcoef
    have hx : birkSplit4 (r, y) = ![y 0, y 1, y 2, r] := rfl
    have h0 : (![y 0, y 1, y 2, r] : Fin 4 → BirkIdx) 0 = y 0 := rfl
    have h1 : (![y 0, y 1, y 2, r] : Fin 4 → BirkIdx) 1 = y 1 := rfl
    have h2 : (![y 0, y 1, y 2, r] : Fin 4 → BirkIdx) 2 = y 2 := rfl
    have h3 : (![y 0, y 1, y 2, r] : Fin 4 → BirkIdx) 3 = r := rfl
    simp only [hx, Fin.prod_univ_four, Fin.prod_univ_three, h0, h1, h2, h3]
    push_cast
    rw [birkLam_cast, birkSgn_neg]
    have hI := Complex.I_mul_I
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [tsum_congr hT]
  have hsum : Summable fun q : BirkIdx × (Fin 3 → BirkIdx) =>
      (-(1 / 4) : ℂ) * birkHterm m hm a p w (birkSplit4 q) :=
    ((birkSplit4.summable_iff (f := fun x => birkHterm m hm a p w x)).2
      (summable_birkHterm m hm ha hp w)).mul_left _
  rw [← hsum.tsum_prod, tsum_mul_left]
  congr 1
  exact birkSplit4.tsum_eq (fun x => birkHterm m hm a p w x)

include ha hp in
/-- (`bpW:w3:homological`) For every `w ∈ 𝔚`: `DΛ(w) X_F(w) = Z'(w) = Ḡ(w) - G^{tan}(w)`. -/
theorem birk_homological (w : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) w (birkEmbed a (p + 1) p (by linarith)
        (birkDiagField (birkFgrad m hm ha hp) w)) =
      birkQuartP m hm ha hp (birkCoefBar_isCoef m hm) w -
        birkQuartP m hm ha hp (birkCoefTan_isCoef m hm) w := by
  rw [birk_DLam_XF m hm ha hp w]
  have h4 := birk_euler m hm ha hp w
  have hbar := (summable_birkQuartTerm m hm ha hp (birkCoefBar_isCoef m hm).bound (fun _ => w)).of_norm
  have htan := (summable_birkQuartTerm m hm ha hp (birkCoefTan_isCoef m hm).bound (fun _ => w)).of_norm
  have e : ∀ x : Fin 4 → BirkIdx, ((birkDivisor m hm x * birkFx m hm x : ℝ) : ℂ) *
      ∏ t, birkCoord a p w (x t) =
      -(birkCoefBar m hm x * birkAtom a p x (fun _ => w) -
        birkCoefTan m hm x * birkAtom a p x (fun _ => w)) := fun x => by
    rw [birk_delta_mul_fx, birkAtom_apply]; ring
  simp only [e] at h4
  rw [tsum_neg, Summable.tsum_sub hbar htan] at h4
  unfold birkQuartP birkDiag
  rw [birkQuartForm_apply, birkQuartForm_apply]
  unfold birkQuartSum
  have : ∑' x, birkHterm m hm a p w x = -(1 / 4 : ℂ) * (∑' x : Fin 4 → BirkIdx,
      birkCoefBar m hm x * birkAtom a p x (fun _ => w) -
        ∑' x : Fin 4 → BirkIdx, birkCoefTan m hm x * birkAtom a p x (fun _ => w)) := by
    have : (4 : ℂ) * ∑' x, birkHterm m hm a p w x = -(∑' x : Fin 4 → BirkIdx,
      birkCoefBar m hm x * birkAtom a p x (fun _ => w) -
        ∑' x : Fin 4 → BirkIdx, birkCoefTan m hm x * birkAtom a p x (fun _ => w)) := h4
    linear_combination (1 / 4 : ℂ) * this
  rw [this]
  ring

include ha hp in
/-- (`bpW:w3:homological`, second form) `G + DΛ·X_F = Ḡ + G^{nor}`. -/
theorem birk_homological' (w : BirkSpace) :
    birkQuartP m hm ha hp (birkCoefAll_isCoef m hm) w +
      fderiv ℂ (birkLambda m hm ha hp) w (birkEmbed a (p + 1) p (by linarith)
        (birkDiagField (birkFgrad m hm ha hp) w)) =
      birkQuartP m hm ha hp (birkCoefBar_isCoef m hm) w +
        birkQuartP m hm ha hp (birkCoefNor_isCoef m hm) w := by
  rw [birk_homological m hm ha hp w, birkQuartP_all_eq_tan_add_nor m hm ha hp w]
  ring

end

end KAM.Wave

end
