/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartMain
public import KAM.Wave.Cubic.CubicMap
public import KAM.Wave.Cubic.HamHamiltonian

/-!
# Identification with Part 0 (blueprint-W `bpW:w3:quartic-ident`), the full quartic

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic-ident`.

For the coefficient `𝔤` on all of `(ℤ∖0)⁴` (`birkCoefAll`; `G = P`),
at every point `x` of the complex
phase space `E^ℂ` (in particular on real points):

* `birkQuartP_birkZ`: `G(𝒵x) = ¼ Σ_{ijkl} g_{ijkl} q̂_i q̂_j q̂_k q̂_l`,
  the Part 0 series; for `a > 0`
  it is `waveG` of the coordinates (`birkQuartP_birkZ_real`);
* `birkZinv_birkQuartX`: `𝒵⁻¹ X_G(𝒵x) = (0, -T(q,q,q)) = waveXG x`, the field of Part 0
  (the landed `waveXG`, the representative of `(0, -𝒢(q))`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The coefficient `𝔤_x` on all of `(ℤ ∖ {0})⁴`. -/
def birkCoefAll : (Fin 4 → BirkIdx) → ℂ := birkQuartCoefOn m hm Set.univ

theorem birkCoefAll_isCoef : IsBirkQuartCoef m hm (birkCoefAll m hm) :=
  isBirkQuartCoef_on m hm Set.univ (by simp) (by simp)

theorem birkCoefAll_apply (x : Fin 4 → BirkIdx) :
    birkCoefAll m hm x = ((waveTriCoef m hm (x 0).2 (x 1).2 (x 2).2 (x 3).2 : ℝ) : ℂ) := by
  simp [birkCoefAll, birkQuartCoefOn, birkG]

theorem birkCoord_fold (a p : ℝ) (x : WaveSpaceK ℂ) (j : ℕ+) :
    birkCoord a p (birkZ x) (true, j) + birkCoord a p (birkZ x) (false, j) =
      birkSqrt2 * coeffW a p x.1 j := by
  rw [birkCoord_birkZ_true, birkCoord_birkZ_false]
  have h := birkSqrt2_sq
  have h2 := birkSqrt2_ne
  field_simp
  linear_combination (-(coeffW a p x.1 j)) * h

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:quartic-ident`) `G(𝒵x) = ¼ Σ_{ijkl} g_{ijkl} q̂_i q̂_j q̂_k q̂_l`
(`= ¼ Σ 𝔤_{ijkl} q_i q_j q_k q_l`), for every `a ≥ 0`. -/
theorem birkQuartP_birkZ (x : WaveSpaceK ℂ) :
    birkQuartP m hm ha hp (birkCoefAll_isCoef m hm) (birkZ x) =
      (1 / 4 : ℂ) * ∑' mm : Fin 4 → ℕ+,
        (waveTriCoef m hm (mm 0) (mm 1) (mm 2) (mm 3) : ℂ) * ∏ t, coeffW a p x.1 (mm t) := by
  have hc := birkCoefAll_isCoef m hm
  set w := birkZ x with hw
  have hsum : Summable fun y : Fin 4 → BirkIdx =>
      ((waveTriCoef m hm (birkAbs y 0) (birkAbs y 1) (birkAbs y 2) (birkAbs y 3) : ℝ) : ℂ) *
        ∏ t, birkCoord a p w (y t) := by
    refine ((summable_birkQuartTerm m hm ha hp hc.bound (fun _ => w)).of_norm).congr fun y => ?_
    rw [birkCoefAll_apply, birkAtom_apply]; rfl
  unfold birkQuartP birkDiag
  rw [birkQuartForm_apply]
  unfold birkQuartSum
  have e1 : ∀ y : Fin 4 → BirkIdx, birkCoefAll m hm y * birkAtom a p y (fun _ => w) =
      ((waveTriCoef m hm (birkAbs y 0) (birkAbs y 1) (birkAbs y 2) (birkAbs y 3) : ℝ) : ℂ) *
        ∏ t, birkCoord a p w (y t) := fun y => by
    rw [birkCoefAll_apply, birkAtom_apply]; rfl
  simp only [e1]
  rw [birk_pi_fold (fun mm => ((waveTriCoef m hm (mm 0) (mm 1) (mm 2) (mm 3) : ℝ) : ℂ))
    (fun _ l => birkCoord a p w l) hsum, ← tsum_mul_left]
  rw [← tsum_mul_left]
  refine tsum_congr fun mm => ?_
  have hf : ∀ t : Fin 4, birkCoord a p w (true, mm t) + birkCoord a p w (false, mm t) =
      birkSqrt2 * coeffW a p x.1 (mm t) := fun t => birkCoord_fold a p x (mm t)
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h4 : birkSqrt2 ^ 4 = 4 := by
    have := birkSqrt2_sq
    calc birkSqrt2 ^ 4 = (birkSqrt2 ^ 2) ^ 2 := by ring
      _ = 4 := by rw [this]; norm_num
  rw [h4]; ring

omit hp in
/-- `Fin 4 → ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ × ℕ+`. -/
def birkQuadEquiv : (Fin 4 → ℕ+) ≃ ℕ+ × ℕ+ × ℕ+ × ℕ+ where
  toFun mm := (mm 0, mm 1, mm 2, mm 3)
  invFun t := ![t.1, t.2.1, t.2.2.1, t.2.2.2]
  left_inv mm := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

@[simp] theorem birkQuadEquiv_apply (mm : Fin 4 → ℕ+) :
    birkQuadEquiv mm = (mm 0, mm 1, mm 2, mm 3) := rfl

end

section

variable {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:quartic-ident`) For real `x = (q, p)`, `a > 0`: `G(𝒵x) = G(q)` of Definition `bpW:w0:H`
(the landed `waveG`, in weighted coordinates `q = κ_{a,p} y`). -/
theorem birkQuartP_birkZ_real (y y' : lp (fun _ : ℕ+ => ℝ) 2) :
    birkQuartP m hm ha.le hp (birkCoefAll_isCoef m hm) (birkZ (birkReal (y, y'))) =
      ((waveG m hm (coeffW a p y) : ℝ) : ℂ) := by
  rw [birkQuartP_birkZ m hm ha.le hp]
  have hc : WaveEll a p (coeffW a p y) := (waveEll_iff_isEll a p _).2 (isEll_coeffW a p y)
  have h := (waveG_hasSum (m := m) hm ha hc).1
  have h2 : ((waveG m hm (coeffW a p y) : ℝ) : ℂ) = ∑' t : ℕ+ × ℕ+ × ℕ+ × ℕ+,
      (((1 / 4) * ((waveHat m hm (coeffW a p y) t.1 *
        (waveHat m hm (coeffW a p y) t.2.1 * (waveHat m hm (coeffW a p y) t.2.2.1 *
          waveHat m hm (coeffW a p y) t.2.2.2))) * waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2) : ℝ) :
        ℂ) := by
    rw [← h.tsum_eq, Complex.ofReal_tsum]
  rw [h2, ← birkQuadEquiv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun mm => ?_
  have hl : ∀ j : ℕ+, (Real.sqrt (lam m hm j) : ℝ) ≠ 0 := fun j => (wave_sqrt_lam_pos m hm j).ne'
  simp only [birkQuadEquiv_apply, waveHat, waveTriCoef, birkReal_apply,
    coeffW_complexifyLp, Fin.prod_univ_four]
  push_cast
  have := hl (mm 0); have := hl (mm 1); have := hl (mm 2); have := hl (mm 3)
  have h0 : ∀ j : ℕ+, ((Real.sqrt (lam m hm j) : ℝ) : ℂ) ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.2 (hl j)
  have := h0 (mm 0); have := h0 (mm 1); have := h0 (mm 2); have := h0 (mm 3)
  field_simp

end

section

variable {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- The coordinates of the gradient at `𝒵x` (Step "the field"):
`X_G(𝒵x)_l = -i sgn(l) (√2/2) T(q,q,q)_{|l|}` in the actual coordinates at weight `p + 1`. -/
theorem birkCoord_birkQuartX_birkZ (x : WaveSpaceK ℂ) (l : BirkIdx) :
    birkCoord a (p + 1) (birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZ x)) l =
      -Complex.I * birkSgn l * (birkSqrt2 / 2) *
        waveTriSeq (K := ℂ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1) l.2 := by
  have hc := birkCoefAll_isCoef m hm
  set w := birkZ x with hw
  unfold birkQuartX birkDiagField
  rw [birkCoord_smul, birkCoord_birkGradML m hm ha hp hc.bound]
  have hsum : Summable fun y : Fin 3 → BirkIdx =>
      ((waveTriCoef m hm (birkAbs y 0) (birkAbs y 1) (birkAbs y 2) l.2 : ℝ) : ℂ) *
        ∏ t, birkCoord a p w (y t) := by
    refine (summable_birkGradTerm m hm ha hp hc.bound l (fun _ => w)).congr fun y => ?_
    simp only [birkGradTerm, birkCoefAll_apply]
    rfl
  have e1 : ∀ y : Fin 3 → BirkIdx,
      birkCoefAll m hm ![y 0, y 1, y 2, birkNeg l] * ∏ t, birkCoord a p w (y t) =
      ((waveTriCoef m hm (birkAbs y 0) (birkAbs y 1) (birkAbs y 2) l.2 : ℝ) : ℂ) *
        ∏ t, birkCoord a p w (y t) := fun y => by
    rw [birkCoefAll_apply]; rfl
  simp only [e1]
  rw [birk_pi_fold (fun mm => ((waveTriCoef m hm (mm 0) (mm 1) (mm 2) l.2 : ℝ) : ℂ))
    (fun _ l => birkCoord a p w l) hsum]
  have hf : ∀ (mm : Fin 3 → ℕ+) (t : Fin 3),
      birkCoord a p w (true, mm t) + birkCoord a p w (false, mm t) =
        birkSqrt2 * coeffW a p x.1 (mm t) := fun mm t => birkCoord_fold a p x (mm t)
  have hS : ∑' mm : Fin 3 → ℕ+, ((waveTriCoef m hm (mm 0) (mm 1) (mm 2) l.2 : ℝ) : ℂ) *
      ∏ t, (birkCoord a p w (true, mm t) + birkCoord a p w (false, mm t)) =
      birkSqrt2 ^ 3 * waveTriSeq (K := ℂ) m hm (coeffW a p x.1) (coeffW a p x.1)
        (coeffW a p x.1) l.2 := by
    unfold waveTriSeq waveSelSum
    rw [← tsum_mul_left, ← birkTriEquiv.tsum_eq]
    refine tsum_congr fun mm => ?_
    simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      birkTriEquiv_apply, Fin.prod_univ_three]
    rw [show ((waveTriCoef m hm (mm 0) (mm 1) (mm 2) l.2 : ℝ) : ℂ) =
      RCLike.ofReal (waveTriCoef m hm (mm 0) (mm 1) (mm 2) l.2) from rfl]
    ring
  rw [hS]
  have h2 := birkSqrt2_sq
  push_cast
  linear_combination (-Complex.I * birkSgn l * waveTriSeq (K := ℂ) m hm (coeffW a p x.1)
    (coeffW a p x.1) (coeffW a p x.1) l.2 * birkSqrt2 / 4) * h2

include ha hp in
/-- (`bpW:w3:quartic-ident`) `𝒵⁻¹ X_G(𝒵x) = (0, -T(q,q,q))`: the landed field `waveXG` of Part 0
(in weighted coordinates at weight `(a, p)`), at every point of `E^ℂ`. -/
theorem birkZinv_birkQuartX_birkZ (x : WaveSpaceK ℂ) :
    birkZinv (birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZ x)) =
      waveXG (K := ℂ) m hm ha hp x := by
  set X := birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZ x) with hX
  set T := waveTriSeq (K := ℂ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1) with hT
  have hXl : ∀ l : BirkIdx, X l = (-Complex.I * birkSgn l * (birkSqrt2 / 2) * T l.2) *
      (RCLike.ofReal (ellWeight a (p + 1) l.2) : ℂ) := fun l => by
    rw [← birkCoord_mul_weight a (p + 1) X l, hX, birkCoord_birkQuartX_birkZ m hm ha hp]
  have h2 := birkSqrt2_sq
  have h3 := birkSqrt2_ne
  have hI := Complex.I_ne_zero
  have hcub : ∀ j : ℕ+, (waveCubicNL (K := ℂ) m hm ha hp x.1) j =
      T j * (RCLike.ofReal (ellWeight a (p + 1) j) : ℂ) := fun j => by
    have h := coeffW_waveTriML (K := ℂ) m hm ha hp x.1 x.1 x.1
    rw [← waveCubicNL_eq] at h
    have := congrFun h j
    rw [coeffW_apply, hT] at *
    rw [← this]
    have hw := ellWeight_cast_ne_zero (K := ℂ) a (p + 1) j
    field_simp
  refine Prod.ext (lp.ext (funext fun j => ?_)) (lp.ext (funext fun j => ?_))
  · simp only [birkZinv_fst_apply, hXl, birkSgn, ite_true, Bool.false_eq_true, ite_false]
    show _ = (0 : lp (fun _ : ℕ+ => ℂ) 2) j
    simp only [lp.coeFn_zero, Pi.zero_apply]
    ring
  · simp only [birkZinv_snd_apply, hXl, birkSgn, ite_true, Bool.false_eq_true, ite_false]
    show _ = (-(waveCubicNL (K := ℂ) m hm ha hp x.1)) j
    simp only [lp.coeFn_neg, Pi.neg_apply, hcub]
    field_simp
    linear_combination (T j * (RCLike.ofReal (ellWeight a (p + 1) j) : ℂ) * birkSqrt2 * Complex.I ^
        2 * 0) * h2

end

end KAM.Wave

end
