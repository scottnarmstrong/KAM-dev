/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartGrad

/-!
# The gradient `∇𝔓` as a continuous trilinear map (blueprint-W `bpW:w3:quartic`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic`.

`birkGradLp` is the point `∇𝔓(w¹,w²,w³) ∈ 𝔚^+` (weighted coordinates at weight `p + 1`),
`birkCoord_birkGradLp` gives its coordinates `-i sgn(l)/16 Σ_y c_{(y,-l)} ∏ w^t_{y_t}`,
`norm_birkGradLp_le` the bound `‖∇𝔓‖₊ ≤ (C_*/4) ∏‖w^t‖` (`C_* = waveCubicConst p`), and `birkGradML`
the continuous trilinear map.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The coordinates `∇𝔓(w)_l = -i sgn(l)/16 Σ_y c_{(y,-l)} ∏_t w^t_{y_t}` (actual coordinates). -/
def birkGradCoord (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (w : Fin 3 → BirkSpace) (l : BirkIdx) : ℂ :=
  (-Complex.I * birkSgn l / 16) * birkGradSum a p c w l

/-- The gradient sequence in weighted coordinates at weight `p + 1`. -/
def birkGradSeq (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (w : Fin 3 → BirkSpace) (l : BirkIdx) : ℂ :=
  (RCLike.ofReal (ellWeight a (p + 1) l.2) : ℂ) * birkGradCoord a p c w l

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c : (Fin 4 → BirkIdx) → ℂ}
  (hc : ∀ x, ‖c x‖ ≤ |birkG m hm x|)

theorem norm_neg_I_sgn_div (l : BirkIdx) : ‖-Complex.I * birkSgn l / 16‖ = 1 / 16 := by
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, norm_birkSgn]
  simp

include ha hp hc in
theorem norm_birkGradSeq_le (w : Fin 3 → BirkSpace) (l : BirkIdx) :
    ‖birkGradSeq a p c w l‖ ≤ (1 / 16) * (ellWeight a (p + 1) l.2 *
      birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
        (birkFoldNorm a p (w 2)) l.2) := by
  unfold birkGradSeq birkGradCoord
  rw [norm_mul, norm_mul, norm_neg_I_sgn_div, RCLike.norm_ofReal, abs_of_pos (ellWeight_pos _ _ _)]
  have := norm_birkGradSum_le m hm ha hp hc l w
  calc ellWeight a (p + 1) l.2 * (1 / 16 * ‖birkGradSum a p c w l‖)
      ≤ ellWeight a (p + 1) l.2 * (1 / 16 * birkMajorant m hm (birkFoldNorm a p (w 0))
        (birkFoldNorm a p (w 1)) (birkFoldNorm a p (w 2)) l.2) := by
        have := ellWeight_pos a (p + 1) l.2
        gcongr
    _ = _ := by ring

include ha hp hc in
/-- The pointwise squares of the gradient sequence are summable, with the bound by `ℓ^{a,p+1}`
norm of the majorant. -/
theorem birkGradSeq_sq (w : Fin 3 → BirkSpace) :
    Summable (fun l => ‖birkGradSeq a p c w l‖ ^ 2) ∧
      ∑' l, ‖birkGradSeq a p c w l‖ ^ 2 ≤ (2 / 256) * ellTsumSq a (p + 1)
        (birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
          (birkFoldNorm a p (w 2))) := by
  set M := birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
    (birkFoldNorm a p (w 2)) with hM
  have hmaj := birkMajorant_bound m hm ha hp (isEll_birkFoldNorm a p (w 0))
    (isEll_birkFoldNorm a p (w 1)) (isEll_birkFoldNorm a p (w 2))
  have hs : Summable fun j : ℕ+ => (ellWeight a (p + 1) j * ‖M j‖) ^ 2 :=
    (wave_isEll_iff_summable a (p + 1) M).1 hmaj.2.1
  have hM0 : ∀ j, 0 ≤ M j := fun j => by
    rw [hM]; unfold birkMajorant waveSelSum
    exact tsum_nonneg fun t => mul_nonneg (abs_nonneg _) (mul_nonneg
      (birkFoldNorm_nonneg a p _ _) (mul_nonneg (birkFoldNorm_nonneg a p _ _)
        (birkFoldNorm_nonneg a p _ _)))
  set g : BirkIdx → ℝ := fun l => (1 / 256) * (ellWeight a (p + 1) l.2 * ‖M l.2‖) ^ 2 with hg
  have hgs : Summable g := by
    rw [birk_summable_iff (fun l => by positivity)]
    exact ⟨hs.mul_left _, hs.mul_left _⟩
  have hle : ∀ l, ‖birkGradSeq a p c w l‖ ^ 2 ≤ g l := fun l => by
    have h1 := norm_birkGradSeq_le m hm ha hp hc w l
    rw [← hM] at h1
    have h2 : 0 ≤ ‖birkGradSeq a p c w l‖ := norm_nonneg _
    rw [hg]
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 _)]
    calc ‖birkGradSeq a p c w l‖ ^ 2 ≤ (1 / 16 * (ellWeight a (p + 1) l.2 * M l.2)) ^ 2 := by
          gcongr
      _ = _ := by ring
  have hsq : Summable fun l => ‖birkGradSeq a p c w l‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle hgs
  refine ⟨hsq, ?_⟩
  calc ∑' l, ‖birkGradSeq a p c w l‖ ^ 2 ≤ ∑' l, g l := Summable.tsum_le_tsum hle hsq hgs
    _ = (2 / 256) * ellTsumSq a (p + 1) M := by
        rw [birk_tsum_split hgs]
        simp only [hg]
        rw [tsum_mul_left]
        unfold ellTsumSq
        ring

include ha hp hc in
theorem memℓp_birkGradSeq (w : Fin 3 → BirkSpace) : Memℓp (birkGradSeq a p c w) 2 :=
  memℓp_gen (by simpa [Real.rpow_two] using (birkGradSeq_sq m hm ha hp hc w).1)

include ha hp hc in
/-- `∇𝔓(w¹,w²,w³) ∈ 𝔚^+`, as a point of `BirkSpace` read at weight `p + 1`. -/
def birkGradLp (w : Fin 3 → BirkSpace) : BirkSpace :=
  ⟨birkGradSeq a p c w, memℓp_birkGradSeq m hm ha hp hc w⟩

include ha hp hc in
/-- (`bpW:w3:quartic`, Step Bound the gradient) `‖∇𝔓(w¹,w²,w³)‖₊ ≤ (C_*/4) ∏‖w^t‖`. -/
theorem norm_birkGradLp_le (w : Fin 3 → BirkSpace) :
    ‖birkGradLp m hm ha hp hc w‖ ≤ (waveCubicConst p / 4) * ∏ t, ‖w t‖ := by
  set M := birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
    (birkFoldNorm a p (w 2)) with hM
  have hmaj := birkMajorant_bound m hm ha hp (isEll_birkFoldNorm a p (w 0))
    (isEll_birkFoldNorm a p (w 1)) (isEll_birkFoldNorm a p (w 2))
  have hC : 0 ≤ waveCubicConst p := by unfold waveCubicConst; positivity
  have hT : ellTsumNorm a (p + 1) M ≤ waveCubicConst p * ((Real.sqrt 2 * ‖w 0‖) *
      (Real.sqrt 2 * ‖w 1‖) * (Real.sqrt 2 * ‖w 2‖)) := by
    refine hmaj.2.2.trans ?_
    have e0 := ellTsumNorm_birkFoldNorm_le a p (w 0)
    have e1 := ellTsumNorm_birkFoldNorm_le a p (w 1)
    have e2 := ellTsumNorm_birkFoldNorm_le a p (w 2)
    have n0 : 0 ≤ ellTsumNorm a p (birkFoldNorm a p (w 0)) := Real.sqrt_nonneg _
    have n1 : 0 ≤ ellTsumNorm a p (birkFoldNorm a p (w 1)) := Real.sqrt_nonneg _
    have n2 : 0 ≤ ellTsumNorm a p (birkFoldNorm a p (w 2)) := Real.sqrt_nonneg _
    gcongr
  have hS : ellTsumSq a (p + 1) M = ellTsumNorm a (p + 1) M ^ 2 := by
    rw [ellTsumNorm, Real.sq_sqrt]
    unfold ellTsumSq
    exact tsum_nonneg fun _ => by positivity
  have h2 : ‖birkGradLp m hm ha hp hc w‖ ^ 2 ≤ (2 / 256) * ellTsumSq a (p + 1) M := by
    calc ‖birkGradLp m hm ha hp hc w‖ ^ 2
        = ∑' l, ‖birkGradSeq a p c w l‖ ^ 2 := (lp_two_hasSum_sq (birkGradLp m hm ha hp hc w)).tsum_eq.symm
      _ ≤ _ := (birkGradSeq_sq m hm ha hp hc w).2
  have hP : 0 ≤ ∏ t, ‖w t‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have e3 : ((Real.sqrt 2 * ‖w 0‖) * (Real.sqrt 2 * ‖w 1‖) * (Real.sqrt 2 * ‖w 2‖)) =
      2 * Real.sqrt 2 * ∏ t, ‖w t‖ := by
    rw [Fin.prod_univ_three]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    calc (Real.sqrt 2 * ‖w 0‖) * (Real.sqrt 2 * ‖w 1‖) * (Real.sqrt 2 * ‖w 2‖)
        = Real.sqrt 2 ^ 2 * Real.sqrt 2 * (‖w 0‖ * ‖w 1‖ * ‖w 2‖) := by ring
      _ = _ := by rw [this]
  rw [e3] at hT
  have hT0 : 0 ≤ ellTsumNorm a (p + 1) M := Real.sqrt_nonneg _
  have h3 : ‖birkGradLp m hm ha hp hc w‖ ^ 2 ≤ ((waveCubicConst p / 4) * ∏ t, ‖w t‖) ^ 2 := by
    refine h2.trans ?_
    rw [hS]
    have h4 : ellTsumNorm a (p + 1) M ^ 2 ≤ (waveCubicConst p * (2 * Real.sqrt 2 * ∏ t, ‖w t‖)) ^ 2 :=
      pow_le_pow_left₀ hT0 hT 2
    calc (2 / 256) * ellTsumNorm a (p + 1) M ^ 2
        ≤ (2 / 256) * (waveCubicConst p * (2 * Real.sqrt 2 * ∏ t, ‖w t‖)) ^ 2 := by gcongr
      _ = _ := by
        have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have e : (waveCubicConst p * (2 * Real.sqrt 2 * ∏ t, ‖w t‖)) ^ 2 =
            waveCubicConst p ^ 2 * (4 * (Real.sqrt 2) ^ 2) * (∏ t, ‖w t‖) ^ 2 := by ring
        rw [e, this]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

theorem birkGradTerm_eq_atom (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (l : BirkIdx)
    (w : Fin 3 → BirkSpace) (y : Fin 3 → BirkIdx) :
    birkGradTerm a p c l w y = c ![y 0, y 1, y 2, birkNeg l] * birkAtom a p y w := by
  rw [birkAtom_apply]; rfl

include ha hp hc in
/-- The gradient sum is multilinear in `(w¹, w², w³)`. -/
def birkGradSumML (l : BirkIdx) : MultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) ℂ where
  toFun w := birkGradSum a p c w l
  map_update_add' w i v v' := by
    classical
    unfold birkGradSum
    rw [← Summable.tsum_add (summable_birkGradTerm m hm ha hp hc l _)
      (summable_birkGradTerm m hm ha hp hc l _)]
    refine tsum_congr fun y => ?_
    simp only [birkGradTerm_eq_atom, MultilinearMap.map_update_add]
    ring
  map_update_smul' w i r v := by
    classical
    unfold birkGradSum
    rw [smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun y => ?_
    simp only [birkGradTerm_eq_atom, MultilinearMap.map_update_smul, smul_eq_mul]
    ring

include ha hp hc in
/-- `∇𝔓` as a multilinear map `𝔚³ → 𝔚^+`. -/
def birkGradMLmap : MultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace where
  toFun := birkGradLp m hm ha hp hc
  map_update_add' w i v v' := by
    classical
    ext l
    show birkGradSeq a p c (Function.update w i (v + v')) l =
      birkGradSeq a p c (Function.update w i v) l + birkGradSeq a p c (Function.update w i v') l
    unfold birkGradSeq birkGradCoord
    have := (birkGradSumML m hm ha hp hc l).map_update_add w i v v'
    simp only [birkGradSumML, MultilinearMap.coe_mk] at this
    rw [this]; ring
  map_update_smul' w i r v := by
    classical
    ext l
    show birkGradSeq a p c (Function.update w i (r • v)) l =
      r * birkGradSeq a p c (Function.update w i v) l
    unfold birkGradSeq birkGradCoord
    have := (birkGradSumML m hm ha hp hc l).map_update_smul w i r v
    simp only [birkGradSumML, MultilinearMap.coe_mk, smul_eq_mul] at this
    rw [this]; ring

include ha hp hc in
/-- (`bpW:w3:quartic`) `∇𝔓 : 𝔚³ → 𝔚^+` is a continuous trilinear map with `‖∇𝔓‖ ≤ C_*/4`. -/
def birkGradML : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace :=
  (birkGradMLmap m hm ha hp hc).mkContinuous (waveCubicConst p / 4)
    (fun w => norm_birkGradLp_le m hm ha hp hc w)

include ha hp hc in
theorem birkGradML_apply (w : Fin 3 → BirkSpace) :
    birkGradML m hm ha hp hc w = birkGradLp m hm ha hp hc w := rfl

include ha hp hc in
/-- (`bpW:w3:quartic`) coordinates of `∇𝔓`:
`birkCoord a (p+1) (∇𝔓 w) l = -i sgn(l)/16 Σ_y c_{(y,-l)} ∏ w^t_{y_t}`. -/
theorem birkCoord_birkGradML (w : Fin 3 → BirkSpace) (l : BirkIdx) :
    birkCoord a (p + 1) (birkGradML m hm ha hp hc w) l =
      (-Complex.I * birkSgn l / 16) * ∑' y : Fin 3 → BirkIdx,
        c ![y 0, y 1, y 2, birkNeg l] * ∏ t, birkCoord a p (w t) (y t) := by
  have h := ellWeight_cast_ne_zero (K := ℂ) a (p + 1) l.2
  show birkGradSeq a p c w l / _ = _
  unfold birkGradSeq birkGradCoord birkGradSum birkGradTerm
  rw [mul_div_cancel_left₀ _ h]

include ha hp hc in
theorem norm_birkGradML_le : ‖birkGradML m hm ha hp hc‖ ≤ waveCubicConst p / 4 :=
  MultilinearMap.mkContinuous_norm_le _ (by unfold waveCubicConst; positivity) _

end

end KAM.Wave

end
