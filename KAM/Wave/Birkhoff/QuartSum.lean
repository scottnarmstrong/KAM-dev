/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartML

/-!
# The quartic sum and its pairing identity (blueprint-W `bpW:w3:quartic`, Step Identify)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic`.

`birkQuartSum a p c w = Σ_{x ∈ (ℤ∖0)⁴} c_x ∏_t w^t_{x_t}` converges absolutely
(`summable_birkQuartTerm`), and equals `16 Ω(∇𝔓(w¹,w²,w³), w⁴)` (`birkQuartSum_eq_omega`), the pairing
identity of the blueprint.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- `(z, y) ↦ (y₁, y₂, y₃, z)`: `(ℤ∖0)⁴ ≃ (ℤ∖0) × (ℤ∖0)³` (the last index split off). -/
def birkSplit4 : BirkIdx × (Fin 3 → BirkIdx) ≃ (Fin 4 → BirkIdx) where
  toFun q := ![q.2 0, q.2 1, q.2 2, q.1]
  invFun x := (x 3, ![x 0, x 1, x 2])
  left_inv q := by
    obtain ⟨z, y⟩ := q
    refine Prod.ext rfl ?_
    funext i; fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl

/-- The first three arguments of a four-tuple. -/
def birkInit4 (w : Fin 4 → BirkSpace) : Fin 3 → BirkSpace := ![w 0, w 1, w 2]

theorem birkAtom_split4 (a p : ℝ) (z : BirkIdx) (y : Fin 3 → BirkIdx) (w : Fin 4 → BirkSpace) :
    birkAtom a p (birkSplit4 (z, y)) w =
      birkAtom a p y (birkInit4 w) * birkCoord a p (w 3) z := by
  simp [birkAtom_apply, birkSplit4, birkInit4, Fin.prod_univ_four, Fin.prod_univ_three]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c : (Fin 4 → BirkIdx) → ℂ}
  (hc : ∀ x, ‖c x‖ ≤ |birkG m hm x|)

include ha hp hc in
/-- The terms of the quartic sum are absolutely summable. -/
theorem summable_birkQuartTerm (w : Fin 4 → BirkSpace) :
    Summable fun x : Fin 4 → BirkIdx => ‖c x * birkAtom a p x w‖ := by
  set w' := birkInit4 w with hw'
  set M := birkMajorant m hm (birkFoldNorm a p (w' 0)) (birkFoldNorm a p (w' 1))
    (birkFoldNorm a p (w' 2)) with hM
  have hmaj := birkMajorant_bound m hm ha hp (isEll_birkFoldNorm a p (w' 0))
    (isEll_birkFoldNorm a p (w' 1)) (isEll_birkFoldNorm a p (w' 2))
  have hs : Summable fun j : ℕ+ => (ellWeight a (p + 1) j * ‖M j‖) ^ 2 :=
    (wave_isEll_iff_summable a (p + 1) M).1 hmaj.2.1
  have hBs : Summable fun z : BirkIdx => (ellWeight a (p + 1) z.2 * ‖M z.2‖) ^ 2 := by
    rw [birk_summable_iff (fun l => by positivity)]; exact ⟨hs, hs⟩
  have hM0 : ∀ j, 0 ≤ M j := fun j => by
    rw [hM]; unfold birkMajorant waveSelSum
    exact tsum_nonneg fun t => mul_nonneg (abs_nonneg _) (mul_nonneg
      (birkFoldNorm_nonneg a p _ _) (mul_nonneg (birkFoldNorm_nonneg a p _ _)
        (birkFoldNorm_nonneg a p _ _)))
  have key : ∀ z y, ‖c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) w‖ =
      ‖birkGradTerm a p c (birkNeg z) w' y‖ * ‖birkCoord a p (w 3) z‖ := fun z y => by
    rw [birkAtom_split4, birkAtom_apply]
    simp only [hw', birkGradTerm, norm_mul, birkNeg_birkNeg, birkSplit4, Equiv.coe_fn_mk, birkInit4]
    ring
  have hfib : ∀ z : BirkIdx, Summable fun y : Fin 3 → BirkIdx =>
      ‖c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) w‖ := fun z => by
    simp only [key]
    exact (birkGrad_majorize m hm ha hp hc (birkNeg z) w').1.mul_right _
  have hout : Summable fun z : BirkIdx => ∑' y : Fin 3 → BirkIdx,
      ‖c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) w‖ := by
    have hcs := waveCauchySchwarz_tsum (f := fun z : BirkIdx => ‖w 3 z‖)
      (g := fun z : BirkIdx => ellWeight a (p + 1) z.2 * ‖M z.2‖) (fun _ => norm_nonneg _)
      (fun z => mul_nonneg (ellWeight_pos _ _ _).le (norm_nonneg _))
      (lp_two_hasSum_sq (w 3)).summable hBs
    refine Summable.of_nonneg_of_le (fun z => tsum_nonneg fun _ => norm_nonneg _) (fun z => ?_)
      hcs.1
    simp only [key]
    rw [tsum_mul_right]
    have h1 := (birkGrad_majorize m hm ha hp hc (birkNeg z) w').2
    rw [← hM] at h1
    simp only [birkNeg_snd] at h1
    have h2 : ‖birkCoord a p (w 3) z‖ ≤ ‖w 3 z‖ := norm_birkCoord_le ha (by linarith) _ _
    have h3 : ‖birkCoord a p (w 3) z‖ = ‖w 3 z‖ / ellWeight a p z.2 := by
      rw [birkCoord, norm_div, norm_ellWeight_cast]
    have hw1 : 1 ≤ ellWeight a p z.2 := birk_one_le_weight ha (by linarith) _
    have hw2 : 1 ≤ ellWeight a (p + 1) z.2 := birk_one_le_weight ha (by linarith) _
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 _)]
    calc (∑' y, ‖birkGradTerm a p c (birkNeg z) w' y‖) * ‖birkCoord a p (w 3) z‖
        ≤ M z.2 * (‖w 3 z‖ / ellWeight a p z.2) := by
          rw [h3]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ M z.2 * ‖w 3 z‖ := by
          exact mul_le_mul_of_nonneg_left (div_le_self (norm_nonneg _) hw1) (hM0 _)
      _ ≤ ‖w 3 z‖ * (ellWeight a (p + 1) z.2 * M z.2) := by
          nlinarith [norm_nonneg (w 3 z), hM0 z.2, mul_nonneg (norm_nonneg (w 3 z)) (hM0 z.2)]
  have hprod : Summable fun q : BirkIdx × (Fin 3 → BirkIdx) =>
      ‖c (birkSplit4 q) * birkAtom a p (birkSplit4 q) w‖ :=
    (summable_prod_of_nonneg (fun q => norm_nonneg _)).2 ⟨hfib, hout⟩
  exact (birkSplit4.summable_iff (f := fun x => ‖c x * birkAtom a p x w‖)).1 hprod

/-- `Σ_{x ∈ (ℤ∖0)⁴} c_x ∏_t w^t_{x_t}`. -/
def birkQuartSum (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (w : Fin 4 → BirkSpace) : ℂ :=
  ∑' x : Fin 4 → BirkIdx, c x * birkAtom a p x w

theorem snoc_eq_vec3 (w : Fin 3 → BirkSpace) (v : BirkSpace) :
    (Fin.snoc (α := fun _ => BirkSpace) w v : Fin 4 → BirkSpace) = ![w 0, w 1, w 2, v] := by
  funext i; fin_cases i <;> rfl

theorem birkInit4_snoc (w : Fin 3 → BirkSpace) (v : BirkSpace) :
    birkInit4 (Fin.snoc (α := fun _ => BirkSpace) w v : Fin 4 → BirkSpace) = w := by
  funext i; fin_cases i <;> rfl

include ha hp hc in
/-- (`bpW:w3:quartic`, Step Identify) `(1/16) Σ_x c_x ∏ w^t_{x_t} = Ω(∇𝔓(w¹,w²,w³), w⁴)`. -/
theorem birkQuartSum_eq_omega (w : Fin 4 → BirkSpace) :
    (1 / 16 : ℂ) * birkQuartSum a p c w =
      birkOmegaPlus a p ha (by linarith) (birkGradML m hm ha hp hc (birkInit4 w)) (w 3) := by
  have hsum := (summable_birkQuartTerm m hm ha hp hc w).of_norm
  have hsum' : Summable fun q : BirkIdx × (Fin 3 → BirkIdx) =>
      c (birkSplit4 q) * birkAtom a p (birkSplit4 q) w := (birkSplit4.summable_iff).2 hsum
  unfold birkQuartSum
  rw [← birkSplit4.tsum_eq]
  rw [Summable.tsum_prod hsum']
  have hp0 : 0 ≤ p := by linarith
  simp only [birkOmegaPlus, birkOmega_apply]
  -- the right side as a sum over `l`
  have hR : ∀ l : BirkIdx, birkSgn l * birkCoord a p (birkEmbed a (p + 1) p (by linarith)
      (birkGradML m hm ha hp hc (birkInit4 w))) l * birkCoord a p (w 3) (birkNeg l) =
        (-Complex.I / 16) * (birkGradSum a p c (birkInit4 w) l * birkCoord a p (w 3) (birkNeg l)) := by
    intro l
    rw [birkCoord_birkEmbed, birkCoord_birkGradML]
    have := birkSgn_mul_self l
    unfold birkGradSum birkGradTerm
    linear_combination (-Complex.I / 16 * ((∑' y : Fin 3 → BirkIdx, c ![y 0, y 1, y 2, birkNeg l] *
      ∏ t, birkCoord a p (birkInit4 w t) (y t)) * birkCoord a p (w 3) (birkNeg l))) * this
  simp only [hR]
  rw [tsum_mul_left]
  have hI : Complex.I * (-Complex.I / 16) = 1 / 16 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 16 : ℂ) * this
  rw [← mul_assoc, hI, ← birkNegEquiv.tsum_eq]
  congr 1
  refine tsum_congr fun z => ?_
  simp only [birkNegEquiv, Equiv.coe_fn_mk]
  unfold birkGradSum
  rw [← tsum_mul_right]
  refine tsum_congr fun y => ?_
  rw [birkAtom_split4]
  unfold birkGradTerm
  rw [birkAtom_apply]
  simp only [birkInit4, birkSplit4, Equiv.coe_fn_mk]
  ring

end

end KAM.Wave

end
