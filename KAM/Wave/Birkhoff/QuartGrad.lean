/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Fold
public import KAM.Wave.Birkhoff.Forms

/-!
# The gradient of the quartic forms (blueprint-W `bpW:w3:quartic`, Steps Majorize and Bound)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic`.

For a coefficient family `c : (ℤ ∖ {0})⁴ → ℂ` with `|c_x| ≤ |𝔤_x|` (`birkG`) the gradient
`∇𝔓(w¹,w²,w³)_l = -i sgn(l)/16 Σ_{y ∈ (ℤ∖0)³} c_{(y,-l)} w¹_{y₁} w²_{y₂} w³_{y₃}` converges absolutely
(`summable_birkGradTerm`, bounded by the majorant `birkMajorant` of the folded sequences,
`norm_birkGradSum_le`), is an element of `𝔚^+` (a point of `BirkSpace` read at weight `p + 1`,
`birkGradSeq`), and defines a continuous trilinear map `birkGradML` with `‖∇𝔓‖ ≤ C_*/4`
(`norm_birkGradML_le`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- `𝔤_x = g_{|x|} / √(λ_{|x₁|} λ_{|x₂|} λ_{|x₃|} λ_{|x₄|})` (blueprint, §quartic-sec). -/
def birkG (x : Fin 4 → BirkIdx) : ℝ := waveTriCoef m hm (x 0).2 (x 1).2 (x 2).2 (x 3).2

/-- The coordinate functional `w ↦ w_l` at weight `(a, p)`. -/
def birkCoordL (a p : ℝ) (l : BirkIdx) : BirkSpace →ₗ[ℂ] ℂ where
  toFun w := birkCoord a p w l
  map_add' w w' := birkCoord_add a p w w' l
  map_smul' c w := by simpa using birkCoord_smul a p c w l

/-- The multilinear monomial `(w¹,…,wⁿ) ↦ ∏_t w^t_{y_t}`. -/
def birkAtom (a p : ℝ) {n : ℕ} (y : Fin n → BirkIdx) :
    MultilinearMap ℂ (fun _ : Fin n => BirkSpace) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap (fun t => birkCoordL a p (y t))

theorem birkAtom_apply (a p : ℝ) {n : ℕ} (y : Fin n → BirkIdx) (w : Fin n → BirkSpace) :
    birkAtom a p y w = ∏ t, birkCoord a p (w t) (y t) := by
  simp [birkAtom, birkCoordL]

/-- The term `c_{(y,-l)} ∏_t w^t_{y_t}` of the gradient. -/
def birkGradTerm (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (l : BirkIdx) (w : Fin 3 → BirkSpace)
    (y : Fin 3 → BirkIdx) : ℂ :=
  c ![y 0, y 1, y 2, birkNeg l] * ∏ t, birkCoord a p (w t) (y t)

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c : (Fin 4 → BirkIdx) → ℂ}
  (hc : ∀ x, ‖c x‖ ≤ |birkG m hm x|)

include hc in
theorem norm_birkGradTerm_le (l : BirkIdx) (w : Fin 3 → BirkSpace) (y : Fin 3 → BirkIdx) :
    ‖birkGradTerm a p c l w y‖ ≤
      |waveTriCoef m hm (y 0).2 (y 1).2 (y 2).2 l.2| * ∏ t, ‖birkCoord a p (w t) (y t)‖ := by
  unfold birkGradTerm
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right ((hc _).trans ?_) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  simp [birkG]

include ha hp hc in
/-- Absolute convergence of the gradient sums, with the majorant of the folded sequences. -/
theorem birkGrad_majorize (l : BirkIdx) (w : Fin 3 → BirkSpace) :
    Summable (fun y : Fin 3 → BirkIdx => ‖birkGradTerm a p c l w y‖) ∧
      ∑' y : Fin 3 → BirkIdx, ‖birkGradTerm a p c l w y‖ ≤
        birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
          (birkFoldNorm a p (w 2)) l.2 := by
  set W : Fin 3 → BirkIdx → ℝ := fun t l' => ‖birkCoord a p (w t) l'‖ with hWdef
  have hW0 : ∀ t l', 0 ≤ W t l' := fun _ _ => norm_nonneg _
  have hmaj := birkMajorant_bound m hm ha hp (isEll_birkFoldNorm a p (w 0))
    (isEll_birkFoldNorm a p (w 1)) (isEll_birkFoldNorm a p (w 2))
  have hsum : Summable fun τ : ℕ+ × ℕ+ × ℕ+ =>
      |waveTriCoef m hm τ.1 τ.2.1 τ.2.2 l.2| * (birkFold (W 0) τ.1 *
        (birkFold (W 1) τ.2.1 * birkFold (W 2) τ.2.2)) := by
    refine (hmaj.1 l.2).congr fun τ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rfl
    · exact mul_nonneg (abs_nonneg _) (mul_nonneg (birkFoldNorm_nonneg a p _ _)
        (mul_nonneg (birkFoldNorm_nonneg a p _ _) (birkFoldNorm_nonneg a p _ _)))
  have h3 := birk_three_sum (G := fun i j k => |waveTriCoef m hm i j k l.2|)
    (fun _ _ _ => abs_nonneg _) W hW0 hsum
  have hb : ∀ y, ‖birkGradTerm a p c l w y‖ ≤
      |waveTriCoef m hm (y 0).2 (y 1).2 (y 2).2 l.2| * ∏ t, W t (y t) :=
    norm_birkGradTerm_le m hm hc l w
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb h3.1, ?_⟩
  calc ∑' y, ‖birkGradTerm a p c l w y‖
      ≤ ∑' y : Fin 3 → BirkIdx, |waveTriCoef m hm (y 0).2 (y 1).2 (y 2).2 l.2| * ∏ t, W t (y t) :=
        Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb h3.1) h3.1
    _ = _ := h3.2

include ha hp hc in
theorem summable_birkGradTerm (l : BirkIdx) (w : Fin 3 → BirkSpace) :
    Summable (birkGradTerm a p c l w) :=
  (birkGrad_majorize m hm ha hp hc l w).1.of_norm

/-- The gradient sum `Σ_y c_{(y,-l)} ∏_t w^t_{y_t}`. -/
def birkGradSum (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (w : Fin 3 → BirkSpace) (l : BirkIdx) : ℂ :=
  ∑' y : Fin 3 → BirkIdx, birkGradTerm a p c l w y

include ha hp hc in
theorem norm_birkGradSum_le (l : BirkIdx) (w : Fin 3 → BirkSpace) :
    ‖birkGradSum a p c w l‖ ≤
      birkMajorant m hm (birkFoldNorm a p (w 0)) (birkFoldNorm a p (w 1))
        (birkFoldNorm a p (w 2)) l.2 := by
  have h := birkGrad_majorize m hm ha hp hc l w
  exact (norm_tsum_le_tsum_norm h.1).trans h.2

end

end KAM.Wave

end
