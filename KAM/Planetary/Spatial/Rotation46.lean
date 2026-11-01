/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# The rotation algebra of the spatial Poincare chart, formula (46)

Package LP-SP-ROT, `LP:MAIN L17 (533–578)`, track LP, non-frozen. Pure `3 × 3` matrix algebra on
`Fin 3 → ℝ` with Mathlib's `crossProduct` (`⨯₃`).

* `skewMatrix t` is the matrix of `w ↦ t ⨯₃ w`; `skewMatrix_mul_skewMatrix` is
  `[t]ₓ² = t tᵀ − |t|² Id`.
* `tiltRotation t c = (1 − 2|t|²) Id + 2 t tᵀ + 2c [t]ₓ` for `c² = 1 − |t|²` is orthogonal of
  determinant one and preserves the cross product.
* `incTilt`, `incCos`, `incRotation` are the objects `t`, `c`, `R` of (46).

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Matrix
open scoped ContDiff

namespace KAM.Planetary.Spatial

/-- The matrix of `w ↦ t ⨯₃ w`. -/
def skewMatrix (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -t 2, t 1; t 2, 0, -t 0; -t 1, t 0, 0]

/-- The rotation `(1 − 2|t|²) Id + 2 t tᵀ + 2c [t]ₓ` with an abstract cosine `c`. -/
def tiltRotation (t : Fin 3 → ℝ) (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - 2 * (t ⬝ᵥ t)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (2 : ℝ) • vecMulVec t t
    + (2 * c) • skewMatrix t

/-- The tilt vector `t = (u, −v, 0) / (2 √G)` of (46). -/
def incTilt (u v G : ℝ) : Fin 3 → ℝ := (1 / (2 * Real.sqrt G)) • ![u, -v, 0]

/-- The cosine `c = √(1 − |t|²)` of (46). -/
def incCos (u v G : ℝ) : ℝ := Real.sqrt (1 - incTilt u v G ⬝ᵥ incTilt u v G)

/-- The rotation `R` of (46). -/
def incRotation (u v G : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - 2 * (incTilt u v G ⬝ᵥ incTilt u v G)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
    + (2 : ℝ) • vecMulVec (incTilt u v G) (incTilt u v G)
    + (2 * incCos u v G) • skewMatrix (incTilt u v G)

lemma incRotation_eq_tiltRotation (u v G : ℝ) :
    incRotation u v G = tiltRotation (incTilt u v G) (incCos u v G) := rfl

/-- The unit vector `e₃`. -/
def e₃ : Fin 3 → ℝ := ![0, 0, 1]

/-- Embedding of a planar vector in the first two coordinates. -/
def planarEmbed (Q : Fin 2 → ℝ) : Fin 3 → ℝ := ![Q 0, Q 1, 0]

lemma skewMatrix_mulVec (t w : Fin 3 → ℝ) : skewMatrix t *ᵥ w = t ⨯₃ w := by
  ext i
  fin_cases i <;>
    simp [skewMatrix, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `[t]ₓ² = t tᵀ − |t|² Id`. -/
theorem skewMatrix_mul_skewMatrix (t : Fin 3 → ℝ) :
    skewMatrix t * skewMatrix t = vecMulVec t t - (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix, Matrix.mul_apply, Fin.sum_univ_three, vecMulVec_apply, dotProduct] <;> ring

section Generic

variable (t : Fin 3 → ℝ) (c : ℝ)

/-- Explicit entries of `tiltRotation`. -/
lemma tiltRotation_eq :
    tiltRotation t c = !![1 - 2 * (t 1 ^ 2 + t 2 ^ 2) + 0, 2 * t 0 * t 1 - 2 * c * t 2,
        2 * t 0 * t 2 + 2 * c * t 1;
      2 * t 0 * t 1 + 2 * c * t 2, 1 - 2 * (t 0 ^ 2 + t 2 ^ 2) + 0, 2 * t 1 * t 2 - 2 * c * t 0;
      2 * t 0 * t 2 - 2 * c * t 1, 2 * t 1 * t 2 + 2 * c * t 0,
        1 - 2 * (t 0 ^ 2 + t 1 ^ 2) + 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tiltRotation, skewMatrix, vecMulVec_apply, dotProduct, Fin.sum_univ_three] <;> ring

lemma tiltRotation_transpose_mul (hc : c ^ 2 = 1 - t ⬝ᵥ t) :
    (tiltRotation t c)ᵀ * tiltRotation t c = 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hc
  rw [tiltRotation_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 1^2 + t 2^2)) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 1) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 1) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 0^2 + t 2^2)) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 1*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 0*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (-4*t 1*t 2) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_three]; linear_combination (4*(t 0^2 + t 1^2)) * hc

lemma tiltRotation_det (hc : c ^ 2 = 1 - t ⬝ᵥ t) : (tiltRotation t c).det = 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hc
  rw [tiltRotation_eq]
  simp [Matrix.det_fin_three]
  linear_combination (4 * (t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2)) * hc

end Generic

/-- A proper orthogonal matrix commutes with the cross product. -/
theorem mulVec_cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (h1 : Mᵀ * M = 1) (h2 : M.det = 1)
    (v w : Fin 3 → ℝ) : (M *ᵥ v) ⨯₃ (M *ᵥ w) = M *ᵥ (v ⨯₃ w) := by
  have key : ∀ x : Fin 3 → ℝ, x ⬝ᵥ ((M *ᵥ v) ⨯₃ (M *ᵥ w)) = x ⬝ᵥ (M *ᵥ (v ⨯₃ w)) := by
    intro x
    have hN : Matrix.of ![x, M *ᵥ v, M *ᵥ w] * M = Matrix.of ![Mᵀ *ᵥ x, v, w] := by
      ext a b
      change (![x, M *ᵥ v, M *ᵥ w] a ᵥ* M) b = ![Mᵀ *ᵥ x, v, w] a b
      fin_cases a
      · simp [Matrix.mulVec_transpose]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have hd := congrArg Matrix.det hN
    rw [Matrix.det_mul, h2, mul_one] at hd
    rw [triple_product_eq_det, dotProduct_mulVec, ← Matrix.mulVec_transpose,
      triple_product_eq_det]
    exact hd
  funext i
  simpa [dotProduct_single] using key (Pi.single i 1)



section Inc

variable {u v G : ℝ}

lemma incTilt_apply_zero (u v G : ℝ) : incTilt u v G 0 = u / (2 * Real.sqrt G) := by
  simp [incTilt]; ring

lemma incTilt_apply_one (u v G : ℝ) : incTilt u v G 1 = -v / (2 * Real.sqrt G) := by
  simp [incTilt]; ring

lemma incTilt_apply_two (u v G : ℝ) : incTilt u v G 2 = 0 := by simp [incTilt]

/-- `|t|² = Z / (2G)` with `Z = (u² + v²)/2`. -/
lemma incTilt_dot (hG : 0 < G) :
    incTilt u v G ⬝ᵥ incTilt u v G = ((u ^ 2 + v ^ 2) / 2) / (2 * G) := by
  have h := Real.sq_sqrt hG.le
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  simp only [dotProduct, Fin.sum_univ_three, incTilt_apply_zero, incTilt_apply_one,
    incTilt_apply_two]
  field_simp
  rw [h]
  ring

lemma incTilt_dot_lt_half (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    incTilt u v G ⬝ᵥ incTilt u v G < 1 / 2 := by
  rw [incTilt_dot hG, div_lt_iff₀ (by positivity)]
  linarith

lemma incCos_sq (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    incCos u v G ^ 2 = 1 - incTilt u v G ⬝ᵥ incTilt u v G := by
  have := incTilt_dot_lt_half hG hZ
  exact Real.sq_sqrt (by linarith)

lemma incCos_pos (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) : 0 < incCos u v G := by
  have := incTilt_dot_lt_half hG hZ
  exact Real.sqrt_pos.2 (by linarith)

/-- (46): `R` is orthogonal. -/
theorem incRotation_transpose_mul (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    (incRotation u v G)ᵀ * incRotation u v G = 1 :=
  tiltRotation_transpose_mul _ _ (incCos_sq hG hZ)

/-- (46): `det R = 1`. -/
theorem incRotation_det (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    (incRotation u v G).det = 1 :=
  tiltRotation_det _ _ (incCos_sq hG hZ)

/-- MAIN line 559: `R e₃ = (−c v/√G, −c u/√G, 1 − Z/G)`. -/
theorem incRotation_mulVec_e₃ (hG : 0 < G) :
    incRotation u v G *ᵥ e₃ =
      ![-(incCos u v G) * v / Real.sqrt G, -(incCos u v G) * u / Real.sqrt G,
        1 - ((u ^ 2 + v ^ 2) / 2) / G] := by
  have h := Real.sq_sqrt hG.le
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  rw [incRotation_eq_tiltRotation, tiltRotation_eq]
  ext i
  fin_cases i
  all_goals
    simp [e₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three, incTilt_apply_zero,
      incTilt_apply_one, incTilt_apply_two]
  · field_simp
  · field_simp
  · field_simp
    rw [h]; ring

/-- Rotations (46) preserve the cross product. -/
theorem incRotation_cross (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) (Q P : Fin 3 → ℝ) :
    (incRotation u v G *ᵥ Q) ⨯₃ (incRotation u v G *ᵥ P) = incRotation u v G *ᵥ (Q ⨯₃ P) :=
  mulVec_cross_mulVec _ (incRotation_transpose_mul hG hZ) (incRotation_det hG hZ) Q P

/-- The cross product of two embedded planar vectors points along `e₃`. -/
lemma planarEmbed_cross (Q P : Fin 2 → ℝ) :
    planarEmbed Q ⨯₃ planarEmbed P = (Q 0 * P 1 - Q 1 * P 0) • e₃ := by
  ext i
  fin_cases i <;> simp [planarEmbed, e₃, cross_apply]

/-- If `Q ⨯₃ P = G e₃`, then `(R Q) ⨯₃ (R P) = G • R e₃`. -/
theorem incRotation_cross_eq_smul (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G)
    {Q P : Fin 3 → ℝ} (hQP : Q ⨯₃ P = G • e₃) :
    (incRotation u v G *ᵥ Q) ⨯₃ (incRotation u v G *ᵥ P) = G • (incRotation u v G *ᵥ e₃) := by
  rw [incRotation_cross hG hZ, hQP, Matrix.mulVec_smul]

/-- MAIN (45): the `e₃`-projection of the rotated angular momentum is `G − Z`. -/
theorem incRotation_cross_dot_e₃ (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G)
    {Q P : Fin 3 → ℝ} (hQP : Q ⨯₃ P = G • e₃) :
    ((incRotation u v G *ᵥ Q) ⨯₃ (incRotation u v G *ᵥ P)) ⬝ᵥ e₃ = G - (u ^ 2 + v ^ 2) / 2 := by
  rw [incRotation_cross_eq_smul hG hZ hQP, incRotation_mulVec_e₃ hG]
  simp [e₃, dotProduct, Fin.sum_univ_three]
  field_simp

/-- The third component of `R e₃` is `1 − Z/G`, positive on the carrier. -/
lemma incRotation_e₃_two (hG : 0 < G) :
    (incRotation u v G *ᵥ e₃) 2 = 1 - ((u ^ 2 + v ^ 2) / 2) / G := by
  rw [incRotation_mulVec_e₃ hG]; simp

lemma incRotation_e₃_two_pos (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    0 < (incRotation u v G *ᵥ e₃) 2 := by
  rw [incRotation_e₃_two hG]
  have : ((u ^ 2 + v ^ 2) / 2) / G < 1 := (div_lt_one hG).2 hZ
  linarith

/-- MAIN lines 571–576: the cosine is recovered from `ŵ = R e₃`. -/
theorem incCos_eq_sqrt_of_e₃ (hG : 0 < G) :
    incCos u v G = Real.sqrt ((1 + (incRotation u v G *ᵥ e₃) 2) / 2) := by
  rw [incRotation_e₃_two hG, incCos, incTilt_dot hG]
  congr 1
  field_simp
  ring

/-- MAIN lines 571–576: `u` is recovered exactly from `R e₃` and `G`. -/
theorem incRotation_recover_u (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    u = -Real.sqrt G * (incRotation u v G *ᵥ e₃) 1 /
      Real.sqrt ((1 + (incRotation u v G *ᵥ e₃) 2) / 2) := by
  have hc := incCos_pos hG hZ
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  rw [← incCos_eq_sqrt_of_e₃ hG, incRotation_mulVec_e₃ hG]
  simp
  field_simp

/-- MAIN lines 571–576: `v` is recovered exactly from `R e₃` and `G`. -/
theorem incRotation_recover_v (hG : 0 < G) (hZ : (u ^ 2 + v ^ 2) / 2 < G) :
    v = -Real.sqrt G * (incRotation u v G *ᵥ e₃) 0 /
      Real.sqrt ((1 + (incRotation u v G *ᵥ e₃) 2) / 2) := by
  have hc := incCos_pos hG hZ
  have hs : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  rw [← incCos_eq_sqrt_of_e₃ hG, incRotation_mulVec_e₃ hG]
  simp
  field_simp

/-- Injectivity of `(u, v) ↦ R e₃` on the carrier at fixed `G`. -/
theorem incRotation_e₃_injective {u' v' : ℝ} (hG : 0 < G)
    (hZ : (u ^ 2 + v ^ 2) / 2 < G) (hZ' : (u' ^ 2 + v' ^ 2) / 2 < G)
    (h : incRotation u v G *ᵥ e₃ = incRotation u' v' G *ᵥ e₃) : u = u' ∧ v = v' := by
  refine ⟨?_, ?_⟩
  · rw [incRotation_recover_u hG hZ, incRotation_recover_u hG hZ', h]
  · rw [incRotation_recover_v hG hZ, incRotation_recover_v hG hZ', h]

/-- The open carrier `{0 < G, (u² + v²)/2 < G}` in the coordinates `(u, v, G)`. -/
def incCarrier : Set (ℝ × ℝ × ℝ) := {p | 0 < p.2.2 ∧ (p.1 ^ 2 + p.2.1 ^ 2) / 2 < p.2.2}

/-- Every entry of `R` is real analytic in `(u, v, G)` on the open carrier. -/
theorem incRotation_analyticOn (i j : Fin 3) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ => incRotation p.1 p.2.1 p.2.2 i j) incCarrier := by
  intro z hz
  obtain ⟨hG, hZ⟩ := hz
  have hu : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) z := analyticAt_fst
  have hv : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) z := analyticAt_fst.comp analyticAt_snd
  have hg : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) z := analyticAt_snd.comp analyticAt_snd
  have hsq : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.sqrt p.2.2) z :=
    ((hg.contDiffAt (n := ω)).sqrt hG.ne').analyticAt
  have hs0 : Real.sqrt z.2.2 ≠ 0 := (Real.sqrt_pos.2 hG).ne'
  have hd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => 2 * Real.sqrt p.2.2) z :=
    analyticAt_const.mul hsq
  have hd0 : 2 * Real.sqrt z.2.2 ≠ 0 := by positivity
  have h0 : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incTilt p.1 p.2.1 p.2.2 0) z := by
    simp only [incTilt_apply_zero]; exact hu.div hd hd0
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incTilt p.1 p.2.1 p.2.2 1) z := by
    simp only [incTilt_apply_one]; exact hv.neg.div hd hd0
  have h2 : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incTilt p.1 p.2.1 p.2.2 2) z := by
    simp only [incTilt_apply_two]; exact analyticAt_const
  have hn : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => 1 - incTilt p.1 p.2.1 p.2.2 ⬝ᵥ
      incTilt p.1 p.2.1 p.2.2) z := by
    simp only [dotProduct, Fin.sum_univ_three]
    exact analyticAt_const.sub (((h0.mul h0).add (h1.mul h1)).add (h2.mul h2))
  have hn0 : 1 - incTilt z.1 z.2.1 z.2.2 ⬝ᵥ incTilt z.1 z.2.1 z.2.2 ≠ 0 := by
    have := incTilt_dot_lt_half hG hZ
    linarith
  have hc : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incCos p.1 p.2.1 p.2.2) z :=
    ((hn.contDiffAt (n := ω)).sqrt hn0).analyticAt
  have hT : ∀ k, AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incTilt p.1 p.2.1 p.2.2 k) z := by
    intro k; fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hdot : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => incTilt p.1 p.2.1 p.2.2 ⬝ᵥ
      incTilt p.1 p.2.1 p.2.2) z := by
    simp only [dotProduct, Fin.sum_univ_three]
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hskew : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => skewMatrix (incTilt p.1 p.2.1 p.2.2) i j) z := by
    fin_cases i <;> fin_cases j <;> simp [skewMatrix] <;>
      first | exact analyticAt_const | exact (hT _) | exact (hT _).neg
  have hmain : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => ((1 - 2 * (incTilt p.1 p.2.1 p.2.2 ⬝ᵥ
      incTilt p.1 p.2.1 p.2.2)) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      + 2 * (incTilt p.1 p.2.1 p.2.2 i * incTilt p.1 p.2.1 p.2.2 j)
      + 2 * incCos p.1 p.2.1 p.2.2 * skewMatrix (incTilt p.1 p.2.1 p.2.2) i j)) z :=
    (((analyticAt_const.sub (analyticAt_const.mul hdot)).mul analyticAt_const).add
      (analyticAt_const.mul ((hT i).mul (hT j)))).add
      ((analyticAt_const.mul hc).mul hskew)
  refine hmain.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [incRotation, vecMulVec_apply]

end Inc

end KAM.Planetary.Spatial
