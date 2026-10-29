/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Constants

/-!
# Part 3 (local charts): the bordered determinant, direction coordinates and slopes

Blueprint nodes `bpI:p3:det-identity`,
`bpI:p3:coordinates` and `bpI:p3:slope-ray`. `n = 2`.

* `det_identity` (`bpI:p3:det-identity`): on the real slice, `∇²h` is symmetric,
  `det 𝖡_h(I) = -(g^⊥ ⬝ ∇²h g^⊥)` with `g = ∇h(I)`, `∇h(I) ≠ 0`, and
  `det (g, ∇²h g^⊥) = -det 𝖡_h(I)`. The determinant is computed after reindexing
  `Fin 2 ⊕ Unit ≃ Fin 3` and `Matrix.det_fin_three` (the technique of `KAM/Iso/Kepler.lean`).
* `coordinates` (`bpI:p3:coordinates`): `w = a_c(w) g_c + b_c(w) g_c^⊥`; `𝒰_c` is open and
  contains `c`; the chart map `Φ_c = (h, m_c)` is `C¹` on `𝒰_c` with `Φ_c(c) = (h(c), 0)`.
* `slope_ray` (`bpI:p3:slope-ray`): two vectors with positive longitudinal coordinate have the
  same slope iff they are positive multiples of each other, with ratio `‖w'‖ / ‖w‖`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-! ### The determinant of the bordered matrix -/

/-- The equivalence `Fin 2 ⊕ Unit ≃ Fin 3`, `(a, ()) ↦ (a, 2)` (reindexing for `det_fin_three`). -/
private def sumFin3 : Fin 2 ⊕ Unit ≃ Fin 3 where
  toFun
    | Sum.inl a => Fin.castSucc a
    | Sum.inr _ => 2
  invFun i := if hi : (i : ℕ) < 2 then Sum.inl ⟨i, hi⟩ else Sum.inr ()
  left_inv := by
    rintro (a | ⟨⟩)
    · fin_cases a <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The `3 × 3` determinant expansion for a matrix indexed by `Fin 2 ⊕ Unit`. -/
private theorem det_bordered {R : Type*} [CommRing R]
    (A : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) R) :
    A.det = A (Sum.inl 0) (Sum.inl 0) * A (Sum.inl 1) (Sum.inl 1) * A (Sum.inr ()) (Sum.inr ()) -
      A (Sum.inl 0) (Sum.inl 0) * A (Sum.inl 1) (Sum.inr ()) * A (Sum.inr ()) (Sum.inl 1) -
      A (Sum.inl 0) (Sum.inl 1) * A (Sum.inl 1) (Sum.inl 0) * A (Sum.inr ()) (Sum.inr ()) +
      A (Sum.inl 0) (Sum.inl 1) * A (Sum.inl 1) (Sum.inr ()) * A (Sum.inr ()) (Sum.inl 0) +
      A (Sum.inl 0) (Sum.inr ()) * A (Sum.inl 1) (Sum.inl 0) * A (Sum.inr ()) (Sum.inl 1) -
      A (Sum.inl 0) (Sum.inr ()) * A (Sum.inl 1) (Sum.inl 1) * A (Sum.inr ()) (Sum.inl 0) := by
  rw [← Matrix.det_reindex_self sumFin3 A, Matrix.det_fin_three]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

/-- The expansion of `det 𝖡_h(I)` along the last row (no hypothesis on `h`). -/
theorem borderedHessian_det_eq (h : (Fin 2 → ℂ) → ℂ) (I : Fin 2 → ℝ) :
    (KAM.Iso.borderedHessian h I).det =
      -(perp (frequencyMap h I) ⬝ᵥ (hessR h I *ᵥ perp (frequencyMap h I))) := by
  rw [det_bordered]
  simp only [KAM.Iso.borderedHessian, hessR, perp, dotProduct, Fin.sum_univ_two, mulVec,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `∇²h(I)` is symmetric on the real slice (`bp:p4:freq-map` (iii), restated). -/
theorem hessR_transpose (hd : HeadData B s₀ r₀ h B' η) {I : Fin 2 → ℝ} (hI : I ∈ realAct B r₀) :
    (hessR h I)ᵀ = hessR h I := by
  obtain ⟨-, -, hv, hsym, -⟩ :=
    KAM.Iso.Linear.freq_map_local (KAM.Head.isOpen_actionNbhd B r₀) hd.holo hd.real hI
  have key : ∀ a b, ((hessR h I a b : ℝ) : ℂ) = KAM.Head.hessian h (toC I) a b := by
    intro a b
    have h1 := congrFun (hv (Pi.single b 1)) a
    have h2 : (fun j => (((Pi.single b (1 : ℝ) : Fin 2 → ℝ) j : ℝ) : ℂ)) = Pi.single b 1 :=
      KAM.Head.realInclusion_single b
    rw [h2, Matrix.mulVec_single_one] at h1
    exact h1
  ext a b
  apply Complex.ofReal_injective
  rw [Matrix.transpose_apply, key, key]
  exact congrFun (congrFun hsym a) b

/-- `bpI:p3:det-identity` (and the symmetry of `∇²h`; (a): `∇h ≠ 0` on `U`). -/
theorem det_identity (hd : HeadData B s₀ r₀ h B' η) {I : Fin 2 → ℝ} (hI : I ∈ realAct B r₀) :
    (hessR h I)ᵀ = hessR h I ∧
    (KAM.Iso.borderedHessian h I).det =
      -(perp (frequencyMap h I) ⬝ᵥ (hessR h I *ᵥ perp (frequencyMap h I))) ∧
    frequencyMap h I ≠ 0 ∧
    det2 (frequencyMap h I) (hessR h I *ᵥ perp (frequencyMap h I)) =
      -(KAM.Iso.borderedHessian h I).det := by
  refine ⟨hessR_transpose hd hI, borderedHessian_det_eq h I,
    frequencyMap_ne_zero_of_det_ne_zero (hd.iso I hI), ?_⟩
  rw [borderedHessian_det_eq, neg_neg]
  simp only [det2, perp, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


/-! ### Direction coordinates -/

/-- `g ⬝ g > 0` for `g ≠ 0`. -/
theorem dotProduct_self_pos {g : Fin 2 → ℝ} (hg : g ≠ 0) : 0 < g ⬝ᵥ g :=
  lt_of_le_of_ne
    (by simpa only [dotProduct, Fin.sum_univ_two] using
      add_nonneg (mul_self_nonneg (g 0)) (mul_self_nonneg (g 1)))
    fun h0 => hg (dotProduct_self_eq_zero.1 h0.symm)

/-- `w ↦ a_g(w)` is continuous. -/
theorem continuous_aCoord (g : Fin 2 → ℝ) : Continuous (aCoord g) := by
  unfold aCoord
  simp only [dotProduct]
  fun_prop

/-- `g ⬝ w = a_g(w) (g ⬝ g)`. -/
theorem dotProduct_eq_aCoord_mul {g : Fin 2 → ℝ} (hg : g ≠ 0) (w : Fin 2 → ℝ) :
    g ⬝ᵥ w = aCoord g w * (g ⬝ᵥ g) := by
  have := (dotProduct_self_pos hg).ne'
  unfold aCoord
  field_simp

/-- `det2 g g = 0`. -/
theorem det2_self (g : Fin 2 → ℝ) : det2 g g = 0 := by
  simp only [det2]
  ring

/-- `w = a_g(w) g + b_g(w) g^⊥` for `g ≠ 0`. -/
theorem eq_aCoord_smul_add_bCoord_smul {g : Fin 2 → ℝ} (hg : g ≠ 0) (w : Fin 2 → ℝ) :
    w = aCoord g w • g + bCoord g w • perp g := by
  have hq' : g 0 * g 0 + g 1 * g 1 ≠ 0 := by
    simpa only [dotProduct, Fin.sum_univ_two] using (dotProduct_self_pos hg).ne'
  ext i
  fin_cases i
  · simp only [aCoord, bCoord, det2, perp, dotProduct, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hq']
    ring
  · simp only [aCoord, bCoord, det2, perp, dotProduct, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hq']
    ring

/-- `bpI:p3:coordinates` (the claims of the definition). -/
theorem coordinates (hd : HeadData B s₀ r₀ h B' η) {c : Fin 2 → ℝ} (hc : c ∈ realAct B r₀) :
    (∀ w, w = aCoord (frequencyMap h c) w • frequencyMap h c +
      bCoord (frequencyMap h c) w • perp (frequencyMap h c)) ∧
    IsOpen (chartDom h B r₀ c) ∧ c ∈ chartDom h B r₀ c ∧
    ContDiffOn ℝ 1 (chartPhi h c) (chartDom h B r₀ c) ∧ chartPhi h c c = (realPart h c, 0) := by
  have hg : frequencyMap h c ≠ 0 := (det_identity hd hc).2.2.1
  have hq : 0 < frequencyMap h c ⬝ᵥ frequencyMap h c := dotProduct_self_pos hg
  have hfreq : ContDiffOn ℝ 1 (frequencyMap h) (realAct B r₀) := contDiffOn_frequencyMap hd
  have hsub : chartDom h B r₀ c ⊆ realAct B r₀ := fun I hI => hI.1
  have haC : aCoord (frequencyMap h c) (frequencyMap h c) = 1 := by
    unfold aCoord
    exact div_self hq.ne'
  refine ⟨eq_aCoord_smul_add_bCoord_smul hg, ?_, ⟨hc, by rw [haC]; exact one_pos⟩, ?_, ?_⟩
  · have hcont : ContinuousOn (fun I => aCoord (frequencyMap h c) (frequencyMap h I))
        (realAct B r₀) :=
      (continuous_aCoord _).comp_continuousOn hfreq.continuousOn
    exact hcont.isOpen_inter_preimage (isOpen_realAct_charts B r₀) isOpen_Ioi
  · -- `C¹` regularity of `Φ_c = (Re h, m_c)`
    have hRe : ContDiffOn ℝ 1 (realPart h) (realAct B r₀) :=
      (KAM.Iso.Linear.freq_map_contDiff (KAM.Head.isOpen_actionNbhd B r₀) hd.holo hd.real).1
    have hcomp : ∀ i, ContDiffOn ℝ 1 (fun I => frequencyMap h I i) (chartDom h B r₀ c) :=
      fun i => ((contDiffOn_pi.1 hfreq) i).mono hsub
    have hnum : ContDiffOn ℝ 1 (fun I => det2 (frequencyMap h c) (frequencyMap h I))
        (chartDom h B r₀ c) := by
      unfold det2
      exact (contDiffOn_const.mul (hcomp 1)).sub (contDiffOn_const.mul (hcomp 0))
    have hden : ContDiffOn ℝ 1 (fun I => frequencyMap h c ⬝ᵥ frequencyMap h I)
        (chartDom h B r₀ c) := by
      simp only [dotProduct, Fin.sum_univ_two]
      exact (contDiffOn_const.mul (hcomp 0)).add (contDiffOn_const.mul (hcomp 1))
    have hne : ∀ I ∈ chartDom h B r₀ c, frequencyMap h c ⬝ᵥ frequencyMap h I ≠ 0 := by
      intro I hI
      rw [dotProduct_eq_aCoord_mul hg]
      exact (mul_pos hI.2 hq).ne'
    exact (hRe.mono hsub).prodMk (hnum.div hden hne)
  · refine Prod.ext rfl ?_
    show slope (frequencyMap h c) (frequencyMap h c) = 0
    rw [slope, det2_self, zero_div]

/-! ### Slopes encode rays -/

/-- `bpI:p3:slope-ray`. -/
theorem slope_ray {g w w' : Fin 2 → ℝ} (hg : g ≠ 0) (hw : 0 < aCoord g w) (hw' : 0 < aCoord g w') :
    (slope g w = slope g w' ↔ w' = (aCoord g w' / aCoord g w) • w) ∧
    (slope g w = slope g w' → aCoord g w' / aCoord g w = ‖w'‖ / ‖w‖) := by
  have hq : 0 < g ⬝ᵥ g := dotProduct_self_pos hg
  have hgw : 0 < g ⬝ᵥ w := by rw [dotProduct_eq_aCoord_mul hg]; exact mul_pos hw hq
  have hgw' : 0 < g ⬝ᵥ w' := by rw [dotProduct_eq_aCoord_mul hg]; exact mul_pos hw' hq
  have hq' : g 0 * g 0 + g 1 * g 1 ≠ 0 := by
    simpa only [dotProduct, Fin.sum_univ_two] using hq.ne'
  have e1 : g ⬝ᵥ w = g 0 * w 0 + g 1 * w 1 := by simp [dotProduct, Fin.sum_univ_two]
  have e2 : g ⬝ᵥ w' = g 0 * w' 0 + g 1 * w' 1 := by simp [dotProduct, Fin.sum_univ_two]
  have hne : g 0 * w 0 + g 1 * w 1 ≠ 0 := by rw [← e1]; exact hgw.ne'
  have hratio : aCoord g w' / aCoord g w = (g ⬝ᵥ w') / (g ⬝ᵥ w) := by
    unfold aCoord
    field_simp
  have hmain : slope g w = slope g w' ↔ w' = (aCoord g w' / aCoord g w) • w := by
    rw [hratio]
    unfold slope
    rw [div_eq_div_iff hgw.ne' hgw'.ne', e1, e2]
    simp only [det2]
    constructor
    · intro hs
      have hpar : w' 0 * w 1 = w' 1 * w 0 := by
        have h0 : (g 0 * g 0 + g 1 * g 1) * (w' 0 * w 1 - w' 1 * w 0) = 0 := by
          linear_combination hs
        rcases mul_eq_zero.1 h0 with h0 | h0
        · exact absurd h0 hq'
        · linarith
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hne]
        linear_combination g 1 * hpar
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hne]
        linear_combination (-g 0) * hpar
    · intro hw'eq
      have h0 : w' 0 = (g 0 * w' 0 + g 1 * w' 1) / (g 0 * w 0 + g 1 * w 1) * w 0 := by
        simpa [e1, e2] using congrFun hw'eq 0
      have h1 : w' 1 = (g 0 * w' 0 + g 1 * w' 1) / (g 0 * w 0 + g 1 * w 1) * w 1 := by
        simpa [e1, e2] using congrFun hw'eq 1
      rw [div_mul_eq_mul_div, eq_div_iff hne] at h0 h1
      linear_combination (-g 0) * h1 + g 1 * h0
  refine ⟨hmain, fun hs => ?_⟩
  have hw'eq := hmain.1 hs
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0] at hgw
    simp at hgw
  have hpos : 0 < aCoord g w' / aCoord g w := div_pos hw' hw
  have hnorm : ‖w'‖ = aCoord g w' / aCoord g w * ‖w‖ := by
    have := congrArg norm hw'eq
    rwa [norm_smul, Real.norm_of_nonneg hpos.le] at this
  rw [hnorm]
  exact (mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hwne)).symm

end KAM.Iso.Charts
