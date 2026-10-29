/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.BorderUnique

/-!
# The bordered triangular system (HL19 Lemma 6.1)

Blueprint node `bpI:p1:border-solve`
(`KAM.Iso.Linear.border_solve`), second module. The solution is the explicit construction
`bordSol`, `bordXi0`, `bordXiOmega`, `bordXiN`, `bordGL`, `bordXiL` of `Linear/Defs`; the proof
follows the steps `bs-first`, `bs-averages`, `bs-bordered`, `bs-energy`, `bs-second`, `bs-unique`,
`bs-real` of the blueprint. Each item is a helper lemma in the namespace
`KAM.Iso.Linear.BorderSolve`; `border_solve` assembles them in the order of the items (a)-(e).

* `𝓡` is `KAM.Apost.cohR`, used through the vector clause of `KAM.cohomological` (Part 1, only
  `γ > 0`, `τ ≥ 0` and `ω` Diophantine) with loss `δ` twice (on `T_r`, then on `T_{r-δ}`), and
  `KAM.Apost.Tools.cohConst_div_le_cR` converts its constant to `c_R γ⁻¹ δ^{-κ}`.
* The averages of the products use `KAM.Apost.Triangular.avg_mulVec_const` and the
  dot-product analogue `avg_dotProduct_const` of `Linear/BorderUnique`.
* The bordered average system is solved on `Fin n ⊕ Unit` by `Matrix.mul_nonsing_inv`
  (`bordAvg_mulVec_bordSol`), its real inverse is `Linear.inv_im_eq_zero`.
* Uniqueness (d) is `border_unique` plus `eq_avg_of_fderiv_eq_zero` for the free constant of `ξᴸ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

namespace BorderSolve

/-! ### Norm helpers -/

/-- The frequency vector, as a complex vector, has norm at most `‖ω‖`. -/
theorem norm_omega_le (ω : Fin n → ℝ) : ‖(fun a => (ω a : ℂ))‖ ≤ ‖ω‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  simpa using norm_le_pi_norm ω a

/-- The norm of a border vector `(x; y)` is at most `M` if both `‖x‖` and `‖y‖` are. -/
theorem norm_sumElim_le {x : Fin n → ℂ} {y : ℂ} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖(Sum.elim x (fun _ => y) : Fin n ⊕ Unit → ℂ)‖ ≤ M := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hy)).2 ?_
  rintro (a | u)
  · exact (norm_le_pi_norm x a).trans hx
  · exact hy

/-- `‖ξ₀‖ ≤ ‖(ξ₀, ξ^ω)‖`. -/
theorem norm_bordXi0_le (ω : Fin n → ℝ) (d : BordData n) : ‖bordXi0 ω d‖ ≤ ‖bordSol ω d‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (bordSol ω d) (Sum.inl a)

/-- `‖ξ^ω‖ ≤ ‖(ξ₀, ξ^ω)‖`. -/
theorem norm_bordXiOmega_le (ω : Fin n → ℝ) (d : BordData n) :
    ‖bordXiOmega ω d‖ ≤ ‖bordSol ω d‖ :=
  norm_le_pi_norm (bordSol ω d) (Sum.inr ())

/-- `|Y ξ| ≤ (∑_b |Y_b|) ‖ξ‖`. -/
theorem norm_dotProduct_le (Y u : Fin n → ℂ) : ‖Y ⬝ᵥ u‖ ≤ (∑ b, ‖Y b‖) * ‖u‖ := by
  calc ‖Y ⬝ᵥ u‖ ≤ ∑ b, ‖Y b * u b‖ := norm_sum_le _ _
    _ ≤ ∑ b, ‖Y b‖ * ‖u‖ := Finset.sum_le_sum fun b _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u b) (norm_nonneg _)
    _ = (∑ b, ‖Y b‖) * ‖u‖ := by rw [Finset.sum_mul]

/-! ### Steps `bs-averages` and `bs-bordered`: the size of `(ξ₀, ξ^ω)` -/

/-- Steps `bs-averages`, `bs-bordered`: `|(ξ₀, ξ^ω)| ≤ σ max {H_L + H_T Z, |η^ω| + H_Y Z}`, where
`Z = Γ_δ H_N` bounds `uᴺ`. -/
theorem norm_bordSol_le {ω : Fin n → ℝ} (d : BordData n) {r δ HL HT HY Z σ : ℝ} (hr : 0 < r)
    (hrδ : 0 < r - δ) (hHL : ∀ θ ∈ complexStrip n r, ‖d.ηL θ‖ ≤ HL)
    (hHT : ∀ θ ∈ complexStrip n (r - δ), ‖d.T θ‖ ≤ HT)
    (hHY : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖d.Y θ b‖ ≤ HY)
    (hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU ω d.ηN θ‖ ≤ Z)
    (hσ : ‖(bordAvg ω d)⁻¹‖ ≤ σ) :
    ‖bordSol ω d‖ ≤ σ * max (HL + HT * Z) (‖d.ηω‖ + HY * Z) := by
  have hHT0 : 0 ≤ HT := (norm_nonneg _).trans (hHT _ (ofReal_mem_complexStrip hrδ 0))
  have hHY0 : 0 ≤ HY :=
    (Finset.sum_nonneg fun b _ => norm_nonneg _).trans (hHY _ (ofReal_mem_complexStrip hrδ 0))
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have h1 : ‖avg d.ηL‖ ≤ HL := norm_torusAverage_le_of_strip_bound hr hHL
  have h2 : ‖avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ)‖ ≤ HT * Z := by
    refine norm_torusAverage_le_of_strip_bound (f := fun θ => d.T θ *ᵥ triU ω d.ηN θ) hrδ ?_
    intro θ hθ
    calc ‖d.T θ *ᵥ triU ω d.ηN θ‖ ≤ ‖d.T θ‖ * ‖triU ω d.ηN θ‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ HT * Z := mul_le_mul (hHT θ hθ) (hU θ hθ) (norm_nonneg _) hHT0
  have h3 : ‖avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)‖ ≤ HY * Z := by
    refine norm_torusAverage_le_of_strip_bound (f := fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ) hrδ ?_
    intro θ hθ
    calc ‖d.Y θ ⬝ᵥ triU ω d.ηN θ‖ ≤ (∑ b, ‖d.Y θ b‖) * ‖triU ω d.ηN θ‖ := norm_dotProduct_le _ _
      _ ≤ HY * Z := mul_le_mul (hHY θ hθ) (hU θ hθ) (norm_nonneg _) hHY0
  have hw : ‖(Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
      (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) : Fin n ⊕ Unit → ℂ)‖ ≤
        max (HL + HT * Z) (‖d.ηω‖ + HY * Z) :=
    norm_sumElim_le ((norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_max_left _ _)))
      ((norm_add_le _ _).trans ((add_le_add le_rfl h3).trans (le_max_right _ _)))
  calc ‖bordSol ω d‖ ≤ ‖(bordAvg ω d)⁻¹‖ * ‖(Sum.elim (avg d.ηL +
        avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
        (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) : Fin n ⊕ Unit → ℂ)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ σ * max (HL + HT * Z) (‖d.ηω‖ + HY * Z) := mul_le_mul hσ hw (norm_nonneg _) hσ0

/-! ### Steps `bs-energy`, `bs-second`: bounds on `ξᴺ` and `gᴸ` -/

/-- Bounds on `ξᴺ` and `gᴸ` in terms of a bound `S` of `|(ξ₀, ξ^ω)|` and `Z ≥ |uᴺ|`. -/
theorem norm_bordXiN_bordGL_le (ω : Fin n → ℝ) (d : BordData n) {S Z HL HT : ℝ}
    {s : Set (Fin n → ℂ)} (hS : ‖bordSol ω d‖ ≤ S) (hU : ∀ θ ∈ s, ‖triU ω d.ηN θ‖ ≤ Z)
    (hHL : ∀ θ ∈ s, ‖d.ηL θ‖ ≤ HL) (hHT : ∀ θ ∈ s, ‖d.T θ‖ ≤ HT) {θ : Fin n → ℂ} (hθ : θ ∈ s) :
    ‖bordXiN ω d θ‖ ≤ S + Z ∧
      ‖bordGL ω d θ‖ ≤ HT * (S + Z) + ‖ω‖ * S + HL := by
  have hHT0 : 0 ≤ HT := (norm_nonneg _).trans (hHT θ hθ)
  have hXN : ‖bordXiN ω d θ‖ ≤ S + Z :=
    (norm_sub_le _ _).trans (add_le_add ((norm_bordXi0_le ω d).trans hS) (hU θ hθ))
  refine ⟨hXN, ?_⟩
  have hω0 : ‖bordXiOmega ω d • (fun a => (ω a : ℂ))‖ ≤ S * ‖ω‖ := by
    rw [norm_smul]
    exact mul_le_mul ((norm_bordXiOmega_le ω d).trans hS) (norm_omega_le ω) (norm_nonneg _)
      ((norm_nonneg _).trans hS)
  calc ‖d.T θ *ᵥ bordXiN ω d θ + bordXiOmega ω d • (fun a => (ω a : ℂ)) - d.ηL θ‖
      ≤ ‖d.T θ *ᵥ bordXiN ω d θ‖ + ‖bordXiOmega ω d • (fun a => (ω a : ℂ))‖ + ‖d.ηL θ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ HT * (S + Z) + S * ‖ω‖ + HL := by
        gcongr
        · exact (Matrix.linfty_opNorm_mulVec _ _).trans
            (mul_le_mul (hHT θ hθ) hXN (norm_nonneg _) hHT0)
        · exact hHL θ hθ
    _ = HT * (S + Z) + ‖ω‖ * S + HL := by ring

/-! ### Step `bs-second`: the average of `gᴸ` -/

/-- Step `bs-second`: `⟨gᴸ⟩ = ⟨T⟩ ξ₀ - ⟨T uᴺ⟩ + ω ξ^ω - ⟨ηᴸ⟩ = 0`, by the first row of the bordered
average system. -/
theorem avg_bordGL_eq_zero (ω : Fin n → ℝ) (d : BordData n) (hinv : IsUnit (bordAvg ω d).det)
    (hcL : Continuous fun x : Fin n → ℝ => d.ηL (fun i => (x i : ℂ)))
    (hcT : Continuous fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ)))
    (hcU : Continuous fun x : Fin n → ℝ => triU ω d.ηN (fun i => (x i : ℂ))) :
    avg (bordGL ω d) = 0 := by
  have hg : bordGL ω d = fun θ => ((d.T θ *ᵥ bordXi0 ω d - d.T θ *ᵥ triU ω d.ηN θ) +
      bordXiOmega ω d • (fun a => (ω a : ℂ))) - d.ηL θ := by
    funext θ
    simp only [bordGL, bordXiN, Matrix.mulVec_sub]
  have hcA : Continuous fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ)) *ᵥ bordXi0 ω d :=
    hcT.matrix_mulVec continuous_const
  have hcB : Continuous fun x : Fin n → ℝ =>
      d.T (fun i => (x i : ℂ)) *ᵥ triU ω d.ηN (fun i => (x i : ℂ)) := hcT.matrix_mulVec hcU
  rw [hg, avg_sub_of_continuous ((hcA.sub hcB).add continuous_const) hcL,
    avg_add_of_continuous (hcA.sub hcB) continuous_const, avg_sub_of_continuous hcA hcB, avg_const,
    Triangular.avg_mulVec_const hcT]
  have h := (bordSol_rows ω d hinv).1
  rw [show avg d.T *ᵥ bordXi0 ω d - avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ) +
      bordXiOmega ω d • (fun a => (ω a : ℂ)) - avg d.ηL =
      (avg d.T *ᵥ bordXi0 ω d + bordXiOmega ω d • (fun a => (ω a : ℂ))) -
        (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ)) by abel, h, sub_self]

/-! ### Step `bs-real`: realness of `(ξ₀, ξ^ω)` -/

/-- Step `bs-real`: `(ξ₀, ξ^ω)` is real when the data are real on reals. -/
theorem bordSol_im_eq_zero (ω : Fin n → ℝ) (d : BordData n)
    (hcL : Continuous fun x : Fin n → ℝ => d.ηL (fun i => (x i : ℂ)))
    (hcT : Continuous fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ)))
    (hcY : Continuous fun x : Fin n → ℝ => d.Y (fun i => (x i : ℂ)))
    (hcU : Continuous fun x : Fin n → ℝ => triU ω d.ηN (fun i => (x i : ℂ)))
    (hηL : IsRealVec d.ηL) (hT : IsRealMat d.T) (hY : IsRealVec d.Y)
    (hU : IsRealVec (triU ω d.ηN)) (hηω : d.ηω.im = 0) (i : Fin n ⊕ Unit) :
    (bordSol ω d i).im = 0 := by
  have hTavg : ∀ a b, ((avg d.T) a b).im = 0 := fun a b => by
    show (torusAverage (fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ))) a b).im = 0
    rw [torusAverage_matrix_apply hcT a b]
    exact Tools.im_integral_eq_zero fun x => hT x a b
  have hYavg : ∀ b, ((avg d.Y) b).im = 0 := fun b => by
    show (torusAverage (fun x : Fin n → ℝ => d.Y (fun i => (x i : ℂ))) b).im = 0
    rw [Tools.torusAverage_vector_apply hcY b]
    exact Tools.im_integral_eq_zero fun x => hY x b
  have hA : ∀ i j, ((bordAvg ω d) i j).im = 0 := by
    rintro (a | u) (b | v)
    · simpa [bordAvg, bordMat] using hTavg a b
    · simp [bordAvg, bordMat]
    · simpa [bordAvg, bordMat] using hYavg b
    · simp [bordAvg, bordMat]
  have hw : ∀ j, ((Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
      (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) : Fin n ⊕ Unit → ℂ) j).im = 0 := by
    rintro (j | u)
    · simp only [Sum.elim_inl]
      have h1 : (avg d.ηL j).im = 0 := by
        show (torusAverage (fun x : Fin n → ℝ => d.ηL (fun i => (x i : ℂ))) j).im = 0
        rw [Tools.torusAverage_vector_apply hcL j]
        exact Tools.im_integral_eq_zero fun x => hηL x j
      have h2 : (avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ) j).im = 0 := by
        show (torusAverage (fun x : Fin n → ℝ =>
          d.T (fun i => (x i : ℂ)) *ᵥ triU ω d.ηN (fun i => (x i : ℂ))) j).im = 0
        rw [Tools.torusAverage_vector_apply (hcT.matrix_mulVec hcU) j]
        exact Tools.im_integral_eq_zero fun x => Triangular.mulVec_im_eq_zero (hT x) (hU x) j
      rw [Pi.add_apply, Complex.add_im, h1, h2, add_zero]
    · simp only [Sum.elim_inr]
      have h3 : (avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)).im = 0 := by
        show (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          d.Y (fun i => (x i : ℂ)) ⬝ᵥ triU ω d.ηN (fun i => (x i : ℂ))).im = 0
        exact Tools.im_integral_eq_zero fun x => by
          simp [dotProduct, Complex.im_sum, Complex.mul_im, hY x, hU x]
      rw [Complex.add_im, hηω, h3, add_zero]
  unfold bordSol
  exact Triangular.mulVec_im_eq_zero (fun a b => inv_im_eq_zero hA a b) hw i

end BorderSolve

open BorderSolve in
/-- `bpI:p1:border-solve` (HL19 Lemma 6.1): (a) well defined, (b) the system, (c) estimates with
`S_* = σ max {H_L + H_TΓH_N, |η^ω| + H_YΓH_N}`, (d) uniqueness up to `⟨ξᴸ⟩`, (e) realness. -/
theorem border_solve {γ τ : ℝ} {ω : Fin n → ℝ} (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hdio : IsDiophantine γ τ ω) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (h2δ : 2 * δ < r)
    (d : BordData n) {HL HN HT HY σ : ℝ}
    (hηL : DifferentiableOn ℂ d.ηL (complexStrip n r)) (hηLp : IsPeriodicOn d.ηL r)
    (hηN : DifferentiableOn ℂ d.ηN (complexStrip n r)) (hηNp : IsPeriodicOn d.ηN r)
    (hHL : ∀ θ ∈ complexStrip n r, ‖d.ηL θ‖ ≤ HL) (hHN : ∀ θ ∈ complexStrip n r, ‖d.ηN θ‖ ≤ HN)
    (hηN0 : avg d.ηN = 0) (hT : DifferentiableOn ℂ d.T (complexStrip n r))
    (hTp : IsPeriodicOn d.T r)
    (hY : DifferentiableOn ℂ d.Y (complexStrip n r)) (hYp : IsPeriodicOn d.Y r)
    (hHT : ∀ θ ∈ complexStrip n (r - δ), ‖d.T θ‖ ≤ HT)
    (hHY : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖d.Y θ b‖ ≤ HY)
    (hinv : IsUnit (bordAvg ω d).det) (hσ : ‖(bordAvg ω d)⁻¹‖ ≤ σ) (ξL0 : Fin n → ℂ) :
    -- (a)
    (DifferentiableOn ℂ (bordXiN ω d) (complexStrip n (r - δ)) ∧
      IsPeriodicOn (bordXiN ω d) (r - δ) ∧
      DifferentiableOn ℂ (bordGL ω d) (complexStrip n (r - δ)) ∧ IsPeriodicOn (bordGL ω d) (r - δ) ∧
      avg (bordGL ω d) = 0 ∧ DifferentiableOn ℂ (bordXiL ω d ξL0) (complexStrip n (r - 2 * δ)) ∧
      IsPeriodicOn (bordXiL ω d ξL0) (r - 2 * δ)) ∧
    -- (b)
    ((∀ θ ∈ complexStrip n (r - 2 * δ), d.T θ *ᵥ bordXiN ω d θ -
        fderiv ℂ (bordXiL ω d ξL0) θ (fun l => (ω l : ℂ)) +
          bordXiOmega ω d • (fun a => (ω a : ℂ)) = d.ηL θ) ∧
      (∀ θ ∈ complexStrip n (r - δ),
        -fderiv ℂ (bordXiN ω d) θ (fun l => (ω l : ℂ)) = d.ηN θ) ∧
      avg (fun θ => d.Y θ ⬝ᵥ bordXiN ω d θ) = d.ηω) ∧
    -- (c)
    (‖bordSol ω d‖ ≤ σ * max (HL + HT * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * HN)
        (‖d.ηω‖ + HY * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * HN) ∧
      ∀ S, ‖bordSol ω d‖ ≤ S →
        (∀ θ ∈ complexStrip n (r - δ),
          ‖bordXiN ω d θ‖ ≤ S + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN ∧
          ‖bordGL ω d θ‖ ≤ HT * (S + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN) + ‖ω‖ * S + HL) ∧
        ∀ G, (∀ θ ∈ complexStrip n (r - δ), ‖bordGL ω d θ‖ ≤ G) →
          ∀ θ ∈ complexStrip n (r - 2 * δ),
            ‖bordXiL ω d ξL0 θ - ξL0‖ ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * G) ∧
    -- (d)
    (∀ (ξL' ξN' : (Fin n → ℂ) → Fin n → ℂ) (ξω' : ℂ),
      DifferentiableOn ℂ ξL' (complexStrip n (r - 2 * δ)) → IsPeriodicOn ξL' (r - 2 * δ) →
      DifferentiableOn ℂ ξN' (complexStrip n (r - 2 * δ)) → IsPeriodicOn ξN' (r - 2 * δ) →
      (∀ θ ∈ complexStrip n (r - 2 * δ), d.T θ *ᵥ ξN' θ -
        fderiv ℂ ξL' θ (fun l => (ω l : ℂ)) + ξω' • (fun a => (ω a : ℂ)) = d.ηL θ) →
      (∀ θ ∈ complexStrip n (r - 2 * δ), -fderiv ℂ ξN' θ (fun l => (ω l : ℂ)) = d.ηN θ) →
      avg (fun θ => d.Y θ ⬝ᵥ ξN' θ) = d.ηω →
      ξω' = bordXiOmega ω d ∧ (∀ θ ∈ complexStrip n (r - 2 * δ), ξN' θ = bordXiN ω d θ) ∧
        ∃ c : Fin n → ℂ, ∀ θ ∈ complexStrip n (r - 2 * δ), ξL' θ - bordXiL ω d ξL0 θ = c) ∧
    -- (e)
    (IsRealVec d.ηL → IsRealVec d.ηN → IsRealMat d.T → IsRealVec d.Y → d.ηω.im = 0 →
      (∀ i, (ξL0 i).im = 0) →
      (∀ i, (bordXi0 ω d i).im = 0) ∧ (bordXiOmega ω d).im = 0 ∧ IsRealVec (bordXiN ω d) ∧
        IsRealVec (bordGL ω d) ∧ IsRealVec (bordXiL ω d ξL0)) := by
  -- the periodicity `hYp` of `Y` is not needed (holomorphy gives continuity on the real torus)
  have _ := hYp
  have hδr : δ < r := by linarith
  have hr1 : 0 < r - δ := by linarith
  have hr2 : 0 < r - 2 * δ := by linarith
  have hδr1 : δ < r - δ := by linarith
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hHN0 : 0 ≤ HN := (norm_nonneg _).trans (hHN _ (ofReal_mem_complexStrip hr 0))
  have hrr : r - δ - δ = r - 2 * δ := by ring
  have hcL := Triangular.continuous_ofReal_comp hr hηL
  have hcT := Triangular.continuous_ofReal_comp hr hT
  have hcY := Triangular.continuous_ofReal_comp hr hY
  -- step `bs-first`: `uᴺ = 𝓡 ηᴺ` on `T_{r-δ}`
  obtain ⟨-, hvec1⟩ := KAM.cohomological hdio hγ hτ hδ hδr (ρ := r)
  obtain ⟨hU1, hU2, -, hU4, hU5, hU6, -⟩ := hvec1 (p := n) d.ηN HN hηN hηNp hHN hηN0
  have hUd : DifferentiableOn ℂ (triU ω d.ηN) (complexStrip n (r - δ)) := hU1
  have hUp : IsPeriodicOn (triU ω d.ηN) (r - δ) := hU2
  have hUderiv : ∀ θ ∈ complexStrip n (r - δ),
      fderiv ℂ (triU ω d.ηN) θ (fun l => (ω l : ℂ)) = d.ηN θ := hU4
  have hUb : ∀ θ ∈ complexStrip n (r - δ),
      ‖triU ω d.ηN θ‖ ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN :=
    fun θ hθ => (hU5 θ hθ).trans (Tools.cohConst_div_le_cR hγ hδ hHN0)
  have hcU : Continuous fun x : Fin n → ℝ => triU ω d.ηN (fun i => (x i : ℂ)) :=
    Triangular.continuous_ofReal_comp hr1 hUd
  have hX : ∀ S, ‖bordSol ω d‖ ≤ S → ∀ θ ∈ complexStrip n (r - δ),
      ‖bordXiN ω d θ‖ ≤ S + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN ∧
        ‖bordGL ω d θ‖ ≤ HT * (S + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN) + ‖ω‖ * S + HL :=
    fun S hS θ hθ => norm_bordXiN_bordGL_le ω d hS hUb (fun θ hθ => hHL θ (hsub hθ)) hHT hθ
  -- `ξᴺ` and `gᴸ` on `T_{r-δ}`
  have hξd : DifferentiableOn ℂ (bordXiN ω d) (complexStrip n (r - δ)) :=
    (differentiableOn_const _).sub hUd
  have hξp : IsPeriodicOn (bordXiN ω d) (r - δ) := fun i z hz => by
    simp only [bordXiN, hUp i z hz]
  have hgd : DifferentiableOn ℂ (bordGL ω d) (complexStrip n (r - δ)) :=
    (((hT.mono hsub).matrix_mulVec hξd).add (differentiableOn_const _)).sub (hηL.mono hsub)
  have hgp : IsPeriodicOn (bordGL ω d) (r - δ) := fun i z hz => by
    simp only [bordGL, Triangular.isPeriodicOn_mono (by linarith) hTp i z hz, hξp i z hz,
      Triangular.isPeriodicOn_mono (by linarith) hηLp i z hz]
  have hg0 : avg (bordGL ω d) = 0 := avg_bordGL_eq_zero ω d hinv hcL hcT hcU
  have hgb : ∀ θ ∈ complexStrip n (r - δ), ‖bordGL ω d θ‖ ≤
      HT * (‖bordSol ω d‖ + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * HN) + ‖ω‖ * ‖bordSol ω d‖ + HL :=
    fun θ hθ => (hX _ le_rfl θ hθ).2
  -- step `bs-second`: `ξᴸ = ξᴸ₀ + 𝓡 gᴸ` on `T_{r-2δ}`
  obtain ⟨-, hvec2⟩ := KAM.cohomological hdio hγ hτ hδ hδr1 (ρ := r - δ)
  obtain ⟨hL1, hL2, -, hL4, -, hL6, -⟩ := hvec2 (p := n) (bordGL ω d) _ hgd hgp hgb hg0
  rw [hrr] at hL1 hL2 hL4
  have hL1' : DifferentiableOn ℂ (cohR ω (bordGL ω d)) (complexStrip n (r - 2 * δ)) := hL1
  have hL2' : IsPeriodicOn (cohR ω (bordGL ω d)) (r - 2 * δ) := hL2
  have hLd : DifferentiableOn ℂ (bordXiL ω d ξL0) (complexStrip n (r - 2 * δ)) :=
    (differentiableOn_const _).add hL1'
  have hLp : IsPeriodicOn (bordXiL ω d ξL0) (r - 2 * δ) := fun i z hz => by
    simp only [bordXiL, hL2' i z hz]
  have hLderiv : ∀ θ ∈ complexStrip n (r - 2 * δ),
      fderiv ℂ (bordXiL ω d ξL0) θ (fun l => (ω l : ℂ)) = bordGL ω d θ := fun θ hθ => by
    have h : fderiv ℂ (bordXiL ω d ξL0) θ = fderiv ℂ (cohR ω (bordGL ω d)) θ :=
      fderiv_const_add (f := cohR ω (bordGL ω d)) (x := θ) ξL0
    rw [h]
    exact hL4 θ hθ
  -- step `bs-energy`: the three equations
  have hb1 : ∀ θ ∈ complexStrip n (r - 2 * δ), d.T θ *ᵥ bordXiN ω d θ -
      fderiv ℂ (bordXiL ω d ξL0) θ (fun l => (ω l : ℂ)) +
        bordXiOmega ω d • (fun a => (ω a : ℂ)) = d.ηL θ := fun θ hθ => by
    rw [hLderiv θ hθ]
    simp only [bordGL]
    abel
  have hb2 : ∀ θ ∈ complexStrip n (r - δ),
      -fderiv ℂ (bordXiN ω d) θ (fun l => (ω l : ℂ)) = d.ηN θ := fun θ hθ => by
    have h : fderiv ℂ (bordXiN ω d) θ = -fderiv ℂ (triU ω d.ηN) θ :=
      fderiv_const_sub (f := triU ω d.ηN) (x := θ) (bordXi0 ω d)
    rw [h, _root_.neg_apply, hUderiv θ hθ, neg_neg]
  have hb3 : avg (fun θ => d.Y θ ⬝ᵥ bordXiN ω d θ) = d.ηω := by
    have hpt : (fun θ => d.Y θ ⬝ᵥ bordXiN ω d θ) =
        fun θ => d.Y θ ⬝ᵥ bordXi0 ω d - d.Y θ ⬝ᵥ triU ω d.ηN θ := by
      funext θ
      simp only [bordXiN, dotProduct_sub]
    rw [hpt, avg_sub_of_continuous (hcY.dotProduct continuous_const) (hcY.dotProduct hcU),
      avg_dotProduct_const hcY, (bordSol_rows ω d hinv).2]
    ring
  refine ⟨⟨hξd, hξp, hgd, hgp, hg0, hLd, hLp⟩, ⟨hb1, hb2, hb3⟩,
    ⟨?_, fun S hS => ⟨fun θ hθ => hX S hS θ hθ, fun G hG θ hθ => ?_⟩⟩, ?_, ?_⟩
  · -- (c): the size of `(ξ₀, ξ^ω)`
    have := norm_bordSol_le (ω := ω) d hr hr1 hHL hHT hHY hUb hσ
    simpa only [mul_assoc] using this
  · -- (c): `ξᴸ - ξᴸ₀ = 𝓡 gᴸ`
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (ofReal_mem_complexStrip hr1 0))
    obtain ⟨-, -, -, -, hL5, -, -⟩ := hvec2 (p := n) (bordGL ω d) G hgd hgp hG hg0
    rw [hrr] at hL5
    have h5 := (hL5 θ hθ).trans (Tools.cohConst_div_le_cR hγ hδ hG0)
    show ‖ξL0 + cohR ω (bordGL ω d) θ - ξL0‖ ≤ _
    rw [add_sub_cancel_left]
    exact h5
  · -- (d): uniqueness
    intro ξL' ξN' ξω' hLd' hLp' hNd' hNp' e1 e2 e3
    obtain ⟨hω, hN⟩ := border_unique hγ hτ hdio hr hδ h2δ d hηN hηNp hHN hηN0 hT hY hinv hLd' hLp'
      hNd' hNp' e1 e2 e3
    refine ⟨hω, hN, avg (fun θ => ξL' θ - bordXiL ω d ξL0 θ), fun θ hθ => ?_⟩
    have hd0 : ∀ θ ∈ complexStrip n (r - 2 * δ),
        fderiv ℂ (fun θ => ξL' θ - bordXiL ω d ξL0 θ) θ (fun l => (ω l : ℂ)) = 0 := by
      intro θ hθ
      have hopen := (isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ
      rw [fderiv_fun_sub (hLd'.differentiableAt hopen) (hLd.differentiableAt hopen)]
      simp only [_root_.sub_apply]
      rw [hLderiv θ hθ]
      have h1 := e1 θ hθ
      rw [hN θ hθ, hω] at h1
      have h' : fderiv ℂ ξL' θ (fun l => (ω l : ℂ)) = bordGL ω d θ := by
        simp only [bordGL]
        rw [← h1]
        abel
      rw [h', sub_self]
    exact eq_avg_of_fderiv_eq_zero hγ hτ hdio hr2 (u := fun θ => ξL' θ - bordXiL ω d ξL0 θ)
      (hLd'.sub hLd) (fun i z hz => by simp only [hLp' i z hz, hLp i z hz]) hd0 θ hθ
  · -- (e): realness
    intro hηLr hηNr hTr hYr hηωr hξL0
    have hUr : IsRealVec (triU ω d.ηN) := hU6 hηNr
    have hsol := bordSol_im_eq_zero ω d hcL hcT hcY hcU hηLr hTr hYr hUr hηωr
    have h0 : ∀ i, (bordXi0 ω d i).im = 0 := fun i => hsol (Sum.inl i)
    have hω0 : (bordXiOmega ω d).im = 0 := hsol (Sum.inr ())
    have hξr : IsRealVec (bordXiN ω d) := fun x i => by
      show ((bordXi0 ω d - triU ω d.ηN (fun j => (x j : ℂ))) i).im = 0
      rw [Pi.sub_apply, Complex.sub_im, h0 i, hUr x i, sub_zero]
    have hgr : IsRealVec (bordGL ω d) := fun x i => by
      show ((d.T (fun j => (x j : ℂ)) *ᵥ bordXiN ω d (fun j => (x j : ℂ)) +
        bordXiOmega ω d • (fun a => (ω a : ℂ)) - d.ηL (fun j => (x j : ℂ))) i).im = 0
      rw [Pi.sub_apply, Complex.sub_im, Pi.add_apply, Complex.add_im,
        Triangular.mulVec_im_eq_zero (hTr x) (hξr x) i, hηLr x i]
      simp [Complex.mul_im, hω0]
    have hLr : IsRealVec (bordXiL ω d ξL0) := fun x i => by
      show (ξL0 i + cohR ω (bordGL ω d) (fun j => (x j : ℂ)) i).im = 0
      have h6 : (cohR ω (bordGL ω d) (fun j => (x j : ℂ)) i).im = 0 := hL6 hgr x i
      rw [Complex.add_im, hξL0 i, h6, add_zero]
    exact ⟨h0, hω0, hξr, hgr, hLr⟩

end KAM.Iso.Linear

end
