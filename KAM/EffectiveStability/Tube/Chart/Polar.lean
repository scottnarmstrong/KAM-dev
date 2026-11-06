/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Bracket
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The polar chart (T2-CONF, N2-Chart, targets (B) and (C))

Per mode, `(I_j, θ_j) ↦ (q_j, p_j) = (-√(2 I_j) sin θ_j, √(2 I_j) cos θ_j)`, i.e.
`(p_j - i q_j)/√2 = √I_j e^{iθ_j}`, on `actionPos = {y | ∀ j, 0 < y.1 j}`. With the actions
`I = y.1` as positions and the angles `θ = y.2` as momenta the map is symplectic.

* `contDiffOn_polar`: `polar` is `C^∞` on the open set `actionPos`.
* `fderiv_polar_apply`: the derivative in closed form (`polarD`).
* `symplecticForm_fderiv_polar`: symplecticity of `fderiv ℝ polar y`, `y ∈ actionPos`.
* `fderiv_apply_hamiltonianVectorField_polar` (target (B)):
  `fderiv ℝ G (polar y) (X_H (polar y)) = fderiv ℝ (G ∘ polar) y (X_{H ∘ polar} y)`, and
  `fderiv_apply_hamiltonianVectorField_polar_eq_bracketSum`: this equals
  `Σ_j (∂_{I_j}(G∘polar) · ∂_{θ_j}(H∘polar) - ∂_{θ_j}(G∘polar) · ∂_{I_j}(H∘polar))` at `y`.
* `polar_polarInv`, `exists_polar_eq` (target (C)): every `x` with `x.1 j ^ 2 + x.2 j ^ 2 > 0` for
  all `j` is `polar (polarInv x)`, `polarInv x = ((q² + p²)/2, arg (p - i q))`.
* `polarInv_polar`: `polarInv (polar y)` has the actions of `y` and its angles modulo `2π`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open KAM Real Filter Topology
open scoped ContDiff

variable {n : ℕ}

/-- The polar chart `(I, θ) ↦ (q, p)`, `q_j = -√(2 I_j) sin θ_j`, `p_j = √(2 I_j) cos θ_j`. -/
def polar (y : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => -√(2 * y.1 j) * sin (y.2 j), fun j => √(2 * y.1 j) * cos (y.2 j))

/-- The domain `{y | ∀ j, 0 < y.1 j}` of the polar chart (all actions positive). -/
def actionPos (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {y | ∀ j, 0 < y.1 j}

theorem isOpen_actionPos : IsOpen (actionPos n) := by
  have : actionPos n = ⋂ j : Fin n, {y : (Fin n → ℝ) × (Fin n → ℝ) | 0 < y.1 j} := by
    ext y
    simp [actionPos]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_fst)

/-- The closed-form derivative of `polar` at `y` applied to `v`. -/
def polarD (y v : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => -(v.1 j / √(2 * y.1 j)) * sin (y.2 j) - √(2 * y.1 j) * cos (y.2 j) * v.2 j,
    fun j => v.1 j / √(2 * y.1 j) * cos (y.2 j) - √(2 * y.1 j) * sin (y.2 j) * v.2 j)

theorem contDiffAt_polar {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k polar y := by
  have hI : ∀ j, ContDiffAt ℝ k (fun y : (Fin n → ℝ) × (Fin n → ℝ) => √(2 * y.1 j)) y := fun j =>
    (contDiffAt_const.mul ((by fun_prop :
      ContDiff ℝ k (fun y : (Fin n → ℝ) × (Fin n → ℝ) => y.1 j))).contDiffAt).sqrt
      (by have := hy j; positivity)
  have hθ : ∀ j, ContDiff ℝ k (fun y : (Fin n → ℝ) × (Fin n → ℝ) => y.2 j) := fun j => by
    fun_prop
  refine ContDiffAt.prodMk ?_ ?_
  · exact contDiffAt_pi.2 fun j => (hI j).neg.mul (Real.contDiff_sin.comp (hθ j)).contDiffAt
  · exact contDiffAt_pi.2 fun j => (hI j).mul (Real.contDiff_cos.comp (hθ j)).contDiffAt

/-- **Target (C), smoothness.** `polar` is `C^∞` on `actionPos`. -/
theorem contDiffOn_polar : ContDiffOn ℝ ∞ (polar (n := n)) (actionPos n) :=
  fun _ hy => (contDiffAt_polar hy).contDiffWithinAt

theorem differentiableAt_polar {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) :
    DifferentiableAt ℝ polar y :=
  (contDiffAt_polar (k := 1) hy).differentiableAt one_ne_zero

/-- The derivative of `polar` in closed form. -/
theorem fderiv_polar_apply {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n)
    (v : (Fin n → ℝ) × (Fin n → ℝ)) : fderiv ℝ polar y v = polarD y v := by
  have hline : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h1 : HasDerivAt (fun t : ℝ => polar (y + t • v)) (fderiv ℝ polar y v) 0 :=
    (differentiableAt_polar hy).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have h2 : HasDerivAt (fun t : ℝ => polar (y + t • v)) (polarD y v) 0 := by
    have hs : ∀ j, HasDerivAt (fun t : ℝ => √(2 * (y + t • v).1 j)) (v.1 j / √(2 * y.1 j)) 0 := by
      intro j
      have hpos : 0 < 2 * y.1 j := by have := hy j; positivity
      have hlin : HasDerivAt (fun t : ℝ => 2 * (y + t • v).1 j) (2 * v.1 j) 0 := by
        have := (((hasDerivAt_id (0 : ℝ)).mul_const (v.1 j)).const_add (y.1 j)).const_mul 2
        simpa using this
      have := hlin.sqrt (by simpa using hpos.ne')
      convert this using 1
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
        add_zero]
      field_simp
    have ha : ∀ j, HasDerivAt (fun t : ℝ => (y + t • v).2 j) (v.2 j) 0 := by
      intro j
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 j)).const_add (y.2 j)
      simpa using this
    refine HasDerivAt.prodMk ?_ ?_
    · refine hasDerivAt_pi.2 fun j => ?_
      have := ((hs j).neg).mul ((ha j).sin)
      convert this using 1
      simp
      ring
    · refine hasDerivAt_pi.2 fun j => ?_
      have := (hs j).mul ((ha j).cos)
      convert this using 1
      simp
      ring
  exact h1.unique h2

/-- **Symplecticity of the polar chart.** -/
theorem symplecticForm_polarD {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    symplecticForm (polarD y u) (polarD y v) = symplecticForm u v := by
  simp only [symplecticForm, polarD]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : 0 < √(2 * y.1 j) := Real.sqrt_pos.2 (by have := hy j; positivity)
  have hsc := sin_sq_add_cos_sq (y.2 j)
  field_simp
  linear_combination (√(2 * y.1 j)) ^ 2 * (u.2 j * v.1 j - u.1 j * v.2 j) * hsc

theorem symplecticForm_fderiv_polar {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n)
    (u v : (Fin n → ℝ) × (Fin n → ℝ)) :
    symplecticForm (fderiv ℝ polar y u) (fderiv ℝ polar y v) = symplecticForm u v := by
  rw [fderiv_polar_apply hy, fderiv_polar_apply hy, symplecticForm_polarD hy]

/-- **Target (B): polar transport.** For `y ∈ actionPos` and `G`, `H` differentiable at `polar y`:
`fderiv ℝ G (polar y) (X_H (polar y)) = fderiv ℝ (G ∘ polar) y (X_{H ∘ polar} y)`. -/
theorem fderiv_apply_hamiltonianVectorField_polar {G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) (hG : DifferentiableAt ℝ G (polar y))
    (hH : DifferentiableAt ℝ H (polar y)) :
    fderiv ℝ G (polar y) (hamiltonianVectorField H (polar y)) =
      fderiv ℝ (G ∘ polar) y (hamiltonianVectorField (H ∘ polar) y) :=
  fderiv_apply_hamiltonianVectorField_comp_symplectic (differentiableAt_polar hy)
    (symplecticForm_fderiv_polar hy) hG hH

/-- **Target (B), coordinate form.** With the actions `I = y.1` as positions and the angles
`θ = y.2` as momenta:
`fderiv ℝ G (polar y) (X_H (polar y))
  = Σ_j (∂_{I_j}(G∘polar) y · ∂_{θ_j}(H∘polar) y - ∂_{θ_j}(G∘polar) y · ∂_{I_j}(H∘polar) y)`. -/
theorem fderiv_apply_hamiltonianVectorField_polar_eq_bracketSum
    {G H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n)
    (hG : DifferentiableAt ℝ G (polar y)) (hH : DifferentiableAt ℝ H (polar y)) :
    fderiv ℝ G (polar y) (hamiltonianVectorField H (polar y)) =
      ∑ j, (fderiv ℝ (G ∘ polar) y (Pi.single j 1, 0) * fderiv ℝ (H ∘ polar) y (0, Pi.single j 1) -
        fderiv ℝ (G ∘ polar) y (0, Pi.single j 1) * fderiv ℝ (H ∘ polar) y (Pi.single j 1, 0)) := by
  rw [fderiv_apply_hamiltonianVectorField_polar hy hG hH,
    fderiv_apply_hamiltonianVectorField_eq_bracketSum]
  rfl

/-- The mode energy of the polar image: `q_j ^ 2 + p_j ^ 2 = 2 I_j` (for `I_j ≥ 0`). -/
theorem polar_sq_add_sq {y : (Fin n → ℝ) × (Fin n → ℝ)} {j : Fin n} (hj : 0 ≤ y.1 j) :
    (polar y).1 j ^ 2 + (polar y).2 j ^ 2 = 2 * y.1 j := by
  have hsq : √(2 * y.1 j) ^ 2 = 2 * y.1 j := Real.sq_sqrt (by positivity)
  simp only [polar]
  linear_combination (2 * y.1 j) * sin_sq_add_cos_sq (y.2 j) +
    (sin (y.2 j) ^ 2 + cos (y.2 j) ^ 2) * hsq

/-- The inverse of the polar chart on the punctured modes:
`I_j = (q_j² + p_j²)/2`, `θ_j = arg (p_j - i q_j)`. -/
def polarInv (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2, fun j => Complex.arg ⟨x.2 j, -x.1 j⟩)

theorem polarInv_mem_actionPos {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : ∀ j, 0 < x.1 j ^ 2 + x.2 j ^ 2) : polarInv x ∈ actionPos n := fun j => by
  simp only [polarInv]
  have := hx j
  positivity

/-- **Target (C), coverage.** `polar ∘ polarInv = id` (everywhere; `polarInv x ∈ actionPos` needs
all modes nonzero). -/
theorem polar_polarInv (x : (Fin n → ℝ) × (Fin n → ℝ)) : polar (polarInv x) = x := by
  have hr : ∀ j, √(2 * ((x.1 j ^ 2 + x.2 j ^ 2) / 2)) = ‖(⟨x.2 j, -x.1 j⟩ : ℂ)‖ := fun j => by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  ext j
  · simp only [polar, polarInv]
    rw [hr, neg_mul, Complex.norm_mul_sin_arg]
    simp
  · simp only [polar, polarInv]
    rw [hr, Complex.norm_mul_cos_arg]

/-- `polarInv ∘ polar` keeps the actions and moves each angle by a multiple of `2π`. -/
theorem polarInv_polar {y : (Fin n → ℝ) × (Fin n → ℝ)} (hy : y ∈ actionPos n) :
    (polarInv (polar y)).1 = y.1 ∧ ∀ j, ∃ k : ℤ, (polarInv (polar y)).2 j = y.2 j + 2 * π * k := by
  refine ⟨funext fun j => ?_, fun j => ?_⟩
  · have h := polar_sq_add_sq (y := y) (j := j) (hy j).le
    simp only [polarInv]
    rw [h]
    ring
  · have hs : 0 < √(2 * y.1 j) := Real.sqrt_pos.2 (by have := hy j; positivity)
    have hz : (⟨(polar y).2 j, -(polar y).1 j⟩ : ℂ) =
        (√(2 * y.1 j) : ℂ) * (Complex.cos (y.2 j) + Complex.sin (y.2 j) * Complex.I) := by
      apply Complex.ext <;> simp [polar, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    refine ⟨⌊(π - y.2 j) / (2 * π)⌋, ?_⟩
    have := Complex.arg_mul_cos_add_sin_mul_I_sub hs (y.2 j)
    simp only [polarInv]
    rw [hz]
    linarith

/-- **Target (C), coverage.** Every point with all modes nonzero is in the image of
`actionPos` under `polar`. -/
theorem exists_polar_eq {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ j, 0 < x.1 j ^ 2 + x.2 j ^ 2) :
    ∃ y ∈ actionPos n, polar y = x :=
  ⟨polarInv x, polarInv_mem_actionPos hx, polar_polarInv x⟩

end KAM.EffectiveStability.Tube

end
