/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.HTilde

/-!
# Bounds for the tube Hamiltonian (T2-CONF, N5a)

* `differentiable_Tn`, `abs_Tn_le`, `abs_pderiv_Tn_le`: `T_n` is differentiable, with
  `|T_n| ≤ Σ |coef|` and `|∂_a T_n| ≤ Σ |coef| |k_a|` over its rows (the ℓ¹ bounds).
* `differentiableAt_hTildeOf`, `differentiable_hCoef`: regularity where `B + u > 0`, `B > 0`.
* `hRem_tube`: the `C¹` bounds of the Taylor remainder `R` on the box `|u_j| ≤ r`, from N4's
  `binomProd_tube`, given bounds `τ_n ≥ |T_n|`, `τ'_n ≥ |∂_a T_n|` and the box data of `B`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

variable (E N : ℕ)

/-- The linear phase `k·φ` and its derivative. -/
def modeCLM (e : (Mon × Mon) × ℤ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ((rowMode e).1 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ((rowMode e).2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem hasFDerivAt_rowTrig (e : (Mon × Mon) × ℤ) (φ : Fin 2 → ℝ) :
    HasFDerivAt (rowTrig E N e) (rowCoef E N e •
      (-Real.sin ((rowMode e).1 * φ 0 + (rowMode e).2 * φ 1) • modeCLM e)) φ := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) φ).const_mul ((rowMode e).1 : ℝ)
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) φ).const_mul ((rowMode e).2 : ℝ)
  exact ((h0.add h1).cos).const_mul (rowCoef E N e)

theorem differentiable_rowTrig (e : (Mon × Mon) × ℤ) : Differentiable ℝ (rowTrig E N e) :=
  fun φ => (hasFDerivAt_rowTrig E N e φ).differentiableAt

theorem abs_pderiv_rowTrig_le (e : (Mon × Mon) × ℤ) (φ : Fin 2 → ℝ) (a : Fin 2) :
    |fderiv ℝ (rowTrig E N e) φ (Pi.single a 1)| ≤
      |rowCoef E N e| * |(![((rowMode e).1 : ℝ), (rowMode e).2] a)| := by
  rw [(hasFDerivAt_rowTrig E N e φ).fderiv]
  have hs := Real.abs_sin_le_one ((rowMode e).1 * φ 0 + (rowMode e).2 * φ 1)
  have hk : modeCLM e (Pi.single a 1) = ![((rowMode e).1 : ℝ), (rowMode e).2] a := by
    fin_cases a <;> simp [modeCLM]
  simp only [smul_apply, smul_eq_mul, hk, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) hs) (abs_nonneg _)

/-- The ℓ¹ list bounds of a sum of rows. -/
private theorem list_bounds (l : List ((Mon × Mon) × ℤ)) (φ : Fin 2 → ℝ) (a : Fin 2) :
    DifferentiableAt ℝ (fun φ => (l.map fun e => rowTrig E N e φ).sum) φ ∧
      |(l.map fun e => rowTrig E N e φ).sum| ≤ (l.map fun e => |rowCoef E N e|).sum ∧
      |fderiv ℝ (fun φ => (l.map fun e => rowTrig E N e φ).sum) φ (Pi.single a 1)| ≤
        (l.map fun e => |rowCoef E N e| * |(![((rowMode e).1 : ℝ), (rowMode e).2] a)|).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨hd, h0, h1⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    have he := (differentiable_rowTrig E N e) φ
    refine ⟨he.add hd, ?_, ?_⟩
    · have : |rowTrig E N e φ| ≤ |rowCoef E N e| := by
        rw [rowTrig, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      exact (abs_add_le _ _).trans (add_le_add this h0)
    · rw [fderiv_fun_add he hd, add_apply]
      exact (abs_add_le _ _).trans (add_le_add (abs_pderiv_rowTrig_le E N e φ a) h1)

theorem differentiable_Tn (rows : List ((Mon × Mon) × ℤ)) (n : Fin 3 → ℕ) :
    Differentiable ℝ (Tn E N rows n) :=
  fun φ => (list_bounds E N _ φ 0).1

/-- `|T_n(φ)| ≤ Σ |coef|` over the rows of exponent `n`. -/
theorem abs_Tn_le (rows : List ((Mon × Mon) × ℤ)) (n : Fin 3 → ℕ) (φ : Fin 2 → ℝ) :
    |Tn E N rows n φ| ≤
      ((rows.filter fun e => decide (rowExp e = n)).map fun e => |rowCoef E N e|).sum :=
  (list_bounds E N _ φ 0).2.1

/-- `|∂_a T_n(φ)| ≤ Σ |coef| |k_a|` over the rows of exponent `n`. -/
theorem abs_pderiv_Tn_le (rows : List ((Mon × Mon) × ℤ)) (n : Fin 3 → ℕ) (φ : Fin 2 → ℝ)
    (a : Fin 2) :
    |fderiv ℝ (Tn E N rows n) φ (Pi.single a 1)| ≤
      ((rows.filter fun e => decide (rowExp e = n)).map fun e =>
        |rowCoef E N e| * |(![((rowMode e).1 : ℝ), (rowMode e).2] a)|).sum :=
  (list_bounds E N _ φ a).2.2

/-- **The `C¹` bounds of the Taylor remainder** on the box `|u_j| ≤ r`, given the box data of `B`
(as in N4's `binomProd_tube`) and bounds `τ_n ≥ |T_n|`, `τ'_n ≥ |∂_a T_n|`. -/
theorem hRem_tube (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (L : ℕ)
    {bmin bmax β : Fin 3 → ℝ} {r : ℝ} {τ τ' : (Fin 3 → ℕ) → ℝ}
    (hBd : ∀ j, Differentiable ℝ fun φ => B φ j) (hr : ∀ j, r < bmin j)
    (h1 : ∀ j φ, bmin j ≤ B φ j) (h2 : ∀ j φ, B φ j ≤ bmax j)
    (hβ : ∀ j φ a, |fderiv ℝ (fun φ => B φ j) φ (Pi.single a 1)| ≤ β j)
    (hτ : ∀ n φ, |Tn E N rows n φ| ≤ τ n)
    (hτ' : ∀ n φ a, |fderiv ℝ (Tn E N rows n) φ (Pi.single a 1)| ≤ τ' n)
    (φ : Fin 2 → ℝ) (u : Fin 3 → ℝ) (hu : ∀ j, |u j| ≤ r) :
    |hRem E N rows B L (u, φ)| ≤
        ∑ n ∈ expSet rows, τ n * remBound₀ (halfExp n) L bmin bmax r ∧
      DifferentiableAt ℝ (fun v => hRem E N rows B L (v, φ)) u ∧
      (∀ i, |fderiv ℝ (fun v => hRem E N rows B L (v, φ)) u (Pi.single i 1)| ≤
        ∑ n ∈ expSet rows, τ n * remBoundU (halfExp n) L bmin bmax r i) ∧
      DifferentiableAt ℝ (fun φ => hRem E N rows B L (u, φ)) φ ∧
      (∀ a, |fderiv ℝ (fun φ => hRem E N rows B L (u, φ)) φ (Pi.single a 1)| ≤
        ∑ n ∈ expSet rows, (τ' n * remBound₀ (halfExp n) L bmin bmax r +
          τ n * remBoundPhi (halfExp n) L bmin bmax r β)) := by
  have T := fun n => binomProd_tube (halfExp n) L (fun j φ => B φ j) hBd hr h1 h2 hβ φ u hu
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => (abs_nonneg _).trans (hτ n φ)
  have hTd := differentiable_Tn E N rows
  have hD : ∀ n, DifferentiableAt ℝ
      (fun φ => Tn E N rows n φ * binomProdRem (halfExp n) L (B φ) u) φ :=
    fun n => (hTd n φ).mul (T n).2.2.2.2.1
  simp only [hRem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hτ n φ) (T n).2.1 (abs_nonneg _) (hτ0 n)
  · exact DifferentiableAt.fun_sum fun n _ => ((T n).2.2.1).const_mul _
  · intro i
    rw [fderiv_fun_sum fun n _ => ((T n).2.2.1).const_mul _, FunLike.coe_sum, Finset.sum_apply]
    refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [fderiv_const_mul (T n).2.2.1, smul_apply, smul_eq_mul,
      abs_mul]
    exact mul_le_mul (hτ n φ) ((T n).2.2.2.1 i) (abs_nonneg _) (hτ0 n)
  · exact DifferentiableAt.fun_sum fun n _ => hD n
  · intro a
    rw [fderiv_fun_sum fun n _ => hD n, FunLike.coe_sum, Finset.sum_apply]
    refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [fderiv_fun_mul (hTd n φ) (T n).2.2.2.2.1, add_apply, smul_apply, smul_apply,
      smul_eq_mul, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, add_comm]
    refine add_le_add ?_ ?_
    · rw [mul_comm]
      exact mul_le_mul (hτ' n φ a) (T n).2.1 (abs_nonneg _) ((abs_nonneg _).trans (hτ' n φ a))
    · exact mul_le_mul (hτ n φ) ((T n).2.2.2.2.2 a) (abs_nonneg _) (hτ0 n)

/-! ### Differentiability -/

/-- `h̃` is differentiable at `(u, φ)` when `B` is differentiable at `φ` and `B_j(φ) + u_j > 0`. -/
theorem differentiableAt_hTildeOf (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ)
    {p : (Fin 3 → ℝ) × (Fin 2 → ℝ)} (hB : DifferentiableAt ℝ B p.2)
    (hpos : ∀ j, 0 < B p.2 j + p.1 j) :
    DifferentiableAt ℝ (hTildeOf E N rows B) p := by
  have hfac : ∀ (s : ℝ) (j : Fin 3),
      DifferentiableAt ℝ (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => (B q.2 j + q.1 j) ^ s) p := by
    intro s j
    have hBs : DifferentiableAt ℝ (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => B q.2) p :=
      hB.comp p differentiableAt_snd
    have hBj : DifferentiableAt ℝ (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => B q.2 j) p :=
      differentiableAt_pi.1 hBs j
    have hu : DifferentiableAt ℝ (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => q.1 j) p :=
      differentiableAt_pi.1 differentiableAt_fst j
    exact (hBj.add hu).rpow_const (Or.inl (hpos j).ne')
  unfold hTildeOf
  refine DifferentiableAt.fun_sum fun n _ => ?_
  have hT : DifferentiableAt ℝ (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => Tn E N rows n q.2) p :=
    (differentiable_Tn E N rows n p.2).comp p differentiableAt_snd
  simp only [binomProd, Fin.prod_univ_three]
  exact hT.mul (((hfac _ 0).mul (hfac _ 1)).mul (hfac _ 2))

/-- The Taylor coefficients `h_m` are differentiable when `B` is differentiable and positive. -/
theorem differentiable_hCoef (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ)
    (hB : Differentiable ℝ B) (hpos : ∀ φ j, 0 < B φ j) (m : Fin 3 → ℕ) :
    Differentiable ℝ (hCoef E N rows B m) := by
  intro φ
  have hfac : ∀ (s : ℝ) (j : Fin 3), DifferentiableAt ℝ (fun φ => B φ j ^ s) φ := fun s j =>
    (differentiableAt_pi.1 (hB φ) j).rpow_const (Or.inl (hpos φ j).ne')
  unfold hCoef
  refine DifferentiableAt.fun_sum fun n _ => ?_
  simp only [Fin.prod_univ_three]
  exact (differentiable_Tn E N rows n φ).mul
    ((((hfac _ 0).const_mul _).mul ((hfac _ 1).const_mul _)).mul ((hfac _ 2).const_mul _))

end KAM.EffectiveStability.Tube

end
