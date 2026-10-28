/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import KAM.Nekhoroshev.Stability.Setting
public import KAM.ODE.Hamiltonian

/-!
# The energy argument (`bpN:p7:resonance-data`, `bpN:p7:energy-core`)

Orthogonal projections of `(ℝⁿ, ⬝ᵥ)` without `EuclideanSpace` (`IsOrthProj`, `exists_orthProj`),
the resonance data `resSpace`, `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound`, and the
reusable energy estimate `energy_core`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Stability

variable {n : ℕ}

/-- An orthogonal projection of `(ℝⁿ, ⟨·,·⟩)` (`dotProduct`), as a linear map. -/
structure IsOrthProj (P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Prop where
  idem : ∀ v, P (P v) = P v
  symm : ∀ u v, P u ⬝ᵥ v = u ⬝ᵥ P v

/-- The orthogonal projection onto any subspace exists (no `EuclideanSpace`: via the dot-product
bilinear form). -/
theorem exists_orthProj (V : Submodule ℝ (Fin n → ℝ)) :
    ∃ P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), IsOrthProj P ∧ (∀ v, P v ∈ V) ∧ ∀ v ∈ V, P v = v := by
  let B : LinearMap.BilinForm ℝ (Fin n → ℝ) := Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) ℝ)
  have hB : ∀ u v, B u v = u ⬝ᵥ v := fun u v => by
    simp [B, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := fun u v h => by
    rw [hB] at h ⊢
    rwa [dotProduct_comm]
  have hself : ∀ x : V, B (x : Fin n → ℝ) x = 0 → x = 0 := fun x h => by
    rw [hB] at h
    exact Subtype.ext (by simpa using h)
  have hnd : (B.restrict V).Nondegenerate :=
    ⟨fun x hx => hself x (by simpa using hx x), fun x hx => hself x (by simpa using hx x)⟩
  have hcompl := B.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  have hmem : ∀ v, V.projection _ hcompl v ∈ V := fun v => Submodule.projection_apply_mem hcompl v
  have hperp : ∀ u v, u ∈ V → v - V.projection _ hcompl v ∈ B.orthogonal V →
      u ⬝ᵥ (v - V.projection _ hcompl v) = 0 :=
    fun u v hu hw => by
      have := (LinearMap.BilinForm.mem_orthogonal_iff).1 hw u hu
      rwa [hB] at this
  have hid : ∀ v ∈ V, V.projection _ hcompl v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hcompl hv
  refine ⟨V.projection _ hcompl, ⟨fun v => hid _ (hmem v), fun u v => ?_⟩, hmem, hid⟩
  have h1 := hperp _ v (hmem u) (Submodule.sub_projection_mem hcompl v)
  have h2 := hperp _ u (hmem v) (Submodule.sub_projection_mem hcompl u)
  rw [dotProduct_sub] at h1 h2
  rw [dotProduct_comm (V.projection _ hcompl v) u] at h2
  rw [dotProduct_comm (V.projection _ hcompl v) (V.projection _ hcompl u)] at h2
  linarith

/-- Linear functionals on `ℝⁿ` are the dot product with their values on the basis. -/
theorem clm_eq_dot (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = (fun i => L (Pi.single i 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [dotProduct, smul_eq_mul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

private theorem taylor_segment {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    (hhR : ContDiffOn ℝ 2 hR U) {x Δ : Fin n → ℝ} (hseg : ∀ a ∈ Icc (0 : ℝ) 1, x + a • Δ ∈ U) :
    ∃ a ∈ Ioo (0 : ℝ) 1, hR (x + Δ) - hR x - fderiv ℝ hR x Δ =
      1 / 2 * hessR hR (x + a • Δ) Δ Δ := by
  set φ : ℝ → ℝ := fun a => hR (x + a • Δ) with hφ
  have hp : ∀ a : ℝ, HasDerivAt (fun a : ℝ => x + a • Δ) Δ a := fun a => by
    simpa using ((hasDerivAt_id a).smul_const Δ).const_add x
  have hat : ∀ a : ℝ, x + a • Δ ∈ U → ContDiffAt ℝ 2 hR (x + a • Δ) := fun a ha =>
    hhR.contDiffAt (hU.mem_nhds ha)
  have hd1 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt φ (fderiv ℝ hR (x + a • Δ) Δ) a := fun a ha =>
    ((hat a ha).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a (hp a)
  have hd2 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (hessR hR (x + a • Δ) Δ Δ) a := fun a ha => by
    have h1 : DifferentiableAt ℝ (fderiv ℝ hR) (x + a • Δ) :=
      ((hat a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h2 := h1.hasFDerivAt.comp_hasDerivAt a (hp a)
    exact (ContinuousLinearMap.apply ℝ ℝ Δ).hasFDerivAt.comp_hasDerivAt a h2
  have hS : IsOpen {a : ℝ | x + a • Δ ∈ U} :=
    hU.preimage (by fun_prop)
  have hderiv : ∀ a ∈ {a : ℝ | x + a • Δ ∈ U}, deriv φ a = fderiv ℝ hR (x + a • Δ) Δ :=
    fun a ha => (hd1 a ha).deriv
  have hcd : ∀ a ∈ uIcc (0 : ℝ) 1, ContDiffAt ℝ 2 φ a := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    exact (hat a (hseg a ha')).comp a (by fun_prop : ContDiffAt ℝ 2 (fun a : ℝ => x + a • Δ) a)
  have hcdOn : ContDiffOn ℝ 2 φ (uIcc 0 1) := fun a ha => (hcd a ha).contDiffWithinAt
  have hud : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact uniqueDiffOn_Icc zero_lt_one
  have hit1 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 1 φ (uIcc 0 1) a = deriv φ a := fun a ha => by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud ((hcd a ha).of_le (by norm_num)) ha,
      iteratedDeriv_one]
  have hit2 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 2 φ (uIcc 0 1) a =
      hessR hR (x + a • Δ) Δ Δ := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hcd a ha) ha, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hev : deriv φ =ᶠ[nhds a] fun a => fderiv ℝ hR (x + a • Δ) Δ :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds (hseg a ha')) hderiv
    rw [hev.deriv_eq]
    exact (hd2 a (hseg a ha')).deriv
  have hIoo : ∀ a ∈ uIoo (0 : ℝ) 1, a ∈ uIcc (0 : ℝ) 1 := fun a ha => by
    rw [uIoo_of_le zero_le_one] at ha
    rw [uIcc_of_le zero_le_one]
    exact Ioo_subset_Icc_self ha
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 1 φ (uIcc 0 1)) (uIoo 0 1) := by
    have h0 : ∀ a ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ) a :=
      fun a ha => (hd2 a (hseg a (by simpa [uIcc_of_le zero_le_one] using ha))).differentiableAt
    refine DifferentiableOn.congr (f := fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (fun a ha => (h0 a (hIoo a ha)).differentiableWithinAt) fun a ha => ?_
    rw [hit1 a (hIoo a ha)]
    exact hderiv a (hseg a (by simpa [uIcc_of_le zero_le_one] using hIoo a ha))
  obtain ⟨a, ha, h⟩ := taylor_mean_remainder_lagrange (n := 1) (x₀ := 0) (x := 1) zero_ne_one
    (hcdOn.of_le (by norm_num)) hdiff
  have ha' : a ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_le zero_le_one] using ha
  refine ⟨a, ha', ?_⟩
  rw [hit2 a (hIoo a ha), taylorWithinEval_succ, taylor_within_zero_eval,
    hit1 0 (by simp), hderiv 0 (by simpa using hseg 0 (by simp))] at h
  simp only [hφ, zero_smul, add_zero, one_smul] at h
  simp at h
  linarith

end KAM.Stability

end
