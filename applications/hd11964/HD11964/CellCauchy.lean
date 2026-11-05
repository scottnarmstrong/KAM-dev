/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Cover

/-!
# HD 11964: the Cauchy bound for the slow-variable derivatives (HD11964-LEMMAS, piece 1)

The cell check bounds the bracket terms, which need the slow-variable derivatives of functions
known only through models: a polynomial in the cell variables `u` plus a remainder bounded on a
polydisc. The derivative of the polynomial is exact; the derivative of the remainder needs a
Cauchy estimate.

* `polyDiscC d s`: the closed polydisc `{u | ∀ j, ‖u j‖ ≤ s}` (kamx-hd-layer's `PackedTF.polyDisc`).
* `norm_fderiv_single_le_of_polyDisc` (1a): a function complex differentiable on the polydisc of
  radius `s₀` and bounded there by `r` has `‖∂_j g‖ ≤ r / (s₀ - s)` on radius `s < s₀`.
* `norm_fderiv_sub_le_of_model` (1b): applied to a model's remainder `f - p`.
* `AffineCell.coord`, `AffineCell.invMx`: the cell variables of a real point and `∂u_j/∂x_i`;
  `coord_map`, `map_coord`: `coord` and `map` are inverse on a well-formed cell.
  `norm_fderiv_comp_coord_le` (1c): the physical slow derivatives (`∂/∂Λ_i`, `∂/∂ξ_i`, `∂/∂η_i`)
  of `x ↦ g (u(x))` are bounded by `Σ_j |∂u_j/∂x_i| B_j` from bounds `B_j` on the cell-variable
  partials.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology KAM KAM.Planetary KAM.Application.LambdaDrift

namespace HD11964.Cover

/-- The closed polydisc `{u | ∀ j, ‖u j‖ ≤ s}` (kamx-hd-layer's `PackedTF.polyDisc`). -/
def polyDiscC (d : ℕ) (s : ℝ) : Set (Fin d → ℂ) := {u | ∀ j, ‖u j‖ ≤ s}

/-- **Cauchy bound for a coordinate derivative on the polydisc** (1a). -/
theorem norm_fderiv_single_le_of_polyDisc {d : ℕ} {g : (Fin d → ℂ) → ℂ} {s₀ s r : ℝ}
    (hg : DifferentiableOn ℂ g (polyDiscC d s₀)) (hr : ∀ u ∈ polyDiscC d s₀, ‖g u‖ ≤ r)
    (hs : s < s₀) {u : Fin d → ℂ} (hu : u ∈ polyDiscC d s) (j : Fin d) :
    ‖fderiv ℂ g u (Pi.single j 1)‖ ≤ r / (s₀ - s) := by
  have hR0 : 0 < s₀ - s := by linarith
  -- the slice through `u` along coordinate `j` stays in the polydisc of radius `s₀`
  have hcoord : ∀ z : ℂ, ‖z - u j‖ ≤ s₀ - s → ‖z‖ ≤ s₀ := fun z hz => by
    have := norm_le_insert' z (u j)
    linarith [hu j]
  have hmapC : ∀ z ∈ closedBall (u j) (s₀ - s), Function.update u j z ∈ polyDiscC d s₀ := by
    intro z hz i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact hcoord z (by rwa [mem_closedBall, dist_eq_norm] at hz)
    · rw [Function.update_of_ne hij]
      exact (hu i).trans hs.le
  -- the open polydisc is a neighbourhood of every slice point of the open ball
  have hopen : IsOpen {v : Fin d → ℂ | ∀ i, ‖v i‖ < s₀} := by
    have e : {v : Fin d → ℂ | ∀ i, ‖v i‖ < s₀} = ⋂ i, {v : Fin d → ℂ | ‖v i‖ < s₀} := by
      ext v; simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const
  have hnhds : ∀ z ∈ ball (u j) (s₀ - s), polyDiscC d s₀ ∈ 𝓝 (Function.update u j z) := by
    intro z hz
    refine Filter.mem_of_superset (hopen.mem_nhds fun i => ?_) fun v hv i => (hv i).le
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      rw [mem_ball, dist_eq_norm] at hz
      have := norm_le_insert' z (u i)
      linarith [hu i]
    · rw [Function.update_of_ne hij]
      exact lt_of_le_of_lt (hu i) hs
  have hd : DiffContOnCl ℂ (fun z => g (Function.update u j z)) (ball (u j) (s₀ - s)) := by
    refine ⟨fun z hz => ?_, ?_⟩
    · exact ((hg.differentiableAt (hnhds z hz)).comp z
        (hasDerivAt_update u j z).differentiableAt).differentiableWithinAt
    · rw [closure_ball (u j) hR0.ne']
      have hc : Continuous fun z : ℂ => Function.update u j z :=
        (continuous_const (y := u)).update j continuous_id
      exact hg.continuousOn.comp hc.continuousOn fun z hz => hmapC z hz
  have hC : ∀ z ∈ sphere (u j) (s₀ - s), ‖g (Function.update u j z)‖ ≤ r :=
    fun z hz => hr _ (hmapC z (sphere_subset_closedBall hz))
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hd hC
  have hu0 : polyDiscC d s₀ ∈ 𝓝 u := by
    simpa [Function.update_eq_self] using hnhds (u j) (mem_ball_self hR0)
  have hgu := (hg.differentiableAt hu0).hasFDerivAt
  have hcomp : HasDerivAt (fun z => g (Function.update u j z)) (fderiv ℂ g u (Pi.single j 1))
      (u j) := by
    have h1 := hasDerivAt_update u j (u j)
    exact hgu.comp_hasDerivAt_of_eq (u j) h1 (Function.update_eq_self j u).symm
  rw [← hcomp.deriv]
  exact hcau

/-- **The model form** (1b): if `f` and the model `p` are complex differentiable on the polydisc
of radius `s₀` and `‖f - p‖ ≤ r` there, their partial derivatives differ by at most `r / (s₀ - s)`
on radius `s` (the derivative of a model's remainder). -/
theorem norm_fderiv_sub_le_of_model {d : ℕ} {f p : (Fin d → ℂ) → ℂ} {s₀ s r : ℝ}
    (hf : DifferentiableOn ℂ f (polyDiscC d s₀)) (hp : DifferentiableOn ℂ p (polyDiscC d s₀))
    (hr : ∀ u ∈ polyDiscC d s₀, ‖f u - p u‖ ≤ r) (hs : s < s₀) {u : Fin d → ℂ}
    (hu : u ∈ polyDiscC d s) (j : Fin d) :
    ‖fderiv ℂ f u (Pi.single j 1) - fderiv ℂ p u (Pi.single j 1)‖ ≤ r / (s₀ - s) := by
  have hopen : IsOpen {v : Fin d → ℂ | ∀ i, ‖v i‖ < s₀} := by
    have e : {v : Fin d → ℂ | ∀ i, ‖v i‖ < s₀} = ⋂ i, {v : Fin d → ℂ | ‖v i‖ < s₀} := by
      ext v; simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const
  have hu0 : polyDiscC d s₀ ∈ 𝓝 u :=
    Filter.mem_of_superset (hopen.mem_nhds fun i => lt_of_le_of_lt (hu i) hs)
      fun v hv i => (hv i).le
  have h := norm_fderiv_single_le_of_polyDisc (hf.sub hp) (fun v hv => hr v hv) hs hu j
  rw [fderiv_sub (hf.differentiableAt hu0) (hp.differentiableAt hu0)] at h
  simpa using h

/-- The cell variables of a real point `x` (the inverse of `AffineCell.map` for a well-formed
cell). -/
def AffineCell.coord (k : AffineCell) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(x 0 - k.c 0) / k.h 0, (x 1 - k.c 1) / k.h 1, (x 2 - k.c 2) / k.h 2,
    (x 3 - k.c 3) / k.h 3, (k.a * (x 4 - k.c 4) + k.b * (x 5 - k.c 5)) / k.h 4,
    (-k.b * (x 4 - k.c 4) + k.a * (x 5 - k.c 5)) / k.h 5]

/-- `∂u_j/∂x_i`, the inverse cell matrix (row `j`, column `i`). -/
def AffineCell.invMx (k : AffineCell) : Fin 6 → Fin 6 → ℚ :=
  ![![1 / k.h 0, 0, 0, 0, 0, 0], ![0, 1 / k.h 1, 0, 0, 0, 0], ![0, 0, 1 / k.h 2, 0, 0, 0],
    ![0, 0, 0, 1 / k.h 3, 0, 0], ![0, 0, 0, 0, k.a / k.h 4, k.b / k.h 4],
    ![0, 0, 0, 0, -k.b / k.h 5, k.a / k.h 5]]

/-- `coord` inverts `map` on a well-formed cell (AUDIT-HD11964-LEMMAS-1, L4; the auditor's
probe). -/
theorem AffineCell.coord_map (k : AffineCell) (hk : k.wf = true) (u : Fin 6 → ℝ) :
    k.coord (k.map u) = u := by
  simp only [AffineCell.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hpos, hrot⟩ := hk
  have hp : ∀ j, (k.h j : ℝ) ≠ 0 := fun j =>
    (show (0 : ℝ) < k.h j by exact_mod_cast hpos j (List.mem_finRange j)).ne'
  have hr : (k.a : ℝ) ^ 2 + (k.b : ℝ) ^ 2 = 1 := by exact_mod_cast hrot
  funext j
  fin_cases j <;> simp [AffineCell.coord, AffineCell.map]
  · field_simp [hp 0]
  · field_simp [hp 1]
  · field_simp [hp 2]
  · field_simp [hp 3]
  · rw [div_eq_iff (hp 4)]; linear_combination ((k.h 4 : ℝ) * u 4) * hr
  · rw [div_eq_iff (hp 5)]; linear_combination ((k.h 5 : ℝ) * u 5) * hr

/-- `map` inverts `coord` on a well-formed cell (AUDIT-HD11964-LEMMAS-1, L4; the auditor's
probe). -/
theorem AffineCell.map_coord (k : AffineCell) (hk : k.wf = true) (x : Fin 6 → ℝ) :
    k.map (k.coord x) = x := by
  simp only [AffineCell.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hpos, hrot⟩ := hk
  have hp : ∀ j, (k.h j : ℝ) ≠ 0 := fun j =>
    (show (0 : ℝ) < k.h j by exact_mod_cast hpos j (List.mem_finRange j)).ne'
  have hr : (k.a : ℝ) ^ 2 + (k.b : ℝ) ^ 2 = 1 := by exact_mod_cast hrot
  funext j
  fin_cases j <;> simp [AffineCell.coord, AffineCell.map]
  · field_simp [hp 0]; ring
  · field_simp [hp 1]; ring
  · field_simp [hp 2]; ring
  · field_simp [hp 3]; ring
  · field_simp [hp 4, hp 5]; linear_combination (x 4 - (k.c 4 : ℝ)) * hr
  · field_simp [hp 4, hp 5]; linear_combination (x 5 - (k.c 5 : ℝ)) * hr

/-- The linear part of `x ↦ u(x)`, into `ℂ⁶`. -/
def AffineCell.coordCLM (k : AffineCell) : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    Complex.ofRealCLM.comp (∑ i, ((k.invMx j i : ℚ) : ℝ) • ContinuousLinearMap.proj i)

theorem AffineCell.coordCLM_apply (k : AffineCell) (v : Fin 6 → ℝ) (j : Fin 6) :
    k.coordCLM v j = ((∑ i, ((k.invMx j i : ℚ) : ℝ) * v i : ℝ) : ℂ) := by
  simp [AffineCell.coordCLM]

/-- `x ↦ u(x)` is affine with linear part `coordCLM`. -/
theorem AffineCell.coord_ofReal_eq (k : AffineCell) (x y : Fin 6 → ℝ) :
    (fun j => (k.coord y j : ℂ)) = (fun j => (k.coord x j : ℂ)) + k.coordCLM (y - x) := by
  funext j
  rw [Pi.add_apply, AffineCell.coordCLM_apply]
  push_cast
  fin_cases j <;> simp [AffineCell.coord, AffineCell.invMx, Fin.sum_univ_six] <;> ring

/-- **The physical slow derivatives** (1c): the derivative of `x ↦ g (u(x))` along the physical
coordinate `x_i` is bounded by `Σ_j |∂u_j/∂x_i| B_j` when the cell-variable partials of `g` are
bounded by `B_j`. -/
theorem norm_fderiv_comp_coord_le (k : AffineCell) {g : (Fin 6 → ℂ) → ℂ} {x : Fin 6 → ℝ}
    (hg : DifferentiableAt ℂ g (fun j => (k.coord x j : ℂ))) (B : Fin 6 → ℝ)
    (hB : ∀ j, ‖fderiv ℂ g (fun j => (k.coord x j : ℂ)) (Pi.single j 1)‖ ≤ B j) (i : Fin 6) :
    ‖fderiv ℝ (fun y : Fin 6 → ℝ => g (fun j => (k.coord y j : ℂ))) x (Pi.single i 1)‖ ≤
      ∑ j, |(k.invMx j i : ℝ)| * B j := by
  set c0 : Fin 6 → ℂ := fun j => (k.coord x j : ℂ)
  have hΦ : HasFDerivAt (fun y : Fin 6 → ℝ => (fun j => (k.coord y j : ℂ))) k.coordCLM x := by
    have h : HasFDerivAt (fun y : Fin 6 → ℝ => c0 + k.coordCLM (y - x)) k.coordCLM x := by
      simpa using ((k.coordCLM.hasFDerivAt).comp x ((hasFDerivAt_id x).sub_const x)).const_add c0
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    exact k.coord_ofReal_eq x y
  have hcomp := (hg.hasFDerivAt.restrictScalars ℝ).comp x hΦ
  rw [show (fun y : Fin 6 → ℝ => g (fun j => (k.coord y j : ℂ))) =
      g ∘ (fun y : Fin 6 → ℝ => fun j => (k.coord y j : ℂ)) from rfl, hcomp.fderiv]
  have hv : k.coordCLM (Pi.single i 1) =
      ∑ j, ((k.invMx j i : ℝ) : ℂ) • (Pi.single j 1 : Fin 6 → ℂ) := by
    funext j
    rw [AffineCell.coordCLM_apply, Finset.sum_apply]
    simp [Pi.single_apply, Finset.sum_ite_eq']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [hv, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)

end HD11964.Cover

end
