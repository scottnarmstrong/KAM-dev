/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRange
public import KAM.Iso.Linear.Tools

/-!
# Part 1 step exports: reduced equation, geometry, perturbation (graph gap GAP-I1b)

Literal exports of the proof-step nodes of `bpI:p1:reduced` (`rd-expand`, `rd-consequence`),
`bpI:p1:geometry-noA5` (`geo-*`) and `bpI:p1:perturbation-noA5` (`pt-*`) under the source setting
`SettingSrc` (`τ ≥ 0`), built from the landed `reduced_src`, `geometry_noA5_src`,
`perturbation_noA5_src` and track K's helper lemmas. In the geometry and perturbation steps the
`σ`'s are free reals: the constants depend on them only through `𝔪`, which is unchanged by
replacing each `σ` by `max σ 1` (`mSize_max_one`).

* `step_rd_expand`, `step_rd_consequence`;
* `step_geo_de`, `step_geo_red`, `step_geo_red_domega`, `step_geo_red_ered`, `step_geo_sym`;
* `step_pt_small`, `step_pt_domain`, `step_pt_frame`, `step_pt_torsion`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `bpI:p1:reduced`, step `rd-expand` (b): for `ξ` holomorphic on `T_{r'}`, `ξ^ω ∈ ℂ`,
`ΔK = Pξ`, `Δω = -ω ξ^ω`, on `T_{r'}`:
`Q(AΔK - ∂_ωΔK - DK Δω) + QE = (Λ + E_red) ξ - ∂_ω ξ + Ω₀ E_sym ∂_ω ξ + (ω; 0) ξ^ω
  - (0; Ω_K ω) ξ^ω - η`. -/
theorem step_rd_expand (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
    (hξ : DifferentiableOn ℂ ξ (complexStrip n r')) (ξω : ℂ) :
    ∀ θ ∈ complexStrip n r',
      reducer K θ *ᵥ (linMat H K θ *ᵥ (frameMat K θ *ᵥ ξ θ) -
          fderiv ℂ (fun y => frameMat K y *ᵥ ξ y) θ (fun l => (ω l : ℂ)) -
          tangentMat K θ *ᵥ (-(ξω • fun l => (ω l : ℂ)))) +
        reducer K θ *ᵥ sumVec n (invarianceError H K ω θ) =
      (triangularMat (torsion H K ω θ) + redDefect H K ω θ) *ᵥ ξ θ -
          fderiv ℂ ξ θ (fun l => (ω l : ℂ)) +
        (omegaZeroMatrix n * symDefect K θ) *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ)) +
        ξω • Sum.elim (fun l => (ω l : ℂ)) (0 : Fin n → ℂ) -
        ξω • Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ)) - eta H K ω θ := by
  intro θ hθ
  have h := (reduced_src hS hr hK hKD hG hr' hr'r hξ ξω).2.1 θ hθ
  have e1 : linMat H K θ *ᵥ (frameMat K θ *ᵥ ξ θ) -
      fderiv ℂ (fun y => frameMat K y *ᵥ ξ y) θ (fun l => (ω l : ℂ)) -
      tangentMat K θ *ᵥ (-(ξω • fun l => (ω l : ℂ))) + sumVec n (invarianceError H K ω θ) =
      isoResidual H K ω ξ ξω θ := by
    simp only [isoResidual, Matrix.mulVec_neg, Matrix.mulVec_smul]
    abel
  rw [← Matrix.mulVec_add, e1, h, bordOp, isoLinError, triangularMat, Matrix.add_mulVec]
  module

/-- `bpI:p1:reduced`, step `rd-consequence`: (c) if the bordered system holds then
`Q Res = E_lin`, with the bound on `E_lin`; (d) `|E_sym| < 1` gives `det P ≠ 0` (Neumann
criterion of radius one, `Q` invertible too); if `det P ≠ 0` on `T_{r'}` then `Res = Q⁻¹ E_lin`
and `Res = 0 ↔ Λξ - ∂_ωξ + (ω;0)ξ^ω = η - E_lin`. -/
theorem step_rd_consequence (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
    (hξ : DifferentiableOn ℂ ξ (complexStrip n r')) (ξω : ℂ) :
    (∀ θ ∈ complexStrip n r', bordOp H K ω ξ ξω θ = eta H K ω θ →
      reducer K θ *ᵥ isoResidual H K ω ξ ξω θ = isoLinError H K ω ξ ξω θ) ∧
    (∀ θ ∈ complexStrip n r', ‖isoLinError H K ω ξ ξω θ‖ ≤ ‖redDefect H K ω θ‖ * ‖ξ θ‖ +
      ‖symDefect K θ‖ * ‖fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ + ‖lagrangeMat K θ‖ * ‖ω‖ * ‖ξω‖) ∧
    (∀ θ : Fin n → ℂ, ‖symDefect K θ‖ < 1 →
      IsUnit (frameMat K θ).det ∧ IsUnit (reducer K θ).det) ∧
    ((∀ θ ∈ complexStrip n r', IsUnit (frameMat K θ).det) → ∀ θ ∈ complexStrip n r',
      (bordOp H K ω ξ ξω θ = eta H K ω θ →
        isoResidual H K ω ξ ξω θ = (reducer K θ)⁻¹ *ᵥ isoLinError H K ω ξ ξω θ) ∧
      (isoResidual H K ω ξ ξω θ = 0 ↔
        bordOp H K ω ξ ξω θ = eta H K ω θ - isoLinError H K ω ξ ξω θ)) := by
  obtain ⟨-, -, hc, hbd, hd⟩ := reduced_src hS hr hK hKD hG hr' hr'r hξ ξω
  refine ⟨hc, hbd, fun θ hθ => ?_, hd⟩
  have hΩ : IsUnit (omegaZeroMatrix n) :=
    IsUnit.of_mul_eq_one (-omegaZeroMatrix n) (by
      rw [Matrix.mul_neg, omegaZeroMatrix_mul_self, neg_neg])
  have hX : ‖omegaZeroMatrix n * symDefect K θ‖ < 1 := by
    rw [norm_omegaZeroMatrix_mul]
    exact hθ
  have hPOP : (frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ =
      omegaZeroMatrix n * (1 - omegaZeroMatrix n * symDefect K θ) := by
    have h : (frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ =
        symDefect K θ + omegaZeroMatrix n := by
      simp [symDefect]
    rw [h, Matrix.mul_sub, ← Matrix.mul_assoc, omegaZeroMatrix_mul_self]
    simp [add_comm]
  have hu : IsUnit ((frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ).det := by
    rw [hPOP, Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hΩ).mul (isUnit_det_one_sub hX)
  rw [Matrix.det_mul, Matrix.det_mul] at hu
  have hP : IsUnit (frameMat K θ).det := (IsUnit.mul_iff.1 hu).2
  exact ⟨hP, isUnit_det_reducer K hP⟩

/-! ### Geometry without the torsion hypothesis -/

section Geometry

variable {σK σB σT : ℝ} {β ε δ : ℝ}

/-- `bpI:p1:geometry-noA5`, step `geo-de`: `E` is holomorphic with `|E| ≤ ε` on `T_r`, and
`|DE| ≤ n ε/δ`, `|(DE)ᵀ| ≤ 2n ε/δ` on `T_{r-δ}`. -/
theorem step_geo_de (hS : SettingSrc n τ M D H ω γ) (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    DifferentiableOn ℂ (invarianceError H K ω) (complexStrip n r) ∧
    (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ ε) ∧
    ∀ θ ∈ complexStrip n (r - δ),
      ‖errDerivMat H K ω θ‖ ≤ n * ε / δ ∧ ‖(errDerivMat H K ω θ)ᵀ‖ ≤ 2 * n * ε / δ := by
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  have hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  exact ⟨FrameAux.differentiableOn_invarianceError hSt hK.holo hKD, hK.error_le,
    fun θ hθ => ⟨((geometry_noA5_src (σT := 1) hS hK hδ hδ1 h2δ).1 θ hθ).1,
      ((geometry_noA5_src (σT := 1) hS hK hδ hδ1 h2δ).1 θ hθ).2.1⟩⟩

/-- `bpI:p1:geometry-noA5`, step `geo-red`: `|∂_ω Ω_K| ≤ (2n𝔪 + 2n²𝔪) ε/δ` and
`|E_red| ≤ C_red ε/δ` on `T_{r-δ}`. -/
theorem step_geo_red (hS : SettingSrc n τ M D H ω γ) (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤
        (2 * n * mSize M σK σB σT + 2 * n ^ 2 * mSize M σK σB σT) * ε / δ ∧
      ‖redDefect H K ω θ‖ ≤ C_red n M σK σB σT * ε / δ := by
  intro θ hθ
  obtain ⟨-, -, h3, h4⟩ := (geometry_noA5_src (σT := σT) hS hK hδ hδ1 h2δ).1 θ hθ
  refine ⟨?_, h4⟩
  have e : 2 * (n : ℝ) * mSize M σK σB σT + 2 * n ^ 2 * mSize M σK σB σT =
      2 * n * (n + 1) * mSize M σK σB σT := by ring
  rwa [e]

/-- `bpI:p1:geometry-noA5`, step `geo-red-domega`:
`|∂_ω Ω_K| ≤ (2n𝔪 + 2n²𝔪) ε/δ = 2n(n+1)𝔪 ε/δ` on `T_{r-δ}`. -/
theorem step_geo_red_domega (hS : SettingSrc n τ M D H ω γ)
    (hK : AdmissibleNoTwist σK σB D H ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    (2 * n * mSize M σK σB σT + 2 * n ^ 2 * mSize M σK σB σT) * ε / δ =
        2 * n * (n + 1) * mSize M σK σB σT * ε / δ ∧
      ∀ θ ∈ complexStrip n (r - δ), ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤
        (2 * n * mSize M σK σB σT + 2 * n ^ 2 * mSize M σK σB σT) * ε / δ :=
  ⟨by ring, fun θ hθ => (step_geo_red (σT := σT) hS hK hδ hδ1 h2δ θ hθ).1⟩

/-- `bpI:p1:geometry-noA5`, step `geo-red-ered`:
`|E_red| ≤ C_red ε/δ = 2n(n+1)𝔪² ε/δ` on `T_{r-δ}`. -/
theorem step_geo_red_ered (hS : SettingSrc n τ M D H ω γ)
    (hK : AdmissibleNoTwist σK σB D H ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    C_red n M σK σB σT * ε / δ = 2 * n * (n + 1) * mSize M σK σB σT ^ 2 * ε / δ ∧
      ∀ θ ∈ complexStrip n (r - δ), ‖redDefect H K ω θ‖ ≤ C_red n M σK σB σT * ε / δ :=
  ⟨rfl, fun θ hθ => (step_geo_red (σT := σT) hS hK hδ hδ1 h2δ θ hθ).2⟩

/-- `bpI:p1:geometry-noA5`, step `geo-sym`: `Ω_K` is holomorphic, `1`-periodic on `T_{r-δ}` with
`⟨Ω_K⟩ = 0`; `|Ω_K| ≤ C_Ω ε/(γ δ^{κ+1})` on `T_{r-2δ}`; `|E_sym| ≤ 𝔪² |Ω_K|` on `T_r`. -/
theorem step_geo_sym (hS : SettingSrc n τ M D H ω γ) (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    DifferentiableOn ℂ (lagrangeMat K) (complexStrip n (r - δ)) ∧
    IsPeriodicOn (lagrangeMat K) (r - δ) ∧ avg (lagrangeMat K) = 0 ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ∧
    ∀ θ ∈ complexStrip n r, ‖symDefect K θ‖ ≤ mSize M σK σB σT ^ 2 * ‖lagrangeMat K θ‖ := by
  have hSt := (hS.setting (σK := max σK 1) (σB := max σB 1) (σT := max σT 1) (by positivity)
    (by positivity) (by positivity)).toStanding
  have hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  obtain ⟨hdiff, hper, havg, -⟩ := Geometry.geo_omegak_inputs hSt
    hK.r_pos hK.holo hK.primary hKD (fun θ hθ => (hK.deriv_le θ hθ).trans (le_max_left _ _))
    hK.error_le hδ
  exact ⟨hdiff, hper, havg, fun θ hθ => ((geometry_noA5_src (σT := σT) hS hK hδ hδ1 h2δ).2.1 θ hθ).1,
    fun θ hθ => Geometry.geo_esym_le (hK.gram θ hθ).1 (hK.gram θ hθ).2⟩

end Geometry

end KAM.Iso.Linear
