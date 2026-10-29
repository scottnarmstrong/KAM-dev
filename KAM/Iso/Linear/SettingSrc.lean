/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Iso.Linear.DioDirichlet
public import KAM.Torus.FrozenAgreement

/-!
# The literal Part 1 setting (graph gap GAP-I1a, ruling N1 option (i))

* `SettingSrc` is `bpI:p1:setting` as the source states it: `n ≥ 2`, `τ ≥ 0`, `M > 0`, no `σ`'s.
* `SettingSrc.setting` projects it to the landed `Setting n τ M σK σB σT` at the same `τ`, for
  every positive `σ` (the exponent range is bridged by `KAM.IsDiophantine.n_sub_one_le_tau`).
* `SettingSrc.k_bridge` is `bpI:p1:setting#k-bridge`: track K's `Standing` data with `h := H`,
  `𝔅 := D`, the extra bound on `DH`, `τ ≥ 0`, `n ≥ 1`, and the frozen agreement of the objects.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

/-- `bpI:p1:setting` (literal source form): `n ≥ 2`, `τ ≥ 0`, `M > 0`; `D` open and
`ℤⁿ`-invariant; `H` holomorphic on `D`, `1`-periodic in `θ`, real at real phase points; bounds
`M` on `DH`, `X_H`, `DX_H`, `D²X_H`; `γ > 0`, `ω ∈ Dio_{γ,τ}`. -/
structure SettingSrc (n : ℕ) (τ M : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (γ : ℝ) : Prop where
  two_le : 2 ≤ n
  tau_nonneg : 0 ≤ τ
  M_pos : 0 < M
  isOpen : IsOpen D
  transl_mem : ∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D
  holo : DifferentiableOn ℂ H D
  periodic : ∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z
  real : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
    (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  dH_le : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M
  bounds : ∀ z ∈ D, ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M
  gamma_pos : 0 < γ
  dio : IsDiophantine γ τ ω

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- `τ ≥ n - 1` follows from the Diophantine condition (Dirichlet). -/
theorem SettingSrc.tau_ge (h : SettingSrc n τ M D H ω γ) : (n : ℝ) - 1 ≤ τ :=
  IsDiophantine.n_sub_one_le_tau h.two_le h.gamma_pos h.dio

/-- `bpI:p1:setting` against the landed `Setting`, at the same `τ`, for positive `σ`'s. -/
theorem SettingSrc.setting (h : SettingSrc n τ M D H ω γ) {σK σB σT : ℝ} (hσK : 0 < σK)
    (hσB : 0 < σB) (hσT : 0 < σT) : Setting n τ M σK σB σT D H ω γ where
  two_le := h.two_le
  tau_ge := h.tau_ge
  M_pos := h.M_pos
  σK_pos := hσK
  σB_pos := hσB
  σT_pos := hσT
  isOpen := h.isOpen
  transl_mem := h.transl_mem
  holo := h.holo
  periodic := h.periodic
  real := h.real
  bounds := h.bounds
  gamma_pos := h.gamma_pos
  dio := h.dio
  dH_le := h.dH_le

/-- `bpI:p1:setting#k-bridge`: the common K standing data (`h := H`, `𝔅 := D`) at the same `τ`,
the bound `‖DH‖ ≤ M`, `τ ≥ 0`, `n ≥ 1`, and the frozen agreement of the objects, wherever
`K` is holomorphic on a strip with invertible Gram matrix. -/
theorem SettingSrc.k_bridge (h : SettingSrc n τ M D H ω γ) :
    KAM.Apost.Standing n τ M 1 1 1 D H ω γ ∧ (∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M) ∧ 0 ≤ τ ∧ 1 ≤ n ∧
    ∀ (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {r : ℝ}, 0 < r →
      DifferentiableOn ℂ K (complexStrip n r) →
      (∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) →
      (∀ θ, gramMatrix K θ = (tangentMat K θ)ᵀ * tangentMat K θ) ∧
      (∀ θ j, sumVec n (normalFrame K θ j) = fun s => normalMat K θ s j) ∧
      (∀ θ, sumVec n (invarianceError H K ω θ) =
        sumVec n (hamiltonianVectorFieldℂ H (K θ)) - tangentMat K θ *ᵥ (fun l => (ω l : ℂ))) ∧
      (∀ θ ∈ complexStrip n r,
        torsion H K ω θ = (normalMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat H K ω θ) ∧
      (∀ θ ∈ complexStrip n r,
        gramMatrix K θ * (gramMatrix K θ)⁻¹ = 1 ∧ (gramMatrix K θ)⁻¹ * gramMatrix K θ = 1) ∧
      (Continuous (fun x : Fin n → ℝ => torsion H K ω (fun i => (x i : ℂ))) →
        torsionAverage H K ω = avg (torsion H K ω)) :=
  ⟨(h.setting one_pos one_pos one_pos).toStanding, h.dH_le, h.tau_nonneg,
    by have := h.two_le; omega, fun K _ hr hK hG => frozen_agreement H K ω hr hK hG⟩

end KAM.Iso.Linear
