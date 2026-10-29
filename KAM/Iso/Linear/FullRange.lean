/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.SettingSrc
public import KAM.Iso.Linear.Extended
public import KAM.Iso.Linear.LastRow
public import KAM.Iso.Linear.Energy
public import KAM.Iso.Linear.EnergyDefect
public import KAM.Iso.Linear.Reduced
public import KAM.Iso.Linear.NoTwist

/-!
# Part 1 parents under the source setting `τ ≥ 0` (graph gap GAP-I1a, ruling N1 option (i))

Literal exports of the eight Part 1 parent nodes: each states the landed conclusion with
`SettingSrc` (the source's `τ ≥ 0`, no `σ`'s) in place of `Setting`, and is proved by projecting
with `SettingSrc.setting` (Dirichlet: `τ ≥ n - 1` follows). The `σ`'s of the landed statements
are `1`; in `geometry_noA5_src`, `perturbation_noA5_src` the `σ`'s are free reals, because the
constants depend on them only through `𝔪 = max {1, M, σK, σB, σT}`, which is unchanged by
replacing each `σ` by `max σ 1`.

* `extended_basic_src` (`bpI:p1:extended-basic`), `last_row_src` (`bpI:p1:last-row`),
  `energy_approx_src`, `energy_defect_src` (`bpI:p1:energy-approx`),
  `energy_conservation_src`, `reduced_src`, `geometry_noA5_src`, `perturbation_noA5_src`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

theorem mSize_max_one (M σK σB σT : ℝ) :
    mSize M (max σK 1) (max σB 1) (max σT 1) = mSize M σK σB σT := by
  refine le_antisymm (max_le one_le_mSize (max_le M_le_mSize (max_le
    (max_le σK_le_mSize one_le_mSize) (max_le (max_le σB_le_mSize one_le_mSize)
    (max_le σT_le_mSize one_le_mSize))))) (max_le one_le_mSize (max_le M_le_mSize (max_le
    ((le_max_left _ _).trans σK_le_mSize) (max_le ((le_max_left _ _).trans σB_le_mSize)
    ((le_max_left _ _).trans σT_le_mSize)))))

/-- `bpI:p1:extended-basic`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `extended_basic`, verbatim, with `SettingSrc` in place of `Setting`. -/
theorem extended_basic_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    (DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧ IsPeriodicOn (energyRow H K) r ∧
      IsRealVec (energyRow H K) ∧
      DifferentiableOn ℂ (KAM.Iso.extendedTorsion H K ω) (complexStrip n r) ∧
      IsPeriodicOn (KAM.Iso.extendedTorsion H K ω) r ∧ IsRealMat (KAM.Iso.extendedTorsion H K ω) ∧
      Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) ∧
      KAM.Iso.extendedTorsionAverage H K ω =
        bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (avg (energyRow H K)) ∧
      ∀ i j, (KAM.Iso.extendedTorsionAverage H K ω i j).im = 0) ∧
    ∀ σK' σB' : ℝ,
      (∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK' ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB') →
      ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ M * σK' * σB' ∧
        ∀ CT : ℝ, ‖torsion H K ω θ‖ ≤ CT →
          ‖KAM.Iso.extendedTorsion H K ω θ‖ ≤ max (CT + ‖ω‖) (M * σK' * σB') :=
  extended_basic (hS.setting one_pos one_pos one_pos) hr hK hKp hKr hKD hG

/-- `bpI:p1:last-row`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `last_row`, verbatim, with `SettingSrc` in place of `Setting`. -/
theorem last_row_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    (∀ θ ∈ complexStrip n r, energyRow H K θ = (fun b => (ω b : ℂ)) - etaL H K ω θ ∧
      ∑ b, ‖energyRow H K θ b - (ω b : ℂ)‖ ≤ n * ‖etaL H K ω θ‖) ∧
    ((∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) →
      (∀ θ ∈ complexStrip n r, KAM.Iso.extendedTorsion H K ω θ =
        bordMat (torsion H K ω θ) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))) ∧
      KAM.Iso.extendedTorsionAverage H K ω =
        bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))) ∧
    KAM.Iso.extendedTorsionAverage H K ω = bordMat (torsionAverage H K ω)
      (fun a => (ω a : ℂ)) ((fun a => (ω a : ℂ)) - avg (etaL H K ω)) ∧
    ∀ e σK' σB' : ℝ, (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ e ∧
        ‖fderiv ℂ K θ‖ ≤ σK' ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB') →
      ‖KAM.Iso.extendedTorsionAverage H K ω -
          bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))‖ ≤
        2 * n ^ 2 * σK' * σB' * e :=
  last_row (hS.setting one_pos one_pos one_pos) hr hK hKD hG

/-- `bpI:p1:energy-approx (a)–(e)`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `energy_approx`, verbatim, with `SettingSrc` in place of `Setting`. -/
theorem energy_approx_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    (DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) ∧
      IsPeriodicOn (fun θ => H (K θ)) r ∧ (∀ x : Fin n → ℝ, (H (K fun i => (x i : ℂ))).im = 0) ∧
      (∀ θ ∈ complexStrip n r,
        fderiv ℂ (fun y => H (K y)) θ = (fderiv ℂ H (K θ)).comp (fderiv ℂ K θ)) ∧
      avg (fun θ => H (K θ)) = KAM.Iso.energyAverage H K ∧
      (KAM.Iso.energyAverage H K).im = 0) ∧
    (∀ θ ∈ complexStrip n r, fderiv ℂ (fun y => H (K y)) θ (fun l => (ω l : ℂ)) =
      -fderiv ℂ H (K θ) (invarianceError H K ω θ)) ∧
    (∀ θ ∈ complexStrip n r, ∀ j, etaN H K ω θ j =
      fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1) - ∑ l, lagrangeMat K θ j l * (ω l : ℂ)) ∧
    ((∀ j, avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)) = 0) ∧
      avg (lagrangeMat K) = 0 ∧ avg (etaN H K ω) = 0) ∧
    ∀ ε δ : ℝ, (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ ε) → 0 < δ → δ < r →
      (∀ θ ∈ complexStrip n (r - δ), ‖H (K θ) - KAM.Iso.energyAverage H K‖ ≤
        M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε) ∧
      ∀ δ' : ℝ, 0 < δ' → δ' < r - δ → ∀ θ ∈ complexStrip n (r - δ - δ'),
        ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε / δ' :=
  energy_approx (hS.setting one_pos one_pos one_pos) hr hK hKp hKr hKD

/-- `bpI:p1:energy-approx (f)`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `energy_defect`, verbatim, with `SettingSrc` in place of `Setting`. -/
theorem energy_defect_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξL ξN : (Fin n → ℂ) → Fin n → ℂ}
    (hξL : DifferentiableOn ℂ ξL (complexStrip n r'))
    (hξN : DifferentiableOn ℂ ξN (complexStrip n r')) :
    (∀ θ ∈ complexStrip n r',
      fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ))) =
        energyRow H K θ ⬝ᵥ ξN θ + fderiv ℂ (fun y => H (K y)) θ (ξL θ) ∧
      fderiv ℂ (fun y => H (K y)) θ (ξL θ) =
        etaN H K ω θ ⬝ᵥ ξL θ - (fun l => (ω l : ℂ)) ⬝ᵥ (lagrangeMat K θ *ᵥ ξL θ) ∧
      ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * (‖etaN H K ω θ‖ + ‖ω‖ * ‖lagrangeMat K θ‖)) ∧
    avg (fun θ => fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ)))) =
      avg (fun θ => energyRow H K θ ⬝ᵥ ξN θ) + avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ)) ∧
    ∀ A X : ℝ,
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ))‖ ≤ A) →
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖ξL (fun i => (x i : ℂ))‖ ≤ X) →
      ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ))‖ ≤ A * X :=
  energy_defect (hS.setting one_pos one_pos one_pos) hr hK hKp hKr hKD hG hr' hr'r hξL hξN

/-- `bpI:p1:energy-conservation`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `energy_conservation`, verbatim, with `SettingSrc` for `Setting`. -/
theorem energy_conservation_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) :
    (∀ θ ∈ complexStrip n r, H (K θ) = KAM.Iso.energyAverage H K) ∧
    (∀ E₀ : ℂ, KAM.Iso.energyAverage H K = E₀ → ∀ θ ∈ complexStrip n r, H (K θ) = E₀) ∧
    ∀ E₀ : ℂ, ∀ θ ∈ complexStrip n r, ‖H (K θ) - E₀‖ = ‖KAM.Iso.energyAverage H K - E₀‖ :=
  energy_conservation (hS.setting one_pos one_pos one_pos) hr hK hKp hKr hKD hE

/-- `bpI:p1:reduced`: literal export, source setting `τ ≥ 0` (GAP-I1a).
The landed conclusion of `reduced`, verbatim, with `SettingSrc` in place of `Setting`. -/
theorem reduced_src (hS : SettingSrc n τ M D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
    (hξ : DifferentiableOn ℂ ξ (complexStrip n r')) (ξω : ℂ) :
    (∀ θ ∈ complexStrip n r', reducer K θ * tangentMat K θ = Matrix.fromRows 1 (-lagrangeMat K θ)) ∧
    (∀ θ ∈ complexStrip n r', reducer K θ *ᵥ isoResidual H K ω ξ ξω θ =
      bordOp H K ω ξ ξω θ - eta H K ω θ + isoLinError H K ω ξ ξω θ) ∧
    (∀ θ ∈ complexStrip n r', bordOp H K ω ξ ξω θ = eta H K ω θ →
      reducer K θ *ᵥ isoResidual H K ω ξ ξω θ = isoLinError H K ω ξ ξω θ) ∧
    (∀ θ ∈ complexStrip n r', ‖isoLinError H K ω ξ ξω θ‖ ≤ ‖redDefect H K ω θ‖ * ‖ξ θ‖ +
      ‖symDefect K θ‖ * ‖fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ + ‖lagrangeMat K θ‖ * ‖ω‖ * ‖ξω‖) ∧
    ((∀ θ ∈ complexStrip n r', IsUnit (frameMat K θ).det) → ∀ θ ∈ complexStrip n r',
      (bordOp H K ω ξ ξω θ = eta H K ω θ →
        isoResidual H K ω ξ ξω θ = (reducer K θ)⁻¹ *ᵥ isoLinError H K ω ξ ξω θ) ∧
      (isoResidual H K ω ξ ξω θ = 0 ↔
        bordOp H K ω ξ ξω θ = eta H K ω θ - isoLinError H K ω ξ ξω θ)) :=
  reduced (hS.setting one_pos one_pos one_pos) hr hK hKD hG hr' hr'r hξ ξω

/-- `bpI:p1:geometry-noA5`: literal export under the source setting `τ ≥ 0` (graph gap
GAP-I1a). The landed conclusion of `geometry_noA5`, verbatim, with `SettingSrc` in place of
`Setting` and free `σK σB σT` (they enter the constants only through `𝔪`). -/
theorem geometry_noA5_src (hS : SettingSrc n τ M D H ω γ) {σK σB σT : ℝ} {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    (∀ θ ∈ complexStrip n (r - δ),
      ‖errDerivMat H K ω θ‖ ≤ n * ε / δ ∧ ‖(errDerivMat H K ω θ)ᵀ‖ ≤ 2 * n * ε / δ ∧
      ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤
        2 * n * (n + 1) * mSize M σK σB σT * ε / δ ∧
      ‖redDefect H K ω θ‖ ≤ C_red n M σK σB σT * ε / δ) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ‖symDefect K θ‖ ≤ C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ∧
    (∀ θ ∈ complexStrip n r, ‖etaL H K ω θ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 * ε ∧
      ‖etaN H K ω θ‖ ≤ 2 * n * mSize M σK σB σT * ε ∧ ‖tangentMat K θ‖ ≤ mSize M σK σB σT ∧
      ‖(gramMatrix K θ)⁻¹‖ ≤ mSize M σK σB σT ∧ ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 ∧
      ‖frameMat K θ‖ ≤ 2 * mSize M σK σB σT ^ 2) ∧
    (‖ω‖ ≤ Theta n M σK σB σT → ∀ θ ∈ complexStrip n (r - δ),
      ‖normalFieldMat H K ω θ‖ ≤ C_X n M σK σB σT / δ ∧
        ‖torsion H K ω θ‖ ≤ C_T n M σK σB σT / δ) := by
  have hK' : AdmissibleNoTwist (max σK 1) (max σB 1) D H ω r β ε K :=
    { hK with
      deriv_le := fun θ hθ => (hK.deriv_le θ hθ).trans (le_max_left _ _)
      gram := fun θ hθ => ⟨(hK.gram θ hθ).1, (hK.gram θ hθ).2.trans (le_max_left _ _)⟩ }
  have h := geometry_noA5 (σT := max σT 1) (hS.setting (by positivity) (by positivity)
    (by positivity)) hK' hδ hδ1 h2δ
  simp only [C_red, C_Omega, C_sym, Theta, C_X, C_T, mSize_max_one] at h ⊢
  exact h

/-- `bpI:p1:perturbation-noA5`: literal export under the source setting `τ ≥ 0` (graph gap
GAP-I1a). The landed conclusion of `perturbation_noA5`, verbatim, with `SettingSrc` in place of
`Setting` and free `σK σB σT` (they enter the constants only through `𝔪`). -/
theorem perturbation_noA5_src (hS : SettingSrc n τ M D H ω γ) {σK σB σT : ℝ} {r δ β d : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r)
    (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hdβ : d < β) (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D ∧
      ‖linMat H K' θ - linMat H K θ‖ ≤ mSize M σK σB σT * d) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det ∧
      ‖(gramMatrix K' θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ C_B n M σK σB σT * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
      ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ^ 2) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2) := by
  have hω' : ‖ω‖ ≤ Theta n M (max σK 1) (max σB 1) (max σT 1) := by
    simpa only [Theta, mSize_max_one] using hω
  have hsmall' : 2 * mSize M (max σK 1) (max σB 1) (max σT 1) *
      C_DT n M (max σK 1) (max σB 1) (max σT 1) * d / δ ^ 2 ≤ 1 := by
    simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using hsmall
  have h := perturbation_noA5 (hS.setting (σK := max σK 1) (σB := max σB 1) (σT := max σT 1)
    (by positivity) (by positivity) (by positivity)) hr hδ hδ1 h2δ hω' hK hball
    (fun θ hθ => (hDK θ hθ).trans (le_max_left _ _))
    (fun θ hθ => ⟨(hG θ hθ).1, (hG θ hθ).2.trans (le_max_left _ _)⟩) hK' hd hdβ hsmall'
  simp only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] at h ⊢
  exact h

end KAM.Iso.Linear
