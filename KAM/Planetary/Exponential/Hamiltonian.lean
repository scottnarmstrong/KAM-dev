/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian
public import KAM.Planetary.Exponential.KeplerData
public import KAM.Planetary.Exponential.Perturbation
public import KAM.Planetary.Exponential.RealDomain
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Poincare.Product

/-!
# P14 package E10: the N-Hamiltonian is the chart Hamiltonian

Blueprint P, Part 14 (`bpP:p14:hnu`, `stepP:p14:hn-eq`, `stepP:p14:hn-field`).  For `ν = B₀ μ`
the degenerate Hamiltonian `h(Λ) + ν Re P(cx w)` built from the Kepler part and the complexified
perturbation agrees on the working cylinder with `H_mov^{(μ)} ∘ Ψ` (`hnu`).  Equal functions on
an open set have equal `fderiv` and equal Hamiltonian vector fields there
(`fderiv_eq_of_eqOn_open`, `hamiltonianVectorField_eq_of_eqOn_open`), and the Hamiltonian of
`(-h, -P)` is the negative (`degenerateHamiltonian_neg`, `hamiltonianVectorField_neg`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {n : ℕ}

/-- The working cylinder lies in the enlarged cylinder. -/
theorem workingCylinder_subset_enlargedCylinder (B : AMDBox n) {kappa A : ℝ} (hk : 0 < kappa) :
    workingCylinder B kappa A ⊆ enlargedCylinder B kappa A := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun i => ?_, ?_⟩
  · have := h1 i
    constructor <;> linarith [this.1, this.2]
  · exact le_of_lt h2

/-- `stepP:p14:hn-eq`: pointwise equality of the N-Hamiltonian and the chart Hamiltonian. -/
theorem hnu (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {B0 mu : ℝ} (hB0 : 0 < B0)
    {P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ}
    (hP : ∀ w ∈ workingCylinder B kappa A, P (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ)) :
    ∀ w ∈ workingCylinder B kappa A,
      degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass))
        (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0*mu) w =
        movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w) := by
  intro w hw
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  have hws : w ∈ chartSafe B.mass :=
    (real_domain B hB hd).1 (workingCylinder_subset_enlargedCylinder B hd.kappa_pos hw)
  have hmov := movingHamiltonian_poincareProd (μ := mu) (G := 1) (m0 := 1) hm (by norm_num) hws.1
  simp only [mul_one] at hmov
  rw [hmov]
  have hk : hProd 1 B.mass w = KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass) (fast w.2) := by
    rw [realPart_planetaryKeplerC]
    simp [hProd, keplerSumGen]
  unfold degenerateHamiltonian
  beta_reduce
  rw [hP w hw, Complex.ofReal_re, ← hk]
  field_simp

/-- `stepP:p14:hn-field`: functions equal on an open set have the same `fderiv` there. -/
theorem fderiv_eq_of_eqOn_open {k : ℕ} {U : Set (Phase k)} (hU : IsOpen U)
    {H₁ H₂ : Phase k → ℝ} (h : ∀ w ∈ U, H₁ w = H₂ w) {w : Phase k} (hw : w ∈ U) :
    fderiv ℝ H₁ w = fderiv ℝ H₂ w :=
  Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) h)

/-- Functions equal on an open set have the same Hamiltonian vector field there. -/
theorem hamiltonianVectorField_eq_of_eqOn_open {k : ℕ} {U : Set (Phase k)} (hU : IsOpen U)
    {H₁ H₂ : Phase k → ℝ} (h : ∀ w ∈ U, H₁ w = H₂ w) {w : Phase k} (hw : w ∈ U) :
    KAM.hamiltonianVectorField H₁ w = KAM.hamiltonianVectorField H₂ w := by
  simp only [KAM.hamiltonianVectorField, fderiv_eq_of_eqOn_open hU h hw]

/-- `stepP:p14:hn-field`, differentiability and field equality: on an open set `U` inside the
working cylinder, the N-Hamiltonian is differentiable at each `w ∈ U`, and its `fderiv` and
Hamiltonian vector field are those of the chart Hamiltonian `H_mov^{(μ)} ∘ Ψ`. -/
theorem differentiableAt_hnu_field (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {B0 mu : ℝ} (hB0 : 0 < B0)
    {P : ((Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)) → ℂ}
    (hP : ∀ w ∈ workingCylinder B kappa A, P (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 B.mass (poincareProd B.mass 1 w) / B0 : ℝ) : ℂ))
    {U : Set (Phase (n + n))} (hU : IsOpen U) (hUW : U ⊆ workingCylinder B kappa A)
    {w : Phase (n + n)} (hw : w ∈ U) :
    let H₁ : Phase (n + n) → ℝ := fun x =>
      degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass))
        (fun _ y => (P (KAM.Nekhoroshev.complexifyPhase y)).re) (B0*mu) x
    let H₂ : Phase (n + n) → ℝ := fun x => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 x)
    DifferentiableAt ℝ H₁ w ∧ fderiv ℝ H₁ w = fderiv ℝ H₂ w ∧
      KAM.hamiltonianVectorField H₁ w = KAM.hamiltonianVectorField H₂ w := by
  intro H₁ H₂
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  have hEq : ∀ x ∈ U, H₁ x = H₂ x := fun x hx => hnu B hB hd hB0 hP x (hUW hx)
  have hws : w ∈ chartSafe B.mass :=
    (real_domain B hB hd).1
      (workingCylinder_subset_enlargedCylinder B hd.kappa_pos (hUW hw))
  have hdiff₂ : DifferentiableAt ℝ H₂ w :=
    (differentiableAt_movingHamiltonian 1 1 B.mass mu hws.2).comp w
      ((analyticOnNhd_poincareProd hm one_pos w hws.1).differentiableAt)
  refine ⟨?_, fderiv_eq_of_eqOn_open hU hEq hw, hamiltonianVectorField_eq_of_eqOn_open hU hEq hw⟩
  exact (Filter.EventuallyEq.differentiableAt_iff
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) hEq)).2 hdiff₂

/-- The Hamiltonian vector field of `-H` is `-X_H` (linearity of `X`). -/
theorem hamiltonianVectorField_neg {k : ℕ} (H : Phase k → ℝ) (w : Phase k) :
    KAM.hamiltonianVectorField (fun z => -H z) w = -KAM.hamiltonianVectorField H w := by
  simp only [KAM.hamiltonianVectorField, fderiv_fun_neg, neg_apply]
  ext i <;> simp

/-- The degenerate Hamiltonian of `(-h, -P)` is the negative of that of `(h, P)`. -/
theorem degenerateHamiltonian_neg {a b : ℕ} (H0 : (Fin a → ℝ) → ℝ)
    (P : ℝ → Phase (a + b) → ℝ) (mu : ℝ) (z : Phase (a + b)) :
    degenerateHamiltonian (fun I => -H0 I) (fun nu x => -P nu x) mu z =
      -degenerateHamiltonian H0 P mu z := by
  unfold degenerateHamiltonian
  ring

end KAM.Planetary

end
