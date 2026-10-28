/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Working
public import KAM.Planetary.SecularForm.Quadratic

/-!
# The literal secular Hessian is the Part 8 matrix (P11A-P1, `bpP:p11:sec-A#data`)

`p11SecularMatrix D L` is the literal Hessian of the frozen secular average of the fixed
Hamiltonian in the position variable `ξ`. At `L = action D a` it equals Part 8's `coeffs D a`:
the second derivative of the secular function along every line `s ↦ (sξ, Λ, 0)` is
`2 ξᵀ Q_h ξ` (`iteratedDeriv_two_rayRemainder`, the output of `quadratic_form`), and the Hessian is
the symmetric bilinear form determined by these diagonal values.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary
open SecularForm

/-- The Part 8 standing data attached to the physical data. -/
def p11PhysicalData {n : ℕ} (D : P11Physical n) : Data n :=
  ⟨D.G, D.m0, D.m, D.G_pos, D.m0_pos, D.m_pos, by have := D.n_ge; omega⟩

section Hessian

variable {n : ℕ}

private theorem hess_diag (D : Data n) {a : Vec n} (ha : a ∈ axes n) (v : Vec n) :
    iteratedFDeriv ℝ 2 (fun ξ : Vec n => secular D false (ξ, action D a, 0)) 0 (fun _ => v) =
      2 * quad (coeffs D a) v := by
  set L := action D a
  set f : Vec n → ℝ := fun ξ => secular D false (ξ, L, 0) with hf
  obtain ⟨r, hr0, -, -, hall⟩ := perturbation_analytic D ha
  set emb : Vec n → Slow n := fun ξ => (ξ, L, 0) with hemb
  have hembc : Continuous emb := by fun_prop
  have hU : IsOpen (emb ⁻¹' realDisc D a r) := (isOpen_realDisc D a hr0).preimage hembc
  have h0U : (0 : Vec n) ∈ emb ⁻¹' realDisc D a r := by
    have := raySlow_zero_mem D a 0 0 hr0
    simpa [raySlow, hemb] using this
  have hfa : AnalyticOnNhd ℝ f (emb ⁻¹' realDisc D a r) := fun ξ hξ =>
    ((hall false).2.2.2.2.1 _ hξ).comp (by fun_prop : AnalyticAt ℝ emb ξ)
  have hcd : ContDiffOn ℝ 2 f (emb ⁻¹' realDisc D a r) := hfa.contDiffOn hU.uniqueDiffOn
  set c : ℝ →L[ℝ] Vec n := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hc
  have hcs : ∀ s, c s = s • v := fun s => by simp [hc]
  have hUc : IsOpen (c ⁻¹' (emb ⁻¹' realDisc D a r)) := hU.preimage c.continuous
  have h0c : (0 : ℝ) ∈ c ⁻¹' (emb ⁻¹' realDisc D a r) := by simpa [hcs] using h0U
  have key := c.iteratedFDerivWithin_comp_right hcd hU.uniqueDiffOn hUc.uniqueDiffOn
    (x := 0) (by simpa [hcs] using h0U) (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hUc h0c,
    iteratedFDerivWithin_of_isOpen _ hU (by simpa [hcs] using h0U)] at key
  have e1 := congrArg (fun T => T (fun _ => (1 : ℝ))) key
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hcs, one_smul, zero_smul]
    at e1
  rw [← e1, ← iteratedDeriv_eq_iteratedFDeriv]
  have hfc : f ∘ c = fun s => secular D false (raySlow D a v 0 s) := by
    funext s
    simp [hf, hcs, raySlow, L]
  rw [hfc]
  have hφ : AnalyticAt ℝ (fun s => secular D false (raySlow D a v 0 s)) 0 :=
    ((hall false).2.2.2.2.1 _ (raySlow_zero_mem D a v 0 hr0)).comp (analyticAt_raySlow D a v 0 0)
  have hp : AnalyticAt ℝ (fun s : ℝ => constantTerm D a +
      (quad (coeffs D a) v + quad (coeffs D a) 0) * s ^ 2) 0 := by fun_prop
  have h2 := iteratedDeriv_two_rayRemainder D ha v 0
  have hrr : rayRemainder D a v 0 = fun s => secular D false (raySlow D a v 0 s) -
      (constantTerm D a + (quad (coeffs D a) v + quad (coeffs D a) 0) * s ^ 2) := by
    funext s; unfold rayRemainder; ring
  rw [hrr, iteratedDeriv_fun_sub hφ.contDiffAt hp.contDiffAt,
    iteratedDeriv_two_quadratic] at h2
  rw [quad_zero] at h2
  linarith

private theorem quad_single (Q : Mat n) (i j : Fin n) :
    quad Q (Pi.single i 1 + Pi.single j 1) =
      Q i i + Q i j + Q j i + Q j j := by
  simp only [quad, Pi.add_apply, Pi.single_apply, mul_add, add_mul, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq, mul_ite, ite_mul]
  ring

private theorem quad_single_self (Q : Mat n) (i : Fin n) : quad Q (Pi.single i 1) = Q i i := by
  simp [quad, Pi.single_apply, Finset.sum_ite_eq, mul_ite, ite_mul]

private theorem contDiffAt_hess (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ContDiffAt ℝ 2 (fun ξ : Vec n => secular D false (ξ, action D a, 0)) 0 := by
  obtain ⟨r, hr0, -, -, hall⟩ := perturbation_analytic D ha
  have h0 : ((0 : Vec n), action D a, (0 : Vec n)) ∈ realDisc D a r := by
    simpa [raySlow] using raySlow_zero_mem D a 0 0 hr0
  have hA := (hall false).2.2.2.2.1 _ h0
  have : AnalyticAt ℝ (fun ξ : Vec n => secular D false (ξ, action D a, 0)) 0 :=
    hA.comp_of_eq (by fun_prop : AnalyticAt ℝ (fun ξ : Vec n => ((ξ, action D a, 0) : Slow n)) 0)
      rfl
  exact this.contDiffAt

end Hessian

/-- At `L = action D a` the literal secular Hessian is Part 8's coefficient matrix. -/
theorem p11SecularMatrix_eq {n : ℕ} (D : P11Physical n) {a : Vec n} (ha : a ∈ axes n) :
    p11SecularMatrix D (action (p11PhysicalData D) a) = coeffs (p11PhysicalData D) a := by
  set E := p11PhysicalData D with hE
  set f : Vec n → ℝ := fun ξ => secular E false (ξ, action E a, 0) with hf
  have hsymS : IsSymmSndFDerivAt ℝ f 0 :=
    (contDiffAt_hess E ha).isSymmSndFDerivAt (by simp)
  have hB : ∀ u v : Vec n, iteratedFDeriv ℝ 2 f 0 ![u, v] = fderiv ℝ (fderiv ℝ f) 0 u v := by
    intro u v
    rw [iteratedFDeriv_two_apply]; rfl
  have hdiag : ∀ v : Vec n, fderiv ℝ (fderiv ℝ f) 0 v v = 2 * quad (coeffs E a) v := fun v => by
    have := hess_diag E ha v
    rw [← this, iteratedFDeriv_two_apply]
  have hherm := coeffs_hermitian E a
  ext i j
  have e1 : p11SecularMatrix D (action E a) i j =
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f 0 ![Pi.single i 1, Pi.single j 1] := rfl
  rw [e1, hB]
  have hsum := hdiag (Pi.single i 1 + Pi.single j 1)
  have hsym := hsymS.eq (Pi.single i 1) (Pi.single j 1)
  have hii := hdiag (Pi.single i 1)
  have hjj := hdiag (Pi.single j 1)
  rw [quad_single] at hsum
  rw [quad_single_self] at hii hjj
  simp only [map_add, add_apply] at hsum
  have hQ : coeffs E a j i = coeffs E a i j := by
    have := hherm.apply i j
    simpa using this
  rw [hQ] at hsum
  linarith

end KAM.Planetary

end
