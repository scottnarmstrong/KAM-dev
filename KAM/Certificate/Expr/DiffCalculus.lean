/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Basic
public import KAM.Certificate.Expr.Slp
public import KAM.Certificate.PhaseBasis

/-!
# Directional derivatives on an open set

The calculus behind the symbolic jet (`KAM.Certificate.Expr.Diff`): the directional derivative
`jetDeriv u f z = fderiv ℂ f z u` of a function on the phase space, closure of smoothness on an
open set under it, its product, sum, `exp` and inverse rules as equalities on the set, the
coordinate directions `dirVec n i` (`i < 2n`, with `phaseBasis a = dirVec n (phaseNat a)`), and the
identification of the second iterated derivative with an iterated directional derivative.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM.Torus

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-- The derivative of `f` in the direction `u`. -/
def jetDeriv (u : Ph) (f : Ph → ℂ) : Ph → ℂ := fun z => fderiv ℂ f z u

/-- Smoothness (`C^∞`) of a function on a set. -/
def JetSmoothOn (S : Set Ph) (f : Ph → ℂ) : Prop :=
  ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) f S

theorem JetSmoothOn.differentiableAt {S : Set Ph} {f : Ph → ℂ} (hS : IsOpen S)
    (hf : JetSmoothOn S f) {z : Ph} (hz : z ∈ S) : DifferentiableAt ℂ f z :=
  (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)

theorem JetSmoothOn.jetDeriv {S : Set Ph} {f : Ph → ℂ} (hS : IsOpen S) (hf : JetSmoothOn S f)
    (u : Ph) : JetSmoothOn S (jetDeriv u f) := by
  have h := hf.fderiv_of_isOpen hS (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  exact h.clm_apply contDiffOn_const

theorem JetSmoothOn.add {S : Set Ph} {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) : JetSmoothOn S (fun z => f z + g z) := ContDiffOn.add hf hg

theorem JetSmoothOn.mul {S : Set Ph} {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) : JetSmoothOn S (fun z => f z * g z) := ContDiffOn.mul hf hg

theorem JetSmoothOn.cexp {S : Set Ph} {f : Ph → ℂ} (hf : JetSmoothOn S f) :
    JetSmoothOn S (fun z => Complex.exp (f z)) := ContDiffOn.cexp hf

theorem JetSmoothOn.inv {S : Set Ph} {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (h0 : ∀ z ∈ S, f z ≠ 0) : JetSmoothOn S (fun z => (f z)⁻¹) :=
  ContDiffOn.inv hf h0

theorem JetSmoothOn.const (S : Set Ph) (c : ℂ) : JetSmoothOn S (fun _ => c) := contDiffOn_const

theorem JetSmoothOn.congr {S : Set Ph} {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (h : Set.EqOn g f S) : JetSmoothOn S g := ContDiffOn.congr hf h

theorem jetDeriv_const (u : Ph) (c : ℂ) : jetDeriv u (fun _ => c) = fun _ => 0 := by
  funext z; simp [jetDeriv]

theorem jetDeriv_congr {S : Set Ph} (hS : IsOpen S) (u : Ph) {F G : Ph → ℂ}
    (h : Set.EqOn F G S) : Set.EqOn (jetDeriv u F) (jetDeriv u G) S := by
  intro z hz
  have : F =ᶠ[nhds z] G := Filter.eventually_of_mem (hS.mem_nhds hz) h
  simp only [jetDeriv, this.fderiv_eq]

theorem jetDeriv_add {S : Set Ph} (hS : IsOpen S) (u : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (fun z => f z + g z)) (fun z => jetDeriv u f z + jetDeriv u g z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  have h2 := hg.differentiableAt hS hz
  simp only [jetDeriv]
  have e : fderiv ℂ (fun z => f z + g z) z = fderiv ℂ f z + fderiv ℂ g z :=
    (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  rw [e]
  rfl

theorem jetDeriv_mul {S : Set Ph} (hS : IsOpen S) (u : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (fun z => f z * g z))
      (fun z => jetDeriv u f z * g z + f z * jetDeriv u g z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  have h2 := hg.differentiableAt hS hz
  simp only [jetDeriv]
  have e : fderiv ℂ (fun z => f z * g z) z =
      f z • fderiv ℂ g z + g z • fderiv ℂ f z := (h1.hasFDerivAt.mul h2.hasFDerivAt).fderiv
  rw [e]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem jetDeriv_cexp {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (fun z => Complex.exp (f z)))
      (fun z => Complex.exp (f z) * jetDeriv u f z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  simp only [jetDeriv]
  rw [h1.hasFDerivAt.cexp.fderiv]
  simp

theorem jetDeriv_inv {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (fun z => (f z)⁻¹))
      (fun z => -((f z)⁻¹ * (f z)⁻¹) * jetDeriv u f z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  simp only [jetDeriv]
  have := (hasDerivAt_inv (h0 z hz)).comp_hasFDerivAt z h1.hasFDerivAt
  have e : fderiv ℂ (fun z => (f z)⁻¹) z = -(f z ^ 2)⁻¹ • fderiv ℂ f z := this.fderiv
  rw [e]
  simp only [smul_apply, smul_eq_mul]
  rw [sq, mul_inv]

/-- The coordinate direction `i`: the angle `i` for `i < n`, the action `i - n` for `n ≤ i < 2n`
(and `0` beyond). -/
def dirVec (n : ℕ) (i : ℕ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  if h : i < n then (Pi.single ⟨i, h⟩ 1, 0)
  else if h2 : i - n < n then (0, Pi.single ⟨i - n, h2⟩ 1) else 0

theorem phaseBasis_eq_dirVec (a : Fin n ⊕ Fin n) : phaseBasis a = dirVec n (phaseNat a) := by
  cases a with
  | inl j =>
    simp only [phaseNat, dirVec, j.isLt]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · by_cases h : i = j <;> simp [phaseBasis, sumVec, h]
    · simp [phaseBasis, sumVec]
  | inr j =>
    rw [phaseBasis_inr]
    have e : dirVec n (n + j.val) = (0, Pi.single j 1) := by simp [dirVec]
    exact e.symm

theorem phaseNat_lt (a : Fin n ⊕ Fin n) : phaseNat a < 2 * n := by
  cases a with
  | inl j => have := j.isLt; simp only [phaseNat]; omega
  | inr j => have := j.isLt; simp only [phaseNat]; omega

/-- The second iterated derivative is an iterated directional derivative. -/
theorem iteratedFDeriv_two_eq_jetDeriv {f : Ph → ℂ} {z : Ph} (hf : ContDiffAt ℂ 2 f z)
    (u v : Ph) :
    iteratedFDeriv ℂ 2 f z ![u, v] = jetDeriv u (jetDeriv v f) z := by
  rw [iteratedFDeriv_two_apply]
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 := fderiv_clm_apply h1 (differentiableAt_const v)
  have e : jetDeriv v f = fun y => fderiv ℂ f y v := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [jetDeriv, e]
  rw [h2]
  simp

end KAM.Certificate

end
