/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Omega

/-!
# Hamiltonian fields and the class `𝒜(U)` (blueprint-W `bpW:w3:hamfield-def`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:hamfield-def`.

Both `P : 𝔚 → ℂ` and the field `X : 𝔚 → 𝔚^+` are maps on `BirkSpace` (weighted coordinates; `X` is
read at weight `p + 1`, so `X(w) ∈ 𝔚^+`, and is paired with `v ∈ 𝔚` through `birkEmbed`):

* `IsBirkHamField a p ha hp U P X`: `DP(w)v = Ω(X(w), v)` on `U`; `birkField_eq` (uniqueness),
  `birkField_coord` (`X(w)_l = -i sgn(l) DP(w) e_{-l}`);
* `IsBirkClassA a p ha hp U P X`: the class `𝒜(U)` (open `ϱ`-invariant `U`, real analytic `P`, field
  `X` analytic into `𝔚^+`); `birkClassA_field_rho` (`X ∘ ϱ = ϱ ∘ X`);
* `birkClassA_iff`: the `∃ X` form `BirkClassA`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable {a p : ℝ}

/-- The pairing `Ω(ι X, v)` of `X ∈ 𝔚^+` (weight `p + 1`) with `v ∈ 𝔚` (weight `p`). -/
def birkOmegaPlus (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (X v : BirkSpace) : ℂ :=
  birkOmega ha hp (birkEmbed a (p + 1) p (by linarith) X) v

theorem birkOmegaPlus_eq (ha : 0 ≤ a) (hp : 0 ≤ p) (X v : BirkSpace) :
    birkOmegaPlus a p ha hp X v = birkOmega ha hp (birkEmbed a (p + 1) p (by linarith) X) v := rfl

theorem norm_birkOmegaPlus_le (ha : 0 ≤ a) (hp : 0 ≤ p) (X v : BirkSpace) :
    ‖birkOmegaPlus a p ha hp X v‖ ≤ ‖X‖ * ‖v‖ := by
  refine (norm_birkOmega_le ha hp _ _).trans ?_
  have h2 : ‖birkEmbed a (p + 1) p (by linarith) X‖ ≤ ‖X‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc _ ≤ 1 * ‖X‖ := by gcongr; exact norm_birkEmbed_le _ _ _ _
      _ = _ := one_mul _
  gcongr

/-- (`bpW:w3:hamfield-def`) `X` is a *Hamiltonian field* of `P` on `U`:
`DP(w)v = Ω(X(w), v)` for `w ∈ U`, `v ∈ 𝔚`; here `P` is complex differentiable on `U`. -/
structure IsBirkHamField (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (U : Set BirkSpace)
    (P : BirkSpace → ℂ) (X : BirkSpace → BirkSpace) : Prop where
  differentiableOn : DifferentiableOn ℂ P U
  deriv_eq : ∀ w ∈ U, ∀ v, fderiv ℂ P w v = birkOmegaPlus a p ha hp (X w) v

/-- (`bpW:w3:hamfield-def`) The class `𝒜(U)`: `U ⊂ 𝔚` open and `ϱ`-invariant, `P` real
(`P(ϱw) = conj P(w)`) and analytic on `U`, `X` its Hamiltonian field, analytic as a map
`U → 𝔚^+` (a map into `BirkSpace` read at weight `p + 1`). -/
structure IsBirkClassA (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (U : Set BirkSpace)
    (P : BirkSpace → ℂ) (X : BirkSpace → BirkSpace) : Prop where
  isOpen : IsOpen U
  rho_mem : ∀ w ∈ U, birkRho w ∈ U
  real : ∀ w ∈ U, P (birkRho w) = conj (P w)
  analytic : AnalyticOnNhd ℂ P U
  field : ∀ w ∈ U, ∀ v, fderiv ℂ P w v = birkOmegaPlus a p ha hp (X w) v
  analytic_field : AnalyticOnNhd ℂ X U

/-- `P ∈ 𝒜(U)`: some field `X` exists. -/
def BirkClassA (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (U : Set BirkSpace) (P : BirkSpace → ℂ) :
    Prop := ∃ X, IsBirkClassA a p ha hp U P X

theorem IsBirkClassA.hamField {ha : 0 ≤ a} {hp : 0 ≤ p} {U : Set BirkSpace} {P : BirkSpace → ℂ}
    {X : BirkSpace → BirkSpace} (h : IsBirkClassA a p ha hp U P X) : IsBirkHamField a p ha hp U P X
        :=
  ⟨h.analytic.differentiableOn, h.field⟩

/-- (`bpW:w3:hamfield-def`) The Hamiltonian field is unique on `U`. -/
theorem birkField_eq {ha : 0 ≤ a} {hp : 0 ≤ p} {U : Set BirkSpace} {P : BirkSpace → ℂ}
    {X X' : BirkSpace → BirkSpace} (h : IsBirkHamField a p ha hp U P X)
    (h' : IsBirkHamField a p ha hp U P X') {w : BirkSpace} (hw : w ∈ U) : X w = X' w := by
  have key : birkEmbed a (p + 1) p (by linarith) (X w) =
      birkEmbed a (p + 1) p (by linarith) (X' w) := by
    rw [← sub_eq_zero]
    refine birkOmega_nondegenerate ha hp (ζ := birkEmbed a (p + 1) p (by linarith) (X w) -
      birkEmbed a (p + 1) p (by linarith) (X' w)) fun v => ?_
    have h1 := h.deriv_eq w hw v
    have h2 := h'.deriv_eq w hw v
    simp only [birkOmegaPlus] at h1 h2
    rw [map_sub, sub_apply, ← h1, ← h2, sub_self]
  exact birkEmbed_injective a (p + 1) p (by linarith) key

/-- (`bpW:w3:hamfield-def`) `X(w)_l = -i sgn(l) DP(w) e_{-l}` in the actual coordinates. -/
theorem birkField_coord {ha : 0 ≤ a} {hp : 0 ≤ p} {U : Set BirkSpace} {P : BirkSpace → ℂ}
    {X : BirkSpace → BirkSpace} (h : IsBirkHamField a p ha hp U P X) {w : BirkSpace} (hw : w ∈ U)
    (l : BirkIdx) :
    birkCoord a (p + 1) (X w) l = -Complex.I * birkSgn l * fderiv ℂ P w (birkUnit a p (birkNeg l))
        := by
  have h1 := h.deriv_eq w hw (birkUnit a p (birkNeg l))
  simp only [birkOmegaPlus] at h1
  rw [h1, birkOmega_unit_neg, birkCoord_birkEmbed]
  have hs := birkSgn_mul_self l
  rw [show -Complex.I * birkSgn l * (Complex.I * birkSgn l * birkCoord a (p + 1) (X w) l) =
      -(Complex.I * Complex.I) * (birkSgn l * birkSgn l) * birkCoord a (p + 1) (X w) l by ring,
    Complex.I_mul_I, hs]
  ring

/-! ### Reality of the field -/

/-- `ϱ` as a continuous `ℝ`-linear map. -/
def birkRhoR : BirkSpace →L[ℝ] BirkSpace :=
  LinearMap.mkContinuous
    { toFun := birkRho
      map_add' := map_add birkRho
      map_smul' := fun c y => by
        ext l
        simp [birkRho_apply, Complex.real_smul, map_mul, Complex.conj_ofReal] }
    1 (fun y => by simp)

@[simp] theorem birkRhoR_apply (y : BirkSpace) : birkRhoR y = birkRho y := rfl

/-- `P ∘ ϱ = conj ∘ P` on an open `ϱ`-invariant set gives `DP(ϱw)(ϱv) = conj (DP(w)v)`. -/
theorem birk_fderiv_rho {U : Set BirkSpace} (hU : IsOpen U) (hρ : ∀ w ∈ U, birkRho w ∈ U)
    {P : BirkSpace → ℂ} (hP : DifferentiableOn ℂ P U) (hreal : ∀ w ∈ U, P (birkRho w) = conj (P w))
    {w : BirkSpace} (hw : w ∈ U) (v : BirkSpace) :
    fderiv ℂ P (birkRho w) (birkRho v) = conj (fderiv ℂ P w v) := by
  have hw' := hρ w hw
  have h1 : HasFDerivAt P (fderiv ℂ P w) w :=
    ((hP w hw).differentiableAt (hU.mem_nhds hw)).hasFDerivAt
  have h2 : HasFDerivAt P (fderiv ℂ P (birkRho w)) (birkRho w) :=
    ((hP _ hw').differentiableAt (hU.mem_nhds hw')).hasFDerivAt
  have h3 : HasFDerivAt (fun y => P (birkRhoR y))
      (((fderiv ℂ P (birkRho w)).restrictScalars ℝ).comp birkRhoR) w :=
    HasFDerivAt.comp w (by simpa using h2.restrictScalars ℝ) birkRhoR.hasFDerivAt
  have h4 : HasFDerivAt (fun y => conj (P y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ P w).restrictScalars ℝ)) w :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp w (h1.restrictScalars ℝ)
  have h5 : HasFDerivAt (fun y => P (birkRhoR y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ P w).restrictScalars ℝ)) w :=
    h4.congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hw] with y hy using hreal y hy)
  have := congrArg (fun L => L v) (h3.unique h5)
  simpa using this

/-- (`bpW:w3:hamfield-def`) For real `P`, the field commutes with `ϱ`: `X(ϱw) = ϱ X(w)`. -/
theorem IsBirkClassA.field_rho {ha : 0 ≤ a} {hp : 0 ≤ p} {U : Set BirkSpace} {P : BirkSpace → ℂ}
    {X : BirkSpace → BirkSpace} (h : IsBirkClassA a p ha hp U P X) {w : BirkSpace} (hw : w ∈ U) :
    X (birkRho w) = birkRho (X w) := by
  have hw' := h.rho_mem w hw
  have key : birkEmbed a (p + 1) p (by linarith) (X (birkRho w)) =
      birkEmbed a (p + 1) p (by linarith) (birkRho (X w)) := by
    rw [← sub_eq_zero]
    refine birkOmega_nondegenerate ha hp fun v' => ?_
    obtain ⟨v, rfl⟩ : ∃ v, birkRho v = v' := ⟨birkRho v', birkRho_birkRho v'⟩
    have e1 := h.field (birkRho w) hw' (birkRho v)
    have e2 := h.field w hw v
    have e3 := birk_fderiv_rho h.isOpen h.rho_mem h.analytic.differentiableOn h.real hw v
    simp only [birkOmegaPlus] at e1 e2
    rw [map_sub, sub_apply, ← e1, ← birkRho_birkEmbed, birkOmega_birkRho, ← e2, e3, sub_self]
  exact birkEmbed_injective a (p + 1) p (by linarith) key

end KAM.Wave

end
