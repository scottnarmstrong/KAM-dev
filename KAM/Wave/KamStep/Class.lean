/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smoothing Hamiltonians and parameter norms (blueprint-W `bpW:w5:class`, `bpW:w5:lambda-product`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`IsSmoothing a p pb V P X`: `P : V → ℂ` is holomorphic, `X : V → 𝒫^{pb}` is holomorphic and
`DP(w)W = ϖ(X(w), W)` (`ϖ = stepSymp` with the weight `pb` of the first and `p` of the second
argument). `X` is unique (`stepSymp_nondeg` in the form `isSmoothing_unique`), so it is *the* field
`X_P`. Holomorphy is that of `bpW:w1:holomorphic` (`DifferentiableOn ℂ`).

`FamBound`: the pair of bounds `|X_{P(ξ)}(w)|_{pb,r} ≤ ε₀`,
`|X_{P(ξ)}(w) - X_{P(ζ)}(w)|_{pb,r} ≤ ε₁|ξ-ζ|` with `ε₀ + λ ε₁ ≤ ε` (the `λ`-norm
`|X|^λ_{r,V} ≤ ε`, read as a conjunction, never as a supremum value), for a family of maps
`(ξ, w) ↦ X ξ w`, and `lamProd_bound` is the submultiplicativity of `bpW:w5:lambda-product`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- **Smoothing Hamiltonians** `𝒮_{p_+}(V)` (`bpW:w5:class`), with `pb = p_+`. -/
structure IsSmoothing {a p pb : ℝ} (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (V : Set KamPhase)
    (P : KamPhase → ℂ) (X : KamPhase → KamPhase) : Prop where
  holoP : DifferentiableOn ℂ P V
  holoX : DifferentiableOn ℂ X V
  deriv_eq : ∀ w ∈ V, ∀ W : KamPhase, fderiv ℂ P w W = stepSymp (q := pb) (q' := p) ha hqq (X w) W

/-- The field is unique (`bpW:w5:class`): `ϖ_{p_+,p}` is nondegenerate. -/
theorem isSmoothing_unique_apply {a p pb : ℝ} (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) {V : Set KamPhase}
    {P : KamPhase → ℂ} {X X' : KamPhase → KamPhase} (h : IsSmoothing (p := p) ha hqq V P X)
    (h' : IsSmoothing (p := p) ha hqq V P X') {w : KamPhase} (hw : w ∈ V) :
    X w = X' w := by
  have key : stepSymp (q := pb) (q' := p) ha hqq (X w - X' w) = fun _ => 0 := funext fun W => by
    rw [stepSymp_sub_left, ← h.deriv_eq w hw W, ← h'.deriv_eq w hw W, sub_self]
  have := stepSymp_nondeg (q := pb) (q' := p) ha hqq (W := X w - X' w) (fun W => congrFun key W)
  exact sub_eq_zero.mp this

/-- A bound `|X_{P(ξ)}(w)|_{p_+,r}` with parameter-Lipschitz part: the conjunction of `ε₀`, `ε₁`
bounds with `ε₀ + λ ε₁ ≤ ε`. -/
def FamBound (Pa : Set (Fin 2 → ℝ)) (V : Set KamPhase) (r lam ε : ℝ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop :=
  ∃ ε₀ ε₁ : ℝ, 0 ≤ ε₀ ∧ 0 ≤ ε₁ ∧ ε₀ + lam * ε₁ ≤ ε ∧
    (∀ ξ ∈ Pa, ∀ w ∈ V, kamNorm r (X ξ w) ≤ ε₀) ∧
    (∀ ξ ∈ Pa, ∀ ζ ∈ Pa, ∀ w ∈ V, kamNorm r (X ξ w - X ζ w) ≤ ε₁ * ‖ξ - ζ‖)

theorem FamBound.mono {Pa : Set (Fin 2 → ℝ)} {V V' : Set KamPhase} {r lam ε ε' : ℝ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (h : FamBound Pa V r lam ε X) (hV : V' ⊆ V)
    (hε : ε ≤ ε') : FamBound Pa V' r lam ε' X := by
  obtain ⟨ε₀, ε₁, h0, h1, hs, hb, hl⟩ := h
  exact ⟨ε₀, ε₁, h0, h1, hs.trans hε, fun ξ hξ w hw => hb ξ hξ w (hV hw),
    fun ξ hξ ζ hζ w hw => hl ξ hξ ζ hζ w (hV hw)⟩

/-- **Products** (`bpW:w5:lambda-product`): the `λ`-norm is submultiplicative. -/
theorem lamProd_bound {lam A₀ A₁ B₀ B₁ : ℝ} (hlam : 0 ≤ lam) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    A₀ * B₀ + lam * (A₁ * B₀ + A₀ * B₁) ≤ (A₀ + lam * A₁) * (B₀ + lam * B₁) := by
  have : 0 ≤ lam * lam * (A₁ * B₁) := by positivity
  nlinarith

end KAM.Wave
