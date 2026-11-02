/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorSmoothing
public import KAM.Wave.KamStep.TaylorBlocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The components of the Taylor polynomial (blueprint-W `bpW:w5:taylor` (i), step `t-comp`)

Given a smoothing pair `(P, X)` the components of `R` are, at `w₀(θ) = (θ,0,0,0)`:
`a = P(w₀)`, `b = 2π X^θ(w₀)`, `c⁺ = -i X^{z̄}(w₀)`, `c⁻ = i X^z(w₀)`, and `P, P', Q, Q^T` the
blocks of `DX(w₀)` (`TaylorBlocks`). Here: holomorphy and periodicity.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- `θ ↦ (θ, 0, 0, 0)` as a continuous linear map. -/
def stepW0L : (Fin 2 → ℂ) →L[ℂ] KamPhase := ContinuousLinearMap.inl ℂ _ _

theorem stepW0L_apply (θ : Fin 2 → ℂ) : stepW0L θ = (θ, 0, 0, 0) := rfl

theorem stepW0L_mem (hr : 0 < r) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    stepW0L θ ∈ kamDomain s r :=
  ⟨fun i => hθ i, by show ‖(0 : Fin 2 → ℂ)‖ < r ^ 2; rw [norm_zero]; exact pow_pos hr 2,
    by show ‖(0 : HomL2)‖ + ‖(0 : HomL2)‖ < r; rw [norm_zero]; linarith⟩

theorem stepW0L_add_single (θ : Fin 2 → ℂ) (i : Fin 2) :
    stepW0L (θ + Pi.single i 1) = stepW0L θ + stepTau i := by
  simp [stepW0L_apply, stepTau]

/-- The components. -/
def tA0 (P : KamPhase → ℂ) (θ : Fin 2 → ℂ) : ℂ := P (stepW0L θ)
def tB (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => (2 * Real.pi : ℂ) * (X (stepW0L θ)).1 i
def tCp (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomL2 := (-Complex.I) • stepZb (X (stepW0L θ))
def tCm (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomL2 := Complex.I • stepZ (X (stepW0L θ))
def tP (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomOp := blockP (fderiv ℂ X (stepW0L θ))
def tP' (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomOp := blockP' (fderiv ℂ X (stepW0L θ))
def tQ (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomOp := blockQ (fderiv ℂ X (stepW0L θ))
def tQt (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) : HomOp := blockQt (fderiv ℂ X (stepW0L θ))

section hol

variable (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hr : 0 < r)
  (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
  (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w)

include hr hP

theorem tA0_differentiableOn : DifferentiableOn ℂ (tA0 P) (complexStrip 2 s) :=
  hP.holoP.comp stepW0L.differentiable.differentiableOn (fun θ hθ => stepW0L_mem hr hθ)

theorem tXfun_differentiableOn : DifferentiableOn ℂ (fun θ => X (stepW0L θ)) (complexStrip 2 s) :=
  hP.holoX.comp stepW0L.differentiable.differentiableOn (fun θ hθ => stepW0L_mem hr hθ)

theorem tB_differentiableOn : DifferentiableOn ℂ (tB X) (complexStrip 2 s) := by
  have h := tXfun_differentiableOn ha hqq hr hP
  refine differentiableOn_pi.2 fun i => ?_
  have h1 : DifferentiableOn ℂ (fun θ => (X (stepW0L θ)).1 i) (complexStrip 2 s) :=
    (differentiableOn_pi.1 (differentiableOn_fst.comp h (fun _ _ => Set.mem_univ _))) i
  exact (differentiableOn_const _).mul h1

theorem tCp_differentiableOn : DifferentiableOn ℂ (tCp X) (complexStrip 2 s) := by
  have := (stepZb.differentiable.comp_differentiableOn
    (tXfun_differentiableOn ha hqq hr hP)).const_smul (-Complex.I)
  exact this

theorem tCm_differentiableOn : DifferentiableOn ℂ (tCm X) (complexStrip 2 s) := by
  have := (stepZ.differentiable.comp_differentiableOn
    (tXfun_differentiableOn ha hqq hr hP)).const_smul Complex.I
  exact this

theorem tDX_differentiableOn :
    DifferentiableOn ℂ (fun θ => fderiv ℂ X (stepW0L θ)) (complexStrip 2 s) :=
  (differentiableOn_fderiv_of_holomorphic (kamDomain_isOpen s r) hP.holoX).comp
    stepW0L.differentiable.differentiableOn (fun θ hθ => stepW0L_mem hr hθ)

theorem tBlock_differentiableOn (L₁ : KamPhase →L[ℂ] HomL2) (L₂ : HomL2 →L[ℂ] KamPhase) (c : ℂ) :
    DifferentiableOn ℂ (fun θ => c • L₁.comp ((fderiv ℂ X (stepW0L θ)).comp L₂))
      (complexStrip 2 s) := by
  have h := tDX_differentiableOn ha hqq hr hP
  have h2 : DifferentiableOn ℂ (fun θ => (fderiv ℂ X (stepW0L θ)).comp L₂) (complexStrip 2 s) :=
    h.clm_comp (differentiableOn_const _)
  exact ((differentiableOn_const L₁).clm_comp h2).const_smul c

include hper

theorem tA0_periodic (i : Fin 2) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    tA0 P (θ + Pi.single i 1) = tA0 P θ := by
  unfold tA0
  rw [stepW0L_add_single]
  exact hper i _ (stepW0L_mem hr hθ)

theorem tX_periodic (i : Fin 2) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    X (stepW0L (θ + Pi.single i 1)) = X (stepW0L θ) := by
  rw [stepW0L_add_single]
  exact stepField_periodic ha hqq hP hper i (stepW0L_mem hr hθ)

theorem tDX_periodic (i : Fin 2) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    fderiv ℂ X (stepW0L (θ + Pi.single i 1)) = fderiv ℂ X (stepW0L θ) := by
  rw [stepW0L_add_single]
  exact fderiv_field_periodic ha hqq hP hper i (stepW0L_mem hr hθ)

end hol

end KAM.Wave
