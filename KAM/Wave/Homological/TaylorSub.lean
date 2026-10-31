/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ComponentsAngleQ
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Differences of Taylor Hamiltonians (`bpW:w4:lemma1`, step *Lipschitz*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`HomTaylor.sub R₁ R₂ ∈ 𝒯_s` has the componentwise differences as components; its field is the
difference of the fields (`X_{R₁ - R₂} = X_{R₁} - X_{R₂}`, the fields being linear in the
components), so the Lipschitz hypothesis `|X_{R(ξ)} - X_{R(ζ)}|_r ≤ ε^L |ξ-ζ|` is
`HomFieldBound … (R₁.sub R₂)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p s : ℝ}

theorem IsHomComp.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : ℝ}
    {f g : (Fin 2 → ℂ) → E} (hf : IsHomComp s f) (hg : IsHomComp s g) :
    IsHomComp s (fun z => f z - g z) := by
  obtain ⟨hd, hp, C, hC⟩ := hf
  obtain ⟨hd', hp', C', hC'⟩ := hg
  refine ⟨hd.sub hd', fun i z hz => by simp only [hp i z hz, hp' i z hz], C + C', fun z hz => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (hC z hz) (hC' z hz))

theorem homPartial_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : (Fin 2 → ℂ) → E} {θ : Fin 2 → ℂ} (hu : DifferentiableAt ℂ u θ)
    (hv : DifferentiableAt ℂ v θ) (i : Fin 2) :
    homPartial i (fun z => u z - v z) θ = homPartial i u θ - homPartial i v θ := by
  unfold homPartial
  have := fderiv_sub (𝕜 := ℂ) hu hv
  rw [show (fun z => u z - v z) = u - v from rfl, this]; rfl

theorem homNormalEntry_sub (a p : ℝ) (A B : HomOp) (i j : ℕ+) :
    homNormalEntry a p (A - B) i j = homNormalEntry a p A i j - homNormalEntry a p B i j := by
  simp [homNormalEntry, kamEntry, mul_sub]

/-- The difference `R₁ - R₂ ∈ 𝒯_s`. -/
def HomTaylor.sub (R₁ R₂ : HomTaylor a p s) : HomTaylor a p s where
  a0 := fun z => R₁.a0 z - R₂.a0 z
  b := fun z => R₁.b z - R₂.b z
  cp := fun z => R₁.cp z - R₂.cp z
  cm := fun z => R₁.cm z - R₂.cm z
  P := fun z => R₁.P z - R₂.P z
  P' := fun z => R₁.P' z - R₂.P' z
  Q := fun z => R₁.Q z - R₂.Q z
  Qt := fun z => R₁.Qt z - R₂.Qt z
  comp_a0 := R₁.comp_a0.sub R₂.comp_a0
  comp_b := R₁.comp_b.sub R₂.comp_b
  comp_cp := R₁.comp_cp.sub R₂.comp_cp
  comp_cm := R₁.comp_cm.sub R₂.comp_cm
  comp_P := R₁.comp_P.sub R₂.comp_P
  comp_P' := R₁.comp_P'.sub R₂.comp_P'
  comp_Q := R₁.comp_Q.sub R₂.comp_Q
  comp_Qt := R₁.comp_Qt.sub R₂.comp_Qt
  symP := fun θ hθ i j => by
    simp only [homNormalEntry_sub, R₁.symP θ hθ i j, R₂.symP θ hθ i j]
  symP' := fun θ hθ i j => by
    simp only [homNormalEntry_sub, R₁.symP' θ hθ i j, R₂.symP' θ hθ i j]
  transQ := fun θ hθ i j => by
    simp only [homNormalEntry_sub, R₁.transQ θ hθ i j, R₂.transQ θ hθ i j]

end KAM.Wave
