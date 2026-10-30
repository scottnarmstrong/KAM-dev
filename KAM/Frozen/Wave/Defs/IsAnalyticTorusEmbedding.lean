/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Frozen definition `KAM.Wave.IsAnalyticTorusEmbedding`

Blueprint-W Definition `bpW:wh:embedding`. Real analyticity is Mathlib's `AnalyticOnNhd ℝ`
(locally a convergent power series with values in the real Banach space `E`); for Banach-space
targets this is equivalent to being locally the restriction of a holomorphic map into the
complexification, the form written in the blueprint.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `K : ℝ² → E` is an analytic torus embedding: `ℤ²`-periodic, real analytic, injective modulo
`ℤ²`, with injective derivative everywhere (blueprint-W `bpW:wh:embedding`). -/
def IsAnalyticTorusEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : (Fin 2 → ℝ) → E) : Prop :=
  (∀ (k : Fin 2 → ℤ) (θ : Fin 2 → ℝ), K (θ + fun i => (k i : ℝ)) = K θ) ∧
  AnalyticOnNhd ℝ K Set.univ ∧
  (∀ θ θ' : Fin 2 → ℝ, K θ = K θ' → ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ)) ∧
  ∀ θ : Fin 2 → ℝ, Function.Injective (fderiv ℝ K θ)

end KAM.Wave

end
