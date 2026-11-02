/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.Holomorphic

/-!
# Equivariance of the flow under translations (`bpW:w5:flow` (iv), step `f-real`)

If `X (z + a) = X z` on `V`, and `V`, `U` are invariant under `z ↦ z + a`, then
`φ^t (w + a) = φ^t w + a` for `w ∈ U`, by uniqueness of the flow (`eq_holoFlow_of_solution`). With
`a = τ_k = (k, 0, 0, 0)`, `k ∈ ℤ²`, and `X = X_F` with `1`-periodic components this is the
equivariance of `bpW:w5:flow` (iv).
-/

@[expose] public section

open Set

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

/-- `φ^t(w + a) = φ^t(w) + a` for translation-invariant fields and domains. -/
theorem holoFlow_translate (a : F) (hXa : ∀ z ∈ V, X (z + a) = X z)
    (hVa : ∀ z ∈ V, z + a ∈ V) (hUa : ∀ z ∈ U, z + a ∈ U) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow X t (w + a) = holoFlow X t w + a := by
  have hwa := hUa w hw
  have key := eq_holoFlow_of_solution h hwa (γ := fun s => holoFlow X s w + a)
    (fun s hs => by
      have := (hasDerivWithinAt_holoFlow h hw hs).add_const a
      have hV : holoFlow X s w ∈ V := h.mem_V_of_ball hw (holoFlow_mem_ball h hw hs)
      simpa [hXa _ hV] using this)
    (fun s hs => hVa _ (h.mem_V_of_ball hw (holoFlow_mem_ball h hw hs)))
    (by simp [holoFlow_zero h hw])
  exact (key t ht).symm

end KAM.Wave
