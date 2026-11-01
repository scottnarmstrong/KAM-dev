/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieSympl

/-!
# Invertibility of `DΓ_t` and gradient transport (blueprint-W `bpW:w3:flow` (iii),
`bpW:w3:symplectic`)

Package W3-FLOW, blueprint labels `bpW:w3:flow`, `bpW:w3:symplectic`.

`lieGammaD_invertible`: `DΓ_t(w)` has a bounded two-sided inverse `B` with `‖B‖ ≤ 2` and
`‖B - I‖ ≤ 20 |t| C ‖w‖²`. `lie_gradient_transport`: if `Ω` is nondegenerate and `DΓ_t(w)` is
`Ω`-symplectic with right inverse `B`, the Hamiltonian field of `P ∘ Γ_t` is `B X_P(Γ_t w)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}
  (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem lieGammaD_invertible (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ∃ B : E →L[ℂ] E, lieGammaD T t w * B = 1 ∧ B * lieGammaD T t w = 1 ∧ ‖B‖ ≤ 2 ∧
      ‖B - 1‖ ≤ 20 * |t| * C * ‖w‖ ^ 2 := by
  have h := norm_lieGammaD_sub_le T hC hT t w hq
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have h1 : ‖lieGammaD T t w - 1‖ ≤ 1 / 2 := by
    change ‖lieGammaD T t w - ContinuousLinearMap.id ℂ E‖ ≤ _
    linarith
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := neumann_inv (lieGammaD T t w) h1
  refine ⟨B, hB1, hB2, hB3, hB4.trans ?_⟩
  have : ‖lieGammaD T t w - 1‖ ≤ 10 * |t| * C * ‖w‖ ^ 2 := h
  linarith

/-- (`bpW:w3:symplectic`, Step Gradient transport) -/
theorem lie_gradient_transport (Ω : E →L[ℂ] E →L[ℂ] ℂ)
    (hnd : ∀ ζ : E, (∀ v, Ω ζ v = 0) → ζ = 0) (A B : E →L[ℂ] E) (hAB : A * B = 1)
    (hsymp : ∀ ξ η, Ω (A ξ) (A η) = Ω ξ η) (dP : E →L[ℂ] ℂ) (X Y : E)
    (hX : ∀ u, dP u = Ω X u) (hY : ∀ v, dP (A v) = Ω Y v) : Y = B X := by
  have : Y - B X = 0 := hnd _ fun v => by
    rw [map_sub, ContinuousLinearMap.sub_apply, ← hY, hX, ← hsymp (B X) v]
    have : A (B X) = X := by
      have := congrArg (fun f => f X) hAB
      simpa using this
    rw [this, sub_self]
  exact sub_eq_zero.1 this

end KAM.Wave

end
