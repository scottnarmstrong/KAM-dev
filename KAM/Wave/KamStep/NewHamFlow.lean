/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamExp
public import KAM.Wave.KamStep.FlowTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The expansion of `H ∘ Φ` along the flow (blueprint-W `bpW:w5:new-ham` (i), step `n-exp`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepNewHam_flow`: for a flow with `FlowHyp`, `C¹` functions `N, N̂, R` (derivatives `DN, DN̂, DR` on
`V`) with `DN·X = N̂ + â₀ - R` on `V` (the homological equation through W4's bracket identity), and
continuous brackets along the trajectory,
`N(Φ w) = N(w) + N̂(w) + â₀ - R(w) + ∫₀¹ (1-τ)(DN̂·X - DR·X)(φ^τ w) dτ`, `Φ = φ¹`; and the version
`stepNewHam_flow_H` with an arbitrary `P(Φ w)`.
-/

@[expose] public section

open Set Metric

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ}

/-- **`H ∘ Φ`, expansion along the flow** (`bpW:w5:new-ham` (i), `n-exp`, abstract in `F`). -/
theorem stepNewHam_flow_H (h : FlowHyp X V U M δ) {N N' R P : F → ℂ} {DN DN' DR : F → F →L[ℂ] ℂ}
    {a0 : ℂ} (hN : ∀ z ∈ V, HasFDerivAt N (DN z) z) (hN' : ∀ z ∈ V, HasFDerivAt N' (DN' z) z)
    (hR : ∀ z ∈ V, HasFDerivAt R (DR z) z)
    (heq : ∀ z ∈ V, DN z (X z) = N' z + a0 - R z) {w : F} (hw : w ∈ U)
    (hbn : ContinuousOn (fun t : ℝ => DN' (holoFlow X t w) (X (holoFlow X t w))) (Icc 0 1))
    (hbr : ContinuousOn (fun t : ℝ => DR (holoFlow X t w) (X (holoFlow X t w))) (Icc 0 1)) :
    N (holoFlow X 1 w) + P (holoFlow X 1 w) =
      N w + N' w + a0 + (P (holoFlow X 1 w) - R (holoFlow X 1 w)) +
        ∫ τ in (0 : ℝ)..1, ((1 - τ) • DN' (holoFlow X τ w) (X (holoFlow X τ w)) +
          τ • DR (holoFlow X τ w) (X (holoFlow X τ w))) := by
  have hmem : ∀ t ∈ Icc (-1 : ℝ) 1, holoFlow X t w ∈ V := fun t ht =>
    h.mem_V_of_ball hw (holoFlow_mem_ball h hw ht)
  have hI : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Icc (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hder : ∀ {G : F → ℂ} {DG : F → F →L[ℂ] ℂ}, (∀ z ∈ V, HasFDerivAt G (DG z) z) →
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => G (holoFlow X s w))
        (DG (holoFlow X t w) (X (holoFlow X t w))) (Icc 0 1) t := fun hG t ht =>
    ((hasDerivWithinAt_comp_holoFlow h hw (hI t ht) (hG _ (hmem t (hI t ht)))).mono
      (fun s hs => hI s hs))
  have h0 := stepExpansion_H (n := fun t => N (holoFlow X t w)) (nu := fun t => N' (holoFlow X t w))
    (rho := fun t => R (holoFlow X t w))
    (bn := fun t => DN' (holoFlow X t w) (X (holoFlow X t w)))
    (br := fun t => DR (holoFlow X t w) (X (holoFlow X t w))) (a0 := a0)
    (p1 := P (holoFlow X 1 w)) hbn hbr
    (fun t ht => by
      have := hder hN t ht
      rwa [heq _ (hmem t (hI t ht))] at this)
    (hder hN') (hder hR)
  rw [holoFlow_zero h hw] at h0
  exact h0

end KAM.Wave
