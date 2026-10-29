/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsRegular

/-!
# P Part 5: literal jet nodes (`stepP:p5:be-an`, `stepP:p5:be-jet`)

Unsigned exports of the literal conclusions of the graph nodes `be-an` (holomorphy in `I`,
continuity in `mu` and symmetry of `β̃`) and `be-jet` (each jet of the remainder at `x = 0` is
holomorphic on the tube `D_c`, vanishes on the real open set `V`, hence on `D_c`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {a b : ℕ}

/-- `stepP:p5:be-an`: the averaged jets are holomorphic in `I` and continuous in `(mu, I)`, and
`jetBeta` is symmetric. -/
theorem be_an (d : PGData a b) :
    (∀ mu ∈ Icc 0 d.mu0,
      DifferentiableOn ℂ (jetP0 d mu) (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) ∧
      (∀ j, DifferentiableOn ℂ (fun I => jetOmega d mu I j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) ∧
      (∀ i j, DifferentiableOn ℂ (fun I => jetBeta d mu I i j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) ∧
      ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2),
        (jetBeta d mu I).IsSymm) ∧
    ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) ∧
    (∀ j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) ∧
    (∀ i j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) :=
  ⟨fun _ hmu => ⟨jetP0_differentiableOn d hmu, jetOmega_differentiableOn d hmu,
    jetBeta_differentiableOn d hmu, fun _ hI => jetBeta_isSymm d hmu hI⟩,
    (jet_continuousOn d).1, (jet_continuousOn d).2.1, (jet_continuousOn d).2.2⟩

/-- `stepP:p5:be-jet`: for `mu ∈ [0, mu0]` and `k ≤ 4`, each derivative `∂ₓ^k Q(mu, ·; 0)` of the
remainder is holomorphic on `D_c`, vanishes on the real open set `V`, hence on `D_c`. -/
theorem be_jet (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (k : ℕ) (hk : k ≤ 4)
    (v : Fin k → PGComplexPhase b) :
    DifferentiableOn ℂ (fun I => iteratedFDeriv ℂ k (pgRemainder d mu I) 0 v)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) ∧
    (∀ I ∈ d.V, iteratedFDeriv ℂ k (pgRemainder d mu (KAM.realInclusion a I)) 0 = 0) ∧
    ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2),
      iteratedFDeriv ℂ k (pgRemainder d mu I) 0 = 0 := by
  refine ⟨?_, fun I hI => remainder_jet_real d hmu hI k hk,
    fun I hI => remainder_jet_tube d hmu hI k hk⟩
  have := differentiableOn_slice_jet (isOpen_avgDom d) (pgRemainder_differentiableOn d hmu) k v
  rw [tube_eq_zero_slice] at this
  exact this

end KAM.Planetary

end
