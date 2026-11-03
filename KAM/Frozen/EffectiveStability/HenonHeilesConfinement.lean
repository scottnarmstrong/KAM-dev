/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.OscillatorAction
import KAM.Provider.EffectiveStability.HenonHeilesConfinement

/-!
# Frozen theorem `KAM.EffectiveStability.henonHeiles_confinement`

Track B literal application (plan §4; CL20 Appendix B). Owner-approved on 2026-11-03 (decision D73;
exact text `docs/tracks/B/FREEZE-PROPOSAL-HH.md`). Frozen and sealed in one pass: the theorem was
already proved as an ordinary theorem from the kernel-checked certificate. Part of the opt-in
application library `KAMHenonHeiles` (D51). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- **Hénon–Heiles confinement** (track B, plan §4 "A first instance with literal acceptance
criteria"; CL20 Appendix B model `H = I₁ - (√2/2) I₂ + q₁² q₂ - q₂³/3`, `q = z.1`, `p = z.2`):
every initial point with both oscillator actions `≤ (1/12500)²` has a Hamiltonian solution on
`(-T₁, T₁)` with `T₁ > 10¹⁰`, unique among solutions on intervals through `0`, whose actions stay
`< 101/10¹⁰` and within `12/10¹⁰` of their initial values for `|t| ≤ 10¹⁰`. -/
theorem henonHeiles_confinement (z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ (1 / 12500) ^ 2) :
    ∃ T₁ : ℝ, 10 ^ 10 < T₁ ∧ ∃ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField
        (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
          (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
            + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField
          (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
            (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
              + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 10 ^ 10 → ∀ j,
        KAM.Planetary.oscillatorAction (z t).2 (z t).1 j < 101 / 10 ^ 10 ∧
        |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
            KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 12 / 10 ^ 10 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.EffectiveStability.henonHeiles_confinement z₀ hz₀
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.EffectiveStability

end
-- FROZEN_ANCHOR_SUFFIX_END
