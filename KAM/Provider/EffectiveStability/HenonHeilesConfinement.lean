/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Confinement

/-!
# Provider for `KAM.EffectiveStability.henonHeiles_confinement`

Provider for the frozen theorem `KAM.EffectiveStability.henonHeiles_confinement` (track B literal
application; decision D73). It states the anchor's exact type and is proved in one line by the
implementation theorem `KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof`. This
module is quarantined: no module other than the anchor may import it (AGENTS rule 9).
-/

@[expose] public noncomputable section

namespace KAM.Provider.EffectiveStability

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
  KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof z₀ hz₀

end KAM.Provider.EffectiveStability

end
