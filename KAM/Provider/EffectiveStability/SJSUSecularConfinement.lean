/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Confinement.Proof

/-!
# Provider for `KAM.EffectiveStability.sjsu_secular_confinement`

Provider for the frozen theorem `KAM.EffectiveStability.sjsu_secular_confinement`
(T2-CONF; decision D76). It states the anchor's exact type (the statement text verbatim,
read with `open KAM.EffectiveStability`, so that `sjsu18O2` is the frozen Hamiltonian),
and it is proved in one line by the implementation theorem
`KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof`.
This module is quarantined: no module other than the anchor may import it
(AGENTS rule 9).
-/

@[expose] public noncomputable section

namespace KAM.Provider.EffectiveStability

open KAM.EffectiveStability

theorem sjsu_secular_confinement (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j, |z₀.2 j - ![0.03446271128616895, -0.0014352339355918572, -0.010122263133599879] j| ≤ 1 / 10 ^ 6 ∧
      |z₀.1 j - ![-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881] j| ≤ 1 / 10 ^ 6) :
    ∃ T₁ : ℝ, 5 * 10 ^ 9 < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 5 * 10 ^ 9 → ∀ j,
        ![0.026, 0.009, 0.006] j ≤ Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j / ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ∧
        Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j / ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof z₀ hz₀

end KAM.Provider.EffectiveStability

end
