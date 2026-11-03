/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusProof

/-!
# Provider for `KAM.EffectiveStability.torus_confinement`

Provider for the frozen theorem `KAM.EffectiveStability.torus_confinement` (B1-T, track B; plan
§2.2; GLS17 §4.3 (56)–(58); decision D72). It states the anchor's exact type and is proved in one
line by the implementation theorem `KAM.EffectiveStability.torus_confinement_proof`. This module is
quarantined: no module other than the anchor may import it (AGENTS rule 9).
-/

@[expose] public noncomputable section

namespace KAM.Provider.EffectiveStability

open Set

theorem torus_confinement {n : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : ContDiffOn ℝ 2 Ψ {w | ∀ j, |w.2 j| < b j + ε})
    (hΨV : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) → Ψ w ∈ V)
    (hΨsymp : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = KAM.symplecticForm u v)
    (hΨinv : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) → Ψinv (Ψ w) = w)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, |w.2 j| < b j + ε})
    (hRper : ∀ (k : Fin n → ℤ) (w : (Fin n → ℝ) × (Fin n → ℝ)), (∀ j, |w.2 j| < b j + ε) →
      R (w + (fun i => (k i : ℝ), 0)) = R w)
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| < b j + ε) →
      H (Ψ w) = N w.2 + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| ≤ b j) →
      ∀ j, |fderiv ℝ R w (Pi.single j 1, 0)| ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧ |(Ψinv (z t)).2 j| ≤ a j + η j * T :=
  KAM.EffectiveStability.torus_confinement_proof a b η ε T hε hT hη hmargin V hV H hH Ψ Ψinv hΨ hΨV
    hΨsymp hΨinv N R hR hRper hHΨ hRη w₀ hw₀

end KAM.Provider.EffectiveStability

end
