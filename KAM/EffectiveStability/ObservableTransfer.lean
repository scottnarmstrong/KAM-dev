/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Torus
public import KAM.EffectiveStability.Oscillator

/-!
# Observable transfer corollaries (track B)

Under the hypotheses of the two headline confinement theorems and an observable `A` that is
affine in the actions up to an error `d` on the closed action domain, the observable along the
physical solution moves by at most `2 d + |t| ∑ |L i j| η j`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Observable transfer for `torus_confinement`: the headline solution `z` also controls the
observable `A`. -/
theorem torus_observable_transfer {n m : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
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
    (A : (Fin n → ℝ) × (Fin n → ℝ) → Fin m → ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ)
    (hA : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |w.2 j| ≤ b j) →
      ∀ i, |A (Ψ w) i - (L.mulVec w.2) i| ≤ d i)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      (∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧ |(Ψinv (z t)).2 j| ≤ a j + η j * T) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ i, |A (z t) i - A (z 0) i| ≤ 2 * d i + |t| * ∑ j, |L i j| * η j := by
  obtain ⟨T₁, hT₁, z, h0, hs, hu, hb⟩ :=
    torus_confinement a b η ε T hε hT hη hmargin V hV H hH Ψ Ψinv
      hΨ hΨV hΨsymp hΨinv N R hR hRper hHΨ hRη w₀ hw₀
  refine ⟨T₁, hT₁, z, h0, hs, hu, hb, fun t ht i => ?_⟩
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := hmargin j; have := mul_nonneg hT (hη j); linarith
  obtain ⟨hz, hJ⟩ := hb t ht
  have hJb : ∀ j, |(Ψinv (z t)).2 j| ≤ b j := fun j => by
    have := (hJ j).2
    have h1 := hmargin j
    have h2 : η j * T = T * η j := mul_comm _ _
    linarith
  refine observable_transfer_bound A L d η t (z 0) (z t) w₀.2 (Ψinv (z t)).2 ?_ ?_
    (fun j => (hJ j).1) i
  · rw [h0]; exact hA w₀ (fun j => (hw₀ j).trans (hab j))
  · have := hA (Ψinv (z t)) hJb
    rwa [hz] at this

/-- Observable transfer for `oscillator_confinement`: the headline solution `z` also controls the
observable `A`. -/
theorem oscillator_observable_transfer {n m : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε)
    (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j)
    (V : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hV : IsOpen V)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hH : ContDiffOn ℝ 2 H V)
    (Ψ Ψinv : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hΨ : ContDiffOn ℝ 2 Ψ {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε})
    (hΨV : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) → Ψ w ∈ V)
    (hΨsymp : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) →
      ∀ u v, KAM.symplecticForm (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = KAM.symplecticForm u v)
    (hΨinv : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) → Ψinv (Ψ w) = w)
    (N : (Fin n → ℝ) → ℝ) (R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hR : DifferentiableOn ℝ R {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε})
    (hHΨ : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < b j + ε) →
      H (Ψ w) = N (KAM.Planetary.oscillatorAction w.2 w.1) + R w)
    (hRη : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
      (∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j ≤ b j) →
      ∀ j, |w.1 j * fderiv ℝ R w (0, Pi.single j 1) - w.2 j * fderiv ℝ R w (Pi.single j 1, 0)|
        ≤ η j)
    (A : (Fin n → ℝ) × (Fin n → ℝ) → Fin m → ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ)
    (hA : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), w ∈ oscClosed b →
      ∀ i, |A (Ψ w) i - (L.mulVec (oscAct w)) i| ≤ d i)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      (∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j ≤ a j + η j * T) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ i, |A (z t) i - A (z 0) i| ≤ 2 * d i + |t| * ∑ j, |L i j| * η j := by
  obtain ⟨T₁, hT₁, z, h0, hs, hu, hb⟩ := oscillator_confinement a b η ε T hε hT hη hmargin V hV H hH
    Ψ Ψinv hΨ hΨV hΨsymp hΨinv N R hR hHΨ hRη w₀ hw₀
  refine ⟨T₁, hT₁, z, h0, hs, hu, hb, fun t ht i => ?_⟩
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := hmargin j; have := mul_nonneg hT (hη j); linarith
  obtain ⟨hz, hJ⟩ := hb t ht
  have hJb : Ψinv (z t) ∈ oscClosed b := fun j => by
    have := (hJ j).2
    have h1 := hmargin j
    have h2 : η j * T = T * η j := mul_comm _ _
    linarith
  refine observable_transfer_bound A L d η t (z 0) (z t) (oscAct w₀) (oscAct (Ψinv (z t))) ?_ ?_
    (fun j => (hJ j).1) i
  · rw [h0]; exact hA w₀ (fun j => (hw₀ j).trans (hab j))
  · have := hA (Ψinv (z t)) hJb
    rwa [hz] at this

end KAM.EffectiveStability
