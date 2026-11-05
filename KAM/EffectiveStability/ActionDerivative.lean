/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Action derivatives of an integrable-plus-remainder Hamiltonian (track B, package B1-TRANSFER)

If `K = N ∘ (actions) + R` near `w`, the integrable part contributes nothing to the derivative of
`K` along the angle directions (torus) or along the rotation of each oscillator (oscillator
case); no differentiability of `N` is assumed. Also the velocity of the oscillator actions along
`X_K`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM Filter Topology

variable {n : ℕ}

/-- If `G` is differentiable at `w` and constant along a curve through `w` with velocity `v`, then
`dG(w) v = 0`. -/
theorem fderiv_eq_zero_of_const_curve {G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {w v : (Fin n → ℝ) × (Fin n → ℝ)} {γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hG : DifferentiableAt ℝ G w) (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = w)
    (hconst : ∀ᶠ s in 𝓝 (0 : ℝ), G (γ s) = G w) : fderiv ℝ G w v = 0 := by
  have h1 : HasDerivAt (G ∘ γ) (fderiv ℝ G w v) 0 := by
    have := (hγ0 ▸ hG).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    simpa [hγ0] using this
  have h2 : HasDerivAt (G ∘ γ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (G w)).congr_of_eventuallyEq hconst
  exact h1.unique h2

/-- The integrable part has no angle derivative. -/
theorem fderiv_angle_eq_of_eventuallyEq {K R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {N : (Fin n → ℝ) → ℝ}
    {w : (Fin n → ℝ) × (Fin n → ℝ)} (hK : DifferentiableAt ℝ K w) (hR : DifferentiableAt ℝ R w)
    (heq : ∀ᶠ x in nhds w, K x = N x.2 + R x) (j : Fin n) :
    fderiv ℝ K w (Pi.single j 1, 0) = fderiv ℝ R w (Pi.single j 1, 0) := by
  set e : (Fin n → ℝ) × (Fin n → ℝ) := (Pi.single j 1, 0)
  set γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun s => w + s • e with hγdef
  have hγ : HasDerivAt γ e 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add w).congr_deriv (by simp)
  have hγ0 : γ 0 = w := by simp [hγdef]
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ {x | K x = N x.2 + R x} :=
    hγ.continuousAt.eventually (by simpa [hγ0] using heq)
  have hG : DifferentiableAt ℝ (K - R) w := hK.sub hR
  have := fderiv_eq_zero_of_const_curve hG hγ hγ0 (by
    filter_upwards [hev] with s hs
    have h0 : (K - R) w = N w.2 := by
      have := heq.self_of_nhds
      simp only [Pi.sub_apply]; linarith
    have hs' : K (γ s) = N (γ s).2 + R (γ s) := hs
    have : (γ s).2 = w.2 := by simp [hγdef, e]
    simp only [Pi.sub_apply, h0]; rw [hs', this]; ring)
  rw [fderiv_sub hK hR, sub_apply] at this
  linarith

/-- Torus action velocity: `(X_K w).2 j = - ∂_{θ_j} K`. -/
theorem hamiltonianVectorField_snd_apply (K : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (w : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    (hamiltonianVectorField K w).2 j = - fderiv ℝ K w (Pi.single j 1, 0) := rfl

/-- The integrable part commutes with each oscillator action. -/
theorem bracket_action_eq_of_eventuallyEq {K R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {N : (Fin n → ℝ) → ℝ} {w : (Fin n → ℝ) × (Fin n → ℝ)} (hK : DifferentiableAt ℝ K w)
    (hR : DifferentiableAt ℝ R w)
    (heq : ∀ᶠ x in nhds w, K x = N (KAM.Planetary.oscillatorAction x.2 x.1) + R x) (j : Fin n) :
    w.1 j * fderiv ℝ K w (0, Pi.single j 1) - w.2 j * fderiv ℝ K w (Pi.single j 1, 0) =
      w.1 j * fderiv ℝ R w (0, Pi.single j 1) - w.2 j * fderiv ℝ R w (Pi.single j 1, 0) := by
  set e₁ : (Fin n → ℝ) × (Fin n → ℝ) := (Pi.single j 1, 0)
  set e₂ : (Fin n → ℝ) × (Fin n → ℝ) := (0, Pi.single j 1)
  set a : ℝ → ℝ := fun θ => w.1 j * (Real.cos θ - 1) + w.2 j * Real.sin θ with ha
  set b : ℝ → ℝ := fun θ => -(w.1 j * Real.sin θ) + w.2 j * (Real.cos θ - 1) with hb
  set γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun θ => w + (a θ • e₁ + b θ • e₂) with hγdef
  have ha' : HasDerivAt a (w.2 j) 0 := by
    exact ((((Real.hasDerivAt_cos 0).sub_const 1).const_mul (w.1 j)).add
      ((Real.hasDerivAt_sin 0).const_mul (w.2 j))).congr_deriv (by simp)
  have hb' : HasDerivAt b (-w.1 j) 0 := by
    exact ((((Real.hasDerivAt_sin 0).const_mul (w.1 j)).neg).add
      (((Real.hasDerivAt_cos 0).sub_const 1).const_mul (w.2 j))).congr_deriv (by simp)
  have hγ : HasDerivAt γ (w.2 j • e₁ + (-w.1 j) • e₂) 0 :=
    (((ha'.smul_const e₁).add (hb'.smul_const e₂)).const_add w).congr_deriv (by simp)
  have hγ0 : γ 0 = w := by simp [hγdef, ha, hb]
  have hact : ∀ θ, KAM.Planetary.oscillatorAction (γ θ).2 (γ θ).1 =
      KAM.Planetary.oscillatorAction w.2 w.1 := by
    intro θ
    funext i
    by_cases hi : i = j
    · subst hi
      have := Real.sin_sq_add_cos_sq θ
      simp only [KAM.Planetary.oscillatorAction, hγdef, ha, hb, e₁, e₂]
      simp
      nlinarith [this]
    · simp [KAM.Planetary.oscillatorAction, hγdef, e₁, e₂, hi]
  have hev :
      ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ {x | K x = N (KAM.Planetary.oscillatorAction x.2 x.1) + R x} :=
    hγ.continuousAt.eventually (by simpa [hγ0] using heq)
  have h0 : (K - R) w = N (KAM.Planetary.oscillatorAction w.2 w.1) := by
    have := heq.self_of_nhds
    simp only [Pi.sub_apply]; linarith
  have key := fderiv_eq_zero_of_const_curve (hK.sub hR) hγ hγ0 (by
    filter_upwards [hev] with s hs
    have hs' : K (γ s) = N (KAM.Planetary.oscillatorAction (γ s).2 (γ s).1) + R (γ s) := hs
    simp only [Pi.sub_apply, h0]; rw [hs', hact]; ring)
  rw [map_add, map_smul, map_smul, fderiv_sub hK hR] at key
  simp only [sub_apply, smul_eq_mul] at key
  linarith

/-- Oscillator action velocity along `X_K`. -/
theorem hasDerivAt_oscillatorAction {K : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {c : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {t : ℝ}
    (hc : HasDerivAt c (KAM.hamiltonianVectorField K (c t)) t) (j : Fin n) :
    HasDerivAt (fun s => KAM.Planetary.oscillatorAction (c s).2 (c s).1 j)
      ((c t).1 j * fderiv ℝ K (c t) (0, Pi.single j 1) -
        (c t).2 j * fderiv ℝ K (c t) (Pi.single j 1, 0)) t := by
  have h1 : HasDerivAt (fun s => (c s).1 j) (fderiv ℝ K (c t) (0, Pi.single j 1)) t :=
    hasDerivAt_pi.1 hc.fst j
  have h2 : HasDerivAt (fun s => (c s).2 j) (-fderiv ℝ K (c t) (Pi.single j 1, 0)) t :=
    hasDerivAt_pi.1 hc.snd j
  have := ((h2.mul h2).add (h1.mul h1)).div_const 2
  simp only [KAM.Planetary.oscillatorAction]
  convert this using 1
  · funext s; simp [sq]
  · ring

end KAM.EffectiveStability

end
