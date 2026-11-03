/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.ChartFlow
public import KAM.EffectiveStability.Transfer
public import KAM.EffectiveStability.ActionDerivative
public import KAM.EffectiveStability.Domains
public import KAM.ODE.Uniqueness
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.OscillatorAction

/-!
# Oscillator confinement (track B, B1-E)

Cartesian oscillator confinement, including zero actions: for a Hamiltonian that is, in a
symplectic chart `Ψ`, a function of the oscillator actions plus a remainder whose action
brackets are small, the actions drift by at most `η t` over `|t| ≤ T`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Implementation of the frozen **B1-E** (plan §2.3; CL20 §4.1 (32)–(37)): Cartesian oscillator
confinement, including zero actions. Coordinates are `w = (q, p)`, with action
`KAM.Planetary.oscillatorAction w.2 w.1`, so `I_j = (p_j² + q_j²) / 2` and
`{I_j, R} = q_j ∂_{p_j} R - p_j ∂_{q_j} R`. Rotation invariance of the differentiable function
`H ∘ Ψ - R` gives the normal-part cancellation without differentiating `N`. -/
theorem oscillator_confinement_proof {n : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
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
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = Ψ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ V ∧ HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = Ψ w₀ →
        (∀ t ∈ I, y t ∈ V ∧ HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → Ψ (Ψinv (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (Ψinv (z t)).2 (Ψinv (z t)).1 j ≤ a j + η j * T := by
  set D : Set ((Fin n → ℝ) × (Fin n → ℝ)) := osc (fun j => b j + ε) with hD
  have hDo : IsOpen D := isOpen_osc _
  have hK : ContDiffOn ℝ 2 (H ∘ Ψ) D := hH.comp hΨ (fun w hw => hΨV w hw)
  have hF : ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (H ∘ Ψ)) D :=
    contDiffOn_hamiltonianVectorField hK hDo
  have hKdiff : ∀ x ∈ D, DifferentiableAt ℝ (H ∘ Ψ) x := fun x hx =>
    (hK.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hx)
  have hRdiff : ∀ x ∈ D, DifferentiableAt ℝ R x := fun x hx =>
    hR.differentiableAt (hDo.mem_nhds hx)
  have hset : {x : (Fin n → ℝ) × (Fin n → ℝ) | ∀ j, |oscAct x j| ≤ b j} = oscClosed b := by
    ext x
    simp only [mem_ofPred_eq, oscClosed]
    refine forall_congr' fun j => ?_
    rw [show oscAct x j = KAM.Planetary.oscillatorAction x.2 x.1 j from rfl,
      abs_of_nonneg (oscillatorAction_nonneg _ _ _)]
  have hKc : IsCompact {x : (Fin n → ℝ) × (Fin n → ℝ) | ∀ j, |oscAct x j| ≤ b j} := by
    rw [hset]; exact isCompact_oscClosed b
  have hKW : {x : (Fin n → ℝ) × (Fin n → ℝ) | ∀ j, |oscAct x j| ≤ b j} ⊆ D := by
    rw [hset]; exact oscClosed_subset_osc hε
  have hdrift : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), (∀ j, |oscAct x j| ≤ b j) →
      ∀ j, |fderiv ℝ (oscAct (n := n)) x (KAM.hamiltonianVectorField (H ∘ Ψ) x) j| ≤ η j := by
    intro x hx j
    have hxD : x ∈ D := hKW hx
    have hxc : ∀ j, KAM.Planetary.oscillatorAction x.2 x.1 j ≤ b j := fun i => by
      have := hx i
      rwa [show oscAct x i = KAM.Planetary.oscillatorAction x.2 x.1 i from rfl,
        abs_of_nonneg (oscillatorAction_nonneg _ _ _)] at this
    have heq : ∀ᶠ y in nhds x, (H ∘ Ψ) y =
        N (KAM.Planetary.oscillatorAction y.2 y.1) + R y := by
      filter_upwards [hDo.mem_nhds hxD] with y hy using hHΨ y hy
    have hb := bracket_action_eq_of_eventuallyEq (hKdiff x hxD) (hRdiff x hxD) heq j
    rw [fderiv_oscAct]
    have e : x.1 j * (KAM.hamiltonianVectorField (H ∘ Ψ) x).1 j +
        x.2 j * (KAM.hamiltonianVectorField (H ∘ Ψ) x).2 j =
        x.1 j * fderiv ℝ (H ∘ Ψ) x (0, Pi.single j 1) -
          x.2 j * fderiv ℝ (H ∘ Ψ) x (Pi.single j 1, 0) := by
      simp only [KAM.hamiltonianVectorField]; ring
    show |x.1 j * (KAM.hamiltonianVectorField (H ∘ Ψ) x).1 j +
        x.2 j * (KAM.hamiltonianVectorField (H ∘ Ψ) x).2 j| ≤ η j
    rw [e, hb]
    exact hRη x hxc j
  have hw0a : ∀ j, |oscAct w₀ j| ≤ a j := fun j => by
    rw [show oscAct w₀ j = KAM.Planetary.oscillatorAction w₀.2 w₀.1 j from rfl,
      abs_of_nonneg (oscillatorAction_nonneg _ _ _)]
    exact hw₀ j
  obtain ⟨T₁, hT₁, w, hw0, hsol, hbd⟩ := exists_confined_solution_compact hDo hF oscAct
    (fun x _ => (contDiff_oscAct.differentiable (by simp)) x) hT hη hmargin hKc hKW hdrift
    w₀ hw0a
  have hT₁pos : 0 < T₁ := lt_of_le_of_lt hT hT₁
  have hwD : ∀ t ∈ Ioo (-T₁) T₁, w t ∈ D := fun t ht => (hsol t ht).1
  have hzsol : ∀ t ∈ Ioo (-T₁) T₁, Ψ (w t) ∈ V ∧
      HasDerivAt (fun s => Ψ (w s)) (KAM.hamiltonianVectorField H (Ψ (w t))) t := by
    intro t ht
    have hwt := hwD t ht
    have hΨd : DifferentiableAt ℝ Ψ (w t) :=
      (hΨ.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hwt)
    have hHd : DifferentiableAt ℝ H (Ψ (w t)) :=
      (hH.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds (hΨV _ hwt))
    exact ⟨hΨV _ hwt, hasDerivAt_comp_chart (hsol t ht).2 hΨd hHd (hΨsymp _ hwt)⟩
  refine ⟨T₁, hT₁, fun t => Ψ (w t), by simp [hw0], hzsol, ?_, ?_⟩
  · intro I y hI h0 hy0 hy t htI htT
    have hu := KAM.ODE.gen_uniqueness_inter hV (contDiffOn_hamiltonianVectorField hH hV) hI
      (ordConnected_Ioo (a := -T₁) (b := T₁)) (t₀ := 0) ⟨h0, by constructor <;> linarith⟩
      (y₁ := y) (y₂ := fun s => Ψ (w s)) hy hzsol (by simp [hy0, hw0])
    exact hu ⟨htI, htT⟩
  · intro t htT
    have htm : t ∈ Ioo (-T₁) T₁ := by
      have := abs_le.1 htT
      constructor <;> linarith [this.1, this.2]
    have hwt : w t ∈ D := hwD t htm
    have e : Ψinv (Ψ (w t)) = w t := hΨinv _ hwt
    refine ⟨by simp only [e], fun j => ?_⟩
    have h1 := hbd t htT j
    simp only [e]
    refine ⟨h1.1, ?_⟩
    exact (le_abs_self _).trans h1.2
end KAM.EffectiveStability
