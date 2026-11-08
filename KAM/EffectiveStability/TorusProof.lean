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
# Torus confinement proof (track B, B1-T)

Finite confinement of the actions in a canonical cylinder, for a Hamiltonian that is, in a
symplectic chart `Ψ`, the sum of a normal part depending only on the actions and an
angle-periodic remainder with small angle derivative.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Implementation of the frozen **B1-T** (plan §2.2; GLS17 §4.3 (56)–(58)): finite confinement in a
canonical cylinder. The physical phase coordinates are lifted real coordinates. Only the pullback
Hamiltonian must be angle-periodic. The normal part is differentiated through `H ∘ Ψ - R`, which is
differentiable on the open chart domain; no differentiability hypothesis on `N` is needed. -/
theorem torus_confinement_proof {n : ℕ} (a b η : Fin n → ℝ) (ε T : ℝ) (hε : 0 < ε) (hT : 0 ≤ T)
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
        ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧ |(Ψinv (z t)).2 j| ≤ a j + η j * T := by
  set D : Set ((Fin n → ℝ) × (Fin n → ℝ)) := cyl (fun j => b j + ε) with hD
  have hDo : IsOpen D := isOpen_cyl _
  have hmemD : ∀ w, w ∈ D ↔ ∀ j, |w.2 j| < b j + ε := fun w => Iff.rfl
  have hK : ContDiffOn ℝ 2 (H ∘ Ψ) D := hH.comp hΨ (fun w hw => hΨV w hw)
  have hF : ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (H ∘ Ψ)) D :=
    contDiffOn_hamiltonianVectorField hK hDo
  have hKdiff : ∀ x ∈ D, DifferentiableAt ℝ (H ∘ Ψ) x := fun x hx =>
    (hK.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hx)
  have hRdiff : ∀ x ∈ D, DifferentiableAt ℝ R x := fun x hx =>
    hR.differentiableAt (hDo.mem_nhds hx)
  -- periodicity of the pullback Hamiltonian
  have hKper : ∀ (k : Fin n → ℤ), ∀ x ∈ D, (H ∘ Ψ) (x + KAM.ODE.angleShift k) = (H ∘ Ψ) x := by
    intro k x hx
    have hx' : x + KAM.ODE.angleShift k ∈ D := add_angleShift_mem_cyl hx k
    simp only [Function.comp_apply]
    rw [hHΨ _ hx', hHΨ _ hx]
    have h2 : (x + KAM.ODE.angleShift k).2 = x.2 := by simp [KAM.ODE.angleShift]
    rw [h2]
    have := hRper k x hx
    exact congrArg _ this
  have hFper : ∀ k : Fin n → ℤ, ∀ x ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ actionBox (fun j => b j + ε),
      KAM.hamiltonianVectorField (H ∘ Ψ) (x + KAM.ODE.angleShift k) =
        KAM.hamiltonianVectorField (H ∘ Ψ) x := by
    intro k x hx
    rw [← cyl_eq_prod] at hx
    have hev : (fun y => (H ∘ Ψ) (y + KAM.ODE.angleShift k)) =ᶠ[nhds x] (H ∘ Ψ) := by
      filter_upwards [hDo.mem_nhds hx] with y hy using hKper k y hy
    have hd : fderiv ℝ (H ∘ Ψ) (x + KAM.ODE.angleShift k) = fderiv ℝ (H ∘ Ψ) x := by
      rw [← fderiv_comp_add_right]
      exact hev.fderiv_eq
    simp only [KAM.hamiltonianVectorField, hd]
  -- drift of the actions
  have hdrift : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      x ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ actionBox (fun j => b j + ε) →
      (∀ j, |x.2 j| ≤ b j) → ∀ j, |(KAM.hamiltonianVectorField (H ∘ Ψ) x).2 j| ≤ η j := by
    intro x hx hxb j
    rw [← cyl_eq_prod] at hx
    have heq : ∀ᶠ y in nhds x, (H ∘ Ψ) y = N y.2 + R y := by
      filter_upwards [hDo.mem_nhds hx] with y hy using hHΨ y hy
    have := fderiv_angle_eq_of_eventuallyEq (hKdiff x hx) (hRdiff x hx) heq j
    show |(-fderiv ℝ (H ∘ Ψ) x (Pi.single j 1, 0))| ≤ η j
    rw [this, abs_neg]
    exact hRη x hxb j
  obtain ⟨T₁, hT₁, w, hw0, hsol, hbd⟩ := exists_confined_solution_periodic
    (isOpen_actionBox (fun j => b j + ε)) (by rwa [← cyl_eq_prod]) hFper hT hη hmargin
    (actionBoxClosed_subset_actionBox hε) hdrift w₀ hw₀
  have hT₁pos : 0 < T₁ := lt_of_le_of_lt hT hT₁
  have hwD : ∀ t ∈ Ioo (-T₁) T₁, w t ∈ D := fun t ht => by
    rw [hD, cyl_eq_prod]; exact (hsol t ht).1
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
    have := hbd t htT j
    simp only [e] at this ⊢
    exact this
end KAM.EffectiveStability
