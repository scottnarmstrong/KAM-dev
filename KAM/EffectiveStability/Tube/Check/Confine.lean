/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Confinement.ApproxIntegral
public import KAM.EffectiveStability.Tube.Check.Solution

/-!
# Abstract tube confinement (T2-CONF, N5b)

The generic assembly of the tube checker, with every literal check replaced by an abstract numeric
hypothesis. Data: observables `F j` and action deviations `u j` (`j : Fin m`), centres `c j`, a
half-width `δ` and a tube radius `ρ` (`κδ`). The domain is

  `D = tubeDomain W F u c δ ρ = {x ∈ W | ∀ j, |F_j x - c_j| < δ ∧ |u_j x| < ρ}`,

and `K` is a compact subset of the open `W` containing every `x ∈ W` with `|u_j x| ≤ ρ` for all `j`.

* **Frontier separation from a face bound.** If `|F_j - c_j - u_j| ≤ ε_j` on `K` with
  `δ + ε_j < ρ`, every frontier point of `D` has some `j` with `|F_j - c_j| ≥ δ`
  (`exists_ge_of_mem_frontier`): on the faces `|u_j| = ρ` the face bound gives `|F_j - c_j| > δ`,
  which a closure point of `D` cannot have.
* **Confinement** (`tube_confinement`): with rates `|dF_j(X_H)| ≤ η_j` on `K`, `T η_j < δ/2`, and an
  initial set `Q` on which `|F_j - c_j| ≤ δ/2` and `|u_j| < ρ`, every `z₀ ∈ Q` has a solution on
  `(-T₁, T₁)`, `T₁ > T`, unique among all solutions through `z₀`, staying in `D ⊆ K` for `|t| ≤ T`
  with drift `|F_j(z(t)) - F_j(z₀)| ≤ η_j |t|`. This applies
  `KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement` with `a = c - δ/2`,
  `b = c + δ/2`, then `hamiltonian_solution_of_maximal`.
* `tube_confinement_observable`: any property holding on `K` holds along the solution for `|t| ≤ T`
  (the eccentricity transfer).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Set Filter Topology KAM.ODE

variable {n m : ℕ}

/-- The tube domain `{x ∈ W | ∀ j, |F_j x - c_j| < δ ∧ |u_j x| < ρ}`. -/
def tubeDomain (W : Set ((Fin n → ℝ) × (Fin n → ℝ))) (F u : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (c : Fin m → ℝ) (δ ρ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | x ∈ W ∧ (∀ j, |F j x - c j| < δ) ∧ ∀ j, |u j x| < ρ}

section Domain

variable {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} {F u : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
  {c : Fin m → ℝ} {δ ρ : ℝ}

theorem isOpen_tubeDomain (hW : IsOpen W) (hF : ∀ j, ContinuousOn (F j) W)
    (hu : ∀ j, ContinuousOn (u j) W) : IsOpen (tubeDomain W F u c δ ρ) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxW : W ∈ 𝓝 x := hW.mem_nhds hx.1
  have h1 : ∀ᶠ y in 𝓝 x, ∀ j, |F j y - c j| < δ := eventually_all.2 fun j =>
    ((((hF j).continuousAt hxW).sub continuousAt_const).abs).eventually_lt continuousAt_const
      (hx.2.1 j)
  have h2 : ∀ᶠ y in 𝓝 x, ∀ j, |u j y| < ρ := eventually_all.2 fun j =>
    (((hu j).continuousAt hxW).abs).eventually_lt continuousAt_const (hx.2.2 j)
  filter_upwards [hxW, h1, h2] with y hy1 hy2 hy3 using ⟨hy1, hy2, hy3⟩

/-- Closure points of the tube domain inside `W` satisfy the closed inequalities. -/
theorem le_of_mem_closure_tubeDomain (hW : IsOpen W) (hF : ∀ j, ContinuousOn (F j) W)
    (hu : ∀ j, ContinuousOn (u j) W) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ closure (tubeDomain W F u c δ ρ)) (hxW : x ∈ W) :
    (∀ j, |F j x - c j| ≤ δ) ∧ ∀ j, |u j x| ≤ ρ := by
  have hfr := mem_closure_iff_frequently.1 hx
  have hxW' : W ∈ 𝓝 x := hW.mem_nhds hxW
  refine ⟨fun j => ?_, fun j => ?_⟩
  · by_contra h
    rw [not_le] at h
    have hev : ∀ᶠ y in 𝓝 x, δ < |F j y - c j| :=
      continuousAt_const.eventually_lt (((hF j).continuousAt hxW').sub continuousAt_const).abs h
    obtain ⟨y, hyD, hy⟩ := (hfr.and_eventually hev).exists
    exact absurd (hyD.2.1 j) (not_lt.2 hy.le)
  · by_contra h
    rw [not_le] at h
    have hev : ∀ᶠ y in 𝓝 x, ρ < |u j y| :=
      continuousAt_const.eventually_lt ((hu j).continuousAt hxW').abs h
    obtain ⟨y, hyD, hy⟩ := (hfr.and_eventually hev).exists
    exact absurd (hyD.2.2 j) (not_lt.2 hy.le)

/-- **Frontier separation from a face bound.** -/
theorem exists_ge_of_mem_frontier {K : Set ((Fin n → ℝ) × (Fin n → ℝ))} {ε : Fin m → ℝ}
    (hW : IsOpen W) (hK : IsClosed K) (hKW : K ⊆ W) (hWK : ∀ x ∈ W, (∀ j, |u j x| ≤ ρ) → x ∈ K)
    (hF : ∀ j, ContinuousOn (F j) W) (hu : ∀ j, ContinuousOn (u j) W)
    (hface : ∀ j, ∀ x ∈ K, |F j x - c j - u j x| ≤ ε j) (hερ : ∀ j, δ + ε j < ρ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ frontier (tubeDomain W F u c δ ρ)) :
    ∃ j, δ ≤ |F j x - c j| := by
  have hD := isOpen_tubeDomain (c := c) (δ := δ) (ρ := ρ) hW hF hu
  rw [hD.frontier_eq] at hx
  have hDK : tubeDomain W F u c δ ρ ⊆ K := fun y hy => hWK y hy.1 fun j => (hy.2.2 j).le
  have hxK : x ∈ K := closure_minimal hDK hK hx.1
  obtain ⟨hFle, hule⟩ := le_of_mem_closure_tubeDomain hW hF hu hx.1 (hKW hxK)
  by_contra hcon
  push Not at hcon
  refine hx.2 ⟨hKW hxK, hcon, fun j => lt_of_le_of_ne (hule j) fun hj => ?_⟩
  -- on the face `|u_j| = ρ` the face bound forces `|F_j - c_j| > δ`
  have h1 := hface j x hxK
  have h2 := abs_sub_abs_le_abs_sub (u j x) (-(F j x - c j - u j x))
  have h3 : u j x - -(F j x - c j - u j x) = F j x - c j := by ring
  rw [h3, abs_neg, hj] at h2
  linarith [hcon j, hερ j]

end Domain

/-- **Abstract tube confinement.** See the module docstring. -/
theorem tube_confinement {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 2 H)
    {W K Q : Set ((Fin n → ℝ) × (Fin n → ℝ))} {F u : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {c ε η : Fin m → ℝ} {δ ρ T : ℝ} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWK : ∀ x ∈ W, (∀ j, |u j x| ≤ ρ) → x ∈ K)
    (hF : ∀ j, DifferentiableOn ℝ (F j) W) (hu : ∀ j, ContinuousOn (u j) W)
    (hη : ∀ j, ∀ x ∈ K, |fderiv ℝ (F j) x (KAM.hamiltonianVectorField H x)| ≤ η j)
    (hface : ∀ j, ∀ x ∈ K, |F j x - c j - u j x| ≤ ε j) (hερ : ∀ j, δ + ε j < ρ)
    (hT : 0 ≤ T) (hTη : ∀ j, T * η j < δ / 2)
    (hQ : ∀ x ∈ Q, x ∈ W ∧ (∀ j, |F j x - c j| ≤ δ / 2) ∧ ∀ j, |u j x| < ρ)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : z₀ ∈ Q) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → z t ∈ tubeDomain W F u c δ ρ ∧ z t ∈ K ∧
        ∀ j, |F j (z t) - F j z₀| ≤ η j * |t| := by
  have hFc : ∀ j, ContinuousOn (F j) W := fun j => (hF j).continuousOn
  set D := tubeDomain W F u c δ ρ with hDdef
  have hD : IsOpen D := isOpen_tubeDomain hW hFc hu
  have hDK : D ⊆ K := fun y hy => hWK y hy.1 fun j => (hy.2.2 j).le
  have hcl : closure D ⊆ K := closure_minimal hDK hK.isClosed
  have hQD : Q ⊆ D := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hQ x hx
    refine ⟨h1, fun j => ?_, h3⟩
    have := hTη j
    have := mul_nonneg hT ((abs_nonneg _).trans (hη j x (hWK x h1 fun j => (h3 j).le)))
    linarith [h2 j]
  obtain ⟨Tm, Tp, z, hz, hTm, hTp, hconf⟩ :=
    KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement (W := W) (D := D) (Q := Q)
      (a := fun j => c j - δ / 2) (b := fun j => c j + δ / 2) (η := η) (T := T)
      hW hH.contDiffOn hD (hK.of_isClosed_subset isClosed_closure hcl) (hcl.trans hKW) hF
      (fun j x hx => hη j x (hcl hx))
      hQD (fun x hx j => by
        have := abs_le.1 ((hQ x hx).2.1 j)
        constructor <;> linarith [this.1, this.2]) hT
      (fun x hx => by
        obtain ⟨j, hj⟩ := exists_ge_of_mem_frontier hW hK.isClosed hKW hWK hFc hu hface hερ hx
        refine ⟨j, ?_⟩
        have := hTη j
        rcases le_abs'.1 hj with h | h
        · left; linarith
        · right; linarith)
      hz₀
  obtain ⟨T₁, hT₁, -, hz0, hder, huniq⟩ := hamiltonian_solution_of_maximal hH hz hTm hTp
  exact ⟨T₁, hT₁, z, hz0, hder, huniq, fun t ht =>
    ⟨(hconf t ht).1, hDK (hconf t ht).1, (hconf t ht).2⟩⟩

/-- **Observable transfer.** Under the hypotheses of `tube_confinement`, any property `P` holding on
`K` holds along the solution for `|t| ≤ T` (e.g. the eccentricity bounds of a tube enclosure). -/
theorem tube_confinement_observable {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 2 H)
    {W K Q : Set ((Fin n → ℝ) × (Fin n → ℝ))} {F u : Fin m → (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {c ε η : Fin m → ℝ} {δ ρ T : ℝ} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWK : ∀ x ∈ W, (∀ j, |u j x| ≤ ρ) → x ∈ K)
    (hF : ∀ j, DifferentiableOn ℝ (F j) W) (hu : ∀ j, ContinuousOn (u j) W)
    (hη : ∀ j, ∀ x ∈ K, |fderiv ℝ (F j) x (KAM.hamiltonianVectorField H x)| ≤ η j)
    (hface : ∀ j, ∀ x ∈ K, |F j x - c j - u j x| ≤ ε j) (hερ : ∀ j, δ + ε j < ρ)
    (hT : 0 ≤ T) (hTη : ∀ j, T * η j < δ / 2)
    (hQ : ∀ x ∈ Q, x ∈ W ∧ (∀ j, |F j x - c j| ≤ δ / 2) ∧ ∀ j, |u j x| < ρ)
    {P : (Fin n → ℝ) × (Fin n → ℝ) → Prop} (hP : ∀ x ∈ K, P x)
    {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hz₀ : z₀ ∈ Q) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → P (z t) := by
  obtain ⟨T₁, hT₁, z, hz0, hder, huniq, hconf⟩ :=
    tube_confinement hH hW hK hKW hWK hF hu hη hface hερ hT hTη hQ hz₀
  exact ⟨T₁, hT₁, z, hz0, hder, huniq, fun t ht => hP _ (hconf t ht).2.1⟩

end KAM.EffectiveStability.Tube

end
