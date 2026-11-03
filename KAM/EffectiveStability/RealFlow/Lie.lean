/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.RealFlow.Symplectic
public import KAM.Canonical.Lie

/-!
# Observables along the real flow, real Lie–Taylor bound, smoke test

* `realObs_realFlow`, `contDiffOn_realObs`: for `h` holomorphic on an open `U`, the real function
  `H x = Re h (ι x)` satisfies `H (X^t x) = Re h (X^t_ℂ (ι x))` and is `C^∞` on `{x | ι x ∈ U}`.
* `real_taylor_lie_bound`: the real parts of both sides of `KAM.Canonical.taylor_lie`; the bound
  needs no reality assumption on `u` or on `adPow φ j u`.
* `smoke_zero_generator`: the standing data for `φ = 0` are satisfiable and the flow is the
  identity.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.EffectiveStability

open KAM.Canonical

variable {n : ℕ}
  {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
  {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-- (6) The real observable `x ↦ Re h (ι x)` along the real flow. -/
theorem realObs_realFlow (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    (g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (g (KAM.realInclusion₂ n (realFlow φ Ω t x))).re =
      (g (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (KAM.realInclusion₂ n x))).re := by
  rw [realInclusion₂_realFlow h.isOpen hφ h hreal hx ht]

/-- (6) Smoothness of `x ↦ Re h (ι x)` on `{x | ι x ∈ U}` for `h` holomorphic on open `U`. -/
theorem contDiffOn_realObs {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g U) :
    ContDiffOn ℝ ∞ (fun x => (g (KAM.realInclusion₂ n x)).re) {x | KAM.realInclusion₂ n x ∈ U} := by
  have h2 : ContDiffOn ℝ ∞ g U :=
    (KAM.contDiffOn_infty_of_differentiableOn hU hg).restrict_scalars ℝ
  exact Complex.reCLM.contDiff.comp_contDiffOn
    (h2.comp (KAM.realInclusion₂ n).contDiff.contDiffOn (fun x hx => hx))

/-- (7) Real Lie–Taylor with remainder bound, at the real point `x`, order `N ≥ 1`. -/
theorem real_taylor_lie_bound {Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : Ω₁ ⊆ Ω) (hu : DifferentiableOn ℂ u Ω₁)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2))
    (htraj : ∀ t ∈ Icc (-1 : ℝ) 1,
      flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (KAM.realInclusion₂ n x) ∈ Ω₁)
    {N : ℕ} (hN : 1 ≤ N) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖adPow φ N u
      (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (KAM.realInclusion₂ n x))‖ ≤ B) :
    |(u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω 1 (KAM.realInclusion₂ n x))).re -
        ∑ j ∈ Finset.range N, ((j.factorial : ℝ)⁻¹) *
          (adPow φ j u (KAM.realInclusion₂ n x)).re| ≤ B / (N.factorial : ℝ) := by
  obtain ⟨h1, h2⟩ := taylor_lie hφ h hΩ₁ hΩ₁Ω hu hx htraj hN
  have h3 := h2 B hB
  set I := ∫ t in (0 : ℝ)..1, ((((1 - t) ^ (N - 1) / ((N - 1).factorial : ℝ) : ℝ) : ℂ)) *
    adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (KAM.realInclusion₂ n x)) with hI
  have hre : (u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω 1 (KAM.realInclusion₂ n x))).re -
      ∑ j ∈ Finset.range N, ((j.factorial : ℝ)⁻¹) *
        (adPow φ j u (KAM.realInclusion₂ n x)).re = I.re := by
    rw [h1, Complex.add_re, Complex.re_sum]
    have : ∀ j ∈ Finset.range N, (((j.factorial : ℂ)⁻¹) *
        adPow φ j u (KAM.realInclusion₂ n x)).re =
        ((j.factorial : ℝ)⁻¹) * (adPow φ j u (KAM.realInclusion₂ n x)).re := fun j _ => by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    rw [Finset.sum_congr rfl this]
    ring
  rw [hre]
  exact (Complex.abs_re_le_norm I).trans h3

/-! ### Smoke test: the zero generator -/

/-- The standing data are satisfiable: for `φ = 0`, `Ω = univ`, `W = id`, `ε = 0`, all hypotheses
hold, and the real flow is the identity on `realInterior W Ω (1/2)`. -/
theorem smoke_zero_generator (n : ℕ) :
    let W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
      ContinuousLinearEquiv.refl ℂ _
    let φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := fun _ => 0
    SmallField W (univ : Set ((Fin n → ℂ) × (Fin n → ℂ))) (KAM.hamiltonianVectorFieldℂ φ) 0 ∧
    DifferentiableOn ℂ φ univ ∧
    (∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ (univ : Set _) →
      (φ (KAM.realInclusion₂ n x)).im = 0) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∈ realInterior W univ (1 / 2), realFlow φ univ t x = x := by
  intro W φ
  have hX : KAM.hamiltonianVectorFieldℂ φ = fun _ => 0 := by
    funext z
    have : fderiv ℂ φ z = 0 := fderiv_const_apply (0 : ℂ)
    simp [KAM.hamiltonianVectorFieldℂ, this]
    rfl
  have hS : SmallField W (univ : Set ((Fin n → ℂ) × (Fin n → ℂ)))
      (KAM.hamiltonianVectorFieldℂ φ) 0 :=
    { isOpen := isOpen_univ
      differentiableOn := by rw [hX]; exact differentiableOn_const _
      eps_nonneg := le_rfl
      eps_le := by norm_num
      bound := fun z _ => by rw [hX]; simp }
  have hφ : DifferentiableOn ℂ φ univ := differentiableOn_const _
  have hr : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ (univ : Set _) →
      (φ (KAM.realInclusion₂ n x)).im = 0 := fun _ _ => rfl
  refine ⟨hS, hφ, hr, fun t ht x hx => ?_⟩
  apply KAM.realInclusion₂_injective n
  rw [realInclusion₂_realFlow isOpen_univ hφ hS hr hx ht]
  have hz : KAM.realInclusion₂ n x ∈ gaugeInterior W univ (1 / 2) := hx
  have hsol : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorFieldℂ φ) univ (Icc (-1) 1)
      (fun _ => KAM.realInclusion₂ n x) := fun s _ => by
    refine ⟨mem_univ _, ?_⟩
    rw [hX]
    exact hasDerivAt_const _ _
  exact ((flow_a hS hz).2.2.1 (Icc (-1) 1) ordConnected_Icc ⟨by norm_num, by norm_num⟩ _ hsol
    rfl t ⟨ht, ht⟩).symm

end KAM.EffectiveStability

end
