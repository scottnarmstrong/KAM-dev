/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowInverse
public import KAM.Canonical.Setting

/-!
# Real time-`t` maps of holomorphic real Hamiltonian flows: definitions, reality, smoothness

For a holomorphic generator `φ` that is real on real points, the repo's complex flow
`KAM.Canonical.flow (X_ℂ φ) Ω t` maps real points to real points (`KAM.Canonical.flow_e`). Its
restriction to the real slice is the *real flow* `realFlow φ Ω t`.

* `KAM.EffectiveStability.reMap`: componentwise real part of a map of `ℂⁿ × ℂⁿ`, restricted to the
  real points (same definition as `reMap` of `KAM/Nekhoroshev/Stability/Setting.lean`, copied to
  keep the import light).
* `KAM.EffectiveStability.realFlow`, `KAM.EffectiveStability.realInterior`.
* `realInclusion₂_realFlow`: the real flow is the restriction of the complex flow.
* `contDiffOn_realFlow`: `C^∞` on `realInterior W Ω (1/2)` (stated with the smooth order `∞`).
* `realFlow_zero`, `norm_realFlow_sub_le`: identity at time `0` and the displacement bound.

No conclusion-shaped hypotheses: reality, smoothness and the displacement are derived from the
standing data (`Ω` open, `φ` holomorphic, `SmallField`, reality of `φ` on real points).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Topology

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- The real part of a map of `ℂⁿ × ℂⁿ`, as a map of `ℝⁿ × ℝⁿ` (value at `ι x`). Same definition as
`reMap` in `KAM/Nekhoroshev/Stability/Setting.lean`. -/
def reMap (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => ((Ψ (KAM.realInclusion₂ n x)).1 i).re, fun i => ((Ψ (KAM.realInclusion₂ n x)).2 i).re)

/-- If `Ψ (ι x)` is real, then `ι (reMap Ψ x) = Ψ (ι x)`.
(Copied from the private `psi_real_eq` of `KAM/Nekhoroshev/Stability/Conjugation.lean`.) -/
theorem realInclusion₂_reMap {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (h : Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) :
    KAM.realInclusion₂ n (reMap Ψ x) = Ψ (KAM.realInclusion₂ n x) := by
  obtain ⟨y, hy⟩ := h
  have : reMap Ψ x = y := by
    unfold reMap
    rw [← hy]
    ext i <;> simp
  rw [this, hy]

/-- Derivative bridge for `reMap` (adapted from the private `reMap_hasFDerivAt` of
`KAM/Nekhoroshev/Stability/Conjugation.lean`): if `Ψ` is complex differentiable at `ι x` and real
on real points near `x`, then `reMap Ψ` has a real derivative `L` at `x` with
`ι (L u) = DΨ(ι x) (ι u)`. -/
theorem reMap_hasFDerivAt {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hd : DifferentiableAt ℂ Ψ (KAM.realInclusion₂ n x))
    (hreal : ∀ᶠ y in 𝓝 x, Ψ (KAM.realInclusion₂ n y) ∈ range (KAM.realInclusion₂ n)) :
    ∃ L : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)),
      HasFDerivAt (reMap Ψ) L x ∧ ∀ u, KAM.realInclusion₂ n (L u) =
        fderiv ℂ Ψ (KAM.realInclusion₂ n x) (KAM.realInclusion₂ n u) := by
  have h2 : HasFDerivAt (fun y => Ψ (KAM.realInclusion₂ n y))
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 : HasFDerivAt (reMap Ψ) ((KAM.realPartCLM₂ n).comp
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n))) x :=
    (KAM.realPartCLM₂ n).hasFDerivAt.comp x h2
  refine ⟨_, h3, fun u => ?_⟩
  have h4 : HasFDerivAt (fun y => KAM.realInclusion₂ n (reMap Ψ y))
      ((KAM.realInclusion₂ n).comp ((KAM.realPartCLM₂ n).comp
      (((fderiv ℂ Ψ (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp
        (KAM.realInclusion₂ n)))) x :=
    (KAM.realInclusion₂ n).hasFDerivAt.comp x h3
  have hev : (fun y => KAM.realInclusion₂ n (reMap Ψ y)) =ᶠ[𝓝 x]
      fun y => Ψ (KAM.realInclusion₂ n y) := by
    filter_upwards [hreal] with y hy
    exact realInclusion₂_reMap hy
  have h5 := (h4.congr_of_eventuallyEq hev.symm).unique h2
  exact congrArg (fun L => L u) h5

/-- Complex differentiable on an open set and real near each real point of the set: `reMap` is
`C^∞` on the real preimage. -/
theorem contDiffOn_reMap {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ Ψ U) :
    ContDiffOn ℝ ∞ (reMap Ψ) {x | KAM.realInclusion₂ n x ∈ U} := by
  have h1 : ContDiffOn ℂ ∞ Ψ U := KAM.contDiffOn_infty_of_differentiableOn hU hΨ
  have h2 : ContDiffOn ℝ ∞ Ψ U := h1.restrict_scalars ℝ
  have h3 : ContDiffOn ℝ ∞ (fun x => Ψ (KAM.realInclusion₂ n x))
      {x | KAM.realInclusion₂ n x ∈ U} :=
    h2.comp (KAM.realInclusion₂ n).contDiff.contDiffOn (fun x hx => hx)
  exact (KAM.realPartCLM₂ n).contDiff.comp_contDiffOn h3

section Flow

open KAM.Canonical

variable {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
  {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-- The real time-`t` map of the flow of `X_ℂ φ`: the real part of the complex flow, restricted to
real points. -/
def realFlow (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))) (t : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  reMap (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t)

/-- The real points whose `ν`-gauge ball of radius `c` (in `ℂⁿ × ℂⁿ`) lies in `Ω`. -/
def realInterior (W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)))
    (Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))) (c : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | KAM.realInclusion₂ n x ∈ gaugeInterior W Ω c}

theorem isOpen_realInterior (hΩ : IsOpen Ω) (c : ℝ) : IsOpen (realInterior W Ω c) :=
  (isOpen_gaugeInterior hΩ W c).preimage (KAM.realInclusion₂ n).continuous

theorem realInterior_mono {c c' : ℝ} (h : c' ≤ c) : realInterior W Ω c ⊆ realInterior W Ω c' :=
  fun _ hx => gaugeInterior_mono W h hx

/-- The Hamiltonian field of a holomorphic function that is real on real points is real on real
points of `Ω`. -/
theorem hamiltonianVectorFieldℂ_real (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : KAM.realInclusion₂ n x ∈ Ω) :
    KAM.hamiltonianVectorFieldℂ φ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) :=
  ⟨_, KAM.hamiltonianVectorField_eq_of_real (H := fun y => (φ (KAM.realInclusion₂ n y)).re)
    hΩ hφ hreal hx (Filter.Eventually.of_forall fun _ => rfl)⟩

/-- (1) The real flow is the restriction of the complex flow. -/
theorem realInclusion₂_realFlow (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    KAM.realInclusion₂ n (realFlow φ Ω t x) =
      flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (KAM.realInclusion₂ n x) := by
  have hfe := flow_e h (fun z hz ⟨y, hy⟩ => by
    subst hy
    exact hamiltonianVectorFieldℂ_real hΩ hφ hreal hz) (KAM.realInclusion₂ n x) hx ⟨x, rfl⟩ t ht
  exact realInclusion₂_reMap hfe

/-- (2) Smoothness of the real flow on `realInterior W Ω (1/2)` (smooth order `∞`). -/
theorem contDiffOn_realFlow (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ContDiffOn ℝ ∞ (realFlow φ Ω t) (realInterior W Ω (1 / 2)) :=
  (contDiffOn_reMap (isOpen_gaugeInterior h.isOpen W (1 / 2))
    ((flow_b h).2.1 t ht))

/-- The real flow at time `0` is the identity on `realInterior W Ω (1/2)`. -/
theorem realFlow_zero (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2)) :
    realFlow φ Ω 0 x = x := by
  apply KAM.realInclusion₂_injective n
  rw [realInclusion₂_realFlow hΩ hφ h hreal hx ⟨by norm_num, by norm_num⟩]
  exact (flow_a h hx).1

/-- (5) Displacement bound for the real flow, in the gauge `W` on `ℂⁿ × ℂⁿ`:
`‖W (ι (X^t x) - ι x)‖ ≤ |t| ε`. -/
theorem norm_realFlow_sub_le (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Ω →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖W (KAM.realInclusion₂ n (realFlow φ Ω t x) - KAM.realInclusion₂ n x)‖ ≤ |t| * ε := by
  rw [realInclusion₂_realFlow hΩ hφ h hreal hx ht]
  exact (flow_a h hx).2.2.2 t ht

end Flow

end KAM.EffectiveStability

end
