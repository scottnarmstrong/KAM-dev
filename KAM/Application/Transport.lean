/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.RealTorus

/-!
# Chart transport to the physical system

The chart transport adapter (improvement #7). A chart `Ψ` from the model phase space
`ℝⁿ × ℝⁿ` (frozen orientation `(θ, I)`, `X_H = (∂_I H, -∂_θ H)`) to a physical phase space `E`
(any real normed space, any ordering of its variables) with the **transport identity**

  `DΨ(p) X_{Hc}(p) = κ F(Ψ p)` for `p ∈ O`  (`IsFieldTransport Ψ Hc F κ O`)

carries the model dynamics of `Hc` to the physical vector field `F` with the clock `κ` (model time
`t` is physical time `κ t`). This generalizes LG00's `lg00_transport` (`κ = 2πκ_LG00`, `F` the
field of LG00's (11) in their `(ξ, η)` order); `KAM/Application/TransportChart.lean` derives the
identity from the core's conformally symplectic charts (`KAM.Planetary.IsChart`).

* `IsFieldTransport.hasDerivAt_comp`: a model solution `y` gives the physical solution
  `τ ↦ Ψ (y (τ / κ))`.
* `IsPhysicalFlowTorus F ν L`: every line `τ ↦ L(θ + τ ν)` solves `ż = F z`.
* `IsRealModelTorus.isPhysicalFlowTorus`: a real model torus `k` of `Hc` at `ω` inside `O` gives
  the physical torus `Ψ ∘ k` at the physical frequency `κ⁻¹ ω`.
* Clause by clause: `analyticOnNhd_comp` (analytic chart), `comp_add_int` (lattice law of the
  chart), `injective_mod_comp` (injective modulo `ℤⁿ` when the chart is injective modulo the angle
  lattice), `injective_fderiv_comp` (immersion), `energy_comp` and `level_comp` (energy levels,
  for `Hc = a · H_phys ∘ Ψ` on `O`).
* `hamiltonianVectorField_const_mul`: `X_{r G} = r X_G` for `r ≠ 0` (time rescaling), and
  `IsFieldTransport.const_mul`: scaling `Hc` by `r` scales the clock by `r`.
* `IsPhysicalFlowTorus` only says that the torus lines are solutions; that the image is invariant
  (every solution meeting it stays on it) is `KAM/Application/Invariance.lean`.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Application

open KAM

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The transport identity** on `O`: `Ψ` is differentiable at `p` and
`DΨ(p) X_{Hc}(p) = κ F(Ψ p)`. -/
def IsFieldTransport (Ψ : (Fin n → ℝ) × (Fin n → ℝ) → E) (Hc : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (F : E → E) (κ : ℝ) (O : Set ((Fin n → ℝ) × (Fin n → ℝ))) : Prop :=
  ∀ p ∈ O, DifferentiableAt ℝ Ψ p ∧ fderiv ℝ Ψ p (hamiltonianVectorField Hc p) = κ • F (Ψ p)

/-- **A physical invariant torus** `L : ℝⁿ → E` of the vector field `F` at the frequency `ν`: every
line `τ ↦ L(θ + τ ν)` is a solution of `ż = F(z)` for all real times. -/
def IsPhysicalFlowTorus (F : E → E) (ν : Fin n → ℝ) (L : (Fin n → ℝ) → E) : Prop :=
  ∀ θ τ, HasDerivAt (fun u : ℝ => L (θ + u • ν)) (F (L (θ + τ • ν))) τ

/-- **Time rescaling**: `X_{r G} = r X_G` for `r ≠ 0` (unconditionally in differentiability). -/
theorem hamiltonianVectorField_const_mul {G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {r : ℝ} (hr : r ≠ 0)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    hamiltonianVectorField (fun q => r * G q) p = r • hamiltonianVectorField G p := by
  by_cases hG : DifferentiableAt ℝ G p
  · ext i <;> simp [hamiltonianVectorField, fderiv_const_mul hG r]
  · have hrG : ¬ DifferentiableAt ℝ (fun q => r * G q) p := fun h => hG (by
      have := h.const_mul r⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hr] using this)
    ext i <;> simp [hamiltonianVectorField, fderiv_zero_of_not_differentiableAt hG,
      fderiv_zero_of_not_differentiableAt hrG]

section Transport

variable {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → E} {Hc : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {F : E → E}
  {κ : ℝ} {O : Set ((Fin n → ℝ) × (Fin n → ℝ))}

/-- **Orbits**: a model solution `y` of Hamilton's equations of `Hc` at model time `τ/κ` (in `O`)
gives the physical solution `τ ↦ Ψ (y (τ / κ))` of `ż = F z` at physical time `τ`. -/
theorem IsFieldTransport.hasDerivAt_comp (hΨ : IsFieldTransport Ψ Hc F κ O) (hκ : κ ≠ 0)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {τ : ℝ} (hyO : y (τ / κ) ∈ O)
    (hy : HasDerivAt y (hamiltonianVectorField Hc (y (τ / κ))) (τ / κ)) :
    HasDerivAt (fun u : ℝ => Ψ (y (u / κ))) (F (Ψ (y (τ / κ)))) τ := by
  have hg : HasDerivAt (fun u : ℝ => u / κ) κ⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const κ⁻¹
  have h1 := hy.scomp τ hg
  have h2 := (hΨ _ hyO).1.hasFDerivAt.comp_hasDerivAt τ h1
  rw [map_smul, (hΨ _ hyO).2, smul_smul, inv_mul_cancel₀ hκ, one_smul] at h2
  exact h2

/-- **Invariant tori**: a real model torus `k` of `Hc` at `ω` lying in `O` gives the physical
invariant torus `Ψ ∘ k` of `F` at the physical frequency `κ⁻¹ ω`. -/
theorem IsRealModelTorus.isPhysicalFlowTorus {ω : Fin n → ℝ} {E₀ : ℝ}
    {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hk : IsRealModelTorus Hc ω E₀ k)
    (hΨ : IsFieldTransport Ψ Hc F κ O) (hκ : κ ≠ 0) (hkO : ∀ θ, k θ ∈ O) :
    IsPhysicalFlowTorus F (κ⁻¹ • ω) (Ψ ∘ k) := by
  intro θ τ
  have e : ∀ u : ℝ, θ + u • κ⁻¹ • ω = θ + (u / κ) • ω := fun u => by
    rw [smul_smul, div_eq_mul_inv]
  simp only [comp_apply, e]
  exact hΨ.hasDerivAt_comp hκ (y := fun s => k (θ + s • ω)) (hkO _) (hk.flow θ (τ / κ))

/-- Analyticity of the physical torus. -/
theorem analyticOnNhd_comp {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hΨ : AnalyticOnNhd ℝ Ψ O) (hk : AnalyticOnNhd ℝ k univ) (hkO : ∀ θ, k θ ∈ O) :
    AnalyticOnNhd ℝ (Ψ ∘ k) univ :=
  hΨ.comp hk fun θ _ => hkO θ

omit [NormedSpace ℝ E] in
/-- The lattice law of the physical torus from that of the chart (`T = 0`: periodic). -/
theorem comp_add_int {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {T : (Fin n → ℤ) → E}
    (hk : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0))
    (hkO : ∀ θ, k θ ∈ O)
    (hΨ : ∀ p ∈ O, ∀ m : Fin n → ℤ, Ψ (p + (fun i => (m i : ℝ), 0)) = Ψ p + T m)
    (θ : Fin n → ℝ) (m : Fin n → ℤ) :
    (Ψ ∘ k) (θ + fun i => (m i : ℝ)) = (Ψ ∘ k) θ + T m := by
  simp only [comp_apply, hk θ m, hΨ _ (hkO θ) m]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Injectivity modulo `ℤⁿ` of the physical torus, from injectivity of the chart modulo the angle
lattice on `O` and injectivity of the model angle map modulo `ℤⁿ` (`IsAngleGraph.injective_mod`). -/
theorem injective_mod_comp {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hkO : ∀ θ, k θ ∈ O)
    (hΨ : ∀ p ∈ O, ∀ q ∈ O, Ψ p = Ψ q → ∃ m : Fin n → ℤ, q = p + (fun i => (m i : ℝ), 0))
    (hk : ∀ θ θ' (m : Fin n → ℤ), (k θ').1 = (k θ).1 + (fun i => (m i : ℝ)) →
      θ' = θ + fun i => (m i : ℝ))
    {θ θ' : Fin n → ℝ} (h : Ψ (k θ) = Ψ (k θ')) : ∃ m : Fin n → ℤ, θ' = θ + fun i => (m i : ℝ) := by
  obtain ⟨m, hm⟩ := hΨ _ (hkO θ) _ (hkO θ') h
  exact ⟨m, hk θ θ' m (by rw [hm]; rfl)⟩

/-- The physical torus is an immersion where the chart's derivative is injective. -/
theorem injective_fderiv_comp {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {θ : Fin n → ℝ}
    (hΨd : DifferentiableAt ℝ Ψ (k θ)) (hkd : DifferentiableAt ℝ k θ)
    (hΨi : Injective (fderiv ℝ Ψ (k θ))) (hki : Injective (fderiv ℝ k θ)) :
    Injective (fderiv ℝ (Ψ ∘ k) θ) := by
  rw [fderiv_comp θ hΨd hkd]
  exact hΨi.comp hki

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Energy levels**: if `Hc = a · H_phys ∘ Ψ` on `O` (`a ≠ 0`), the level `Hc = E₀` goes to the
physical level `H_phys = E₀ / a`. -/
theorem level_comp {Hp : E → ℝ} {a : ℝ} (ha : a ≠ 0) (hHc : ∀ p ∈ O, Hc p = a * Hp (Ψ p))
    {p : (Fin n → ℝ) × (Fin n → ℝ)} (hp : p ∈ O) {E₀ : ℝ} (h : Hc p = E₀) :
    Hp (Ψ p) = E₀ / a := by
  rw [eq_div_iff ha, mul_comm, ← hHc p hp, h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The physical torus lies on the physical level `E₀ / a`. -/
theorem IsRealModelTorus.energy_comp {ω : Fin n → ℝ} {E₀ : ℝ}
    {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hk : IsRealModelTorus Hc ω E₀ k)
    (hkO : ∀ θ, k θ ∈ O) {Hp : E → ℝ} {a : ℝ} (ha : a ≠ 0)
    (hHc : ∀ p ∈ O, Hc p = a * Hp (Ψ p)) (θ : Fin n → ℝ) : Hp ((Ψ ∘ k) θ) = E₀ / a :=
  level_comp ha hHc (hkO θ) (hk.energy θ)

/-- **Clock rescaling**: scaling the model Hamiltonian by `r ≠ 0` scales the clock by `r`
(e.g. a certificate Hamiltonian `κ · H` with a chart transporting `H` at clock `1`). -/
theorem IsFieldTransport.const_mul (hΨ : IsFieldTransport Ψ Hc F κ O) {r : ℝ} (hr : r ≠ 0) :
    IsFieldTransport Ψ (fun p => r * Hc p) F (r * κ) O := fun p hp =>
  ⟨(hΨ p hp).1, by
    rw [hamiltonianVectorField_const_mul hr, map_smul, (hΨ p hp).2, smul_smul]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A real model torus is a flow torus of its own Hamiltonian field (model coordinates). -/
theorem IsRealModelTorus.isPhysicalFlowTorus_self {ω : Fin n → ℝ} {E₀ : ℝ}
    {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (hk : IsRealModelTorus Hc ω E₀ k) :
    IsPhysicalFlowTorus (hamiltonianVectorField Hc) ω k :=
  hk.flow

end Transport

end KAM.Application
