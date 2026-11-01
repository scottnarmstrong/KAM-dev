/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Certified
public import KAM.Application.Transport

/-!
# The certified torus in physical coordinates

The assembly of the adapters (improvement #7), the generic form of LG00's `lg00_physical_orbits`:

* `CertifiedTorusAt.physical`: a certified torus, a model chart domain `O` (open, containing the
  real points of `c.D`), a real model Hamiltonian `Hc` agreeing with `Re c.H` on `O` (e.g. a
  closed-form physical expression), and a chart with the transport identity
  `DΨ X_{Hc} = κ F ∘ Ψ` on `O` give: the real torus lies in `O`, it is a real model torus of `Hc`,
  and `Ψ ∘ k` is a physical invariant torus of `F` at the physical frequency `κ⁻¹ s∞ ω*`.
* `CertifiedTorusAt.physical_energy`: with `Hc = a · H_phys ∘ Ψ` on `O`, the physical torus lies on
  the physical level `H_phys = E₀ / a`.

Every result is stated on the named witnesses (`CertifiedTorusAt`), so the graph
(`CertifiedTorusAt.isAngleGraph`), the observables (`KAM/Application/Observables.lean`) and these
can be attached to the same exact torus.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α] {c : TorusCertificate n α}
  {ωstar : Fin n → ℝ} {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real certified torus lies in every set containing the real points of `c.D`. -/
theorem CertifiedTorusAt.realRestriction_mem (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) {O : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hDO : ∀ p, realInclusion₂ n p ∈ c.D → p ∈ O) (θ : Fin n → ℝ) : realRestriction Kinf θ ∈ O := by
  apply hDO
  rw [← isRealOnReals_iff.mp hT.2.2.2.2.1]
  exact hT.realInclusion_mem_D hs θ

/-- **The certified torus in physical coordinates.** -/
theorem CertifiedTorusAt.physical (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H)
    {O : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hO : IsOpen O)
    (hDO : ∀ p, realInclusion₂ n p ∈ c.D → p ∈ O) {Hc : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hHc : ∀ p ∈ O, Hc p = realHam c.H p) {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → E} {F : E → E}
    {κ : ℝ} (hκ : κ ≠ 0) (hΨ : IsFieldTransport Ψ Hc F κ O) :
    (∀ θ, realRestriction Kinf θ ∈ O) ∧
      IsRealModelTorus Hc (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      IsPhysicalFlowTorus F (κ⁻¹ • (sinf • ωstar)) (Ψ ∘ realRestriction Kinf) := by
  have hkO := hT.realRestriction_mem hs hDO
  have hk := (hT.isRealModelTorus hs hH).congr hO hkO hHc
  exact ⟨hkO, hk, hk.isPhysicalFlowTorus hΨ hκ hkO⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The physical energy level**: with `Hc = a · H_phys ∘ Ψ` on `O` (`a ≠ 0`), the physical torus
lies on `H_phys = E₀ / a`. -/
theorem CertifiedTorusAt.physical_energy (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H)
    {O : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hO : IsOpen O)
    (hDO : ∀ p, realInclusion₂ n p ∈ c.D → p ∈ O) {Hc : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hHc : ∀ p ∈ O, Hc p = realHam c.H p) {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → E} {Hp : E → ℝ}
    {a : ℝ} (ha : a ≠ 0) (hHp : ∀ p ∈ O, Hc p = a * Hp (Ψ p)) (θ : Fin n → ℝ) :
    Hp (Ψ (realRestriction Kinf θ)) = (c.params.E0 : ℝ) / a := by
  have hkO := hT.realRestriction_mem hs hDO
  exact ((hT.isRealModelTorus hs hH).congr hO hkO hHc).energy_comp hkO ha hHp θ

end KAM.Application
