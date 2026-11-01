/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Observables
public import KAM.Application.Physical
public import KAM.Application.TransportChart
public import KAM.Certificate.Tests.Toy2

/-!
# The application adapters on the toy certificate T2

T2 (`KAM/Certificate/Tests/Toy2.lean`): `H = J + p²/2`, `K(θ) = (θ, (ν̃, -ν̃²/2))`, a passing
certificate and `toyCert2_torus : CertifiedTorus toyCert2 (ν₋/2, 1/2)`. Every certificate-side
input below is a passing `Bool` check (`decide +kernel`, small):

* `toyCert2_angleGraph`, `toyCert2_angleGraphReal`: the strip and real-torus graph checks at
  `δ = 0` (the angle displacement vanishes; the margin is `disp < ρ∞`);
* `toyCert2_actionRange`, `toyCert2_actionRangeReal`: `I₀ ∈ [0.974, 0.976]` (strip and real).

`toyCert2_physical` chains the adapters through `CertifiedTorusAt.physical` and
`CertifiedTorusAt.physical_energy`: the exact torus, its graph over the angles, the transport
through the `2π` angle chart `S_{2π}(θ, I) = (2πθ, I)` (a core `2π`-chart; clock `2π`) to the
Hamiltonian in radian angles, the physical energy level, and a checked action bound at every torus
point (hence along every torus line). Negative cases and nonzero angle data are in
`Tests/Probes.lean`, which does not import the chart layer.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application.Tests

open KAM KAM.Certificate KAM.Application KAM.Planetary

theorem toyCert2_static : checkStatic toyCert2 = true :=
  (checkStatic_checkHamBounds_of_checkTorusCertificate toyCert2_passes).1

theorem toyCert2_hamBounds : checkHamBounds toyCert2 = true :=
  (checkStatic_checkHamBounds_of_checkTorusCertificate toyCert2_passes).2

/-- The strip graph check with `δ = 0`. -/
theorem toyCert2_angleGraph : checkAngleGraph toyCert2 0 = true := by
  decide +kernel

/-- The real-torus graph check with `δ = 0`. -/
theorem toyCert2_angleGraphReal : checkAngleGraphReal toyCert2 0 = true := by
  decide +kernel

/-- The action `I₀ = ν̃ ≈ 0.97538` lies in `[0.974, 0.976]` (strip check). -/
theorem toyCert2_actionRange : checkActionRange toyCert2 0 (975 / 1000) (1 / 1000) = true := by
  decide +kernel

/-- The same with the real-torus check. -/
theorem toyCert2_actionRangeReal :
    checkActionRangeReal toyCert2 0 (975 / 1000) (1 / 1000) = true := by
  decide +kernel

/-- **The graph adapter on T2** (dot notation on `CertifiedTorus`). -/
theorem toyCert2_realGraph :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧
      IsRealModelTorus (realHam toyCert2.H) (sinf • ![lunarNuMinus / 2, 1 / 2])
        toyCert2.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf)
        (((0 : ℚ) : ℝ) + (toyCert2.params.disp : ℝ) / toyCert2.params.rhoInf) :=
  toyCert2_torus.exists_realGraph_of_checks toyCert2_static toyCert2_hamBounds
    (.inl toyCert2_angleGraphReal)

/-- The same through the strip check and the adapter-namespace alias. -/
example : ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧
      IsRealModelTorus (realHam toyCert2.H) (sinf • ![lunarNuMinus / 2, 1 / 2])
        toyCert2.params.E0 (realRestriction Kinf) ∧
      IsAngleGraph (realRestriction Kinf)
        (((0 : ℚ) : ℝ) + (toyCert2.params.disp : ℝ) / toyCert2.params.rhoInf) :=
  Application.CertifiedTorus.exists_realGraph_of_checks toyCert2_torus toyCert2_static
    toyCert2_hamBounds (.inr toyCert2_angleGraph)

/-- The toy's Hamiltonian in radian angles: `H_phys(φ, I) = Re H(φ/2π, I)`. -/
def toyHphys : Phase 2 → ℝ := fun z => realHam toyCert2.H (angleScale (2 * Real.pi)⁻¹ z)

theorem toyHc_eq (p : Phase 2) :
    realHam toyCert2.H p = 1 * toyHphys (angleScale (2 * Real.pi) p) := by
  have h : angleScale (2 * Real.pi)⁻¹ (angleScale (2 * Real.pi) p) = p := by
    have h2 : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
    simp only [angleScale]
    rw [smul_smul, h2, one_smul]
  rw [one_mul, toyHphys, h]

/-- The transport identity for `S_{2π}`, clock `2π`. -/
theorem toy_transport : IsFieldTransport (angleScale (2 * Real.pi)) (realHam toyCert2.H)
    (hamiltonianVectorField toyHphys) (1 * (2 * Real.pi)) univ :=
  isFieldTransport_of_isChart (by positivity) one_ne_zero isOpen_univ
    (isChart_angleScale (by positivity)) fun p _ => toyHc_eq p

/-- **The adapters end to end on T2**: an exact torus `K∞` at `s∞` (all clauses of
`CertifiedTorus`) whose real restriction is an analytic graph over the angles, whose image under the
`2π` angle chart is a physical torus of `toyHphys` (its lines solve Hamilton's equations) at the
frequency `(2π)⁻¹ s∞ ω*` on the level `E₀`, and whose action `I₀` is within `10⁻³ + disp` of
`0.975` at every torus point, in particular along every torus line. -/
theorem toyCert2_physical :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧
      IsAngleGraph (realRestriction Kinf)
        (((0 : ℚ) : ℝ) + (toyCert2.params.disp : ℝ) / toyCert2.params.rhoInf) ∧
      IsPhysicalFlowTorus (hamiltonianVectorField toyHphys)
        ((1 * (2 * Real.pi))⁻¹ • (sinf • ![lunarNuMinus / 2, 1 / 2]))
        (angleScale (2 * Real.pi) ∘ realRestriction Kinf) ∧
      (∀ θ, toyHphys (angleScale (2 * Real.pi) (realRestriction Kinf θ)) =
        (toyCert2.params.E0 : ℝ) / 1) ∧
      ∀ θ (τ : ℝ), |(realRestriction Kinf (θ + τ • ((1 * (2 * Real.pi))⁻¹ •
        (sinf • ![lunarNuMinus / 2, 1 / 2])))).2 0 - ((975 / 1000 : ℚ) : ℝ)| ≤
          ((1 / 1000 : ℚ) : ℝ) + toyCert2.params.disp := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff _ _).1 toyCert2_torus
  have hH := isRealHolo_of_checkHamBounds toyCert2_static toyCert2_hamBounds
  have hg := checkAngleGraphReal_sound toyCert2_static toyCert2_angleGraphReal
  obtain ⟨-, -, hflow⟩ := hT.physical toyCert2_static hH isOpen_univ (fun _ _ => mem_univ _)
    (fun _ _ => rfl) (by positivity) toy_transport
  refine ⟨Kinf, sinf, hT, hT.isAngleGraph toyCert2_static hg.1 hg.2, hflow,
    hT.physical_energy toyCert2_static hH isOpen_univ (fun _ _ => mem_univ _)
      (fun _ _ => rfl) one_ne_zero fun p _ => toyHc_eq p, fun θ τ => ?_⟩
  exact forall_orbit (P := fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      |z.2 0 - ((975 / 1000 : ℚ) : ℝ)| ≤ ((1 / 1000 : ℚ) : ℝ) + toyCert2.params.disp)
    (hT.abs_action_sub_ctr_le_real toyCert2_static (i := 0) toyCert2_actionRangeReal) _ θ τ

end KAM.Application.Tests
