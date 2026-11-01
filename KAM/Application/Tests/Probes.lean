/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Invariance
public import KAM.Application.Observables
public import KAM.Application.Physical
public import KAM.Certificate.Tests.Toy2

/-!
# Probes of the application checks and adapters

Cheap regression probes (from AUDIT-V2-ADAPT-1), without the chart layer's Mathlib import.

* Negative cases on T2: `checkAngleGraph`/`checkAngleGraphReal` reject `δ < 0` and a failing margin
  (`δ = 1`); `checkActionRange`/`checkActionRangeReal` reject a too tight radius, a wrong centre
  and the wrong row, and accept the second action `-ν̃²/2 ≈ -0.4757`.
* Nonzero angle data: `probeCert a k` is T2's data with the angle displacement
  `U₀(θ) = 2a cos(2π k θ₀)` (checker inputs only, not the certificate of a torus), so
  `sup_ℝ |∂₀ U₀| = 4π |k| a`. The real-torus check is tight (it brackets `4π|k|a` between two
  passing/failing `δ`); the strip check weights the mode by
  about `e^{2π|k|ρ}` (`ρ = 9`): at `a = 10⁻²⁰` the strip check fails `δ = 0.99` while the real check
  passes `δ = 2 · 10⁻¹⁹` (true value `≈ 1.257 · 10⁻¹⁹`; on `ℚ` the real check is exact up to the
  rational upper bound of `2π`).
* The adapters on T2 without a chart: `CertifiedTorusAt.physical` and `physical_energy` through the
  identity chart with the clock `2` (`IsFieldTransport.const_mul`, physical Hamiltonian
  `H_phys = Re H / 2`), and `CertifiedTorusAt.observable_bounds` for the action `I₀` from the
  real-torus action check.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application.Tests

open KAM KAM.Certificate KAM.Application

/-! ### Negative cases on T2 -/

theorem probe_angleGraph_neg : checkAngleGraph toyCert2 (-1) = false := by decide +kernel
theorem probe_angleGraphReal_neg : checkAngleGraphReal toyCert2 (-1) = false := by decide +kernel
theorem probe_angleGraph_margin : checkAngleGraph toyCert2 1 = false := by decide +kernel
theorem probe_angleGraphReal_margin : checkAngleGraphReal toyCert2 1 = false := by decide +kernel

theorem probe_actionRange_tight :
    checkActionRange toyCert2 0 (975 / 1000) (1 / 100000) = false := by decide +kernel
theorem probe_actionRangeReal_tight :
    checkActionRangeReal toyCert2 0 (975 / 1000) (1 / 100000) = false := by decide +kernel
theorem probe_actionRange_centre : checkActionRange toyCert2 0 0 (1 / 1000) = false := by
  decide +kernel
theorem probe_actionRangeReal_centre : checkActionRangeReal toyCert2 0 0 (1 / 1000) = false := by
  decide +kernel
theorem probe_actionRange_row :
    checkActionRange toyCert2 1 (975 / 1000) (1 / 1000) = false := by decide +kernel
theorem probe_actionRange_row1 :
    checkActionRange toyCert2 1 (-4757 / 10000) (1 / 1000) = true := by decide +kernel
theorem probe_actionRangeReal_row1 :
    checkActionRangeReal toyCert2 1 (-4757 / 10000) (1 / 1000) = true := by decide +kernel

/-! ### Nonzero angle data -/

/-- T2's data with the angle displacement `U₀(θ) = 2a cos(2π k θ₀)` (checker inputs only). -/
def probeCert (a : ℚ) (k : ℤ) : TorusCertificate 2 ℚ :=
  { toyCert2 with emb := { toyCert2.emb with angle := [⟨0, [([k, 0], ⟨a, 0⟩)]⟩, ⟨0, []⟩] } }

/-- `a = 10⁻³⁰`, `k = 1`: `sup_ℝ |∂₀ U₀| = 4π · 10⁻³⁰ ≈ 1.257 · 10⁻²⁹`. The real-torus check is
tight (passes at `2 · 10⁻²⁹`, fails at `10⁻²⁹`); the strip check passes at `10⁻³` and fails at
`10⁻⁷`. -/
theorem probe_real_pass :
    checkAngleGraphReal (probeCert (1 / 10 ^ 30) 1) (2 / 10 ^ 29) = true := by
  decide +kernel
theorem probe_real_fail :
    checkAngleGraphReal (probeCert (1 / 10 ^ 30) 1) (1 / 10 ^ 29) = false := by
  decide +kernel
theorem probe_strip_pass : checkAngleGraph (probeCert (1 / 10 ^ 30) 1) (1 / 1000) = true := by
  decide +kernel
theorem probe_strip_fail : checkAngleGraph (probeCert (1 / 10 ^ 30) 1) (1 / 10 ^ 7) = false := by
  decide +kernel

/-- `a = 10⁻²⁰`: the strip check fails at `δ = 0.99`, the real check passes at `δ = 2 · 10⁻¹⁹`
(true value `≈ 1.257 · 10⁻¹⁹`). -/
theorem probe_strip_conservative :
    checkAngleGraph (probeCert (1 / 10 ^ 20) 1) (99 / 100) = false := by decide +kernel
theorem probe_real_sharp :
    checkAngleGraphReal (probeCert (1 / 10 ^ 20) 1) (2 / 10 ^ 19) = true := by decide +kernel

/-- `k = 2` (`sup_ℝ |∂₀ U₀| ≈ 2.513 · 10⁻²⁹`): the strip check fails at `δ = 1/2`; the real check
passes at `3 · 10⁻²⁹` and fails at `2 · 10⁻²⁹`. -/
theorem probe_strip_k2 : checkAngleGraph (probeCert (1 / 10 ^ 30) 2) (1 / 2) = false := by
  decide +kernel
theorem probe_real_k2 :
    checkAngleGraphReal (probeCert (1 / 10 ^ 30) 2) (3 / 10 ^ 29) = true := by decide +kernel
theorem probe_real_k2_fail :
    checkAngleGraphReal (probeCert (1 / 10 ^ 30) 2) (2 / 10 ^ 29) = false := by decide +kernel

/-! ### The adapters on T2 without a chart -/

theorem probe_static : checkStatic toyCert2 = true :=
  (checkStatic_checkHamBounds_of_checkTorusCertificate toyCert2_passes).1

theorem probe_hamBounds : checkHamBounds toyCert2 = true :=
  (checkStatic_checkHamBounds_of_checkTorusCertificate toyCert2_passes).2

/-- The identity chart transports any Hamiltonian field to itself at clock `1`. -/
theorem id_isFieldTransport (H : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ) :
    IsFieldTransport id H (hamiltonianVectorField H) 1 univ := fun p _ =>
  ⟨differentiableAt_id, by rw [fderiv_id, ContinuousLinearMap.id_apply, one_smul]; rfl⟩

/-- The physical Hamiltonian `Re H / 2`: the certificate's `Re H` is `2 H_phys`, clock `2`. -/
def probeHphys : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ := fun p => realHam toyCert2.H p / 2

theorem probe_transport :
    IsFieldTransport id (fun p => 2 * probeHphys p) (hamiltonianVectorField probeHphys) (2 * 1)
      univ :=
  (id_isFieldTransport probeHphys).const_mul two_ne_zero

/-- **`CertifiedTorusAt.physical`, `physical_energy` and `observable_bounds` on T2**: the physical
torus of `H_phys = Re H / 2` at the frequency `(2 · 1)⁻¹ s∞ ω*`, on the level `E₀ / 2`, with the
action `I₀` enclosed from the real-torus check (`Λ = 1`). -/
theorem probe_physical :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧
      IsPhysicalFlowTorus (hamiltonianVectorField probeHphys)
        ((2 * 1 : ℝ)⁻¹ • (sinf • ![lunarNuMinus / 2, 1 / 2])) (id ∘ realRestriction Kinf) ∧
      (∀ θ, probeHphys (id (realRestriction Kinf θ)) = (toyCert2.params.E0 : ℝ) / 2) ∧
      ∀ θ, ((974 / 1000 : ℚ) : ℝ) - 1 * toyCert2.params.disp ≤ (realRestriction Kinf θ).2 0 ∧
        (realRestriction Kinf θ).2 0 ≤ ((976 / 1000 : ℚ) : ℝ) + 1 * toyCert2.params.disp := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff _ _).1 toyCert2_torus
  have hH := isRealHolo_of_checkHamBounds probe_static probe_hamBounds
  have hHc : ∀ p ∈ (univ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))),
      (fun p => 2 * probeHphys p) p = realHam toyCert2.H p := fun p _ => by
    simp only [probeHphys]; ring
  obtain ⟨-, -, hflow⟩ := hT.physical probe_static hH isOpen_univ (fun _ _ => mem_univ _) hHc
    (by norm_num) probe_transport
  have hrange : ∀ x : Fin 2 → ℝ,
      ‖(toyCert2.K (realInclusion 2 x)).2 0 - (((975 / 1000 : ℚ) : ℝ) : ℂ)‖ ≤
        ((1 / 1000 : ℚ) : ℝ) :=
    checkActionRangeReal_sound probe_static (i := 0)
      (show checkActionRangeReal toyCert2 0 (975 / 1000) (1 / 1000) = true by decide +kernel)
  -- the action observable `p ↦ p.2 0`, a continuous linear map of norm `≤ 1`
  set f := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)) with hf
  have hfn : ‖f‖ ≤ 1 := f.opNorm_le_bound zero_le_one fun z => by
    rw [one_mul]
    exact (norm_le_pi_norm z.2 0).trans (norm_snd_le z)
  have hfa : ∀ z : (Fin 2 → ℝ) × (Fin 2 → ℝ), f z = z.2 0 := fun _ => rfl
  refine ⟨Kinf, sinf, hT, hflow, hT.physical_energy probe_static hH isOpen_univ
    (fun _ _ => mem_univ _) hHc two_ne_zero (fun _ _ => rfl), fun θ => ?_⟩
  have hK := fun θ => abs_le.1 (abs_realRestriction_K_snd_sub_le hrange θ)
  have h := hT.observable_bounds probe_static (f := f) convex_univ (fun _ _ => mem_univ _)
    (fun _ => mem_univ _) (Λ := 1) (fun z _ => f.differentiableAt)
    (fun z _ => by rw [f.fderiv]; exact hfn)
    (lo := ((974 / 1000 : ℚ) : ℝ)) (hi := ((976 / 1000 : ℚ) : ℝ))
    (fun θ => by rw [hfa]; have := (hK θ).1; push_cast at this ⊢; linarith)
    (fun θ => by rw [hfa]; have := (hK θ).2; push_cast at this ⊢; linarith) θ
  rwa [hfa] at h

end KAM.Application.Tests
