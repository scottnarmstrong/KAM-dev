/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Kepler.Basic
public import KAM.Canonical.Setting
public import KAM.Strip.Analytic
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.Hamiltonian.Chart

/-!
# Holomorphic charts

`bpP:p1:hol-chart` and `stepP:p1:hc-real-derivative`. A holomorphic map `Ψ` on an arbitrary open
`V ⊆ ℂᵈ × ℂᵈ`, with a real total extension `Ψr` on the real slice `phaseToC ⁻¹' V`, is real-analytic
there, its real derivative is the restriction of the complex derivative, and conformal symplecticity
of the complex derivative gives a `c`-chart.
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Planetary

open KAM KAM.Kepler

section HolChart

variable {d : ℕ}

/-- The real-linear inclusion `Phase d → ℂᵈ × ℂᵈ`, of which `phaseToC` is the underlying map. -/
private def phaseToCL (d : ℕ) : Phase d →L[ℝ] (Fin d → ℂ) × (Fin d → ℂ) :=
  (realInclusion d).prodMap (realInclusion d)

private theorem phaseToCL_apply (z : Phase d) : phaseToCL d z = phaseToC z := rfl

private def realPartL (d : ℕ) : ((Fin d → ℂ) × (Fin d → ℂ)) →L[ℝ] Phase d :=
  (realPartCLM d).prodMap (realPartCLM d)

private theorem realPartL_phaseToC (z : Phase d) : realPartL d (phaseToC z) = z := by
  ext i <;> simp [realPartL, phaseToC]

private theorem symplFormC_phaseToC (u v : Phase d) :
    KAM.Canonical.symplFormC (phaseToC u) (phaseToC v) = ((symplecticForm u v : ℝ) : ℂ) := by
  simp [KAM.Canonical.symplFormC, symplecticForm, phaseToC]

private theorem isOpen_preimage_phaseToC {V : Set ((Fin d → ℂ) × (Fin d → ℂ))} (hV : IsOpen V) :
    IsOpen (phaseToC ⁻¹' V) :=
  hV.preimage (phaseToCL d).continuous

/-- `stepP:p1:hc-real-derivative`: on the real slice of an arbitrary open `V`, the real derivative
of a real-at-real-points holomorphic map is the restriction of the complex derivative. -/
theorem fderiv_real_slice {V : Set ((Fin d → ℂ) × (Fin d → ℂ))} (hV : IsOpen V)
    {Ψ : (Fin d → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) × (Fin d → ℂ)} (hΨ : DifferentiableOn ℂ Ψ V)
    {Ψr : Phase d → Phase d} (hagree : ∀ z, phaseToC z ∈ V → phaseToC (Ψr z) = Ψ (phaseToC z))
    {z : Phase d} (hz : phaseToC z ∈ V) :
    AnalyticAt ℝ Ψr z ∧
      ∀ u, phaseToC (fderiv ℝ Ψr z u) = fderiv ℂ Ψ (phaseToC z) (phaseToC u) := by
  have hΨa : AnalyticAt ℂ Ψ (phaseToC z) := analyticOnNhd_of_differentiableOn hV hΨ _ hz
  have hopen : phaseToC ⁻¹' V ∈ nhds z := (isOpen_preimage_phaseToC hV).mem_nhds hz
  have hev : Ψr =ᶠ[nhds z] fun z' => realPartL d (Ψ (phaseToCL d z')) := by
    filter_upwards [hopen] with z' hz'
    rw [phaseToCL_apply, ← hagree z' hz', realPartL_phaseToC]
  have hcomp : AnalyticAt ℝ (Ψ ∘ phaseToCL d) z :=
    (hΨa.restrictScalars (𝕜 := ℝ)).comp ((phaseToCL d).analyticAt z)
  have hana : AnalyticAt ℝ Ψr z :=
    (((realPartL d).analyticAt _).comp hcomp).congr hev.symm
  refine ⟨hana, fun u => ?_⟩
  have h1 : HasFDerivAt (fun z' => phaseToCL d (Ψr z'))
      ((phaseToCL d).comp (fderiv ℝ Ψr z)) z :=
    (phaseToCL d).hasFDerivAt.comp z hana.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (Ψ ∘ phaseToCL d)
      (((fderiv ℂ Ψ (phaseToC z)).restrictScalars ℝ).comp (phaseToCL d)) z := by
    have := (hΨa.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp z
      (phaseToCL d).hasFDerivAt
    exact this
  have heq : (fun z' => phaseToCL d (Ψr z')) =ᶠ[nhds z] Ψ ∘ phaseToCL d := by
    filter_upwards [hopen] with z' hz'
    simp only [phaseToCL_apply, Function.comp]
    exact hagree z' hz'
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  have := congrArg (fun L => L u) this
  simpa [phaseToCL_apply] using this

/-- `bpP:p1:hol-chart`: a holomorphic, conformally symplectic map, real at real points, restricts
to a `c`-chart on `O = V ∩ ℝ^{2d}` (any total extension `Ψr` off `O`). -/
theorem hol_chart {c : ℝ} (hc : 0 < c) {V : Set ((Fin d → ℂ) × (Fin d → ℂ))} (hV : IsOpen V)
    {Ψ : (Fin d → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) × (Fin d → ℂ)} (hΨ : DifferentiableOn ℂ Ψ V)
    (hsympl : ∀ z : Phase d, phaseToC z ∈ V → ∀ u v,
      KAM.Canonical.symplFormC (fderiv ℂ Ψ (phaseToC z) u) (fderiv ℂ Ψ (phaseToC z) v) =
        (c : ℂ) * KAM.Canonical.symplFormC u v)
    {Ψr : Phase d → Phase d} (hagree : ∀ z, phaseToC z ∈ V → phaseToC (Ψr z) = Ψ (phaseToC z)) :
    IsOpen (phaseToC ⁻¹' V) ∧ IsChart c Ψr (phaseToC ⁻¹' V) ∧
      ∀ z, phaseToC z ∈ V → ∀ u,
        phaseToC (fderiv ℝ Ψr z u) = fderiv ℂ Ψ (phaseToC z) (phaseToC u) := by
  have hder := fun z (hz : phaseToC z ∈ V) => fderiv_real_slice hV hΨ hagree hz
  refine ⟨isOpen_preimage_phaseToC hV, ⟨fun z hz => (hder z hz).1, fun z hz u v => ?_⟩,
    fun z hz => (hder z hz).2⟩
  have h := hsympl z hz (phaseToC u) (phaseToC v)
  rw [← (hder z hz).2, ← (hder z hz).2, symplFormC_phaseToC, symplFormC_phaseToC] at h
  exact_mod_cast h

end HolChart

end KAM.Planetary
