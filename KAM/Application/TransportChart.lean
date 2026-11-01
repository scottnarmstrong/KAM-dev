/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Transport
public import KAM.Planetary.Hamiltonian.Chart

/-!
# The transport identity from a conformally symplectic chart

`isFieldTransport_of_isChart`: a core `c`-chart `Ψ` on the open `O` (`KAM.Planetary.IsChart c Ψ O`:
analytic, `Ω(DΨ u, DΨ v) = c Ω(u, v)`) and a model Hamiltonian `Hc = a · H ∘ Ψ` on `O` (`a ≠ 0`)
satisfy the transport identity `DΨ X_{Hc} = (a c) X_H ∘ Ψ` on `O` (via the core's `chart_field`,
`DΨ X_{c⁻¹ H ∘ Ψ} = X_H ∘ Ψ`). LG00's chart is of this kind with `c = 2πℓ`, `a = κ/ℓ`
(`Ψ*(Σ dξ ∧ dη) = 2πℓ Σ da ∧ dθ`), up to the order of LG00's variables, so its clock is `2πκ`.

This module imports the core chart layer (which imports all of Mathlib); the field-identity
interface itself is in the lighter `KAM/Application/Transport.lean`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace KAM.Application

open KAM KAM.Planetary

variable {d : ℕ}

/-- **The transport identity from a `c`-chart**: `Ψ` a `c`-chart on the open `O` (`c > 0`) and
`Hc = a · H ∘ Ψ` on `O` (`a ≠ 0`) give `DΨ X_{Hc} = (a c) X_H ∘ Ψ` on `O`. -/
theorem isFieldTransport_of_isChart {c a : ℝ} (hc : 0 < c) (ha : a ≠ 0)
    {Ψ : Phase d → Phase d} {O : Set (Phase d)} (hO : IsOpen O) (hΨ : IsChart c Ψ O)
    {H Hc : Phase d → ℝ} (hHc : ∀ p ∈ O, Hc p = a * H (Ψ p)) :
    IsFieldTransport Ψ Hc (hamiltonianVectorField H) (a * c) O := by
  intro p hp
  refine ⟨(hΨ.1 p hp).differentiableAt, ?_⟩
  have hev : Hc =ᶠ[𝓝 p] fun q => (a * c) * chartPullback c H Ψ q :=
    eventuallyEq_of_mem (hO.mem_nhds hp) fun q hq => by
      simp only [chartPullback]
      rw [hHc q hq]
      field_simp
  rw [hamiltonianVectorField_congr hev,
    hamiltonianVectorField_const_mul (mul_ne_zero ha hc.ne'), map_smul, chart_field hc hΨ H hp]

/-- The chart's derivative is injective on `O` (for `injective_fderiv_comp`). -/
theorem IsChart.injective_fderiv {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d}
    {O : Set (Phase d)} (hΨ : IsChart c Ψ O) {p : Phase d} (hp : p ∈ O) :
    Function.Injective (fderiv ℝ Ψ p) :=
  (hΨ.bijective_fderiv hc hp).1

end KAM.Application
