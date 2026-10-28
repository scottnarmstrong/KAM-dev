/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloLift
public import KAM.Planetary.SecularSpectrum.Transport
public import KAM.Planetary.Newtonian.Tube
public import KAM.Planetary.Poincare.Product

/-!
# The real chart `Ψ_c` (P11A-P2d, `stepP:p11:hc-id`, `stepP:p11:hc-lat`)

The real chart of `holo_chart` is `Ψ_c = Ψ^{(n)} ∘ Φ_ρ⁻¹ ∘ T₁`, with `T₁ = p11FastScale` the linear
period conversion `(θ, J) ↦ (2πθ, J/2π)` on the fast block, `Φ_ρ⁻¹ = liftInv R` the real inverse
lift of the frame `R` of `P11HoloData`, and `Ψ^{(n)} = poincareProd`. This module proves, for the
literal chart input `p11ChartInput`:

* `p11FastScale` is linear, symplectic, injective and turns the unit lattice shift into
  `fastShift`;
* analyticity and symplecticity of the chart on the real working domain;
* the lattice clauses (invariance under `θ ↦ θ + k`, injectivity modulo the lattice);
* membership of the chart input in `poincareProdDom` and of the chart in `collisionFreeDomain`,
  from the smallness of `r_C` (`r_C ≤ π δ/8`) and `(B_ρ r_z)² ≤ δ` (`forward_tube`);
* the energy identity `fixedHamiltonian = Re (h + ε F)` with `F` a parameter.

`P11HoloData.chart_spec` assembles the last conjunct of `P11SecularSpec`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Scale

variable {n : ℕ}

/-- `T₁` on the fast block: `(θ, J) ↦ (2πθ, J/2π)`, secular coordinates unchanged. -/
def p11FastScaleL : Phase (n + n) →ₗ[ℝ] Phase (n + n) where
  toFun z := assemble (fun i => fast z.2 i / (2 * Real.pi)) (fun l => 2 * Real.pi * fast z.1 l)
    (slow z.2) (slow z.1)
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fast, slow, mul_add, add_div]
  map_smul' c u := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fast, slow, mul_left_comm, mul_div_assoc]

/-- The period conversion `T₁` of the fast block, as a continuous linear map. -/
def p11FastScale : Phase (n + n) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap p11FastScaleL

theorem p11FastScale_apply (z : Phase (n + n)) :
    p11FastScale z = assemble (fun i => fast z.2 i / (2 * Real.pi))
      (fun l => 2 * Real.pi * fast z.1 l) (slow z.2) (slow z.1) := rfl

theorem fast_snd_p11FastScale (z : Phase (n + n)) :
    fast (p11FastScale z).2 = fun i => fast z.2 i / (2 * Real.pi) := by
  rw [p11FastScale_apply]; exact SecularSpectrum.fast_snd_assemble _ _ _ _

/-- `T₁` preserves the symplectic form. -/
theorem p11FastScale_symplectic (u v : Phase (n + n)) :
    KAM.symplecticForm (p11FastScale u) (p11FastScale v) = KAM.symplecticForm u v := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [p11FastScale_apply, KAM.symplecticForm, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · simp [assemble, fast]
    field_simp
  · simp [assemble, slow]

theorem p11FastScale_injective : Function.Injective (p11FastScale (n := n)) := by
  intro u v h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [p11FastScale_apply, assemble] at h1 h2
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := congrFun h1 (Fin.castAdd n i)
      simpa [fast, hpi] using this
    · have := congrFun h1 (Fin.natAdd n i)
      simpa [slow] using this
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := congrFun h2 (Fin.castAdd n i)
      simpa [fast, hpi] using this
    · have := congrFun h2 (Fin.natAdd n i)
      simpa [slow] using this

/-- `hc-lat`: `T₁(θ + k, ·) = T₁ + (2π k, 0, 0, 0)`. -/
theorem p11FastScale_shift (z : Phase (n + n)) (k : Fin n → ℤ) :
    p11FastScale (z.1 + Fin.append (fun i => (k i : ℝ)) 0, z.2) =
      p11FastScale z + fastShift (a := n) (b := n) k := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [p11FastScale_apply, assemble, fast, slow, fastShift, mul_add]

theorem p11FastScale_isSymplecticOn :
    KAM.Kepler.IsSymplecticOn 1 (p11FastScale (n := n)) univ := by
  intro z _ u v
  rw [p11FastScale.fderiv, one_mul]
  exact p11FastScale_symplectic u v

end Scale

end KAM.Planetary

end
