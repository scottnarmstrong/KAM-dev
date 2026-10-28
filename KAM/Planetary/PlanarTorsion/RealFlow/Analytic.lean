/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.ODE.Basic
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Planetary.PlanarTorsion.RealFlow.PicardData

/-!
# Planar quartic torsion: real analytic parametric flow (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2).  For a real analytic vector field `f` near
`x ∈ ℝⁿ` the local flow `Φ (t, y)` is jointly real analytic on `Ioo (-T) T ×ˢ ball x r`.  The proof
extends `f` to a holomorphic `F` on a complex ball (`p11_complexification`), runs the complex-time
Picard iteration of `PicardComplex` (holomorphic iterates, geometric uniform convergence,
holomorphic limit by `KAM.Weighted.uniform_limit_holomorphic`), restricts the limit to real time
and real data, and differentiates the resulting integral equation.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Planetary

variable {n : ℕ}

/-- The real-linear embedding `(t, y) ↦ (t, y₁, …, yₙ) ∈ ℂⁿ⁺¹`. -/
def p11cPt (n : ℕ) : ℝ × (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (Fin.cons (z.1 : ℂ) (fun i => (z.2 i : ℂ)) : Fin (n + 1) → ℂ)
      map_add' := fun a b => by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun a z => by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }

@[simp] theorem p11cPt_zero (z : ℝ × (Fin n → ℝ)) : p11cPt n z 0 = z.1 := by
  simp [p11cPt]

@[simp] theorem p11cPt_succ (z : ℝ × (Fin n → ℝ)) (i : Fin n) : p11cPt n z i.succ = z.2 i := by
  simp [p11cPt]

theorem p11cSp_p11cPt (z : ℝ × (Fin n → ℝ)) : p11cSp n (p11cPt n z) = realInclusion n z.2 := by
  ext i; simp

theorem p11cTimeScale_p11cPt (σ t : ℝ) (y : Fin n → ℝ) :
    p11cTimeScale n σ (p11cPt n (t, y)) = p11cPt n (σ * t, y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [p11cTimeScale_zero]
  · have := congrFun (p11cSp_timeScale (n := n) σ (p11cPt n (t, y))) j
    simpa using this

theorem p11cIsReal_realInclusion (y : Fin n → ℝ) : p11cIsReal (realInclusion n y) := fun i => by
  simp

theorem p11c_eq_realInclusion {X : Fin n → ℂ} (h : p11cIsReal X) :
    X = realInclusion n (realPartCLM n X) := by
  ext i; exact Complex.ext (by simp) (by simpa using h i)

/-- From the integral equation `Φ t = y + t ∫₀¹ g (σ t) dσ` to `Φ' = g`. -/
theorem p11c_hasDerivAt_of_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g Φ : ℝ → E} {y : E} {T : ℝ} (hg : ContinuousOn g (Ioo (-T) T))
    (heq : ∀ t ∈ Ioo (-T) T, Φ t = y + t • ∫ σ in (0 : ℝ)..1, g (σ * t)) :
    ∀ t ∈ Ioo (-T) T, HasDerivAt Φ (g t) t := by
  have hint : ∀ t ∈ Ioo (-T) T, Φ t = y + ∫ τ in (0 : ℝ)..t, g τ := by
    intro t ht
    rw [heq t ht]
    by_cases h0 : t = 0
    · simp [h0]
    · congr 1
      have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) g h0
      simp only [mul_zero, mul_one] at this
      simp_rw [mul_comm _ t] at *
      rw [this, smul_inv_smul₀ h0]
  intro t₀ ht₀
  have hsub : uIcc (0 : ℝ) t₀ ⊆ Ioo (-T) T :=
    (ordConnected_Ioo).uIcc_subset ⟨by linarith [ht₀.1, ht₀.2], by linarith [ht₀.1, ht₀.2]⟩ ht₀
  have hF : HasDerivAt (fun t => ∫ τ in (0 : ℝ)..t, g τ) (g t₀) t₀ :=
    intervalIntegral.integral_hasDerivAt_right (hg.mono hsub |>.intervalIntegrable)
      (hg.stronglyMeasurableAtFilter isOpen_Ioo _ ht₀)
      ((hg.continuousAt (isOpen_Ioo.mem_nhds ht₀)))
  refine (hF.const_add y).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht using hint t ht

end KAM.Planetary
