/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The value of the Taylor polynomial (blueprint-W `bpW:w5:taylor` step `t-poly`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`taylorRv_eq`: with `w₀ = (θ,0,0,0)`, `c₁ = (0,0,u,v)`, `c₂ = (0,y,0,0)`,
`R(w) = P(w₀) + ϖ(X(w₀), c₁ + c₂) + ½ ϖ(DX(w₀) c₁, c₁)`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

theorem taylorCoeff_zero {g : ℂ → ℂ} : taylorCoeff g 0 = g 0 := by simp [taylorCoeff]

/-- The curve `t ↦ S_t w = w₀ + t c₁ + t² c₂`. -/
theorem scaleS_eq (t : ℂ) (w : KamPhase) :
    scaleS t w = stepW0L w.1 + t • ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), w.2.2.1, w.2.2.2) +
      t ^ 2 • ((0 : Fin 2 → ℂ), w.2.1, (0 : HomL2), (0 : HomL2)) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [scaleS, stepW0L_apply]

section value

variable (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hr : 0 < r)
  (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)

include hr hP

/-- **`R` explicitly** (`bpW:w5:taylor` step `t-poly`). -/
theorem taylorRv_eq {w : KamPhase} (hw : w ∈ kamDomain s r) :
    taylorRv P w =
      P (stepW0L w.1) +
        stepSymp (q := pb) (q' := p) ha hqq (X (stepW0L w.1)) (0, 0, w.2.2.1, w.2.2.2) +
        (2 : ℂ)⁻¹ * (stepSymp (q := pb) (q' := p) ha hqq
            (fderiv ℂ X (stepW0L w.1) (0, 0, w.2.2.1, w.2.2.2)) (0, 0, w.2.2.1, w.2.2.2) +
          2 * stepSymp (q := pb) (q' := p) ha hqq (X (stepW0L w.1)) (0, w.2.1, 0, 0)) := by
  set w0 := stepW0L w.1 with hw0
  set c1 : KamPhase := (0, 0, w.2.2.1, w.2.2.2) with hc1
  set c2 : KamPhase := (0, w.2.1, 0, 0) with hc2
  have hV := kamDomain_isOpen s r
  have hcc : ∀ t : ℂ, scaleS t w = w0 + t • c1 + t ^ 2 • c2 := fun t => scaleS_eq t w
  have hccd : ∀ t : ℂ, HasDerivAt (fun t : ℂ => scaleS t w) (c1 + (2 * t) • c2) t := by
    intro t
    have e : (fun t : ℂ => scaleS t w) = fun t : ℂ => w0 + t • c1 + t ^ 2 • c2 := funext hcc
    rw [e]
    have h1 : HasDerivAt (fun t : ℂ => t • c1) c1 t := by
      simpa using (hasDerivAt_id t).smul_const c1
    have h2 : HasDerivAt (fun t : ℂ => t ^ 2 • c2) ((2 * t) • c2) t := by
      simpa using (hasDerivAt_pow 2 t).smul_const c2
    exact (h1.const_add w0).add h2
  have hw0V : w0 ∈ kamDomain s r := stepW0L_mem hr (fun i => hw.1 i)
  have hS0 : scaleS 0 w = w0 := by rw [hcc]; simp
  have hevV : ∀ᶠ t in 𝓝 (0 : ℂ), scaleS t w ∈ kamDomain s r := by
    have hc : ContinuousAt (fun t : ℂ => scaleS t w) 0 := (hccd 0).continuousAt
    exact hc.eventually (hV.mem_nhds (by show scaleS 0 w ∈ kamDomain s r; rw [hS0]; exact hw0V))
  set ψ : ℂ → ℂ := fun t => P (scaleS t w) with hψ
  set χ : ℂ → ℂ := fun t => stepSymp (q := pb) (q' := p) ha hqq (X (scaleS t w))
    (c1 + (2 * t) • c2) with hχ
  have hψ' : ∀ᶠ t in 𝓝 (0 : ℂ), deriv ψ t = χ t := by
    filter_upwards [hevV] with t ht
    have hPd : DifferentiableAt ℂ P (scaleS t w) :=
      hP.holoP.differentiableAt (hV.mem_nhds ht)
    have := hPd.hasFDerivAt.comp_hasDerivAt t (hccd t)
    rw [show deriv ψ t = _ from this.deriv, hP.deriv_eq _ ht]
  have hψ1 : deriv ψ 0 = stepSymp (q := pb) (q' := p) ha hqq (X w0) c1 := by
    rw [hψ'.self_of_nhds]
    simp [hχ, hS0]
  have hXd : DifferentiableAt ℂ X w0 := hP.holoX.differentiableAt (hV.mem_nhds hw0V)
  have hχd : HasDerivAt χ (stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w0 c1) c1 +
      2 * stepSymp (q := pb) (q' := p) ha hqq (X w0) c2) 0 := by
    have g1 : HasDerivAt (fun t : ℂ => X (scaleS t w)) (fderiv ℂ X w0 c1) 0 := by
      have h1 : HasFDerivAt X (fderiv ℂ X w0) (scaleS 0 w) := by rw [hS0]; exact hXd.hasFDerivAt
      have := h1.comp_hasDerivAt 0 (hccd 0)
      have e : c1 + (2 * (0 : ℂ)) • c2 = c1 := by simp
      rw [e] at this
      exact this
    have g2 : HasDerivAt (fun t : ℂ => sympK (q := pb) (q' := p) ha hqq (X (scaleS t w)))
        (sympK (q := pb) (q' := p) ha hqq (fderiv ℂ X w0 c1)) 0 :=
      (sympK (q := pb) (q' := p) ha hqq).hasFDerivAt.comp_hasDerivAt 0 g1
    have g3 : HasDerivAt (fun t : ℂ => c1 + (2 * t) • c2) ((2 : ℂ) • c2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 2 |>.smul_const c2).const_add c1
    have := g2.clm_apply g3
    simpa [hχ, sympK_apply, hS0] using this
  have hψ2 : deriv (deriv ψ) 0 = stepSymp (q := pb) (q' := p) ha hqq (fderiv ℂ X w0 c1) c1 +
      2 * stepSymp (q := pb) (q' := p) ha hqq (X w0) c2 := by
    have : deriv ψ =ᶠ[𝓝 0] χ := hψ'
    rw [this.deriv_eq]
    exact hχd.deriv
  unfold taylorRv
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  change taylorCoeff ψ 0 + taylorCoeff ψ 1 + taylorCoeff ψ 2 = _
  rw [taylorCoeff_zero, taylorCoeff_one, taylorCoeff_two, hψ1, hψ2]
  have h0 : ψ 0 = P w0 := by simp [hψ, hS0]
  rw [h0]

end value

end KAM.Wave
