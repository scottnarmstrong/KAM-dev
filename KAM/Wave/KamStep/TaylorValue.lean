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

theorem c1_decomp (w : KamPhase) :
    ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), w.2.2.1, w.2.2.2) =
      stepIotaZ (stepZ w) + stepIotaZb (stepZb w) := by
  obtain ⟨θ, y, u, v⟩ := w
  rw [stepZ_apply, stepZb_apply, stepIotaZ_apply, stepIotaZb_apply]
  have h2 := homSqrt2_inv_sq
  refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext ?_ ?_))
  · show u = _
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      lp.coeFn_sub, Pi.sub_apply, Prod.fst_add, Prod.snd_add]
    linear_combination (-2 * (u j : ℂ)) * h2
  · show v = _
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      lp.coeFn_sub, Pi.sub_apply, Prod.fst_add, Prod.snd_add]
    linear_combination (-2 * (v j : ℂ)) * h2 + ((homSqrt2⁻¹ * homSqrt2⁻¹) * (v j : ℂ) * 2) *
        Complex.I_sq

theorem stepZ_c1 (w : KamPhase) : stepZ ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), w.2.2.1, w.2.2.2) =
    stepZ w := by
  simp [stepZ]

theorem stepZb_c1 (w : KamPhase) :
    stepZb ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), w.2.2.1, w.2.2.2) = stepZb w := by
  simp [stepZb]

section pieces

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)

/-- Linear part. -/
theorem stepSymp_linear (Y : KamPhase) (w : KamPhase) :
    stepSymp (q := p) (q' := pb) ha (homPP hp hpb) Y (0, 0, w.2.2.1, w.2.2.2) =
      Complex.I * (stepPr ha (homPP hp hpb) (stepZ Y) (stepZb w) -
        stepPr ha (homPP hp hpb) (stepZb Y) (stepZ w)) := by
  rw [stepSymp_z, stepZ_c1, stepZb_c1]
  simp

/-- The `y`-part. -/
theorem stepSymp_ypart (Y : KamPhase) (w : KamPhase) :
    stepSymp (q := p) (q' := pb) ha (homPP hp hpb) Y (0, w.2.1, 0, 0) =
      2 * Real.pi * ∑ i, Y.1 i * w.2.1 i := by
  rw [stepSymp_z]
  have h1 : stepZ ((0 : Fin 2 → ℂ), w.2.1, (0 : HomL2), (0 : HomL2)) = 0 := by simp [stepZ]
  have h2 : stepZb ((0 : Fin 2 → ℂ), w.2.1, (0 : HomL2), (0 : HomL2)) = 0 := by simp [stepZb]
  rw [h1, h2]
  simp

/-- The quadratic part. -/
theorem stepSymp_quadratic (A : KamPhase →L[ℂ] KamPhase)
    (hA : ∀ u v, stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A u) v =
      stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A v) u) (w : KamPhase) :
    stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A (0, 0, w.2.2.1, w.2.2.2))
        (0, 0, w.2.2.1, w.2.2.2) =
      2 * (stepPr ha (homPP hp hpb) (blockP A (stepZ w)) (stepZ w) +
        stepPr ha (homPP hp hpb) (blockQ A (stepZ w)) (stepZb w) +
        stepPr ha (homPP hp hpb) (blockP' A (stepZb w)) (stepZb w)) := by
  rw [c1_decomp, map_add]
  simp only [stepSymp_add_left, stepSymp_add_right]
  have e1 := stepPr_blockP ha (homPP hp hpb) A (stepZ w) (stepZ w)
  have e2 := stepPr_blockQ ha (homPP hp hpb) A (stepZ w) (stepZb w)
  have e3 := stepPr_blockQt ha (homPP hp hpb) A (stepZb w) (stepZ w)
  have e4 := stepPr_blockP' ha (homPP hp hpb) A (stepZb w) (stepZb w)
  have hs := hA (stepIotaZb (stepZb w)) (stepIotaZ (stepZ w))
  linear_combination (-2 : ℂ) * e1 - 2 * e4 - 2 * e2 + hs

end pieces

/-- **`R = waveStepFun T`** (`bpW:w5:taylor` (i), last claim): the value of the Taylor polynomial of
`P` is the polynomial of the element `T = stepTaylorOf … ∈ 𝒯_s`. -/
theorem stepFun_taylorOf_eq (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    waveStepFun ha (homPP hp hpb) (stepTaylorOf ha hp hpb hs hr hP hper hb) w = taylorRv P w := by
  rw [taylorRv_eq ha _ hr hP hw]
  have hw0 : stepW0L w.1 ∈ kamDomain s r := stepW0L_mem hr (fun i => hw.1 i)
  set Y := X (stepW0L w.1) with hY
  set A := fderiv ℂ X (stepW0L w.1) with hA
  have hqq' : 0 ≤ pb + p := by linarith
  have cw := fun (U V : KamPhase) => stepSymp_comm_weights (q := pb) (q' := p) ha hqq'
    (homPP hp hpb) U V
  rw [cw, cw, cw]
  rw [stepSymp_linear ha hp hpb, stepSymp_ypart ha hp hpb,
    stepSymp_quadratic ha hp hpb A (stepDX_symm_pp ha hp hpb hP hw0)]
  unfold waveStepFun
  simp only [stepTaylorOf, tA0, tB, tCp, tCm, tP, tP', tQ, tQt]
  simp only [map_smul, smul_apply, smul_eq_mul, hY]
  rw [Finset.mul_sum]
  simp only [← hA]
  have e : ∑ i, 2 * (Real.pi : ℂ) * ((X (stepW0L w.1)).1 i * w.2.1 i) =
      ∑ k, 2 * (Real.pi : ℂ) * (X (stepW0L w.1)).1 k * w.2.1 k :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-- **`X_R = X_{T}`** (`bpW:w5:taylor` (ii), step `t-field`): the field of the polynomial of
`T = stepTaylorOf …` is the Taylor field `taylorXR X` on `D(s,r)`. -/
theorem stepField_taylorOf_eq (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    stepField ha hp hpb (stepTaylorOf ha hp hpb hs hr hP hper hb) w = taylorXR X w := by
  set T := stepTaylorOf ha hp hpb hs hr hP hper hb with hT
  have hV := kamDomain_isOpen s r
  obtain ⟨D, hD, hDW⟩ := stepFun_field ha hp hpb T (w := w) (fun i => hw.1 i)
  have hqq' : 0 ≤ pb + p := by linarith
  have key : ∀ W : KamPhase, stepSymp (q := p) (q' := pb) ha (homPP hp hpb)
      (stepField ha hp hpb T w) W =
      stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (taylorXR X w) W := by
    intro W
    -- the derivative of ε ↦ waveStepFun T (w + εW) at 0
    have hline : HasDerivAt (fun ε : ℂ => w + ε • W) W 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add w
    have h1 : HasDerivAt (fun ε : ℂ => waveStepFun ha (homPP hp hpb) T (w + ε • W)) (D W) 0 := by
      have : HasFDerivAt (waveStepFun ha (homPP hp hpb) T) D (w + (0 : ℂ) • W) := by simpa using hD
      exact this.comp_hasDerivAt 0 hline
    have hS0 : scaleS 0 w ∈ kamDomain s r := by
      have : scaleS 0 w = stepW0L w.1 := by simp [scaleS, stepW0L_apply]
      rw [this]; exact stepW0L_mem hr (fun i => hw.1 i)
    have h2 := hasDerivAt_taylorRv hV hP.holoP (w := w) (W' := W) hS0
    have hev : ∀ᶠ ε in 𝓝 (0 : ℂ), w + ε • W ∈ kamDomain s r := by
      have hc : ContinuousAt (fun ε : ℂ => w + ε • W) 0 := hline.continuousAt
      exact hc.eventually (hV.mem_nhds (by simpa using hw))
    have h3 : HasDerivAt (fun ε : ℂ => taylorRv P (w + ε • W)) (D W) 0 := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with ε hε
      exact (stepFun_taylorOf_eq ha hp hpb hs hr hP hper hb hε).symm
    have h4 := h3.unique h2
    rw [sum_taylorCoeff_symp ha hqq' hP hr hw W] at h4
    rw [← hDW W, h4, stepSymp_comm_weights ha hqq' (homPP hp hpb)]
  exact sub_eq_zero.mp (stepSymp_nondeg (q := p) (q' := pb) ha (homPP hp hpb)
    (W := stepField ha hp hpb T w - taylorXR X w) (fun W => by
      rw [stepSymp_sub_left, key W, sub_self]))

end KAM.Wave
