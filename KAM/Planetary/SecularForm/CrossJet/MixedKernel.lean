/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.CrossJet.Parametric
public import KAM.Planetary.SecularForm.CrossJet.Variation

/-!
# Cross jet: the mixed Hessian of the pair kernel

Blueprint P, Part 8, `stepP:p8:qf-cross`: the mixed second derivative of `-c/|α(s) - β(t)|` at
`(0,0)`
in terms of the first variations `α'`, `β'` and the separation `d = α 0 - β 0` is
`c (3 (d·α')(d·β')/|d|⁵ - (α'·β')/|d|³)` (`crossKernel`). It is computed from the two one-variable
derivatives (`t` first, then `s`), then identified with the second Fréchet derivative.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm

/-- Mixed Hessian of `-c/|α(s) - β(t)|`: `c (3 (d·x)(d·z)/|d|⁵ - (x·z)/|d|³)`. -/
def crossKernel (c : ℝ) (d x z : Fin 2 → ℝ) : ℝ :=
  c * (3 * (d 0 * x 0 + d 1 * x 1) * (d 0 * z 0 + d 1 * z 1) / planeLength d ^ 5 -
    (x 0 * z 0 + x 1 * z 1) / planeLength d ^ 3)

theorem planeLength_eq_sqrt (d : Fin 2 → ℝ) : planeLength d = √(d 0 ^ 2 + d 1 ^ 2) := by
  simp [planeLength, planeSq, Fin.sum_univ_two]

/-- The `t`-derivative of the pair integrand at `t = 0`. -/
theorem hasDerivAt_pair_t (c : ℝ) (a : Fin 2 → ℝ) {β : ℝ → Fin 2 → ℝ} {β' : Fin 2 → ℝ}
    (hβ : HasDerivAt β β' 0) (hne : a - β 0 ≠ 0) :
    HasDerivAt (fun t => -c / planeLength (a - β t))
      (-c * ((a 0 - β 0 0) * β' 0 + (a 1 - β 0 1) * β' 1) /
        (((a 0 - β 0 0) ^ 2 + (a 1 - β 0 1) ^ 2) *
          √((a 0 - β 0 0) ^ 2 + (a 1 - β 0 1) ^ 2))) 0 := by
  have h0 := (hasDerivAt_pi.1 hβ) 0
  have h1 := (hasDerivAt_pi.1 hβ) 1
  have hρ : HasDerivAt (fun t => (a 0 - β t 0) ^ 2 + (a 1 - β t 1) ^ 2)
      (-2 * ((a 0 - β 0 0) * β' 0 + (a 1 - β 0 1) * β' 1)) 0 := by
    have := (((hasDerivAt_const (0:ℝ) (a 0)).sub h0).pow 2).add
      (((hasDerivAt_const (0:ℝ) (a 1)).sub h1).pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hpos : 0 < (a 0 - β 0 0) ^ 2 + (a 1 - β 0 1) ^ 2 := by
    by_contra hle
    apply hne
    have h0' : a 0 - β 0 0 = 0 := by nlinarith [sq_nonneg (a 0 - β 0 0), sq_nonneg (a 1 - β 0 1)]
    have h1' : a 1 - β 0 1 = 0 := by nlinarith [sq_nonneg (a 0 - β 0 0), sq_nonneg (a 1 - β 0 1)]
    ext i; fin_cases i <;> simp [h0', h1']
  have hs := (hρ.sqrt hpos.ne')
  have hinv := hs.inv (Real.sqrt_pos.2 hpos).ne'
  have := hinv.const_mul (-c)
  refine (this.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Eventually.of_forall fun t => by simp [planeLength_eq_sqrt, div_eq_mul_inv]
  · have hsq := Real.sq_sqrt hpos.le
    have hq := (Real.sqrt_pos.2 hpos).ne'
    field_simp
    rw [hsq]

/-- The `s`-derivative of the `t`-derivative, at `s = 0`. -/
theorem hasDerivAt_pair_s (c : ℝ) {α : ℝ → Fin 2 → ℝ} {α' : Fin 2 → ℝ} (b : Fin 2 → ℝ)
    (β' : Fin 2 → ℝ) (hα : HasDerivAt α α' 0) (hne : α 0 - b ≠ 0) :
    HasDerivAt (fun s => -c * ((α s 0 - b 0) * β' 0 + (α s 1 - b 1) * β' 1) /
        (((α s 0 - b 0) ^ 2 + (α s 1 - b 1) ^ 2) * √((α s 0 - b 0) ^ 2 + (α s 1 - b 1) ^ 2)))
      (crossKernel c (α 0 - b) α' β') 0 := by
  have h0 := (hasDerivAt_pi.1 hα) 0
  have h1 := (hasDerivAt_pi.1 hα) 1
  have hd0 : HasDerivAt (fun s => α s 0 - b 0) (α' 0) 0 := by simpa using h0.sub_const (b 0)
  have hd1 : HasDerivAt (fun s => α s 1 - b 1) (α' 1) 0 := by simpa using h1.sub_const (b 1)
  have hpos : 0 < (α 0 0 - b 0) ^ 2 + (α 0 1 - b 1) ^ 2 := by
    by_contra hle
    apply hne
    have h0' : α 0 0 - b 0 = 0 := by nlinarith [sq_nonneg (α 0 0 - b 0), sq_nonneg (α 0 1 - b 1)]
    have h1' : α 0 1 - b 1 = 0 := by nlinarith [sq_nonneg (α 0 0 - b 0), sq_nonneg (α 0 1 - b 1)]
    ext i; fin_cases i <;> simp [h0', h1']
  have hρ := (hd0.pow 2).add (hd1.pow 2)
  have hsq := hρ.sqrt hpos.ne'
  have hnum := ((hd0.mul_const (β' 0)).add (hd1.mul_const (β' 1))).const_mul (-c)
  have hden := hρ.mul hsq
  have hq := hnum.div hden (mul_pos hpos (Real.sqrt_pos.2 hpos)).ne'
  have hs := Real.sq_sqrt hpos.le
  have hr := (Real.sqrt_pos.2 hpos).ne'
  have hlen : planeLength (α 0 - b) = √((α 0 0 - b 0) ^ 2 + (α 0 1 - b 1) ^ 2) := by
    rw [planeLength_eq_sqrt]; simp
  refine hq.congr_deriv ?_
  unfold crossKernel
  rw [hlen]
  simp
  field_simp
  rw [hs]
  ring_nf

theorem iteratedFDeriv_two_mixed (c : ℝ) {α β : ℝ → Fin 2 → ℝ} {α' β' : Fin 2 → ℝ}
    (hα : HasDerivAt α α' 0) (hβ : HasDerivAt β β' 0) (hne : α 0 - β 0 ≠ 0)
    {f : Vec 2 → ℝ} (hf : ∀ y, f y = -c / planeLength (α (y 0) - β (y 1)))
    (hC : ContDiffAt ℝ 2 f 0) :
    iteratedFDeriv ℝ 2 f 0 ![Pi.single 0 1, Pi.single 1 1] =
      crossKernel c (α 0 - β 0) α' β' := by
  set e0 : Vec 2 := Pi.single 0 1 with he0
  set e1 : Vec 2 := Pi.single 1 1 with he1
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline0 : HasDerivAt (fun s : ℝ => s • e0) e0 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const e0
  have H1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • e0)) (fderiv ℝ (fderiv ℝ f) 0 e0) 0 := by
    have h := hfd.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hline0 (by simp)
    exact h
  have H : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • e0) e1) (fderiv ℝ (fderiv ℝ f) 0 e0 e1) 0 := by
    simpa using H1.clm_apply (hasDerivAt_const (0:ℝ) e1)
  have N := hasDerivAt_pair_s c (β 0) β' hα hne
  have hev : ∀ᶠ s in 𝓝 (0:ℝ), fderiv ℝ f (s • e0) e1 =
      -c * ((α s 0 - β 0 0) * β' 0 + (α s 1 - β 0 1) * β' 1) /
        (((α s 0 - β 0 0) ^ 2 + (α s 1 - β 0 1) ^ 2) *
          √((α s 0 - β 0 0) ^ 2 + (α s 1 - β 0 1) ^ 2)) := by
    have hcont : ContinuousAt (fun s : ℝ => s • e0) 0 := by fun_prop
    have h1 : ∀ᶠ s in 𝓝 (0:ℝ), DifferentiableAt ℝ f (s • e0) := by
      have := hC.eventually (by simp)
      have h2 : ∀ᶠ y in 𝓝 (0 : Vec 2), DifferentiableAt ℝ f y :=
        this.mono fun y hy => hy.differentiableAt (by norm_num)
      exact (hcont.eventually (by simpa using h2))
    have h2 : ∀ᶠ s in 𝓝 (0:ℝ), α s - β 0 ≠ 0 := by
      have : ContinuousAt (fun s => α s - β 0) 0 := hα.continuousAt.sub continuousAt_const
      exact this.eventually_ne hne
    filter_upwards [h1, h2] with s hs1 hs2
    have hl : HasDerivAt (fun t : ℝ => s • e0 + t • e1) e1 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const e1).const_add (s • e0)
    have hA : HasDerivAt (fun t : ℝ => f (s • e0 + t • e1)) (fderiv ℝ f (s • e0) e1) 0 := by
      have := hs1.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
      exact this
    have hB := hasDerivAt_pair_t c (α s) hβ (by simpa using hs2)
    have hfun : (fun t : ℝ => f (s • e0 + t • e1)) = fun t => -c / planeLength (α s - β t) := by
      funext t
      rw [hf]
      simp [he0, he1]
    rw [hfun] at hA
    exact hA.unique hB
  exact H.unique (N.congr_of_eventuallyEq hev)

end SecularForm
end KAM.Planetary
