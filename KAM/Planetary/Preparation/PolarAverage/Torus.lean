/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Averages
public import KAM.Planetary.MaximalStep.Basic
public import KAM.Planetary.Preparation.PolarAverage.ParamIntegral

/-!
# The radial-variable polar average (P11A-P6 helper)

`p11PolarW G (J, w)` is the torus average of `G (J, (w_i sin 2πθ_i, w_i cos 2πθ_i))` in the radial
variable `w = √(ρ/π)`. For `G` holomorphic on `D × B(0, r)` it is holomorphic in `(J, w)` on
`D × B(0, r)` (parameter integral over the real torus, via `p11_differentiableOn_paramIntegral`),
and it is even in each `w_j`: the shift `θ_j ↦ θ_j + 1/2` flips the sign of both `w_j sin` and
`w_j cos`, and the torus average is invariant under shifts of a periodic coordinate.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric Filter
open scoped Topology Real

namespace KAM.Planetary

/-- The polar point `(w_i sin 2πϑ_i, w_i cos 2πϑ_i)`. -/
def p11PolarPt {n : ℕ} (w ϑ : P11CVec n) : P11Phase n :=
  ((fun i => w i * Complex.sin (2 * Real.pi * ϑ i)),
    fun i => w i * Complex.cos (2 * Real.pi * ϑ i))

/-- The torus average of `G` along polar points of radial variable `w`. -/
def p11PolarW {n : ℕ} (G : P11CVec n × P11Phase n → ℂ) (q : P11CVec n × P11CVec n) : ℂ :=
  KAM.torusAverage (fun θ : P11Vec n => G (q.1, p11PolarPt q.2 (fun i => (θ i : ℂ))))

theorem p11_norm_sin_le (x : ℝ) : ‖Complex.sin (2 * Real.pi * (x : ℂ))‖ ≤ 1 := by
  have : (2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

theorem p11_norm_cos_le (x : ℝ) : ‖Complex.cos (2 * Real.pi * (x : ℂ))‖ ≤ 1 := by
  have : (2 : ℂ) * (Real.pi : ℂ) * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

theorem p11_norm_polarPt_le {n : ℕ} (w : P11CVec n) (θ : P11Vec n) :
    ‖p11PolarPt w (fun i => (θ i : ℂ))‖ ≤ ‖w‖ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_
    rw [p11PolarPt, norm_mul]
    calc ‖w i‖ * ‖Complex.sin (2 * Real.pi * (θ i : ℂ))‖ ≤ ‖w i‖ * 1 := by
          gcongr; exact p11_norm_sin_le _
      _ ≤ ‖w‖ := by rw [mul_one]; exact norm_le_pi_norm w i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_
    rw [p11PolarPt, norm_mul]
    calc ‖w i‖ * ‖Complex.cos (2 * Real.pi * (θ i : ℂ))‖ ≤ ‖w i‖ * 1 := by
          gcongr; exact p11_norm_cos_le _
      _ ≤ ‖w‖ := by rw [mul_one]; exact norm_le_pi_norm w i

theorem p11_polarPt_mem_ball {n : ℕ} {r : ℝ} {w : P11CVec n} (hw : ‖w‖ < r) (θ : P11Vec n) :
    p11PolarPt w (fun i => (θ i : ℂ)) ∈ ball (0 : P11Phase n) r := by
  rw [mem_ball_zero_iff]
  exact (p11_norm_polarPt_le w θ).trans_lt hw

theorem p11_continuous_polarPt {n : ℕ} (w : P11CVec n) :
    Continuous fun θ : P11Vec n => p11PolarPt w (fun i => (θ i : ℂ)) := by
  unfold p11PolarPt
  fun_prop

theorem p11_continuous_polar_integrand {n : ℕ} {D : Set (P11CVec n)} {r : ℝ}
    {G : P11CVec n × P11Phase n → ℂ} (hG : DifferentiableOn ℂ G (D ×ˢ ball 0 r))
    {J : P11CVec n} (hJ : J ∈ D) {w : P11CVec n} (hw : ‖w‖ < r) :
    Continuous fun θ : P11Vec n => G (J, p11PolarPt w (fun i => (θ i : ℂ))) := by
  refine hG.continuousOn.comp_continuous (by have := p11_continuous_polarPt w; fun_prop) ?_
  intro θ
  exact ⟨hJ, p11_polarPt_mem_ball hw θ⟩

/-- `p11PolarW` is holomorphic in `(J, w)` on `D × B(0, r)`. -/
theorem p11PolarW_differentiableOn {n : ℕ} {D : Set (P11CVec n)} (hD : IsOpen D) {r : ℝ}
    {G : P11CVec n × P11Phase n → ℂ} (hG : DifferentiableOn ℂ G (D ×ˢ ball 0 r)) :
    DifferentiableOn ℂ (p11PolarW G) (D ×ˢ ball (0 : P11CVec n) r) := by
  let Φ : (P11CVec n × P11CVec n) × P11CVec n → P11CVec n × P11Phase n :=
    fun x => (x.1.1, p11PolarPt x.1.2 x.2)
  have hΦ : Differentiable ℂ Φ := by
    unfold Φ p11PolarPt
    fun_prop
  let W : Set ((P11CVec n × P11CVec n) × P11CVec n) := Φ ⁻¹' (D ×ˢ ball 0 r)
  have hWo : IsOpen W := (hD.prod isOpen_ball).preimage hΦ.continuous
  have hf : DifferentiableOn ℂ (fun x => G (Φ x)) W :=
    hG.comp hΦ.differentiableOn (fun x hx => hx)
  have hmem : ∀ q ∈ D ×ˢ ball (0 : P11CVec n) r, ∀ θ ∈ Set.pi Set.univ
      (fun _ : Fin n => Icc (0 : ℝ) 1), (q, fun i => (θ i : ℂ)) ∈ W := by
    intro q hq θ _
    exact ⟨hq.1, p11_polarPt_mem_ball (mem_ball_zero_iff.mp hq.2) θ⟩
  exact p11_differentiableOn_paramIntegral (μ := volume)
    (K := Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) (by
      rw [pi_univ_Icc]; exact isCompact_Icc) (γ := fun θ : P11Vec n => fun i => (θ i : ℂ))
    (by fun_prop) (hD.prod isOpen_ball) hWo hf hmem

theorem p11_insertNth_add {n : ℕ} (j : Fin (n + 1)) (t c : ℝ) (y : Fin n → ℝ) :
    j.insertNth (α := fun _ => ℝ) (t + c) y = j.insertNth (α := fun _ => ℝ) t y + c • Pi.single j 1 := by
  ext k
  refine j.succAboveCases ?_ (fun k' => ?_) k
  · simp
  · simp [Fin.succAbove_ne]

/-- The torus average as an iterated integral over the `j`-th coordinate and the others. -/
theorem p11_torusAverage_eq_iterated {n : ℕ} (j : Fin (n + 1)) {g : (Fin (n + 1) → ℝ) → ℂ}
    (hg : Continuous g) :
    KAM.torusAverage g = ∫ y, ∫ t, g (j.insertNth (α := fun _ => ℝ) t y)
      ∂(volume.restrict (Icc (0 : ℝ) 1)) ∂Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  have hgi : Integrable g (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
    rw [← Measure.restrict_pi_pi]
    apply hg.continuousOn.integrableOn_compact
    rw [pi_univ_Icc]
    exact isCompact_Icc
  have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j).symm
  have hcomp := (hpres.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hgi
  dsimp only [Function.comp_def] at hcomp
  change (∫ x, g x ∂volume.restrict (Set.pi Set.univ (fun _ => Icc 0 1))) = _
  change (∫ x, g x ∂(Measure.pi (fun _ => volume)).restrict
    (Set.pi Set.univ (fun _ => Icc 0 1))) = _
  rw [Measure.restrict_pi_pi, ← hpres.integral_comp' g, integral_prod_symm _ hcomp]
  rfl

/-- The torus average is invariant under real shifts of a periodic coordinate. -/
theorem p11_torusAverage_shift {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : Continuous f) (j : Fin n)
    (hp : ∀ x, f (x + Pi.single j 1) = f x) (c : ℝ) :
    KAM.torusAverage (fun x => f (x + c • Pi.single j 1)) = KAM.torusAverage f := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    have hf' : Continuous fun x : Fin (n + 1) → ℝ => f (x + c • Pi.single j 1) := by fun_prop
    rw [p11_torusAverage_eq_iterated j hf', p11_torusAverage_eq_iterated j hf]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    set g1 : ℝ → ℂ := fun t => f (j.insertNth (α := fun _ => ℝ) t y) with hg1
    have hper : Function.Periodic g1 1 := fun t => by
      simp only [hg1]
      rw [p11_insertNth_add]
      simpa using hp _
    have e1 : ∀ φ : ℝ → ℂ, (∫ t, φ t ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        ∫ t in (0 : ℝ)..1, φ t := fun φ => by
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    have e2 : ∀ t, f (j.insertNth (α := fun _ => ℝ) t y + c • Pi.single j 1) = g1 (t + c) := by
      intro t
      simp only [hg1]
      rw [p11_insertNth_add]
    simp only [e2]
    rw [e1, e1, intervalIntegral.integral_comp_add_right g1 c, zero_add]
    have := hper.intervalIntegral_add_eq c 0
    simpa [add_comm] using this

theorem p11PolarPt_update_neg {n : ℕ} (w : P11CVec n) (θ : P11Vec n) (j : Fin n) :
    p11PolarPt (Function.update w j (-(w j))) (fun i => (θ i : ℂ)) =
      p11PolarPt w (fun i => (((θ + (1 / 2 : ℝ) • Pi.single j 1 : P11Vec n) i : ℝ) : ℂ)) := by
  have hs : Complex.sin (2 * Real.pi * ((θ j + 1 / 2 : ℝ) : ℂ)) =
      -Complex.sin (2 * Real.pi * (θ j : ℂ)) := by
    have : (2 : ℂ) * (Real.pi : ℂ) * ((θ j + 1 / 2 : ℝ) : ℂ) =
        2 * Real.pi * (θ j : ℂ) + Real.pi := by push_cast; ring
    rw [this, Complex.sin_add_pi]
  have hc : Complex.cos (2 * Real.pi * ((θ j + 1 / 2 : ℝ) : ℂ)) =
      -Complex.cos (2 * Real.pi * (θ j : ℂ)) := by
    have : (2 : ℂ) * (Real.pi : ℂ) * ((θ j + 1 / 2 : ℝ) : ℂ) =
        2 * Real.pi * (θ j : ℂ) + Real.pi := by push_cast; ring
    rw [this, Complex.cos_add_pi]
  have hji : ((θ + (1 / 2 : ℝ) • Pi.single j 1 : P11Vec n) j) = θ j + 1 / 2 := by simp
  have hne : ∀ i, i ≠ j → ((θ + (1 / 2 : ℝ) • Pi.single j 1 : P11Vec n) i) = θ i := by
    intro i hij; simp [hij]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · by_cases hij : i = j
    · subst hij
      simp only [p11PolarPt, Function.update_self, hji, hs]
      ring
    · simp only [p11PolarPt, Function.update_of_ne hij, hne i hij]
  · by_cases hij : i = j
    · subst hij
      simp only [p11PolarPt, Function.update_self, hji, hc]
      ring
    · simp only [p11PolarPt, Function.update_of_ne hij, hne i hij]

/-- `p11PolarW` is even in each radial coordinate. -/
theorem p11PolarW_even {n : ℕ} {D : Set (P11CVec n)} {r : ℝ} {G : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ ball 0 r)) {J : P11CVec n} (hJ : J ∈ D)
    {w : P11CVec n} (hw : ‖w‖ < r) (j : Fin n) :
    p11PolarW G (J, Function.update w j (-(w j))) = p11PolarW G (J, w) := by
  set f : P11Vec n → ℂ := fun θ => G (J, p11PolarPt w (fun i => (θ i : ℂ))) with hfdef
  have hfc : Continuous f := p11_continuous_polar_integrand hG hJ hw
  have hper : ∀ x, f (x + Pi.single j 1) = f x := by
    intro x
    simp only [hfdef]
    congr 2
    have hji : ((x + Pi.single j 1 : P11Vec n) j) = x j + 1 := by simp
    have hne : ∀ i, i ≠ j → ((x + Pi.single j 1 : P11Vec n) i) = x i := by
      intro i hij; simp [hij]
    have hcast : (2 : ℂ) * (Real.pi : ℂ) * ((x j + 1 : ℝ) : ℂ) =
        2 * Real.pi * (x j : ℂ) + 2 * Real.pi := by push_cast; ring
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · by_cases hij : i = j
      · subst hij
        simp only [p11PolarPt, hji, hcast, Complex.sin_add_two_pi]
      · simp only [p11PolarPt, hne i hij]
    · by_cases hij : i = j
      · subst hij
        simp only [p11PolarPt, hji, hcast, Complex.cos_add_two_pi]
      · simp only [p11PolarPt, hne i hij]
  have hsh := p11_torusAverage_shift hfc j hper (1 / 2)
  unfold p11PolarW
  simp only
  rw [← hsh]
  congr 1
  funext θ
  simp only [hfdef, p11PolarPt_update_neg]

end KAM.Planetary
