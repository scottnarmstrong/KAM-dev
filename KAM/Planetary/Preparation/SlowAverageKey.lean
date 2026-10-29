/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageOsc

/-!
# Slow averaging: the polar average of `G` (P11A-P7b, graph step `as-osc`, items (b), (d))

`p11_slow_key`: for `Re ρ̃ > 0`, `𝒜 G = C + Σ Ω_i ρ̃_i / 2π + 𝒜R₄ + 𝒜ḡ`, by linearity
(`polar_average_linear`) and the normalization (`polar_average_normalization`) of the polar
average, and `p11_slow_avg_real`: the polar average of `G` is real at real data.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Key

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem p11_sqrt_ofReal {r : ℝ} (hr : 0 ≤ r) :
    Complex.sqrt (r : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  unfold Complex.sqrt
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]
  push_cast
  rw [one_div]

/-- The polar point of a real, nonnegative radial action and a real angle is real. -/
theorem p11_polarPt_real {ρ : P11Vec n} (hρ : ∀ i, 0 ≤ ρ i) (θ : P11Vec n) :
    p11PolarPt (p11Rad (KAM.realInclusion n ρ)) (fun i => (θ i : ℂ)) =
      KAM.realInclusion₂ n (fun i => Real.sqrt (ρ i / Real.pi) * Real.sin (2 * Real.pi * θ i),
        fun i => Real.sqrt (ρ i / Real.pi) * Real.cos (2 * Real.pi * θ i)) := by
  have hs : ∀ i, Complex.sin (2 * Real.pi * (θ i : ℂ)) = ((Real.sin (2 * Real.pi * θ i) : ℝ) : ℂ) :=
    fun i => by rw [Complex.ofReal_sin]; push_cast; rfl
  have hc : ∀ i, Complex.cos (2 * Real.pi * (θ i : ℂ)) = ((Real.cos (2 * Real.pi * θ i) : ℝ) : ℂ) :=
    fun i => by rw [Complex.ofReal_cos]; push_cast; rfl
  have h' : ∀ i, Complex.sqrt ((ρ i : ℂ) / (Real.pi : ℂ)) = ((Real.sqrt (ρ i / Real.pi) : ℝ) : ℂ) :=
    fun i => by rw [← Complex.ofReal_div]; exact p11_sqrt_ofReal (div_nonneg (hρ i) Real.pi_pos.le)
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [p11PolarPt, p11Rad, KAM.realInclusion_apply, KAM.realInclusion₂_apply, h', hs]
    push_cast; rfl
  · simp only [p11PolarPt, p11Rad, KAM.realInclusion_apply, KAM.realInclusion₂_apply, h', hc]
    push_cast; rfl

/-- The polar average of the fast Hamiltonian is real at real data. -/
theorem p11_slow_avg_real (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {J ρ : P11Vec n} (hJ : ‖J - C.J0‖ < p11s1 C eps / 2)
    (hρ : ∀ i, 0 < ρ i) (hρn : ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2) :
    (p11PolarAverage Fast.G (KAM.realInclusion n J, KAM.realInclusion n ρ)).im = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  have hr : 0 < C.rz / 2 := by positivity
  obtain ⟨-, -, -, -, hGd, hGr, -⟩ := hF
  have hJ' : KAM.realInclusion n J ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) := by
    rw [KAM.realInclusion_mem_ball_iff]; exact mem_ball_iff_norm.2 hJ
  have hw : ‖p11Rad (KAM.realInclusion n ρ)‖ < C.rz / 2 :=
    p11_rad_norm_lt hr (by rwa [KAM.norm_realInclusion])
  have hc := p11_continuous_polar_integrand hGd hJ' hw
  have hint : IntegrableOn (fun θ : P11Vec n => Fast.G (KAM.realInclusion n J,
      p11PolarPt (p11Rad (KAM.realInclusion n ρ)) (fun i => (θ i : ℂ))))
      (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    KAM.integrableOn_unitCube_of_continuous hc
  have hdef : p11PolarAverage Fast.G (KAM.realInclusion n J, KAM.realInclusion n ρ) =
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), Fast.G (KAM.realInclusion n J,
        p11PolarPt (p11Rad (KAM.realInclusion n ρ)) (fun i => (x i : ℂ))) := rfl
  have := integral_im (μ := volume.restrict (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)))
    hint
  simp only [RCLike.im_to_complex] at this
  rw [hdef, ← this]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun θ => ?_)
  show (Fast.G (KAM.realInclusion n J, _)).im = 0
  rw [p11_polarPt_real (fun i => (hρ i).le)]
  refine hGr J hJ _ ?_
  rw [← KAM.norm_realInclusion₂, ← p11_polarPt_real (fun i => (hρ i).le)]
  exact mem_ball_zero_iff.1 (p11_polarPt_mem_ball hw θ)

theorem p11PolarAverage_add_of {D : Set (P11CVec n)} (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {G H : P11CVec n × P11Phase n → ℂ} (hG : DifferentiableOn ℂ G (D ×ˢ ball 0 r))
    (hH : DifferentiableOn ℂ H (D ×ˢ ball 0 r)) {z : P11CVec n × P11CVec n}
    (hz : z ∈ D ×ˢ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4)) (hre : ∀ i, 0 < (z.2 i).re) :
    p11PolarAverage (G + H) z = p11PolarAverage G z + p11PolarAverage H z := by
  have := polar_average_linear hD hr hG hH 1 1 z hz hre
  simpa using this

theorem p11PolarAverage_const_mul (c : P11CVec n → ℂ) (g : P11CVec n × P11Phase n → ℂ)
    (z : P11CVec n × P11CVec n) :
    p11PolarAverage (fun y => c y.1 * g y) z = c z.1 * p11PolarAverage g z := by
  unfold p11PolarAverage KAM.torusAverage
  exact integral_const_mul (c z.1) _

/-- Polar average of the quadratic secular part `Σ Ω_i (x_i² + y_i²)/2`. -/
theorem p11PolarAverage_sec {D : Set (P11CVec n)} (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {Om : P11CVec n → P11CVec n} (hOm : DifferentiableOn ℂ Om D) :
    DifferentiableOn ℂ (fun y : P11CVec n × P11Phase n =>
        ∑ i, Om y.1 i * ((y.2.1 i ^ 2 + y.2.2 i ^ 2) / 2)) (D ×ˢ ball 0 r) ∧
      ∀ z ∈ D ×ˢ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
        p11PolarAverage (fun y : P11CVec n × P11Phase n =>
          ∑ i, Om y.1 i * ((y.2.1 i ^ 2 + y.2.2 i ^ 2) / 2)) z =
        ∑ i, Om z.1 i / (2 * Real.pi) * z.2 i := by
  set T : Fin n → P11CVec n × P11Phase n → ℂ :=
    fun i y => Om y.1 i * ((y.2.1 i ^ 2 + y.2.2 i ^ 2) / 2) with hT
  have hTd : ∀ i, DifferentiableOn ℂ (T i) (D ×ˢ ball 0 r) := by
    intro i
    have h1 : DifferentiableOn ℂ (fun y : P11CVec n × P11Phase n => Om y.1 i)
        (D ×ˢ ball 0 r) :=
      (differentiableOn_pi.1 hOm i).comp (f := fun y : P11CVec n × P11Phase n => y.1)
        (by fun_prop) fun y hy => hy.1
    have h2 : DifferentiableOn ℂ (fun y : P11CVec n × P11Phase n =>
        (y.2.1 i ^ 2 + y.2.2 i ^ 2) / 2) (D ×ˢ ball 0 r) := by
      apply Differentiable.differentiableOn
      fun_prop
    exact h1.mul h2
  have hTa : ∀ i, ∀ z : P11CVec n × P11CVec n,
      p11PolarAverage (T i) z = Om z.1 i * (z.2 i / (2 * Real.pi)) := by
    intro i z
    rw [← (polar_average_normalization (fun _ => (0 : ℂ)) z).2 i]
    exact p11PolarAverage_const_mul (fun J => Om J i) _ z
  have key : ∀ s : Finset (Fin n),
      DifferentiableOn ℂ (fun y => ∑ i ∈ s, T i y) (D ×ˢ ball 0 r) ∧
      ∀ z ∈ D ×ˢ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
        p11PolarAverage (fun y => ∑ i ∈ s, T i y) z =
          ∑ i ∈ s, Om z.1 i / (2 * Real.pi) * z.2 i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simp, fun z _ _ => ?_⟩
      simpa using (polar_average_normalization (fun _ => (0 : ℂ)) z).1
    | insert a s ha ih =>
      have hfun : (fun y => ∑ i ∈ insert a s, T i y) = T a + fun y => ∑ i ∈ s, T i y := by
        funext y; simp [Finset.sum_insert ha]
      rw [hfun]
      refine ⟨(hTd a).add ih.1, fun z hz hre => ?_⟩
      rw [p11PolarAverage_add_of hD hr (hTd a) ih.1 hz hre, hTa, ih.2 z hz hre,
        Finset.sum_insert ha]
      ring
  exact key Finset.univ

/-- `𝒜 G = C + Σ Ω_i ρ̃_i/2π + 𝒜R₄ + 𝒜ḡ` for `Re ρ̃ > 0` (`polar_average_linear` and
`polar_average_normalization`; graph step `as-osc`, uses (b), (d) of `polar_avg`). -/
theorem p11_slow_key (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    {AR AB : P11CVec n × P11CVec n → ℂ}
    (hARe : ∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
      AR z = p11PolarAverage (p11R4 C) z)
    (hABe : ∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
      AB z = p11PolarAverage (p11Gbar C Fast) z)
    {z : P11CVec n × P11CVec n}
    (hz : z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4)) (hre : ∀ i, 0 < (z.2 i).re) :
    C.C z.1 + ∑ i, C.Omega z.1 i / (2 * Real.pi) * z.2 i + (AR z + AB z) =
      p11PolarAverage Fast.G z := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hr : 0 < C.rz / 2 := by positivity
  set Dm : Set (P11CVec n) := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) with hDm
  have hsub : Dm ⊆ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    ball_subset_ball (by linarith [p11s1_le C eps, p11s1_pos hC heps hεM])
  have hsubz : ball (0 : P11Phase n) (C.rz / 2) ⊆ ball (0 : P11Phase n) C.rz :=
    ball_subset_ball (by linarith)
  obtain ⟨hGbd, -⟩ := p11_gbar_data hC Fast hF heps hεM
  have hR4d : DifferentiableOn ℂ (p11R4 C) (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) :=
    (p11R4_differentiableOn hC).mono (prod_mono hsub hsubz)
  obtain ⟨hOm, -⟩ := secular_extract hC
  have hCd : DifferentiableOn ℂ (fun y : P11CVec n × P11Phase n => C.C y.1)
      (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) :=
    (p11C_differentiableOn hC).comp (f := fun y : P11CVec n × P11Phase n => y.1) (by fun_prop)
      fun y hy => hsub hy.1
  obtain ⟨hSd, hSa⟩ := p11PolarAverage_sec (D := Dm) isOpen_ball hr (hOm.mono hsub)
  have hfun : Fast.G = (fun y : P11CVec n × P11Phase n => C.C y.1) +
      (fun y : P11CVec n × P11Phase n => ∑ i, C.Omega y.1 i * ((y.2.1 i ^ 2 + y.2.2 i ^ 2) / 2)) +
      p11R4 C + p11Gbar C Fast := by
    funext p
    simp only [Pi.add_apply]
    exact p11G_decomp C Fast p
  rw [hfun]
  rw [p11PolarAverage_add_of isOpen_ball hr ((hCd.add hSd).add hR4d) hGbd hz hre,
    p11PolarAverage_add_of isOpen_ball hr (hCd.add hSd) hR4d hz hre,
    p11PolarAverage_add_of isOpen_ball hr hCd hSd hz hre,
    (polar_average_normalization (fun J => C.C J) z).1, hSa z hz hre, ← hARe z hz hre,
    ← hABe z hz hre]
  ring

end Key

end KAM.Planetary

end
