/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.AffineFlow

/-!
# Affine flow: joint holomorphy in the parameter (P11A-C6)

`stepP:p11a:af-rest` / `bpP:p11a:affine-flow` (f): the augmented field `(b, z) ↦ (0, X_{φ_b}(z))`
on `B × Ω` is holomorphic and small in the gauge `diag(δ₀⁻¹, W)` on a parameter disc of radius
`δ₀ ⊆ B`; by uniqueness its flow is `(b, X_{φ_b}^t z)`, and `Canonical.flow_b` gives joint
holomorphy near every `(b₀, z₀)`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

/-- The augmented field `(b, z) ↦ (0, X_{φ_b}(z))`. -/
def paramField (p0 : P11CVec n × P11CVec n → ℂ) (p1 : P11CVec n × P11CVec n → P11CVec n)
    (w : P11CVec n × P11Phase n) : P11CVec n × P11Phase n :=
  (0, KAM.hamiltonianVectorFieldℂ (p11Affine (fun θ => p0 (θ, w.1)) (fun θ => p1 (θ, w.1))) w.2)

/-- Partial derivative in the angle of a function of `(θ, b)`. -/
theorem fderiv_partial {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {f : P11CVec n × P11CVec n → W} {θ b : P11CVec n} (hf : DifferentiableAt ℂ f (θ, b))
    (a : P11CVec n) :
    fderiv ℂ (fun θ' => f (θ', b)) θ a = fderiv ℂ f (θ, b) (a, 0) := by
  have h := hf.hasFDerivAt.comp θ (hasFDerivAt_id (𝕜 := ℂ) θ |>.prodMk
    (hasFDerivAt_const (𝕜 := ℂ) b θ))
  refine (congrArg (fun L => L a) h.fderiv).trans ?_
  simp

variable {B : Set (P11CVec n)} {p0 : P11CVec n × P11CVec n → ℂ}
  {p1 : P11CVec n × P11CVec n → P11CVec n} {r s sigma A : ℝ}

/-- The augmented field is holomorphic on `B × Ω`. -/
theorem paramField_differentiableOn (hB : IsOpen B)
    (h0 : DifferentiableOn ℂ p0 (KAM.complexStrip n r ×ˢ B))
    (h1 : DifferentiableOn ℂ p1 (KAM.complexStrip n r ×ˢ B))
    (H : ∀ b ∈ B, P11AffineHyp (fun θ => p0 (θ, b)) (fun θ => p1 (θ, b)) r s sigma A) :
    DifferentiableOn ℂ (paramField p0 p1) (B ×ˢ KAM.Weighted.Dom n {0} s (r-sigma)) := by
  have hO : IsOpen (KAM.complexStrip n r ×ˢ B) := (KAM.isOpen_complexStrip n r).prod hB
  have d0 := (KAM.holomorphic_regularity_of_finiteDimensional hO h0).1
  have d1 := (KAM.holomorphic_regularity_of_finiteDimensional hO h1).1
  set S : Set (P11CVec n × P11Phase n) := B ×ˢ KAM.Weighted.Dom n {0} s (r-sigma) with hS
  have hκ : DifferentiableOn ℂ (fun w : P11CVec n × P11Phase n => (w.2.1, w.1)) S :=
    ((differentiable_fst.comp differentiable_snd).prodMk differentiable_fst).differentiableOn
  have hmaps : MapsTo (fun w : P11CVec n × P11Phase n => (w.2.1, w.1)) S
      (KAM.complexStrip n r ×ˢ B) := by
    rintro ⟨b, z⟩ ⟨hb, hz⟩
    rw [mem_Dom_iff] at hz
    exact ⟨(H b hb |> strip_sub_sigma_subset) hz.1, hb⟩
  have D0 := d0.comp hκ hmaps
  have D1 := d1.comp hκ hmaps
  have hc1 : DifferentiableOn ℂ (fun w : P11CVec n × P11Phase n => p1 (w.2.1, w.1)) S :=
    h1.comp hκ hmaps
  have hη : ∀ j : Fin n, DifferentiableOn ℂ (fun w : P11CVec n × P11Phase n => w.2.2 j) S :=
    fun j => (by fun_prop : Differentiable ℂ fun w : P11CVec n × P11Phase n => w.2.2 j).differentiableOn
  have hc2 : ∀ i : Fin n, DifferentiableOn ℂ (fun w : P11CVec n × P11Phase n =>
      -(fderiv ℂ p0 (w.2.1, w.1) (Pi.single i 1, 0) +
        ∑ j, fderiv ℂ p1 (w.2.1, w.1) (Pi.single i 1, 0) j * w.2.2 j)) S := fun i => by
    refine ((D0.clm_apply (differentiableOn_const _)).add
      (DifferentiableOn.fun_sum fun j _ => ?_)).neg
    exact ((differentiableOn_pi.1 (D1.clm_apply (differentiableOn_const _))) j).mul (hη j)
  have hfun : DifferentiableOn ℂ (fun w : P11CVec n × P11Phase n =>
      ((0 : P11CVec n), ((fun i => p1 (w.2.1, w.1) i : P11CVec n), (fun i => -(fderiv ℂ p0 (w.2.1, w.1)
        (Pi.single i 1, 0) + ∑ j, fderiv ℂ p1 (w.2.1, w.1) (Pi.single i 1, 0) j * w.2.2 j) :
          P11CVec n)))) S :=
    (differentiableOn_const _).prodMk (differentiableOn_pi.2 (differentiableOn_pi.1 hc1) |>.prodMk
      (differentiableOn_pi.2 hc2))
  refine hfun.congr ?_
  rintro ⟨b, θ, η⟩ ⟨hb, hz⟩
  have hHb := H b hb
  have hθ : θ ∈ KAM.complexStrip n r := by
    rw [mem_Dom_iff] at hz
    exact strip_sub_sigma_subset hHb hz.1
  have hd0 : DifferentiableAt ℂ p0 (θ, b) := h0.differentiableAt (hO.mem_nhds ⟨hθ, hb⟩)
  have hd1 : DifferentiableAt ℂ p1 (θ, b) := h1.differentiableAt (hO.mem_nhds ⟨hθ, hb⟩)
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact field_fst hHb hθ
  · funext i
    show (KAM.hamiltonianVectorFieldℂ _ (θ, η)).2 i = _
    rw [field_snd hHb hθ, fderiv_partial hd0, fderiv_partial hd1 _]

/-- The gauge `diag(δ₀⁻¹, W)` on the augmented space. -/
def paramGauge (δ0 : ℝ) (hδ : 0 < δ0) (Wg : P11Phase n ≃L[ℂ] P11Phase n) :
    (P11CVec n × P11Phase n) ≃L[ℂ] (P11CVec n × P11Phase n) :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((δ0 : ℂ)⁻¹) (by simpa using hδ.ne'))).prodCongr Wg

theorem norm_paramGauge (δ0 : ℝ) (hδ : 0 < δ0) (Wg : P11Phase n ≃L[ℂ] P11Phase n)
    (w : P11CVec n × P11Phase n) :
    ‖paramGauge δ0 hδ Wg w‖ = max (‖w.1‖/δ0) ‖Wg w.2‖ := by
  simp [paramGauge, Prod.norm_def, norm_smul, abs_of_pos hδ, div_eq_inv_mul]

/-- `af-rest(f)`: joint parameter holomorphy of the time-one map. -/
theorem affine_flow_param {n : ℕ} {B : Set (P11CVec n)} (hB : IsOpen B)
    (p0 : P11CVec n × P11CVec n → ℂ) (p1 : P11CVec n × P11CVec n → P11CVec n)
    {r s sigma A : ℝ}
    (h0 : DifferentiableOn ℂ p0 (KAM.complexStrip n r ×ˢ B))
    (h1 : DifferentiableOn ℂ p1 (KAM.complexStrip n r ×ˢ B))
    (H : ∀ b ∈ B, P11AffineHyp (fun theta => p0 (theta,b)) (fun theta => p1 (theta,b)) r s sigma A) :
    DifferentiableOn ℂ (fun z : P11CVec n × P11Phase n =>
      p11Flow (p11Affine (fun theta => p0 (theta,z.1)) (fun theta => p1 (theta,z.1))) r s sigma 1 z.2)
      (B ×ˢ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) := by
  rintro ⟨b0, z0⟩ ⟨hb0, hz0⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.1 hB b0 hb0
  have H0 := H b0 hb0
  set Wg := affineGauge H0 with hWg
  set W' := paramGauge δ0 hδ0 Wg with hW'
  set Ω : Set (P11Phase n) := KAM.Weighted.Dom n {0} s (r-sigma) with hΩ
  set Ω' : Set (P11CVec n × P11Phase n) := B ×ˢ Ω with hΩ'
  set κ := 2*(n+1)*A/sigma with hκ
  have hsf : KAM.Canonical.SmallField W' Ω' (paramField p0 p1) κ := by
    refine ⟨hB.prod (KAM.Weighted.isOpen_Dom _ _ _), paramField_differentiableOn hB h0 h1 H,
      kappa_nonneg H0, kappa_le_half H0, ?_⟩
    rintro ⟨b, z⟩ ⟨hb, hz⟩
    have := (smallField (H b hb)).bound z hz
    rw [hW', norm_paramGauge]
    simp only [paramField, norm_zero, zero_div]
    exact max_le (by linarith [kappa_nonneg H0]) this
  -- the augmented gauge interior contains a parameter disc times `U`
  have hN : ∀ b ∈ Metric.ball b0 (δ0/2), ∀ z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2),
      (b, z) ∈ KAM.Canonical.gaugeInterior W' Ω' (1/2) := by
    intro b hb z hz w hw
    rw [hW', norm_paramGauge] at hw
    simp only [Prod.fst_sub, Prod.snd_sub, max_le_iff, div_le_iff₀ hδ0] at hw
    refine ⟨hball ?_, (U_sub_half H0 hz) w.2 hw.2⟩
    rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
    calc ‖w.1 - b0‖ = ‖(w.1 - b) + (b - b0)‖ := by congr 1; abel
      _ ≤ ‖w.1 - b‖ + ‖b - b0‖ := norm_add_le _ _
      _ < δ0 := by linarith [hw.1]
  have hkey : ∀ b ∈ Metric.ball b0 (δ0/2), ∀ z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2),
      KAM.Canonical.flow (paramField p0 p1) Ω' 1 (b, z) = (b,
        p11Flow (p11Affine (fun θ => p0 (θ, b)) (fun θ => p1 (θ, b))) r s sigma 1 z) := by
    intro b hb z hz
    have hbB : b ∈ B := hball (Metric.ball_subset_ball (by linarith) hb)
    have Hb := H b hbB
    obtain ⟨h0', hsol, -, -⟩ := KAM.Canonical.flow_a (smallField Hb) (U_sub_half Hb hz)
    have hγ : KAM.ODE.IsSolutionIn (paramField p0 p1) Ω' (Icc (-1) 1)
        (fun t => (b, KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ
          (p11Affine (fun θ => p0 (θ, b)) (fun θ => p1 (θ, b)))) Ω t z)) :=
      fun t ht => ⟨⟨hbB, (hsol t ht).1⟩, (hasDerivAt_const t b).prodMk (hsol t ht).2⟩
    have := (KAM.Canonical.flow_a hsf (hN b hb z hz)).2.2.1 (Icc (-1) 1)
      isPreconnected_Icc.ordConnected (by simp) _ hγ (Prod.ext rfl h0') 1
      ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩
    exact this.symm
  have h1' : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hdiffG := (KAM.Canonical.flow_b hsf).2.1 1 h1'
  have hmem : (b0, z0) ∈ KAM.Canonical.gaugeInterior W' Ω' (1/2) :=
    hN b0 (Metric.mem_ball_self (by linarith)) z0 hz0
  have hG := hdiffG.differentiableAt
    ((KAM.Canonical.isOpen_gaugeInterior hsf.isOpen W' (1/2)).mem_nhds hmem)
  have heq : (fun w : P11CVec n × P11Phase n => (KAM.Canonical.flow (paramField p0 p1) Ω' 1 w).2)
      =ᶠ[nhds (b0, z0)] fun w : P11CVec n × P11Phase n =>
        p11Flow (p11Affine (fun θ => p0 (θ, w.1)) (fun θ => p1 (θ, w.1))) r s sigma 1 w.2 := by
    filter_upwards [((Metric.isOpen_ball (x := b0) (ε := δ0/2)).prod
      (KAM.Weighted.isOpen_Dom (n := n) (m := n) {0} (3*s/4) (r-3*sigma/2))).mem_nhds
      ⟨Metric.mem_ball_self (by linarith), hz0⟩] with w hw
    have := hkey w.1 hw.1 w.2 hw.2
    simp only [Prod.mk.eta] at this
    rw [this]
  exact (differentiableAt_snd.comp (b0, z0) hG).congr_of_eventuallyEq heq.symm

end KAM.Planetary

end
