/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.FlowInverse
public import KAM.Canonical.Symplectic
public import KAM.Head.HamiltonianField
public import KAM.Planetary.MaximalStep.Basic
public import KAM.Planetary.MaximalStep.Affine

/-!
# Affine generating functions: data and field estimates (P11A-C6)

The affine-in-action generating function `p11Affine`, its flow `p11Flow` (the existing
`Canonical.flow` for the frozen Hamiltonian field on `Dom n {0} s (r-σ)`), the scaled-gauge bound
`p11GaugeBound` and the hypotheses `P11AffineHyp` of `bpP:p11a:affine-flow`. This file proves the
field part `stepP:p11a:af-field`: the explicit components of the Hamiltonian field and the
`SmallField` hypothesis in the gauge `scaleCLE (s/2) σ`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

def p11Flow {n : ℕ} (phi : P11Phase n → ℂ) (r s sigma : ℝ) (t : ℝ) :=
  KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ phi)
    (KAM.Weighted.Dom n {0} s (r-sigma)) t

def p11GaugeBound {n : ℕ} (rho sigma : ℝ) (L : P11Phase n →L[ℂ] P11Phase n) (M : ℝ) : Prop :=
  ∀ z, KAM.Canonical.scaledNorm rho sigma (L z) ≤ M*KAM.Canonical.scaledNorm rho sigma z

structure P11AffineHyp {n : ℕ} (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n)
    (r s sigma A : ℝ) : Prop where
  n_pos : 1 ≤ n
  sigma_pos : 0 < sigma
  radius : 2*sigma < r
  s_pos : 0 < s
  A_nonneg : 0 ≤ A
  small : 4*(n+1)*A ≤ sigma
  hol0 : DifferentiableOn ℂ p0 (KAM.complexStrip n r)
  hol1 : DifferentiableOn ℂ p1 (KAM.complexStrip n r)
  per0 : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n r, p0 (x+Pi.single j 1)=p0 x
  per1 : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n r, p1 (x+Pi.single j 1)=p1 x
  bound0 : p11Bound (KAM.complexStrip n r) p0 (s*A)
  bound1 : p11Bound (KAM.complexStrip n r) p1 A

variable {n : ℕ} {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {r s sigma A : ℝ}

/-- The Fréchet derivative of `p11Affine` at a point where `p0, p1` are differentiable. -/
theorem fderiv_p11Affine_apply (z : P11Phase n) (h0 : DifferentiableAt ℂ p0 z.1)
    (h1 : DifferentiableAt ℂ p1 z.1) (a b : P11CVec n) :
    fderiv ℂ (p11Affine p0 p1) z (a, b) =
      fderiv ℂ p0 z.1 a + ∑ j, fderiv ℂ p1 z.1 a j * z.2 j + ∑ j, p1 z.1 j * b j := by
  have hp0 : HasFDerivAt (fun w : P11Phase n => p0 w.1) ((fderiv ℂ p0 z.1).comp
      (ContinuousLinearMap.fst ℂ _ _)) z :=
    h0.hasFDerivAt.comp z hasFDerivAt_fst
  have hp1 : ∀ j : Fin n, HasFDerivAt (fun w : P11Phase n => p1 w.1 j)
      (((ContinuousLinearMap.proj j : P11CVec n →L[ℂ] ℂ).comp (fderiv ℂ p1 z.1)).comp
        (ContinuousLinearMap.fst ℂ _ _)) z := fun j =>
    (((ContinuousLinearMap.proj j : P11CVec n →L[ℂ] ℂ).hasFDerivAt (x := p1 z.1)).comp z.1
      h1.hasFDerivAt).comp z hasFDerivAt_fst
  have hq : ∀ j : Fin n, HasFDerivAt (fun w : P11Phase n => w.2 j)
      ((ContinuousLinearMap.proj j : P11CVec n →L[ℂ] ℂ).comp (ContinuousLinearMap.snd ℂ _ _)) z :=
    fun j => ((ContinuousLinearMap.proj j : P11CVec n →L[ℂ] ℂ).hasFDerivAt (x := z.2)).comp z
      hasFDerivAt_snd
  have hsum := HasFDerivAt.sum (u := Finset.univ) (A := fun j (w : P11Phase n) => p1 w.1 j * w.2 j)
    (fun j _ => (hp1 j).mul (hq j))
  have hall := hp0.add hsum
  have := hall.fderiv
  have hfun : (p11Affine p0 p1) = (fun w : P11Phase n => p0 w.1) +
      ∑ j, fun w : P11Phase n => p1 w.1 j * w.2 j := by
    funext w
    simp [p11Affine, Finset.sum_apply]
  rw [hfun, this]
  simp [Finset.sum_add_distrib, mul_comm, add_assoc]
  ring

theorem mem_Dom_iff {a b : ℝ} (z : P11Phase n) :
    z ∈ KAM.Weighted.Dom n {0} a b ↔ z.1 ∈ KAM.complexStrip n b ∧ ‖z.2‖ < a := by
  simp [KAM.Weighted.Dom, KAM.Weighted.polyNbhd, mem_prod]

theorem differentiableOn_p11Affine (H : P11AffineHyp p0 p1 r s sigma A) :
    DifferentiableOn ℂ (p11Affine p0 p1) (KAM.complexStrip n r ×ˢ univ) := by
  have hmaps : MapsTo (fun w : P11Phase n => w.1) (KAM.complexStrip n r ×ˢ univ)
      (KAM.complexStrip n r) := fun w hw => hw.1
  have h0 : DifferentiableOn ℂ (fun w : P11Phase n => p0 w.1) (KAM.complexStrip n r ×ˢ univ) :=
    H.hol0.comp differentiableOn_fst hmaps
  have h1 : ∀ j : Fin n, DifferentiableOn ℂ (fun w : P11Phase n => p1 w.1 j)
      (KAM.complexStrip n r ×ˢ univ) := fun j =>
    ((differentiableOn_pi.1 H.hol1) j).comp differentiableOn_fst hmaps
  refine h0.add (DifferentiableOn.fun_sum fun j _ => (h1 j).mul ?_)
  exact ((differentiable_apply j).comp_differentiableOn differentiableOn_snd).congr
    (fun _ _ => rfl)

theorem field_fst (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z.1 ∈ KAM.complexStrip n r) :
    (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) z).1 = p1 z.1 := by
  have h0 := H.hol0.differentiableAt ((KAM.isOpen_complexStrip n r).mem_nhds hz)
  have h1 := H.hol1.differentiableAt ((KAM.isOpen_complexStrip n r).mem_nhds hz)
  funext i
  simp [KAM.hamiltonianVectorFieldℂ, fderiv_p11Affine_apply z h0 h1 0 (Pi.single i 1),
    Pi.single_apply]

theorem field_snd (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z.1 ∈ KAM.complexStrip n r) (i : Fin n) :
    (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) z).2 i =
      -(fderiv ℂ p0 z.1 (Pi.single i 1) +
        ∑ j, fderiv ℂ p1 z.1 (Pi.single i 1) j * z.2 j) := by
  have h0 := H.hol0.differentiableAt ((KAM.isOpen_complexStrip n r).mem_nhds hz)
  have h1 := H.hol1.differentiableAt ((KAM.isOpen_complexStrip n r).mem_nhds hz)
  simp [KAM.hamiltonianVectorFieldℂ, fderiv_p11Affine_apply z h0 h1 (Pi.single i 1) 0]

/-- `stepP:p11a:af-field`: componentwise bounds of the field on `Dom n {0} s (r-σ)`. -/
theorem field_bound (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} s (r-sigma)) :
    ‖(KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) z).1‖ ≤ A ∧
    ‖(KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) z).2‖ ≤ (n+1)*s*A/sigma := by
  rw [mem_Dom_iff] at hz
  have hsub : KAM.complexStrip n (r-sigma) ⊆ KAM.complexStrip n r := fun θ hθ i =>
    (hθ i).trans (by linarith [H.sigma_pos])
  have hθ := hsub hz.1
  have c0 := (KAM.cauchy_strip H.hol0 H.bound0 H.sigma_pos).1
  have c1 := (KAM.cauchy_strip H.hol1 H.bound1 H.sigma_pos).1
  refine ⟨?_, ?_⟩
  · rw [field_fst H hθ]
    exact H.bound1 _ hθ
  · have hnn : 0 ≤ (n+1)*s*A/sigma := by
      have := H.s_pos; have := H.sigma_pos; have := H.A_nonneg; positivity
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
    rw [field_snd H hθ i, norm_neg]
    have hA0 := H.A_nonneg
    have hs0 := H.s_pos
    have hσ0 := H.sigma_pos
    have hz2 : ∀ j, ‖z.2 j‖ ≤ s := fun j => ((norm_le_pi_norm z.2 j).trans hz.2.le)
    have e0 := c0 i _ hz.1
    have e1 : ∀ j, ‖fderiv ℂ p1 z.1 (Pi.single i 1) j‖ ≤ sigma⁻¹ * A := fun j =>
      (norm_le_pi_norm _ j).trans (c1 i _ hz.1)
    have hsum : ‖∑ j, fderiv ℂ p1 z.1 (Pi.single i 1) j * z.2 j‖ ≤ n * (sigma⁻¹ * A * s) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖fderiv ℂ p1 z.1 (Pi.single i 1) j * z.2 j‖
          ≤ ∑ _j : Fin n, sigma⁻¹ * A * s := Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (e1 j) (hz2 j) (norm_nonneg _) (by positivity)
        _ = n * (sigma⁻¹ * A * s) := by simp
    calc ‖fderiv ℂ p0 z.1 (Pi.single i 1) + ∑ j, fderiv ℂ p1 z.1 (Pi.single i 1) j * z.2 j‖
        ≤ ‖fderiv ℂ p0 z.1 (Pi.single i 1)‖ +
            ‖∑ j, fderiv ℂ p1 z.1 (Pi.single i 1) j * z.2 j‖ := norm_add_le _ _
      _ ≤ sigma⁻¹ * (s * A) + n * (sigma⁻¹ * A * s) := add_le_add e0 hsum
      _ = (n+1)*s*A/sigma := by field_simp; ring

/-- The gauge `diag(σ⁻¹, (s/2)⁻¹)` for the scale of the affine flow. -/
def affineGauge (H : P11AffineHyp p0 p1 r s sigma A) : P11Phase n ≃L[ℂ] P11Phase n :=
  KAM.Canonical.scaleCLE (s/2) sigma (by linarith [H.s_pos]) H.sigma_pos

/-- `kappa = 2(n+1)A/σ`. -/
theorem kappa_le_half (H : P11AffineHyp p0 p1 r s sigma A) : 2*(n+1)*A/sigma ≤ 1/2 := by
  have := H.sigma_pos
  rw [div_le_iff₀ this]
  linarith [H.small]

theorem kappa_nonneg (H : P11AffineHyp p0 p1 r s sigma A) : 0 ≤ 2*(n+1)*A/sigma := by
  have := H.sigma_pos; have := H.A_nonneg; positivity

/-- `bpN:p5:flow` standing hypotheses for the affine field. -/
theorem smallField (H : P11AffineHyp p0 p1 r s sigma A) :
    KAM.Canonical.SmallField (affineGauge H) (KAM.Weighted.Dom n {0} s (r-sigma))
      (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1)) (2*(n+1)*A/sigma) := by
  refine ⟨KAM.Weighted.isOpen_Dom _ _ _, ?_, kappa_nonneg H, kappa_le_half H, ?_⟩
  · refine KAM.Head.differentiableOn_hamiltonianVectorField (KAM.Weighted.isOpen_Dom _ _ _)
      ((differentiableOn_p11Affine H).mono ?_)
    intro z hz
    rw [mem_Dom_iff] at hz
    exact ⟨fun i => (hz.1 i).trans (by linarith [H.sigma_pos]), trivial⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := field_bound H hz
    unfold affineGauge
    rw [KAM.Canonical.norm_scaleCLE, KAM.Canonical.scaledNorm]
    have hσ := H.sigma_pos
    have hs := H.s_pos
    have hA := H.A_nonneg
    refine max_le ?_ ?_
    · rw [div_le_div_iff_of_pos_right hσ]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast H.n_pos
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      calc ‖(KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) z).2‖ ≤ (n+1)*s*A/sigma := h2
        _ = 2*(n+1)*A/sigma * (s/2) := by ring

end KAM.Planetary

end
