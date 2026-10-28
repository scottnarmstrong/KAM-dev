/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepHom
public import KAM.Canonical.Lie

/-!
# Analytic tools for the bracket estimate (P11A-C8, `stepP:p11a:cs-bracket`)

The displacement of the affine flow at every time `t ∈ [-1, 1]`, the one-variable Cauchy estimate
along a coordinate direction, and the resulting bound of `Du(x)(a, c)` on the phase space.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

section Displacement

variable {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {r s sigma A : ℝ}

/-- Displacement of the flow at every time `t ∈ [-1, 1]`
(`flow_displacement` is the case `t = 1`). -/
theorem flow_displacement_t (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖(p11Flow (p11Affine p0 p1) r s sigma t z).1 - z.1‖ ≤ A ∧
    ‖(p11Flow (p11Affine p0 p1) r s sigma t z).2 - z.2‖ ≤ (n+1)*s*A/sigma := by
  obtain ⟨h0, hsol, -, -⟩ := KAM.Canonical.flow_a (smallField H) (U_sub_half H hz)
  have hI : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt
      (fun t => KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z)
      (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z)) t :=
    fun t ht => (hsol t ht).2
  have h1 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have habs : ‖t - 0‖ ≤ 1 := by simpa using abs_le.2 ⟨ht.1, ht.2⟩
  have hA := H.A_nonneg
  have hC : 0 ≤ (n+1)*s*A/sigma := by
    have := H.s_pos; have := H.sigma_pos; positivity
  constructor
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Icc (-1 : ℝ) 1)
      (f := fun t => (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).1)
      (f' := fun t => (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z)).1)
      (C := A)
      (fun t ht => by
        have := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt t (hI t ht)
        simpa [Function.comp_def] using this.hasDerivWithinAt)
      (fun t ht => (field_bound H (hsol t ht).1).1) (convex_Icc _ _) h1 ht
    simp only [h0] at this
    exact this.trans (by nlinarith)
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Icc (-1 : ℝ) 1)
      (f := fun t => (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).2)
      (f' := fun t => (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z)).2)
      (C := (n+1)*s*A/sigma)
      (fun t ht => by
        have := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt t (hI t ht)
        simpa [Function.comp_def] using this.hasDerivWithinAt)
      (fun t ht => (field_bound H (hsol t ht).1).2) (convex_Icc _ _) h1 ht
    simp only [h0] at this
    exact this.trans (by nlinarith)

end Displacement

/-- One-variable Cauchy estimate along a direction `e`. -/
theorem norm_fderiv_dir_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {O : Set E}
    {u : E → ℂ} (hO : IsOpen O) (hu : DifferentiableOn ℂ u O) {x e : E} {ρ U : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → x + ζ • e ∈ O) (hb : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖u (x + ζ • e)‖ ≤ U) :
    ‖fderiv ℂ u x e‖ ≤ U / ρ := by
  set g : ℂ → ℂ := fun ζ => u (x + ζ • e) with hg
  have hlin : Differentiable ℂ (fun ζ : ℂ => x + ζ • e) := by fun_prop
  have hgd : DifferentiableOn ℂ g (closedBall 0 ρ) :=
    hu.comp hlin.differentiableOn fun ζ hζ => hsub ζ (mem_closedBall_zero_iff.1 hζ)
  have hd : DiffContOnCl ℂ g (ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball _ hρ.ne']
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd
    (C := U) fun ζ hζ => hb ζ (le_of_eq (mem_sphere_zero_iff_norm.1 hζ))
  have hx : x ∈ O := by simpa using hsub 0 (by simpa using hρ.le)
  have hder : HasDerivAt g (fderiv ℂ u x e) 0 := by
    have h1 : HasDerivAt (fun ζ : ℂ => x + ζ • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add x
    have h2 : HasFDerivAt u (fderiv ℂ u x) (x + (0 : ℂ) • e) := by
      simpa using (hu.differentiableAt (hO.mem_nhds hx)).hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  rwa [hder.deriv] at key

/-- Bound of `Du(x)(a, c)` from coordinatewise Cauchy estimates. -/
theorem norm_fderiv_phase_le {O : Set (P11Phase n)} {u : P11Phase n → ℂ} (hO : IsOpen O)
    (hu : DifferentiableOn ℂ u O) {x : P11Phase n} {σ ρ U : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (hθ : ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ σ →
      (x.1 + ζ • Pi.single i 1, x.2) ∈ O ∧ ‖u (x.1 + ζ • Pi.single i 1, x.2)‖ ≤ U)
    (hη : ∀ i : Fin n, ∀ ζ : ℂ, ‖ζ‖ ≤ ρ →
      (x.1, x.2 + ζ • Pi.single i 1) ∈ O ∧ ‖u (x.1, x.2 + ζ • Pi.single i 1)‖ ≤ U)
    (a c : P11CVec n) :
    ‖fderiv ℂ u x (a, c)‖ ≤ n * ‖a‖ * (U / σ) + n * ‖c‖ * (U / ρ) := by
  have h1 : ∀ (i : Fin n) (ζ : ℂ), x + ζ • ((Pi.single i 1 : P11CVec n), (0 : P11CVec n)) =
      (x.1 + ζ • Pi.single i 1, x.2) := fun i ζ => by ext <;> simp
  have h2 : ∀ (i : Fin n) (ζ : ℂ), x + ζ • ((0 : P11CVec n), (Pi.single i 1 : P11CVec n)) =
      (x.1, x.2 + ζ • Pi.single i 1) := fun i ζ => by ext <;> simp
  have e1 : ∀ i : Fin n, ‖fderiv ℂ u x (Pi.single i 1, 0)‖ ≤ U / σ := fun i =>
    norm_fderiv_dir_le hO hu hσ (fun ζ hζ => by rw [h1]; exact (hθ i ζ hζ).1)
      (fun ζ hζ => by rw [h1]; exact (hθ i ζ hζ).2)
  have e2 : ∀ i : Fin n, ‖fderiv ℂ u x (0, Pi.single i 1)‖ ≤ U / ρ := fun i =>
    norm_fderiv_dir_le hO hu hρ (fun ζ hζ => by rw [h2]; exact (hη i ζ hζ).1)
      (fun ζ hζ => by rw [h2]; exact (hη i ζ hζ).2)
  have hdec : ((a, c) : P11Phase n) = ∑ i, a i • ((Pi.single i 1 : P11CVec n), (0 : P11CVec n)) +
      ∑ i, c i • ((0 : P11CVec n), (Pi.single i 1 : P11CVec n)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hdec, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖a i * fderiv ℂ u x (Pi.single i 1, 0)‖ ≤ ∑ _i : Fin n, ‖a‖ * (U / σ) :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul]
            exact mul_le_mul (norm_le_pi_norm a i) (e1 i) (norm_nonneg _) (norm_nonneg _)
      _ = n * ‖a‖ * (U / σ) := by simp; ring
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖c i * fderiv ℂ u x (0, Pi.single i 1)‖ ≤ ∑ _i : Fin n, ‖c‖ * (U / ρ) :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul]
            exact mul_le_mul (norm_le_pi_norm c i) (e2 i) (norm_nonneg _) (norm_nonneg _)
      _ = n * ‖c‖ * (U / ρ) := by simp; ring

end KAM.Planetary

end
