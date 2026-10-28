/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.AffineFlowSimple

/-!
# Affine generating functions: the time-one flow (P11A-C6)

`bpP:p11a:affine-flow` (`affine_flow`). The standing hypotheses of `bpN:p5:flow` hold in the gauge
`scaleCLE (s/2) σ` with `ε = κ = 2(n+1)A/σ ≤ 1/2` (`stepP:p11a:af-field`); the flow `Φ = X^1` is
holomorphic on `U ⊆ Ω^{1/2}` with trajectories in `Ω` (`af-flow`, via `Canonical.flow_a`, `flow_b`);
its simple form is `AffineFlowSimple` (`af-simple`); `D Φ - 1` is controlled by `Canonical.flow_c`
and the block structure (`af-deriv`); form invariance, periodicity, inverse and reality are
`flow_symplFormC`, `flow_d`, `flow_c`, `flow_e` (`af-rest`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {r s sigma A : ℝ}

/-- `stepP:p11a:af-flow`: displacement of the time-one map along trajectories. -/
theorem flow_displacement (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) :
    ‖(p11Flow (p11Affine p0 p1) r s sigma 1 z).1 - z.1‖ ≤ A ∧
    ‖(p11Flow (p11Affine p0 p1) r s sigma 1 z).2 - z.2‖ ≤ (n+1)*s*A/sigma := by
  obtain ⟨h0, hsol, -, -⟩ := KAM.Canonical.flow_a (smallField H) (U_sub_half H hz)
  have hI : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt
      (fun t => KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z)
      (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1)) (KAM.Weighted.Dom n {0} s (r-sigma)) t z)) t :=
    fun t ht => (hsol t ht).2
  have h1 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h2 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Icc (-1 : ℝ) 1)
      (f := fun t => (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).1)
      (f' := fun t => (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1)) (KAM.Weighted.Dom n {0} s (r-sigma)) t z)).1)
      (C := A)
      (fun t ht => by
        have := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt t (hI t ht)
        simpa [Function.comp_def] using this.hasDerivWithinAt)
      (fun t ht => (field_bound H (hsol t ht).1).1) (convex_Icc _ _) h1 h2
    simp only [h0] at this
    simp at this
    exact this
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Icc (-1 : ℝ) 1)
      (f := fun t => (KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1))
        (KAM.Weighted.Dom n {0} s (r-sigma)) t z).2)
      (f' := fun t => (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1) (KAM.Canonical.flow
        (KAM.hamiltonianVectorFieldℂ (p11Affine p0 p1)) (KAM.Weighted.Dom n {0} s (r-sigma)) t z)).2)
      (C := (n+1)*s*A/sigma)
      (fun t ht => by
        have := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt t (hI t ht)
        simpa [Function.comp_def] using this.hasDerivWithinAt)
      (fun t ht => (field_bound H (hsol t ht).1).2) (convex_Icc _ _) h1 h2
    simp only [h0] at this
    simp at this
    exact this

/-- Scaled norm and the gauge norm agree. -/
theorem norm_affineGauge_eq (H : P11AffineHyp p0 p1 r s sigma A) (u : P11Phase n) :
    ‖affineGauge H u‖ = KAM.Canonical.scaledNorm (s/2) sigma u :=
  KAM.Canonical.norm_scaleCLE _ _ u

/-- `stepP:p11a:af-deriv`: the gauge and operator-norm bounds on `D Φ - 1`. -/
theorem fderiv_flow_sub_id (H : P11AffineHyp p0 p1 r s sigma A) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (s/2) (r-2*sigma)) :
    p11GaugeBound (s/2) sigma
      (fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z - ContinuousLinearMap.id ℂ _)
      (2*(2*(n+1)*A/sigma)) ∧
    ‖fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z - ContinuousLinearMap.id ℂ _‖ ≤
      2*(2*(n+1)*A/sigma) + (2*(n+1)*A/sigma)*s/sigma := by
  set κ := 2*(n+1)*A/sigma with hκ
  have hσ := H.sigma_pos
  have hs := H.s_pos
  have hκ0 : 0 ≤ κ := kappa_nonneg H
  have hzU := V_sub_U H hz
  have hc := (KAM.Canonical.flow_c (smallField H) (V_sub_one H hz)).2.2.2.2 1
    ⟨by norm_num, le_rfl⟩
  set L := fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z - ContinuousLinearMap.id ℂ _
    with hL
  have hLu : ∀ u, L u = fderiv ℂ (p11Flow (p11Affine p0 p1) r s sigma 1) z u - u := fun u => rfl
  have hgauge : ∀ u, ‖affineGauge H (L u)‖ ≤ 2*κ*‖affineGauge H u‖ := fun u => by
    rw [hLu]; exact hc u
  refine ⟨fun u => ?_, ?_⟩
  · rw [← norm_affineGauge_eq H, ← norm_affineGauge_eq H]
    simpa [mul_assoc] using hgauge u
  · have hnn : 0 ≤ 2*κ + κ*s/sigma := by positivity
    refine (ContinuousLinearMap.opNorm_le_bound _ hnn fun u => ?_)
    obtain ⟨u1, u2⟩ := u
    have hge : ∀ w : P11Phase n, ‖affineGauge H (L w)‖ ≤ 2*κ*‖affineGauge H w‖ := hgauge
    have e1 : ‖affineGauge H ((u1, (0 : P11CVec n)))‖ ≤ ‖u1‖/sigma := by
      rw [norm_affineGauge_le_iff]
      exact ⟨by rw [div_mul_cancel₀ _ hσ.ne'], by simpa using by positivity⟩
    have e2 : ‖affineGauge H (((0 : P11CVec n), u2))‖ ≤ ‖u2‖/(s/2) := by
      rw [norm_affineGauge_le_iff]
      exact ⟨by simpa using by positivity, by rw [div_mul_cancel₀ _ (by positivity)]⟩
    have a1 := (norm_affineGauge_le_iff H _ _).1
      ((hge (u1, 0)).trans (mul_le_mul_of_nonneg_left e1 (by positivity)))
    have a2 := (norm_affineGauge_le_iff H _ _).1
      ((hge (0, u2)).trans (mul_le_mul_of_nonneg_left e2 (by positivity)))
    -- the first component of `L u` is that of `L (u1, 0)`
    have hfst : (L (u1, u2)).1 = (L (u1, 0)).1 := by
      rw [hLu, hLu]
      have := fderiv_flow_fst H hzU (u1, u2)
      have := fderiv_flow_fst H hzU (u1, 0)
      simp only at *
      simp [*]
    have hsnd : (L (u1, u2)).2 = (L (u1, 0)).2 + (L (0, u2)).2 := by
      have : ((u1, u2) : P11Phase n) = (u1, 0) + (0, u2) := by simp
      rw [this, map_add]; rfl
    have hu1 : ‖u1‖ ≤ ‖(u1, u2)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hu2 : ‖u2‖ ≤ ‖(u1, u2)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hk : (0 : ℝ) ≤ κ * s / sigma := by positivity
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [hfst]
      calc ‖(L (u1, 0)).1‖ ≤ 2*κ*(‖u1‖/sigma)*sigma := a1.1
        _ = 2*κ*‖u1‖ := by field_simp
        _ ≤ (2*κ + κ*s/sigma) * ‖(u1, u2)‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hu1 hκ0, mul_nonneg hk (norm_nonneg (u1, u2))]
    · rw [hsnd]
      calc ‖(L (u1, 0)).2 + (L (0, u2)).2‖ ≤ ‖(L (u1, 0)).2‖ + ‖(L (0, u2)).2‖ := norm_add_le _ _
        _ ≤ 2*κ*(‖u1‖/sigma)*(s/2) + 2*κ*(‖u2‖/(s/2))*(s/2) := add_le_add a1.2 a2.2
        _ = κ*s/sigma*‖u1‖ + 2*κ*‖u2‖ := by field_simp
        _ ≤ (2*κ + κ*s/sigma) * ‖(u1, u2)‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hu1 hk, mul_le_mul_of_nonneg_left hu2 hκ0]

end KAM.Planetary

end
