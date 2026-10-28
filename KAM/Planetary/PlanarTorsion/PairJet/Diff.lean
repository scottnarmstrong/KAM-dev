/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.PairJet.Defs
public import KAM.Planetary.PlanarTorsion.PairJet.Ray
public import KAM.Planetary.PlanarTorsion.PairJet.Diag
public import KAM.Planetary.SecularForm.ParameterIntegral

/-!
# Planar quartic torsion: differentiating the pair average under the integral

Blueprint P, Part 11b (`stepP:p11b:pj-formal`, via `bpP:p8:e-diff`): the pair integrand is jointly
real analytic in the angles and the slow variable on an open neighbourhood of
`[0,2π]² × {0}`, so the diagonal derivatives of the pair average at `0` are the averages of the
diagonal derivatives of the integrand (`p11cPJ_diag_integral`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary

section Orbit

private theorem pjD_planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem pjD_planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem pjD_planeSq_lt_one {v : Fin 2 → ℝ} (hv : planeLength v < 1) : planeSq v < 1 := by
  have h : planeLength v ^ 2 < 1 := by
    have := planeLength_nonneg v; nlinarith
  rwa [planeLength_sq] at h

private theorem pjD_analyticAt_snd (i : Fin 2) (x : ℝ × (Fin 2 → ℝ)) :
    AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => x.2 i) x :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin 2 → ℝ))).analyticAt x

/-- The unit-axis orbit is real analytic jointly in the mean longitude and `v`, for `ℓ v < 1`. -/
theorem p11cPJ_orbit_analyticAt {x : ℝ × (Fin 2 → ℝ)} (hx : planeLength x.2 < 1) :
    AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => p11c_orbit x.1 x.2) x := by
  have hF : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) x :=
    analyticOnNhd_keplerLong x hx
  have hcos : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => Real.cos (keplerLong x.1 x.2)) x :=
    AnalyticAt.comp (g := Real.cos) (f := fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (x := x)
      (Real.contDiff_cos (n := ω)).contDiffAt.analyticAt hF
  have hsin : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => Real.sin (keplerLong x.1 x.2)) x :=
    AnalyticAt.comp (g := Real.sin) (f := fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (x := x)
      (Real.contDiff_sin (n := ω)).contDiffAt.analyticAt hF
  have hsq : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => planeSq x.2) x := by
    simp only [pjD_planeSq_two]
    exact ((pjD_analyticAt_snd 0 x).pow 2).add ((pjD_analyticAt_snd 1 x).pow 2)
  have hpos : 0 < 1 - planeSq x.2 := sub_pos.2 (pjD_planeSq_lt_one hx)
  have hk : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => sqrt (1 - planeSq x.2)) x :=
    (((analyticAt_const.sub hsq).contDiffAt (n := ω)).sqrt hpos.ne').analyticAt
  have hk0 : 0 ≤ sqrt (1 - planeSq x.2) := Real.sqrt_nonneg _
  have hd : AnalyticAt ℝ
      (fun x : ℝ × (Fin 2 → ℝ) => planeDot x.2 (orbitalUnit (keplerLong x.1 x.2))) x := by
    simp only [pjD_planeDot_two, orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ((pjD_analyticAt_snd 0 x).mul hcos).add ((pjD_analyticAt_snd 1 x).mul hsin)
  have hm : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) =>
      planeDot x.2 (orbitalUnit (keplerLong x.1 x.2)) / (1 + sqrt (1 - planeSq x.2))) x :=
    hd.div (analyticAt_const.add hk) (by linarith)
  have h0 : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) =>
      (sqrt (1 - planeSq x.2) • orbitalUnit (keplerLong x.1 x.2) - x.2 +
        (planeDot x.2 (orbitalUnit (keplerLong x.1 x.2)) / (1 + sqrt (1 - planeSq x.2))) • x.2) 0)
      x := by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbitalUnit,
      Matrix.cons_val_zero]
    exact ((hk.mul hcos).sub (pjD_analyticAt_snd 0 x)).add (hm.mul (pjD_analyticAt_snd 0 x))
  have h1 : AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) =>
      (sqrt (1 - planeSq x.2) • orbitalUnit (keplerLong x.1 x.2) - x.2 +
        (planeDot x.2 (orbitalUnit (keplerLong x.1 x.2)) / (1 + sqrt (1 - planeSq x.2))) • x.2) 1)
      x := by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbitalUnit,
      Matrix.cons_val_one]
    exact ((hk.mul hsin).sub (pjD_analyticAt_snd 1 x)).add (hm.mul (pjD_analyticAt_snd 1 x))
  have e : (fun x : ℝ × (Fin 2 → ℝ) => p11c_orbit x.1 x.2) = fun x : ℝ × (Fin 2 → ℝ) =>
      Complex.ofRealCLM
          ((sqrt (1 - planeSq x.2) • orbitalUnit (keplerLong x.1 x.2) - x.2 +
            (planeDot x.2 (orbitalUnit (keplerLong x.1 x.2)) / (1 + sqrt (1 - planeSq x.2))) •
              x.2) 0) +
        Complex.I * Complex.ofRealCLM
          ((sqrt (1 - planeSq x.2) • orbitalUnit (keplerLong x.1 x.2) - x.2 +
            (planeDot x.2 (orbitalUnit (keplerLong x.1 x.2)) / (1 + sqrt (1 - planeSq x.2))) •
              x.2) 1) := by
    funext x; simp [p11c_orbit]
  rw [e]
  exact (Complex.ofRealCLM.analyticAt _ |>.comp h0).add
    (analyticAt_const.mul (Complex.ofRealCLM.analyticAt _ |>.comp h1))

theorem p11c_orbit_zero (lam : ℝ) : p11c_orbit lam 0 = Complex.exp (Complex.I * (lam : ℂ)) := by
  have h1 : keplerLong lam (0 : Fin 2 → ℝ) = lam := keplerLong_zero_vec lam
  have h2 : planeSq (0 : Fin 2 → ℝ) = 0 := by simp [planeSq]
  have hE : Complex.exp (Complex.I * (lam : ℂ)) =
      ((Real.cos lam : ℝ) : ℂ) + Complex.I * ((Real.sin lam : ℝ) : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]; ring
  rw [hE]
  simp [p11c_orbit, h1, h2, orbitalUnit, planeDot]

end Orbit

section Integrand

local notation "cell2" => Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))

/-- The orbit difference whose inverse norm is the pair integrand, on `(l, y) ∈ ℝ² × ℝ⁴`. -/
def p11cPJG (a : ℝ) (p : (Fin 2 → ℝ) × (Fin 4 → ℝ)) : ℂ :=
  (a : ℂ) * p11c_orbit (p.1 0) ![p.2 0, p.2 2] - p11c_orbit (p.1 1) ![p.2 1, p.2 3]

/-- Points where both eccentricity vectors are in the disc and the planets are apart. -/
def p11cPJW (a : ℝ) : Set ((Fin 2 → ℝ) × (Fin 4 → ℝ)) :=
  {p | planeLength ![p.2 0, p.2 2] < 1 ∧ planeLength ![p.2 1, p.2 3] < 1 ∧ p11cPJG a p ≠ 0}

/-- The pair integrand on `ℝ² × ℝ⁴`. -/
def p11cPJF4 (a : ℝ) (p : (Fin 2 → ℝ) × (Fin 4 → ℝ)) : ℝ := ‖p11cPJG a p‖⁻¹

theorem p11cPJF4_eq (a : ℝ) (l : Fin 2 → ℝ) (y : Fin 4 → ℝ) :
    p11cPJF4 a (l, y) = p11cPJF a l (p11cPJequiv y) := by
  simp [p11cPJF4, p11cPJG, p11cPJF, p11cPJequiv_apply]

private theorem pjD_analyticAt_arg (m : Fin 2) (u v : Fin 4) (p : (Fin 2 → ℝ) × (Fin 4 → ℝ)) :
    AnalyticAt ℝ (fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => ((p.1 m, ![p.2 u, p.2 v]) :
      ℝ × (Fin 2 → ℝ))) p := by
  refine AnalyticAt.prod ?_ ?_
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) m).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 4 → ℝ))).analyticAt p
  · rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) u).comp
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 4 → ℝ))).analyticAt p
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) v).comp
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 4 → ℝ))).analyticAt p

theorem p11cPJG_analyticAt {a : ℝ} {p : (Fin 2 → ℝ) × (Fin 4 → ℝ)}
    (h0 : planeLength ![p.2 0, p.2 2] < 1) (h1 : planeLength ![p.2 1, p.2 3] < 1) :
    AnalyticAt ℝ (p11cPJG a) p := by
  have e0 : AnalyticAt ℝ (fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) =>
      p11c_orbit (p.1 0) ![p.2 0, p.2 2]) p :=
    AnalyticAt.comp (g := fun x : ℝ × (Fin 2 → ℝ) => p11c_orbit x.1 x.2)
      (f := fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => ((p.1 0, ![p.2 0, p.2 2]) : ℝ × (Fin 2 → ℝ)))
      (x := p) (p11cPJ_orbit_analyticAt (x := (p.1 0, ![p.2 0, p.2 2])) h0)
      (pjD_analyticAt_arg 0 0 2 p)
  have e1 : AnalyticAt ℝ (fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) =>
      p11c_orbit (p.1 1) ![p.2 1, p.2 3]) p :=
    AnalyticAt.comp (g := fun x : ℝ × (Fin 2 → ℝ) => p11c_orbit x.1 x.2)
      (f := fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => ((p.1 1, ![p.2 1, p.2 3]) : ℝ × (Fin 2 → ℝ)))
      (x := p) (p11cPJ_orbit_analyticAt (x := (p.1 1, ![p.2 1, p.2 3])) h1)
      (pjD_analyticAt_arg 1 1 3 p)
  exact (analyticAt_const.mul e0).sub e1

theorem p11cPJF4_analyticAt {a : ℝ} {p : (Fin 2 → ℝ) × (Fin 4 → ℝ)} (hp : p ∈ p11cPJW a) :
    AnalyticAt ℝ (p11cPJF4 a) p := by
  obtain ⟨h0, h1, h2⟩ := hp
  have hG := p11cPJG_analyticAt (a := a) h0 h1
  have hre : AnalyticAt ℝ (fun p => (p11cPJG a p).re) p :=
    (Complex.reCLM.analyticAt _).comp hG
  have him : AnalyticAt ℝ (fun p => (p11cPJG a p).im) p :=
    (Complex.imCLM.analyticAt _).comp hG
  have hsq : AnalyticAt ℝ (fun p => (p11cPJG a p).re ^ 2 + (p11cPJG a p).im ^ 2) p :=
    (hre.pow 2).add (him.pow 2)
  have hpos : 0 < (p11cPJG a p).re ^ 2 + (p11cPJG a p).im ^ 2 := by
    by_contra hneg
    have hz : (p11cPJG a p).re ^ 2 + (p11cPJG a p).im ^ 2 = 0 := by
      have := add_nonneg (sq_nonneg (p11cPJG a p).re) (sq_nonneg (p11cPJG a p).im)
      linarith
    apply h2
    apply Complex.ext
    · simpa using (by nlinarith [sq_nonneg (p11cPJG a p).re, sq_nonneg (p11cPJG a p).im] :
        (p11cPJG a p).re = 0)
    · simpa using (by nlinarith [sq_nonneg (p11cPJG a p).re, sq_nonneg (p11cPJG a p).im] :
        (p11cPJG a p).im = 0)
  have hsqrt : AnalyticAt ℝ (fun p => √((p11cPJG a p).re ^ 2 + (p11cPJG a p).im ^ 2)) p :=
    ((hsq.contDiffAt (n := ω)).sqrt hpos.ne').analyticAt
  have hnorm : (fun q => ‖p11cPJG a q‖⁻¹) = fun q =>
      (√((p11cPJG a q).re ^ 2 + (p11cPJG a q).im ^ 2))⁻¹ := by
    funext q; rw [Complex.norm_eq_sqrt_sq_add_sq]
  unfold p11cPJF4
  have hn0 : √((p11cPJG a p).re ^ 2 + (p11cPJG a p).im ^ 2) ≠ 0 := Real.sqrt_pos.2 hpos |>.ne'
  rw [hnorm]
  exact hsqrt.inv hn0

theorem isOpen_p11cPJW (a : ℝ) : IsOpen (p11cPJW a) := by
  have hc0 : Continuous fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => (![p.2 0, p.2 2] : Fin 2 → ℝ) := by
    fun_prop
  have hc1 : Continuous fun p : (Fin 2 → ℝ) × (Fin 4 → ℝ) => (![p.2 1, p.2 3] : Fin 2 → ℝ) := by
    fun_prop
  have hW1 : IsOpen {p : (Fin 2 → ℝ) × (Fin 4 → ℝ) |
      planeLength ![p.2 0, p.2 2] < 1 ∧ planeLength ![p.2 1, p.2 3] < 1} :=
    (isOpen_planeLength_lt_one.preimage hc0).inter (isOpen_planeLength_lt_one.preimage hc1)
  have hcont : ContinuousOn (p11cPJG a) {p : (Fin 2 → ℝ) × (Fin 4 → ℝ) |
      planeLength ![p.2 0, p.2 2] < 1 ∧ planeLength ![p.2 1, p.2 3] < 1} :=
    fun p hp => (p11cPJG_analyticAt hp.1 hp.2).continuousAt.continuousWithinAt
  have := hcont.isOpen_inter_preimage hW1 (isOpen_ne (x := (0 : ℂ)))
  convert this using 1
  ext p
  simp [p11cPJW, and_assoc]

theorem mem_p11cPJW_zero {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (l : Fin 2 → ℝ) :
    (l, (0 : Fin 4 → ℝ)) ∈ p11cPJW a := by
  have hz : planeLength (![0, 0] : Fin 2 → ℝ) < 1 := by simp [planeLength, planeSq]
  refine ⟨by simpa using hz, by simpa using hz, ?_⟩
  simp only [p11cPJG, Pi.zero_apply]
  have h0 : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> simp
  rw [h0, p11c_orbit_zero, p11c_orbit_zero]
  intro h
  have h1 : ‖(a : ℂ) * Complex.exp (Complex.I * (l 0 : ℂ))‖ =
      ‖Complex.exp (Complex.I * (l 1 : ℂ))‖ := by rw [sub_eq_zero.1 h]
  have e0 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, e0, e0, Complex.norm_real, Real.norm_eq_abs, mul_one,
    abs_of_pos ha.1] at h1
  linarith [ha.2]

end Integrand

section Differentiation

/-- Partial `y`-derivatives of a jointly smooth function on an open set. -/
theorem p11cPJ_iteratedFDeriv_slice {W : Set ((Fin 2 → ℝ) × (Fin 4 → ℝ))} (hW : IsOpen W)
    {F : (Fin 2 → ℝ) × (Fin 4 → ℝ) → ℝ} (hF : ContDiffOn ℝ 4 F W) {t : Fin 2 → ℝ}
    {y : Fin 4 → ℝ} (hty : (t, y) ∈ W) (j : ℕ) (hj : j ≤ 4) :
    iteratedFDeriv ℝ j (fun y' => F (t, y')) y =
      (iteratedFDeriv ℝ j F (t, y)).compContinuousLinearMap
        fun _ => (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Fin 4 → ℝ)) := by
  set ι := ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Fin 4 → ℝ) with hι
  set a : (Fin 2 → ℝ) × (Fin 4 → ℝ) := (t, 0) with ha
  set S : Set ((Fin 2 → ℝ) × (Fin 4 → ℝ)) := (fun z => a + z) ⁻¹' W with hS
  have hSo : IsOpen S := hW.preimage (continuous_const.add continuous_id)
  have hFa : ContDiffOn ℝ 4 (fun z => F (a + z)) S :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have hy : ι y ∈ S := by simpa [hS, ha, hι] using hty
  have h1 := ι.iteratedFDerivWithin_comp_right (f := fun z => F (a + z)) hFa hSo.uniqueDiffOn
    ((hSo.preimage ι.continuous).uniqueDiffOn) hy (i := j) (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen _ hSo hy,
    iteratedFDerivWithin_of_isOpen _ (hSo.preimage ι.continuous) (by exact hy)] at h1
  have hfun : (fun y' => F (t, y')) = (fun z => F (a + z)) ∘ ι := by
    funext y'; simp [ha, hι]
  rw [hfun, h1, iteratedFDeriv_comp_add_left]
  simp [ha, hι]

/-- Differentiation under the angle integral for a jointly `C⁴` integrand. -/
theorem p11cPJ_e_diff {W : Set ((Fin 2 → ℝ) × (Fin 4 → ℝ))} (hW : IsOpen W)
    {F : (Fin 2 → ℝ) × (Fin 4 → ℝ) → ℝ} (hF : ContDiffOn ℝ 4 F W)
    (hK : ∀ t ∈ SecularForm.cell 2, (t, (0 : Fin 4 → ℝ)) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ t ∈ SecularForm.cell 2, ∀ y ∈ ball (0 : Fin 4 → ℝ) δ, (t, y) ∈ W) ∧
      (∀ j ≤ 4, ContinuousOn (fun t => iteratedFDeriv ℝ j (fun y => F (t, y)) 0)
        (SecularForm.cell 2)) ∧
      ∀ j ≤ 4, iteratedFDeriv ℝ j (fun y : Fin 4 → ℝ => ∫ t in SecularForm.cell 2, F (t, y)) 0 =
        ∫ t in SecularForm.cell 2, iteratedFDeriv ℝ j (fun y => F (t, y)) 0 := by
  have hKc : IsCompact (SecularForm.cell 2 ×ˢ ({0} : Set (Fin 4 → ℝ))) :=
    SecularForm.isCompact_cell.prod isCompact_singleton
  have hKW : SecularForm.cell 2 ×ˢ ({0} : Set (Fin 4 → ℝ)) ⊆ W := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact hK t ht
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hW hKW
  have hmem : ∀ t ∈ SecularForm.cell 2, ∀ y ∈ ball (0 : Fin 4 → ℝ) δ, (t, y) ∈ W := by
    intro t ht y hy
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨(t, 0), ⟨ht, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    exact max_lt hδ (by simpa using hy)
  have hcontj : ∀ j : ℕ, j ≤ 4 → ContinuousOn
      (fun z : (Fin 2 → ℝ) × (Fin 4 → ℝ) => iteratedFDeriv ℝ j (fun y => F (z.1, y)) z.2)
      (SecularForm.cell 2 ×ˢ ball (0 : Fin 4 → ℝ) δ) := by
    intro j hj
    have hcont : ContinuousOn (fun z : (Fin 2 → ℝ) × (Fin 4 → ℝ) => iteratedFDeriv ℝ j F z) W := by
      have := hF.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
        hW.uniqueDiffOn
      exact this.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hW hz).symm
    have hL := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℝ)
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Fin 4 → ℝ))).continuous
    refine (hL.comp_continuousOn hcont).mono ?_ |>.congr ?_
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact hmem t ht y hy
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact p11cPJ_iteratedFDeriv_slice hW hF (hmem t ht y hy) j hj
  refine ⟨δ, hδ, hmem, fun j hj => ?_, fun j hj => ?_⟩
  · exact (hcontj j hj).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_ball_self hδ⟩)
  · refine SecularForm.e_diff (n := 2) (d := 4) isOpen_ball (f := fun t y => F (t, y)) j
      (fun i hi => hcontj i (hi.trans hj)) ?_ (mem_ball_self hδ)
    intro t ht
    exact (hF.of_le (by exact_mod_cast hj)).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy => hmem t ht y hy)

/-- The diagonal derivatives of the pair average at `0` are the averages of those of the
integrand. -/
theorem p11cPJ_diag_integral {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j ≤ 4)
    (w : Phase 2) :
    iteratedFDeriv ℝ j (p11c_pairAverage a) 0 (fun _ => w) =
      (2 * π) ^ (-2 : ℤ) * ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        iteratedFDeriv ℝ j (p11cPJF a l) 0 (fun _ => w) := by
  set c : ℝ := (2 * π) ^ (-2 : ℤ) with hc
  set F : (Fin 2 → ℝ) × (Fin 4 → ℝ) → ℝ := fun p => c * p11cPJF4 a p with hF
  have hAn : AnalyticOnNhd ℝ (p11cPJF4 a) (p11cPJW a) := fun p hp => p11cPJF4_analyticAt hp
  have hCD : ContDiffOn ℝ 4 (p11cPJF4 a) (p11cPJW a) := fun p hp =>
    ((hAn p hp).contDiffAt).contDiffWithinAt
  have hFd : ContDiffOn ℝ 4 F (p11cPJW a) := contDiffOn_const.mul hCD
  obtain ⟨δ, hδ, hmem, hcont, hdiff⟩ := p11cPJ_e_diff (isOpen_p11cPJW a) hFd
    (fun t _ => mem_p11cPJW_zero ha t)
  set y : Fin 4 → ℝ := p11cPJequiv.symm w with hy
  have hey : p11cPJequiv y = w := by simp [hy]
  have hfun : (p11c_pairAverage a ∘ p11cPJequiv) =
      fun y => ∫ t in SecularForm.cell 2, F (t, y) := by
    funext y
    simp only [Function.comp, p11c_pairAverage, hF, p11cPJF4_eq, integral_const_mul]
    rfl
  have h1 := p11cPJ_diag_comp_equiv (p11c_pairAverage a) j y
  rw [hey] at h1
  rw [← h1, hfun, hdiff j hj]
  have hint : IntegrableOn (fun t => iteratedFDeriv ℝ j (fun y => F (t, y)) 0)
      (SecularForm.cell 2) volume := (hcont j hj).integrableOn_compact SecularForm.isCompact_cell
  have happ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Fin 4 → ℝ) ℝ
    (fun _ => y)).integral_comp_comm hint
  have hcomm : (∫ t in SecularForm.cell 2, iteratedFDeriv ℝ j (fun y => F (t, y)) 0)
      (fun _ => y) = ∫ t in SecularForm.cell 2, iteratedFDeriv ℝ j (fun y => F (t, y)) 0
        (fun _ => y) := by
    simpa using happ.symm
  rw [hcomm, ← integral_const_mul]
  refine setIntegral_congr_fun SecularForm.measurableSet_cell fun t ht => ?_
  have hfa : ContDiffAt ℝ j (fun y' => p11cPJF4 a (t, y')) 0 := by
    have h0 : AnalyticAt ℝ (fun y' : Fin 4 → ℝ => p11cPJF4 a (t, y')) 0 :=
      (hAn (t, 0) (mem_p11cPJW_zero ha t)).comp
        (analyticAt_const.prod (analyticAt_id))
    exact h0.contDiffAt
  have h2 : (fun y' => F (t, y')) = fun y' => c • p11cPJF4 a (t, y') := by
    funext y'; simp [hF]
  have h3 : (fun y' => p11cPJF4 a (t, y')) = (p11cPJF a t) ∘ p11cPJequiv := by
    funext y'; simp [p11cPJF4_eq]
  simp only [h2]
  rw [iteratedFDeriv_const_smul_apply' hfa, h3, p11cPJ_diag_comp_equiv, hey]
  simp

/-- The pair integrand is real analytic at `0`. -/
theorem p11cPJF_analyticAt {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (l : Fin 2 → ℝ) :
    AnalyticAt ℝ (p11cPJF a l) 0 := by
  have h := p11cPJF4_analyticAt (mem_p11cPJW_zero ha l)
  have h2 : AnalyticAt ℝ (fun z : Phase 2 => p11cPJF4 a (l, p11cPJequiv.symm z)) 0 := by
    refine AnalyticAt.comp (g := p11cPJF4 a)
      (f := fun z : Phase 2 => ((l, p11cPJequiv.symm z) : (Fin 2 → ℝ) × (Fin 4 → ℝ))) (x := 0)
      (by simpa using h) ?_
    exact analyticAt_const.prod (p11cPJequiv.symm.toContinuousLinearMap.analyticAt 0)
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [p11cPJF4_eq]

end Differentiation

end KAM.Planetary

end
