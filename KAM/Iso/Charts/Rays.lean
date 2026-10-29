/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Chart

/-!
# Part 3 (local charts): Diophantine vectors in an open set, rays of a patch

Blueprint nodes `bpI:p3:dio-open`,
`bpI:p3:rays` and `bpI:p3:patch-rays`. `n = 2`, `τ = 2`.

* `dio_open` (`bpI:p3:dio-open`): a nonempty, open, bounded `O ⊆ ℝ²` contains a
  `(γ, 2)`-Diophantine vector for some `γ > 0`. G3 enters only through the premise
  `G3Statement` (the frozen `KAM.volume_not_diophantine_le`): with `C` from G3 and
  `γ = vol O / (2 (C + 1))`, the non-Diophantine part of `O` has measure `≤ C γ < vol O`.
* `rays` (`bpI:p3:rays`): at a centre `c ∈ closure B'` and for any open interval `(a, b)` there
  is a ray (`IsRay`): a Diophantine vector `ω*` with `a_c(ω*) > 0`, slope `m ∈ (a, b)` and
  `m_h/4 < ‖ω*‖ < m_h/2`. The open set is the sector `O` of the blueprint; it is nonempty
  because `t (g_c + ς g_c^⊥)` has `a_c = t` and slope `ς`.
* `patch_rays` (`bpI:p3:patch-rays`, existence form): for a patch, one ray with slope in
  `(δ_m/2, δ_m)` and one with slope in `(-δ_m, -δ_m/2)`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology MeasureTheory

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-! ### Diophantine vectors in an open set -/

/-- `bpI:p3:dio-open` (G3 as the premise `hG3`). -/
theorem dio_open (hG3 : G3Statement) {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (hne : O.Nonempty)
    (hb : Bornology.IsBounded O) : ∃ γ : ℝ, 0 < γ ∧ ∃ ω ∈ O, IsDiophantine γ 2 ω := by
  have hτ : ((2 : ℕ) : ℝ) - 1 < 2 := by norm_num
  obtain ⟨C, hC⟩ := hG3 (n := 2) (τ := 2) hτ hb
  have hvpos : 0 < volume O := hO.measure_pos volume hne
  have hvfin : volume O < ⊤ := hb.measure_lt_top
  have hv : 0 < (volume O).toReal := ENNReal.toReal_pos hvpos.ne' hvfin.ne
  set v := (volume O).toReal with hvdef
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hγ : 0 < v / (2 * (C' + 1)) := by positivity
  refine ⟨v / (2 * (C' + 1)), hγ, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : O ⊆ {ω ∈ O | ¬ IsDiophantine (v / (2 * (C' + 1))) 2 ω} :=
    fun ω hω => ⟨hω, hcon ω hω⟩
  have h1 : volume O ≤ volume {ω ∈ O | ¬ IsDiophantine (v / (2 * (C' + 1))) 2 ω} :=
    measure_mono hsub
  have h2 := hC _ hγ
  have h3 : C * (v / (2 * (C' + 1))) ≤ v / 2 := by
    have hCle : C * (v / (2 * (C' + 1))) ≤ C' * (v / (2 * (C' + 1))) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hγ.le
    have heq : C' * (v / (2 * (C' + 1))) = v / 2 * (C' / (C' + 1)) := by
      field_simp
    have hle1 : C' / (C' + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    calc C * (v / (2 * (C' + 1))) ≤ C' * (v / (2 * (C' + 1))) := hCle
      _ = v / 2 * (C' / (C' + 1)) := heq
      _ ≤ v / 2 * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = v / 2 := mul_one _
  have h4 : volume O ≤ ENNReal.ofReal (v / 2) :=
    h1.trans (h2.trans (ENNReal.ofReal_le_ofReal h3))
  have h5 : ENNReal.ofReal (v / 2) < ENNReal.ofReal v :=
    (ENNReal.ofReal_lt_ofReal_iff hv).2 (by linarith)
  rw [hvdef, ENNReal.ofReal_toReal hvfin.ne] at h5
  exact absurd (h4.trans_lt h5) (lt_irrefl _)

/-! ### Rays in a sector -/

/-- The point `t (g + ς g^⊥)` has longitudinal coordinate `t` and slope `ς`. -/
theorem aCoord_slope_dir {g : Fin 2 → ℝ} (hg : g ≠ 0) {t : ℝ} (ht : t ≠ 0) (ς : ℝ) :
    aCoord g (t • (g + ς • perp g)) = t ∧ slope g (t • (g + ς • perp g)) = ς := by
  have hgg : g ⬝ᵥ g ≠ 0 := (dotProduct_self_pos hg).ne'
  have e1 : g ⬝ᵥ (t • (g + ς • perp g)) = t * (g ⬝ᵥ g) := by
    simp only [dotProduct, Fin.sum_univ_two, perp, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have e2 : det2 g (t • (g + ς • perp g)) = ς * (t * (g ⬝ᵥ g)) := by
    simp only [det2, dotProduct, Fin.sum_univ_two, perp, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨?_, ?_⟩
  · unfold aCoord
    rw [e1, mul_div_assoc, div_self hgg, mul_one]
  · unfold slope
    rw [e2, e1]
    exact mul_div_cancel_right₀ _ (mul_ne_zero ht hgg)

/-- The sector `{ω : a_g(ω) > 0, slope ∈ J, lo < ‖ω‖ < hi}` is open. -/
theorem isOpen_sector {g : Fin 2 → ℝ} (hg : g ≠ 0) {J : Set ℝ} (hJ : IsOpen J) (lo hi : ℝ) :
    IsOpen {ω : Fin 2 → ℝ | 0 < aCoord g ω ∧ slope g ω ∈ J ∧ lo < ‖ω‖ ∧ ‖ω‖ < hi} := by
  have hA : IsOpen {ω : Fin 2 → ℝ | 0 < aCoord g ω} :=
    isOpen_lt continuous_const (continuous_aCoord g)
  have hq : 0 < g ⬝ᵥ g := dotProduct_self_pos hg
  have hslope : ContinuousOn (slope g) {ω : Fin 2 → ℝ | 0 < aCoord g ω} := by
    have hnum : Continuous (fun ω : Fin 2 → ℝ => det2 g ω) := by
      unfold det2
      fun_prop
    have hden : Continuous (fun ω : Fin 2 → ℝ => g ⬝ᵥ ω) := by
      simp only [dotProduct]
      fun_prop
    refine hnum.continuousOn.div hden.continuousOn fun ω hω => ?_
    rw [dotProduct_eq_aCoord_mul hg]
    exact (mul_pos hω hq).ne'
  have h1 := hslope.isOpen_inter_preimage hA hJ
  have h2 : IsOpen {ω : Fin 2 → ℝ | lo < ‖ω‖} := isOpen_lt continuous_const continuous_norm
  have h3 : IsOpen {ω : Fin 2 → ℝ | ‖ω‖ < hi} := isOpen_lt continuous_norm continuous_const
  have := (h1.inter h2).inter h3
  convert this using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  tauto

/-- `∇h(c) ≠ 0` at a centre `c ∈ closure B'` (`det_identity` (a), `closure B' ⊆ B ⊆ U`). -/
theorem frequencyMap_ne_zero_of_mem_closure (hd : HeadData B s₀ r₀ h B' η) {c : Fin 2 → ℝ}
    (hc : c ∈ closure B') : frequencyMap h c ≠ 0 :=
  (det_identity hd (subset_realAct_charts hd.hr (hd.inside hc))).2.2.1

/-- `bpI:p3:rays` (`J = (a, b)`). -/
theorem rays (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) (hG3 : G3Statement)
    {c : Fin 2 → ℝ} (hc : c ∈ closure B') {a b : ℝ} (hab : a < b) :
    ∃ (γ : ℝ) (ωs : Fin 2 → ℝ) (m : ℝ), IsRay h B B' c γ ωs m ∧ m ∈ Ioo a b := by
  have hg : frequencyMap h c ≠ 0 := frequencyMap_ne_zero_of_mem_closure hd hc
  have hmh : 0 < mhConst h B B' := (compact hd hne).2.2.2.2.1
  set O : Set (Fin 2 → ℝ) := {ω | 0 < aCoord (frequencyMap h c) ω ∧
    slope (frequencyMap h c) ω ∈ Ioo a b ∧ mhConst h B B' / 4 < ‖ω‖ ∧
    ‖ω‖ < mhConst h B B' / 2} with hO
  have hOopen : IsOpen O := isOpen_sector hg isOpen_Ioo _ _
  have hObdd : Bornology.IsBounded O := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := mhConst h B B' / 2)).subset ?_
    intro ω hω
    rw [mem_closedBall, dist_zero_right]
    exact hω.2.2.2.le
  -- nonempty: the ray `t (g + ς g^⊥)` with `ς = (a + b) / 2`
  have hONe : O.Nonempty := by
    have hς : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hv1 : aCoord (frequencyMap h c)
        (frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)) = 1 := by
      have := (aCoord_slope_dir hg one_ne_zero ((a + b) / 2)).1
      simpa using this
    have hvne : frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c) ≠ 0 := by
      intro h0
      rw [h0] at hv1
      simp [aCoord] at hv1
    have hvpos : 0 < ‖frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)‖ :=
      norm_pos_iff.2 hvne
    have htpos : 0 < (3 / 8 * mhConst h B B') /
        ‖frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)‖ := by positivity
    obtain ⟨hat, hst⟩ := aCoord_slope_dir hg htpos.ne' ((a + b) / 2)
    refine ⟨((3 / 8 * mhConst h B B') /
        ‖frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)‖) •
        (frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)), ?_⟩
    have hnorm : ‖((3 / 8 * mhConst h B B') /
        ‖frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c)‖) •
        (frequencyMap h c + ((a + b) / 2) • perp (frequencyMap h c))‖ =
        3 / 8 * mhConst h B B' := by
      rw [norm_smul, Real.norm_of_nonneg htpos.le]
      field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hat]; exact htpos
    · rw [hst]; exact hς
    · rw [hnorm]; linarith
    · rw [hnorm]; linarith
  obtain ⟨γ, hγ, ω, hωO, hωD⟩ := dio_open hG3 hOopen hONe hObdd
  exact ⟨γ, ω, slope (frequencyMap h c) ω, ⟨hγ, hωD, hωO.1, rfl, hωO.2.2.1, hωO.2.2.2⟩,
    hωO.2.1⟩

/-- `bpI:p3:patch-rays` (existence form): rays with slopes in `(δ_m/2, δ_m)`, `(-δ_m, -δ_m/2)`. -/
theorem patch_rays (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) (hG3 : G3Statement)
    {η₁ δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)} {Ψ : ℝ × ℝ → Fin 2 → ℝ}
    (hp : IsPatch h B r₀ B' η₁ c W Ψ δE δm ρc) :
    ∃ (γp γm mp mm : ℝ) (ωp ωm : Fin 2 → ℝ), IsRay h B B' c γp ωp mp ∧ mp ∈ Ioo (δm / 2) δm ∧
      IsRay h B B' c γm ωm mm ∧ mm ∈ Ioo (-δm) (-(δm / 2)) := by
  have hδ := hp.δm_pos
  obtain ⟨γp, ωp, mp, hrp, hmp⟩ := rays hd hne hG3 hp.c_mem (a := δm / 2) (b := δm) (by linarith)
  obtain ⟨γm, ωm, mm, hrm, hmm⟩ :=
    rays hd hne hG3 hp.c_mem (a := -δm) (b := -(δm / 2)) (by linarith)
  exact ⟨γp, γm, mp, mm, ωp, ωm, hrp, hmp, hrm, hmm⟩

end KAM.Iso.Charts
