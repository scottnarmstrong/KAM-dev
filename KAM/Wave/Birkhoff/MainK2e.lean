/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2d

/-!
# The field of `K₂` (blueprint-W `bpW:w3:main`, Step XK2)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birkK2_field`: `DK₂(w) u = Ω(X_{K₂}(w), u)` with `X_{K₂} = birkXK2 = Σ_{n ≥ 1} V_n/(n+1)`.
Proof: `g(s) = DΛ(Γ_s w)(DΓ_s u) - DΛ(w)u - s DZ'(w)u - Ω(Q(s) - s V_0, u)` has derivative `0`
on `(-2,2)` (flow and variational equations, derivative of the homological identity,
symplecticity, `DΓ_s(ι V_s) = ι X_{Z'}(Γ_s)`), and `g(0) = 0`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem birkK2_field (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) (u : BirkSpace) :
    fderiv ℂ (birkK2 m hm ha hp) w u =
      birkOmegaPlus a p ha (by linarith) (birkXK2 m hm ha hp w) u := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  set ι := birkEmbed a (p + 1) p (by linarith) with hι
  set Ω := birkOmega ha (by linarith : (0 : ℝ) ≤ p) with hΩ
  set v : ℕ → BirkSpace := fun n => birkVn m hm ha hp n (fun _ => w) with hv
  set Q : ℝ → BirkSpace := fun r => ∑' k : ℕ, (r ^ k) • uqF m hm ha hp w k with hQ
  set c : ℂ := fderiv ℂ (birkHamZ m hm ha hp) w u with hc
  let g : ℝ → ℂ := fun s =>
    fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp s w) (birkGammaD m hm ha hp s w u) -
      fderiv ℂ (birkLambda m hm ha hp) w u - (s : ℂ) * c - Ω (ι (Q s - s • v 0)) u
  have hgd : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt g 0 s := by
    intro s hs
    have hs2 : |s| < 2 := abs_lt.2 ⟨hs.1, hs.2⟩
    have d1 := hasDerivAt_dLambda_gamma (ha := ha) (hm := hm) (hp := hp) s w u hs2 hw40
    have d2 : HasDerivAt (fun r : ℝ => (r : ℂ) * c) c s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const c
    have dQ := hasDerivAt_Qseries (ha := ha) (hm := hm) (hp := hp) w hw s hs2
    have dl : HasDerivAt (fun r : ℝ => Q r - r • v 0)
        ((∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w)) - v 0) s := by
      have h5 := (hasDerivAt_id s).smul_const (v 0)
      rw [one_smul] at h5
      exact dQ.sub h5
    set ℓ : BirkSpace →L[ℂ] ℂ := (Ω.flip u).comp ι with hℓ
    have d3 := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s dl
    have hfin := ((d1.sub_const (fderiv ℂ (birkLambda m hm ha hp) w u)).sub d2).sub d3
    refine hfin.congr_deriv ?_
    -- the value is `0`
    set Vs := ∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w) with hVs
    have hid := birkV_identity (ha := ha) (hm := hm) (hp := hp) s hs2 w hw
    have hsymp := birkGammaD_symplectic (ha := ha) (hm := hm) (hp := hp) s w (ι Vs) u hs2 hw40
    have hZ1 : fderiv ℂ (birkHamZ m hm ha hp) (birkGamma m hm ha hp s w)
        (birkGammaD m hm ha hp s w u) = Ω (ι Vs) u := by
      rw [(birkHamZ_isClassA m hm ha hp).field _ (Set.mem_univ _)]
      show Ω (ι (birkHamZX m hm ha hp (birkGamma m hm ha hp s w))) _ = _
      rw [← hid, ← hsymp]
    have hZ0 : c = Ω (ι (v 0)) u := by
      rw [hc, (birkHamZ_isClassA m hm ha hp).field _ (Set.mem_univ _)]
      show Ω (ι (birkHamZX m hm ha hp w)) _ = _
      rw [hv]; simp only []
      rw [birkVn_zero_const]
    rw [hZ1, hZ0]
    simp only [hℓ, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, map_sub, ContinuousLinearMap.sub_apply]
    ring
  have hdiff : DifferentiableOn ℝ g (Set.Ioo (-2) 2) := fun s hs =>
    (hgd s hs).differentiableAt.differentiableWithinAt
  have hconst := (isOpen_Ioo (a := (-2 : ℝ)) (b := 2)).is_const_of_deriv_eq_zero
    (convex_Ioo (-2 : ℝ) 2).isPreconnected hdiff (fun s hs => (hgd s hs).deriv)
    (x := 1) (y := 0) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have hg0 : g 0 = 0 := by
    have e1 : birkGamma m hm ha hp 0 w = w := lieGamma_zero _ w
    have e2 : birkGammaD m hm ha hp 0 w = ContinuousLinearMap.id ℂ BirkSpace :=
      lieGammaD_zero _ w
    have e3 : Q 0 = 0 := by
      simp only [hQ]
      rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
      simp [uqF]
    simp only [g, e1, e2, e3]
    simp
  have hg1 : g 1 = 0 := hconst.trans hg0
  -- identify the series at `s = 1`
  have hsu : Summable fun k : ℕ => uqF m hm ha hp w k := by
    refine (summable_nat_add_iff 1).1 ?_
    have hs1 := summable_birkVn (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw
    refine Summable.of_norm_bounded hs1 fun n => ?_
    simp only [uqF, norm_smul, one_pow, one_smul, Real.norm_eq_abs]
    have : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have hQ1 : Q 1 - (1 : ℝ) • v 0 = birkXK2 m hm ha hp w := by
    have : Q 1 = ∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)) • v n := by
      simp only [hQ, one_pow, one_smul]
      rw [hsu.tsum_eq_zero_add]
      simp only [uqF, zero_add]
      refine tsum_congr fun n => ?_
      rw [show ((1 : ℂ) / ((n : ℂ) + 1)) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
        Complex.coe_smul]
      rfl
    rw [this, one_smul]; rfl
  -- the chain rule for `K₂`
  have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hΛa : ∀ y, AnalyticAt ℂ (birkLambda m hm ha hp) y := fun y =>
    (birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y (Set.mem_univ _)
  have hZa : ∀ y, AnalyticAt ℂ (birkHamZ m hm ha hp) y := fun y =>
    (birkHamZ_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hcomp : AnalyticAt ℂ (fun w' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 w')) w :=
    (hΛa _).comp hΓa
  have hDcomp : fderiv ℂ (fun w' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 w')) w u =
      fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp 1 w)
        (birkGammaD m hm ha hp 1 w u) := by
    have hR := ((hΛa (birkGamma m hm ha hp 1 w)).differentiableAt.hasFDerivAt.restrictScalars ℝ
      ).comp w (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num) hw40)
    have h3 := (hcomp.differentiableAt.hasFDerivAt.restrictScalars ℝ).unique hR
    have := DFunLike.congr_fun h3 u
    simpa using this
  have hK2 : fderiv ℂ (birkK2 m hm ha hp) w u =
      fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp 1 w) (birkGammaD m hm ha hp 1 w u) -
        fderiv ℂ (birkLambda m hm ha hp) w u - c := by
    unfold birkK2
    rw [fderiv_fun_sub (f := fun y => birkLambda m hm ha hp (birkGamma m hm ha hp 1 y) -
        birkLambda m hm ha hp y) (g := birkHamZ m hm ha hp)
      (hcomp.differentiableAt.sub (hΛa w).differentiableAt) (hZa w).differentiableAt,
      fderiv_fun_sub (f := fun y => birkLambda m hm ha hp (birkGamma m hm ha hp 1 y))
        (g := birkLambda m hm ha hp) hcomp.differentiableAt (hΛa w).differentiableAt]
    simp only [ContinuousLinearMap.sub_apply]
    rw [hDcomp]
  rw [hK2]
  have hg1' : fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp 1 w)
      (birkGammaD m hm ha hp 1 w u) - fderiv ℂ (birkLambda m hm ha hp) w u - ((1 : ℝ) : ℂ) * c -
        Ω (ι (Q 1 - (1 : ℝ) • v 0)) u = 0 := hg1
  rw [hQ1] at hg1'
  simp only [Complex.ofReal_one, one_mul] at hg1'
  show _ = Ω (ι (birkXK2 m hm ha hp w)) u
  linear_combination hg1'

end KAM.Wave

end
