/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.GradIdentity

/-!
# The gradient identity on `ℓ²` (blueprint `bpW:w1:gradient-identity` (i)–(iii))

For `a > 0`, `p ≥ 1/2` and `y ∈ ℓ²_ℝ`, put `q = κ_{a,p} y` and let
`ρ_l = 1/(ω_{a,p+1}(l) ω_{a,p}(l))`,
`D_ρ = waveRhoCLM`. Then `G^w(y) := G(κ_{a,p} y) = ¼ ⟨D_ρ 𝒩(y), y⟩_{ℓ²}`
(`waveG_coeffW_eq_inner`), `G^w` is real analytic on `ℓ²` (`waveG_coeffW_analyticOnNhd`) and its
`ℓ²` gradient is `D_ρ 𝒩(y)`, i.e. `DG^w(y) h = ⟨D_ρ 𝒩(y), h⟩ = Σ_l 𝒢(q)_l (κ_{a,p} h)_l =
⟨𝒢(q), κ_{a,p} h⟩₀` (`waveG_coeffW_hasFDerivAt`, `waveG_coeffW_fderiv_apply`). The frozen form
`a = p = 1` is `waveG_frozen_fderiv_apply`; the gradient sequence is
`𝒢^w(y)_j / (ω_{1,1}(j) ω_{1,2}(j))` (`waveGradW_one_one_apply`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

lemma one_le_ellWeight (ha : 0 ≤ a) (hp : 0 ≤ p) (l : ℕ+) : 1 ≤ ellWeight a p l := by
  unfold ellWeight
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast l.pos
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 hp)
    (Real.one_le_exp (mul_nonneg ha (by positivity)))

/-- The diagonal `ρ_l = 1 / (ω_{a,p+1}(l) ω_{a,p}(l))` of the pairing
`⟨κ_{a,p+1} u, κ_{a,p} v⟩₀`. -/
def waveRho (a p : ℝ) (l : ℕ+) : ℝ := 1 / (ellWeight a (p + 1) l * ellWeight a p l)

lemma waveRho_norm_le_one (ha : 0 ≤ a) (hp : 0 ≤ p) (l : ℕ+) : ‖waveRho a p l‖ ≤ 1 := by
  have h1 := one_le_ellWeight ha hp l
  have h2 := one_le_ellWeight ha (by linarith : 0 ≤ p + 1) l
  have h3 : (0 : ℝ) < ellWeight a (p + 1) l * ellWeight a p l := by positivity
  rw [waveRho, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_le_one h3]
  nlinarith

/-- The multiplier `D_ρ` on `ℓ²_ℝ`. -/
def waveRhoCLM (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  weightedDiagCLM (waveRho a p) (M := 1) (waveRho_norm_le_one ha hp)

@[simp] lemma waveRhoCLM_apply (ha : 0 ≤ a) (hp : 0 ≤ p) (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    waveRhoCLM a p ha hp y l = waveRho a p l * y l := rfl

variable (ha : 0 < a) (hp : 1 / 2 ≤ p)

/-- The `ℓ²` gradient `D_ρ 𝒩(y)` of `G^w`. -/
def waveGradW (y : lp (fun _ : ℕ+ => ℝ) 2) : lp (fun _ : ℕ+ => ℝ) 2 :=
  waveRhoCLM a p ha.le (by linarith) (waveCubicNL (K := ℝ) m hm ha.le hp y)

/-- `G^w(y) = G(κ_{a,p} y)`. -/
def waveGw' (a p : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) : ℝ := waveG m hm (coeffW a p y)

include ha hp in
/-- `bpW:w1:gradient-identity` (i): `G(κ_{a,p} y) = ¼ ⟨D_ρ 𝒩(y), y⟩_{ℓ²}`. -/
theorem waveG_coeffW_eq_inner (y : lp (fun _ : ℕ+ => ℝ) 2) :
    waveG m hm (coeffW a p y) = (1 / 4) * inner ℝ (waveGradW m hm ha hp y) y := by
  have hc : WaveEll a p (coeffW a p y) := (waveEll_iff_isEll a p _).2 (isEll_coeffW a p y)
  have h := waveG_hasSum_pairing m hm ha hc
  have hN := waveCubic_coeffW_eq_coeffW_triML m hm (a := a) (p := p) hp ha y
  have hinner : inner ℝ (waveGradW m hm ha hp y) y =
      ∑' l : ℕ+, (coeffW a p y l * waveCubic m hm (coeffW a p y) l) := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun l => ?_
    have hw1 := ellWeight_pos a p l
    have hw2 := ellWeight_pos a (p + 1) l
    have hl : waveCubic m hm (coeffW a p y) l = waveCubicNL (K := ℝ) m hm ha.le hp y l /
        ellWeight a (p + 1) l := by
      rw [hN, waveCubicNL_eq]; simp [coeffW]
    simp only [waveGradW, waveRhoCLM_apply, waveRho, hl, coeffW_apply, RCLike.inner_apply,
      RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id]
    field_simp
  have h4 : HasSum (fun l : ℕ+ => coeffW a p y l * waveCubic m hm (coeffW a p y) l)
      (4 * waveG m hm (coeffW a p y)) := by
    convert h.mul_left 4 using 1
    funext l; ring
  rw [hinner, h4.tsum_eq]
  ring

include ha hp in
/-- `bpW:w1:gradient-identity` (ii): `G^w = G ∘ κ_{a,p}` is real analytic on all of `ℓ²_ℝ`. -/
theorem waveG_coeffW_analyticOnNhd :
    AnalyticOnNhd ℝ (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeffW a p y)) Set.univ := by
  have hF : (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeffW a p y)) =
      fun y => (1 / 4 : ℝ) * inner ℝ (waveGradW m hm ha hp y) y :=
    funext (waveG_coeffW_eq_inner m hm ha hp)
  rw [hF]
  intro y _
  have hN : AnalyticAt ℝ (fun y => waveGradW m hm ha hp y) y :=
    ((waveRhoCLM a p ha.le (by linarith)).analyticAt _).comp
      (waveCubicNL_analyticOnNhd m hm ha.le hp y trivial)
  have hid : AnalyticAt ℝ (fun y : lp (fun _ : ℕ+ => ℝ) 2 => y) y := analyticAt_id
  have hb : AnalyticAt ℝ (fun x : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2 =>
      innerSL ℝ x.1 x.2) (waveGradW m hm ha hp y, y) :=
    (innerSL ℝ : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ).analyticAt_bilinear _
  have hc := AnalyticAt.comp (f := fun x : lp (fun _ : ℕ+ => ℝ) 2 => (waveGradW m hm ha hp x, x))
    (x := y) hb (hN.prod hid)
  refine analyticAt_const.mul ?_
  simpa [Function.comp_def] using hc

lemma waveCoeffW_add_single (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) (t : ℝ) :
    coeffW a p (y + t • lp.single 2 l (1 : ℝ)) =
      waveCoordShift l (t / ellWeight a p l) (coeffW a p y) := by
  funext j
  have hw := ellWeight_pos a p j
  by_cases hj : j = l
  · subst hj
    simp only [coeffW_apply, waveCoordShift, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, lp.single_apply_self, smul_eq_mul, if_true, RCLike.ofReal_real_eq_id, id]
    field_simp
  · have h0 : (lp.single (E := fun _ : ℕ+ => ℝ) 2 l (1 : ℝ)) j = 0 := lp.single_apply_ne 2 l 1 hj
    simp only [coeffW_apply, waveCoordShift, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, h0, hj, smul_zero, add_zero, if_false, mul_zero, RCLike.ofReal_real_eq_id, id]

include ha hp in
/-- The directional derivative of `G^w` along the basis vector `δ_l` is `𝒢(q)_l / ω_{a,p}(l)`. -/
lemma waveG_coeffW_hasDerivAt_single (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    HasDerivAt (fun t : ℝ => waveG m hm (coeffW a p (y + t • lp.single 2 l (1 : ℝ))))
      (inner ℝ (waveGradW m hm ha hp y) (lp.single 2 l (1 : ℝ))) 0 := by
  have hc : WaveEll a p (coeffW a p y) := (waveEll_iff_isEll a p _).2 (isEll_coeffW a p y)
  have hd := hasDerivAt_waveG_coord (m := m) hm ha hc l
  have hw := ellWeight_pos a p l
  have hlin : HasDerivAt (fun t : ℝ => t / ellWeight a p l) (1 / ellWeight a p l) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (ellWeight a p l)
  have hd' : HasDerivAt (fun s : ℝ => waveG m hm (waveCoordShift l s (coeffW a p y)))
      (waveCubic m hm (coeffW a p y) l) ((fun t : ℝ => t / ellWeight a p l) 0) := by
    simpa using hd
  have hcomp := hd'.scomp (0 : ℝ) hlin
  simp only [waveCoeffW_add_single]
  refine HasDerivAt.congr_deriv hcomp ?_
  have hN := waveCubic_coeffW_eq_coeffW_triML m hm (a := a) (p := p) hp ha y
  have hw2 := ellWeight_pos a (p + 1) l
  have hl : waveCubic m hm (coeffW a p y) l = waveCubicNL (K := ℝ) m hm ha.le hp y l /
      ellWeight a (p + 1) l := by
    rw [hN, waveCubicNL_eq]; simp [coeffW]
  rw [lp.inner_single_right]
  simp only [waveGradW, waveRhoCLM_apply, waveRho, hl, smul_eq_mul, RCLike.inner_apply,
    RCLike.conj_to_real]
  field_simp

include ha hp in
/-- `bpW:w1:gradient-identity` (ii)/(iii): the Fréchet derivative of `G^w` at `y` is
`h ↦ ⟨D_ρ 𝒩(y), h⟩_{ℓ²}`, i.e. the `ℓ²` gradient of `G^w` is `D_ρ 𝒩(y)`. -/
theorem waveG_coeffW_hasFDerivAt (y : lp (fun _ : ℕ+ => ℝ) 2) :
    HasFDerivAt (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeffW a p y))
      (innerSL ℝ (waveGradW m hm ha hp y)) y := by
  set F : lp (fun _ : ℕ+ => ℝ) 2 → ℝ := fun y => waveG m hm (coeffW a p y) with hF
  have hFd : HasFDerivAt F (fderiv ℝ F y) y :=
    ((waveG_coeffW_analyticOnNhd m hm ha hp y trivial).differentiableAt).hasFDerivAt
  suffices hL : fderiv ℝ F y = innerSL ℝ (waveGradW m hm ha hp y) by rwa [hL] at hFd
  have key : ∀ l : ℕ+, fderiv ℝ F y (lp.single 2 l (1 : ℝ)) =
      inner ℝ (waveGradW m hm ha hp y) (lp.single 2 l (1 : ℝ)) := by
    intro l
    have hline : HasDerivAt (fun t : ℝ => y + t • lp.single 2 l (1 : ℝ))
        (lp.single 2 l (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (lp.single 2 l (1 : ℝ))).const_add y
    have hFd0 : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • lp.single 2 l (1 : ℝ)) := by
      simpa using hFd
    have h1 := hFd0.comp_hasDerivAt (0 : ℝ) hline
    exact h1.unique (waveG_coeffW_hasDerivAt_single m hm ha hp y l)
  refine ContinuousLinearMap.ext fun h => ?_
  have hs := lp.hasSum_single (E := fun _ : ℕ+ => ℝ) (p := 2) (by simp) h
  have h1 := hs.mapL (fderiv ℝ F y)
  have h2 := hs.mapL (innerSL ℝ (waveGradW m hm ha hp y))
  refine h1.unique ?_
  convert h2 using 1
  funext l
  have e : lp.single (E := fun _ : ℕ+ => ℝ) 2 l (h l) =
      h l • lp.single (E := fun _ : ℕ+ => ℝ) 2 l (1 : ℝ) := by
    rw [← lp.single_smul]; simp
  rw [e, map_smul, map_smul, key]
  simp [innerSL_apply_apply]

include ha hp in
/-- `bpW:w1:gradient-identity` (ii): `DG^w(y) h = Σ_l 𝒢(q)_l (κ_{a,p} h)_l = ⟨𝒢(q), κ_{a,p} h⟩₀`,
`q = κ_{a,p} y`. -/
theorem waveG_coeffW_fderiv_apply (y h : lp (fun _ : ℕ+ => ℝ) 2) :
    fderiv ℝ (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeffW a p y)) y h =
      ∑' l : ℕ+, waveCubic m hm (coeffW a p y) l * coeffW a p h l := by
  rw [(waveG_coeffW_hasFDerivAt m hm ha hp y).fderiv, innerSL_apply_apply, lp.inner_eq_tsum]
  refine tsum_congr fun l => ?_
  have hN := waveCubic_coeffW_eq_coeffW_triML m hm (a := a) (p := p) hp ha y
  have hw1 := ellWeight_pos a p l
  have hw2 := ellWeight_pos a (p + 1) l
  have hl : waveCubic m hm (coeffW a p y) l = waveCubicNL (K := ℝ) m hm ha.le hp y l /
      ellWeight a (p + 1) l := by
    rw [hN, waveCubicNL_eq]; simp [coeffW]
  simp only [waveGradW, waveRhoCLM_apply, waveRho, hl, coeffW_apply, RCLike.inner_apply,
    RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id]
  field_simp

/-- The `ℓ²` gradient in the frozen coordinates: `(𝒢^w(y)_j / (ω_{1,1}(j) ω_{1,2}(j)))_j`. -/
theorem waveGradW_one_one_apply (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    waveGradW m hm (a := 1) (p := 1) one_pos (by norm_num) y j =
      waveGw m hm y j / (ellWeight 1 1 j * ellWeight 1 2 j) := by
  have e : (1 : ℝ) + 1 = 2 := by norm_num
  have h1 := ellWeight_pos 1 1 j
  have h2 := ellWeight_pos 1 2 j
  simp only [waveGradW, waveRhoCLM_apply, waveRho, e]
  rw [show waveCubicNL (K := ℝ) m hm (zero_le_one) (by norm_num : (1 / 2 : ℝ) ≤ 1) y j =
    waveGw m hm y j from rfl]
  field_simp

/-- `bpW:w1:gradient-identity` (iii), frozen form: `DG^w(y) h = Σ_j cubicGrad y j · coeff h j`. -/
theorem waveG_frozen_fderiv_apply (y h : lp (fun _ : ℕ+ => ℝ) 2) :
    fderiv ℝ (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeff y)) y h =
      ∑' j : ℕ+, cubicGrad m hm y j * coeff h j := by
  have e : (fun y : lp (fun _ : ℕ+ => ℝ) 2 => waveG m hm (coeff y)) =
      fun y => waveG m hm (coeffW 1 1 y) := by
    funext y; rw [coeffW_one_one]
  rw [e, waveG_coeffW_fderiv_apply m hm (a := 1) (p := 1) one_pos (by norm_num)]
  refine tsum_congr fun j => ?_
  rw [coeffW_one_one, coeffW_one_one, cubicGrad_eq_waveCubic]

end KAM.Wave

end
