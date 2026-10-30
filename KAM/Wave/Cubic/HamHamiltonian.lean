/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.HamField
public import KAM.Wave.Cubic.GradLp

/-!
# Hamiltonian structure (blueprint `bpW:w1:hamfield` (iv))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

For `a > 0`, `p ≥ 1/2` and the weighted coordinates `z = (y, y')` of `(q, p) = (κ_{a,p} y,
κ_{a,p} y')`, `KAM.Wave.waveHw z = Λ(q,p) + G(q)` with
`Λ = ½ (⟨λ q, q⟩₀ + ⟨λ p, p⟩₀)` (`KAM.Wave.waveLamQuad`) is real analytic on `ℓ² × ℓ²`
(`waveHw_analyticOnNhd`), with derivative `v ↦ ⟨S y, v₁⟩ + ⟨S y', v₂⟩ + ⟨D_ρ 𝒩(y), v₁⟩`
(`waveHw_hasFDerivAt`), whence
`DH(q,p)(0, e_j) = λ_j p_j` (`waveHw_fderiv_p`) and `DH(q,p)(e_j, 0) = λ_j q_j + 𝒢(q)_j`
(`waveHw_fderiv_q`), the coordinate vector `e_j` being `ω_{a,p}(j) δ_j` in weighted coordinates.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- The diagonal `σ_j = λ_j / ω_{a,p}(j)²` of the quadratic form `⟨λ q, q⟩₀` in weighted
coordinates. -/
def waveSigma (a p : ℝ) (j : ℕ+) : ℝ := lam m hm j / ellWeight a p j ^ 2

lemma waveSigma_norm_le {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (j : ℕ+) :
    ‖waveSigma m hm a p j‖ ≤ Real.sqrt (1 + m) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hw : (j : ℝ) ≤ ellWeight a p j ^ 2 := by
    unfold ellWeight
    rw [mul_pow, ← Real.rpow_natCast ((j : ℝ) ^ p) 2, ← Real.rpow_mul (by positivity)]
    have h1 : (j : ℝ) ≤ (j : ℝ) ^ (p * ((2 : ℕ) : ℝ)) := by
      calc (j : ℝ) = (j : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hj (by push_cast; linarith)
    have h2 : (1 : ℝ) ≤ Real.exp (a * j) ^ 2 :=
      one_le_pow₀ (Real.one_le_exp (mul_nonneg ha (by positivity)))
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ j) (p * ((2 : ℕ) : ℝ))]
  have hl := lam_le_sqrt_mul hm j
  have hlp : 0 < lam m hm j := lt_of_lt_of_le (by positivity) (pnat_le_lam hm j)
  have hw2 : 0 < ellWeight a p j ^ 2 := pow_pos (ellWeight_pos a p j) 2
  rw [waveSigma, Real.norm_eq_abs, abs_of_pos (div_pos hlp hw2), div_le_iff₀ hw2]
  calc lam m hm j ≤ Real.sqrt (1 + m) * j := hl
    _ ≤ Real.sqrt (1 + m) * ellWeight a p j ^ 2 := by gcongr

/-- The multiplier `S_σ` of the quadratic form `Λ`. -/
def waveSigmaCLM {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) :
    lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  weightedDiagCLM (waveSigma m hm a p) (waveSigma_norm_le m hm ha hp)

@[simp] lemma waveSigmaCLM_apply {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    waveSigmaCLM m hm ha hp y j = waveSigma m hm a p j * y j := rfl

lemma waveSigmaCLM_selfAdjoint {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    (y h : lp (fun _ : ℕ+ => ℝ) 2) :
    inner ℝ (waveSigmaCLM m hm ha hp h) y = inner ℝ h (waveSigmaCLM m hm ha hp y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  simp only [waveSigmaCLM_apply, RCLike.inner_apply, RCLike.conj_to_real]
  ring

/-- `Λ(q,p) = ½ (⟨λ q, q⟩₀ + ⟨λ p, p⟩₀)` in weighted coordinates. -/
def waveLamQuad {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) : ℝ :=
  (1 / 2) * (inner ℝ (waveSigmaCLM m hm ha hp z.1) z.1 + inner ℝ (waveSigmaCLM m hm ha hp z.2) z.2)

/-- `H(q,p) = Λ(q,p) + G(q)` in weighted coordinates. -/
def waveHw {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) : ℝ :=
  waveLamQuad m hm ha hp z + waveG m hm (coeffW a p z.1)

lemma hasFDerivAt_inner_sigma {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    HasFDerivAt (fun y : lp (fun _ : ℕ+ => ℝ) 2 => inner ℝ (waveSigmaCLM m hm ha hp y) y)
      ((2 : ℝ) • innerSL ℝ (waveSigmaCLM m hm ha hp y)) y := by
  have h1 := ((waveSigmaCLM m hm ha hp).hasFDerivAt (x := y)).inner ℝ
    (ContinuousLinearMap.id ℝ (lp (fun _ : ℕ+ => ℝ) 2)).hasFDerivAt
  refine h1.congr_fderiv ?_
  ext h : 1
  simp only [smul_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  rw [waveSigmaCLM_selfAdjoint m hm ha hp y h, real_inner_comm]
  ring

/-- `bpW:w1:hamfield` (iv): `H` is real analytic on all of `ℓ² × ℓ²`. -/
theorem waveHw_analyticOnNhd {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p) :
    AnalyticOnNhd ℝ (waveHw m hm ha.le hp) Set.univ := by
  intro z _
  have hfst : AnalyticAt ℝ (fun z : WaveSpaceK ℝ => z.1) z :=
    (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt z
  have hsnd : AnalyticAt ℝ (fun z : WaveSpaceK ℝ => z.2) z :=
    (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt z
  have hq : ∀ w : WaveSpaceK ℝ → lp (fun _ : ℕ+ => ℝ) 2, AnalyticAt ℝ w z →
      AnalyticAt ℝ (fun z => inner ℝ (waveSigmaCLM m hm ha.le hp (w z)) (w z)) z := by
    intro w hw
    have hb : AnalyticAt ℝ (fun x : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2 =>
        innerSL ℝ x.1 x.2) (waveSigmaCLM m hm ha.le hp (w z), w z) :=
      (innerSL ℝ : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ).analyticAt_bilinear _
    have hc := AnalyticAt.comp (f := fun x => (waveSigmaCLM m hm ha.le hp (w x), w x)) (x := z) hb
      (((waveSigmaCLM m hm ha.le hp).analyticAt _).comp hw |>.prod hw)
    simpa [Function.comp_def] using hc
  have hG : AnalyticAt ℝ (fun z : WaveSpaceK ℝ => waveG m hm (coeffW _ _ z.1)) z :=
    (waveG_coeffW_analyticOnNhd m hm ha hp z.1 trivial).comp hfst
  exact (analyticAt_const.mul ((hq _ hfst).add (hq _ hsnd))).add hG

/-- The derivative of `H` in weighted coordinates:
`v ↦ ⟨S y, v₁⟩ + ⟨S y', v₂⟩ + ⟨D_ρ 𝒩(y), v₁⟩`. -/
def waveHwDeriv {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) :
    WaveSpaceK ℝ →L[ℝ] ℝ :=
  (innerSL ℝ (waveSigmaCLM m hm ha.le hp z.1)).comp
      (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)) +
    (innerSL ℝ (waveSigmaCLM m hm ha.le hp z.2)).comp
      (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)) +
    (innerSL ℝ (waveGradW m hm ha hp z.1)).comp
      (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2))

/-- `bpW:w1:hamfield` (iv): the Fréchet derivative of `H`. -/
theorem waveHw_hasFDerivAt {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) :
    HasFDerivAt (waveHw m hm ha.le hp) (waveHwDeriv m hm ha hp z) z := by
  have hf := (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).hasFDerivAt (x := z)
  have hs := (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).hasFDerivAt (x := z)
  have hq1 := (hasFDerivAt_inner_sigma m hm ha.le hp z.1).comp z hf
  have hq2 := (hasFDerivAt_inner_sigma m hm ha.le hp z.2).comp z hs
  have hG := (waveG_coeffW_hasFDerivAt m hm ha hp z.1).comp z hf
  have h := (((hq1.add hq2).const_mul (1 / 2 : ℝ)).add hG)
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [waveHwDeriv, smul_apply, ContinuousLinearMap.comp_apply, add_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

lemma wave_inner_single_right (f : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) (c : ℝ) :
    inner ℝ f (c • lp.single (E := fun _ : ℕ+ => ℝ) 2 j (1 : ℝ)) = f j * c := by
  rw [← lp.single_smul, lp.inner_single_right]
  simp [RCLike.inner_apply, mul_comm]

/-- `bpW:w1:hamfield` (iv): `DH(q,p)(0, e_j) = λ_j p_j` (`e_j = ω_{a,p}(j) δ_j` in weighted
coordinates, `p = κ_{a,p} z.2`). -/
theorem waveHw_fderiv_p {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) (j : ℕ+) :
    fderiv ℝ (waveHw m hm ha.le hp) z
        (0, ellWeight a p j • lp.single (E := fun _ : ℕ+ => ℝ) 2 j (1 : ℝ)) =
      lam m hm j * coeffW a p z.2 j := by
  rw [(waveHw_hasFDerivAt m hm ha hp z).fderiv]
  simp only [waveHwDeriv, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', inner_zero_right,
    add_zero, zero_add, wave_inner_single_right, waveSigmaCLM_apply]
  have hw := ellWeight_pos a p j
  simp only [waveSigma, coeffW_apply, RCLike.ofReal_real_eq_id, id]
  field_simp

/-- `bpW:w1:hamfield` (iv): `DH(q,p)(e_j, 0) = λ_j q_j + 𝒢(q)_j` (`q = κ_{a,p} z.1`). -/
theorem waveHw_fderiv_q {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) (j : ℕ+) :
    fderiv ℝ (waveHw m hm ha.le hp) z
        (ellWeight a p j • lp.single (E := fun _ : ℕ+ => ℝ) 2 j (1 : ℝ), 0) =
      lam m hm j * coeffW a p z.1 j + waveCubic m hm (coeffW a p z.1) j := by
  rw [(waveHw_hasFDerivAt m hm ha hp z).fderiv]
  have hN := waveCubic_coeffW_eq_coeffW_triML m hm (a := a) (p := p) hp ha z.1
  have hw1 := ellWeight_pos a p j
  have hw2 := ellWeight_pos a (p + 1) j
  have hl : waveCubic m hm (coeffW a p z.1) j = waveCubicNL (K := ℝ) m hm ha.le hp z.1 j /
      ellWeight a (p + 1) j := by
    rw [hN, waveCubicNL_eq]; simp [coeffW]
  simp only [waveHwDeriv, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', inner_zero_right,
    add_zero, wave_inner_single_right, waveSigmaCLM_apply, waveGradW, waveRhoCLM_apply, waveRho, hl]
  simp only [waveSigma, coeffW_apply, RCLike.ofReal_real_eq_id, id]
  field_simp

end KAM.Wave

end
