/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloMeanReal
public import KAM.Planetary.Preparation.HoloMeanAvg
public import KAM.Planetary.Preparation.HoloMeanJets
public import KAM.Planetary.Preparation.HoloData

/-!
# The fast mean `F₀` (P11A-P2e, `stepP:p11:hc-mean`)

For the working function `F = p11hsF D ρ` of `hc-F` (parametric in the data `d : P11HoloData D`
and the strip hypotheses `P11HsHyp`), `p11_hc_mean` proves the mean clause of
`P11SecularSpec`: with `C J := F₀(J, 0)`,
`‖p11FastMean F J z - C J - ∑ Ωᵢ(J) (xᵢ² + yᵢ²)/2‖ ≤ M (‖z‖/rz)⁴`
for all `J` in the complex ball and `‖z‖ < rz`, for some `M ≥ MF`.

Steps: `F₀` is holomorphic (`p11_fastMean_differentiableOn`); on real points `F₀` is the matched
average of `SecularSpectrum.diagonalize` (`p11hsF_real_eq`, `p11_torusAverage_eq_avg`), so the real
remainder is `O(‖z‖⁴)` (`diagonalize` (d)); complex jets vanish (`p11_jets_zero_gen`); finally the
radial Schwarz lemma (`p11_radial_schwarz_diag`).

The realness of `Ω` on real points is the premise `hΩ` (it holds for `Ω = 2π G` with `G` the
complexification of `varpi ∘ natAdd`, `p11_holo_data`, but is not a field of `P11HoloData`).
-/

@[expose] public noncomputable section
open Set Filter Metric Real
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Mean

variable {n : ℕ} {D : P11Physical n}

/-- The remainder function `G(J, z) = F₀(J, z) - F₀(J, 0) - ∑ Ωᵢ(J) (xᵢ² + yᵢ²)/2`. -/
def p11MeanRem (F : P11Phase (n + n) → ℂ) (Ω : P11CVec n → P11CVec n)
    (u : P11CVec n × P11Phase n) : ℂ :=
  p11FastMean F u.1 u.2 - p11FastMean F u.1 0 - ∑ i, Ω u.1 i * (u.2.1 i ^ 2 + u.2.2 i ^ 2) / 2

theorem p11_mean_L_norm (d : P11HoloData D) {J : P11Vec n} (hJ : ‖J - d.J0‖ < 2 * d.rC) :
    ‖(fun i => J i / (2 * π)) - (2 * π)⁻¹ • d.J0‖ < d.rC / π := by
  have h : (fun i => J i / (2 * π)) - (2 * π)⁻¹ • d.J0 = (2 * π)⁻¹ • (J - d.J0) := by
    funext i; simp [div_eq_inv_mul, mul_sub]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hp := Real.pi_pos
  calc (2 * π)⁻¹ * ‖J - d.J0‖ < (2 * π)⁻¹ * (2 * d.rC) := by gcongr
    _ = d.rC / π := by field_simp

theorem p11_mean_L_t2 (d : P11HoloData D) {J : P11Vec n} (hJ : ‖J - d.J0‖ < 2 * d.rC) :
    ‖(fun i => J i / (2 * π)) - (2 * π)⁻¹ • d.J0‖ < d.t2 := by
  refine (p11_mean_L_norm d hJ).trans_le ?_
  have := d.rC_le_t2
  rw [div_le_iff₀ Real.pi_pos]; nlinarith [d.t2_pos, Real.pi_pos]

/-- On real working points the mean is the matched average of `diagonalize`. -/
theorem p11_mean_real_value (D : P11Physical n) (d : P11HoloData D) {a : P11Vec n}
    (ha : a ∈ axes n) {σ rz B B' r' σ' : ℝ}
    (h : P11HsHyp (p11PhysicalData D) a d.rho d.J0 d.rC σ rz B B' r' σ')
    {J : P11Vec n} (hJ : ‖J - d.J0‖ < 2 * d.rC) {x y : P11Vec n} (hxy : ‖(x, y)‖ < rz) :
    p11FastMean (p11hsF (p11PhysicalData D) d.rho) (KAM.realInclusion n J)
        (KAM.realInclusion n x, KAM.realInclusion n y) =
      ((SecularForm.avg (fun t => perturbation (p11PhysicalData D) false
        (SecularSpectrum.liftInv d.R
          (assemble (fun i => J i / (2 * π)) t y x))) : ℝ) : ℂ) := by
  have hn : 0 < n := by have := D.n_ge; omega
  set L : P11Vec n := fun i => J i / (2 * π) with hL
  have hLt2 := p11_mean_L_t2 d hJ
  have hLb : KAM.realInclusion n L ∈
      Metric.ball (KAM.realInclusion n ((2 * π)⁻¹ • d.J0)) d.t2 := by
    rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion]; exact hLt2
  have hLb1 : L ∈ Metric.ball ((2 * π)⁻¹ • d.J0) d.t1 :=
    mem_ball_iff_norm.2 (hLt2.trans_le d.t2_le)
  have hρd : DifferentiableAt ℂ d.rho (KAM.realInclusion n L) :=
    (differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => d.rho_diff i j).differentiableAt
      (Metric.isOpen_ball.mem_nhds hLb)
  have hev : ∀ᶠ y in 𝓝 L, d.rho (KAM.realInclusion n y) = (d.R y).map (fun r : ℝ => (r : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_iff_norm.2 hLt2)] with y hy
    exact d.rho_real y (mem_ball_iff_norm.1 hy)
  have hRd : DifferentiableAt ℝ d.R L :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      (d.R_analytic i j L hLb1).differentiableAt
  unfold p11FastMean
  have hpt : ∀ θ : P11Vec n,
      p11hsF (p11PhysicalData D) d.rho (Fin.append (KAM.realInclusion n θ) (KAM.realInclusion n x),
          Fin.append (KAM.realInclusion n J) (KAM.realInclusion n y)) =
        ((perturbation (p11PhysicalData D) false (SecularSpectrum.liftInv d.R
          (assemble L ((2 * π) • θ) y x)) : ℝ) : ℂ) := by
    intro θ
    set z : Phase (n + n) := (Fin.append θ x, Fin.append J y) with hz
    have hzc : KAM.realInclusion₂ (n + n) z = (Fin.append (KAM.realInclusion n θ)
        (KAM.realInclusion n x), Fin.append (KAM.realInclusion n J) (KAM.realInclusion n y)) := by
      refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [hz]
    have hfast : (fun i => fast z.2 i / (2 * π)) = L := by funext i; simp [hz, fast, hL]
    have hxn : ‖x‖ < rz := lt_of_le_of_lt (le_max_left _ _) hxy
    have hyn : ‖y‖ < rz := lt_of_le_of_lt (le_max_right _ _) hxy
    have hwd : KAM.realInclusion₂ (n + n) z ∈ p11WorkingDom n d.J0 (2 * σ) (2 * d.rC) rz := by
      have e1 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).1 (Fin.castAdd n i)) =
          KAM.realInclusion n θ := by funext i; simp [hz]
      have e2 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.castAdd n i)) =
          KAM.realInclusion n J := by funext i; simp [hz]
      have e3 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).1 (Fin.natAdd n i)) =
          KAM.realInclusion n x := by funext i; simp [hz]
      have e4 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.natAdd n i)) =
          KAM.realInclusion n y := by funext i; simp [hz]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1]; exact KAM.ofReal_mem_complexStrip (by linarith [h.sigma_pos]) θ
      · rw [e2, ← map_sub, KAM.norm_realInclusion]; exact hJ
      · rw [e3, KAM.norm_realInclusion]; exact hxn
      · rw [e4, KAM.norm_realInclusion]; exact hyn
    have := p11hsF_real_eq (R := d.R) hn ha h hwd (by rw [hfast]; exact hρd)
      (by rw [hfast]; exact hev) (by rw [hfast]; exact hRd)
    rw [← hzc, this, hfast]
    have a1 : (fun l => 2 * π * fast z.1 l) = (2 * π) • θ := by
      funext l; simp [hz, fast]
    have a2 : slow z.2 = y := by funext l; simp [hz, slow]
    have a3 : slow z.1 = x := by funext l; simp [hz, slow]
    rw [a1, a2, a3]
  have hint : (fun θ : P11Vec n => p11hsF (p11PhysicalData D) d.rho
      (Fin.append (KAM.realInclusion n θ) (KAM.realInclusion n x),
        Fin.append (KAM.realInclusion n J) (KAM.realInclusion n y))) = fun θ =>
      (((fun t => perturbation (p11PhysicalData D) false (SecularSpectrum.liftInv d.R
          (assemble L t y x))) ((2 * π) • θ) : ℝ) : ℂ) := funext hpt
  rw [hint]
  have h2 := integral_ofReal (𝕜 := ℂ)
    (μ := MeasureTheory.volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1))
    (f := fun θ : P11Vec n => perturbation (p11PhysicalData D) false
      (SecularSpectrum.liftInv d.R (assemble L ((2 * π) • θ) y x)))
  exact h2.trans (congrArg _ (p11_torusAverage_eq_avg
    (fun t => perturbation (p11PhysicalData D) false
      (SecularSpectrum.liftInv d.R (assemble L t y x)))))

/-- `hc-mean`: on real points `Ω` is `2 σ`, the doubled sorted eigenvalue of the secular form. -/
theorem p11_mean_Omega_real (D : P11Physical n) (d : P11HoloData D) {J : P11Vec n}
    (hJ : ‖J - d.J0‖ < 2 * d.rC)
    (hΩ : ∀ i, (d.Omega (KAM.realInclusion n J) i).im = 0) (i : Fin n) :
    d.Omega (KAM.realInclusion n J) i =
      ((2 * SecularSpectrum.sigma (p11PhysicalData D)
        (axis (p11PhysicalData D) ((2 * π)⁻¹ • J)) i : ℝ) : ℂ) := by
  have hmem : KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n d.J0) (2 * d.rC) := by
    rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion]; exact hJ
  obtain ⟨hV, -, hΩre⟩ := d.freq J hmem
  have hLt1 : (2 * π)⁻¹ • J ∈ Metric.ball ((2 * π)⁻¹ • d.J0) d.t1 := by
    rw [mem_ball_iff_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    have h1 := p11_mean_L_t2 d hJ
    have : (fun i => J i / (2 * π)) - (2 * π)⁻¹ • d.J0 = (2 * π)⁻¹ • (J - d.J0) := by
      funext i; simp [div_eq_inv_mul, mul_sub]
    rw [this, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)] at h1
    exact lt_of_lt_of_le h1 d.t2_le
  have hsig := (d.R_frame _ hLt1).2.2.2.2.1
  rw [smul_inv_smul₀ (by positivity : (2 * π : ℝ) ≠ 0)] at hsig
  have hvar := ((p11PatchData_spec D).2.1 J hV)
  have hre := hΩre i
  rw [hvar, Fin.append_right, hsig] at hre
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [hre]; field_simp
  · simp [hΩ i]

/-- `hc-mean`: the real remainder is `O(‖z‖⁴)` (`diagonalize` (d)). -/
theorem p11_mean_real_bound (D : P11Physical n) (d : P11HoloData D) {a : P11Vec n}
    (ha : a ∈ axes n) {σ rz B B' r' σ' : ℝ}
    (h : P11HsHyp (p11PhysicalData D) a d.rho d.J0 d.rC σ rz B B' r' σ')
    (hΩ : ∀ J : P11Vec n, ‖J - d.J0‖ < 2 * d.rC → ∀ i, (d.Omega (KAM.realInclusion n J) i).im = 0)
    {J : P11Vec n} (hJ : ‖J - d.J0‖ < 2 * d.rC) :
    ∃ r0 C0 : ℝ, 0 < r0 ∧ ∀ z' : Phase n, ‖z'‖ < r0 →
      ‖p11MeanRem (p11hsF (p11PhysicalData D) d.rho) d.Omega
        (KAM.realInclusion n J, KAM.realInclusion₂ n z')‖ ≤ C0 * ‖z'‖ ^ 4 := by
  set E := p11PhysicalData D with hE
  set Lam : P11Vec n := (2 * π)⁻¹ • J with hLam
  have hLeq : (fun i => J i / (2 * π)) = Lam := by funext i; simp [hLam, div_eq_inv_mul]
  have hLt1 : Lam ∈ Metric.ball ((2 * π)⁻¹ • d.J0) d.t1 := by
    have h1 := p11_mean_L_t2 d hJ
    rw [hLeq] at h1
    exact mem_ball_iff_norm.2 (h1.trans_le d.t2_le)
  have hRfr := fun L hL => d.R_frame L hL
  have diag := SecularSpectrum.diagonalize E D.n_ge (W := Metric.ball ((2 * π)⁻¹ • d.J0) d.t1)
    Metric.isOpen_ball (fun L hL => (hRfr L hL).2.1) (R := d.R)
    (fun L hL => analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j =>
      d.R_analytic i j L hL)
    (fun L hL => (hRfr L hL).2.2.1) (fun L hL => (hRfr L hL).2.2.2.1)
  obtain ⟨r0, C0, hr0, -, -, hbd⟩ := diag.2.2.2 Lam hLt1
  refine ⟨min r0 rz, C0, lt_min hr0 h.rz_pos, fun z' hz' => ?_⟩
  obtain ⟨x, y⟩ := z'
  have hzr : ‖(x, y)‖ < rz := hz'.trans_le (min_le_right _ _)
  have hzr0 : ‖(x, y)‖ < r0 := hz'.trans_le (min_le_left _ _)
  have hmem : ((x, y) : Phase n) = (x, y) := rfl
  have hV := p11_mean_real_value D d ha h hJ (x := x) (y := y) hzr
  have hV0 := p11_mean_real_value D d ha h hJ (x := 0) (y := 0) (by simpa using h.rz_pos)
  have hb1 := hbd false Lam (mem_ball_self hr0) x y hzr0
  have hb0 := hbd false Lam (mem_ball_self hr0) 0 0 (by simpa using hr0)
  rw [hLeq] at hV hV0
  have h0eq : (0 : P11Phase n) = (KAM.realInclusion n 0, KAM.realInclusion n 0) := by
    simp [Prod.ext_iff]
  have hcast : ∑ i, d.Omega (KAM.realInclusion n J) i *
      (((x i : ℝ) : ℂ) ^ 2 + ((y i : ℝ) : ℂ) ^ 2) / 2 =
      ((∑ j, (2 * SecularSpectrum.sigma E (axis E Lam) j) * oscillatorAction y x j : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [p11_mean_Omega_real D d hJ (hΩ J hJ) i]
    simp only [oscillatorAction]
    push_cast
    ring
  simp only [p11MeanRem, KAM.realInclusion₂_apply, KAM.realInclusion_apply]
  rw [hV, h0eq]
  rw [hV0]
  rw [hcast, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hosc0 : ∀ j, oscillatorAction (0 : P11Vec n) (0 : P11Vec n) j = 0 := fun j => by
    simp [oscillatorAction]
  simp only [hosc0, mul_zero, Finset.sum_const_zero, add_zero, Bool.false_eq_true, ite_false,
    Prod.norm_def, norm_zero, max_self] at hb0
  have hb0' : (SecularForm.avg fun t => perturbation E false
      (SecularSpectrum.liftInv d.R (assemble Lam t 0 0))) = constantTerm E (axis E Lam) := by
    have : |(SecularForm.avg fun t => perturbation E false
        (SecularSpectrum.liftInv d.R (assemble Lam t 0 0))) - constantTerm E (axis E Lam)| ≤ 0 := by
      simpa using hb0
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  rw [hb0']
  simp only [Bool.false_eq_true, ite_false, add_zero] at hb1
  calc _ = |(SecularForm.avg fun t => perturbation E false
          (SecularSpectrum.liftInv d.R (assemble Lam t y x))) -
          (constantTerm E (axis E Lam) + ∑ j, 2 * SecularSpectrum.sigma E (axis E Lam) j *
            oscillatorAction y x j)| := by congr 1; ring
    _ ≤ _ := hb1

end Mean

end KAM.Planetary

end
