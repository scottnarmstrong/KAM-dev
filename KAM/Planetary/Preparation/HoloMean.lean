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

end Mean

end KAM.Planetary

end
