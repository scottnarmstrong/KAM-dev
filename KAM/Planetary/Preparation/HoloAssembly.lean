/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloShrink
public import KAM.Planetary.Preparation.HoloChart
public import KAM.Planetary.Preparation.HoloMean

/-!
# Assembly of `holo_chart` (P11A-P2f, `bpP:p11:holo-chart`)

The signed theorem `holo_chart` is assembled from `p11_holo_data` (P2b, shrunk to the strip
radius), `p11hs_F`/`p11hs_strip_data` (P2c), `P11HoloData.chart_spec` (P2d) and `p11_hc_mean` (P2e).
The base axis is `a = axis (J₀/2π)`, so the strip centre is exactly `J₀/2π`.
-/

@[expose] public noncomputable section
open Set Filter Metric Real
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Assembly

variable {n : ℕ}

/-- The patch base point is `δ/8`-close to the physical action, so its axis is ordered. -/
theorem p11_J0_close (D : P11Physical n) {J0 : P11Vec n} (hJ0 : J0 ∈ (p11PatchData D).K) :
    ∀ i, |((2 * π)⁻¹ • J0) i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| <
      p11PhysicalDelta D / 8 := fun i => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hKclose⟩ := p11PatchData_spec D
  have := hKclose J0 hJ0 i
  simpa [div_eq_inv_mul] using this

/-- Real-point identification of `F`: `Re F = f_fix ∘ Ψ⁽ⁿ⁾ ∘ (chart input)` on the real domain. -/
theorem p11_F_real_eq {D : P11Physical n} (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {a : P11Vec n} (ha : a ∈ axes n) {σ rz B B' r' σ' : ℝ}
    (h : P11HsHyp (p11PhysicalData D) a d.rho d.J0 d.rC σ rz B B' r' σ')
    {z : Phase (n + n)} (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) :
    ((p11hsF (p11PhysicalData D) d.rho (KAM.realInclusion₂ (n + n) z)).re) =
      fFix D.G D.m (poincareProd D.m (D.G * D.m0) (p11ChartInput C z)) := by
  have hn : 0 < n := by have := D.n_ge; omega
  have hz' : KAM.realInclusion₂ (n + n) z ∈
      p11WorkingDom n d.J0 (2 * σ) (2 * d.rC) rz := by
    have := p11_preimage_workingDom (J0 := d.J0) (s := 2 * σ) (r := 2 * d.rC) (rz := rz)
      (by linarith [h.sigma_pos])
    have h2 : z ∈ KAM.realInclusion₂ (n + n) ⁻¹' p11WorkingDom n d.J0 (2 * σ) (2 * d.rC) rz := by
      rw [this]; exact hz
    exact h2
  have hfc := d.fast_close hz.1
  have hρ : DifferentiableAt ℂ d.rho (KAM.realInclusion n (fun i => fast z.2 i / (2 * π))) := by
    have hmem : KAM.realInclusion n (fun i => fast z.2 i / (2 * π)) ∈
        Metric.ball ((2 * π)⁻¹ • KAM.realInclusion n d.J0) (d.rC / π) := by
      rw [← map_smul, Metric.mem_ball, dist_eq_norm, ← map_sub, KAM.norm_realInclusion]
      exact hfc.1
    exact d.rho_bounds.1.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hev : ∀ᶠ y in 𝓝 (fun i => fast z.2 i / (2 * π)),
      d.rho (KAM.realInclusion n y) = (d.R y).map (fun r : ℝ => (r : ℂ)) := by
    have : Metric.ball ((2 * π)⁻¹ • d.J0) d.t2 ∈ 𝓝 (fun i => fast z.2 i / (2 * π)) :=
      Metric.isOpen_ball.mem_nhds (by rw [mem_ball_iff_norm]; exact hfc.2.1)
    filter_upwards [this] with y hy
    exact d.rho_real y (by rwa [mem_ball_iff_norm] at hy)
  have hR : DifferentiableAt ℝ d.R (fun i => fast z.2 i / (2 * π)) := by
    have hmem : (fun i => fast z.2 i / (2 * π)) ∈
        Metric.ball ((2 * π)⁻¹ • d.J0) d.t1 := by rw [mem_ball_iff_norm]; exact hfc.2.2
    refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
    exact (d.R_analytic i j _ hmem).differentiableAt
  have := p11hsF_real_eq hn ha h hz' hρ hev hR
  rw [this, Complex.ofReal_re, d.chartInput_eq C hC hz.1, p11FastScale_apply]
  rfl

/-- The signed `holo_chart`: the holomorphic secular package exists for every physical datum. -/
theorem holo_chart {n : ℕ} (D : P11Physical n) :
    ∃ C, P11SecularFullSpec D C := by
  have hn : 0 < n := by have := D.n_ge; omega
  obtain ⟨d0⟩ := p11_holo_data D
  set E := p11PhysicalData D with hE
  have hclose := p11_J0_close D (interior_subset d0.J0_interior)
  have hpos0 := p11_pos_of_close D hclose
  set a : Vec n := axis E ((2 * π)⁻¹ • d0.J0) with ha_def
  have ha : a ∈ axes n := p11_axis_mem_axes D hclose
  have hact : action E a = (2 * π)⁻¹ • d0.J0 := action_axis E hpos0
  obtain ⟨r', σ', hr'0, hr'rho, hσ'0, hσ'1, hσ'2, hstrip⟩ := p11hs_strip_data E ha
  set rC' : ℝ := min d0.rC (π * r' / 2) with hrC'
  have hrC'0 : 0 < rC' := lt_min d0.rC_pos (by positivity)
  set d := d0.shrink rC' hrC'0 (min_le_left _ _) with hd
  have hdrC : d.rC = rC' := rfl
  have hrCr : d.rC / π ≤ r' / 2 := by
    rw [hdrC, div_le_iff₀ Real.pi_pos]
    have := min_le_right d0.rC (π * r' / 2)
    nlinarith [Real.pi_pos]
  have hδ : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  set B : ℝ := d.Brho with hB
  set B' : ℝ := d.Bdrho with hB'
  have hB1 : 1 ≤ B := d.one_le_Brho
  have hB'1 : 1 ≤ B' := d.one_le_Bdrho
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set rz : ℝ := min 1 (min (r' / (2 * B)) (min (π * σ' / (2 * n * B')) (min 1 (p11PhysicalDelta D) / B)))
    with hrz
  have hrz0 : 0 < rz := lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (div_pos (lt_min one_pos hδ) (by positivity))))
  have hrz1 : rz ≤ 1 := min_le_left _ _
  have hrz2 : rz ≤ r' / (2 * B) := (min_le_right _ _).trans (min_le_left _ _)
  have hrz3 : rz ≤ π * σ' / (2 * n * B') :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrz4 : rz ≤ min 1 (p11PhysicalDelta D) / B :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBr : B * rz ≤ r' / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B)).1 hrz2
    linarith
  have hBrδ : B * rz ≤ min 1 (p11PhysicalDelta D) := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < B)).1 hrz4
    linarith
  have hhyp : P11HsHyp E a d.rho d.J0 d.rC (σ' / 4) rz B B' r' σ' := by
    refine ⟨fun i j => ?_, fun J hJ => ⟨(d.rho_bounds.2 J hJ).2.1, (d.rho_bounds.2 J hJ).2.2⟩,
      fun L hL i j => (d.rho_clause L hL).1 i j, by linarith, d.rC_pos, by linarith, hrz0,
      fun L hL i => ?_, by linarith, ?_, le_refl _, hr'rho, hσ'0, hσ'2, hstrip⟩
    · exact (differentiableOn_pi.1 (differentiableOn_pi.1 d.rho_bounds.1 i) j)
    · have hc : (2 * π)⁻¹ • KAM.realInclusion n d.J0 =
          KAM.realInclusion n ((2 * π)⁻¹ • d.J0) := (map_smul _ _ _).symm
      rw [hc] at hL
      have h1 : ‖L - KAM.realInclusion n ((2 * π)⁻¹ • d.J0)‖ < d.rC / π := by
        rw [mem_ball_iff_norm] at hL; exact hL
      have h2 : ‖L i - (action E a i : ℂ)‖ ≤ ‖L - KAM.realInclusion n ((2 * π)⁻¹ • d.J0)‖ := by
        have := norm_le_pi_norm (L - KAM.realInclusion n ((2 * π)⁻¹ • d.J0)) i
        rwa [hact]
      linarith
    · have h2 : rz ^ 2 ≤ rz := by nlinarith
      have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n * B')).1 hrz3
      have h4 : (0 : ℝ) ≤ n * B' := by positivity
      nlinarith
  have hMF1 : 1 ≤ max 1 (max (KAM.Weighted.coth (π * (σ' / 4)) ^ n * p11hsMInf E a)
      (p11MeanM0 D d a rz)) := le_max_left _ _
  set MF := max 1 (max (KAM.Weighted.coth (π * (σ' / 4)) ^ n * p11hsMInf E a)
      (p11MeanM0 D d a rz)) with hMF
  have hMFa : KAM.Weighted.coth (π * (σ' / 4)) ^ n * p11hsMInf E a ≤ MF :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMFb : p11MeanM0 D d a rz ≤ MF := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hFd, hFb, hFs, hFr⟩ := p11hs_F hn ha hhyp hMFa
  have hmean := p11_hc_mean D d ha hhyp (fun J hJ i => d.Omega_real J hJ i) hMFb
  let C1 : P11SecularData n :=
    { J0 := d.J0, gamma := d.gamma, tau := d.tau, rC := d.rC, sigma := σ' / 4, rz := rz,
      MF := MF, L := d.L, Brho := B, Bdrho := B', h := d.h,
      C := fun J => p11FastMean (p11hsF E d.rho) J 0, omega := d.omega, Omega := d.Omega,
      F := p11hsF E d.rho, rho := d.rho,
      chart := fun z => poincareProd D.m (D.G * D.m0) z }
  let C : P11SecularData n :=
    { C1 with chart := fun z => poincareProd D.m (D.G * D.m0) (p11ChartInput C1 z) }
  have hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z) := fun z => rfl
  have hsp := d.chart_spec C rfl rfl rfl rfl (by show 0 < σ' / 4; linarith)
    (by
      show (B * rz) ^ 2 ≤ _
      have h0 : 0 ≤ B * rz := by positivity
      have h1 : B * rz ≤ 1 := hBrδ.trans (min_le_left _ _)
      have h2 : B * rz ≤ p11PhysicalDelta D := hBrδ.trans (min_le_right _ _)
      nlinarith)
    hch (fun z hz => by
      have hz' : z ∈ p11RealDom d.J0 (2 * d.rC) rz := by
        have := p11_preimage_workingDom (J0 := d.J0) (s := 2 * (σ' / 4)) (r := 2 * d.rC)
          (rz := rz) (by linarith)
        have hz2 : z ∈ KAM.realInclusion₂ (n + n) ⁻¹'
            p11WorkingDom n d.J0 (2 * (σ' / 4)) (2 * d.rC) rz := hz
        rw [this] at hz2; exact hz2
      exact p11_F_real_eq d C rfl ha hhyp hz')
  refine ⟨C, ⟨d.freq, d.h_re, ⟨d.omega_diff, d.Omega_diff⟩, d.tau_eq, d.h_diff, d.omega_eq,
    d.jets, d.J0_interior, d.gamma_pos, d.gamma_le, d.dio, d.rC_pos, d.rC_le_one,
    d.rC_le_delta, by show 0 < σ' / 4; linarith, by show σ' / 4 ≤ 1 / 4; linarith, hrz0, hrz1,
    hMF1, d.one_le_L, d.one_le_Brho, d.one_le_Bdrho, hFd, hFb, hFs, hFr, hmean,
    d.rho_clause, d.rho_bounds, hsp⟩, d.euclid_le⟩

end Assembly

end KAM.Planetary

end
