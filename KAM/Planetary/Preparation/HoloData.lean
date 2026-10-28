/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.Preparation.BasePoint
public import KAM.Planetary.Preparation.HoloFrame
public import KAM.Planetary.Preparation.HoloScalar

/-!
# The single data interface of `holo_chart` (P11A-P2b, `stepP:p11:hc-rot`)

`P11HoloData D` packages everything of `P11SecularSpec` that does not involve the periodic
perturbation `F`, the chart and the mean: the base point `(γ, J₀)` of `select`, the radius `r_C`,
the holomorphic energy `h` with its frequency `ω̃ = ∇h` and the secular frequency `Ω̃`, the
constant `L`, the holomorphic rotation `ρ` with its constants `B_ρ`, `B'_ρ`, and the real analytic
frame `R` it extends. `p11_holo_data` is the existence theorem; the later packages P2c–P2f read
only this structure.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Data

variable {n : ℕ}

/-- The data of `hc-rot` and the scalar clauses of `P11SecularSpec`, chosen from `select`,
`p11PatchData_spec` and `local_analytic`. The Prop fields are the corresponding conjuncts of
`P11SecularSpec`/`P11SecularFullSpec` verbatim (with the data fields in place of `C.`). -/
structure P11HoloData (D : P11Physical n) where
  J0 : P11Vec n
  gamma : ℝ
  tau : ℝ
  rC : ℝ
  L : ℝ
  Brho : ℝ
  Bdrho : ℝ
  h : P11CVec n → ℂ
  omega : P11CVec n → P11CVec n
  Omega : P11CVec n → P11CVec n
  rho : P11CVec n → Matrix (Fin n) (Fin n) ℂ
  /-- the real analytic frame, with its real-analyticity radius `t1` -/
  R : P11Vec n → Matrix (Fin n) (Fin n) ℝ
  t1 : ℝ
  /-- the complex radius of `ρ`, `t2 ≤ t1` -/
  t2 : ℝ
  t2_pos : 0 < t2
  t2_le : t2 ≤ t1
  -- the frame (`hc-rot`, real part)
  R_analytic : ∀ i j,
    AnalyticOnNhd ℝ (fun x => R x i j) (Metric.ball ((2 * Real.pi)⁻¹ • J0) t1)
  R_frame : ∀ L ∈ Metric.ball ((2 * Real.pi)⁻¹ • J0) t1,
    (2 * Real.pi) • L ∈ (p11PatchData D).V ∧ L ∈ SecularForm.actionDomain (p11PhysicalData D) ∧
    SecularSpectrum.isSO (R L) ∧
    SecularForm.coeffs (p11PhysicalData D) (SecularForm.axis (p11PhysicalData D) L) =
      R L * Matrix.diagonal (SecularSpectrum.sigma (p11PhysicalData D)
        (SecularForm.axis (p11PhysicalData D) L)) * (R L).transpose ∧
    (p11PatchData D).sigma ((2 * Real.pi) • L) =
      SecularSpectrum.sigma (p11PhysicalData D) (SecularForm.axis (p11PhysicalData D) L) ∧
    (R L).transpose * p11SecularMatrix D L * R L =
      Matrix.diagonal ((p11PatchData D).sigma ((2 * Real.pi) • L))
  -- the holomorphic extension `ρ` (`hc-rot`, complex part)
  rho_diff : ∀ i j, DifferentiableOn ℂ (fun z => rho z i j)
    (Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • J0)) t2)
  rho_real : ∀ y : P11Vec n, ‖y - (2 * Real.pi)⁻¹ • J0‖ < t2 →
    rho (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ))
  rho_orth_t2 : ∀ z ∈ Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • J0)) t2,
    (rho z).transpose * rho z = 1
  -- radii
  rC_le_t2 : rC ≤ Real.pi * t2 / 2
  nonvanishing : Metric.ball (KAM.realInclusion n J0) (2 * rC) ⊆ p11NonVanishing n
  -- the clauses of `P11SecularSpec`
  freq : ∀ J : P11Vec n, KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n J0) (2 * rC) →
    J ∈ (p11PatchData D).V ∧
    (∀ i : Fin n,
      (omega (KAM.realInclusion n J) i).re = (p11PatchData D).varpi J (Fin.castAdd n i)) ∧
    (∀ i : Fin n, (Omega (KAM.realInclusion n J) i).re =
      2 * Real.pi * (p11PatchData D).varpi J (Fin.natAdd n i))
  h_re : ∀ J : P11Vec n, ‖J - J0‖ < 2 * rC →
    (h (KAM.realInclusion n J)).re =
      -∑ i, (D.G * D.m0) ^ 2 * D.m i ^ 3 / (2 * (J i / (2 * Real.pi)) ^ 2)
  /-- typing datum: `Ω̃` is real on real points (used only by the mean clause) -/
  Omega_real : ∀ J : P11Vec n, ‖J - J0‖ < 2 * rC → ∀ i, (Omega (KAM.realInclusion n J) i).im = 0
  omega_diff : DifferentiableOn ℂ omega (Metric.ball (KAM.realInclusion n J0) (2 * rC))
  Omega_diff : DifferentiableOn ℂ Omega (Metric.ball (KAM.realInclusion n J0) (2 * rC))
  tau_eq : tau = max ((n : ℝ) * (p11PatchData D).mu) (2 * n)
  h_diff : DifferentiableOn ℂ h (Metric.ball (KAM.realInclusion n J0) (2 * rC))
  omega_eq : ∀ J ∈ Metric.ball (KAM.realInclusion n J0) (2 * rC),
    omega J = fun i => fderiv ℂ h J (Pi.single i 1)
  jets : ∀ J ∈ Metric.ball (KAM.realInclusion n J0) (2 * rC), ∀ j ≤ (p11PatchData D).mu + 1,
    ‖iteratedFDeriv ℂ j
      (fun J => Fin.append (omega J) ((2 * Real.pi : ℂ)⁻¹ • Omega J)) J‖ ≤ L
  euclid_le : ∀ J ∈ Metric.ball (KAM.realInclusion n J0) (2 * rC),
    KAM.Nekhoroshev.euclid (Fin.append (omega J) ((2 * Real.pi : ℂ)⁻¹ • Omega J)) ≤ L
  J0_interior : J0 ∈ interior (p11PatchData D).K
  gamma_pos : 0 < gamma
  gamma_le : gamma ≤ 1
  dio : KAM.IsDiophantine gamma tau ((p11PatchData D).varpi J0)
  dio_fast : KAM.IsDiophantine gamma tau (fast (a := n) (b := n) ((p11PatchData D).varpi J0))
  dio_slow : KAM.IsDiophantine gamma tau (slow (a := n) (b := n) ((p11PatchData D).varpi J0))
  rC_pos : 0 < rC
  rC_le_one : rC ≤ 1
  rC_le_delta : rC ≤ Real.pi * p11PhysicalDelta D / 8
  one_le_L : 1 ≤ L
  one_le_Brho : 1 ≤ Brho
  one_le_Bdrho : 1 ≤ Bdrho
  rho_clause : ∀ L : P11Vec n, ‖L - (2 * Real.pi)⁻¹ • J0‖ < rC / Real.pi →
    (∀ i j, (rho (KAM.realInclusion n L) i j).im = 0) ∧
    (rho (KAM.realInclusion n L)).det = 1 ∧
    (let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (rho (KAM.realInclusion n L) i j).re
     R.transpose * p11SecularMatrix D L * R =
       Matrix.diagonal ((p11PatchData D).sigma ((2 * Real.pi) • L)))
  rho_bounds : DifferentiableOn ℂ rho
    (Metric.ball ((2 * Real.pi)⁻¹ • KAM.realInclusion n J0) (rC / Real.pi)) ∧
    ∀ J ∈ Metric.ball ((2 * Real.pi)⁻¹ • KAM.realInclusion n J0) (rC / Real.pi),
      (rho J).transpose * rho J = 1 ∧
      (∀ i, (∑ j, ‖rho J i j‖) ≤ Brho) ∧
      (∀ l : Fin n, ∀ i,
        (∑ j, ‖((rho J).transpose * fderiv ℂ rho J (Pi.single l 1)) i j‖) ≤ Bdrho)

theorem differentiableOn_p11_append {m k : ℕ} {U : Set (P11CVec n)} {f : P11CVec n → P11CVec m}
    {g : P11CVec n → P11CVec k} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun J => (Fin.append (f J) (g J) : Fin (m + k) → ℂ)) U := by
  refine differentiableOn_pi.2 fun r => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r
  · simpa [Fin.append_left] using differentiableOn_pi.1 hf i
  · simpa [Fin.append_right] using differentiableOn_pi.1 hg i

/-- `hc-rot`, data: existence of the single interface used by the later packages. -/
theorem p11_holo_data (D : P11Physical n) : Nonempty (P11HoloData D) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hsel := select D
  dsimp only at hsel
  obtain ⟨gamma, hg0, hg1, J0, hJ0int, hd, hdf, hds⟩ := hsel
  have hJ0K : J0 ∈ (p11PatchData D).K := interior_subset hJ0int
  obtain ⟨-, hVar, hVo, -, -, -, hKV, -, -, -, -, hAn, -, -, hKclose⟩ := p11PatchData_spec D
  have hJ0V : J0 ∈ (p11PatchData D).V := hKV hJ0K
  have hclose : ∀ i, |((2 * Real.pi)⁻¹ • J0) i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| <
      p11PhysicalDelta D / 8 := fun i => by
    have := hKclose J0 hJ0K i
    simpa [div_eq_inv_mul] using this
  have hJ0pos : ∀ i, 0 < J0 i := fun i => by
    have h := p11_pos_of_close D hclose i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have h2 : 0 < 2 * Real.pi := by positivity
    exact (mul_pos_iff_of_pos_left (inv_pos.2 h2)).1 h
  obtain ⟨t1, ht1, R, hRan, hRfr⟩ := p11_holo_frame D hJ0K
  obtain ⟨t2, ht2, ht21, ρ, hρent, hρdiff, hρreal, hρorth⟩ :=
    p11_rotation_complex ht1 hRan (fun x hx => (hRfr x hx).2.2.1.1)
  obtain ⟨B, B', hB1, hB1', hBb⟩ := p11_rotation_bounds (r := t2 / 2) (by linarith) hρent
  obtain ⟨rV, hrV, hrVsub⟩ := Metric.isOpen_iff.1 hVo J0 hJ0V
  have hfan : AnalyticAt ℝ (fun J : P11Vec n => fun i : Fin n =>
      (p11PatchData D).varpi J (Fin.natAdd n i)) J0 :=
    analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.1 (hAn J0 hJ0V) (Fin.natAdd n i)
  obtain ⟨rΩ, hrΩ, G, hGd, hGeq⟩ := p11_complexification hfan
  obtain ⟨rnv, hrnv, hnvsub⟩ := exists_ball_nonvanishing hJ0pos
  have hδ : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  set r0 : ℝ := min rΩ rnv with hr0
  have hr0pos : 0 < r0 := lt_min hrΩ hrnv
  set rC : ℝ := min (min 1 (Real.pi * p11PhysicalDelta D / 8))
    (min (Real.pi * t2 / 2) (min (r0 / 4) (rV / 2))) with hrC
  have hrC0 : 0 < rC := lt_min (lt_min one_pos (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hrC1 : rC ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hrCδ : rC ≤ Real.pi * p11PhysicalDelta D / 8 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hrCt2 : rC ≤ Real.pi * t2 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC0' : rC ≤ r0 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrCV : rC ≤ rV / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h2rC : 2 * rC < r0 := by linarith
  have hr0Ω : r0 ≤ rΩ := min_le_left _ _
  have hr0nv : r0 ≤ rnv := min_le_right _ _
  have hnv : Metric.ball (KAM.realInclusion n J0) (2 * rC) ⊆ p11NonVanishing n :=
    ((Metric.ball_subset_ball h2rC.le).trans (Metric.ball_subset_ball hr0nv)).trans hnvsub
  have hGd' : DifferentiableOn ℂ G (Metric.ball (KAM.realInclusion n J0) r0) :=
    hGd.mono (Metric.ball_subset_ball hr0Ω)
  have hFd : DifferentiableOn ℂ (p11HoloFreq D) (Metric.ball (KAM.realInclusion n J0) r0) :=
    (differentiableOn_p11HoloFreq D).mono
      ((Metric.ball_subset_ball hr0nv).trans hnvsub)
  have hΩd : DifferentiableOn ℂ (fun J => (2 * Real.pi : ℂ) • G J)
      (Metric.ball (KAM.realInclusion n J0) r0) := hGd'.fun_const_smul _
  have hWd : DifferentiableOn ℂ (fun J => (Fin.append (p11HoloFreq D J)
      ((2 * Real.pi : ℂ)⁻¹ • ((2 * Real.pi : ℂ) • G J)) : Fin (n + n) → ℂ))
      (Metric.ball (KAM.realInclusion n J0) r0) :=
    differentiableOn_p11_append hFd (hΩd.fun_const_smul _)
  obtain ⟨L, hL1, hL⟩ := p11_jet_bound_complex h2rC hWd ((p11PatchData D).mu + 1)
  have hcenter : (2 * Real.pi)⁻¹ • KAM.realInclusion n J0 =
      KAM.realInclusion n ((2 * Real.pi)⁻¹ • J0) := by
    rw [map_smul]
  have hrCπ : rC / Real.pi ≤ t2 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith
  have hballρ : Metric.ball ((2 * Real.pi)⁻¹ • KAM.realInclusion n J0) (rC / Real.pi) ⊆
      Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • J0)) (t2 / 2) := by
    rw [hcenter]; exact Metric.ball_subset_ball hrCπ
  refine ⟨{
    J0 := J0, gamma := gamma, tau := max ((n : ℝ) * (p11PatchData D).mu) (2 * n), rC := rC,
    L := L, Brho := B, Bdrho := B', h := p11HoloH D, omega := p11HoloFreq D,
    Omega := fun J => (2 * Real.pi : ℂ) • G J, rho := ρ, R := R, t1 := t1, t2 := t2,
    t2_pos := ht2, t2_le := ht21, R_analytic := hRan, R_frame := hRfr, rho_diff := hρent,
    rho_real := hρreal, rho_orth_t2 := hρorth, rC_le_t2 := hrCt2, nonvanishing := hnv,
    freq := ?_, h_re := ?_, Omega_real := ?_, omega_diff := ?_, Omega_diff := ?_, tau_eq := rfl, h_diff := ?_,
    omega_eq := ?_, jets := ?_, euclid_le := ?_, J0_interior := hJ0int, gamma_pos := hg0,
    gamma_le := hg1, dio := hd, dio_fast := hdf, dio_slow := hds, rC_pos := hrC0,
    rC_le_one := hrC1, rC_le_delta := hrCδ, one_le_L := hL1, one_le_Brho := hB1,
    one_le_Bdrho := hB1', rho_clause := ?_, rho_bounds := ?_ }⟩
  · -- freq
    intro J hJ
    have hJ' : ‖J - J0‖ < 2 * rC := by
      have := KAM.realInclusion_mem_ball_iff.1 hJ
      rwa [mem_ball_iff_norm] at this
    have hJV : J ∈ (p11PatchData D).V := by
      refine hrVsub ?_
      rw [mem_ball_iff_norm]; linarith
    have hnvJ : ∀ i, J i ≠ 0 := fun i => by
      have := hnv hJ i
      simpa using this
    have hlt : ‖J - J0‖ < rΩ := by linarith
    refine ⟨hJV, fun i => ?_, fun i => ?_⟩
    · rw [p11HoloFreq_re D hnvJ i, hVar J hJV, Fin.append_left]
    · have := hGeq J hlt
      simp only [this, Pi.smul_apply, smul_eq_mul, KAM.realInclusion_apply]
      simp
  · -- h_re
    intro J hJ
    have hnvJ : ∀ i, J i ≠ 0 := fun i => by
      have hm : KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n J0) (2 * rC) := by
        rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion]; exact hJ
      have := hnv hm i
      simpa using this
    exact p11HoloH_re D hnvJ
  · -- Omega_real
    intro J hJ i
    have hlt : ‖J - J0‖ < rΩ := by linarith
    have := hGeq J hlt
    simp only [this, Pi.smul_apply, smul_eq_mul, KAM.realInclusion_apply]
    simp
  · exact (differentiableOn_p11HoloFreq D).mono hnv
  · exact (hGd.mono ((Metric.ball_subset_ball (by linarith)))).fun_const_smul _
  · exact (differentiableOn_p11HoloH D).mono hnv
  · intro J hJ
    funext i
    exact (fderiv_p11HoloH D (hnv hJ) i).symm
  · intro J hJ j hj
    exact (hL J hJ).1 j hj
  · intro J hJ
    exact (hL J hJ).2
  · -- rho_clause
    intro Lr hLr
    have hLt2 : ‖Lr - (2 * Real.pi)⁻¹ • J0‖ < t2 := by
      refine lt_of_lt_of_le hLr ?_
      refine (div_le_iff₀ Real.pi_pos).2 ?_
      nlinarith [Real.pi_pos]
    have hLt1 : Lr ∈ Metric.ball ((2 * Real.pi)⁻¹ • J0) t1 := by
      rw [mem_ball_iff_norm]; linarith
    obtain ⟨-, -, hSO, -, -, hdiag⟩ := hRfr Lr hLt1
    have hreal := hρreal Lr hLt2
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [hreal]; simp
    · rw [hreal]
      have h := RingHom.map_det Complex.ofRealHom (R Lr)
      rw [hSO.2] at h
      simp only [RingHom.mapMatrix_apply, map_one] at h
      exact h.symm
    · have : (fun i j => (ρ (KAM.realInclusion n Lr) i j).re) = R Lr := by
        funext i j; rw [hreal]; simp
      simpa only [this] using hdiag
  · -- rho_bounds
    refine ⟨?_, fun J hJ => ?_⟩
    · refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
      exact (hρent i j).mono (hballρ.trans (Metric.ball_subset_ball (by linarith)))
    · have hJ2 := hballρ hJ
      have hJ3 : J ∈ Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • J0)) t2 :=
        Metric.ball_subset_ball (by linarith) hJ2
      exact ⟨hρorth J hJ3, (hBb J hJ2).1, (hBb J hJ2).2⟩

end Data

end KAM.Planetary

end
