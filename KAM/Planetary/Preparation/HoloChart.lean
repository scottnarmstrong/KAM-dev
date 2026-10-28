/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloLift
public import KAM.Planetary.SecularSpectrum.Transport
public import KAM.Planetary.Newtonian.Tube
public import KAM.Planetary.Poincare.Product

/-!
# The real chart `Ψ_c` (P11A-P2d, `stepP:p11:hc-id`, `stepP:p11:hc-lat`)

The real chart of `holo_chart` is `Ψ_c = Ψ^{(n)} ∘ Φ_ρ⁻¹ ∘ T₁`, with `T₁ = p11FastScale` the linear
period conversion `(θ, J) ↦ (2πθ, J/2π)` on the fast block, `Φ_ρ⁻¹ = liftInv R` the real inverse
lift of the frame `R` of `P11HoloData`, and `Ψ^{(n)} = poincareProd`. This module proves, for the
literal chart input `p11ChartInput`:

* `p11FastScale` is linear, symplectic, injective and turns the unit lattice shift into
  `fastShift`;
* analyticity and symplecticity of the chart on the real working domain;
* the lattice clauses (invariance under `θ ↦ θ + k`, injectivity modulo the lattice);
* membership of the chart input in `poincareProdDom` and of the chart in `collisionFreeDomain`,
  from the smallness of `r_C` (`r_C ≤ π δ/8`) and `(B_ρ r_z)² ≤ δ` (`forward_tube`);
* the energy identity `fixedHamiltonian = Re (h + ε F)` with `F` a parameter.

`P11HoloData.chart_spec` assembles the last conjunct of `P11SecularSpec`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Scale

variable {n : ℕ}

/-- `T₁` on the fast block: `(θ, J) ↦ (2πθ, J/2π)`, secular coordinates unchanged. -/
def p11FastScaleL : Phase (n + n) →ₗ[ℝ] Phase (n + n) where
  toFun z := assemble (fun i => fast z.2 i / (2 * Real.pi)) (fun l => 2 * Real.pi * fast z.1 l)
    (slow z.2) (slow z.1)
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fast, slow, mul_add, add_div]
  map_smul' c u := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fast, slow, mul_left_comm, mul_div_assoc]

/-- The period conversion `T₁` of the fast block, as a continuous linear map. -/
def p11FastScale : Phase (n + n) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap p11FastScaleL

theorem p11FastScale_apply (z : Phase (n + n)) :
    p11FastScale z = assemble (fun i => fast z.2 i / (2 * Real.pi))
      (fun l => 2 * Real.pi * fast z.1 l) (slow z.2) (slow z.1) := rfl

theorem fast_snd_p11FastScale (z : Phase (n + n)) :
    fast (p11FastScale z).2 = fun i => fast z.2 i / (2 * Real.pi) := by
  rw [p11FastScale_apply]; exact SecularSpectrum.fast_snd_assemble _ _ _ _

/-- `T₁` preserves the symplectic form. -/
theorem p11FastScale_symplectic (u v : Phase (n + n)) :
    KAM.symplecticForm (p11FastScale u) (p11FastScale v) = KAM.symplecticForm u v := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [p11FastScale_apply, KAM.symplecticForm, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · simp [assemble, fast]
    field_simp
  · simp [assemble, slow]

theorem p11FastScale_injective : Function.Injective (p11FastScale (n := n)) := by
  intro u v h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [p11FastScale_apply, assemble] at h1 h2
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := congrFun h1 (Fin.castAdd n i)
      simpa [fast, hpi] using this
    · have := congrFun h1 (Fin.natAdd n i)
      simpa [slow] using this
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := congrFun h2 (Fin.castAdd n i)
      simpa [fast, hpi] using this
    · have := congrFun h2 (Fin.natAdd n i)
      simpa [slow] using this

/-- `hc-lat`: `T₁(θ + k, ·) = T₁ + (2π k, 0, 0, 0)`. -/
theorem p11FastScale_shift (z : Phase (n + n)) (k : Fin n → ℤ) :
    p11FastScale (z.1 + Fin.append (fun i => (k i : ℝ)) 0, z.2) =
      p11FastScale z + fastShift (a := n) (b := n) k := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [p11FastScale_apply, assemble, fast, slow, fastShift, mul_add]

theorem p11FastScale_isSymplecticOn :
    KAM.Kepler.IsSymplecticOn 1 (p11FastScale (n := n)) univ := by
  intro z _ u v
  rw [p11FastScale.fderiv, one_mul]
  exact p11FastScale_symplectic u v

end Scale

section Domain

variable {n : ℕ} {D : P11Physical n}

/-- The real points of the working domain: the fast action near `J₀`, the slow block small. -/
def p11RealDom (J0 : P11Vec n) (r rz : ℝ) : Set (Phase (n + n)) :=
  {z | ‖fast z.2 - J0‖ < r ∧ ‖slow z.1‖ < rz ∧ ‖slow z.2‖ < rz}

theorem p11_preimage_workingDom {J0 : P11Vec n} {s r rz : ℝ} (hs : 0 < s) :
    KAM.realInclusion₂ (n + n) ⁻¹' p11WorkingDom n J0 s r rz = p11RealDom J0 r rz := by
  ext z
  have h1 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.castAdd n i)) -
      KAM.realInclusion n J0 = KAM.realInclusion n (fast z.2 - J0) := by
    ext i; simp [fast]
  have h2 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).1 (Fin.natAdd n i)) =
      KAM.realInclusion n (slow z.1) := by ext i; simp [slow]
  have h3 : (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.natAdd n i)) =
      KAM.realInclusion n (slow z.2) := by ext i; simp [slow]
  simp only [mem_preimage, p11WorkingDom, p11RealDom, mem_ofPred_eq, h1, h2, h3,
    KAM.norm_realInclusion]
  exact ⟨fun h => h.2, fun h => ⟨KAM.realInclusion_mem_complexStrip hs _, h⟩⟩

theorem p11RealDom_shift {J0 : P11Vec n} {r rz : ℝ} {z : Phase (n + n)}
    (hz : z ∈ p11RealDom J0 r rz) (k : Fin n → ℤ) :
    (z.1 + Fin.append (fun i => (k i : ℝ)) 0, z.2) ∈ p11RealDom J0 r rz := by
  have h1 : slow (z.1 + Fin.append (fun i => (k i : ℝ)) 0) = slow z.1 := by
    funext i; simp [slow]
  exact ⟨hz.1, by simpa [h1] using hz.2.1, hz.2.2⟩

/-- On the real working domain the rescaled fast action is inside the frame ball. -/
theorem P11HoloData.fast_close (d : P11HoloData D) {z : Phase (n + n)}
    (hz : ‖fast z.2 - d.J0‖ < 2 * d.rC) :
    ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.rC / Real.pi ∧
      ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2 ∧
      ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : (fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0 =
      (2 * Real.pi)⁻¹ • (fast z.2 - d.J0) := by
    ext i; simp [div_eq_inv_mul, mul_sub]
  have h1 : ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ <
      d.rC / Real.pi := by
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpi.le)]
    calc (2 * Real.pi)⁻¹ * ‖fast z.2 - d.J0‖ < (2 * Real.pi)⁻¹ * (2 * d.rC) :=
          mul_lt_mul_of_pos_left hz (inv_pos.2 hpi)
      _ = d.rC / Real.pi := by field_simp
  have hr := d.rC_le_t2
  have h2 : d.rC / Real.pi ≤ d.t2 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [d.t2_pos, Real.pi_pos]
  exact ⟨h1, by linarith [d.t2_pos], by linarith [d.t2_pos, d.t2_le]⟩

end Domain

section Membership

variable {n : ℕ} {D : P11Physical n}
open SecularSpectrum

/-- The literal chart input is the real inverse lift of `T₁ z` (`hc-lift` on the real domain). -/
theorem P11HoloData.chartInput_eq' (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {z : Phase (n + n)}
    (hz : ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2) :
    p11ChartInput C z = liftInv d.R (p11FastScale z) := by
  rw [p11FastScale_apply]
  exact d.chartInput_eq_liftInv C hC z hz

theorem P11HoloData.chartInput_eq (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {z : Phase (n + n)} (hz : ‖fast z.2 - d.J0‖ < 2 * d.rC) :
    p11ChartInput C z = liftInv d.R (p11FastScale z) :=
  d.chartInput_eq' C hC (d.fast_close hz).2.1

/-- Row sums of the real frame on the real `ρ`-ball. -/
theorem P11HoloData.R_row_bound (d : P11HoloData D) {L : P11Vec n}
    (hL : ‖L - (2 * Real.pi)⁻¹ • d.J0‖ < d.rC / Real.pi) (i : Fin n) :
    ∑ j, |d.R L i j| ≤ d.Brho := by
  have hL2 : ‖L - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2 := by
    refine hL.trans_le ?_
    have hr := d.rC_le_t2
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [d.t2_pos, Real.pi_pos]
  have hball : KAM.realInclusion n L ∈
      Metric.ball ((2 * Real.pi)⁻¹ • KAM.realInclusion n d.J0) (d.rC / Real.pi) := by
    rw [← map_smul]
    exact KAM.realInclusion_mem_ball_iff.2 (by rwa [mem_ball_iff_norm])
  have h := (d.rho_bounds.2 _ hball).2.1 i
  rw [d.rho_real L hL2] at h
  simpa using h

theorem P11HoloData.R_mulVec_bound (d : P11HoloData D) {L : P11Vec n}
    (hL : ‖L - (2 * Real.pi)⁻¹ • d.J0‖ < d.rC / Real.pi) (v : P11Vec n) (i : Fin n) :
    |(d.R L).mulVec v i| ≤ d.Brho * ‖v‖ := by
  have hrow := d.R_row_bound hL i
  calc |(d.R L).mulVec v i| = |∑ j, d.R L i j * v j| := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |d.R L i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |d.R L i j| * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |d.R L i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ d.Brho * ‖v‖ := mul_le_mul_of_nonneg_right hrow (norm_nonneg _)

/-- The circular tube of radius `ζ` is collision free. -/
theorem p11_noCollision_of_circularTube (D : P11Physical n) {z : Phase (n * 2)}
    (hz : z ∈ circularTube D.G D.m0 D.m D.a (p11Zeta D)) : NoCollision z.1 := by
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) D.n_ge
  have hax := axisData_canonical hn D.a_pos D.ordered.injective
  refine (circularTube_pair_bounds hax (p11_zeta_pos D) ?_ hz).2.2
  exact min_le_right _ _

/-- `hc-id`, membership: on the real working domain the chart input lies in `poincareProdDom` and
its Poincaré image in the `ζ`-tube around the circular torus (forward tube), under
`r_C ≤ π δ/8` (from the data) and `(B_ρ r_z)² ≤ δ`. -/
theorem P11HoloData.chartInput_mem (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D)
    {z : Phase (n + n)} (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) :
    p11ChartInput C z ∈ poincareProdDom n ∧
      poincareProd D.m (D.G * D.m0) (p11ChartInput C z) ∈
        circularTube D.G D.m0 D.m D.a (p11Zeta D) := by
  obtain ⟨hδ0, -, hft⟩ : 0 < p11PhysicalDelta D ∧
      (∀ i, p11PhysicalDelta D ≤ D.m i * Real.sqrt (D.G * D.m0 * D.a i) / 4) ∧
      ∀ w : Phase (n + n),
        (∀ i : Fin n, |w.2 (Fin.castAdd n i) - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| ≤
          p11PhysicalDelta D) →
        (∀ i, poincareGamma (planetBlock w i) ≤ p11PhysicalDelta D) →
        w ∈ poincareProdDom n ∧
          ‖poincareProd D.m (D.G * D.m0) w -
            circularPoint D.G D.m0 D.m D.a
              (fun i => w.1 (Fin.castAdd n i) / (2 * Real.pi))‖ < p11Zeta D :=
    (forward_tube D (p11_zeta_pos D)).choose_spec
  have hpi : 0 < 2 * Real.pi := by positivity
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨hc1, -, -⟩ := d.fast_close hz1
  have hw := d.chartInput_eq C hC hz1
  set w := p11ChartInput C z with hwdef
  have hfast : fast w.2 = fun i => fast z.2 i / (2 * Real.pi) := by
    rw [hw]; simp only [liftInv]
    rw [fast_snd_assemble, fast_snd_p11FastScale]
  have hs1 : slow w.1 = (d.R fun i => fast z.2 i / (2 * Real.pi)).mulVec (slow z.1) := by
    rw [hw]; simp only [liftInv]
    rw [slow_fst_assemble, p11FastScale_apply, slow_fst_assemble, fast_snd_assemble]
  have hs2 : slow w.2 = (d.R fun i => fast z.2 i / (2 * Real.pi)).mulVec (slow z.2) := by
    rw [hw]; simp only [liftInv]
    rw [slow_snd_assemble, p11FastScale_apply, slow_snd_assemble, fast_snd_assemble]
  have hK : d.J0 ∈ (p11PatchData D).K := interior_subset d.J0_interior
  have hpatch := (p11PatchData_spec D).2.2.2.2.2.2.2.2.2.2.2.2.2.2 d.J0 hK
  have hδ8 : d.rC / Real.pi ≤ p11PhysicalDelta D / 8 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [d.rC_le_delta]
  have hBr : 0 ≤ d.Brho := zero_le_one.trans d.one_le_Brho
  have h1 : ∀ i : Fin n, |w.2 (Fin.castAdd n i) - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| ≤
      p11PhysicalDelta D := fun i => by
    have e1 : w.2 (Fin.castAdd n i) = fast z.2 i / (2 * Real.pi) := congrFun hfast i
    have hi : |fast z.2 i / (2 * Real.pi) - (2 * Real.pi)⁻¹ * d.J0 i| ≤
        ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm ((fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0) i
    have h0 := hpatch i
    rw [inv_mul_eq_div] at hi
    rw [e1]
    calc _ = |(fast z.2 i / (2 * Real.pi) - d.J0 i / (2 * Real.pi)) +
          (d.J0 i / (2 * Real.pi) - D.m i * Real.sqrt (D.G * D.m0 * D.a i))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  have hrw : ∀ v : P11Vec n, ‖v‖ < rz → ∀ i, |(d.R fun i => fast z.2 i / (2 * Real.pi)).mulVec v i|
      ≤ d.Brho * rz := fun v hv i =>
    (d.R_mulVec_bound hc1 v i).trans (mul_le_mul_of_nonneg_left hv.le hBr)
  have h2 : ∀ i, poincareGamma (planetBlock w i) ≤ p11PhysicalDelta D := fun i => by
    have a1 := hrw _ hz2 i
    have a2 := hrw _ hz3 i
    rw [← hs1] at a1
    rw [← hs2] at a2
    have b1 := sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2
    have b2 := sq_le_sq' (abs_le.1 a2).1 (abs_le.1 a2).2
    simp only [poincareGamma, planetBlock, slow, Matrix.cons_val_one, Matrix.cons_val_zero]
    change (slow w.1 i ^ 2 + slow w.2 i ^ 2) / 2 ≤ _
    nlinarith [mul_pow d.Brho rz 2]
  obtain ⟨hdom, hnorm⟩ := hft w h1 h2
  exact ⟨hdom, _, hnorm⟩

/-- The fast block of the chart input is the rescaled fast action. -/
theorem P11HoloData.fast_chartInput (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {z : Phase (n + n)} (hz : ‖fast z.2 - d.J0‖ < 2 * d.rC) :
    fast (p11ChartInput C z).2 = fun i => fast z.2 i / (2 * Real.pi) := by
  rw [d.chartInput_eq C hC hz]; simp only [liftInv]
  rw [fast_snd_assemble, fast_snd_p11FastScale]

end Membership

section Clauses

variable {n : ℕ} {D : P11Physical n}
open SecularSpectrum

/-- The ball on which the real frame `R` is analytic. -/
def P11HoloData.frameBall (d : P11HoloData D) : Set (P11Vec n) :=
  Metric.ball ((2 * Real.pi)⁻¹ • d.J0) d.t1

theorem P11HoloData.isOpen_frameBall (d : P11HoloData D) : IsOpen d.frameBall :=
  Metric.isOpen_ball

theorem P11HoloData.fast_scale_mem (d : P11HoloData D) {z : Phase (n + n)}
    (hz : ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t1) :
    p11FastScale z ∈ liftDomain d.frameBall := by
  show fast (p11FastScale z).2 ∈ d.frameBall
  rw [fast_snd_p11FastScale]
  exact mem_ball_iff_norm.2 hz

open scoped Matrix.Norms.Elementwise in
/-- `hc-lift`/`hc-id`: the inverse lift of the frame is analytic and symplectic on its domain. -/
theorem P11HoloData.liftInv_facts (d : P11HoloData D) :
    AnalyticOnNhd ℝ (liftInv d.R) (liftDomain d.frameBall) ∧
      KAM.Kepler.IsSymplecticOn 1 (liftInv d.R) (liftDomain d.frameBall) := by
  have hAn : AnalyticOnNhd ℝ d.R d.frameBall := fun x hx =>
    analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => d.R_analytic i j x hx
  obtain ⟨-, h2, -, h4, -⟩ := lift d.isOpen_frameBall hAn
    (fun I hI => (d.R_frame I hI).2.2.1)
  exact ⟨h2, h4⟩

theorem P11HoloData.liftInv_isSO (d : P11HoloData D) : ∀ I ∈ d.frameBall, isSO (d.R I) :=
  fun I hI => (d.R_frame I hI).2.2.1

/-- Near a point of the `t₂`-ball the literal chart is `Ψ^{(n)} ∘ Φ_ρ⁻¹ ∘ T₁`. -/
theorem P11HoloData.chart_eventuallyEq (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {z : Phase (n + n)}
    (hz : ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2) :
    C.chart =ᶠ[nhds z] poincareProd D.m (D.G * D.m0) ∘ liftInv d.R ∘ p11FastScale := by
  have hcont : Continuous fun z' : Phase (n + n) =>
      ‖(fun i => fast z'.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ := by
    unfold fast
    fun_prop
  have hopen : IsOpen {z' : Phase (n + n) |
      ‖(fun i => fast z'.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2} :=
    isOpen_lt hcont continuous_const
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  rw [hch z', d.chartInput_eq' C hC hz']
  rfl

end Clauses

section Properties

variable {n : ℕ} {D : P11Physical n}
open SecularSpectrum

theorem p11_kappa_pos (D : P11Physical n) : 0 < D.G * D.m0 := mul_pos D.G_pos D.m0_pos

/-- `hc-id`: the chart input of a real point of the working domain lies in `poincareProdDom` and
equals `liftInv R (T₁ z)`; packaged for the clauses below. -/
theorem P11HoloData.chartInput_dom (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D)
    {z : Phase (n + n)} (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) :
    liftInv d.R (p11FastScale z) ∈ poincareProdDom n := by
  rw [← d.chartInput_eq C hC hz.1]
  exact (d.chartInput_mem C hC hrz hz).1

/-- `hc-id`: the chart is real analytic on the real working domain. -/
theorem P11HoloData.chart_analyticAt (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D) {z : Phase (n + n)}
    (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) : AnalyticAt ℝ C.chart z := by
  obtain ⟨-, ht2, ht1⟩ := d.fast_close hz.1
  refine AnalyticAt.congr ?_ (d.chart_eventuallyEq C hC hch ht2).symm
  have hP := analyticOnNhd_poincareProd D.m_pos (p11_kappa_pos D) _
    (d.chartInput_dom C hC hrz hz)
  have hL : AnalyticAt ℝ (liftInv d.R) (p11FastScale z) :=
    d.liftInv_facts.1 _ (d.fast_scale_mem ht1)
  exact (hP.comp hL).comp (p11FastScale.analyticAt z)

/-- `hc-id`: the chart is symplectic (`c = 1`) on the real working domain. -/
theorem P11HoloData.chart_symplectic (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D) :
    KAM.Kepler.IsSymplecticOn 1 C.chart (p11RealDom d.J0 (2 * d.rC) rz) := by
  intro z hz u v
  obtain ⟨-, ht2, ht1⟩ := d.fast_close hz.1
  rw [(d.chart_eventuallyEq C hC hch ht2).fderiv_eq]
  have hlift := d.liftInv_facts
  have h12 : KAM.Kepler.IsSymplecticOn (1 * 1) (liftInv d.R ∘ p11FastScale)
      {z | p11FastScale z ∈ liftDomain d.frameBall} :=
    KAM.Kepler.IsSymplecticOn.comp (fun z _ => p11FastScale_isSymplecticOn z (mem_univ _))
      hlift.2 (fun z _ => p11FastScale.differentiableAt)
      (fun w hw => (hlift.1 w hw).differentiableAt) (fun z hz => hz)
  have hOsub : ∀ z ∈ p11RealDom d.J0 (2 * d.rC) rz,
      p11FastScale z ∈ liftDomain d.frameBall := fun z hz =>
    d.fast_scale_mem (d.fast_close hz.1).2.2
  have h123 : KAM.Kepler.IsSymplecticOn (1 * (1 * 1))
      (poincareProd D.m (D.G * D.m0) ∘ (liftInv d.R ∘ p11FastScale))
      (p11RealDom d.J0 (2 * d.rC) rz) :=
    KAM.Kepler.IsSymplecticOn.comp (fun z hz => h12 z (hOsub z hz))
      (poincareProd_symplectic D.m_pos (p11_kappa_pos D))
      (fun z hz => ((d.liftInv_facts.1 _ (hOsub z hz)).comp
        (p11FastScale.analyticAt z)).differentiableAt)
      (fun w hw => (analyticOnNhd_poincareProd D.m_pos (p11_kappa_pos D) w hw).differentiableAt)
      (fun z hz => d.chartInput_dom C hC hrz hz)
  simpa using h123 z hz u v

/-- `hc-lat`, (Q1) with `σ_k = 0`: the chart is invariant under the unit lattice in `θ`. -/
theorem P11HoloData.chart_lattice (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D) {z : Phase (n + n)}
    (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) (k : Fin n → ℤ) :
    C.chart (z.1 + Fin.append (fun i => (k i : ℝ)) 0, z.2) = C.chart z := by
  have hz' := p11RealDom_shift hz k
  rw [hch, hch, d.chartInput_eq C hC hz'.1, d.chartInput_eq C hC hz.1, p11FastScale_shift,
    liftInv_add_fastShift]
  exact (poincareProd_lattice D.m_pos (p11_kappa_pos D) (d.chartInput_dom C hC hrz hz) k).2

/-- `hc-lat`, (Q2): injectivity modulo the unit lattice in `θ`. -/
theorem P11HoloData.chart_injective (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D) {z z' : Phase (n + n)}
    (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) (hz' : z' ∈ p11RealDom d.J0 (2 * d.rC) rz)
    (h : C.chart z = C.chart z') :
    ∃ k : Fin n → ℤ, z' = (z.1 + Fin.append (fun i => (k i : ℝ)) 0, z.2) := by
  rw [hch, hch, d.chartInput_eq C hC hz.1, d.chartInput_eq C hC hz'.1] at h
  obtain ⟨k, hk⟩ := (poincareProd_eq_iff D.m_pos (p11_kappa_pos D)
    (d.chartInput_dom C hC hrz hz) (d.chartInput_dom C hC hrz hz')).1 h
  refine ⟨k, p11FastScale_injective ?_⟩
  rw [p11FastScale_shift]
  refine liftInv_injOn (R := d.R) (W := d.frameBall) d.liftInv_isSO
    (u := p11FastScale z') (v := p11FastScale z + fastShift (a := n) (b := n) k) ?_ ?_ ?_
  · exact d.fast_scale_mem (d.fast_close hz'.1).2.2
  · rw [fast_snd_add_fastShift]; exact d.fast_scale_mem (d.fast_close hz.1).2.2
  · rw [liftInv_add_fastShift]; exact hk

/-- `hc-id`, energy identity: `H_fix (Ψ_c) = Re (h + ε F)`, with `F` a parameter whose real part
on real points is `f_fix ∘ Ψ^{(n)} ∘ (chart input)` (`hF`). -/
theorem P11HoloData.chart_energy (d : P11HoloData D) (C : P11SecularData n)
    (hC : C.rho = d.rho) (hh : C.h = d.h)
    (hch : ∀ z, C.chart z = poincareProd D.m (D.G * D.m0) (p11ChartInput C z))
    {rz : ℝ} (hrz : (d.Brho * rz) ^ 2 ≤ p11PhysicalDelta D)
    (hF : ∀ z ∈ p11RealDom d.J0 (2 * d.rC) rz,
      (C.F (KAM.realInclusion₂ (n + n) z)).re =
        fFix D.G D.m (poincareProd D.m (D.G * D.m0) (p11ChartInput C z)))
    (eps : ℝ) {z : Phase (n + n)} (hz : z ∈ p11RealDom d.J0 (2 * d.rC) rz) :
    fixedHamiltonian D.G D.m0 D.m eps (C.chart z) =
      (p11WorkingH C eps (KAM.realInclusion₂ (n + n) z)).re := by
  have hw := (d.chartInput_mem C hC hrz hz).1
  rw [hch, fixedHamiltonian_poincareProd D.m_pos (p11_kappa_pos D) hw]
  unfold p11WorkingH
  rw [Complex.add_re, Complex.re_ofReal_mul, hF z hz]
  congr 1
  have hJ : ‖fast z.2 - d.J0‖ < 2 * d.rC := hz.1
  have h1 := d.h_re (fast z.2) hJ
  have h2 : C.h (fun i : Fin n => (KAM.realInclusion₂ (n + n) z).2 (Fin.castAdd n i)) =
      d.h (KAM.realInclusion n (fast z.2)) := by
    rw [hh]; rfl
  rw [h2, h1]
  unfold hProd
  rw [d.fast_chartInput C hC hJ]

end Properties

end KAM.Planetary

end
