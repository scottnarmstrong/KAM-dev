/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputs
public import KAM.Planetary.PGAssembly.Chart
public import KAM.Planetary.TwoScale.Theorem
public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian

/-!
# P Part 5: the torus family, auxiliary lemmas (`bpP:p5:torus-conv`)

Helper lemmas for `torus_conv`: the tube/neighbourhood identification, agreement of the
extension with the real Hamiltonian on the cylinder, the identity
`H ∘ phi ∘ angleScale / (2*pi) = Re (kamH + kamF)` on the real strip (the Hamiltonian input of
`cyl_pipeline`), the transfer of a lattice torus from `Re (kamH + kamF)` to the chart-pulled-back
physical Hamiltonian, and the Lipschitz estimate from the two defect bounds of `two_scale_kam`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FAM.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

theorem fam_realTube_eq {n : ℕ} (D : Set (Fin n → ℝ)) (s : ℝ) :
    realTube D s = realNbhd D s := by
  ext v
  rw [mem_realTube_iff]
  simp only [realNbhd, mem_ofPred_eq, dist_eq_norm]

theorem fam_isOpen_realNbhd {n : ℕ} (D : Set (Fin n → ℝ)) (s : ℝ) :
    IsOpen (realNbhd D s) := by
  have h : realNbhd D s = ⋃ J ∈ D, Metric.ball J s := by
    ext I
    simp [realNbhd, Metric.mem_ball]
  rw [h]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem fam_angleScale_injective {c : ℝ} (hc : c ≠ 0) {n : ℕ} :
    Function.Injective (angleScale c : Phase n → Phase n) := by
  intro z z' h
  have h1 : c • z.1 = c • z'.1 := congrArg Prod.fst h
  exact Prod.ext ((smul_right_injective _ hc) h1) (by simpa [angleScale] using congrArg Prod.snd h)

theorem fam_hvf_congr {n : ℕ} {G G' : Phase n → ℝ} {z : Phase n} (hev : G =ᶠ[𝓝 z] G') :
    KAM.hamiltonianVectorField G z = KAM.hamiltonianVectorField G' z := by
  simp only [KAM.hamiltonianVectorField, hev.fderiv_eq]

/-- The real cylinder of radius `r` lies in the real domain of the extension. -/
theorem fam_cyl_ext (h : admissible d (pgRstar d) r mu) {y : Phase (a+b)}
    (hy : y ∈ cylinder d.V r) :
    KAM.realInclusion₂ (a+b) y ∈ extensionDomain d (pgExtension d).delta ∧
      y ∈ closure (cylinder d.V d.r0) := by
  obtain ⟨-, -, hr3, -⟩ := kh_dyn h
  have hr0 : 0 < r := h.1
  have hosc : pgOscRadius d ≤ d.r0/2 := min_le_left _ _
  have hsl : ∀ j : Fin b, |slow y.2 j| < r ∧ |slow y.1 j| < r := fun j => by
    have := hy.2 j
    have e1 : (slow y.2 j)^2 + (slow y.1 j)^2 < r^2 := this
    exact ⟨abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (slow y.1 j)]) hr0.le,
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (slow y.2 j)]) hr0.le⟩
  refine ⟨⟨y, subset_closure hy.1, ?_, ?_⟩, subset_closure ⟨hy.1, fun j => ?_⟩⟩
  · rw [Prod.norm_def, max_le_iff]
    constructor <;> refine (pi_norm_le_iff_of_nonneg (by linarith [d.hr0])).2 fun j => ?_ <;>
      rw [Real.norm_eq_abs]
    · have := (hsl j).1
      show |slow y.2 j| ≤ _
      linarith
    · have := (hsl j).2
      show |slow y.1 j| ≤ _
      linarith
  · rw [sub_self, norm_zero]; exact (pgExtension d).delta_pos
  · have := hy.2 j
    have e1 : (slow y.2 j)^2 + (slow y.1 j)^2 < r^2 := this
    have : r^2 < d.r0^2 := by nlinarith [d.hr0]
    exact lt_trans e1 this

/-- The Hamiltonian input of `cyl_pipeline`: on the real strip over the action domain, the
pulled-back physical Hamiltonian is the real part of `kamH + kamF`. -/
theorem fam_ham_eq (h : admissible d (pgRstar d) r mu) {z : Phase (a+b)}
    (hz : z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) :
    chartPullback (2*Real.pi) (degenerateHamiltonian d.H0 d.P mu)
        (phi d r mu h ∘ angleScale (2*Real.pi)) z =
      (kamH d mu (KAM.realInclusion (a+b) z.2) +
        kamF d r mu h (KAM.realInclusion₂ (a+b) z)).re := by
  obtain ⟨hphi, hcyl⟩ := location d r mu h z hz
  have hspec := kh_avg_spec h
  have hmu := mu_mem_Icc h
  have hpos : ∀ j : Fin b, 0 < blockSlow (angleScale (2*Real.pi) z).2 j :=
    phiDomain_slow_pos h hphi
  have hav := polar_mem_averagingDomain h hphi
  set u : Phase (a+b) := angleScale (2*Real.pi) z with hu
  have hpt : kamPolarPt (KAM.realInclusion₂ (a+b) z) =
      KAM.realInclusion₂ (a+b) (oscillatorPolar u) := by
    rw [← oscillatorPolarComplex_real u (fun j => hpos j)]
    show oscillatorPolarComplex ((2*Real.pi:ℂ) • (KAM.realInclusion₂ (a+b) z).1,
      (KAM.realInclusion₂ (a+b) z).2) = _
    congr 1
    refine Prod.ext (funext fun i => ?_) rfl
    simp [hu, angleScale]
  have hPsi := hspec.2.2.2.2.2.2.2.2.1 (oscillatorPolar u) hav
  have hWc : phi d r mu h u = realAverageMap (pgAvg d r mu h) (oscillatorPolar u) := rfl
  obtain ⟨hext, hcl⟩ := fam_cyl_ext h hcyl
  have hP := (pgExtension d).agrees mu hmu _ hcl hext
  have hH0 := (pgExtension d).h0real (blockFast (phi d r mu h u).2)
    (realInclusion_mem_actionNbhd (pgExtension d).delta_pos (subset_closure hcyl.1))
  have e : blockFast (KAM.realInclusion₂ (a+b) (phi d r mu h u)).2 =
      KAM.realInclusion a (blockFast (phi d r mu h u).2) := rfl
  have key : kamH d mu (KAM.realInclusion (a+b) z.2) +
      kamF d r mu h (KAM.realInclusion₂ (a+b) z) =
      ((((d.H0 (blockFast (phi d r mu h u).2) + mu * d.P mu (phi d r mu h u))/(2*Real.pi) :
        ℝ)) : ℂ) := by
    show kamH d mu (KAM.realInclusion (a+b) z.2) +
      (((pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi
        (kamPolarPt (KAM.realInclusion₂ (a+b) z))).2) + mu*(pgExtension d).P mu
        ((pgAvg d r mu h).Psi (kamPolarPt (KAM.realInclusion₂ (a+b) z))))/(2*Real.pi) -
        kamH d mu (KAM.realInclusion (a+b) z.2)) = _
    rw [hpt, hPsi, ← hWc, e, hH0, hP]
    push_cast
    ring
  rw [key, Complex.ofReal_re]
  show (2*Real.pi)⁻¹ * (d.H0 (fast (phi d r mu h u).2) + mu * d.P mu (phi d r mu h u)) = _
  show (2*Real.pi)⁻¹ * (d.H0 (blockFast (phi d r mu h u).2) + mu * d.P mu (phi d r mu h u)) = _
  rw [div_eq_inv_mul]

/-- Transfer of the lattice torus from `Re (kamH + kamF)` to the pulled-back physical
Hamiltonian. -/
theorem fam_lattice (h : admissible d (pgRstar d) r mu) {w : Fin (a+b) → ℝ}
    {K : (Fin (a+b) → ℝ) → Phase (a+b)}
    (hT : IsLatticeTorus KAM.ODE.angleShift
      (fun z : Phase (a+b) => (kamH d mu (KAM.realInclusion (a+b) z.2) +
        kamF d r mu h (KAM.realInclusion₂ (a+b) z)).re)
      (univ ×ˢ realTube (pgActionDomain d r mu) (params d r mu).rK) w K) :
    IsLatticeTorus KAM.ODE.angleShift
      (chartPullback (2*Real.pi) (degenerateHamiltonian d.H0 d.P mu)
        (phi d r mu h ∘ angleScale (2*Real.pi)))
      (angleScale (2*Real.pi) ⁻¹' phiDomain d r mu) w K := by
  obtain ⟨⟨han, hKO⟩, hlat, hinj, hD, hLag, hflow⟩ := hT
  have hZo : IsOpen {z : Phase (a+b) | z.2 ∈ realNbhd (pgActionDomain d r mu)
      (params d r mu).rK} := (fam_isOpen_realNbhd _ _).preimage continuous_snd
  have hmem : ∀ θ, (K θ).2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK := fun θ => by
    have := (hKO θ).1.2
    rwa [fam_realTube_eq] at this
  have hev : ∀ θ, (chartPullback (2*Real.pi) (degenerateHamiltonian d.H0 d.P mu)
      (phi d r mu h ∘ angleScale (2*Real.pi))) =ᶠ[𝓝 (K θ)]
      fun z : Phase (a+b) => (kamH d mu (KAM.realInclusion (a+b) z.2) +
        kamF d r mu h (KAM.realInclusion₂ (a+b) z)).re := fun θ => by
    filter_upwards [hZo.mem_nhds (hmem θ)] with z hz
    exact fam_ham_eq h hz
  refine ⟨⟨han, fun θ => ⟨(location d r mu h _ (hmem θ)).1, ?_⟩⟩, hlat, hinj, hD, hLag,
    fun θ t => ?_⟩
  · exact (show DifferentiableAt ℝ _ _ from (hKO θ).2).congr_of_eventuallyEq (hev θ)
  · rw [fam_hvf_congr (hev (θ + t • w))]
    exact hflow θ t

/-- The Lipschitz estimate of the raw family `(J, θ) ↦ Φ (θ, i J)` from the two defect bounds
of `two_scale_kam`, compared with the ordinary norm through the rescaled norm. -/
theorem fam_lipschitz {n : ℕ} {R s c c' : ℝ} (hR : 0 < R) (hs : 0 < s) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (Φ : Phase n → Phase n) (i : (Fin n → ℝ) → (Fin n → ℝ))
    (D₀ : Set (Fin n → ℝ))
    (hi : ∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ c * ‖I - J‖)
    (hΦ : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)), ∀ y ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)),
      limitmap_data R s ((Φ x - x) - (Φ y - y)) ≤ c' * limitmap_data R s (x - y)) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ D₀ ×ˢ (univ : Set (Fin n → ℝ)), ∀ z' ∈ D₀ ×ˢ (univ : Set (Fin n → ℝ)),
      ‖Φ (z.2, i z.1) - Φ (z'.2, i z'.1)‖ ≤ L * ‖z - z'‖ := by
  set M1 := max (s / (2 * Real.pi)) R with hM1
  set M2 := max (2 * Real.pi / s) R⁻¹ with hM2
  have hM1p : 0 ≤ M1 := le_max_of_le_right hR.le
  have hM2p : 0 ≤ M2 := le_max_of_le_right (inv_nonneg.2 hR.le)
  refine ⟨(1 + M1 * c' * M2) * (1 + c) + 1, by positivity, fun z hz z' hz' => ?_⟩
  have hx : ((z.2, i z.1) : Phase n) ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)) :=
    ⟨mem_univ _, z.1, hz.1, rfl⟩
  have hy : ((z'.2, i z'.1) : Phase n) ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)) :=
    ⟨mem_univ _, z'.1, hz'.1, rfl⟩
  have h1 : ‖z.1 - z'.1‖ ≤ ‖z - z'‖ := norm_fst_le (z - z')
  have h2 : ‖z.2 - z'.2‖ ≤ ‖z - z'‖ := norm_snd_le (z - z')
  have h3 : ‖i z.1 - i z'.1‖ ≤ (1 + c) * ‖z - z'‖ := by
    have e : i z.1 - i z'.1 = (z.1 - z'.1) + ((i z.1 - z.1) - (i z'.1 - z'.1)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := hi _ hz.1 _ hz'.1
    nlinarith [norm_nonneg (z - z')]
  have hxy : ‖((z.2, i z.1) : Phase n) - (z'.2, i z'.1)‖ ≤ (1 + c) * ‖z - z'‖ := by
    rw [Prod.mk_sub_mk, Prod.norm_def, max_le_iff]
    refine ⟨h2.trans ?_, h3⟩
    nlinarith [norm_nonneg (z - z')]
  set x : Phase n := (z.2, i z.1)
  set y : Phase n := (z'.2, i z'.1)
  have h4 : ‖(Φ x - x) - (Φ y - y)‖ ≤ M1 * (c' * (M2 * ‖x - y‖)) := by
    refine (norm_le_limitmap_data hR hs _).trans ?_
    refine mul_le_mul_of_nonneg_left ((hΦ x hx y hy).trans ?_) hM1p
    exact mul_le_mul_of_nonneg_left (limitmap_data_le_norm hR hs _) hc'
  have h5 : ‖Φ x - Φ y‖ ≤ ‖x - y‖ + ‖(Φ x - x) - (Φ y - y)‖ := by
    have e : Φ x - Φ y = (x - y) + ((Φ x - x) - (Φ y - y)) := by abel
    rw [e]; exact norm_add_le _ _
  have h6 : ‖x - y‖ ≥ 0 := norm_nonneg _
  show ‖Φ x - Φ y‖ ≤ _
  have h7 : M1 * (c' * (M2 * ‖x - y‖)) = (M1 * c' * M2) * ‖x - y‖ := by ring
  have h8 : ‖x - y‖ ≤ (1 + c) * ‖z - z'‖ := hxy
  have h9 : 0 ≤ M1 * c' * M2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h8 h9, norm_nonneg (z - z')]

end KAM.Planetary

end
