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

end KAM.Planetary

end
