/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Hamiltonian
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Planetary.Spatial.ChartLift.Stopped
public import KAM.Planetary.Spatial.ChartLift.Uniform

/-!
# The spatial chart setting for the stopped lift

Package LP-SP-LIFT, MAIN Lemma 14 for `d = 3` (`LP:MAIN L14 (468–500)`) with Lemma 18
(`LP:MAIN L18 (595–597)`); track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The spatial mirror of track P's `chartSafe`, `liftChartHam`, `liftQ`, `liftPhysicalDeriv`,
`liftField_periodic`, on `Phase (n + (n + n))` (`n` fast, `2n` slow canonical pairs):

* `spLiftChartSafe ν`: the open collision-free part of the chart domain (44);
* `spatialPulledHam ν μ = H_μ ∘ Ψ` (analytic on `spLiftChartSafe`), `spLiftChartHam ν μ =
  spatialHProd ν + μ · fSpatial ν ∘ Ψ` (the SP-PROD split; equal to `spatialPulledHam` on the
  domain, `spLiftChartHam_eq_pulled`);
* `spatialLiftPhysicalDeriv`: a chart-field solution projects to a physical solution;
* `spatialLiftQ`: the compact set of zero-angle chart points over the closed action box with
  `ΣΓ + Z ≤ c`, with the periodic uniform data of `uniformDataNM`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.ODE KAM.Kepler Set

variable {n : ℕ}

/-- The spatial chart AMD `Σ_k (ξ_k² + η_k²)/2` over the `2n` slow pairs (the left side of (47)). -/
def spatialChartAMD (w : Phase (n + (n + n))) : ℝ :=
  ∑ k, ((slow w.1 k) ^ 2 + (slow w.2 k) ^ 2) / 2

/-- The collision-free part of the product chart domain. -/
def spLiftChartSafe (ν : Fin n → ℝ) : Set (Phase (n + (n + n))) :=
  spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n

/-- The pulled-back moving Hamiltonian `w ↦ H_μ (Ψ w)` for the spatial product chart. -/
def spatialPulledHam (ν : Fin n → ℝ) (μ : ℝ) : Phase (n + (n + n)) → ℝ :=
  fun w => spatialHamiltonian ν μ (spatialPoincareProd ν w)

/-- The chart Hamiltonian `spatialHProd ν + μ · fSpatial ν ∘ Ψ` (SP-PROD item 4). -/
def spLiftChartHam (ν : Fin n → ℝ) (μ : ℝ) : Phase (n + (n + n)) → ℝ :=
  fun w => spatialHProd ν w + μ * fSpatial ν (spatialPoincareProd ν w)

theorem spLiftChartHam_eq_pulled {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spLiftChartHam ν μ w = spatialPulledHam ν μ w :=
  (spatialHamiltonian_spatialPoincareProd hν μ hw).symm

theorem isOpen_spLiftChartSafe {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    IsOpen (spLiftChartSafe ν) :=
  isOpen_spatialPoincareProd_preimage hν

theorem spLiftChartSafe_subset_dom (ν : Fin n → ℝ) : spLiftChartSafe ν ⊆ spatialPoincareProdDom n :=
  inter_subset_left

theorem analyticOnNhd_spatialPulledHam {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) :
    AnalyticOnNhd ℝ (spatialPulledHam ν μ) (spLiftChartSafe ν) :=
  analyticOnNhd_spatialHamiltonian_spatialPoincareProd hν μ

/-- The chart Hamiltonian field and the pulled-back field agree on the open set
`spLiftChartSafe`. -/
theorem spLiftChartHam_field_eq {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {w : Phase (n + (n + n))} (hw : w ∈ spLiftChartSafe ν) :
    hamiltonianVectorField (spLiftChartHam ν μ) w =
      hamiltonianVectorField (spatialPulledHam ν μ) w := by
  have hev : spLiftChartHam ν μ =ᶠ[nhds w] spatialPulledHam ν μ :=
    Filter.eventuallyEq_of_mem ((isOpen_spLiftChartSafe hν).mem_nhds hw) fun y hy =>
      spLiftChartHam_eq_pulled hν μ (spLiftChartSafe_subset_dom ν hy)
  simp only [hamiltonianVectorField, hev.fderiv_eq]

theorem differentiableAt_spatialChartHam {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {w : Phase (n + (n + n))} (hw : w ∈ spLiftChartSafe ν) :
    DifferentiableAt ℝ (spLiftChartHam ν μ) w := by
  have hev : spLiftChartHam ν μ =ᶠ[nhds w] spatialPulledHam ν μ :=
    Filter.eventuallyEq_of_mem ((isOpen_spLiftChartSafe hν).mem_nhds hw) fun y hy =>
      spLiftChartHam_eq_pulled hν μ (spLiftChartSafe_subset_dom ν hy)
  exact ((analyticOnNhd_spatialPulledHam hν μ) w hw).differentiableAt.congr_of_eventuallyEq hev

theorem contDiffOn_spatialLiftField {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) :
    ContDiffOn ℝ 1 (hamiltonianVectorField (spatialPulledHam ν μ)) (spLiftChartSafe ν) :=
  ham_smooth_c1 (isOpen_spLiftChartSafe hν)
    ((analyticOnNhd_spatialPulledHam hν μ).contDiffOn (isOpen_spLiftChartSafe hν).uniqueDiffOn)

/-! ### The chart as an equal-dimension chart, and projection of chart solutions -/

/-- The reindexing `n * 3 = n + (n + n)`. -/
theorem spatialDim_eq (n : ℕ) : n * 3 = n + (n + n) := by omega

/-- `Ψ` composed with the canonical reindexing, an endomorphism chart of `Phase (n * 3)`. -/
def spatialPoincareProdCast (ν : Fin n → ℝ) : Phase (n * 3) → Phase (n * 3) :=
  spatialPoincareProd ν ∘ phaseCast (spatialDim_eq n)

/-- Its domain. -/
def spatialPoincareProdCastDom (n : ℕ) : Set (Phase (n * 3)) :=
  phaseCast (spatialDim_eq n) ⁻¹' spatialPoincareProdDom n

theorem spatialPoincareProdCast_isChart {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    IsChart 1 (spatialPoincareProdCast ν) (spatialPoincareProdCastDom n) := by
  refine ⟨(analyticOnNhd_spatialPoincareProd hν).comp
    ((phaseCast_analytic (spatialDim_eq n)).mono (subset_univ _)) fun _ hz => hz, ?_⟩
  have h1 : IsSymplecticOn 1 (phaseCast (spatialDim_eq n)) (spatialPoincareProdCastDom n) :=
    fun z _ => phaseCast_symplectic (spatialDim_eq n) z (mem_univ _)
  have h := IsSymplecticOn.comp h1 (spatialPoincareProd_symplectic hν)
    (fun z _ => (phaseCast (spatialDim_eq n)).differentiableAt)
    (fun z hz => ((analyticOnNhd_spatialPoincareProd hν) z hz).differentiableAt)
    (fun z hz => hz)
  rw [mul_one] at h
  exact h

/-- Pointwise chart orbit: a solution of the pulled-back field in the chart domain projects, under
`Ψ`, to a solution of the spatial moving Hamilton field. -/
theorem spatialLiftPhysicalDeriv {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {y : ℝ → Phase (n + (n + n))} {t : ℝ} (hyO : y t ∈ spatialPoincareProdDom n)
    (hd : DifferentiableAt ℝ (spatialPulledHam ν μ) (y t))
    (hy : HasDerivAt y (hamiltonianVectorField (spatialPulledHam ν μ) (y t)) t) :
    HasDerivAt (spatialPoincareProd ν ∘ y)
      (hamiltonianVectorField (spatialHamiltonian ν μ) (spatialPoincareProd ν (y t))) t := by
  set c := phaseCast (spatialDim_eq n) with hc
  have hchart := spatialPoincareProdCast_isChart hν
  have hG : chartPullback 1 (spatialHamiltonian ν μ) (spatialPoincareProdCast ν) =
      spatialPulledHam ν μ ∘ c := by
    funext z
    simp [chartPullback, spatialPulledHam, spatialPoincareProdCast, hc]
  have hyO' : (c.symm ∘ y) t ∈ spatialPoincareProdCastDom n := by
    show c (c.symm (y t)) ∈ spatialPoincareProdDom n
    rwa [c.apply_symm_apply]
  have hy' : HasDerivAt (c.symm ∘ y)
      (c.symm (hamiltonianVectorField (spatialPulledHam ν μ) (y t))) t :=
    c.symm.hasFDerivAt.comp_hasDerivAt t hy
  have hd' : DifferentiableAt ℝ (spatialPulledHam ν μ) (c (c.symm (y t))) := by
    rwa [c.apply_symm_apply]
  have key := chart_orbit one_pos hchart (H := spatialHamiltonian ν μ) (J := {t})
    (y := c.symm ∘ y) (fun s hs => by rw [mem_singleton_iff.1 hs]; exact hyO')
    (fun s hs => by
      rw [mem_singleton_iff.1 hs, hG]
      refine ⟨hd'.comp _ c.differentiableAt, ?_⟩
      rw [Function.comp_apply]
      have := phaseCast_hamiltonianVectorField (spatialDim_eq n) (spatialPulledHam ν μ)
        (c.symm (y t))
      rw [← hc, c.apply_symm_apply] at this
      rw [this]; exact hy') t rfl
  have hfun : spatialPoincareProdCast ν ∘ (c.symm ∘ y) = spatialPoincareProd ν ∘ y := by
    funext s
    simp [spatialPoincareProdCast, hc]
  rw [hfun] at key
  have hpt : spatialPoincareProdCast ν ((c.symm ∘ y) t) = spatialPoincareProd ν (y t) := by
    simp [spatialPoincareProdCast, hc]
  rw [hpt] at key
  exact key.2

/-! ### Periodicity in the fast angles -/

theorem spatialFastShift_neg (k : Fin n → ℤ) :
    (fastShift (a := n) (b := n + n) (-k) : Phase (n + (n + n))) =
      -fastShift (a := n) (b := n + n) k := by
  refine Prod.ext (funext fun j => ?_) ?_
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift, Fin.append_left]
  · simp [fastShift]

theorem spLiftChartSafe_shift_iff {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (k : Fin n → ℤ)
    (w : Phase (n + (n + n))) :
    w ∈ spLiftChartSafe ν ↔ w + fastShift (a := n) (b := n + n) k ∈ spLiftChartSafe ν := by
  have key : ∀ (k : Fin n → ℤ) (w : Phase (n + (n + n))), w ∈ spLiftChartSafe ν →
      w + fastShift (a := n) (b := n + n) k ∈ spLiftChartSafe ν := by
    intro k w hw
    obtain ⟨h1, h2⟩ := spatialPoincareProd_lattice hν hw.1 k
    exact ⟨h1, by
      have : spatialPoincareProd ν (w + fastShift (a := n) (b := n + n) k) =
          spatialPoincareProd ν w := h2
      show spatialPoincareProd ν (w + fastShift (a := n) (b := n + n) k) ∈
        spatialCollisionFreeDomain n
      rw [this]; exact hw.2⟩
  refine ⟨key k w, fun h => ?_⟩
  have := key (-k) _ h
  rwa [spatialFastShift_neg, add_neg_cancel_right] at this

theorem spatialLiftField_periodic {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) (k : Fin n → ℤ) :
    ∀ w ∈ spLiftChartSafe ν, hamiltonianVectorField (spatialPulledHam ν μ)
      (w + fastShift (a := n) (b := n + n) k) =
        hamiltonianVectorField (spatialPulledHam ν μ) w := by
  intro x hx
  have hH : ∀ y ∈ spLiftChartSafe ν, spatialPulledHam ν μ
      (y + fastShift (a := n) (b := n + n) k) = spatialPulledHam ν μ y := by
    intro y hy
    simp only [spatialPulledHam]
    have : spatialPoincareProd ν (y + fastShift (a := n) (b := n + n) k) =
        spatialPoincareProd ν y := (spatialPoincareProd_lattice hν hy.1 k).2
    rw [this]
  have hev : (fun y => spatialPulledHam ν μ (y + fastShift (a := n) (b := n + n) k)) =ᶠ[nhds x]
      spatialPulledHam ν μ :=
    Filter.eventuallyEq_of_mem ((isOpen_spLiftChartSafe hν).mem_nhds hx) hH
  have hf : fderiv ℝ (spatialPulledHam ν μ) (x + fastShift (a := n) (b := n + n) k) =
      fderiv ℝ (spatialPulledHam ν μ) x := by
    rw [← hev.fderiv_eq, fderiv_comp_add_right]
  simp only [hamiltonianVectorField, hf]

/-! ### The compact zero-angle set -/

/-- The compact set of zero-angle chart points over the closed action box `I⁰ ± r` with
`ΣΓ + Z ≤ c` (spatial `liftQ`). -/
def spatialLiftQ (I0 : Fin n → ℝ) (r c : ℝ) : Set (Phase (n + (n + n))) :=
  {w | fast w.1 = 0 ∧ (∀ i, I0 i - r ≤ fast w.2 i ∧ fast w.2 i ≤ I0 i + r) ∧
    spatialChartAMD w ≤ c}

theorem spatialLiftQ_isClosed (I0 : Fin n → ℝ) (r c : ℝ) : IsClosed (spatialLiftQ I0 r c) := by
  have hc : Continuous (fun w : Phase (n + (n + n)) => spatialChartAMD w) := by
    unfold spatialChartAMD slow; fun_prop
  have hf1 : ∀ i, Continuous (fun w : Phase (n + (n + n)) => fast w.1 i) := fun i => by
    unfold fast; fun_prop
  have hf2 : ∀ i, Continuous (fun w : Phase (n + (n + n)) => fast w.2 i) := fun i => by
    unfold fast; fun_prop
  have h1 : IsClosed {w : Phase (n + (n + n)) | fast w.1 = 0} :=
    isClosed_eq (continuous_pi hf1) continuous_const
  have h2 : IsClosed {w : Phase (n + (n + n)) |
      ∀ i, I0 i - r ≤ fast w.2 i ∧ fast w.2 i ≤ I0 i + r} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (hf2 i)).inter
      (isClosed_le (hf2 i) continuous_const)
  exact h1.inter (h2.inter (isClosed_le hc continuous_const))

theorem spatialLiftQ_slow_bound {I0 : Fin n → ℝ} {r c : ℝ} {w : Phase (n + (n + n))}
    (hw : w ∈ spatialLiftQ I0 r c) (k : Fin (n + n)) :
    |slow w.1 k| ≤ |c| + 1 ∧ |slow w.2 k| ≤ |c| + 1 := by
  have h1 : ((slow w.1 k) ^ 2 + (slow w.2 k) ^ 2) / 2 ≤ spatialChartAMD w :=
    Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
      (fun j _ => by positivity) (Finset.mem_univ k)
  have h2 := hw.2.2
  have h3 := le_abs_self c
  have a1 := sq_abs (slow w.1 k)
  have a2 := sq_abs (slow w.2 k)
  constructor <;> nlinarith [abs_nonneg (slow w.1 k), abs_nonneg (slow w.2 k),
    sq_nonneg (slow w.1 k), sq_nonneg (slow w.2 k), sq_nonneg (|slow w.1 k| - 1),
    sq_nonneg (|slow w.2 k| - 1)]

theorem spatialLiftQ_fast_bound {I0 : Fin n → ℝ} {r c : ℝ} {w : Phase (n + (n + n))}
    (hw : w ∈ spatialLiftQ I0 r c) (i : Fin n) :
    |fast w.2 i| ≤ ∑ j, (|I0 j - r| + |I0 j + r|) := by
  obtain ⟨h1, h2⟩ := hw.2.1 i
  have : |fast w.2 i| ≤ |I0 i - r| + |I0 i + r| := by
    rw [abs_le']
    constructor <;> linarith [le_abs_self (I0 i + r), neg_abs_le (I0 i - r),
      abs_nonneg (I0 i + r), abs_nonneg (I0 i - r)]
  exact this.trans (Finset.single_le_sum (f := fun j => |I0 j - r| + |I0 j + r|)
    (fun j _ => by positivity) (Finset.mem_univ i))

theorem spatialLiftQ_isCompact (I0 : Fin n → ℝ) (r c : ℝ) : IsCompact (spatialLiftQ I0 r c) := by
  set S : ℝ := ∑ j, (|I0 j - r| + |I0 j + r|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  set R : ℝ := |c| + 1 + S with hR
  have hR0 : 0 ≤ R := by positivity
  refine Metric.isCompact_of_isClosed_isBounded (spatialLiftQ_isClosed I0 r c)
    (Metric.isBounded_closedBall (x := (0 : Phase (n + (n + n)))) (r := R) |>.subset
      fun w hw => ?_)
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h0 : w.1 (Fin.castAdd (n + n) i) = 0 := congrFun hw.1 i
      rw [h0]; simpa using hR0
    · have := (spatialLiftQ_slow_bound hw i).1
      show ‖slow w.1 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := spatialLiftQ_fast_bound hw i
      show ‖fast w.2 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith [abs_nonneg c]
    · have := (spatialLiftQ_slow_bound hw i).2
      show ‖slow w.2 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith

theorem spatialChartAMD_zeroAngle (w : Phase (n + (n + n))) :
    spatialChartAMD (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + (n + n))) =
      spatialChartAMD w := by
  have h1 : slow (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + (n + n))).1 =
      slow w.1 := funext fun i => udZeroFstNatAdd w i
  have h2 : slow (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + (n + n))).2 =
      slow w.2 := by rw [udZeroSnd]
  simp only [spatialChartAMD, h1, h2]

/-- `spatialChartAMD` is the deficit `Σ_i (Γ_i + Z_i)` over the bodies. -/
theorem spatialChartAMD_eq_sum_body (w : Phase (n + (n + n))) :
    spatialChartAMD w = ∑ i, (spatialGammaBody w i + spatialZBody w i) := by
  rw [sum_gamma_add_z_eq_half_slow_sq, spatialChartAMD, ← Finset.sum_add_distrib,
    ← Finset.sum_div]

end KAM.Planetary.Spatial

end
