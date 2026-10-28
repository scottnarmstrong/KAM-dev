/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.FlowRegular
public import KAM.Nekhoroshev.Averaging.FlowSymplectic

/-!
# Part N12: the averaging flow (`bpN:p12:flow`)

Openness of the flow domain, joint continuity of the flow and of its spatial derivative, `C¹`
time slices, the inverse `φ₋ₜ ∘ φₜ = id`, translation equivariance under `ℤⁿ` angle shifts, and
the symplectic determinant `det Dφₜ = 1`. The regularity comes from `FlowRegular`
(`avgFlow_regOn`); the determinant from `FlowSymplectic`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology
open KAM.ODE (IsSolutionIn IsMaximalSolution eIoo)

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

section Regularity

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

theorem isOpen_avgFlowDomain : IsOpen (avgFlowDomain h f R ε) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  refine Filter.mem_of_superset (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU)) ?_
  rintro q ⟨hq1, hq2⟩
  exact ⟨hR.1 hq2, hR.2.1 q.2 hq2 hq1⟩

theorem continuousOn_avgFlow :
    ContinuousOn (fun p : ℝ × AvgPhase n => avgFlow h f R ε p.1 p.2)
      (avgFlowDomain h f R ε) := by
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  exact (hR.2.2.1.continuousAt
    (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU))).continuousWithinAt

theorem continuousOn_fderiv_avgFlow :
    ContinuousOn (fun p : ℝ × AvgPhase n => fderiv ℝ (avgFlow h f R ε p.1) p.2)
      (avgFlowDomain h f R ε) := by
  intro p hp
  obtain ⟨J, U, hJ, hU, hpJ, hpU, hR⟩ := avgFlow_regOn d ε hp
  exact (hR.2.2.2.1.continuousAt
    (prod_mem_nhds (hJ.mem_nhds hpJ) (hU.mem_nhds hpU))).continuousWithinAt

theorem isOpen_avgOmega (t : ℝ) : IsOpen (avgOmega h f R ε t) :=
  (isOpen_avgFlowDomain d ε).preimage (continuous_const.prodMk continuous_id)

theorem contDiffOn_avgFlow (t : ℝ) :
    ContDiffOn ℝ 1 (avgFlow h f R ε t) (avgOmega h f R ε t) := by
  have hΩ := isOpen_avgOmega d ε t
  have hdiff : ∀ x ∈ avgOmega h f R ε t,
      HasFDerivAt (avgFlow h f R ε t) (fderiv ℝ (avgFlow h f R ε t) x) x := by
    intro x hx
    obtain ⟨J, U, -, -, htJ, hxU, hR⟩ := avgFlow_regOn d ε (p := (t, x)) hx
    exact (hR.2.2.2.2 x hxU t htJ).1
  have hc : ContinuousOn (fderiv ℝ (avgFlow h f R ε t)) (avgOmega h f R ε t) :=
    (continuousOn_fderiv_avgFlow d ε).comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => hx)
  have := (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).2
    ⟨fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.2 hc⟩
  simpa using this

end Regularity

section Inverse

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- The flow maps `Ω_t` into `Ω_{-t}` and `φ₋ₜ` inverts `φₜ` there. -/
theorem avgFlow_inverse {t : ℝ} {x : AvgPhase n} (hx : x ∈ avgOmega h f R ε t) :
    avgFlow h f R ε t x ∈ avgOmega h f R ε (-t) ∧
      avgFlow h f R ε (-t) (avgFlow h f R ε t x) = x := by
  have hmx := avgMaximal_spec d ε hx.1
  have hpW := (hmx.isSolution t hx.2).1
  have hmp := avgMaximal_spec d ε hpW
  have hI : IsOpen ((fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x)) :=
    (KAM.ODE.isOpen_eIoo _ _).preimage (continuous_id.add continuous_const)
  have hIc : ((fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x)).OrdConnected :=
    (KAM.ODE.ordConnected_eIoo _ _).preimage_mono fun a b hab => add_le_add_left hab _
  have h0 : (0 : ℝ) ∈ (fun u => u + t) ⁻¹' eIoo (avgTm h f R ε x) (avgTp h f R ε x) := by
    simpa using hx.2
  have := FlowChain.shift_sol (isOpen_avgDomain' n R) (avgField_contDiffOn d ε) hmp (t₀ := 0)
    (KAM.ODE.zero_mem_eIoo hmp) hI hIc h0
    (w := fun u => avgFlow h f R ε (u + t) x) (KAM.ODE.gen_symmetry_shift hmx.isSolution t)
    (by simpa using hmp.init.symm) (-t) (by simpa using KAM.ODE.zero_mem_eIoo hmx)
  obtain ⟨h1, h2⟩ := this
  refine ⟨⟨hpW, by simpa using h1⟩, ?_⟩
  have h3 : avgFlow h f R ε (-t) (avgFlow h f R ε t x) = avgFlow h f R ε (-t + t) x := by
    simpa using h2
  rw [h3, neg_add_cancel]
  exact hmx.init

end Inverse

section Determinant

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- Symplectic determinant: `det Dφₜ = 1` on `Ω_t`. -/
theorem det_fderiv_avgFlow {t : ℝ} {x : AvgPhase n} (hx : x ∈ avgOmega h f R ε t) :
    (fderiv ℝ (avgFlow h f R ε t) x).det = 1 := by
  have hxW : x ∈ avgDomain n R := hx.1
  have hmx := avgMaximal_spec d ε hxW
  have hIo : IsOpen (eIoo (avgTm h f R ε x) (avgTp h f R ε x)) := KAM.ODE.isOpen_eIoo _ _
  have hIc : IsPreconnected (eIoo (avgTm h f R ε x) (avgTp h f R ε x)) :=
    isPreconnected_iff_ordConnected.2 (KAM.ODE.ordConnected_eIoo _ _)
  have h0 := KAM.ODE.zero_mem_eIoo hmx
  set Φ : ℝ → AvgPhase n →L[ℝ] AvgPhase n := fun u => fderiv ℝ (avgFlow h f R ε u) x with hΦdef
  have hΦ : ∀ u ∈ eIoo (avgTm h f R ε x) (avgTp h f R ε x), HasDerivAt Φ
      ((fderiv ℝ (KAM.hamiltonianVectorField (avgH h f ε)) (avgFlow h f R ε u x)).comp (Φ u)) u :=
    fun u hu => flow_variational d ε (x := x) (t := u) ⟨hxW, hu⟩
  have hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ _ := by
    have : avgFlow h f R ε 0 =ᶠ[𝓝 x] id :=
      Filter.eventuallyEq_of_mem ((isOpen_avgDomain' n R).mem_nhds hxW) fun y hy =>
        (avgMaximal_spec d ε hy).init
    show fderiv ℝ (avgFlow h f R ε 0) x = _
    rw [this.fderiv_eq]
    exact fderiv_id
  have hskew : ∀ u ∈ eIoo (avgTm h f R ε x) (avgTp h f R ε x), ∀ a b,
      sympl (fderiv ℝ (KAM.hamiltonianVectorField (avgH h f ε)) (avgFlow h f R ε u x) a) b +
      sympl a (fderiv ℝ (KAM.hamiltonianVectorField (avgH h f ε)) (avgFlow h f R ε u x) b)
        = 0 := by
    intro u hu a b
    have hz := (hmx.isSolution u hu).1
    exact sympl_fderiv_field_skew (((avgH_contDiffOn d ε).contDiffAt
      ((isOpen_Wdom (n := n) R s).mem_nhds (avgDomain_subset_Wdom d hz))) ) a b
  have hpres : ∀ u ∈ eIoo (avgTm h f R ε x) (avgTp h f R ε x), ∀ a b,
      sympl (Φ u a) (Φ u b) = sympl a b := by
    intro u hu a b
    have := sympl_const_of_skew hIo hIc hΦ hskew h0 hu a b
    rwa [hΦ0] at this
  have hdet : ∀ u ∈ eIoo (avgTm h f R ε x) (avgTp h f R ε x),
      (Φ u).det = 1 ∨ (Φ u).det = -1 := fun u hu =>
    det_eq_one_or_neg_one (Φ u : AvgPhase n →ₗ[ℝ] AvgPhase n) (hpres u hu)
  have hΦc : ContinuousOn Φ (eIoo (avgTm h f R ε x) (avgTp h f R ε x)) := fun u hu =>
    (hΦ u hu).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun u => (Φ u).det) (eIoo (avgTm h f R ε x) (avgTp h f R ε x)) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hΦc
  have ht : t ∈ eIoo (avgTm h f R ε x) (avgTp h f R ε x) := hx.2
  rcases hdet t ht with h1 | h1
  · exact h1
  · exfalso
    have h00 : (Φ 0).det = 1 := by rw [hΦ0]; simp [ContinuousLinearMap.det]
    have := IsPreconnected.intermediate_value hIc ht h0 hgc
    have hmem : (0 : ℝ) ∈ Icc ((Φ t).det) ((Φ 0).det) := by rw [h1, h00]; constructor <;> norm_num
    obtain ⟨u, hu, hu0⟩ := this hmem
    have hu0' : (Φ u).det = 0 := hu0
    rcases hdet u hu with h2 | h2 <;> rw [h2] at hu0' <;> norm_num at hu0'

end Determinant

section Translation

theorem angleShift_neg (k : Fin n → ℤ) :
    KAM.ODE.angleShift (-k) = -KAM.ODE.angleShift k := by
  ext i <;> simp [KAM.ODE.angleShift]

theorem avgDomain_image_shift (k : Fin n → ℤ) :
    (fun x => x + KAM.ODE.angleShift k) '' avgDomain n R = avgDomain n R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨mem_univ _, by simpa [KAM.ODE.angleShift] using hx.2⟩
  · intro hy
    refine ⟨y + KAM.ODE.angleShift (-k), ⟨mem_univ _, by simpa [KAM.ODE.angleShift] using hy.2⟩, ?_⟩
    rw [angleShift_neg]
    exact neg_add_cancel_right _ _

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

theorem avgField_shift (k : Fin n → ℤ) {x : AvgPhase n} (hx : x ∈ avgDomain n R) :
    KAM.hamiltonianVectorField (avgH h f ε) (x + KAM.ODE.angleShift k) =
      KAM.hamiltonianVectorField (avgH h f ε) x :=
  (holo_real_d (data_smul' d ε) x (avgDomain_subset_Wdom d hx) k).2.2.2.1

/-- Forward half of translation equivariance. -/
theorem avgFlow_translate_fwd (k : Fin n → ℤ) {t : ℝ} {x : AvgPhase n}
    (hx : x ∈ avgOmega h f R ε t) :
    x + KAM.ODE.angleShift k ∈ avgOmega h f R ε t ∧
      avgFlow h f R ε t (x + KAM.ODE.angleShift k) =
        avgFlow h f R ε t x + KAM.ODE.angleShift k := by
  have hxW : x ∈ avgDomain n R := hx.1
  have hmx := avgMaximal_spec d ε hxW
  have hxvW : x + KAM.ODE.angleShift k ∈ avgDomain n R := by
    rw [← avgDomain_image_shift (R := R) k]; exact mem_image_of_mem _ hxW
  have hmv := avgMaximal_spec d ε hxvW
  have hsol : IsSolutionIn (KAM.hamiltonianVectorField (avgH h f ε)) (avgDomain n R)
      (eIoo (avgTm h f R ε x) (avgTp h f R ε x))
      (fun u => avgFlow h f R ε u x + KAM.ODE.angleShift k) :=
    KAM.ODE.gen_symmetry_translate hmx.isSolution (avgDomain_image_shift k)
      (fun y hy => avgField_shift d ε k hy)
  obtain ⟨hsub, heq⟩ := hmv.maximal _ _ (KAM.ODE.ordConnected_eIoo _ _)
    (KAM.ODE.zero_mem_eIoo hmx) (by simpa using congrArg (· + KAM.ODE.angleShift k) hmx.init) hsol
  exact ⟨⟨hxvW, hsub hx.2⟩, (heq hx.2).symm⟩

theorem avgFlow_translate (k : Fin n → ℤ) {t : ℝ} (x : AvgPhase n) :
    (x + KAM.ODE.angleShift k ∈ avgOmega h f R ε t ↔ x ∈ avgOmega h f R ε t) ∧
      (x ∈ avgOmega h f R ε t →
        avgFlow h f R ε t (x + KAM.ODE.angleShift k) =
          avgFlow h f R ε t x + KAM.ODE.angleShift k) := by
  refine ⟨⟨fun hx => ?_, fun hx => (avgFlow_translate_fwd d ε k hx).1⟩,
    fun hx => (avgFlow_translate_fwd d ε k hx).2⟩
  have := (avgFlow_translate_fwd d ε (-k) hx).1
  rwa [angleShift_neg, add_neg_cancel_right] at this

end Translation

theorem flow (d : AveragingData n R s h f) (ε : ℝ) :
    IsOpen (avgFlowDomain h f R ε) ∧
    ContinuousOn (fun p : ℝ × AvgPhase n => avgFlow h f R ε p.1 p.2)
      (avgFlowDomain h f R ε) ∧
    ContinuousOn (fun p : ℝ × AvgPhase n => fderiv ℝ (avgFlow h f R ε p.1) p.2)
      (avgFlowDomain h f R ε) ∧
    ∀ t : ℝ, IsOpen (avgOmega h f R ε t) ∧
      ContDiffOn ℝ 1 (avgFlow h f R ε t) (avgOmega h f R ε t) ∧
      Set.MapsTo (avgFlow h f R ε t) (avgOmega h f R ε t) (avgOmega h f R ε (-t)) ∧
      Set.LeftInvOn (avgFlow h f R ε (-t)) (avgFlow h f R ε t) (avgOmega h f R ε t) ∧
      (∀ x ∈ avgOmega h f R ε t,
        (fderiv ℝ (avgFlow h f R ε t) x).det = 1) ∧
      ∀ k : Fin n → ℤ, ∀ x : AvgPhase n,
        (x + KAM.ODE.angleShift k ∈ avgOmega h f R ε t ↔ x ∈ avgOmega h f R ε t) ∧
        (x ∈ avgOmega h f R ε t →
          avgFlow h f R ε t (x + KAM.ODE.angleShift k) =
            avgFlow h f R ε t x + KAM.ODE.angleShift k) :=
  ⟨isOpen_avgFlowDomain d ε, continuousOn_avgFlow d ε, continuousOn_fderiv_avgFlow d ε,
    fun t => ⟨isOpen_avgOmega d ε t, contDiffOn_avgFlow d ε t,
      fun _ hx => (avgFlow_inverse d ε hx).1, fun _ hx => (avgFlow_inverse d ε hx).2,
      fun _ hx => det_fderiv_avgFlow d ε hx, fun k x => avgFlow_translate d ε k x⟩⟩

end KAM.Nekhoroshev

end
