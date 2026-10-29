/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Constants
public import KAM.Iso.Linear.Tools
public import KAM.Head.Unperturbed
import KAM.Head.H1
import KAM.Head.HamiltonianField

/-!
# Part 3 (local charts): hypothesis (d) and the flat torus

Blueprint nodes `bpI:p3:hypothesis-d` and
`bpI:p3:torus`. `n = 2`, `τ = 2`.

* `hypothesis_d` (`bpI:p3:hypothesis-d`): (I1)-(I4) of I-G1 for `(𝔇, h + f)` with `M = Mconst`,
  and `|D^j f| ≤ F_j ε`. A wrapper on the Kolmogorov `derivative_bounds_design`, `h1_domainD_*`,
  `norm_iteratedFDeriv_hbold_le`, `cbar_mul_le_derivConstM` (none of which needs the Kolmogorov
  field of `KAM.Head.Data`).
* `torus` (`bpI:p3:torus`): the flat torus `K⁰(θ) = (θ, I)` is an approximately invariant torus of
  `h + f` at the frequency `∇h(I) = s' ω*`, with the extended torsion `𝖡_h(I) + R(θ)`,
  `R = flatRemainder`, a bounded perturbation, an invertible average for small `ε`, and an energy
  average within `ε` of `h(I)`.

The Kolmogorov `KAM.Head.unperturbed` carries `KAM.Head.Data` (Kolmogorov); the flat-torus facts are
restated here for `HeadData` and `PerturbData`, with the same proofs (`TorusAux`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Set Metric Filter Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement
open KAM.Head (unperturbedTorus muParam Fconst Mconst actionHessian)

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-! ### `hypothesis-d` -/

/-- `bpI:p3:hypothesis-d`: (I1)–(I4) for `(𝔇, h + f)` with `M = Mconst`, and `|D^j f| ≤ F_j ε`. -/
theorem hypothesis_d (hd : HeadData B s₀ r₀ h B' η) {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ}
    (hf : PerturbData B s₀ r₀ f ε) (hε1 : ε ≤ 1) :
    IsOpen (fractD B s₀ r₀) ∧
    (∀ z ∈ fractD B s₀ r₀, ∀ k : Fin 2 → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ fractD B s₀ r₀) ∧
    DifferentiableOn ℂ (totalH h f) (fractD B s₀ r₀) ∧
    (∀ z ∈ fractD B s₀ r₀, ∀ k : Fin 2 → ℤ,
      totalH h f (z.1 + (fun i => (k i : ℂ)), z.2) = totalH h f z) ∧
    (∀ θ I : Fin 2 → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ fractD B s₀ r₀ →
      (totalH h f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) ∧
    (∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ (totalH h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖hamiltonianVectorFieldℂ (totalH h f) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ (totalH h f)) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ (totalH h f)) z‖ ≤ Mconst s₀ r₀ B h ∧
      ‖iteratedFDeriv ℂ 2 (totalH h f) z‖ ≤ Mconst s₀ r₀ B h) ∧
    ∀ z ∈ fractD B s₀ r₀,
      (∀ j ∈ ({1, 2, 3} : Set ℕ), ‖iteratedFDeriv ℂ j f z‖ ≤ Fconst 2 s₀ r₀ j * ε) ∧
      ‖fderiv ℂ f z‖ ≤ Fconst 2 s₀ r₀ 1 * ε ∧
      ‖hamiltonianVectorFieldℂ f z‖ ≤ Fconst 2 s₀ r₀ 1 * ε := by
  have hs := hd.hs
  have hr := hd.hr
  obtain ⟨-, -, hc, hdd⟩ := KAM.Head.derivative_bounds_design hs hr hd.bounded hd.holo hf.holo
    hf.bound
  have hhalf : ∀ {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)}, z ∈ fractD B s₀ r₀ → z.2 ∈ actionNbhd B r₀ :=
    fun hz => KAM.Head.actionNbhd_mono B (half_le_self hr.le) hz.2
  refine ⟨KAM.Head.isOpen_domainD 2 s₀ r₀ B, fun z hz k => KAM.Head.h1_domainD_add_intCast hz k,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (fun z : (Fin 2 → ℂ) × (Fin 2 → ℂ) => h z.2)
        (fractD B s₀ r₀) :=
      hd.holo.comp differentiableOn_snd fun z hz => hhalf hz
    exact h1.add (hf.holo.mono (KAM.Head.h1_domainD_subset_domain 2 hs hr B))
  · intro z hz k
    have := hf.periodic z (KAM.Head.h1_domainD_subset_domain 2 hs hr B hz) k
    simp only [totalH]
    rw [this]
  · intro θ I hz
    have hI : toC I ∈ actionNbhd B r₀ := hhalf hz
    simp only [totalH, Complex.add_im]
    rw [hd.real I hI, hf.real θ I hI, add_zero]
  · intro z hz
    have hM := (hdd hε1 z hz)
    have h2 : ‖iteratedFDeriv ℂ 2 (totalH h f) z‖ ≤ Mconst s₀ r₀ B h := by
      rw [KAM.Head.Mconst_eq_derivConstM]
      exact (KAM.Head.norm_iteratedFDeriv_hbold_le hs hr hd.bounded hd.holo hf.holo hf.bound hz
        (j := 2) (by simp)).trans
        (KAM.Head.cbar_mul_le_derivConstM hs hr (KAM.Head.hBound_nonneg h B r₀) hε1 (by norm_num))
    exact ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2, h2⟩
  · intro z hz
    obtain ⟨hj, hX, -⟩ := hc z hz
    refine ⟨hj, ?_, hX⟩
    have := hj 1 (by simp)
    rwa [norm_iteratedFDeriv_one] at this


/-! ### The flat torus: pointwise identities -/

namespace TorusAux

open Filter Topology

variable {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ} {I : Fin 2 → ℝ}

theorem toC_mem_half (hr : 0 < r₀) (hI : I ∈ B) : toC I ∈ actionNbhd B (r₀ / 2) :=
  ⟨I, hI, by
    show ‖toC I - toC I‖ < r₀ / 2
    rw [sub_self, norm_zero]
    exact half_pos hr⟩

theorem unperturbed_mem (hr : 0 < r₀) (hI : I ∈ B) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) : unperturbedTorus I θ ∈ fractD B s₀ r₀ :=
  ⟨hθ, toC_mem_half hr hI⟩

theorem real_mem (hs : 0 < s₀) (hr : 0 < r₀) (hI : I ∈ B) (x : Fin 2 → ℝ) :
    ((toC x, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
  unperturbed_mem hr hI (ofReal_mem_complexStrip (half_pos (KAM.Head.stripWidth_pos hs)) x)

theorem differentiableOn_totalH (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε) :
    DifferentiableOn ℂ (totalH h f) (fractD B s₀ r₀) := by
  have h1 : DifferentiableOn ℂ (fun z : (Fin 2 → ℂ) × (Fin 2 → ℂ) => h z.2) (fractD B s₀ r₀) :=
    hd.holo.comp differentiableOn_snd fun z hz =>
      KAM.Head.actionNbhd_mono B (half_le_self hd.hr.le) hz.2
  exact h1.add (hf.holo.mono (KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B))

theorem differentiableAt_h (hd : HeadData B s₀ r₀ h B' η) {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    (hw : w ∈ fractD B s₀ r₀) : DifferentiableAt ℂ h w.2 :=
  hd.holo.differentiableAt ((KAM.Head.isOpen_actionNbhd B r₀).mem_nhds
    (KAM.Head.actionNbhd_mono B (half_le_self hd.hr.le) hw.2))

theorem differentiableAt_f (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hw : w ∈ fractD B s₀ r₀) : DifferentiableAt ℂ f w :=
  hf.holo.differentiableAt (((isOpen_complexStrip 2 s₀).prod
    (KAM.Head.isOpen_actionNbhd B r₀)).mem_nhds
    (KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B hw))

/-- `D(h + f)(w) = Dh(w.2) ∘ pr₂ + Df(w)` on `𝔇`. -/
theorem fderiv_totalH (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hw : w ∈ fractD B s₀ r₀) :
    fderiv ℂ (totalH h f) w =
      (fderiv ℂ h w.2).comp (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)) +
        fderiv ℂ f w := by
  have h1 : HasFDerivAt (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => h w.2)
      ((fderiv ℂ h w.2).comp (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ))) w :=
    (differentiableAt_h hd hw).hasFDerivAt.comp w hasFDerivAt_snd
  exact (h1.add (differentiableAt_f hd hf hw).hasFDerivAt).fderiv

/-- `∂²_I (h + f) = ∇²h + ∂²_I f` on `𝔇`. -/
theorem actionHessian_totalH (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hz : z ∈ fractD B s₀ r₀) :
    actionHessian (totalH h f) z = KAM.Head.hessian h z.2 + actionHessian f z := by
  have hopen : IsOpen (fractD B s₀ r₀) := KAM.Head.isOpen_domainD 2 s₀ r₀ B
  have hr := hd.hr
  have hz2 : z.2 ∈ actionNbhd B r₀ := KAM.Head.actionNbhd_mono B (half_le_self hr.le) hz.2
  have hfd_h : DifferentiableAt ℂ (fderiv ℂ h) z.2 :=
    (differentiableOn_fderiv_of_isOpen (KAM.Head.isOpen_actionNbhd B r₀)
      hd.holo).differentiableAt ((KAM.Head.isOpen_actionNbhd B r₀).mem_nhds hz2)
  have hfd_f : DifferentiableAt ℂ (fderiv ℂ f) z :=
    (differentiableOn_fderiv_of_isOpen ((isOpen_complexStrip 2 s₀).prod
      (KAM.Head.isOpen_actionNbhd B r₀)) hf.holo).differentiableAt
      (((isOpen_complexStrip 2 s₀).prod (KAM.Head.isOpen_actionNbhd B r₀)).mem_nhds
        (KAM.Head.h1_domainD_subset_domain 2 hd.hs hr B hz))
  ext i j
  have hev : (fun w => fderiv ℂ (totalH h f) w (0, Pi.single i 1)) =ᶠ[𝓝 z]
      fun w => fderiv ℂ h w.2 (Pi.single i 1) + fderiv ℂ f w (0, Pi.single i 1) :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => by
      beta_reduce
      rw [fderiv_totalH hd hf hw]
      rfl
  have hg : DifferentiableAt ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2 :=
    hfd_h.clm_apply (differentiableAt_const _)
  have hk : DifferentiableAt ℂ (fun w => fderiv ℂ f w (0, Pi.single i 1)) z :=
    hfd_f.clm_apply (differentiableAt_const _)
  have hgs : HasFDerivAt (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => fderiv ℂ h w.2 (Pi.single i 1))
      ((fderiv ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ))) z :=
    hg.hasFDerivAt.comp z hasFDerivAt_snd
  simp only [actionHessian, KAM.Head.hessian, Matrix.of_apply, Matrix.add_apply]
  rw [hev.fderiv_eq, (hgs.fun_add hk.hasFDerivAt).fderiv]
  simp

/-- For `θ ∈ T_{s/2}` the torsion of `K⁰` is `∂²_I (h + f)(θ, I)`, whatever `ω` is. -/
theorem torsion_flat (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hI : I ∈ B) (ω : Fin 2 → ℝ) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) :
    torsion (totalH h f) (unperturbedTorus I) ω θ = actionHessian (totalH h f) (θ, toC I) := by
  have hz : ((θ, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
    unperturbed_mem hd.hr hI hθ
  have hopen : IsOpen (fractD B s₀ r₀) := KAM.Head.isOpen_domainD 2 s₀ r₀ B
  have hdiff := differentiableOn_totalH hd hf
  have hX := KAM.Head.fderiv_hamiltonianVectorField hopen hdiff hz
  have hfd : DifferentiableAt ℂ (fderiv ℂ (totalH h f)) (θ, toC I) :=
    (differentiableOn_fderiv_of_isOpen hopen hdiff).differentiableAt (hopen.mem_nhds hz)
  have hK : unperturbedTorus I θ = (θ, toC I) := rfl
  ext i j
  rw [KAM.Head.unperturbed_actionHessian_apply hfd]
  simp only [torsion, hK, KAM.Head.normalFrame_unperturbedTorus, hX]
  simp [dotℂ, omegaZero, KAM.Head.hamJ_apply, Pi.single_apply]


/-- The last row of the extended torsion of `K⁰`: `Y_b = ∂_{I_b} h(I) + ∂_{I_b} f(θ, I)`. -/
theorem energyRow_flat (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hI : I ∈ B) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) (b : Fin 2) :
    KAM.Iso.Linear.energyRow (totalH h f) (unperturbedTorus I) θ b =
      fderiv ℂ h (toC I) (Pi.single b 1) + fderiv ℂ f (θ, toC I) (0, Pi.single b 1) := by
  have hz : ((θ, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
    unperturbed_mem hd.hr hI hθ
  have hK : unperturbedTorus I θ = (θ, toC I) := rfl
  simp only [KAM.Iso.Linear.energyRow, KAM.Head.normalFrame_unperturbedTorus]
  rw [hK, fderiv_totalH hd hf hz]
  simp

/-- `∇h(I)` read in `ℂ²`, and the Hessian `∇²h(I)` as the derivative of the frequency map. -/
theorem freq_facts (hd : HeadData B s₀ r₀ h B' η) (hI : I ∈ B) :
    (fun i => ((frequencyMap h I i : ℝ) : ℂ)) = KAM.Head.gradC h (toC I) ∧
    ∀ v : Fin 2 → ℝ, (fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)) =
      KAM.Head.hessian h (toC I) *ᵥ fun j => (v j : ℂ) := by
  have hI' : toC I ∈ actionNbhd B r₀ := KAM.Head.actionNbhd_mono B (half_le_self hd.hr.le)
    (toC_mem_half hd.hr hI)
  obtain ⟨h1, -, h3, -, -⟩ := KAM.Iso.Linear.freq_map_local (KAM.Head.isOpen_actionNbhd B r₀)
    hd.holo hd.real hI'
  exact ⟨h1, h3⟩

/-- For `ω = ∇h(I)` the invariance error of `K⁰` is the vector field of `f`. -/
theorem invarianceError_flat (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hI : I ∈ B) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) :
    invarianceError (totalH h f) (unperturbedTorus I) (frequencyMap h I) θ =
      hamiltonianVectorFieldℂ f (θ, toC I) := by
  have hz : ((θ, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
    unperturbed_mem hd.hr hI hθ
  have hgrad := (freq_facts hd hI).1
  have hK : unperturbedTorus I θ = (θ, toC I) := rfl
  simp only [invarianceError, hK, KAM.Head.fderiv_unperturbedTorus, hamiltonianVectorFieldℂ,
    fderiv_totalH hd hf hz]
  ext i
  · simp [congrFun hgrad i, KAM.Head.gradC]
  · simp

/-- `𝖡_h(I)` over `ℂ` is the bordered matrix of `∇²h(I)` and `∇h(I)`. -/
theorem borderedHessian_map (hd : HeadData B s₀ r₀ h B' η) (hI : I ∈ B) :
    (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) =
      KAM.Iso.Linear.bordMat (KAM.Head.hessian h (toC I)) (fun a => (frequencyMap h I a : ℂ))
        (fun a => (frequencyMap h I a : ℂ)) := by
  obtain ⟨-, h3⟩ := freq_facts hd hI
  ext (a | u) (b | v)
  · have h4 := congrFun (h3 (Pi.single b 1)) a
    have h5 : (fun j => (((Pi.single b (1 : ℝ) : Fin 2 → ℝ) j : ℝ) : ℂ)) = Pi.single b 1 := by
      ext j
      by_cases hj : j = b <;> simp [hj]
    rw [h5] at h4
    simp only [Matrix.map_apply, KAM.Iso.borderedHessian]
    rw [h4]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, KAM.Iso.Linear.bordMat]
  · simp [Matrix.map_apply, KAM.Iso.borderedHessian, KAM.Iso.Linear.bordMat]
  · simp [Matrix.map_apply, KAM.Iso.borderedHessian, KAM.Iso.Linear.bordMat]
  · simp [Matrix.map_apply, KAM.Iso.borderedHessian, KAM.Iso.Linear.bordMat]

/-- On `T_{s/2}` the extended torsion of `K⁰` at `ω = ∇h(I)` is `𝖡_h(I) + R(θ)`. -/
theorem extendedTorsion_flat (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hI : I ∈ B) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) :
    KAM.Iso.extendedTorsion (totalH h f) (unperturbedTorus I) (frequencyMap h I) θ =
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) + flatRemainder f I θ := by
  have hz : ((θ, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
    unperturbed_mem hd.hr hI hθ
  have hgrad := (freq_facts hd hI).1
  rw [borderedHessian_map hd hI, KAM.Iso.Linear.extendedTorsion_eq_bordMat]
  ext (a | u) (b | v)
  · show torsion (totalH h f) (unperturbedTorus I) (frequencyMap h I) θ a b = _
    rw [torsion_flat hd hf hI _ hθ, actionHessian_totalH hd hf hz]
    simp [KAM.Iso.Linear.bordMat, flatRemainder]
  · simp [KAM.Iso.Linear.bordMat, flatRemainder]
  · show KAM.Iso.Linear.energyRow (totalH h f) (unperturbedTorus I) θ b = _
    rw [energyRow_flat hd hf hI hθ]
    have := congrFun hgrad b
    simp [KAM.Iso.Linear.bordMat, flatRemainder, KAM.Head.gradC] at this ⊢
    rw [← this]
  · simp [KAM.Iso.Linear.bordMat, flatRemainder]


/-! ### The flat torus: size of the perturbation -/

theorem Fconst_nonneg (hs : 0 < s₀) (hr : 0 < r₀) (j : ℕ) : 0 ≤ Fconst 2 s₀ r₀ j := by
  have hδ := KAM.Head.deltaStar_pos hs hr
  unfold KAM.Head.Fconst
  rw [KAM.Head.cbar_eq]
  exact div_nonneg (by norm_num) (pow_nonneg hδ.le _)

theorem Fconst_one_le_two (hs : 0 < s₀) (hr : 0 < r₀) : Fconst 2 s₀ r₀ 1 ≤ Fconst 2 s₀ r₀ 2 := by
  have hδ := KAM.Head.deltaStar_pos hs hr
  have hδ1 : KAM.Head.deltaStar s₀ r₀ ≤ 1 :=
    (KAM.Head.deltaStar_le_quarter s₀ r₀).trans (by norm_num)
  unfold KAM.Head.Fconst
  rw [KAM.Head.cbar_eq]
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ 2)
    (pow_le_pow_of_le_one hδ.le hδ1 (by norm_num))

theorem differentiableAt_fderiv_f (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hz : z ∈ fractD B s₀ r₀) :
    DifferentiableAt ℂ (fderiv ℂ f) z :=
  (differentiableOn_fderiv_of_isOpen ((isOpen_complexStrip 2 s₀).prod
    (KAM.Head.isOpen_actionNbhd B r₀)) hf.holo).differentiableAt
    (((isOpen_complexStrip 2 s₀).prod (KAM.Head.isOpen_actionNbhd B r₀)).mem_nhds
      (KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B hz))

/-- `‖∂²_I f(z)‖ ≤ F₂ ε` on `𝔇`. -/
theorem norm_actionHessian_f_le (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hε1 : ε ≤ 1) {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hz : z ∈ fractD B s₀ r₀) :
    ‖actionHessian f z‖ ≤ Fconst 2 s₀ r₀ 2 * ε := by
  have hb := ((hypothesis_d hd hf hε1).2.2.2.2.2.2 z hz).1 2 (by simp)
  refine (KAM.Head.unperturbed_norm_actionHessian_le (differentiableAt_fderiv_f hd hf hz)).trans ?_
  rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb

/-- `‖∂_{I_b} f(z)‖ ≤ F₁ ε` on `𝔇`. -/
theorem norm_row_f_le (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hε1 : ε ≤ 1) {z : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hz : z ∈ fractD B s₀ r₀) (b : Fin 2) :
    ‖fderiv ℂ f z (0, Pi.single b 1)‖ ≤ Fconst 2 s₀ r₀ 1 * ε := by
  have hn : ‖((0 : Fin 2 → ℂ), (Pi.single b 1 : Fin 2 → ℂ))‖ ≤ 1 := by
    rw [Prod.norm_def]
    exact max_le (by simp) (by simp [Pi.norm_single])
  have hb := ((hypothesis_d hd hf hε1).2.2.2.2.2.2 z hz).2.1
  calc ‖fderiv ℂ f z (0, Pi.single b 1)‖
      ≤ ‖fderiv ℂ f z‖ * ‖((0 : Fin 2 → ℂ), (Pi.single b 1 : Fin 2 → ℂ))‖ :=
        (fderiv ℂ f z).le_opNorm _
    _ ≤ ‖fderiv ℂ f z‖ * 1 := by gcongr
    _ ≤ Fconst 2 s₀ r₀ 1 * ε := by rwa [mul_one]

/-- `‖R(θ)‖ ≤ 2 F₂ ε` on `T_{s/2}`. -/
theorem norm_flatRemainder_le (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hε1 : ε ≤ 1) (hI : I ∈ B) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (min s₀ 1 / 2)) :
    ‖flatRemainder f I θ‖ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε := by
  have hz : ((θ, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈ fractD B s₀ r₀ :=
    unperturbed_mem hd.hr hI hθ
  have hε0 := hf.nonneg
  have hF1 := Fconst_one_le_two hd.hs hd.hr
  have hF0 := Fconst_nonneg hd.hs hd.hr 2
  have hF10 := Fconst_nonneg hd.hs hd.hr 1
  have hA := norm_actionHessian_f_le hd hf hε1 hz
  have hrow := norm_row_f_le hd hf hε1 hz
  have hFε : Fconst 2 s₀ r₀ 1 * ε ≤ Fconst 2 s₀ r₀ 2 * ε := mul_le_mul_of_nonneg_right hF1 hε0
  have hFε0 : 0 ≤ Fconst 2 s₀ r₀ 2 * ε := mul_nonneg hF0 hε0
  refine (norm_le_iff_forall_rowSum (by positivity)).2 ?_
  rintro (a | u)
  · rw [Fintype.sum_sum_type]
    have e1 : ∀ b, flatRemainder f I θ (Sum.inl a) (Sum.inl b) = actionHessian f (θ, toC I) a b :=
      fun _ => rfl
    have e2 : ∀ v, flatRemainder f I θ (Sum.inl a) (Sum.inr v) = 0 := fun _ => rfl
    simp only [e1, e2, norm_zero, Finset.sum_const_zero, add_zero]
    calc ∑ b, ‖actionHessian f (θ, toC I) a b‖ ≤ ‖actionHessian f (θ, toC I)‖ :=
          rowSum_le_norm _ a
      _ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε := by linarith
  · rw [Fintype.sum_sum_type]
    have e3 : ∀ b, flatRemainder f I θ (Sum.inr u) (Sum.inl b) =
        fderiv ℂ f (θ, toC I) (0, Pi.single b 1) := fun _ => rfl
    have e4 : ∀ v, flatRemainder f I θ (Sum.inr u) (Sum.inr v) = 0 := fun _ => rfl
    simp only [e3, e4, norm_zero, Finset.sum_const_zero, add_zero]
    calc ∑ b, ‖fderiv ℂ f (θ, toC I) (0, Pi.single b 1)‖
        ≤ ∑ _b : Fin 2, Fconst 2 s₀ r₀ 1 * ε := Finset.sum_le_sum fun b _ => hrow b
      _ = 2 * (Fconst 2 s₀ r₀ 1 * ε) := by simp
      _ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε := by linarith


/-! ### Real matrices over `ℂ` -/

theorem norm_map_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖M.map (fun x : ℝ => (x : ℂ))‖ = ‖M‖ := by
  simp only [Matrix.linfty_opNorm_def, Matrix.map_apply, Complex.nnnorm_real]

theorem det_map_ofReal' {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    (M.map (fun x : ℝ => (x : ℂ))).det = (M.det : ℂ) := by
  have h := RingHom.map_det Complex.ofRealHom M
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem inv_map_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    (M.map (fun x : ℝ => (x : ℂ)))⁻¹ = M⁻¹.map (fun x : ℝ => (x : ℂ)) := by
  have hadj : (M.map (fun x : ℝ => (x : ℂ))).adjugate = M.adjugate.map (fun x : ℝ => (x : ℂ)) := by
    have h := RingHom.map_adjugate Complex.ofRealHom M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv', det_map_ofReal',
    hadj]
  ext i j
  simp [Matrix.smul_apply]

/-! ### Averages -/

/-- `‖∫ A‖ ≤ S` for an entrywise average of a continuous matrix-valued function on the real torus
(any finite index type; `KAM.Head.norm_matrixAverage_le` is for `Fin p × Fin q`). -/
theorem norm_entrywiseAverage_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : (Fin 2 → ℝ) → Matrix ι ι ℂ} {S : ℝ} (hA : Continuous A) (hS : ∀ x, ‖A x‖ ≤ S) :
    ‖(Matrix.of fun i j => torusAverage fun x => A x i j : Matrix ι ι ℂ)‖ ≤ S := by
  set cube : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 with hcube
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hint : ∀ i j, IntegrableOn (fun x => A x i j) cube := fun i j =>
    integrableOn_unitCube_of_continuous ((continuous_apply j).comp ((continuous_apply i).comp hA))
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec
    (Matrix.of fun i j => torusAverage fun x => A x i j : Matrix ι ι ℂ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  rw [← hMv]
  refine (pi_norm_le_iff_of_nonneg hS0).2 fun i => ?_
  have hcomp : (Matrix.of fun i j => torusAverage fun x => A x i j : Matrix ι ι ℂ).mulVec v i =
      torusAverage fun x => (A x).mulVec v i := by
    simp only [torusAverage, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
    · exact fun j _ => (hint i j).mul_const _
  rw [hcomp]
  refine norm_torusAverage_le (fun x _ => ?_)
  calc ‖(A x).mulVec v i‖ ≤ ‖(A x).mulVec v‖ := norm_le_pi_norm _ i
    _ ≤ ‖A x‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ S * 1 := mul_le_mul (hS x) hv1 (norm_nonneg _) hS0
    _ = S := mul_one S

/-- The integral of `c + a(x)` over the unit cube is `c + ∫ a`, for continuous `a`. -/
theorem integral_const_add {a : (Fin 2 → ℝ) → ℂ} (ha : Continuous a) (c : ℂ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1), (c + a x) =
      c + torusAverage a := by
  have hfin : volume (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by
    rw [volume_unitCube]
    exact ENNReal.one_ne_top
  rw [integral_add (integrableOn_const hfin) (integrableOn_unitCube_of_continuous ha),
    setIntegral_const, measureReal_def, volume_unitCube]
  simp [torusAverage]

/-- `x ↦ R(ι x)` is continuous on the real torus. -/
theorem continuous_flatRemainder (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hI : I ∈ B) : Continuous fun x : Fin 2 → ℝ => flatRemainder f I (toC x) := by
  have hU : IsOpen (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
    (isOpen_complexStrip 2 s₀).prod (KAM.Head.isOpen_actionNbhd B r₀)
  have hg : Continuous fun x : Fin 2 → ℝ => ((toC x, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).prodMk
      continuous_const
  have hmem : ∀ x : Fin 2 → ℝ, ((toC x, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) ∈
      complexStrip 2 s₀ ×ˢ actionNbhd B r₀ := fun x =>
    KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B (TorusAux.real_mem hd.hs hd.hr hI x)
  have hd1 : ∀ a : Fin 2, DifferentiableOn ℂ (fun w => fderiv ℂ f w (0, Pi.single a 1))
      (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) := fun a =>
    (differentiableOn_fderiv_of_isOpen hU hf.holo).clm_apply (differentiableOn_const _)
  have hc1 : ∀ a : Fin 2,
      Continuous fun x : Fin 2 → ℝ => fderiv ℂ f (toC x, toC I) (0, Pi.single a 1) :=
    fun a => (hd1 a).continuousOn.comp_continuous hg hmem
  have hc2 : ∀ a b : Fin 2, Continuous fun x : Fin 2 → ℝ => actionHessian f (toC x, toC I) a b :=
    fun a b => by
      have h2 : DifferentiableOn ℂ (fun w => fderiv ℂ (fun w' => fderiv ℂ f w' (0, Pi.single a 1)) w
          (0, Pi.single b 1)) (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
        (differentiableOn_fderiv_of_isOpen hU (hd1 a)).clm_apply (differentiableOn_const _)
      exact h2.continuousOn.comp_continuous hg hmem
  refine continuous_matrix ?_
  rintro (a | u) (b | v)
  · exact hc2 a b
  · exact continuous_const
  · exact hc1 b
  · exact continuous_const


/-- The average of the extended torsion of `K⁰` differs from `𝖡_h(I)` by at most `2 F₂ ε`. -/
theorem norm_extendedAverage_sub_le (hd : HeadData B s₀ r₀ h B' η)
    (hf : PerturbData B s₀ r₀ f ε) (hε1 : ε ≤ 1) (hI : I ∈ B) :
    ‖KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I) (frequencyMap h I) -
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ))‖ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε := by
  have hcont := continuous_flatRemainder hd hf hI
  have hreal : ∀ x : Fin 2 → ℝ, (fun i => (x i : ℂ)) ∈ complexStrip 2 (min s₀ 1 / 2) :=
    ofReal_mem_complexStrip (half_pos (KAM.Head.stripWidth_pos hd.hs))
  have hbound : ∀ x : Fin 2 → ℝ, ‖flatRemainder f I (toC x)‖ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε :=
    fun x => norm_flatRemainder_le hd hf hε1 hI (hreal x)
  have hent : KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I)
      (frequencyMap h I) - (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) =
      Matrix.of fun i j => torusAverage fun x => flatRemainder f I (toC x) i j := by
    ext i j
    have hc : Continuous fun x : Fin 2 → ℝ => flatRemainder f I (toC x) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hcont)
    have hfun : ∀ x : Fin 2 → ℝ, KAM.Iso.extendedTorsion (totalH h f) (unperturbedTorus I)
        (frequencyMap h I) (toC x) i j =
        (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) i j +
          flatRemainder f I (toC x) i j := fun x => by
      rw [extendedTorsion_flat hd hf hI (hreal x)]
      rfl
    have hint : KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I)
        (frequencyMap h I) i j = (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) i j +
          torusAverage fun x => flatRemainder f I (toC x) i j := by
      rw [← integral_const_add hc]
      exact setIntegral_congr_fun (MeasurableSet.pi Set.countable_univ
        fun _ _ => measurableSet_Icc) fun x _ => hfun x
    rw [Matrix.sub_apply, hint]
    simp
  rw [hent]
  exact norm_entrywiseAverage_le hcont hbound

/-- The inverse threshold: for `ε ≤ ε_T` and `I ∈ 𝒮`, `⟨𝖳_H⟩` is invertible with
`‖⟨𝖳_H⟩⁻¹‖ ≤ 2 S_h`. -/
theorem extendedAverage_inv (hd : HeadData B s₀ r₀ h B' η) (hf : PerturbData B s₀ r₀ f ε)
    (hε1 : ε ≤ 1) (hI : I ∈ B) (hS : I ∈ sSet B B') (hε : ε ≤ epsT h B B' s₀ r₀) :
    IsUnit (KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I)
      (frequencyMap h I)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I)
      (frequencyMap h I))⁻¹‖ ≤ 2 * ShConst h B B' := by
  have hne : B'.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have : I ∈ cthickening (dB B B' / 2) (closure (∅ : Set (Fin 2 → ℝ))) := hcon ▸ hS
    rw [closure_empty, cthickening_empty] at this
    exact this
  obtain ⟨-, -, -, -, -, -, hSh, hbd⟩ := compact hd hne
  have hSbd := (hbd I hS).2.2
  have hdet : (KAM.Iso.borderedHessian h I).det ≠ 0 :=
    hd.iso I (subset_realAct_charts hd.hr hI)
  have hAu : IsUnit ((KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ))).det := by
    rw [det_map_ofReal']
    exact (Complex.ofReal_ne_zero.2 hdet).isUnit
  have hAinv : ‖((KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)))⁻¹‖ ≤
      ShConst h B B' := by
    rw [inv_map_ofReal, norm_map_ofReal]
    exact hSbd
  have hF2 : 0 < Fconst 2 s₀ r₀ 2 := by
    have hδ := KAM.Head.deltaStar_pos hd.hs hd.hr
    unfold KAM.Head.Fconst
    rw [KAM.Head.cbar_eq]
    positivity
  have hΔ := norm_extendedAverage_sub_le hd hf hε1 hI
  have hε' : ε ≤ 1 / (4 * ShConst h B B' * Fconst 2 s₀ r₀ 2) := hε
  have h4 : 4 * ShConst h B B' * Fconst 2 s₀ r₀ 2 * ε ≤ 1 := by
    have hpos : 0 < 4 * ShConst h B B' * Fconst 2 s₀ r₀ 2 := by positivity
    rwa [le_div_iff₀ hpos, mul_comm] at hε'
  have hsmall : ShConst h B B' * ‖KAM.Iso.extendedTorsionAverage (totalH h f)
      (unperturbedTorus I) (frequencyMap h I) -
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ))‖ ≤ 1 / 2 := by
    calc _ ≤ ShConst h B B' * (2 * Fconst 2 s₀ r₀ 2 * ε) :=
          mul_le_mul_of_nonneg_left hΔ hSh.le
      _ ≤ 1 / 2 := by nlinarith
  have key := KAM.Iso.Linear.neumann_fintype hAu hAinv hsmall
  rw [add_sub_cancel] at key
  exact ⟨key.1, key.2.1⟩

/-- `‖Ē_{h+f}(K⁰) - h(I)‖ ≤ ε`. -/
theorem norm_energyAverage_sub_le (hd : HeadData B s₀ r₀ h B' η)
    (hf : PerturbData B s₀ r₀ f ε) (hI : I ∈ B) :
    ‖KAM.Iso.energyAverage (totalH h f) (unperturbedTorus I) - h (toC I)‖ ≤ ε := by
  have hg : Continuous fun x : Fin 2 → ℝ => f (toC x, toC I) := by
    have hg1 : Continuous fun x : Fin 2 → ℝ =>
        ((toC x, toC I) : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).prodMk
        continuous_const
    exact hf.holo.continuousOn.comp_continuous hg1 fun x =>
      KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B (real_mem hd.hs hd.hr hI x)
  have hav : KAM.Iso.energyAverage (totalH h f) (unperturbedTorus I) =
      h (toC I) + torusAverage fun x => f (toC x, toC I) :=
    integral_const_add hg (h (toC I))
  rw [hav, add_sub_cancel_left]
  refine norm_torusAverage_le fun x _ => hf.bound _ ?_
  exact KAM.Head.h1_domainD_subset_domain 2 hd.hs hd.hr B (real_mem hd.hs hd.hr hI x)

end TorusAux


/-! ### `torus` -/

/-- `bpI:p3:torus` (a)–(e) for `K⁰(θ) = (θ, I)`, `ω = s'ω* = ∇h(I)`. -/
theorem torus (hd : HeadData B s₀ r₀ h B' η) {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ}
    (hf : PerturbData B s₀ r₀ f ε) (hε1 : ε ≤ 1) {I ωs : Fin 2 → ℝ} (hI : I ∈ B) {s' : ℝ}
    (hgrad : frequencyMap h I = s' • ωs) :
    (Differentiable ℂ (unperturbedTorus I) ∧ IsPrimaryOnStrip (unperturbedTorus I) (min s₀ 1 / 2) ∧
      IsRealOnReals (unperturbedTorus I) ∧
      (∀ θ ∈ complexStrip 2 (min s₀ 1 / 2), unperturbedTorus I θ ∈ fractD B s₀ r₀) ∧
      (∀ θ, ‖fderiv ℂ (unperturbedTorus I) θ‖ = 1 ∧ gramMatrix (unperturbedTorus I) θ = 1 ∧
        ∀ j, normalFrame (unperturbedTorus I) θ j = (0, Pi.single j 1)) ∧
      ∀ θ ∈ complexStrip 2 (rhoIso s₀),
        Metric.ball (unperturbedTorus I θ) (muParam s₀ r₀) ⊆ fractD B s₀ r₀) ∧
    (∀ θ ∈ complexStrip 2 (min s₀ 1 / 2),
      invarianceError (totalH h f) (unperturbedTorus I) (s' • ωs) θ =
        hamiltonianVectorFieldℂ f (θ, toC I) ∧
      ‖invarianceError (totalH h f) (unperturbedTorus I) (s' • ωs) θ‖ ≤ Fconst 2 s₀ r₀ 1 * ε) ∧
    (∀ θ ∈ complexStrip 2 (min s₀ 1 / 2),
      KAM.Iso.extendedTorsion (totalH h f) (unperturbedTorus I) (s' • ωs) θ =
        (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) + flatRemainder f I θ ∧
      ‖flatRemainder f I θ‖ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε) ∧
    ‖KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I) (s' • ωs) -
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ))‖ ≤ 2 * Fconst 2 s₀ r₀ 2 * ε ∧
    (I ∈ sSet B B' → ε ≤ epsT h B B' s₀ r₀ →
      IsUnit (KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I) (s' • ωs)).det ∧
      ‖(KAM.Iso.extendedTorsionAverage (totalH h f) (unperturbedTorus I) (s' • ωs))⁻¹‖ ≤
        2 * ShConst h B B') ∧
    ‖KAM.Iso.energyAverage (totalH h f) (unperturbedTorus I) - h (toC I)‖ ≤ ε := by
  rw [← hgrad]
  have hD := (hypothesis_d hd hf hε1).2.2.2.2.2.2
  refine ⟨⟨KAM.Head.differentiable_unperturbedTorus I,
      KAM.Head.isPrimaryOnStrip_unperturbedTorus I _,
      KAM.Head.isRealOnReals_unperturbedTorus I,
      fun θ hθ => TorusAux.unperturbed_mem hd.hr hI hθ,
      fun θ => ⟨KAM.Head.norm_fderiv_unperturbedTorus (by norm_num) I θ,
        KAM.Head.gramMatrix_unperturbedTorus I θ, KAM.Head.normalFrame_unperturbedTorus I θ⟩,
      fun θ hθ => ?_⟩, fun θ hθ => ?_, fun θ hθ => ?_, ?_, fun hS hεT => ?_, ?_⟩
  · refine (Metric.ball_subset_ball ?_).trans
      (KAM.Head.ball_unperturbedTorus_subset_domainD (s₀ := s₀) hd.hr hI hθ)
    have := KAM.Head.deltaStar_pos hd.hs hd.hr
    unfold KAM.Head.muParam
    linarith
  · rw [TorusAux.invarianceError_flat hd hf hI hθ]
    exact ⟨rfl, (hD _ (TorusAux.unperturbed_mem hd.hr hI hθ)).2.2⟩
  · exact ⟨TorusAux.extendedTorsion_flat hd hf hI hθ,
      TorusAux.norm_flatRemainder_le hd hf hε1 hI hθ⟩
  · exact TorusAux.norm_extendedAverage_sub_le hd hf hε1 hI
  · exact TorusAux.extendedAverage_inv hd hf hε1 hI hS hεT
  · exact TorusAux.norm_energyAverage_sub_le hd hf hI

end KAM.Iso.Charts
