/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Strip.Bridges
public import KAM.ODE.Uniqueness
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn

/-!
# Part 5: the real Hamiltonian

Blueprint `bpI:p5:real-ham`: the
frozen `KAM.realHamiltonian h f` on `ℝ² × B`, for `h` and `f` as in I-HEAD.

* `isOpen_realAct`, `subset_realAct`, `toC_pair_mem_fractD`: the real points of the domains.
* (a) `realHam_eq`, `realHam_contDiffOn`, `realHam_periodic`: the value `h(ι I) + f(ι θ, ι I)`,
  smoothness on `ℝ² × U` (through `KAM.holomorphic_regularity_of_finiteDimensional`), and
  `ℤ²`-periodicity in the angles.
* (b) `realHam_field_eq`: `X_ℝ = X_H` at real points (`KAM.hamiltonian_real`).
* (c) `realHam_field_contDiffOn`, `realHam_field_periodic`, `realHam_solution_iff`: the ODE
  layer applies to `X_ℝ` on `ℝ² × B`.
* (d) `realHam_fderiv_bound`: the real derivative of `I ↦ Re f(ι φ, ι I)` is bounded by `F₁ ε`.
* (e) `realHam_sub_le`: `|H_ℝ - Re h ∘ ι| ≤ ε`.
* `realHam_energy_const`, `realHam_unique`: energy conservation and uniqueness for `H_ℝ`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Iso.Confinement

open KAM KAM.ODE

section RealHam

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ}

/-- `actionNbhd B r` is open: a union of open balls around the points `ι J`, `J ∈ B`. -/
private theorem isOpen_actionNbhd_two (B : Set (Fin 2 → ℝ)) (r : ℝ) :
    IsOpen (actionNbhd B r) := by
  have : actionNbhd B r = ⋃ J ∈ B, ball (toC J) r := by
    ext I
    simp only [actionNbhd, Set.mem_ofPred_eq, Set.mem_iUnion, mem_ball, dist_eq_norm,
      exists_prop]
  rw [this]
  exact isOpen_biUnion fun J _ => isOpen_ball

/-- The domain `T_{s₀} × B_{r₀}` of `f` is open. -/
private theorem isOpen_domain (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) :
    IsOpen (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
  (isOpen_complexStrip 2 s₀).prod (isOpen_actionNbhd_two B r₀)

theorem isOpen_realAct (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) : IsOpen (realAct B r₀) :=
  (isOpen_actionNbhd_two B r₀).preimage
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

theorem subset_realAct (hr : 0 < r₀) : B ⊆ realAct B r₀ := fun I hI =>
  ⟨I, hI, by simpa using hr⟩

/-- Real points of `T_{s₀} × B_{r₀/2}` over `ℝ² × B` (`s₀, r₀ > 0`): used for `fractD`. -/
theorem toC_pair_mem_fractD (hs : 0 < s₀) (hr : 0 < r₀) (φ : Fin 2 → ℝ) {I : Fin 2 → ℝ}
    (hI : I ∈ B) : (toC φ, toC I) ∈ fractD B s₀ r₀ := by
  refine ⟨fun i => ?_, I, hI, ?_⟩
  · have : 0 < min s₀ 1 / 2 := half_pos (lt_min hs one_pos)
    simpa using this
  · simpa using half_pos hr

/-- Real points of the domain of `f` over `ℝ² × U`. -/
private theorem toC_pair_mem_domain (hs : 0 < s₀) (φ : Fin 2 → ℝ) {I : Fin 2 → ℝ}
    (hI : I ∈ realAct B r₀) : (toC φ, toC I) ∈ complexStrip 2 s₀ ×ˢ actionNbhd B r₀ :=
  ⟨realInclusion_mem_complexStrip hs φ, hI⟩

/-- (a) values: `H_ℝ(θ, I) = h(ι I) + f(ι θ, ι I)` on `ℝ² × U`, as complex numbers. -/
theorem realHam_eq (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) {z : P2}
    (hz : z.2 ∈ realAct B r₀) :
    ((realHamiltonian h f z : ℝ) : ℂ) = h (toC z.2) + f (toC z.1, toC z.2) := by
  have h1 := hb.real z.2 hz
  have h2 := hf.real z.1 z.2 hz
  apply Complex.ext
  · simp [realHamiltonian]
  · simp [realHamiltonian, h1, h2]

/-- `H_ℝ` is `(h + f) ∘ ι₂` followed by the real part (definitionally). -/
private theorem realHamiltonian_eq_re_comp :
    realHamiltonian h f = fun z => (totalH h f (realInclusion₂ 2 z)).re := rfl

/-- `totalH h f` is holomorphic on the domain `T_{s₀} × B_{r₀}` of `f`. -/
private theorem differentiableOn_totalH (hb : BaseData B s₀ r₀ h)
    (hf : PerturbData B s₀ r₀ f ε) :
    DifferentiableOn ℂ (totalH h f) (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) := by
  have h1 : DifferentiableOn ℂ (fun z : (Fin 2 → ℂ) × (Fin 2 → ℂ) => h z.2)
      (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
    hb.holo.comp differentiableOn_snd fun z hz => hz.2
  exact h1.add hf.holo

/-- (a) `H_ℝ` is `C^∞` on the open set `ℝ² × U`. -/
theorem realHam_contDiffOn (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) :
    ContDiffOn ℝ ∞ (realHamiltonian h f) (univ ×ˢ realAct B r₀) := by
  have hC : ContDiffOn ℂ ∞ (totalH h f) (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
    (holomorphic_regularity_of_finiteDimensional (isOpen_domain B s₀ r₀)
      (differentiableOn_totalH hb hf)).2.2.1
  have hR : ContDiffOn ℝ ∞ (totalH h f) (complexStrip 2 s₀ ×ˢ actionNbhd B r₀) :=
    hC.restrict_scalars ℝ
  have hcomp : ContDiffOn ℝ ∞ (fun z => totalH h f (realInclusion₂ 2 z))
      (univ ×ˢ realAct B r₀) :=
    hR.comp (realInclusion₂ 2).contDiff.contDiffOn fun z hz =>
      toC_pair_mem_domain hb.hs z.1 hz.2
  exact Complex.reCLM.contDiff.comp_contDiffOn hcomp

/-- (a) `ℤ²`-periodicity in the angles. -/
theorem realHam_periodic (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (k : Fin 2 → ℤ) {z : P2} (hz : z.2 ∈ realAct B r₀) :
    realHamiltonian h f (z + angleShift k) = realHamiltonian h f z := by
  have hper : f (toC z.1 + (fun i => (k i : ℂ)), toC z.2) = f (toC z.1, toC z.2) :=
    hf.periodic (toC z.1, toC z.2) (toC_pair_mem_domain hb.hs z.1 hz) k
  have hshift : toC (z + angleShift k).1 = toC z.1 + fun i => (k i : ℂ) := by
    ext i
    change ((z.1 i + (k i : ℝ) : ℝ) : ℂ) = (z.1 i : ℂ) + ((k i : ℤ) : ℂ)
    push_cast
    rfl
  have hsnd : (z + angleShift k).2 = z.2 := by simp [angleShift]
  show (h (toC (z + angleShift k).2) + f (toC (z + angleShift k).1,
    toC (z + angleShift k).2)).re = (h (toC z.2) + f (toC z.1, toC z.2)).re
  rw [hsnd, hshift, hper]

/-- Real points of the domain, in the form used by `hamiltonian_real`. -/
private theorem mem_domain_of_realAct (hb : BaseData B s₀ r₀ h) {z : P2}
    (hz : z.2 ∈ realAct B r₀) :
    realInclusion₂ 2 z ∈ complexStrip 2 s₀ ×ˢ actionNbhd B r₀ :=
  toC_pair_mem_domain hb.hs z.1 hz

/-- (b) `X_ℝ(z) = X_H(z)` at real points of `ℝ² × U`, `H = h + f` (identification `ι₂`). -/
theorem realHam_field_eq (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) {z : P2}
    (hz : z.2 ∈ realAct B r₀) :
    realInclusion₂ 2 (hamiltonianVectorField (realHamiltonian h f) z) =
      hamiltonianVectorFieldℂ (totalH h f) (realInclusion₂ 2 z) := by
  refine (hamiltonian_real (isOpen_domain B s₀ r₀) (differentiableOn_totalH hb hf) ?_
    (mem_domain_of_realAct hb hz) (Filter.Eventually.of_forall fun y => rfl)).1.2
  intro y hy
  have h1 := hb.real y.2 hy.2
  have h2 := hf.real y.1 y.2 hy.2
  show (h (toC y.2) + f (toC y.1, toC y.2)).im = 0
  rw [Complex.add_im, h1, h2, add_zero]

/-- The open set `ℝ² × U` contains `ℝ² × B`. -/
private theorem prod_subset (hr : 0 < r₀) :
    (univ : Set (Fin 2 → ℝ)) ×ˢ B ⊆ univ ×ˢ realAct B r₀ :=
  prod_mono subset_rfl (subset_realAct hr)

/-- `ℝ² × U` is open. -/
private theorem isOpen_prod_realAct (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) :
    IsOpen ((univ : Set (Fin 2 → ℝ)) ×ˢ realAct B r₀) :=
  isOpen_univ.prod (isOpen_realAct B r₀)

/-- `H_ℝ` is `C²` on `ℝ² × U`. -/
private theorem realHam_contDiffOn_two (hb : BaseData B s₀ r₀ h)
    (hf : PerturbData B s₀ r₀ f ε) :
    ContDiffOn ℝ 2 (realHamiltonian h f) (univ ×ˢ realAct B r₀) :=
  (realHam_contDiffOn hb hf).of_le (by norm_cast)

/-- (c) `X_ℝ` is `C¹` on `W_B = ℝ² × B`. -/
theorem realHam_field_contDiffOn (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) :
    ContDiffOn ℝ 1 (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) :=
  (ham_reduction (isOpen_prod_realAct B r₀) (prod_subset hb.hr)
    (realHam_contDiffOn_two hb hf)).1

/-- (c) `X_ℝ` is `ℤ²`-periodic in the angles on `W_B`. -/
theorem realHam_field_periodic (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (k : Fin 2 → ℤ) {z : P2} (hz : z ∈ (univ : Set (Fin 2 → ℝ)) ×ˢ B) :
    hamiltonianVectorField (realHamiltonian h f) (z + angleShift k) =
      hamiltonianVectorField (realHamiltonian h f) z := by
  have hWk : ∀ k : Fin 2 → ℤ, (fun x => x + angleShift k) '' ((univ : Set (Fin 2 → ℝ)) ×ˢ
      realAct B r₀) = univ ×ˢ realAct B r₀ := by
    intro k
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_univ _, by simpa [angleShift] using hy.2⟩
    · intro hx
      refine ⟨x - angleShift k, ⟨mem_univ _, by simpa [angleShift] using hx.2⟩, ?_⟩
      simp
  exact (ham_periodic (isOpen_prod_realAct B r₀) hWk
    (fun k x hx => realHam_periodic hb hf k hx.2)).1 k z (prod_subset hb.hr hz)

/-- (c) `IsHamiltonianSolutionOn H_ℝ B J z ↔ IsSolutionIn X_ℝ W_B J z`, for all `J`, `z`. -/
theorem realHam_solution_iff (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (J : Set ℝ) (z : ℝ → P2) :
    KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B J z ↔
      IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) J z :=
  ((ham_reduction (isOpen_prod_realAct B r₀) (prod_subset hb.hr)
    (realHam_contDiffOn_two hb hf)).2 J z).2.symm

/-- (d) `|∂_t f(φ, I + t v)|_{t=0} ≤ F₁ ε ‖v‖`, as the operator norm of the real derivative of
`I ↦ Re f(ι φ, ι I)`, for `I ∈ B`; `hD` is the derivative bound of `bpI:p3:hypothesis-d`; `hf`
(holomorphy of `f`) is REQUIRED: without it the total `fderiv` is `0` for non-holomorphic `f` and
the bound is false. -/
theorem realHam_fderiv_bound (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) {F₁ : ℝ}
    (hD : ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε) (φ : Fin 2 → ℝ) {I : Fin 2 → ℝ}
    (hI : I ∈ B) :
    DifferentiableAt ℝ (fun x : Fin 2 → ℝ => (f (toC φ, toC x)).re) I ∧
      ‖fderiv ℝ (fun x : Fin 2 → ℝ => (f (toC φ, toC x)).re) I‖ ≤ F₁ * ε := by
  have hmem := toC_pair_mem_domain (B := B) (r₀ := r₀) hb.hs φ (subset_realAct hb.hr hI)
  have hfd : DifferentiableAt ℂ f (toC φ, toC I) :=
    hf.holo.differentiableAt ((isOpen_domain B s₀ r₀).mem_nhds hmem)
  have hg : HasFDerivAt (fun x : Fin 2 → ℝ => ((toC φ, toC x) :
      (Fin 2 → ℂ) × (Fin 2 → ℂ)))
      ((0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℂ)).prod (realInclusion 2)) I :=
    (hasFDerivAt_const (toC φ) I).prodMk (realInclusion 2).hasFDerivAt
  have hcomp := (hfd.hasFDerivAt.restrictScalars ℝ).comp I hg
  have hre := Complex.reCLM.hasFDerivAt.comp I hcomp
  refine ⟨hre.differentiableAt, ?_⟩
  have hfd' := hre.fderiv
  change ‖fderiv ℝ (Complex.reCLM ∘ f ∘ fun x : Fin 2 → ℝ => (toC φ, toC x)) I‖ ≤ F₁ * ε
  rw [hfd']
  have hbound := hD _ (toC_pair_mem_fractD hb.hs hb.hr φ hI)
  have hnn : 0 ≤ F₁ * ε := (norm_nonneg _).trans hbound
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.prod_apply, zero_apply]
  calc ‖Complex.reCLM (fderiv ℂ f (toC φ, toC I) (0, realInclusion 2 v))‖
      ≤ ‖fderiv ℂ f (toC φ, toC I) (0, realInclusion 2 v)‖ := by
        simpa using Complex.abs_re_le_norm (fderiv ℂ f (toC φ, toC I) (0, realInclusion 2 v))
    _ ≤ ‖fderiv ℂ f (toC φ, toC I)‖ * ‖((0, realInclusion 2 v) :
          (Fin 2 → ℂ) × (Fin 2 → ℂ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (F₁ * ε) * ‖v‖ := by
        have : ‖((0, realInclusion 2 v) : (Fin 2 → ℂ) × (Fin 2 → ℂ))‖ = ‖v‖ := by
          simp [Prod.norm_def, norm_realInclusion]
        rw [this]
        exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- (e) `|H_ℝ - Re h ∘ ι| ≤ ε` on `ℝ² × U`. -/
theorem realHam_sub_le (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) {z : P2}
    (hz : z.2 ∈ realAct B r₀) : |realHamiltonian h f z - realPart h z.2| ≤ ε := by
  have hre : realHamiltonian h f z - realPart h z.2 = (f (toC z.1, toC z.2)).re := by
    simp [realHamiltonian, realPart]
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans (hf.bound _ (toC_pair_mem_domain hb.hs z.1 hz))

/-- Energy conservation along `IsSolutionIn` in `W_B` (`bpN:p3:ham-energy` for `H_ℝ`). -/
theorem realHam_energy_const (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    {J : Set ℝ} (hJ : J.OrdConnected) {z : ℝ → P2}
    (hz : IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) J z) :
    ∀ t ∈ J, ∀ t' ∈ J, realHamiltonian h f (z t) = realHamiltonian h f (z t') := by
  have hsol := (realHam_solution_iff hb hf J z).2 hz
  exact ham_energy hJ fun t ht => (hsol t ht).2

/-- The uniqueness clause of I-HEAD for `H_ℝ`: two solutions in `B` on `(a, b) ∋ 0` agreeing at
`0` agree (`gen_uniqueness` on `Ioo a b`; no confinement of the competitor). -/
theorem realHam_unique (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε) {a b : ℝ}
    (ha : a < 0) (hb0 : 0 < b) {y z : ℝ → P2} (h0 : y 0 = z 0)
    (hy : KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B (Ioo a b) y)
    (hz : KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B (Ioo a b) z) :
    ∀ t ∈ Ioo a b, y t = z t := by
  intro t ht
  have hW := isOpen_prod_realAct B r₀
  have hmono : ∀ {w : ℝ → P2}, IsSolutionIn (hamiltonianVectorField (realHamiltonian h f))
      (univ ×ˢ B) (Ioo a b) w → IsSolutionIn (hamiltonianVectorField (realHamiltonian h f))
      (univ ×ˢ realAct B r₀) (Ioo a b) w := fun hw s hs =>
    ⟨prod_subset hb.hr (hw s hs).1, (hw s hs).2⟩
  exact gen_uniqueness hW (ham_smooth_c1 hW (realHam_contDiffOn_two hb hf))
    ordConnected_Ioo ⟨ha, hb0⟩ (hmono ((realHam_solution_iff hb hf _ y).1 hy))
    (hmono ((realHam_solution_iff hb hf _ z).1 hz)) h0 ht

end RealHam

end KAM.Iso.Confinement
