/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
public import Mathlib.Analysis.Matrix.Normed
import KAM.Head.Adapters
import KAM.Matrix.Norms
import KAM.Strip.Bridges

/-!
# The frequency map

Blueprint Part 4, `bp:p4:freq-map`. With `U = {I ∈ ℝⁿ : ι I ∈ B_{r₀}}`
(`KAM.Head.realDomain`) and `g = KAM.frequencyMap h`:

* (i) `U` is open and contains the closure of `B`
  (`KAM.Head.isOpen_realDomain`, `KAM.Head.closure_subset_realDomain`, step `step:p4:fm-domain`);
* (ii) on `U` the complex partials `∂ᵢ h (ι I)` are real and `g I = ∇h (ι I)`
  (`KAM.Head.frequencyMap_eq_gradC`, step `step:p4:fm-gradient`);
* (iii) `g` is differentiable on `U` and `D g (I)` is the real symmetric Hessian
  (`KAM.Head.differentiableOn_frequencyMap`, `KAM.Head.fderiv_frequencyMap_eq_hessian`,
  `KAM.Head.hessian_transpose`, `KAM.Head.hessian_im`, step `step:p4:fm-hessian`);
* (iv) bounds by `H₁`, `H₂` on `B_{r₀/2}` (`KAM.Head.norm_frequencyMap_le`,
  `KAM.Head.norm_hessian_le`, step `step:p4:fm-bounds`);
* (v) the Lipschitz bound on `B` and the boundedness of `g (B)`
  (`KAM.Head.frequencyMap_lipschitz`, step `step:p4:fm-lipschitz`).

The theorem `KAM.Head.freq_map` assembles the five items.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}

/-! ### Real inclusion and the real part -/

theorem realInclusion_eq (x : Fin n → ℝ) : realInclusion n x = fun i => (x i : ℂ) := rfl

/-- The real derivative of the real part of a function that is real near a real point is the
(real) complex derivative: if `F` is complex differentiable at `ι I` and real on a neighbourhood
of `I`, then `DF(ι I)(ι v) = ((D (Re ∘ F ∘ ι)(I)) v : ℂ)`. -/
theorem fderiv_realInclusion_of_real {F : (Fin n → ℂ) → ℂ} {I : Fin n → ℝ}
    (hF : DifferentiableAt ℂ F (realInclusion n I))
    (hreal : ∀ᶠ J in 𝓝 I, (F (realInclusion n J)).im = 0) (v : Fin n → ℝ) :
    fderiv ℂ F (realInclusion n I) (realInclusion n v) =
      ((fderiv ℝ (fun J => (F (realInclusion n J)).re) I v : ℝ) : ℂ) := by
  have hφ : HasFDerivAt (fun J => F (realInclusion n J))
      (((fderiv ℂ F (realInclusion n I)).restrictScalars ℝ).comp (realInclusion n)) I :=
    (hF.hasFDerivAt.restrictScalars ℝ).comp I (realInclusion n).hasFDerivAt
  have hre := Complex.reCLM.hasFDerivAt.comp I hφ
  have hofReal := Complex.ofRealCLM.hasFDerivAt.comp I hre
  have heq : (fun J => F (realInclusion n J)) =ᶠ[𝓝 I]
      (Complex.ofRealCLM ∘ Complex.reCLM ∘ fun J => F (realInclusion n J)) := by
    filter_upwards [hreal] with J hJ
    exact Complex.ext (by simp) (by simpa using hJ)
  have hφ' := hofReal.congr_of_eventuallyEq heq
  have hu := hφ.unique hφ'
  have hv := congrArg (fun L => L v) hu
  have hre' : fderiv ℝ (fun J => (F (realInclusion n J)).re) I =
      Complex.reCLM.comp (((fderiv ℂ F (realInclusion n I)).restrictScalars ℝ).comp
        (realInclusion n)) := hre.fderiv
  rw [hre']
  simpa using hv

/-- Real partial derivatives: `(Re ∘ F ∘ ι)` is differentiable where `F` is. -/
theorem differentiableAt_re_comp {F : (Fin n → ℂ) → ℂ} {I : Fin n → ℝ}
    (hF : DifferentiableAt ℂ F (realInclusion n I)) :
    DifferentiableAt ℝ (fun J => (F (realInclusion n J)).re) I :=
  (Complex.reCLM.differentiableAt).comp I
    ((hF.restrictScalars ℝ).comp I (realInclusion n).differentiableAt)

/-- `ι (e_i) = e_i`. -/
theorem realInclusion_single (i : Fin n) :
    realInclusion n (Pi.single i 1) = (Pi.single i 1 : Fin n → ℂ) := by
  ext k
  by_cases hk : k = i <;> simp [hk]

/-- `‖e_i‖ ≤ 1`. -/
theorem norm_single_one_le (i : Fin n) : ‖(Pi.single i 1 : Fin n → ℂ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
  by_cases hk : k = i <;> simp [hk]

/-! ### Step `step:p4:fm-domain`: the real domain -/

/-- `U = ι⁻¹ (B_{r₀})` is open. -/
theorem isOpen_realDomain (B : Set (Fin n → ℝ)) (r₀ : ℝ) : IsOpen (realDomain B r₀) :=
  (isOpen_actionNbhd B r₀).preimage (realInclusion n).continuous

/-- `closure B ⊆ U`, for `r₀ > 0`. -/
theorem closure_subset_realDomain {r₀ : ℝ} (hr₀ : 0 < r₀) (B : Set (Fin n → ℝ)) :
    closure B ⊆ realDomain B r₀ := by
  intro J hJ
  obtain ⟨I, hI, hdist⟩ := Metric.mem_closure_iff.1 hJ r₀ hr₀
  refine ⟨I, hI, ?_⟩
  show ‖realInclusion n J - realInclusion n I‖ < r₀
  rw [← map_sub, norm_realInclusion, ← dist_eq_norm]
  exact hdist

/-- A real point whose image lies in `B_{r₀/2}` lies in `U`. -/
theorem mem_realDomain_of_half {r₀ : ℝ} (hr₀ : 0 < r₀) {I : Fin n → ℝ}
    (hI : realInclusion n I ∈ actionNbhd B (r₀ / 2)) : I ∈ realDomain B r₀ :=
  actionNbhd_mono B (by linarith) hI

/-- A point of `B` lies in `U`'s half-neighbourhood: `ι I ∈ B_{r₀/2}` for `I ∈ B`. -/
theorem realInclusion_mem_half {r₀ : ℝ} (hr₀ : 0 < r₀) {I : Fin n → ℝ} (hI : I ∈ B) :
    realInclusion n I ∈ actionNbhd B (r₀ / 2) :=
  ⟨I, hI, by
    show ‖realInclusion n I - realInclusion n I‖ < r₀ / 2
    rw [sub_self, norm_zero]; linarith⟩

/-! ### Step `step:p4:fm-gradient`: the frozen frequency map is the gradient -/

section Gradient

variable (hD : Data τ s₀ r₀ B h Lh)
include hD

/-- `h` is complex differentiable at `ι I` for `I ∈ U`. -/
theorem differentiableAt_h {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    DifferentiableAt ℂ h (realInclusion n I) :=
  hD.holo.differentiableAt ((isOpen_actionNbhd B r₀).mem_nhds hI)

/-- `h ∘ ι` is real near every point of `U`. -/
theorem eventually_im_h {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    ∀ᶠ J in 𝓝 I, (h (realInclusion n J)).im = 0 := by
  filter_upwards [(isOpen_realDomain B r₀).mem_nhds hI] with J hJ
  exact hD.real J hJ

/-- Blueprint `bp:p4:freq-map` (ii) (step `step:p4:fm-gradient`). -/
theorem frequencyMap_eq_gradC {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    (fun i => ((frequencyMap h I i : ℝ) : ℂ)) = gradC h (fun i => (I i : ℂ)) := by
  ext i
  have h1 := fderiv_realInclusion_of_real (differentiableAt_h hD hI) (eventually_im_h hD hI)
    (Pi.single i 1)
  rw [realInclusion_single] at h1
  simp only [gradC]
  exact h1.symm

/-- The partial derivatives `∂_i h` of a holomorphic `h` are holomorphic. -/
theorem differentiableOn_partial (i : Fin n) :
    DifferentiableOn ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (actionNbhd B r₀) :=
  (differentiableOn_fderiv_of_isOpen (isOpen_actionNbhd B r₀) hD.holo).clm_apply
    (differentiableOn_const _)

/-- `∂_i h` is complex differentiable at `ι I` for `I ∈ U`. -/
theorem differentiableAt_partial {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (i : Fin n) :
    DifferentiableAt ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I) :=
  (differentiableOn_partial hD i).differentiableAt ((isOpen_actionNbhd B r₀).mem_nhds hI)

/-- Blueprint `bp:p4:freq-map` (ii): the partials `∂_i h (ι I)` are real. -/
theorem partial_im {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (i : Fin n) :
    (fderiv ℂ h (realInclusion n I) (Pi.single i 1)).im = 0 := by
  have h1 : ((frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (realInclusion n I) (Pi.single i 1) :=
    congrFun (frequencyMap_eq_gradC hD hI) i
  rw [← h1]
  exact Complex.ofReal_im _

/-- `∂_i h ∘ ι` is real near every point of `U`. -/
theorem eventually_im_partial {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (i : Fin n) :
    ∀ᶠ J in 𝓝 I, ((fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n J)).im = 0 := by
  filter_upwards [(isOpen_realDomain B r₀).mem_nhds hI] with J hJ
  exact partial_im hD hJ i

/-- Near `I ∈ U`, the `i`-th coordinate of `g` is the real part of `∂_i h ∘ ι`. -/
theorem frequencyMap_apply_eventuallyEq {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (i : Fin n) :
    (fun J => frequencyMap h J i) =ᶠ[𝓝 I]
      fun J => ((fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n J)).re := by
  filter_upwards [(isOpen_realDomain B r₀).mem_nhds hI] with J hJ
  have h1 : ((frequencyMap h J i : ℝ) : ℂ) = fderiv ℂ h (realInclusion n J) (Pi.single i 1) :=
    congrFun (frequencyMap_eq_gradC hD hJ) i
  show frequencyMap h J i = (fderiv ℂ h (realInclusion n J) (Pi.single i 1)).re
  rw [← h1]
  exact (Complex.ofReal_re _).symm

/-- Blueprint `bp:p4:freq-map` (iii): `g` is differentiable at every point of `U`. -/
theorem differentiableAt_frequencyMap {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    DifferentiableAt ℝ (frequencyMap h) I := by
  rw [differentiableAt_pi]
  intro i
  exact (differentiableAt_re_comp (differentiableAt_partial hD hI i)).congr_of_eventuallyEq
    (frequencyMap_apply_eventuallyEq hD hI i)

/-- Blueprint `bp:p4:freq-map` (iii): `g` is differentiable on `U`. -/
theorem differentiableOn_frequencyMap : DifferentiableOn ℝ (frequencyMap h) (realDomain B r₀) :=
  fun _ hI => (differentiableAt_frequencyMap hD hI).differentiableWithinAt

/-- The row `i` of `D g (I) v`, as a complex number, is `D (∂_i h) (ι I) (ι v)`. -/
theorem fderiv_frequencyMap_apply {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (v : Fin n → ℝ)
    (i : Fin n) :
    ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ) =
      fderiv ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I) (realInclusion n v) := by
  have hpi : fderiv ℝ (frequencyMap h) I v i = fderiv ℝ (fun J => frequencyMap h J i) I v := by
    rw [fderiv_pi (fun k => (differentiableAt_pi.1 (differentiableAt_frequencyMap hD hI)) k)]
    rfl
  rw [hpi, (frequencyMap_apply_eventuallyEq hD hI i).fderiv_eq,
    fderiv_realInclusion_of_real (differentiableAt_partial hD hI i)
      (eventually_im_partial hD hI i) v]

end Gradient

/-! ### Step `step:p4:fm-hessian`: the Hessian -/

/-- The Hessian acts on a complex vector `w` row by row as `D (∂_i h) (z) w`. -/
theorem hessian_mulVec_apply (h : (Fin n → ℂ) → ℂ) (z w : Fin n → ℂ) (i : Fin n) :
    (hessian h z *ᵥ w) i = fderiv ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) z w := by
  simp only [Matrix.mulVec, dotProduct, hessian, Matrix.of_apply]
  have hw : w = ∑ j, w j • (Pi.single j 1 : Fin n → ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

section Hessian

variable (hD : Data τ s₀ r₀ B h Lh)
include hD

/-- Blueprint `bp:p4:freq-map` (iii): `D g (I) v = ∇²h (ι I) v`. -/
theorem fderiv_frequencyMap_eq_hessian {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀)
    (v : Fin n → ℝ) :
    (fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)) =
      hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ) := by
  ext i
  rw [fderiv_frequencyMap_apply hD hI v i]
  exact (hessian_mulVec_apply h (realInclusion n I) (realInclusion n v) i).symm

/-- Blueprint `bp:p4:freq-map` (iii): the Hessian is symmetric (mixed complex partials of a
holomorphic function commute). -/
theorem hessian_transpose {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    (hessian h (fun i => (I i : ℂ)))ᵀ = hessian h (fun i => (I i : ℂ)) := by
  ext i j
  have hsymm := fderiv_apply_comm_of_differentiableOn (isOpen_actionNbhd B r₀) hD.holo
    (z := realInclusion n I) hI (Pi.single j 1) (Pi.single i 1)
  simp only [Matrix.transpose_apply, hessian, Matrix.of_apply]
  exact hsymm.symm

/-- Blueprint `bp:p4:freq-map` (iii): the entries of the Hessian are real. -/
theorem hessian_im {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) (i j : Fin n) :
    (hessian h (fun i => (I i : ℂ)) i j).im = 0 := by
  have h1 := fderiv_frequencyMap_apply hD hI (Pi.single j 1) i
  rw [realInclusion_single] at h1
  have h2 : hessian h (fun i => (I i : ℂ)) i j =
      fderiv ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I) (Pi.single j 1) := rfl
  rw [h2, ← h1]
  exact Complex.ofReal_im _

end Hessian

/-! ### Step `step:p4:fm-bounds`: bounds -/

section Bounds

variable (hD : Data τ s₀ r₀ B h Lh)
include hD

theorem Hconst_nonneg (j : ℕ) : 0 ≤ Hconst s₀ r₀ B h j := by
  have hδ := deltaStar_pos hD.s₀_pos hD.r₀_pos
  unfold Hconst
  have := hBound_nonneg h B r₀
  rw [cbar_eq]
  positivity

/-- `‖iteratedFDeriv ℂ j h z‖ ≤ H_j` on `B_{r₀/2}` (Lemma `bp:p4:derivative-bounds` (b), applied
to the perturbation `f = 0`). -/
theorem norm_iteratedFDeriv_le_Hconst {z : Fin n → ℂ} (hz : z ∈ actionNbhd B (r₀ / 2)) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Set ℕ)) : ‖iteratedFDeriv ℂ j h z‖ ≤ Hconst s₀ r₀ B h j :=
  (derivative_bounds_design hD.s₀_pos hD.r₀_pos hD.isBounded hD.holo
    (f := fun _ => 0) (ε := 0) (differentiableOn_const 0) (fun z _ => by simp)).2.1 z hz j hj

/-- Blueprint `bp:p4:freq-map` (iv): `|g (I)| ≤ H₁` for `ι I ∈ B_{r₀/2}`. -/
theorem norm_frequencyMap_le {I : Fin n → ℝ} (hI : realInclusion n I ∈ actionNbhd B (r₀ / 2)) :
    ‖frequencyMap h I‖ ≤ Hconst s₀ r₀ B h 1 := by
  have hU := mem_realDomain_of_half hD.r₀_pos hI
  have hfd : ‖fderiv ℂ h (realInclusion n I)‖ ≤ Hconst s₀ r₀ B h 1 := by
    have := norm_iteratedFDeriv_le_Hconst hD hI (j := 1) (by simp)
    rwa [norm_iteratedFDeriv_one] at this
  refine (pi_norm_le_iff_of_nonneg (Hconst_nonneg hD 1)).2 fun i => ?_
  have h1 : ((frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (realInclusion n I) (Pi.single i 1) :=
    congrFun (frequencyMap_eq_gradC hD hU) i
  calc ‖frequencyMap h I i‖ = ‖((frequencyMap h I i : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
    _ = ‖fderiv ℂ h (realInclusion n I) (Pi.single i 1)‖ := by rw [h1]
    _ ≤ ‖fderiv ℂ h (realInclusion n I)‖ * ‖(Pi.single i 1 : Fin n → ℂ)‖ :=
        (fderiv ℂ h (realInclusion n I)).le_opNorm _
    _ ≤ Hconst s₀ r₀ B h 1 := by
        calc _ ≤ ‖fderiv ℂ h (realInclusion n I)‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_single_one_le i) (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hfd

/-- Blueprint `bp:p4:freq-map` (iv): `|∇²h (ι I)| ≤ H₂` for `ι I ∈ B_{r₀/2}`. -/
theorem norm_hessian_le {I : Fin n → ℝ} (hI : realInclusion n I ∈ actionNbhd B (r₀ / 2)) :
    ‖hessian h (fun i => (I i : ℂ))‖ ≤ Hconst s₀ r₀ B h 2 := by
  have hU := mem_realDomain_of_half hD.r₀_pos hI
  have hfd : ‖fderiv ℂ (fderiv ℂ h) (realInclusion n I)‖ ≤ Hconst s₀ r₀ B h 2 := by
    have := norm_iteratedFDeriv_le_Hconst hD hI (j := 2) (by simp)
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  refine (norm_le_iff_forall_rowSum (Hconst_nonneg hD 2)).2 fun i => ?_
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_apply_eq_rowSum (hessian h (fun i => (I i : ℂ))) i
  have hdiff : DifferentiableAt ℂ (fderiv ℂ h) (realInclusion n I) :=
    (differentiableOn_fderiv_of_isOpen (isOpen_actionNbhd B r₀) hD.holo).differentiableAt
      ((isOpen_actionNbhd B r₀).mem_nhds hU)
  have hrow : (hessian h (realInclusion n I) *ᵥ v) i =
      fderiv ℂ (fderiv ℂ h) (realInclusion n I) v (Pi.single i 1) := by
    rw [hessian_mulVec_apply, fderiv_clm_apply hdiff (differentiableAt_const (Pi.single i 1))]
    simp
  have hsum : ‖((∑ j, ‖hessian h (fun i => (I i : ℂ)) i j‖ : ℝ) : ℂ)‖ =
      ∑ j, ‖hessian h (fun i => (I i : ℂ)) i j‖ :=
    by rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  rw [← hsum, ← hMv]
  change ‖(hessian h (realInclusion n I) *ᵥ v) i‖ ≤ _
  rw [hrow]
  calc _ ≤ ‖fderiv ℂ (fderiv ℂ h) (realInclusion n I) v‖ * ‖(Pi.single i 1 : Fin n → ℂ)‖ :=
        (fderiv ℂ (fderiv ℂ h) (realInclusion n I) v).le_opNorm _
    _ ≤ ‖fderiv ℂ (fderiv ℂ h) (realInclusion n I)‖ * ‖v‖ * 1 := by
        refine mul_le_mul ((fderiv ℂ (fderiv ℂ h) (realInclusion n I)).le_opNorm v)
          (norm_single_one_le i) (norm_nonneg _) (by positivity)
    _ ≤ Hconst s₀ r₀ B h 2 := by
        rw [mul_one]
        calc _ ≤ ‖fderiv ℂ (fderiv ℂ h) (realInclusion n I)‖ * 1 :=
              mul_le_mul_of_nonneg_left hv (by positivity)
          _ ≤ _ := by rw [mul_one]; exact hfd

end Bounds

/-! ### Step `step:p4:fm-lipschitz`: the Lipschitz bound on `B` -/

theorem deltaStar_le_quarter_radius (s₀ r₀ : ℝ) : deltaStar s₀ r₀ ≤ r₀ / 4 := by
  unfold deltaStar
  have := min_le_right (stripWidth s₀) r₀
  linarith

section Lipschitz

variable (hD : Data τ s₀ r₀ B h Lh)
include hD

/-- For `ι I ∈ B_{r₀/2}`, `‖D g (I)‖ ≤ H₂`. -/
theorem norm_fderiv_frequencyMap_le {I : Fin n → ℝ}
    (hI : realInclusion n I ∈ actionNbhd B (r₀ / 2)) :
    ‖fderiv ℝ (frequencyMap h) I‖ ≤ Hconst s₀ r₀ B h 2 := by
  have hU := mem_realDomain_of_half hD.r₀_pos hI
  refine ContinuousLinearMap.opNorm_le_bound _ (Hconst_nonneg hD 2) fun v => ?_
  have h1 := fderiv_frequencyMap_eq_hessian hD hU v
  calc ‖fderiv ℝ (frequencyMap h) I v‖
      = ‖fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)‖ :=
        (norm_realInclusion (fderiv ℝ (frequencyMap h) I v)).symm
    _ = ‖hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)‖ := by rw [h1]
    _ ≤ ‖hessian h (fun i => (I i : ℂ))‖ * ‖fun j => (v j : ℂ)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ Hconst s₀ r₀ B h 2 * ‖v‖ := by
        rw [show ‖fun j => (v j : ℂ)‖ = ‖v‖ from norm_realInclusion v]
        exact mul_le_mul_of_nonneg_right (norm_hessian_le hD hI) (norm_nonneg _)

/-- Blueprint `bp:p4:freq-map` (v): the Lipschitz bound on `B`. -/
theorem frequencyMap_lipschitz {I J : Fin n → ℝ} (hI : I ∈ B) (hJ : J ∈ B) :
    ‖frequencyMap h I - frequencyMap h J‖ ≤ LambdaG s₀ r₀ B h * ‖I - J‖ := by
  have hr := hD.r₀_pos
  have hδ := deltaStar_pos hD.s₀_pos hr
  have hmem : ∀ x : Fin n → ℝ, x ∈ Metric.ball J (deltaStar s₀ r₀) →
      realInclusion n x ∈ actionNbhd B (r₀ / 2) := fun x hx => by
    refine ⟨J, hJ, ?_⟩
    show ‖realInclusion n x - realInclusion n J‖ < r₀ / 2
    rw [← map_sub, norm_realInclusion, ← dist_eq_norm]
    have := deltaStar_le_quarter_radius s₀ r₀
    have hx' := Metric.mem_ball.1 hx
    linarith
  by_cases hnear : ‖I - J‖ < deltaStar s₀ r₀
  · have hIball : I ∈ Metric.ball J (deltaStar s₀ r₀) := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hnear
    have hJball : J ∈ Metric.ball J (deltaStar s₀ r₀) := Metric.mem_ball_self hδ
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := frequencyMap h) (C := Hconst s₀ r₀ B h 2) (s := Metric.ball J (deltaStar s₀ r₀))
      (fun x hx => differentiableAt_frequencyMap hD (mem_realDomain_of_half hr (hmem x hx)))
      (fun x hx => norm_fderiv_frequencyMap_le hD (hmem x hx)) (convex_ball _ _) hJball hIball
    calc ‖frequencyMap h I - frequencyMap h J‖ ≤ Hconst s₀ r₀ B h 2 * ‖I - J‖ := hmv
      _ ≤ LambdaG s₀ r₀ B h * ‖I - J‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · replace hnear := not_lt.1 hnear
    have hI1 := norm_frequencyMap_le hD (realInclusion_mem_half hr hI)
    have hJ1 := norm_frequencyMap_le hD (realInclusion_mem_half hr hJ)
    calc ‖frequencyMap h I - frequencyMap h J‖ ≤ ‖frequencyMap h I‖ + ‖frequencyMap h J‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Hconst s₀ r₀ B h 1 := by linarith
      _ = (2 * Hconst s₀ r₀ B h 1 / deltaStar s₀ r₀) * deltaStar s₀ r₀ := by
          field_simp
      _ ≤ (2 * Hconst s₀ r₀ B h 1 / deltaStar s₀ r₀) * ‖I - J‖ :=
          mul_le_mul_of_nonneg_left hnear (by have := Hconst_nonneg hD 1; positivity)
      _ ≤ LambdaG s₀ r₀ B h * ‖I - J‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end Lipschitz

/-! ### Blueprint `bp:p4:freq-map` -/

/-- Blueprint `bp:p4:freq-map`, items (i)–(v). -/
theorem freq_map (hD : Data τ s₀ r₀ B h Lh) :
    -- (i)
    (IsOpen (realDomain B r₀) ∧ closure B ⊆ realDomain B r₀) ∧
    -- (ii)
    (∀ I ∈ realDomain B r₀,
      (fun i => ((frequencyMap h I i : ℝ) : ℂ)) = gradC h (fun i => (I i : ℂ))) ∧
    -- (iii)
    (DifferentiableOn ℝ (frequencyMap h) (realDomain B r₀) ∧
      ∀ I ∈ realDomain B r₀,
        (∀ v : Fin n → ℝ, (fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)) =
          hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)) ∧
        (hessian h (fun i => (I i : ℂ)))ᵀ = hessian h (fun i => (I i : ℂ)) ∧
        ∀ i j, (hessian h (fun i => (I i : ℂ)) i j).im = 0) ∧
    -- (iv)
    (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B (r₀ / 2) →
      ‖frequencyMap h I‖ ≤ Hconst s₀ r₀ B h 1 ∧
      ‖hessian h (fun i => (I i : ℂ))‖ ≤ Hconst s₀ r₀ B h 2) ∧
    -- (v)
    (∀ I ∈ B, ∀ J ∈ B,
      ‖frequencyMap h I - frequencyMap h J‖ ≤ LambdaG s₀ r₀ B h * ‖I - J‖) ∧
    (∀ I ∈ B, ‖frequencyMap h I‖ ≤ Winf s₀ r₀ B h) ∧
    Bornology.IsBounded (frequencyMap h '' B) := by
  have hhalf : ∀ I ∈ B, realInclusion n I ∈ actionNbhd B (r₀ / 2) := fun I hI =>
    realInclusion_mem_half hD.r₀_pos hI
  refine ⟨⟨isOpen_realDomain B r₀, closure_subset_realDomain hD.r₀_pos B⟩,
    fun I hI => frequencyMap_eq_gradC hD hI,
    ⟨differentiableOn_frequencyMap hD, fun I hI => ⟨fderiv_frequencyMap_eq_hessian hD hI,
      hessian_transpose hD hI, hessian_im hD hI⟩⟩,
    fun I hI => ⟨norm_frequencyMap_le hD hI, norm_hessian_le hD hI⟩,
    fun I hI J hJ => frequencyMap_lipschitz hD hI hJ,
    fun I hI => norm_frequencyMap_le hD (hhalf I hI), ?_⟩
  rw [isBounded_iff_forall_norm_le]
  exact ⟨Winf s₀ r₀ B h, by
    rintro _ ⟨I, hI, rfl⟩
    exact norm_frequencyMap_le hD (hhalf I hI)⟩

end KAM.Head

end
