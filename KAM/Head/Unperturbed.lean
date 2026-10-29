/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Adapters
public import KAM.Head.UnperturbedFrame
import KAM.Head.H1
import KAM.Head.HamiltonianField
import KAM.Head.InverseFrequency
import KAM.Matrix.Neumann
import KAM.Strip.Averages

/-!
# Geometry of the unperturbed torus

Blueprint Part 4, `bp:p4:unperturbed`. For `I_* ∈ B`, `ω ∈ ℝⁿ` and
`K⁰ = K⁰_{I_*}`, `θ ↦ (θ, ι I_*)`, the theorem `KAM.Head.unperturbed` collects the items
(a)–(g). The frame side, items (a), (b), (c) and (g), is computed from the frozen definitions in
`KAM/Head/UnperturbedFrame.lean`. This file proves the torsion side, items (d), (e), (f).

* `step:p4:unp-torsion`: the torsion of `K⁰` is `∂²_I 𝐡(θ, ι I_*)`
  (`KAM.Head.torsion_unperturbedTorus_eq`; the derivative term vanishes by
  `KAM.Head.fderiv_normalFrame_unperturbedTorus`, and `DX_𝐡 = J ∘ D²𝐡` is
  `KAM.Head.fderiv_hamiltonianVectorField`). It splits as `∇²h(ι I_*) + ∂²_I f`
  (`KAM.Head.unperturbed_actionHessian_hbold`), is continuous on the real torus (through the
  `torsion_regular` adapter), and its average is `∇²h + ∫ ∂²_I f`
  (`KAM.Head.unperturbed_torsionAverage`).
* `step:p4:unp-twist`: `‖∂²_I f‖ ≤ ‖D²f‖ ≤ F₂ ε` row by row
  (`KAM.Head.unperturbed_norm_actionHessian_le`), then the Neumann criterion with the bound
  `‖(∇²h)⁻¹‖ ≤ L₊` of `bp:p4:hessian-inverse` (`KAM.Head.unperturbed_twist`).
* `step:p4:unp-error`: `E⁰ = X_f(θ, ι I_*)` for `ω = g(I_*)`
  (`KAM.Head.unperturbed_invarianceError`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}

/-! ### The derivative of `𝐡 = h ∘ pr₂ + f` on `𝔇` -/

theorem unperturbed_differentiableAt_h (hD : Data τ s₀ r₀ B h Lh)
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ domainD n s₀ r₀ B) : DifferentiableAt ℂ h w.2 :=
  hD.holo.differentiableAt ((isOpen_actionNbhd B r₀).mem_nhds
    (actionNbhd_mono B (half_le_self hD.r₀_pos.le) hw.2))

theorem unperturbed_differentiableAt_f (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ domainD n s₀ r₀ B) : DifferentiableAt ℂ f w :=
  hP.holo.differentiableAt (((isOpen_complexStrip n s₀).prod (isOpen_actionNbhd B r₀)).mem_nhds
    (h1_domainD_subset_domain n hD.s₀_pos hD.r₀_pos B hw))

/-- `D𝐡(w) = Dh(w.2) ∘ pr₂ + Df(w)` on `𝔇`. -/
theorem unperturbed_fderiv_hbold (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ domainD n s₀ r₀ B) :
    fderiv ℂ (hbold h f) w =
      (fderiv ℂ h w.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ)) +
        fderiv ℂ f w := by
  have h1 : HasFDerivAt (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)
      ((fderiv ℂ h w.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))) w :=
    (unperturbed_differentiableAt_h hD hw).hasFDerivAt.comp w hasFDerivAt_snd
  exact (h1.add (unperturbed_differentiableAt_f hD hP hw).hasFDerivAt).fderiv

/-! ### The action Hessian -/

/-- `∂²_I φ (z)_{ij} = D(Dφ)(z) (0, e_j) (0, e_i)`. -/
theorem unperturbed_actionHessian_apply {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hφ : DifferentiableAt ℂ (fderiv ℂ φ) z) (i j : Fin n) :
    actionHessian φ z i j = fderiv ℂ (fderiv ℂ φ) z (0, Pi.single j 1) (0, Pi.single i 1) := by
  simp only [actionHessian, Matrix.of_apply]
  rw [fderiv_clm_apply hφ (differentiableAt_const _)]
  simp

/-- Step `step:p4:unp-torsion`: `∂²_I 𝐡 = ∇²h + ∂²_I f` on `𝔇`. -/
theorem unperturbed_actionHessian_hbold (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ domainD n s₀ r₀ B) :
    actionHessian (hbold h f) z = hessian h z.2 + actionHessian f z := by
  have hopen := isOpen_domainD n s₀ r₀ B
  have hr := hD.r₀_pos
  have hz2 : z.2 ∈ actionNbhd B r₀ := actionNbhd_mono B (half_le_self hr.le) hz.2
  have hfd_h : DifferentiableAt ℂ (fderiv ℂ h) z.2 :=
    (differentiableOn_fderiv_of_isOpen (isOpen_actionNbhd B r₀) hD.holo).differentiableAt
      ((isOpen_actionNbhd B r₀).mem_nhds hz2)
  have hfd_f : DifferentiableAt ℂ (fderiv ℂ f) z :=
    (differentiableOn_fderiv_of_isOpen ((isOpen_complexStrip n s₀).prod (isOpen_actionNbhd B r₀))
      hP.holo).differentiableAt (((isOpen_complexStrip n s₀).prod
        (isOpen_actionNbhd B r₀)).mem_nhds (h1_domainD_subset_domain n hD.s₀_pos hr B hz))
  ext i j
  have hev : (fun w => fderiv ℂ (hbold h f) w (0, Pi.single i 1)) =ᶠ[𝓝 z]
      fun w => fderiv ℂ h w.2 (Pi.single i 1) + fderiv ℂ f w (0, Pi.single i 1) :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => by
      beta_reduce
      rw [unperturbed_fderiv_hbold hD hP hw]; rfl
  have hg : DifferentiableAt ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2 :=
    hfd_h.clm_apply (differentiableAt_const _)
  have hk : DifferentiableAt ℂ (fun w => fderiv ℂ f w (0, Pi.single i 1)) z :=
    hfd_f.clm_apply (differentiableAt_const _)
  have hgs : HasFDerivAt (fun w : (Fin n → ℂ) × (Fin n → ℂ) => fderiv ℂ h w.2 (Pi.single i 1))
      ((fderiv ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))) z :=
    hg.hasFDerivAt.comp z hasFDerivAt_snd
  simp only [actionHessian, hessian, Matrix.of_apply, Matrix.add_apply]
  rw [hev.fderiv_eq, (hgs.fun_add hk.hasFDerivAt).fderiv]
  simp

/-- Step `step:p4:unp-twist`, first estimate: `‖∂²_I φ (z)‖ ≤ ‖D²φ (z)‖`. The row sum of the
action Hessian is the value of `D²φ(z)(0, v)(0, eᵢ)` at the test vector `v`. -/
theorem unperturbed_norm_actionHessian_le {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hφ : DifferentiableAt ℂ (fderiv ℂ φ) z) :
    ‖actionHessian φ z‖ ≤ ‖fderiv ℂ (fderiv ℂ φ) z‖ := by
  refine (norm_le_iff_forall_rowSum (norm_nonneg (fderiv ℂ (fderiv ℂ φ) z))).2 fun i => ?_
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_apply_eq_rowSum (actionHessian φ z) i
  have hrow : (actionHessian φ z *ᵥ v) i =
      fderiv ℂ (fderiv ℂ φ) z (0, v) (0, Pi.single i 1) := by
    simp only [Matrix.mulVec, dotProduct, unperturbed_actionHessian_apply hφ]
    have hw : ((0 : Fin n → ℂ), v) =
        ∑ j, v j • ((0 : Fin n → ℂ), (Pi.single j 1 : Fin n → ℂ)) := by
      ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw, map_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, _root_.smul_apply, smul_eq_mul, mul_comm]
  have hsum : ‖((∑ j, ‖actionHessian φ z i j‖ : ℝ) : ℂ)‖ = ∑ j, ‖actionHessian φ z i j‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  rw [← hsum, ← hMv]
  change ‖(actionHessian φ z *ᵥ v) i‖ ≤ _
  rw [hrow]
  have hn0 : ‖((0 : Fin n → ℂ), v)‖ ≤ 1 := by
    rw [Prod.norm_def]; exact max_le (by simp) hv
  have hn1 : ‖((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ))‖ ≤ 1 := by
    rw [Prod.norm_def]; exact max_le (by simp) (by simp [Pi.norm_single])
  calc _ ≤ ‖fderiv ℂ (fderiv ℂ φ) z (0, v)‖ * ‖((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ))‖ :=
        (fderiv ℂ (fderiv ℂ φ) z (0, v)).le_opNorm _
    _ ≤ ‖fderiv ℂ (fderiv ℂ φ) z‖ * ‖((0 : Fin n → ℂ), v)‖ * 1 :=
        mul_le_mul ((fderiv ℂ (fderiv ℂ φ) z).le_opNorm _) hn1 (norm_nonneg _) (by positivity)
    _ ≤ ‖fderiv ℂ (fderiv ℂ φ) z‖ := by
        rw [mul_one]
        calc _ ≤ ‖fderiv ℂ (fderiv ℂ φ) z‖ * 1 := by gcongr
          _ = _ := mul_one _

/-- The entrywise average of `C + A(x)` over the unit cube is `C + ⟨A⟩`, for continuous `A`. -/
theorem unperturbed_matrixAverage_const_add {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℂ)
    {A : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ} (hA : Continuous A) :
    matrixAverage (fun x => C + A x) = C + matrixAverage A := by
  ext i j
  have hc : Continuous fun x => A x i j :=
    (continuous_apply j).comp ((continuous_apply i).comp hA)
  have hfin : volume (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by
    rw [KAM.volume_unitCube]; exact ENNReal.one_ne_top
  simp only [matrixAverage, Matrix.of_apply, Matrix.add_apply, KAM.torusAverage]
  rw [integral_add (integrableOn_const hfin) (KAM.integrableOn_unitCube_of_continuous hc),
    setIntegral_const, measureReal_def, KAM.volume_unitCube]
  simp

/-! ### Item (d): the torsion -/

section Torsion

variable (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) {I : Fin n → ℝ} (hI : I ∈ B)
include hD hI

/-- `K⁰(T_{s/2}) ⊆ 𝔇` for `I_* ∈ B`. -/
theorem unperturbed_mem_domainD {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (stripWidth s₀ / 2)) :
    unperturbedTorus I θ ∈ domainD n s₀ r₀ B :=
  ⟨hθ, ⟨I, hI, by
    show ‖(fun i => (I i : ℂ)) - fun i => (I i : ℂ)‖ < r₀ / 2
    rw [sub_self, norm_zero]; exact half_pos hD.r₀_pos⟩⟩

/-- The real points `(ι x, ι I_*)` lie in `𝔇`. -/
theorem unperturbed_mem_domainD_real (x : Fin n → ℝ) :
    ((fun l => (x l : ℂ)), fun i => (I i : ℂ)) ∈ domainD n s₀ r₀ B :=
  unperturbed_mem_domainD hD hI
    (KAM.ofReal_mem_complexStrip (half_pos (stripWidth_pos hD.s₀_pos)) x)

include hP

/-- Step `step:p4:unp-torsion`: for `θ ∈ T_{s/2}` the torsion of `K⁰` is `∂²_I 𝐡(θ, ι I_*)`,
whatever `ω` is. -/
theorem torsion_unperturbedTorus_eq (ω : Fin n → ℝ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (stripWidth s₀ / 2)) :
    torsion (hbold h f) (unperturbedTorus I) ω θ =
      actionHessian (hbold h f) (θ, fun i => (I i : ℂ)) := by
  have hz : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)) ∈ domainD n s₀ r₀ B :=
    unperturbed_mem_domainD hD hI hθ
  have hopen := isOpen_domainD n s₀ r₀ B
  have hdiff := h1_differentiableOn hD hP
  have hX := fderiv_hamiltonianVectorField hopen hdiff hz
  have hfd : DifferentiableAt ℂ (fderiv ℂ (hbold h f)) (θ, fun i => (I i : ℂ)) :=
    (differentiableOn_fderiv_of_isOpen hopen hdiff).differentiableAt (hopen.mem_nhds hz)
  have hK : unperturbedTorus I θ = (θ, fun i => (I i : ℂ)) := rfl
  ext i j
  rw [unperturbed_actionHessian_apply hfd]
  simp only [torsion, hK, normalFrame_unperturbedTorus, hX]
  simp [dotℂ, omegaZero, hamJ_apply, Pi.single_apply]

/-- Item (d), continuity: the torsion of `K⁰` is continuous on the real torus. This is
`torsion_regular` (c) for `K = K⁰` on `T_{s/2}`. -/
theorem unperturbed_continuous_torsion (ω : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ =>
      torsion (hbold h f) (unperturbedTorus I) ω (fun l => (x l : ℂ))) :=
  (torsion_regular_design hD.s₀_pos hD.r₀_pos hD.holo hP.holo hP.periodic
    (half_pos (stripWidth_pos hD.s₀_pos)) (differentiable_unperturbedTorus I).differentiableOn
    (fun _ hθ => unperturbed_mem_domainD hD hI hθ)
    (fun θ _ => by rw [gramMatrix_unperturbedTorus]; simp) ω).2.2.1.2.2

/-- The torsion of `K⁰` at a real point is `∇²h(ι I_*) + ∂²_I f(ι x, ι I_*)`. -/
theorem unperturbed_torsion_real (ω : Fin n → ℝ) (x : Fin n → ℝ) :
    torsion (hbold h f) (unperturbedTorus I) ω (fun l => (x l : ℂ)) =
      hessian h (fun i => (I i : ℂ)) +
        actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ)) := by
  rw [torsion_unperturbedTorus_eq hD hP hI ω
    (KAM.ofReal_mem_complexStrip (half_pos (stripWidth_pos hD.s₀_pos)) x)]
  exact unperturbed_actionHessian_hbold hD hP (unperturbed_mem_domainD_real hD hI x)

/-- `x ↦ ∂²_I f(ι x, ι I_*)` is continuous on `ℝⁿ`. -/
theorem unperturbed_continuous_actionHessian :
    Continuous (fun x : Fin n → ℝ =>
      actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ))) := by
  have : (fun x : Fin n → ℝ => actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ))) =
      fun x => torsion (hbold h f) (unperturbedTorus I) 0 (fun l => (x l : ℂ)) -
        hessian h (fun i => (I i : ℂ)) :=
    funext fun x => by rw [unperturbed_torsion_real hD hP hI 0 x]; abel
  rw [this]
  exact (unperturbed_continuous_torsion hD hP hI 0).sub continuous_const

/-- Item (d), average: `⟨T⁰⟩ = ∇²h(ι I_*) + ⟨∂²_I f(·, ι I_*)⟩`. -/
theorem unperturbed_torsionAverage (ω : Fin n → ℝ) :
    torsionAverage (hbold h f) (unperturbedTorus I) ω =
      hessian h (fun i => (I i : ℂ)) +
        matrixAverage (fun x : Fin n → ℝ =>
          actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ))) := by
  rw [torsionAverage_eq_matrixAverage]
  simp only [unperturbed_torsion_real hD hP hI ω]
  exact unperturbed_matrixAverage_const_add _ (unperturbed_continuous_actionHessian hD hP hI)

end Torsion

/-! ### Items (e) and (f): the twist and the invariance error -/

section TwistError

variable (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) {I : Fin n → ℝ} (hI : I ∈ B)
include hD hP

/-- `‖∂²_I f(z)‖ ≤ F₂ ε` on `𝔇` (`bp:p4:derivative-bounds` (c)). -/
theorem unperturbed_norm_actionHessian_f_le {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ domainD n s₀ r₀ B) : ‖actionHessian f z‖ ≤ Fconst n s₀ r₀ 2 * ε := by
  have hr := hD.r₀_pos
  have hopen := (isOpen_complexStrip n s₀).prod (isOpen_actionNbhd B r₀)
  have hfd : DifferentiableAt ℂ (fderiv ℂ f) z :=
    (differentiableOn_fderiv_of_isOpen hopen hP.holo).differentiableAt
      (hopen.mem_nhds (h1_domainD_subset_domain n hD.s₀_pos hr B hz))
  have hb := (((derivative_bounds_design hD.s₀_pos hr hD.isBounded hD.holo hP.holo
    hP.bound).2.2.1 z hz).1 2 (by simp))
  refine (unperturbed_norm_actionHessian_le hfd).trans ?_
  rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb

include hI

/-- Item (e), step `step:p4:unp-twist`: if `L₊ F₂ ε ≤ 1/2`, then `⟨T⁰⟩` is invertible with
`‖⟨T⁰⟩⁻¹‖ ≤ 2 L₊`. -/
theorem unperturbed_twist (ω : Fin n → ℝ) (hsmall : Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2) :
    IsUnit (torsionAverage (hbold h f) (unperturbedTorus I) ω).det ∧
      ‖(torsionAverage (hbold h f) (unperturbedTorus I) ω)⁻¹‖ ≤ 2 * Lplus Lh := by
  obtain ⟨-, hAdet, -, hAinv⟩ := hessian_inverse hD I hI
  have hAunit : IsUnit (hessian h (fun i => (I i : ℂ))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hAdet
  have hΔ : ‖matrixAverage (fun x : Fin n → ℝ =>
      actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ)))‖ ≤ Fconst n s₀ r₀ 2 * ε :=
    norm_matrixAverage_le (unperturbed_continuous_actionHessian hD hP hI).continuousOn
      fun x _ => unperturbed_norm_actionHessian_f_le hD hP (unperturbed_mem_domainD_real hD hI x)
  have hsm : ‖(hessian h (fun i => (I i : ℂ)))⁻¹‖ * ‖matrixAverage (fun x : Fin n → ℝ =>
      actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ)))‖ ≤ 1 / 2 :=
    calc _ ≤ Lplus Lh * (Fconst n s₀ r₀ 2 * ε) :=
          mul_le_mul hAinv hΔ (norm_nonneg _) (zero_le_one.trans (one_le_Lplus Lh))
      _ ≤ 1 / 2 := by linarith
  rw [unperturbed_torsionAverage hD hP hI ω]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).1 (matrix_isUnit_add_of_inv_norm_mul_le_half hAunit hsm),
    (matrix_norm_inv_add_le hAunit hsm).trans (by linarith)⟩

/-- Item (f), step `step:p4:unp-error`: for `ω = g(I_*)` the invariance error of `K⁰` is the
vector field of `f`, `E⁰(θ) = X_f(θ, ι I_*)`, of size at most `F₁ ε`. -/
theorem unperturbed_invarianceError (ω : Fin n → ℝ) (hω : ω = frequencyMap h I)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (stripWidth s₀ / 2)) :
    invarianceError (hbold h f) (unperturbedTorus I) ω θ =
      hamiltonianVectorFieldℂ f (θ, fun i => (I i : ℂ)) ∧
    ‖invarianceError (hbold h f) (unperturbedTorus I) ω θ‖ ≤ Fconst n s₀ r₀ 1 * ε := by
  have hz : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)) ∈ domainD n s₀ r₀ B :=
    unperturbed_mem_domainD hD hI hθ
  have hgrad := frequencyMap_eq_gradC hD
    (closure_subset_realDomain hD.r₀_pos B (subset_closure hI))
  have heq : invarianceError (hbold h f) (unperturbedTorus I) ω θ =
      hamiltonianVectorFieldℂ f (θ, fun i => (I i : ℂ)) := by
    have hK : unperturbedTorus I θ = (θ, fun i => (I i : ℂ)) := rfl
    simp only [invarianceError, hK, fderiv_unperturbedTorus, hamiltonianVectorFieldℂ,
      unperturbed_fderiv_hbold hD hP hz]
    ext i
    · simp [hω, congrFun hgrad i, gradC]
    · simp
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ((derivative_bounds_design hD.s₀_pos hD.r₀_pos hD.isBounded hD.holo hP.holo
    hP.bound).2.2.1 _ hz).2.1

end TwistError

/-! ### The node -/

/-- Blueprint `bp:p4:unperturbed`, items (a)–(g), for `K⁰ = K⁰_{I_*}` with `I_* ∈ B`. -/
theorem unperturbed (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1)
    {I : Fin n → ℝ} (hI : I ∈ B) (ω : Fin n → ℝ) :
    -- (a)
    (Differentiable ℂ (unperturbedTorus I) ∧ (∀ ρ, IsPrimaryOnStrip (unperturbedTorus I) ρ) ∧
      IsRealOnReals (unperturbedTorus I) ∧
      ∀ θ, tangentMat (unperturbedTorus I) θ = frameL0 n ∧
        ‖fderiv ℂ (unperturbedTorus I) θ‖ = 1) ∧
    -- (b)
    (∀ θ, gramMatrix (unperturbedTorus I) θ = 1 ∧
      IsUnit (gramMatrix (unperturbedTorus I) θ).det ∧
      ‖(gramMatrix (unperturbedTorus I) θ)⁻¹‖ = 1) ∧
    -- (c)
    (∀ θ j, normalFrame (unperturbedTorus I) θ j = (0, Pi.single j 1)) ∧
    (∀ θ, normalMat (unperturbedTorus I) θ = frameN0 n) ∧
    (∀ θ j, fderiv ℂ (fun θ' => normalFrame (unperturbedTorus I) θ' j) θ
      (fun l => (ω l : ℂ)) = 0) ∧
    -- (d)
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 2),
      torsion (hbold h f) (unperturbedTorus I) ω θ =
        actionHessian (hbold h f) (θ, fun i => (I i : ℂ)) ∧
      actionHessian (hbold h f) (θ, fun i => (I i : ℂ)) =
        hessian h (fun i => (I i : ℂ)) + actionHessian f (θ, fun i => (I i : ℂ))) ∧
    Continuous (fun x : Fin n → ℝ =>
      torsion (hbold h f) (unperturbedTorus I) ω (fun l => (x l : ℂ))) ∧
    torsionAverage (hbold h f) (unperturbedTorus I) ω =
      hessian h (fun i => (I i : ℂ)) +
        matrixAverage (fun x : Fin n → ℝ =>
          actionHessian f ((fun l => (x l : ℂ)), fun i => (I i : ℂ))) ∧
    -- (e)
    (Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2 →
      IsUnit (torsionAverage (hbold h f) (unperturbedTorus I) ω).det ∧
      ‖(torsionAverage (hbold h f) (unperturbedTorus I) ω)⁻¹‖ ≤ 2 * Lplus Lh) ∧
    -- (f)
    (ω = frequencyMap h I → ∀ θ ∈ complexStrip n (stripWidth s₀ / 2),
      invarianceError (hbold h f) (unperturbedTorus I) ω θ =
        hamiltonianVectorFieldℂ f (θ, fun i => (I i : ℂ)) ∧
      ‖invarianceError (hbold h f) (unperturbedTorus I) ω θ‖ ≤ Fconst n s₀ r₀ 1 * ε) ∧
    -- (g)
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 4),
      Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀) ⊆ domainD n s₀ r₀ B := by
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) hD.two_le
  have _hε := hε
  refine ⟨⟨differentiable_unperturbedTorus I, isPrimaryOnStrip_unperturbedTorus I,
      isRealOnReals_unperturbedTorus I,
      fun θ => ⟨tangentMat_unperturbedTorus I θ, norm_fderiv_unperturbedTorus hn I θ⟩⟩,
    fun θ => ⟨gramMatrix_unperturbedTorus I θ, by simp [gramMatrix_unperturbedTorus],
      by rw [gramMatrix_unperturbedTorus, inv_one]; exact unperturbed_norm_one hn⟩,
    normalFrame_unperturbedTorus I, normalMat_unperturbedTorus I,
    fun θ j => fderiv_normalFrame_unperturbedTorus I θ j _,
    fun θ hθ => ⟨torsion_unperturbedTorus_eq hD hP hI ω hθ,
      unperturbed_actionHessian_hbold hD hP (unperturbed_mem_domainD hD hI hθ)⟩,
    unperturbed_continuous_torsion hD hP hI ω, unperturbed_torsionAverage hD hP hI ω,
    fun hsmall => unperturbed_twist hD hP hI ω hsmall,
    fun hω θ hθ => unperturbed_invarianceError hD hP hI ω hω hθ,
    fun θ hθ => ball_unperturbedTorus_subset_domainD hD.r₀_pos hI hθ⟩

end KAM.Head

end
