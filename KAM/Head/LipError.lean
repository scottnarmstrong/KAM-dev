/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Normalize
import KAM.Head.Adapters
import KAM.Head.Frequency
import KAM.Head.H1
import KAM.Head.HamiltonianField
import KAM.Head.InverseFrequency
import KAM.Head.Parameters
import KAM.Head.Unperturbed
import KAM.Head.UnperturbedFrame
import KAM.Strip.Increments
import KAM.Strip.Limits
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The error of the shifted torus

Blueprint Part 4, `bp:p4:lip-error`. For `ω, ω' ∈ Ω_γ` with
`|ω' - ω| ≤ λ_* γ²`, put `ΔI = I_{ω'} - I_ω` and `K' = K_ω + (0, ι ΔI)`
(`KAM.Head.shiftedTorus`). Then `K'` is holomorphic and primary on `T_{s/8}`, real on reals,
`K' - K⁰_{ω'} = W_ω` (so `|K' - K⁰_{ω'}| ≤ η₀` on `T_{s/8}`), and the invariance error `E'` of
`K'` at `ω'` satisfies `|E'| ≤ A₁ ε γ⁻² |Δω|` on `T_{3s/32}`.

The elementary properties come from `KAM.Head.normalize`; no G premise is used beyond it. The
estimate of `E'` (steps `step:p4:le-basic` to `step:p4:le-sum`) is proved for an abstract torus `K`
(`KAM.Head.invarianceError_shift_le`), so that no constant is unfolded in it:

* `step:p4:le-split`: `X_𝐡 = (∇h ∘ pr₂, 0) + X_f` on `𝔇` (`KAM.Head.hamiltonianVectorField_hbold`),
  and the decomposition `E' = (P_h, 0) + P_f - DW Δω`;
* `step:p4:le-h`: the mixed difference of `∇h` (`KAM.Head.gradC_mixed_difference`), with
  `|D²∇h| ≤ |D³h| ≤ H₃` (`KAM.Head.norm_iteratedFDeriv_two_gradC_le`);
* `step:p4:le-f`: the increment of `X_f` along the segment `K + t (0, ι ΔI)`
  (`KAM.Head.norm_hamiltonianVectorField_f_shift_le`);
* `step:p4:le-transport`: the Cauchy estimate `|DW| ≤ 32 n η₀ / s` on `T_{3s/32}`
  (`KAM.Head.norm_fderiv_sub_unperturbed_le`);
* `step:p4:le-sum`: the arithmetic, using `γ ≤ 1`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Metric

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-! ### The gradient as a linear image of the derivative -/

/-- `J'(ℓ) = (ℓ(eᵢ))ᵢ`: the gradient `∇h` is `J' ∘ Dh`. -/
def gradJ (n : ℕ) : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)

theorem gradJ_apply (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : gradJ n ℓ = fun i => ℓ (Pi.single i 1) := rfl

/-- `∇h = J' ∘ Dh`. -/
theorem gradC_eq_gradJ (h : (Fin n → ℂ) → ℂ) : gradC h = fun z => gradJ n (fderiv ℂ h z) := rfl

/-- `‖J'(ℓ)‖ ≤ ‖ℓ‖`. -/
theorem norm_gradJ_apply_le (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : ‖gradJ n ℓ‖ ≤ ‖ℓ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (ℓ.le_opNorm _).trans ?_
  calc ‖ℓ‖ * ‖(Pi.single i 1 : Fin n → ℂ)‖ ≤ ‖ℓ‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_single_one_le i) (norm_nonneg _)
    _ = ‖ℓ‖ := mul_one _

/-- `‖J'‖ ≤ 1`. -/
theorem norm_gradJ_le : ‖gradJ n‖ ≤ 1 :=
  (gradJ n).opNorm_le_bound zero_le_one fun ℓ => by simpa using norm_gradJ_apply_le ℓ

/-- `∇h` is holomorphic where `h` is, on an open set. -/
theorem differentiableOn_gradC {V : Set (Fin n → ℂ)} (hV : IsOpen V) (hh : DifferentiableOn ℂ h V) :
    DifferentiableOn ℂ (gradC h) V :=
  (gradJ n).differentiable.comp_differentiableOn (differentiableOn_fderiv_of_isOpen hV hh)

/-- Step `step:p4:le-h`: `‖D²∇h‖ ≤ ‖D³h‖` on the open set where `h` is holomorphic, since `∇h` is
the image of `Dh` under the contraction `J'`. -/
theorem norm_iteratedFDeriv_two_gradC_le {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hh : DifferentiableOn ℂ h V) {z : Fin n → ℂ} (hz : z ∈ V) :
    ‖iteratedFDeriv ℂ 2 (gradC h) z‖ ≤ ‖iteratedFDeriv ℂ 3 h z‖ := by
  have hc : ContDiffAt ℂ 2 (fderiv ℂ h) z :=
    ((contDiffOn_nat_of_differentiableOn hV hh 3).fderiv_of_isOpen hV (m := 2)
      (by norm_num)).contDiffAt (hV.mem_nhds hz)
  have h1 := (gradJ n).norm_iteratedFDeriv_comp_left hc (n := 2) (by norm_num)
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (by nlinarith [norm_gradJ_le (n := n), norm_nonneg (iteratedFDeriv ℂ 3 h z)])

/-! ### Step `step:p4:le-h`: the mixed difference of `∇h` -/

/-- The mixed second difference of `∇h` on a parallelogram in `B_{r₀/2}`:
`‖∇h(a+v+w) - ∇h(a+v) - ∇h(a+w) + ∇h(a)‖ ≤ H₃ ‖v‖ ‖w‖`. -/
theorem gradC_mixed_difference (hD : Data τ s₀ r₀ B h Lh) {a v w : Fin n → ℂ}
    (hpar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      a + t • v + t' • w ∈ actionNbhd B (r₀ / 2)) :
    ‖gradC h (a + v + w) - gradC h (a + v) - gradC h (a + w) + gradC h a‖ ≤
      Hconst s₀ r₀ B h 3 * ‖v‖ * ‖w‖ := by
  have hV := isOpen_actionNbhd B (r₀ / 2)
  have hh : DifferentiableOn ℂ h (actionNbhd B (r₀ / 2)) :=
    hD.holo.mono (actionNbhd_mono B (half_le_self hD.r₀_pos.le))
  exact mixed_difference_design hV (differentiableOn_gradC hV hh) hpar
    (fun t ht t' ht' => (norm_iteratedFDeriv_two_gradC_le hV hh (hpar t ht t' ht')).trans
      (norm_iteratedFDeriv_le_Hconst hD (hpar t ht t' ht') (j := 3) (by simp)))

/-! ### Step `step:p4:le-split`: the Hamiltonian vector field of `𝐡 = h ∘ pr₂ + f` -/

/-- `X_𝐡 = (∇h ∘ pr₂, 0) + X_f` on `𝔇`. -/
theorem hamiltonianVectorField_hbold (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ domainD n s₀ r₀ B) :
    hamiltonianVectorFieldℂ (hbold h f) z = (gradC h z.2, 0) + hamiltonianVectorFieldℂ f z := by
  simp only [hamiltonianVectorFieldℂ, unperturbed_fderiv_hbold hD hP hz]
  ext i <;> simp [gradC]

/-! ### Step `step:p4:le-f`: the perturbation -/

/-- The increment of `X_f` along a segment inside the ball `B_{δ_*}(K⁰_I(θ)) ⊆ 𝔇`, `θ ∈ T_{s/4}`,
`I ∈ B`, where `‖DX_f‖ ≤ F₂ ε`. -/
theorem norm_hamiltonianVectorField_f_shift_le (hD : Data τ s₀ r₀ B h Lh)
    (hP : Pert s₀ r₀ B f ε) {I : Fin n → ℝ} (hI : I ∈ B) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4)) {z c : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ ball (unperturbedTorus I θ) (deltaStar s₀ r₀))
    (hzc : z + c ∈ ball (unperturbedTorus I θ) (deltaStar s₀ r₀)) :
    ‖hamiltonianVectorFieldℂ f (z + c) - hamiltonianVectorFieldℂ f z‖ ≤
      Fconst n s₀ r₀ 2 * ε * ‖c‖ := by
  have hsub := ball_unperturbedTorus_subset_domainD hD.r₀_pos hI hθ (s₀ := s₀)
  have hopen : IsOpen (complexStrip n s₀ ×ˢ actionNbhd B r₀) :=
    (isOpen_complexStrip n s₀).prod (isOpen_actionNbhd B r₀)
  have hdiff : DifferentiableOn ℂ (hamiltonianVectorFieldℂ f)
      (ball (unperturbedTorus I θ) (deltaStar s₀ r₀)) :=
    (differentiableOn_hamiltonianVectorField hopen hP.holo).mono
      (fun x hx => h1_domainD_subset_domain n hD.s₀_pos hD.r₀_pos B (hsub hx))
  have hbound : ∀ x ∈ ball (unperturbedTorus I θ) (deltaStar s₀ r₀),
      ‖fderiv ℂ (hamiltonianVectorFieldℂ f) x‖ ≤ Fconst n s₀ r₀ 2 * ε := fun x hx =>
    ((derivative_bounds_design hD.s₀_pos hD.r₀_pos hD.isBounded hD.holo hP.holo
      hP.bound).2.2.1 x (hsub hx)).2.2
  exact increments_open isOpen_ball hdiff hbound
    ((convex_ball _ _).segment_subset hz hzc)

/-! ### Step `step:p4:le-transport`: the Cauchy estimate -/

/-- The displacement `W = K - K⁰_I` of a torus `K` with `‖W‖ ≤ η` on `T_{s/8}` satisfies
`‖DW‖ ≤ n (s/32)⁻¹ η` on `T_{3s/32}` (`bp:p1:cauchy-strip` with loss `s/32`). -/
theorem norm_fderiv_sub_unperturbed_le (hs₀ : 0 < s₀) {I : Fin n → ℝ} {η : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hKd : DifferentiableOn ℂ K (complexStrip n (stripWidth s₀ / 8)))
    (hKW : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8), ‖K θ - unperturbedTorus I θ‖ ≤ η) :
    ∀ θ ∈ complexStrip n (3 * stripWidth s₀ / 32),
      ‖fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ‖ ≤ n * (stripWidth s₀ / 32)⁻¹ * η := by
  have hs := stripWidth_pos hs₀
  have hW : DifferentiableOn ℂ (fun θ' => K θ' - unperturbedTorus I θ')
      (complexStrip n (stripWidth s₀ / 8)) :=
    hKd.sub (differentiable_unperturbedTorus I).differentiableOn
  have hstrip : 3 * stripWidth s₀ / 32 = stripWidth s₀ / 8 - stripWidth s₀ / 32 := by ring
  rw [hstrip]
  exact increments_cauchy hW hKW (by positivity)

/-! ### Step `step:p4:le-split`: the decomposition of `E'` -/

/-- The norm of the real shift `(0, ι a)` is `‖a‖`. -/
theorem norm_shiftConst (a : Fin n → ℝ) :
    ‖((0 : Fin n → ℂ), fun i => (a i : ℂ))‖ = ‖a‖ := by
  have h1 : ‖fun i => (a i : ℂ)‖ = ‖a‖ := norm_realInclusion a
  rw [Prod.norm_def, norm_zero, h1]
  exact max_eq_right (norm_nonneg _)

/-- The norm of `(x, 0)` is `‖x‖`. -/
theorem norm_pair_zero (x : Fin n → ℂ) : ‖((x, 0) : (Fin n → ℂ) × (Fin n → ℂ))‖ = ‖x‖ := by
  rw [Prod.norm_def, norm_zero]
  exact max_eq_left (norm_nonneg _)

/-- The algebra of the splitting: `(g₁, 0) + F₁ - (((g₀, 0) + F₀) + (DW + (g₂ - g₃, 0)))
= (g₁ - g₀ - g₂ + g₃, 0) + (F₁ - F₀) - DW`. -/
theorem lipError_split (g₁ g₀ g₂ g₃ : Fin n → ℂ) (F₁ F₀ DW : (Fin n → ℂ) × (Fin n → ℂ)) :
    ((g₁, 0) + F₁ - (((g₀, 0) + F₀) + (DW + (g₂ - g₃, 0))) :
        (Fin n → ℂ) × (Fin n → ℂ)) =
      (g₁ - g₀ - g₂ + g₃, 0) + (F₁ - F₀) - DW := by
  ext i <;> (simp; try ring)

/-- Steps `step:p4:le-split`: for a torus `K` with `E = 0` at `ω = ∇h(I)`, the invariance error of
`K' = K + (0, ι ΔI)` at `ω' = ∇h(I')` is `(P_h, 0) + P_f - DW Δω`, with `W = K - K⁰_I`,
`a = ι I`, `v = W₂`, `w = ι ΔI`,
`P_h = ∇h(a+v+w) - ∇h(a+v) - ∇h(a+w) + ∇h(a)` and `P_f = X_f(K + (0,w)) - X_f(K)`. -/
theorem invarianceError_shift_eq (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    {I I' : Fin n → ℝ} (hI : I ∈ B) (hI' : I' ∈ B) {ω ω' : Fin n → ℝ}
    (hωI : frequencyMap h I = ω) (hωI' : frequencyMap h I' = ω')
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hKd : DifferentiableOn ℂ K (complexStrip n (stripWidth s₀ / 8)))
    (hKE : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8), invarianceError (hbold h f) K ω θ = 0)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (stripWidth s₀ / 8))
    (hz : K θ ∈ domainD n s₀ r₀ B)
    (hzc : K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ)) ∈ domainD n s₀ r₀ B) :
    invarianceError (hbold h f)
        (fun θ' => K θ' + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) ω' θ =
      ((gradC h ((fun i => (I i : ℂ)) + (K θ - unperturbedTorus I θ).2 +
            fun i => (((I' - I) i : ℝ) : ℂ)) -
          gradC h ((fun i => (I i : ℂ)) + (K θ - unperturbedTorus I θ).2) -
          gradC h ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)) +
          gradC h (fun i => (I i : ℂ)), 0) : (Fin n → ℂ) × (Fin n → ℂ)) +
        (hamiltonianVectorFieldℂ f
            (K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) -
          hamiltonianVectorFieldℂ f (K θ)) -
        fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ
          (fun i => (((ω' - ω) i : ℝ) : ℂ)) := by
  subst hωI hωI'
  have hr := hD.r₀_pos
  have hIr : I ∈ realDomain B r₀ := mem_realDomain_of_half hr (realInclusion_mem_half hr hI)
  have hI'r : I' ∈ realDomain B r₀ := mem_realDomain_of_half hr (realInclusion_mem_half hr hI')
  have hKθ : DifferentiableAt ℂ K θ :=
    hKd.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ)
  -- derivatives
  have hD1 : fderiv ℂ (fun θ' => K θ' + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) θ =
      fderiv ℂ K θ := fderiv_add_const _
  have hDK : fderiv ℂ K θ = fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ +
      ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) := by
    have h2 : HasFDerivAt (fun θ' => K θ' - unperturbedTorus I θ')
        (fderiv ℂ K θ - ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ)) θ :=
      hKθ.hasFDerivAt.sub (unperturbedTorus_hasFDerivAt I θ)
    rw [h2.fderiv]
    abel
  -- the frequencies
  have hfreq : (fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ)) =
      gradC h ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)) -
        gradC h (fun i => (I i : ℂ)) := by
    have e1 := (freq_map hD).2.1 I' hI'r
    have e2 := (freq_map hD).2.1 I hIr
    have e3 : ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)) =
        fun i => (I' i : ℂ) := by
      funext i; simp
    rw [e3, ← e1, ← e2]
    funext i; simp
  have hω : (fun i => ((frequencyMap h I' i : ℝ) : ℂ)) =
      (fun i => ((frequencyMap h I i : ℝ) : ℂ)) +
        fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ) := by
    funext i; simp
  -- the identity
  have hE := hKE θ hθ
  simp only [invarianceError, sub_eq_zero] at hE
  have e0 : hamiltonianVectorFieldℂ (hbold h f) (K θ) =
      (gradC h (K θ).2, 0) + hamiltonianVectorFieldℂ f (K θ) :=
    hamiltonianVectorField_hbold hD hP hz
  have e1 : hamiltonianVectorFieldℂ (hbold h f)
      (K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) =
      (gradC h ((K θ).2 + fun i => (((I' - I) i : ℝ) : ℂ)), 0) +
        hamiltonianVectorFieldℂ f
          (K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) :=
    hamiltonianVectorField_hbold hD hP hzc
  have hav : (fun i => (I i : ℂ)) + (K θ - unperturbedTorus I θ).2 = (K θ).2 := by
    simp [unperturbedTorus]
  have hDKΔ : fderiv ℂ K θ (fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ)) =
      fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ
          (fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ)) +
        (fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ), 0) := by
    rw [hDK]; rfl
  simp only [invarianceError]
  rw [hD1, hω, map_add, ← hE, hDKΔ, hfreq, e1, e0, hav]
  have := lipError_split (gradC h ((K θ).2 + fun i => (((I' - I) i : ℝ) : ℂ))) (gradC h (K θ).2)
    (gradC h ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)))
    (gradC h (fun i => (I i : ℂ)))
    (hamiltonianVectorFieldℂ f
      (K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))))
    (hamiltonianVectorFieldℂ f (K θ))
    (fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ
      (gradC h ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)) -
        gradC h (fun i => (I i : ℂ))))
  exact this

/-! ### Steps `step:p4:le-basic` and `step:p4:le-sum`: the estimate -/

/-- Steps `step:p4:le-basic` to `step:p4:le-sum` for an abstract torus `K`: if `K` is holomorphic
on `T_{s/8}` with `E = 0` at `ω = ∇h(I)` and `‖K - K⁰_I‖ ≤ η ≤ δ_*/2` there, and
`I' ∈ B` with `ω' = ∇h(I')`, `‖I' - I‖ ≤ min (δ_*/4, L₊ ‖ω' - ω‖)`, then the invariance error of
`K' = K + (0, ι (I' - I))` at `ω'` is at most
`(L₊ (H₃ η + F₂ ε) + n (s/32)⁻¹ η) ‖ω' - ω‖` on `T_{3s/32}`. -/
theorem invarianceError_shift_le (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hε : 0 ≤ ε) {I I' : Fin n → ℝ} (hI : I ∈ B) (hI' : I' ∈ B) {ω ω' : Fin n → ℝ}
    (hωI : frequencyMap h I = ω) (hωI' : frequencyMap h I' = ω')
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {η : ℝ}
    (hKd : DifferentiableOn ℂ K (complexStrip n (stripWidth s₀ / 8)))
    (hKE : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8), invarianceError (hbold h f) K ω θ = 0)
    (hKW : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8), ‖K θ - unperturbedTorus I θ‖ ≤ η)
    (hη : η ≤ deltaStar s₀ r₀ / 2) (hΔ : ‖I' - I‖ ≤ deltaStar s₀ r₀ / 4)
    (hLip : ‖I' - I‖ ≤ Lplus Lh * ‖ω' - ω‖) :
    ∀ θ ∈ complexStrip n (3 * stripWidth s₀ / 32),
      ‖invarianceError (hbold h f)
          (fun θ' => K θ' + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))) ω' θ‖ ≤
        (Lplus Lh * (Hconst s₀ r₀ B h 3 * η + Fconst n s₀ r₀ 2 * ε) +
          n * (stripWidth s₀ / 32)⁻¹ * η) * ‖ω' - ω‖ := by
  intro θ hθ
  have hs := stripWidth_pos hD.s₀_pos
  have hr := hD.r₀_pos
  have hδ := deltaStar_pos hD.s₀_pos hr
  have hδr := deltaStar_le_div s₀ r₀
  have hθ8 : θ ∈ complexStrip n (stripWidth s₀ / 8) := complexStrip_mono (by linarith) hθ
  have hθ4 : θ ∈ complexStrip n (stripWidth s₀ / 4) := complexStrip_mono (by linarith) hθ
  have hW := hKW θ hθ8
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hW
  have hcn : ‖((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))‖ = ‖I' - I‖ :=
    norm_shiftConst _
  have hsubD := ball_unperturbedTorus_subset_domainD (s₀ := s₀) hr hI hθ4
  have hz : K θ ∈ ball (unperturbedTorus I θ) (deltaStar s₀ r₀) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hzc : K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ)) ∈
      ball (unperturbedTorus I θ) (deltaStar s₀ r₀) := by
    rw [mem_ball, dist_eq_norm]
    have e : K θ + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ)) - unperturbedTorus I θ =
        (K θ - unperturbedTorus I θ) + ((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ)) := by
      abel
    rw [e]
    calc _ ≤ ‖K θ - unperturbedTorus I θ‖ +
          ‖((0 : Fin n → ℂ), fun i => (((I' - I) i : ℝ) : ℂ))‖ := norm_add_le _ _
      _ < _ := by rw [hcn]; linarith
  -- the identity
  rw [invarianceError_shift_eq hD hP hI hI' hωI hωI' hKd hKE hθ8 (hsubD hz) (hsubD hzc)]
  -- the three terms
  have hv : ‖(K θ - unperturbedTorus I θ).2‖ ≤ η := (norm_snd_le _).trans hW
  have hw : ‖fun i => (((I' - I) i : ℝ) : ℂ)‖ = ‖I' - I‖ := norm_realInclusion _
  have hpar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      (fun i => (I i : ℂ)) + t • (K θ - unperturbedTorus I θ).2 +
        t' • (fun i => (((I' - I) i : ℝ) : ℂ)) ∈ actionNbhd B (r₀ / 2) := by
    intro t ht t' ht'
    refine ⟨I, hI, ?_⟩
    have e : (fun i => (I i : ℂ)) + t • (K θ - unperturbedTorus I θ).2 +
        t' • (fun i => (((I' - I) i : ℝ) : ℂ)) - (fun i => (I i : ℂ)) =
        t • (K θ - unperturbedTorus I θ).2 + t' • (fun i => (((I' - I) i : ℝ) : ℂ)) := by
      abel
    rw [e]
    have h1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have h2 : |t'| ≤ 1 := by rw [abs_of_nonneg ht'.1]; exact ht'.2
    calc _ ≤ ‖t • (K θ - unperturbedTorus I θ).2‖ +
          ‖t' • (fun i => (((I' - I) i : ℝ) : ℂ))‖ := norm_add_le _ _
      _ = |t| * ‖(K θ - unperturbedTorus I θ).2‖ + |t'| * ‖I' - I‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw]
      _ ≤ 1 * η + 1 * ‖I' - I‖ :=
        add_le_add (mul_le_mul h1 hv (norm_nonneg _) zero_le_one)
          (mul_le_mul h2 le_rfl (norm_nonneg _) zero_le_one)
      _ < r₀ / 2 := by linarith
  have hPh := gradC_mixed_difference hD hpar
  have hPf := norm_hamiltonianVectorField_f_shift_le hD hP hI hθ4 hz hzc
  have hDW := norm_fderiv_sub_unperturbed_le hD.s₀_pos hKd hKW θ hθ
  have hH3 : 0 ≤ Hconst s₀ r₀ B h 3 := Parameters.Hconst_nonneg hD.s₀_pos hr 3
  have hF2 : 0 ≤ Fconst n s₀ r₀ 2 := (Parameters.Fconst_pos n hD.s₀_pos hr 2).le
  have hωn : ‖fun i => (((ω' - ω) i : ℝ) : ℂ)‖ = ‖ω' - ω‖ := norm_realInclusion _
  subst hωI hωI'
  set Δ : ℝ := ‖frequencyMap h I' - frequencyMap h I‖ with hΔdef
  set ΔI : ℝ := ‖I' - I‖ with hΔIdef
  have hT1 : ‖gradC h ((fun i => (I i : ℂ)) + (K θ - unperturbedTorus I θ).2 +
            fun i => (((I' - I) i : ℝ) : ℂ)) -
          gradC h ((fun i => (I i : ℂ)) + (K θ - unperturbedTorus I θ).2) -
          gradC h ((fun i => (I i : ℂ)) + fun i => (((I' - I) i : ℝ) : ℂ)) +
          gradC h (fun i => (I i : ℂ))‖ ≤ Hconst s₀ r₀ B h 3 * η * ΔI := by
    refine hPh.trans ?_
    rw [hw]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hH3) (norm_nonneg _)
  have hT2 := hPf.trans_eq (by rw [hcn])
  have hT3 : ‖fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ
      (fun i => (((frequencyMap h I' - frequencyMap h I) i : ℝ) : ℂ))‖ ≤
        n * (stripWidth s₀ / 32)⁻¹ * η * Δ := by
    refine ((fderiv ℂ (fun θ' => K θ' - unperturbedTorus I θ') θ).le_opNorm _).trans ?_
    rw [hωn]
    exact mul_le_mul_of_nonneg_right hDW (norm_nonneg _)
  have hsum : 0 ≤ Hconst s₀ r₀ B h 3 * η + Fconst n s₀ r₀ 2 * ε := by positivity
  have hmul := mul_le_mul_of_nonneg_left hLip hsum
  have key : ∀ x y z : (Fin n → ℂ) × (Fin n → ℂ), ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
    fun x y z => by linarith [norm_sub_le (x + y) z, norm_add_le x y]
  refine (key _ _ _).trans ?_
  rw [norm_pair_zero]
  nlinarith [hT1, hT2, hT3, hmul]

/-! ### The constants and the node -/

/-- Step `step:p4:le-sum`: the arithmetic, using `γ ≤ 1` and `ε ≥ 0`:
`L₊ (H₃ η₀ + F₂ ε) + n (s/32)⁻¹ η₀ ≤ A₁ ε γ⁻²` for `η₀ = A₀ ε γ⁻²`. -/
theorem lipError_const_le (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 ≤ ε) :
    Lplus Lh * (Hconst s₀ r₀ B h 3 * eta0 n τ s₀ r₀ gc ε γ + Fconst n s₀ r₀ 2 * ε) +
        n * (stripWidth s₀ / 32)⁻¹ * eta0 n τ s₀ r₀ gc ε γ ≤
      A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 := by
  have hs := stripWidth_pos hs₀
  have hL : 0 ≤ Lplus Lh := (Parameters.Lplus_pos Lh).le
  have hF2 : 0 ≤ Fconst n s₀ r₀ 2 := (Parameters.Fconst_pos n hs₀ hr₀ 2).le
  have hH3 : 0 ≤ Hconst s₀ r₀ B h 3 := Parameters.Hconst_nonneg hs₀ hr₀ 3
  have hγ2 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have he : ε ≤ ε / γ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_of_le_one_right hε hγ2
  have hη : eta0 n τ s₀ r₀ gc ε γ = A0 n τ s₀ r₀ gc * (ε / γ ^ 2) := by unfold eta0; ring
  have hA : A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 = A1 τ s₀ r₀ B h Lh gc * (ε / γ ^ 2) := by ring
  rw [hη, hA]
  calc _ ≤ Lplus Lh * (Hconst s₀ r₀ B h 3 * (A0 n τ s₀ r₀ gc * (ε / γ ^ 2)) +
          Fconst n s₀ r₀ 2 * (ε / γ ^ 2)) +
        n * (stripWidth s₀ / 32)⁻¹ * (A0 n τ s₀ r₀ gc * (ε / γ ^ 2)) := by
        gcongr
    _ = _ := by
        unfold A1
        field_simp

/-- Blueprint `bp:p4:lip-error`. -/
theorem lip_error (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω ω' : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) (hω' : ω' ∈ OmegaGamma h B τ γ)
    (hclose : ‖ω' - ω‖ ≤ lamStar Lh s₀ r₀ * γ ^ 2) :
    DifferentiableOn ℂ (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω')
      (complexStrip n (stripWidth s₀ / 8)) ∧
    IsPrimaryOnStrip (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') (stripWidth s₀ / 8) ∧
    IsRealOnReals (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') ∧
    (∀ θ, shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ - unperturbedTorus (invFreq h B ω') θ =
      normDisp τ s₀ r₀ B h f gc ε γ ω θ) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ - unperturbedTorus (invFreq h B ω') θ‖ ≤
        eta0 n τ s₀ r₀ gc ε γ) ∧
    ∀ θ ∈ complexStrip n (3 * stripWidth s₀ / 32),
      ‖invarianceError (hbold h f) (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') ω' θ‖ ≤
        A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖ := by
  have hr := hD.r₀_pos
  have hS := smallness hD hgc.toPos hSA
  have hinv := inverse_freq hD
  obtain ⟨hIB, hfreq, -⟩ := hinv.2.2.1 ω hω.1
  obtain ⟨hIB', hfreq', -⟩ := hinv.2.2.1 ω' hω'.1
  have hLip : ‖invFreq h B ω' - invFreq h B ω‖ ≤ Lplus Lh * ‖ω' - ω‖ :=
    hinv.2.2.2.1 ω' hω'.1 ω hω.1
  obtain ⟨hNd, hNp, hNr, hNE, -, -, -, hNW⟩ := normalize hD hP hgc hSA hω
  have hshift : ∀ θ, shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ =
      normTorus τ s₀ r₀ B h f gc ε γ ω θ +
        ((0 : Fin n → ℂ), fun i => (((invFreq h B ω' - invFreq h B ω) i : ℝ) : ℂ)) :=
    fun θ => rfl
  have hdisp : ∀ θ, shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ -
      unperturbedTorus (invFreq h B ω') θ = normDisp τ s₀ r₀ B h f gc ε γ ω θ := by
    intro θ
    rw [hshift]
    ext i
    · simp [normDisp, unperturbedTorus]
    · simp [normDisp, unperturbedTorus]; ring
  refine ⟨?_, ?_, ?_, hdisp, fun θ hθ => (hdisp θ).symm ▸ hNW θ hθ, ?_⟩
  · exact (hNd.add_const _).congr fun θ _ => (hshift θ).symm
  · intro θ hθ k
    rw [hshift, hshift, hNp θ hθ k]
    exact add_right_comm _ _ _
  · intro x
    obtain ⟨z, hz⟩ := hNr x
    refine ⟨(z.1, z.2 + (invFreq h B ω' - invFreq h B ω)), ?_⟩
    rw [hshift, hz]
    ext i <;> simp
  · intro θ hθ
    have hs := stripWidth_pos hD.s₀_pos
    have hδ := deltaStar_pos hD.s₀_pos hr
    have hγ2 : γ ^ 2 ≤ 1 := pow_le_one₀ hSA.gamma_pos.le hSA.gamma_le
    have hη : eta0 n τ s₀ r₀ gc ε γ ≤ deltaStar s₀ r₀ / 2 := by
      have := hS.2.2.1.2.2.1
      unfold muParam at this
      linarith
    have hΔ : ‖invFreq h B ω' - invFreq h B ω‖ ≤ deltaStar s₀ r₀ / 4 := by
      have hLl : Lplus Lh * lamStar Lh s₀ r₀ = deltaStar s₀ r₀ / 4 := by
        unfold lamStar
        have := (Parameters.Lplus_pos Lh).ne'
        field_simp
      calc _ ≤ Lplus Lh * ‖ω' - ω‖ := hLip
        _ ≤ Lplus Lh * (lamStar Lh s₀ r₀ * γ ^ 2) :=
            mul_le_mul_of_nonneg_left hclose (Parameters.Lplus_pos Lh).le
        _ = deltaStar s₀ r₀ / 4 * γ ^ 2 := by rw [← mul_assoc, hLl]
        _ ≤ deltaStar s₀ r₀ / 4 := mul_le_of_le_one_right (by positivity) hγ2
    have hbound := invarianceError_shift_le hD hP hSA.eps_nonneg hIB hIB' hfreq hfreq' hNd hNE
      (fun θ hθ => hNW θ hθ) hη hΔ hLip θ hθ
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (lipError_const_le hD.s₀_pos hr hSA.gamma_pos hSA.gamma_le hSA.eps_nonneg)
      (norm_nonneg _))

end KAM.Head

end
