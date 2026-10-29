/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Coefficients
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Cauchy estimates in the weighted norm (`bpN:p4:cauchy`)

For `u` in the class `O(r₀, s₀)` with `|u|_{r₀,s₀} ≤ M`:

* `cauchy_theta` (a): the angular derivatives lose width `s₀ - s` and a factor `1/(e (s₀ - s))`,
  *summed over `j` inside the supremum* pointwise in `I`, and individually in the global norm. The
  proof is coefficientwise: `û_k(∂_{θⱼ}u) = 2πi kⱼ û_k(u)`, `∑ⱼ 2π |kⱼ| = 2π |k|₁` and
  `x e^{-ax} ≤ 1/(e a)` (`KAM.Fourier.mul_exp_radius_sub_le`).
* `cauchy_action` (b): the action derivatives lose radius `r₀ - r` and a factor `1/(r₀ - r)`. For a
  finite set `Λ` of modes, norming functionals `λ_k` of the derivatives `∂_{Iᵢ}û_k(I)` give the
  scalar holomorphic function `J ↦ ∑_{k ∈ Λ} e^{2π s₀|k|₁} λ_k(û_k(J))`, bounded by `M` on the ball
  `B(I, r₀ - r) ⊆ V_{r₀} D`; `general_cauchy` bounds its derivative at `I`, which is the finite
  weighted sum of the derivative coefficients. The sum over modes thus stays inside the Cauchy
  estimate (no `∑ₖ sup_I`).
* `cauchy_loss`: the same with losses `σ`, `ρ`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Weighted

-- The signatures keep the instance block `[NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W]
-- [FiniteDimensional ℂ W]` (consumers supply it); several lemmas do not need all of it.
set_option linter.unusedSectionVars false

variable {n m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]

/-! ### Angular derivatives -/

/-- The weighted norms of the coefficients of `∂_{θⱼ}u` are `2π |kⱼ|` times those of `u`. -/
private theorem norm_coeff_dtheta {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : InClass D r s u) (j : Fin n)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    ‖coeff (dtheta j u) I k‖ = 2 * Real.pi * |(k j : ℝ)| * ‖coeff u I k‖ := by
  rw [(coefficients_deriv hs hu).1 j |>.2 I hI k, norm_smul]
  congr 1
  rw [norm_mul, norm_mul, norm_mul]
  simp [abs_of_pos Real.pi_pos]

/-- Termwise angular Cauchy estimate: `∑ⱼ 2π |kⱼ| = 2π |k|₁` is absorbed by the width loss. -/
private theorem theta_weight_le {s₀ s : ℝ} (hss : s < s₀) (a : ℝ) (ha : 0 ≤ a)
    (k : Fin n → ℤ) :
    (∑ j : Fin n, 2 * Real.pi * |(k j : ℝ)| * a) * modeWeight s k ≤
      (1 / (Real.exp 1 * (s₀ - s))) * (a * modeWeight s₀ k) := by
  have hpi := Real.pi_pos
  have hs : 0 < s₀ - s := by linarith
  have hδ : 0 < 2 * Real.pi * (s₀ - s) := by positivity
  unfold modeWeight
  set x : ℝ := KAM.Fourier.modeSize k with hxdef
  have hsum : ∑ j : Fin n, 2 * Real.pi * |(k j : ℝ)| * a = 2 * Real.pi * x * a := by
    rw [hxdef]
    unfold KAM.Fourier.modeSize
    rw [Finset.mul_sum, Finset.sum_mul]
  have hx := KAM.Fourier.mul_exp_radius_sub_le (2 * Real.pi * s₀) x hδ
  have hexp : (2 * Real.pi * s₀ - 2 * Real.pi * (s₀ - s)) * x = 2 * Real.pi * s * x := by ring
  rw [hexp] at hx
  rw [hsum]
  have hcalc : 2 * Real.pi * x * a * Real.exp (2 * Real.pi * s * x) =
      (2 * Real.pi * a) * (x * Real.exp (2 * Real.pi * s * x)) := by ring
  rw [hcalc]
  have h1 : (2 * Real.pi * a) * (x * Real.exp (2 * Real.pi * s * x)) ≤
      (2 * Real.pi * a) * ((Real.exp (-1) / (2 * Real.pi * (s₀ - s))) *
        Real.exp (2 * Real.pi * s₀ * x)) :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  refine h1.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- `bpN:p4:cauchy` (a): angular derivative, pointwise in `I`, summed over `j` *inside* the
supremum, plus the global single-`j` form. -/
theorem cauchy_theta {D : Set (Fin m → ℂ)} {r₀ s₀ s M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hu : InClass D r₀ s₀ u) (hb : WBound D r₀ s₀ u M) (hs0 : 0 < s) (hs : s < s₀) :
    (∀ I ∈ polyNbhd D r₀, (∀ j, WSummable (dtheta j u) s I) ∧
      ∑ j, wsum (dtheta j u) s I ≤ wsum u s₀ I / (Real.exp 1 * (s₀ - s))) ∧
    ∀ j, WBound D r₀ s (dtheta j u) (M / (Real.exp 1 * (s₀ - s))) := by
  have hs₀ : 0 < s₀ := hs0.trans hs
  have hsub : 0 < s₀ - s := by linarith
  have key : ∀ I ∈ polyNbhd D r₀, (∀ j, WSummable (dtheta j u) s I) ∧
      ∑ j, wsum (dtheta j u) s I ≤ wsum u s₀ I / (Real.exp 1 * (s₀ - s)) := by
    intro I hI
    have hsum := (hb I hI).1
    set c : ℝ := 1 / (Real.exp 1 * (s₀ - s)) with hc
    have hc0 : 0 ≤ c := by positivity
    have hterm : ∀ k, ∑ j, ‖coeff (dtheta j u) I k‖ * modeWeight s k ≤
        c * (‖coeff u I k‖ * modeWeight s₀ k) := fun k => by
      have h := theta_weight_le (n := n) hs (‖coeff u I k‖) (norm_nonneg _) k
      rw [Finset.sum_mul] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_coeff_dtheta hs₀ hu j hI k]
    have hnn : ∀ j k, 0 ≤ ‖coeff (dtheta j u) I k‖ * modeWeight s k := fun j k =>
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    have hj : ∀ j, WSummable (dtheta j u) s I := fun j =>
      Summable.of_nonneg_of_le (hnn j) (fun k =>
        (Finset.single_le_sum (f := fun j' => ‖coeff (dtheta j' u) I k‖ * modeWeight s k)
          (fun j' _ => hnn j' k) (Finset.mem_univ j)).trans (hterm k)) (hsum.mul_left c)
    refine ⟨hj, ?_⟩
    unfold wsum
    rw [← Summable.tsum_finsetSum fun j _ => hj j]
    calc ∑' k, ∑ j, ‖coeff (dtheta j u) I k‖ * modeWeight s k
        ≤ ∑' k, c * (‖coeff u I k‖ * modeWeight s₀ k) :=
          Summable.tsum_le_tsum hterm (summable_sum fun j _ => hj j) (hsum.mul_left c)
      _ = c * ∑' k, ‖coeff u I k‖ * modeWeight s₀ k := tsum_mul_left
      _ = (∑' k, ‖coeff u I k‖ * modeWeight s₀ k) / (Real.exp 1 * (s₀ - s)) := by
          rw [hc]; ring
  refine ⟨key, fun j I hI => ?_⟩
  obtain ⟨hj, hle⟩ := key I hI
  refine ⟨hj j, ?_⟩
  have hw : ∀ j', 0 ≤ wsum (dtheta j' u) s I := fun j' =>
    tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have h1 : wsum (dtheta j u) s I ≤ ∑ j', wsum (dtheta j' u) s I :=
    Finset.single_le_sum (f := fun j' => wsum (dtheta j' u) s I) (fun j' _ => hw j')
      (Finset.mem_univ j)
  have h2 : wsum u s₀ I ≤ M := (hb I hI).2
  have hpos : 0 < Real.exp 1 * (s₀ - s) := by positivity
  exact h1.trans (hle.trans (div_le_div_of_nonneg_right h2 hpos.le))

/-! ### Action derivatives -/

/-- Finite partial sums of the weighted derivative coefficients are bounded by `M / (r₀ - r)`: the
Cauchy estimate for `J ↦ ∑_{k ∈ Λ} w_k λ_k(û_k(J))` on `B(I, r₀ - r)`. -/
private theorem action_partial_sum_le {D : Set (Fin m → ℂ)} {r₀ r s₀ M : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s₀) (hu : InClass D r₀ s₀ u)
    (hb : WBound D r₀ s₀ u M) (hr : r < r₀) (i : Fin m) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) (Λ : Finset (Fin n → ℤ)) :
    ∑ k ∈ Λ, ‖coeff (dI i u) I k‖ * modeWeight s₀ k ≤ M / (r₀ - r) := by
  have hR : 0 < r₀ - r := sub_pos.mpr hr
  have hball : ball I (r₀ - r) ⊆ polyNbhd D r₀ := by
    intro J hJ
    obtain ⟨I', hI'D, hI'⟩ := hI
    refine ⟨I', hI'D, ?_⟩
    rw [mem_ball, dist_eq_norm] at hJ
    calc ‖J - I'‖ = ‖(J - I) + (I - I')‖ := by congr 1; abel
      _ ≤ ‖J - I‖ + ‖I - I'‖ := norm_add_le _ _
      _ < r₀ := by linarith
  have hI₀ : I ∈ polyNbhd D r₀ := polyNbhd_mono hr.le hI
  have hcoef : ∀ k, coeff (dI i u) I k = fderiv ℂ (fun I' => coeff u I' k) I (Pi.single i 1) :=
    fun k => ((coefficients_deriv hs hu).2 i).2 I hI₀ k
  choose g hgn hgv using fun k => exists_dual_vector'' ℂ (coeff (dI i u) I k)
  set w : (Fin n → ℤ) → ℝ := fun k => modeWeight s₀ k with hw
  set H : (Fin m → ℂ) → ℂ := fun J => ∑ k ∈ Λ, (w k : ℂ) * g k (coeff u J k) with hH
  have hdiff : ∀ k, DifferentiableAt ℂ (fun J => coeff u J k) I := fun k =>
    ((coeff_differentiableOn hs hu k).differentiableAt ((isOpen_polyNbhd D r₀).mem_nhds hI₀))
  have hHdiff : DifferentiableOn ℂ H (ball I (r₀ - r)) := by
    intro J hJ
    have hJ₀ : J ∈ polyNbhd D r₀ := hball hJ
    have hat : ∀ k, DifferentiableAt ℂ (fun J => coeff u J k) J := fun k =>
      ((coeff_differentiableOn hs hu k).differentiableAt ((isOpen_polyNbhd D r₀).mem_nhds hJ₀))
    refine DifferentiableAt.differentiableWithinAt ?_
    exact DifferentiableAt.fun_sum fun k _ =>
      ((g k).differentiableAt.comp J (hat k)).const_mul _
  have hHbound : ∀ J ∈ ball I (r₀ - r), ‖H J‖ ≤ M := by
    intro J hJ
    have hJ₀ : J ∈ polyNbhd D r₀ := hball hJ
    obtain ⟨hsm, hle⟩ := hb J hJ₀
    calc ‖H J‖ ≤ ∑ k ∈ Λ, ‖(w k : ℂ) * g k (coeff u J k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Λ, ‖coeff u J k‖ * modeWeight s₀ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (show 0 ≤ w k from (Real.exp_pos _).le)]
          have h1 : ‖g k (coeff u J k)‖ ≤ ‖coeff u J k‖ :=
            ((g k).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hgn k))
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right h1 (show 0 ≤ w k from (Real.exp_pos _).le)
      _ ≤ ∑' k, ‖coeff u J k‖ * modeWeight s₀ k :=
          hsm.sum_le_tsum Λ fun k _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ M := hle
  have hcauchy := general_cauchy hR hHdiff hHbound
  -- the derivative of `H` at `I` in the direction `e_i`
  have hder : fderiv ℂ H I (Pi.single i 1) =
      ((∑ k ∈ Λ, ‖coeff (dI i u) I k‖ * modeWeight s₀ k : ℝ) : ℂ) := by
    have hk : ∀ k ∈ Λ, HasFDerivAt (fun J => (w k : ℂ) * g k (coeff u J k))
        ((w k : ℂ) • (g k).comp (fderiv ℂ (fun J => coeff u J k) I)) I := fun k _ =>
      ((g k).hasFDerivAt.comp I (hdiff k).hasFDerivAt).const_mul _
    rw [(HasFDerivAt.fun_sum hk).fderiv]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoef k, hgv k]
    simp [hw, mul_comm]
  have hnorm : ‖fderiv ℂ H I (Pi.single i 1)‖ ≤ M / (r₀ - r) := by
    calc ‖fderiv ℂ H I (Pi.single i 1)‖ ≤ ‖fderiv ℂ H I‖ * ‖(Pi.single i 1 : Fin m → ℂ)‖ :=
          (fderiv ℂ H I).le_opNorm _
      _ ≤ M / (r₀ - r) * 1 := by
          rw [Pi.norm_single, norm_one]
          exact mul_le_mul_of_nonneg_right hcauchy zero_le_one
      _ = M / (r₀ - r) := mul_one _
  have hnn : 0 ≤ ∑ k ∈ Λ, ‖coeff (dI i u) I k‖ * modeWeight s₀ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  rw [hder, Complex.norm_real, Real.norm_of_nonneg hnn] at hnorm
  exact hnorm

/-- `bpN:p4:cauchy` (b): action derivative, global. -/
theorem cauchy_action {D : Set (Fin m → ℂ)} {r₀ r s₀ M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s₀) (hu : InClass D r₀ s₀ u) (hb : WBound D r₀ s₀ u M) (hr : r < r₀) :
    ∀ i, WBound D r s₀ (dI i u) (M / (r₀ - r)) := by
  intro i I hI
  have hnn : ∀ k, 0 ≤ ‖coeff (dI i u) I k‖ * modeWeight s₀ k := fun k =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hpart := action_partial_sum_le hs hu hb hr i hI
  exact ⟨summable_of_sum_le hnn hpart, (summable_of_sum_le hnn hpart).tsum_le_of_sum_le hpart⟩

/-! ### Losses -/

-- `hρr : ρ < r` is part of the signature (`r - ρ > 0` is not needed by the proof: for `r ≤ ρ` the
-- region `V_{r-ρ} D` is empty), so the unused-variable linter is silenced for this statement only.
set_option linter.unusedVariables false in
/-- `bpN:p4:cauchy`, "in particular" (losses `σ`, `ρ`): `|∂θ u|_{r,s-σ} ≤ |u|_{r,s}/(eσ)`,
`|∂I u|_{r-ρ,s} ≤ |u|_{r,s}/ρ`. -/
theorem cauchy_loss {D : Set (Fin m → ℂ)} {r s ρ σ M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hu : InClass D r s u) (hb : WBound D r s u M) (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ)
    (hσs : σ < s) :
    (∀ I ∈ polyNbhd D r, ∑ j, wsum (dtheta j u) (s - σ) I ≤ M / (Real.exp 1 * σ)) ∧
    (∀ j, WBound D r (s - σ) (dtheta j u) (M / (Real.exp 1 * σ))) ∧
    (∀ i, WBound D (r - ρ) s (dI i u) (M / ρ)) := by
  have hs : 0 < s := hσ.trans hσs
  have hsσ : 0 < s - σ := sub_pos.mpr hσs
  have hlt : s - σ < s := by linarith
  have hθ := cauchy_theta hu hb hsσ hlt
  have hdiff : s - (s - σ) = σ := by ring
  rw [hdiff] at hθ
  refine ⟨fun I hI => ?_, hθ.2, ?_⟩
  · refine (hθ.1 I hI).2.trans ?_
    exact div_le_div_of_nonneg_right (hb I hI).2 (by positivity)
  · have h := cauchy_action hs hu hb (show r - ρ < r by linarith)
    have hdiff' : r - (r - ρ) = ρ := by ring
    rw [hdiff'] at h
    exact h

end KAM.Weighted

end
