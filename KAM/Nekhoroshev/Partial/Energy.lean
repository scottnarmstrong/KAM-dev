/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Bracket
public import KAM.Nekhoroshev.Partial.EnergyIdentity
public import KAM.Nekhoroshev.Stability.Setting

/-!
# Energy confinement near a resonance, convex case, no bound on `ω` (Part 11, package N11-L2)

`energy_free` (`bpN:p11:energy-free`): an orbit of `h + g + fs` in the extended phase space that
starts in the `δ/(4M)`-ball around `Ic` and keeps its slow part in the half-radius tube moves its
fast action by at most `r/4` for times `|t| ≤ s m r/(20 M ζ)`.  The proof is by contradiction at
the first exit time of the `r/4`-ball (`exit_ball`): the energy inequality (`ef-en`), the
frequency-free identity of `EnergyIdentity` (`ef-id`, `ef-C`) and the Cauchy estimates on the
half-radius tube (`ef-tube`, `ef-adm`) give `(3/16) m Δ² ≤ A + C`, which is absurd (`ef-contra`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm
open KAM.Stability (IsOrthProj hessR clm_eq_dot euclid_sq_eq_dot abs_dot_le_euclid)

variable {n k : ℕ}

/-! ### Euclidean and projection algebra -/

private theorem ef_euclid_nonneg (x : Fin n → ℝ) : 0 ≤ euclid x := Real.sqrt_nonneg _

private theorem ef_euclid_le_sum (x : Fin n → ℝ) : euclid x ≤ ∑ i, |x i| := by
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

private theorem ef_orth_sq {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (v : Fin n → ℝ) : euclid (P v) ^ 2 = v ⬝ᵥ P v := by
  rw [euclid_sq_eq_dot, hP.symm v (P v), hP.idem]

private theorem ef_le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ a * b) :
    a ≤ b := by
  by_contra hlt
  push Not at hlt
  nlinarith [mul_pos (lt_of_le_of_lt hb hlt) (sub_pos.2 hlt)]

private theorem ef_orth_euclid_le {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (v : Fin n → ℝ) : euclid (P v) ≤ euclid v := by
  refine ef_le_of_sq_le (ef_euclid_nonneg _) (ef_euclid_nonneg _) ?_
  rw [ef_orth_sq hP, dotProduct_comm]
  exact (le_abs_self _).trans (abs_dot_le_euclid _ _)

/-- `‖Π ω(Ic)‖₂ ≤ δ` from the dual form of `NearResonance`. -/
private theorem ef_proj_freq_le {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {Ic : Fin n → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hnr : NearResonance Λ h Ic δ)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (hPV : ∀ v, P v ∈ KAM.Stability.resSpan Λ) :
    euclid (P (KAM.frequencyMap h Ic)) ≤ δ := by
  refine ef_le_of_sq_le (ef_euclid_nonneg _) hδ ?_
  have h1 := hnr _ (hPV (KAM.frequencyMap h Ic))
  have h2 : KAM.frequencyMap h Ic ⬝ᵥ P (KAM.frequencyMap h Ic) ≤
      δ * euclid (P (KAM.frequencyMap h Ic)) := (le_abs_self _).trans h1
  rw [ef_orth_sq hP, mul_comm]
  exact h2

/-! ### Real analysis of the fast part -/

private theorem ef_realPart_contDiffOn {Ic : Fin n → ℝ} {R : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)) :
    ContDiffOn ℝ 2 (realPart h) (ball Ic R) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_polyNbhd _ R) hh
  have h1 : ContDiffOn ℝ ∞ h (polyNbhd {KAM.realInclusion n Ic} R) :=
    hreg.2.2.1.restrict_scalars ℝ
  have hmem : ∀ x ∈ ball Ic R, KAM.realInclusion n x ∈ polyNbhd {KAM.realInclusion n Ic} R :=
    fun x hx => ⟨_, rfl, by rw [← map_sub, KAM.norm_realInclusion]; exact mem_ball_iff_norm.1 hx⟩
  have h2 : ContDiffOn ℝ ∞ (fun x => h (KAM.realInclusion n x)) (ball Ic R) :=
    h1.comp (KAM.realInclusion n).contDiff.contDiffOn hmem
  exact (Complex.reCLM.contDiff.comp_contDiffOn h2).of_le
    (by exact WithTop.coe_le_coe.2 le_top)

private theorem ef_hess_abs_le {hR : (Fin n → ℝ) → ℝ} {I : Fin n → ℝ} {M : ℝ}
    (hM : ∀ v, euclid (fun i => fderiv ℝ (fderiv ℝ hR) I (Pi.single i 1) v) ≤ M * euclid v)
    (ξ η : Fin n → ℝ) : |hessR hR I ξ η| ≤ M * euclid ξ * euclid η := by
  have e : hessR hR I ξ η =
      (fun i => fderiv ℝ (fderiv ℝ hR) I (Pi.single i 1) η) ⬝ᵥ ξ := by
    have := clm_eq_dot ((fderiv ℝ (fderiv ℝ hR) I).flip η) ξ
    unfold hessR
    simpa [ContinuousLinearMap.flip_apply] using this
  rw [e]
  refine (abs_dot_le_euclid _ _).trans ?_
  calc _ ≤ (M * euclid η) * euclid ξ :=
        mul_le_mul_of_nonneg_right (hM η) (ef_euclid_nonneg _)
    _ = _ := by ring

private theorem ef_taylor_segment {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    (hhR : ContDiffOn ℝ 2 hR U) {x Δ : Fin n → ℝ} (hseg : ∀ a ∈ Icc (0 : ℝ) 1, x + a • Δ ∈ U) :
    ∃ a ∈ Ioo (0 : ℝ) 1, hR (x + Δ) - hR x - fderiv ℝ hR x Δ =
      1 / 2 * hessR hR (x + a • Δ) Δ Δ := by
  set φ : ℝ → ℝ := fun a => hR (x + a • Δ) with hφ
  have hp : ∀ a : ℝ, HasDerivAt (fun a : ℝ => x + a • Δ) Δ a := fun a => by
    simpa using ((hasDerivAt_id a).smul_const Δ).const_add x
  have hat : ∀ a : ℝ, x + a • Δ ∈ U → ContDiffAt ℝ 2 hR (x + a • Δ) := fun a ha =>
    hhR.contDiffAt (hU.mem_nhds ha)
  have hd1 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt φ (fderiv ℝ hR (x + a • Δ) Δ) a := fun a ha =>
    ((hat a ha).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a (hp a)
  have hd2 : ∀ a : ℝ, x + a • Δ ∈ U → HasDerivAt (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (hessR hR (x + a • Δ) Δ Δ) a := fun a ha => by
    have h1 : DifferentiableAt ℝ (fderiv ℝ hR) (x + a • Δ) :=
      ((hat a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h2 := h1.hasFDerivAt.comp_hasDerivAt a (hp a)
    exact (ContinuousLinearMap.apply ℝ ℝ Δ).hasFDerivAt.comp_hasDerivAt a h2
  have hS : IsOpen {a : ℝ | x + a • Δ ∈ U} :=
    hU.preimage (by fun_prop)
  have hderiv : ∀ a ∈ {a : ℝ | x + a • Δ ∈ U}, deriv φ a = fderiv ℝ hR (x + a • Δ) Δ :=
    fun a ha => (hd1 a ha).deriv
  have hcd : ∀ a ∈ uIcc (0 : ℝ) 1, ContDiffAt ℝ 2 φ a := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    exact (hat a (hseg a ha')).comp a (by fun_prop : ContDiffAt ℝ 2 (fun a : ℝ => x + a • Δ) a)
  have hcdOn : ContDiffOn ℝ 2 φ (uIcc 0 1) := fun a ha => (hcd a ha).contDiffWithinAt
  have hud : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact uniqueDiffOn_Icc zero_lt_one
  have hit1 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 1 φ (uIcc 0 1) a = deriv φ a :=
      fun a ha => by
    rw [iteratedDerivWithin_eq_iteratedDeriv hud ((hcd a ha).of_le (by norm_num)) ha,
      iteratedDeriv_one]
  have hit2 : ∀ a ∈ uIcc (0 : ℝ) 1, iteratedDerivWithin 2 φ (uIcc 0 1) a =
      hessR hR (x + a • Δ) Δ Δ := fun a ha => by
    have ha' : a ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ha
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hcd a ha) ha, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hev : deriv φ =ᶠ[nhds a] fun a => fderiv ℝ hR (x + a • Δ) Δ :=
      Filter.eventuallyEq_of_mem (hS.mem_nhds (hseg a ha')) hderiv
    rw [hev.deriv_eq]
    exact (hd2 a (hseg a ha')).deriv
  have hIoo : ∀ a ∈ uIoo (0 : ℝ) 1, a ∈ uIcc (0 : ℝ) 1 := fun a ha => by
    rw [uIoo_of_le zero_le_one] at ha
    rw [uIcc_of_le zero_le_one]
    exact Ioo_subset_Icc_self ha
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 1 φ (uIcc 0 1)) (uIoo 0 1) := by
    have h0 : ∀ a ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ (fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ) a :=
      fun a ha => (hd2 a (hseg a (by simpa [uIcc_of_le zero_le_one] using ha))).differentiableAt
    refine DifferentiableOn.congr (f := fun a : ℝ => fderiv ℝ hR (x + a • Δ) Δ)
      (fun a ha => (h0 a (hIoo a ha)).differentiableWithinAt) fun a ha => ?_
    rw [hit1 a (hIoo a ha)]
    exact hderiv a (hseg a (by simpa [uIcc_of_le zero_le_one] using hIoo a ha))
  obtain ⟨a, ha, h⟩ := taylor_mean_remainder_lagrange (n := 1) (x₀ := 0) (x := 1) zero_ne_one
    (hcdOn.of_le (by norm_num)) hdiff
  have ha' : a ∈ Ioo (0 : ℝ) 1 := by simpa [uIoo_of_le zero_le_one] using ha
  refine ⟨a, ha', ?_⟩
  rw [hit2 a (hIoo a ha), taylorWithinEval_succ, taylor_within_zero_eval,
    hit1 0 (by simp), hderiv 0 (by simpa using hseg 0 (by simp))] at h
  simp only [hφ, zero_smul, add_zero, one_smul] at h
  simp at h
  linarith

/-- Mean value inequality for the gradient in the Euclidean size, from a Hessian bound. -/
private theorem ef_hess_lipschitz {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    (h2 : ContDiffOn ℝ 2 hR U) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ I ∈ U, ∀ ξ η, |hessR hR I ξ η| ≤ M * euclid ξ * euclid η) {I J : Fin n → ℝ}
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, J + a • (I - J) ∈ U) :
    euclid ((fun i => fderiv ℝ hR I (Pi.single i 1)) - fun i => fderiv ℝ hR J (Pi.single i 1)) ≤
      M * euclid (I - J) := by
  set v : Fin n → ℝ :=
    (fun i => fderiv ℝ hR I (Pi.single i 1)) - fun i => fderiv ℝ hR J (Pi.single i 1) with hv
  set Δ : Fin n → ℝ := I - J with hΔ
  have hp : ∀ a : ℝ, HasDerivAt (fun a : ℝ => J + a • Δ) Δ a := fun a => by
    simpa using ((hasDerivAt_id a).smul_const Δ).const_add J
  have hat : ∀ a ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 hR (J + a • Δ) := fun a ha =>
    h2.contDiffAt (hU.mem_nhds (hseg a ha))
  have hd : ∀ a ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun a : ℝ => fderiv ℝ hR (J + a • Δ) v)
      (hessR hR (J + a • Δ) Δ v) (Icc (0 : ℝ) 1) a := fun a ha => by
    have h1 : DifferentiableAt ℝ (fderiv ℝ hR) (J + a • Δ) :=
      ((hat a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h3 := h1.hasFDerivAt.comp_hasDerivAt a (hp a)
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt a h3).hasDerivWithinAt
  have hbd : ∀ a ∈ Icc (0 : ℝ) 1, ‖hessR hR (J + a • Δ) Δ v‖ ≤ M * euclid Δ * euclid v :=
    fun a ha => by
      rw [Real.norm_eq_abs]
      exact hM _ (hseg a ha) _ _
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd (convex_Icc 0 1)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have hval : fderiv ℝ hR (J + (1 : ℝ) • Δ) v - fderiv ℝ hR (J + (0 : ℝ) • Δ) v =
      euclid v ^ 2 := by
    have e1 : J + (1 : ℝ) • Δ = I := by rw [hΔ, one_smul]; abel
    have e0 : J + (0 : ℝ) • Δ = J := by rw [zero_smul, add_zero]
    rw [e1, e0, clm_eq_dot (fderiv ℝ hR I), clm_eq_dot (fderiv ℝ hR J), ← sub_dotProduct,
      euclid_sq_eq_dot]
  rw [hval, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sub_zero, norm_one, mul_one] at hmv
  have hE : 0 ≤ euclid v := ef_euclid_nonneg v
  rcases hE.eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg hM0 (ef_euclid_nonneg _)
  · nlinarith [mul_pos h h]

end KAM.Nekhoroshev

end
