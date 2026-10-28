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

/-! ### Domains, orbits and the fast action -/

private theorem ef_mem_realDom_iff (b : PartialBlock n k) (R : ℝ) (z : ER n k) :
    z ∈ b.realDom R ↔ (extCx z).2 ∈ polyNbhd b.base R := by
  simp only [PartialBlock.realDom, Set.mem_ofPred_eq, Dom, mem_prod]
  exact ⟨fun h => h.2, fun h => ⟨KAM.ofReal_mem_complexStrip one_pos z.1, h⟩⟩

/-- Step `ef-tube`: a real point with fast action `ρ`-close to `Ic` and slow part `ρ`-close to
`λ⁻¹ S` lies in the real domain of radius `ρ`. -/
private theorem ef_mem_realDom_of_tube (b : PartialBlock n k) {ρ : ℝ} {z : ER n k}
    (hI : euclid (fastAction z - b.Ic) < ρ) {v : KAM.Planetary.Phase k} (hv : v ∈ b.S)
    (hsl : ‖slowPair z - b.lam⁻¹ • v‖ < ρ) : z ∈ b.realDom ρ := by
  rw [ef_mem_realDom_iff]
  refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hsl
  refine (pi_norm_lt_iff hρ).2 fun j => ?_
  have hmax := Prod.norm_def (slowPair z - b.lam⁻¹ • v)
  have h1 : ‖(slowPair z - b.lam⁻¹ • v).1‖ < ρ := by
    refine lt_of_le_of_lt ?_ hsl
    rw [hmax]
    exact le_max_left _ _
  have h2 : ‖(slowPair z - b.lam⁻¹ • v).2‖ < ρ := by
    refine lt_of_le_of_lt ?_ hsl
    rw [hmax]
    exact le_max_right _ _
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · simp only [Pi.sub_apply, Fin.append_left]
    simp only [extCx]
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact lt_of_le_of_lt ((norm_le_pi_norm (fastAction z - b.Ic) i).trans
      (norm_le_euclid _).1) hI
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j'
    · simp only [Pi.sub_apply, Fin.append_right, Fin.append_left]
      simp only [extCx]
      rw [← Complex.ofReal_sub, Complex.norm_real]
      refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (norm_le_pi_norm _ i) h1)
      simp [slowPair, div_eq_inv_mul]
    · simp only [Pi.sub_apply, Fin.append_right]
      simp only [extCx]
      rw [← Complex.ofReal_sub, Complex.norm_real]
      refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (norm_le_pi_norm _ i) h2)
      simp [slowPair, div_eq_inv_mul]

private theorem ef_fast_continuousOn {b : PartialBlock n k} {R : ℝ} {H : EC n k → ℂ} {J : Set ℝ}
    {y : ℝ → ER n k} (hy : ExtOrbit b R H J y) :
    ContinuousOn (fun t => ((0 : Fin n → ℝ), fastAction (y t))) J := by
  have hyc : ContinuousOn y J := KAM.ODE.IsSolutionIn.continuousOn hy
  refine continuousOn_const.prodMk (continuousOn_pi.2 fun i => ?_)
  exact ((continuous_apply (Fin.castAdd (k + k) i)).comp continuous_snd).comp_continuousOn hyc

/-- A segment starting `ρ₀`-close to `Ic` and of Euclidean length `≤ ρ` stays in the ball. -/
private theorem ef_seg_mem {Ic I₀ I : Fin n → ℝ} {R ρ : ℝ} (h0 : euclid (I₀ - Ic) + ρ < R)
    (hI : euclid (I - I₀) ≤ ρ) : ∀ a ∈ Icc (0 : ℝ) 1, I₀ + a • (I - I₀) ∈ ball Ic R := by
  intro a ha
  rw [mem_ball_iff_norm]
  have e : I₀ + a • (I - I₀) - Ic = (I₀ - Ic) + a • (I - I₀) := by abel
  rw [e]
  refine lt_of_le_of_lt ((KAM.Stability.isActionNorm_euclid.norm_le _).trans
    (KAM.Stability.isActionNorm_euclid.add_le _ _)) ?_
  rw [KAM.Stability.isActionNorm_euclid.smul, abs_of_nonneg ha.1]
  have : a * euclid (I - I₀) ≤ ρ := by
    calc a * euclid (I - I₀) ≤ 1 * ρ :=
          mul_le_mul ha.2 hI (ef_euclid_nonneg _) zero_le_one
      _ = ρ := one_mul ρ
  linarith

/-- The frequency map is `M`-Lipschitz along segments in the convex ball. -/
private theorem ef_freq_lip {Ic : Fin n → ℝ} {R m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : RealFastConvex Ic R m M h) {I J : Fin n → ℝ}
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, J + a • (I - J) ∈ ball Ic R) :
    euclid (KAM.frequencyMap h I - KAM.frequencyMap h J) ≤ M * euclid (I - J) :=
  ef_hess_lipschitz isOpen_ball (ef_realPart_contDiffOn hh.hol) (hh.m_pos.le.trans hh.m_le)
    (fun I hI => ef_hess_abs_le (hh.hessian_real I (mem_ball_iff_norm.1 hI))) hseg

/-- Step `ef-en-energy`: `h + g + fs` is conserved along the orbit (at real points). -/
private theorem ef_energy (b : PartialBlock n k) {r s m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    {g fs : EC n k → ℂ} (hr : 0 < r) (hs : 0 < s) (hh : RealFastConvex b.Ic r m M h)
    (hg : ext_class b r s g) (hf : ext_class b r s fs) {J : Set ℝ} (hJ : J.OrdConnected)
    {y : ℝ → ER n k} (hy : ExtOrbit b r (liftFast h + g + fs) J y) {t u : ℝ} (ht : t ∈ J)
    (hu : u ∈ J) :
    realPart h (fastAction (y t)) + ((g (extCx (y t))).re + (fs (extCx (y t))).re) =
      realPart h (fastAction (y u)) + ((g (extCx (y u))).re + (fs (extCx (y u))).re) := by
  have hH := ext_class_add b (ext_class_add b (ext_class_liftFast b hh) hg) hf
  have := (real_system b hr hs hH).2.2.2.2.2 J hJ r hr le_rfl y hy t ht u hu
  have e : ∀ z : ER n k, fastAction (extCx z) = fun i => ((fastAction z i : ℝ) : ℂ) :=
    fun _ => rfl
  simp only [realHamiltonianExt, indicator_of_mem (hy t ht).1, indicator_of_mem (hy u hu).1,
    Pi.add_apply, Complex.add_re, liftFast, e] at this
  unfold realPart
  linarith

private theorem ef_re_abs_le (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ} (hs : 0 < s)
    (hu : InClass b.base R s u) (hb : WBound b.base R s u U) {z : ER n k}
    (hz : z ∈ b.realDom R) : |(u (extCx z)).re| ≤ U :=
  (Complex.abs_re_le_norm _).trans (real_system_bounds b hs hu hb z hz).1

/-- Step `ef-C`, angular derivative: `‖∂_θ fs‖₂ ≤ η/(e s)` at real points. -/
private theorem ef_theta_bound (b : PartialBlock n k) {r s η : ℝ} {fs : EC n k → ℂ}
    (hs : 0 < s) (hf : InClass b.base r s fs) (hfb : WBound b.base r s fs η) {z : ER n k}
    (hz : z ∈ b.realDom r) : euclid (fun i => (dtheta i fs (extCx z)).re) ≤ η / (Real.exp 1 * s) :=
  (ef_euclid_le_sum _).trans <|
    le_trans (Finset.sum_le_sum fun _ _ => Complex.abs_re_le_norm _)
      (real_system_bounds b hs hf hfb z hz).2

/-- Step `ef-C`, bracket: `|{fs, g}_c| ≤ 5 η ε/(r s)` on the half-radius real domain. -/
private theorem ef_bracket_bound (b : PartialBlock n k) {r s ε η : ℝ} {g fs : EC n k → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hg : InClass b.base r s g) (hf : InClass b.base r s fs)
    (hgb : WBound b.base r s g (5 * ε / 4)) (hfb : WBound b.base r s fs η) (hη : 0 ≤ η)
    (hε : 0 < ε) (hSL : 16 * k * b.c * s ≤ r) {z : ER n k} (hz : z ∈ b.realDom (r / 2)) :
    |(extBracket b.c fs g (extCx z)).re| ≤ 5 * η * ε / (r * s) := by
  have hc : 0 ≤ b.c := div_nonneg (by positivity) (sq_nonneg _)
  obtain ⟨hc1, hb1⟩ := bracket b (R0 := r) (s0 := s) (R := r) (s := s) (ρ := r / 2)
    (σ := s / 2) (U := η) (V := 5 * ε / 4) (by positivity) (by linarith) (by positivity)
    (by linarith) (by linarith) (by linarith) hf hg hη (by positivity) hfb hgb
  have hd := bracket_dominated (k := k) (c := b.c) (ρ := r / 2) (σ := s / 2) (R0 := r) (R := r)
    (s0 := s) (s := s) hc (by positivity) (by positivity) (by linarith) (by linarith)
    (by unfold slowLoss; linarith)
  have key : ((Real.exp 1)⁻¹ * (1 / ((r - r + r / 2) * (s / 2)) + 1 / ((s - s + s / 2) * (r / 2))) +
      2 * k * b.c / ((r - r + r / 2) * (r / 2))) * η * (5 * ε / 4) ≤ 5 * η * ε / (r * s) := by
    calc _ ≤ ((1 / 2) * (1 / ((r - r + r / 2) * (s / 2)) +
          1 / ((s - s + s / 2) * (r / 2)))) * η * (5 * ε / 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hη) (by positivity)
      _ = _ := by field_simp; ring
  have e1 : r - r / 2 = r / 2 := by ring
  have e2 : s - s / 2 = s / 2 := by ring
  rw [e1, e2] at hc1 hb1
  exact (ef_re_abs_le b (by positivity) hc1 (hb1.mono le_rfl le_rfl key) hz)

end KAM.Nekhoroshev

end
