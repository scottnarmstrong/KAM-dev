/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.RealSystem
public import KAM.Head.Frequency

/-!
# The frequency-free energy identity (Part 11, package N11-L1)

Along an orbit `y` of `liftFast h + g + fs` in the extended phase space, `fs ∘ y` has
derivative `∂_θ fs · ω(I) + {fs, g}_c` (`bpN:p11:eq:lie`, step `ef-id`): the Poisson bracket of
`fs` with `fs` vanishes and `h` depends on the fast action only.  Consequently (step `ef-C`) the
pairing of `ω(I(0))` with the transverse part `ΔI - P ΔI` of the fast displacement is controlled
by the oscillation of `fs`, with no bound on `ω`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-! ### Reality and the class of the total Hamiltonian -/

private theorem fastAction_extCx (z : ER n k) :
    fastAction (extCx z) = KAM.realInclusion n (fastAction z) := by
  ext i; simp [fastAction, extCx]

private theorem fast_mem_polyNbhd (b : PartialBlock n k) {R : ℝ} {z : EC n k}
    (hz : z.2 ∈ polyNbhd b.base R) :
    fastAction z ∈ polyNbhd {KAM.realInclusion n b.Ic} R := by
  obtain ⟨J, ⟨x, -, rfl⟩, hlt⟩ := hz
  refine ⟨KAM.realInclusion n b.Ic, rfl, lt_of_le_of_lt ?_ hlt⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (z.2 - Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i / b.lam : ℝ) : ℂ)) (fun i => ((x.2 i / b.lam : ℝ) : ℂ))))
    (Fin.castAdd (k + k) i)
  simpa [fastAction] using this

private theorem differentiableAt_fastAction (z : EC n k) :
    DifferentiableAt ℂ (fun z : EC n k => fastAction z) z :=
  differentiableAt_pi.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + (k + k)) => ℂ)
      (Fin.castAdd (k + k) i)).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ)
        (Fin (n + (k + k)) → ℂ))).differentiableAt

private theorem differentiableOn_liftFast (b : PartialBlock n k) {R s : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R)) :
    DifferentiableOn ℂ (liftFast h : EC n k → ℂ) (Dom n b.base R s) := fun z hz =>
  ((hh _ (fast_mem_polyNbhd b hz.2)).differentiableAt
    ((isOpen_polyNbhd _ R).mem_nhds (fast_mem_polyNbhd b hz.2))).comp_differentiableWithinAt z
    (differentiableAt_fastAction z).differentiableWithinAt

/-- The fast part of the Hamiltonian is an extended-class function. -/
theorem ext_class_liftFast (b : PartialBlock n k) {R s m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : RealFastConvex b.Ic R m M h) : ext_class b R s (liftFast h) :=
  ⟨⟨differentiableOn_liftFast b hh.hol, fun _ _ _ => rfl⟩, fun (x : ER n k) hx => by
    have h0 := fast_mem_polyNbhd b (z := extCx x) hx.2
    rw [fastAction_extCx] at h0
    have h1 := hh.real _ h0
    rw [← fastAction_extCx] at h1
    exact h1⟩

theorem ext_class_add (b : PartialBlock n k) {R s : ℝ} {u v : EC n k → ℂ}
    (hu : ext_class b R s u) (hv : ext_class b R s v) : ext_class b R s (u + v) :=
  ⟨⟨hu.1.differentiableOn.add hv.1.differentiableOn, fun j z hz => by
    simp only [Pi.add_apply, hu.1.periodic j z hz, hv.1.periodic j z hz]⟩, fun x hx => by
    simp [Pi.add_apply, hu.2 x hx, hv.2 x hx]⟩

/-! ### The weighted field as a function of the differential -/

/-- The body of `wfield` with `fderiv ℂ H z` replaced by an arbitrary functional. -/
private def wvec (c : ℝ) (L : EC n k →L[ℂ] ℂ) : EC n k :=
  (fun i => L (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -L (Pi.single i 1, 0))
    (Fin.append
      (fun i => (c : ℂ) * L (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -(c : ℂ) * L (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))

private theorem wfield_eq_wvec (c : ℝ) (H : EC n k → ℂ) (z : EC n k) :
    wfield c H z = wvec c (fderiv ℂ H z) := rfl

private theorem wvec_add (c : ℝ) (L L' : EC n k →L[ℂ] ℂ) :
    wvec c (L + L') = wvec c L + wvec c L' := by
  refine Prod.ext (funext fun i => by simp [wvec]) (funext fun j => ?_)
  refine ext_cases (P := fun j => (wvec c (L + L')).2 j = (wvec c L + wvec c L').2 j)
    (fun i => ?_) (fun i => ?_) (fun i => ?_) j <;>
    simp only [wvec, Prod.snd_add, Pi.add_apply, add_apply,
      Fin.append_left, Fin.append_right] <;> ring

/-- A continuous linear functional is the sum of its values on the coordinate directions. -/
private theorem clm_apply_split (L : EC n k →L[ℂ] ℂ) (x : EC n k) :
    L x = ∑ i, x.1 i * L (Pi.single i 1, 0) + ∑ j, x.2 j * L (0, Pi.single j 1) := by
  have h1 : ((x.1, 0) : EC n k) = ∑ i, x.1 i • ((Pi.single i 1, 0) : EC n k) := by
    ext a
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have h2 : ((0, x.2) : EC n k) = ∑ j, x.2 j • ((0, Pi.single j 1) : EC n k) := by
    ext a
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx, map_add, h1, h2, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The bracket of a function with itself vanishes: `L (wvec L) = 0`. -/
private theorem apply_wvec_self (c : ℝ) (L : EC n k →L[ℂ] ℂ) : L (wvec c L) = 0 := by
  rw [clm_apply_split]
  simp only [wvec, Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_mul,
    Finset.sum_neg_distrib]
  have e1 : ∑ i : Fin n, L (0, Pi.single (Fin.castAdd (k+k) i) 1) * L (Pi.single i 1, 0) =
      ∑ i : Fin n, L (Pi.single i 1, 0) * L (0, Pi.single (Fin.castAdd (k+k) i) 1) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∑ i : Fin k, (c : ℂ) * L (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) *
      L (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) =
      ∑ i : Fin k, (c : ℂ) * L (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) *
        L (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

/-! ### The fast part -/

/-- The fast action as a continuous linear map. -/
private def fastCLM (n k : ℕ) : EC n k →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + (k + k)) => ℂ)
      (Fin.castAdd (k + k) i)).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin (n + (k + k)) → ℂ))

private theorem fastCLM_apply (z : EC n k) : fastCLM n k z = fastAction z := rfl

private theorem fastCLM_fast (i : Fin n) :
    fastCLM n k (0, Pi.single (Fin.castAdd (k + k) i) 1) = Pi.single i 1 := by
  funext j
  simp [fastCLM, Pi.single_apply, Fin.castAdd_inj]

private theorem fastCLM_slow (i : Fin k) :
    fastCLM n k (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) = 0 ∧
    fastCLM n k (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) = 0 := by
  constructor <;> (funext j; simp [fastCLM, Pi.single_apply, Fin.ext_iff]; have := j.isLt; omega)

private theorem fastCLM_theta (i : Fin n) : fastCLM n k (Pi.single i 1, 0) = 0 := by
  funext j; simp [fastCLM]

/-- The weighted field of a function of the fast action alone is `(∇h, 0)`. -/
private theorem wvec_comp_fast (c : ℝ) (D : (Fin n → ℂ) →L[ℂ] ℂ) :
    wvec c (D.comp (fastCLM n k)) = ((fun i => D (Pi.single i 1)), 0) := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp [wvec, fastCLM_fast]
  · refine ext_cases (P := fun j => (wvec c (D.comp (fastCLM n k))).2 j = 0)
      (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · simp [wvec, fastCLM_theta]
    · simp only [wvec, Fin.append_right, Fin.append_left, ContinuousLinearMap.comp_apply,
        (fastCLM_slow i).2, map_zero, mul_zero]
    · simp only [wvec, Fin.append_right, ContinuousLinearMap.comp_apply,
        (fastCLM_slow i).1, map_zero, mul_zero]

/-- `L (v, 0) = ∑ vᵢ L(eᵢ, 0)`. -/
private theorem clm_apply_theta (L : EC n k →L[ℂ] ℂ) (v : Fin n → ℂ) :
    L (v, 0) = ∑ i, v i * L (Pi.single i 1, 0) := by
  rw [clm_apply_split]
  simp

/-! ### Derivatives along an orbit -/

private theorem mem_Dom_of_realDom (b : PartialBlock n k) {R s : ℝ} (hs : 0 < s) {z : ER n k}
    (hz : z ∈ b.realDom R) : extCx z ∈ Dom n b.base R s :=
  ⟨KAM.ofReal_mem_complexStrip hs z.1, hz.2⟩

/-- `ER n k → EC n k` as a continuous `ℝ`-linear map. -/
private def cxCLM (n k : ℕ) : ER n k →L[ℝ] EC n k :=
  (KAM.realInclusion n).prodMap (KAM.realInclusion (n + (k + k)))

private theorem cxCLM_apply (z : ER n k) : cxCLM n k z = extCx z := by
  ext i <;> simp [cxCLM, extCx]

/-- Chain rule along an orbit: the derivative of `u ∘ extCx ∘ y` is `Du (wfield H)`. -/
private theorem hasDerivAt_orbit (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hH : ext_class b R s H) {J : Set ℝ} {y : ℝ → ER n k}
    (hy : ExtOrbit b R H J y) {τ : ℝ} (hτ : τ ∈ J) {u : EC n k → ℂ}
    (hu : DifferentiableAt ℂ u (extCx (y τ))) :
    HasDerivAt (fun t => u (extCx (y t)))
      (fderiv ℂ u (extCx (y τ)) (wfield b.c H (extCx (y τ)))) τ := by
  obtain ⟨hmem, hd⟩ := hy τ hτ
  have h1 : HasDerivAt (fun t => extCx (y t)) (extCx (realWfield b.c
      (realHamiltonianExt b R H) (y τ))) τ := by
    have := (cxCLM n k).hasFDerivAt.comp_hasDerivAt τ hd
    rw [cxCLM_apply] at this
    have hfun : (fun t => extCx (y t)) = cxCLM n k ∘ y := funext fun t => (cxCLM_apply _).symm
    rw [hfun]
    exact this
  have h2 := (hu.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ h1
  rw [(real_system b hR hs hH).2.2.1 _ hmem] at h2
  exact h2

/-! ### The identity -/

/-- `bpN:p11:eq:lie` (step `ef-id`): along an orbit of `h + g + fs`, `fs ∘ y` has derivative
`∂_θ fs · ω(I) + {fs, g}_c`; equivalently `∂_θ fs · ω = (fs ∘ y)' - {fs, g}_c`.  No bound on the
frequency `ω` enters. -/
theorem energy_identity (b : PartialBlock n k) {r s m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    {g fs : EC n k → ℂ} (hr : 0 < r) (hs : 0 < s) (hh : RealFastConvex b.Ic r m M h)
    (hg : ext_class b r s g) (hf : ext_class b r s fs) {J : Set ℝ} {y : ℝ → ER n k}
    (hy : ExtOrbit b r (liftFast h + g + fs) J y) {τ : ℝ} (hτ : τ ∈ J) :
    HasDerivAt (fun t => fs (extCx (y t)))
      (∑ i, dtheta i fs (extCx (y τ)) * freq h (fastAction (extCx (y τ))) i +
        extBracket b.c fs g (extCx (y τ))) τ := by
  have hz : extCx (y τ) ∈ Dom n b.base r s := mem_Dom_of_realDom b hs (hy τ hτ).1
  have hnh : ∀ {u : EC n k → ℂ}, ext_class b r s u → DifferentiableAt ℂ u (extCx (y τ)) :=
    fun hu => hu.1.differentiableOn.differentiableAt ((isOpen_Dom _ r s).mem_nhds hz)
  have hlh : DifferentiableAt ℂ (liftFast h : EC n k → ℂ) (extCx (y τ)) :=
    (differentiableOn_liftFast b hh.hol).differentiableAt ((isOpen_Dom _ r s).mem_nhds hz)
  have hHd := hasDerivAt_orbit b hr hs
    (ext_class_add b (ext_class_add b (ext_class_liftFast b hh) hg) hf) hy hτ (hnh hf)
  refine hHd.congr_deriv ?_
  have hderiv : fderiv ℂ (liftFast h + g + fs) (extCx (y τ)) =
      fderiv ℂ (liftFast h) (extCx (y τ)) + fderiv ℂ g (extCx (y τ)) +
        fderiv ℂ fs (extCx (y τ)) := by
    have := fderiv_add (hlh.add (hnh hg)) (hnh hf)
    rw [fderiv_add hlh (hnh hg)] at this
    exact this
  have hfast : fderiv ℂ (liftFast h : EC n k → ℂ) (extCx (y τ)) =
      (fderiv ℂ h (fastAction (extCx (y τ)))).comp (fastCLM n k) := by
    have hhd : DifferentiableAt ℂ h (fastCLM n k (extCx (y τ))) :=
      (hh.hol _ (fast_mem_polyNbhd b hz.2)).differentiableAt
        ((isOpen_polyNbhd _ r).mem_nhds (fast_mem_polyNbhd b hz.2))
    have := fderiv_comp (extCx (y τ)) hhd (fastCLM n k).differentiableAt
    rw [(fastCLM n k).fderiv] at this
    exact this
  rw [wfield_eq_wvec, hderiv, wvec_add, wvec_add, hfast, wvec_comp_fast, map_add, map_add,
    apply_wvec_self, clm_apply_theta]
  simp only [extBracket, wfield_eq_wvec, add_zero, dtheta, freq]
  simp only [mul_comm]

end KAM.Nekhoroshev

end
