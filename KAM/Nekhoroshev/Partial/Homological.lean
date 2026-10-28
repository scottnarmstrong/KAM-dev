/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.NormalForm.Homological

/-!
# Homological equation on the extended space (`bpN:p11:hom`, Part 11, package N11-F3)

`homGenerator` is the Part 6 parametrized generator `homGenParam` for the frequency
`J ↦ freq h (fast projection J)`, and `hom` is `homological_param` instantiated at
`m = n + (k + k)`, base `b.base`, with the directional equation identified with `extBracket`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

def homGenerator (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) : EC n k → ℂ :=
  KAM.NormalForm.homGenParam K Λ (fun J => freq h (fun i => J (Fin.castAdd (k+k) i))) f

private theorem fastAction_mem_polyNbhd
    {b : PartialBlock n k} {R : ℝ} {J : Fin (n + (k + k)) → ℂ}
    (hJ : J ∈ polyNbhd b.base R) :
    (fun i => J (Fin.castAdd (k+k) i)) ∈ polyNbhd {KAM.realInclusion n b.Ic} R := by
  obtain ⟨J', ⟨x, -, rfl⟩, hlt⟩ := hJ
  refine ⟨KAM.realInclusion n b.Ic, rfl, lt_of_le_of_lt ?_ hlt⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (J - Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i / b.lam : ℝ) : ℂ)) (fun i => ((x.2 i / b.lam : ℝ) : ℂ))))
    (Fin.castAdd (k+k) i)
  simpa [Fin.append_left] using this

private theorem fderiv_liftFast {h : (Fin n → ℂ) → ℂ} {z : EC n k}
    (hh : DifferentiableAt ℂ h (fastAction z)) (v : EC n k) :
    fderiv ℂ (liftFast (k := k) h) z v = fderiv ℂ h (fastAction z) (fastAction v) := by
  let L : EC n k →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + (k + k)) => ℂ)
        (Fin.castAdd (k+k) i)).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) _)
  have hL : ∀ w, L w = fastAction w := fun w => rfl
  have hd : HasFDerivAt (fun w => h (L w)) ((fderiv ℂ h (L z)).comp L) z :=
    (show HasFDerivAt h (fderiv ℂ h (L z)) (L z) from hh.hasFDerivAt).comp z L.hasFDerivAt
  have e : liftFast (k := k) h = fun w => h (L w) := rfl
  rw [e, hd.fderiv]
  rfl

private theorem fastAction_single_slow (a : Fin (k + k)) :
    fastAction (n := n) (k := k)
      ((0 : Fin n → ℂ), (Pi.single (Fin.natAdd n a) 1 : Fin (n + (k + k)) → ℂ)) = 0 := by
  funext i
  have h : Fin.castAdd (k+k) i ≠ Fin.natAdd n a := fun e => by
    have := congrArg Fin.val e
    simp at this
    omega
  simp [fastAction, h]

private theorem fastAction_single_fast (i : Fin n) :
    fastAction (n := n) (k := k)
      ((0 : Fin n → ℂ), (Pi.single (Fin.castAdd (k+k) i) 1 : Fin (n + (k + k)) → ℂ)) =
      Pi.single i 1 := by
  funext j
  simp [fastAction, Pi.single_apply, (Fin.castAdd_injective n (k+k)).eq_iff]

private theorem wfield_liftFast (c : ℝ) {h : (Fin n → ℂ) → ℂ} {z : EC n k}
    (hh : DifferentiableAt ℂ h (fastAction z)) :
    wfield c (liftFast (k := k) h) z = (freq h (fastAction z), 0) := by
  refine Prod.ext ?_ ?_
  · funext i
    show fderiv ℂ (liftFast (k := k) h) z _ = _
    rw [fderiv_liftFast hh, fastAction_single_fast]
    rfl
  · funext j
    refine Fin.addCases (fun i => ?_) (fun a => ?_) j
    · simp only [wfield, Fin.append_left, Pi.zero_apply]
      rw [fderiv_liftFast hh]
      have e : fastAction (n := n) (k := k)
          ((Pi.single i 1 : Fin n → ℂ), (0 : Fin (n + (k + k)) → ℂ)) = 0 := rfl
      simp [e]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · simp only [wfield, Fin.append_right, Fin.append_left, Pi.zero_apply]
        rw [fderiv_liftFast hh, fastAction_single_slow]
        simp
      · simp only [wfield, Fin.append_right, Pi.zero_apply]
        rw [fderiv_liftFast hh, fastAction_single_slow]
        simp

private theorem fderiv_eq_sum (u : EC n k → ℂ) (z : EC n k) (v : Fin n → ℂ) :
    fderiv ℂ u z (v, 0) = ∑ i, fderiv ℂ u z (Pi.single i 1, 0) * v i := by
  have e : ((v, 0) : EC n k) =
      ∑ i, v i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin (n+(k+k)) → ℂ)) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem hom (b : PartialBlock n k) {R s K α q U : ℝ} (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (hR : 0 < R) (hs : 0 < s) (hK : 0 ≤ K) (hα : 0 < α) (hq : 1 ≤ q)
    (Λ : Set (Fin n → ℤ)) (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/q))
    (hU : 0 ≤ U) (hf : InClass b.base R s f) (hb : WBound b.base R s f U) :
    let ξ := projMode Λ (truncate K f)
    let φ := homGenerator K Λ h f
    InClass b.base R s ξ ∧ InClass b.base R s φ ∧
    WBound b.base R s ξ U ∧ WBound b.base R s (truncate K f) U ∧
    WBound b.base R s φ (q*U/(2*Real.pi*α)) ∧
    (∀ z ∈ Dom n b.base R s, extBracket b.c φ (liftFast h) z+ξ z = truncate K f z) ∧
    (∀ z ∈ Dom n b.base R s, projMode Λ φ z = 0) ∧
    ((∀ j, j ∈ Λ ↔ -j ∈ Λ) → extReal (Dom n b.base R s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      extReal (Dom n b.base R s) ξ ∧ extReal (Dom n b.base R s) φ) := by
  intro ξ φ
  have _ := hR
  have _ := hU
  have hfreq : DifferentiableOn ℂ (freq h) (polyNbhd {KAM.realInclusion n b.Ic} R) :=
    fun I hI => (differentiableAt_freq (isOpen_polyNbhd _ _) hh hI).differentiableWithinAt
  have hfast : Differentiable ℂ
      (fun J : Fin (n + (k + k)) → ℂ => fun i => J (Fin.castAdd (k+k) i)) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hω : DifferentiableOn ℂ
      (fun J : Fin (n + (k + k)) → ℂ => freq h (fun i => J (Fin.castAdd (k+k) i)))
      (polyNbhd b.base R) :=
    hfreq.comp hfast.differentiableOn fun J hJ => fastAction_mem_polyNbhd hJ
  have hdir : ∀ J ∈ polyNbhd b.base R, ∀ j ∈ zBall n K \ Λ,
      α / q ≤ ‖dotC j (freq h (fun i => J (Fin.castAdd (k+k) i)))‖ :=
    fun J hJ j hj => hdiv _ (fastAction_mem_polyNbhd hJ) j hj
  obtain ⟨c1, c2, -, c4, c5, -, c7, c8, c9, c10⟩ :=
    homological_param (D := b.base) (r := R) (s := s) (K := K) (α := α) (q := q) (δ := U)
      (Λ := Λ) (f := f)
      (ω := fun J : Fin (n + (k + k)) → ℂ => freq h (fun i => J (Fin.castAdd (k+k) i)))
      hq hα hs hK hω hdir hf hb
  have hreal : (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      ∀ I : Fin (n + (k + k)) → ℝ, KAM.realInclusion (n + (k + k)) I ∈ polyNbhd b.base R →
        ∀ i, (freq h (fun i => KAM.realInclusion (n + (k + k)) I (Fin.castAdd (k+k) i)) i).im = 0 :=
    fun hfr I hI i =>
      hfr (fun i => I (Fin.castAdd (k+k) i)) (fastAction_mem_polyNbhd hI) i
  refine ⟨c2, c1, c7, c8, c9, ?_, ?_, fun hsym hre hfr =>
    (c10 (fun j hj => (hsym j).1 hj) hre (hreal hfr)).symm⟩
  · intro z hz
    have hda : DifferentiableAt ℂ h (fastAction z) :=
      hh.differentiableAt ((isOpen_polyNbhd _ _).mem_nhds (fastAction_mem_polyNbhd hz.2))
    have := c4 z hz
    unfold extBracket
    rw [wfield_liftFast b.c hda, fderiv_eq_sum]
    exact this
  · intro z hz
    unfold projMode
    refine (tsum_congr fun j => ?_).trans tsum_zero
    by_cases hj : j ∈ Λ
    · simp only [Set.indicator_of_mem hj]
      rw [show coeff φ z.2 j = 0 from c5 z.2 hz.2 j hj, zero_mul]
    · simp [hj]

end KAM.Nekhoroshev

end
