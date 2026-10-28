/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Maximal
public import KAM.ODE.Continuation
public import KAM.ODE.Hamiltonian
public import KAM.Planetary.SecularBox.Field
public import KAM.Planetary.SecularBox.Numerics
public import KAM.Frozen.Planetary.Defs.SecularAMD

/-!
# The global slow flow on the secular box

Blueprint `bpP:p14:sb-slow` (steps `sb-sl-1`..`sb-sl-5`).

* `sb_slow`: at constant fast actions `Λ⁰`, the reduced secular flow with initial datum
  `(slow w₀.1, slow w₀.2)` exists for all time in the open slice of `S`, and conserves the AMD.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
open KAM.Kepler

namespace KAM.Planetary

private theorem sbSlow_mem_iff (saturn : ℝ) (w : Phase (2+2)) :
    w ∈ sb_sdef saturn ↔ (∀ i, 0 < fast w.2 i ∧
        50 * ((slow w.2 i ^ 2 + slow w.1 i ^ 2) / 2) < fast w.2 i) ∧
      51/10 < (fast w.2 0 / jupiterSaturnWeights saturn 0) ^ 2 ∧
      (fast w.2 0 / jupiterSaturnWeights saturn 0) ^ 2 < 53/10 ∧
      47/5 < (fast w.2 1 / jupiterSaturnWeights saturn 1) ^ 2 ∧
      (fast w.2 1 / jupiterSaturnWeights saturn 1) ^ 2 < 97/10 := by
  simp only [sb_sdef, mem_ofPred_eq, secularGamma, oscillatorAction, secularAxis]


/-- The affine slice embedding `y ↦ (0, ξ; Λ⁰, η)`. -/
private def sbSlowG (I : Fin 2 → ℝ) (y : Phase 2) : Phase (2+2) := assemble I 0 y.2 y.1

private theorem sbSlow_g_contDiff (I : Fin 2 → ℝ) : ContDiff ℝ ∞ (sbSlowG I) := by
  refine ContDiff.prodMk (contDiff_pi.2 fun k => ?_) (contDiff_pi.2 fun k => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
    simp only [Fin.append_left, Fin.append_right] <;> fun_prop

private theorem sbSlow_fast (I : Fin 2 → ℝ) (y : Phase 2) : fast (sbSlowG I y).2 = I := by
  funext i; simp [sbSlowG, assemble, fast]

private theorem sbSlow_slow_snd (I : Fin 2 → ℝ) (y : Phase 2) : slow (sbSlowG I y).2 = y.2 := by
  funext i; exact Fin.append_right _ _ i

private theorem sbSlow_slow_fst (I : Fin 2 → ℝ) (y : Phase 2) : slow (sbSlowG I y).1 = y.1 := by
  funext i; exact Fin.append_right _ _ i

private theorem sbSlow_mem_g (saturn : ℝ) (I : Fin 2 → ℝ) (y : Phase 2) :
    sbSlowG I y ∈ sb_sdef saturn ↔ (∀ i, 0 < I i ∧ 50 * ((y.2 i ^ 2 + y.1 i ^ 2) / 2) < I i) ∧
      51/10 < (I 0 / jupiterSaturnWeights saturn 0) ^ 2 ∧
      (I 0 / jupiterSaturnWeights saturn 0) ^ 2 < 53/10 ∧
      47/5 < (I 1 / jupiterSaturnWeights saturn 1) ^ 2 ∧
      (I 1 / jupiterSaturnWeights saturn 1) ^ 2 < 97/10 := by
  rw [sbSlow_mem_iff, sbSlow_fast, sbSlow_slow_snd, sbSlow_slow_fst]

/-- The AMD of the slice point. -/
private def sbSlowA (y : Phase 2) : ℝ := ∑ i, (y.2 i ^ 2 + y.1 i ^ 2) / 2

private theorem sbSlow_amd_g (I : Fin 2 → ℝ) (y : Phase 2) :
    secularAMD (sbSlowG I y) = sbSlowA y := by
  simp [secularAMD, secularGamma, oscillatorAction, sbSlow_slow_snd, sbSlow_slow_fst, sbSlowA]

private theorem sbSlow_continuous_A : Continuous sbSlowA := by
  unfold sbSlowA; fun_prop

/-- `sb-sl-3`: the AMD is conserved along a solution of the reduced flow. -/
private theorem sbSlow_conserved (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    (I : Fin 2 → ℝ) {J : Set ℝ} (hJo : IsOpen J) (hJc : J.OrdConnected) {z : ℝ → Phase 2}
    (hz : KAM.ODE.IsSolutionIn
      (KAM.hamiltonianVectorField (reducedSecularH (jupiterSaturnWeights saturn) mu I))
      {y | sbSlowG I y ∈ sb_sdef saturn} J z) {t₀ : ℝ} (h0 : t₀ ∈ J) :
    ∀ t ∈ J, sbSlowA (z t) = sbSlowA (z t₀) := by
  have hder : ∀ t ∈ J, HasDerivAt (fun t => sbSlowA (z t)) 0 t := by
    intro t ht
    obtain ⟨hmem, hd⟩ := hz t ht
    have hw : sbSlowG I (z t) ∈ sb_sdef saturn := hmem
    obtain ⟨-, hcons⟩ := sb_field saturn mu hs hw
    obtain ⟨-, hcomp⟩ := secular_field_components saturn mu hs hw
    simp only [sbSlow_fast, sbSlow_slow_fst, sbSlow_slow_snd] at hcomp
    have hX : KAM.hamiltonianVectorField (reducedSecularH (jupiterSaturnWeights saturn) mu I)
        (z t) = (slow (KAM.hamiltonianVectorField
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sbSlowG I (z t))).1,
          slow (KAM.hamiltonianVectorField
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sbSlowG I (z t))).2) := by
      rw [hcomp]
    rw [hX] at hd
    simp only [sbSlow_slow_fst, sbSlow_slow_snd] at hcons
    have h1 : ∀ i, HasDerivAt (fun t => (z t).1 i) ((slow (KAM.hamiltonianVectorField
        (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sbSlowG I (z t))).1) i) t :=
      fun i => hasDerivAt_pi.1 hd.fst i
    have h2 : ∀ i, HasDerivAt (fun t => (z t).2 i) ((slow (KAM.hamiltonianVectorField
        (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sbSlowG I (z t))).2) i) t :=
      fun i => hasDerivAt_pi.1 hd.snd i
    have hs' := (((h2 0).pow 2).add ((h1 0).pow 2)).div_const 2 |>.add
      ((((h2 1).pow 2).add ((h1 1).pow 2)).div_const 2)
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib] at hcons
    convert hs' using 1
    · funext t; simp [sbSlowA, Fin.sum_univ_two]
    · simp only [Nat.cast_ofNat] at *
      linarith
  exact fun t ht => (hJo.is_const_of_deriv_eq_zero hJc.isPreconnected
    (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hder t ht).deriv) ht h0)

theorem sb_slow (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (hw : w0 ∈ sb_sdef saturn)
    (hA : secularAMD w0 < (16373/2500000 : ℝ)) (hI : ∀ i, (87/100 : ℝ) < fast w0.2 i) :
    ∃ y : ℝ → Phase 2, y 0 = (slow w0.1, slow w0.2) ∧
      KAM.ODE.IsSolutionIn
        (KAM.hamiltonianVectorField (reducedSecularH (jupiterSaturnWeights saturn) mu (fast w0.2)))
        {y | assemble (fast w0.2) 0 y.2 y.1 ∈ sb_sdef saturn} univ y ∧
      ∀ t, secularAMD (assemble (fast w0.2) 0 (y t).2 (y t).1) = secularAMD w0 := by
  set I := fast w0.2 with hIdef
  set h := reducedSecularH (jupiterSaturnWeights saturn) mu I with hh
  set W : Set (Phase 2) := {y | sbSlowG I y ∈ sb_sdef saturn} with hW
  set y0 : Phase 2 := (slow w0.1, slow w0.2) with hy0
  have hgc : Continuous (sbSlowG I) := (sbSlow_g_contDiff I).continuous
  have hWo : IsOpen W := (sb_s saturn hs).1.preimage hgc
  have hy0W : y0 ∈ W := by
    show sbSlowG I y0 ∈ sb_sdef saturn
    rw [sbSlow_mem_g]
    have := (sbSlow_mem_iff saturn w0).1 hw
    simpa [hy0, hIdef] using this
  -- `sb-sl-1`
  have hhc : ContDiffOn ℝ 2 h W := by
    have := (sb_smooth_prop saturn mu hs).1.comp (t := sb_sdef saturn) (s := W)
      (sbSlow_g_contDiff I).contDiffOn (fun y hy => hy)
    exact (this.of_le (by norm_cast)).congr fun y _ => rfl
  have hF : ContDiffOn ℝ 1 (KAM.hamiltonianVectorField h) W := KAM.ODE.ham_smooth_c1 hWo hhc
  -- `sb-sl-2`
  obtain ⟨⟨Tm, Tp, z, hz⟩, -⟩ := KAM.ODE.gen_maximal hWo hF hy0W
  -- `sb-sl-3`
  have hA0 : sbSlowA y0 = secularAMD w0 := by
    rw [← sbSlow_amd_g I y0]
    simp only [secularAMD, secularGamma, sbSlow_slow_snd, sbSlow_slow_fst]
    rfl
  have hcons := sbSlow_conserved saturn mu hs I (KAM.ODE.isOpen_eIoo Tm Tp)
    (KAM.ODE.ordConnected_eIoo Tm Tp) hz.isSolution (KAM.ODE.zero_mem_eIoo hz)
  have hzA : ∀ t ∈ KAM.ODE.eIoo Tm Tp, sbSlowA (z t) = secularAMD w0 := fun t ht => by
    rw [hcons t ht, hz.init, hA0]
  -- `sb-sl-4`
  set K : Set (Phase 2) := {y | sbSlowA y = secularAMD w0} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq sbSlow_continuous_A continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Phase 2)) (r := 1 + 2 * secularAMD w0)).subset
      fun y hy => ?_
    have hy' : sbSlowA y = secularAMD w0 := hy
    have hnn : ∀ i, 0 ≤ y.2 i ^ 2 + y.1 i ^ 2 := fun i => by positivity
    have hsum : sbSlowA y = (y.2 0 ^ 2 + y.1 0 ^ 2) / 2 + (y.2 1 ^ 2 + y.1 1 ^ 2) / 2 := by
      simp [sbSlowA, Fin.sum_univ_two]
    have hR : 0 ≤ 1 + 2 * secularAMD w0 := by
      rw [← hy', hsum]; linarith [hnn 0, hnn 1]
    have habs : ∀ x : ℝ, x ^ 2 ≤ 2 * secularAMD w0 → ‖x‖ ≤ 1 + 2 * secularAMD w0 := by
      intro x hx
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs x, abs_nonneg x]
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ((pi_norm_le_iff_of_nonneg hR).2 fun i => habs _ ?_)
      ((pi_norm_le_iff_of_nonneg hR).2 fun i => habs _ ?_)
    · fin_cases i <;> simp <;> nlinarith [hnn 0, hnn 1, sq_nonneg (y.2 0), sq_nonneg (y.2 1)]
    · fin_cases i <;> simp <;> nlinarith [hnn 0, hnn 1, sq_nonneg (y.1 0), sq_nonneg (y.1 1)]
  have hKW : K ⊆ W := by
    intro y hy
    have hy' : sbSlowA y = secularAMD w0 := hy
    have hsum : sbSlowA y = (y.2 0 ^ 2 + y.1 0 ^ 2) / 2 + (y.2 1 ^ 2 + y.1 1 ^ 2) / 2 := by
      simp [sbSlowA, Fin.sum_univ_two]
    have hnn : ∀ i, 0 ≤ y.2 i ^ 2 + y.1 i ^ 2 := fun i => by positivity
    obtain ⟨-, hax⟩ := (sbSlow_mem_iff saturn w0).1 hw
    show sbSlowG I y ∈ sb_sdef saturn
    rw [sbSlow_mem_g]
    refine ⟨fun i => ⟨by linarith [hI i], ?_⟩, hax⟩
    have : (y.2 i ^ 2 + y.1 i ^ 2) / 2 ≤ secularAMD w0 := by
      rw [← hy', hsum]; fin_cases i <;> simp <;> linarith [hnn 0, hnn 1]
    linarith [hI i]
  -- `sb-sl-5`
  have hzK : ∀ t ∈ KAM.ODE.eIoo Tm Tp, z t ∈ K := fun t ht => hzA t ht
  obtain ⟨hR, hL⟩ := KAM.ODE.gen_continuation_compact hWo hF hz hKc hKW
  have hTp : Tp = ⊤ := hR ⟨0, le_rfl, hz.pos_lt, fun t ht htT => hzK t
    ⟨lt_of_lt_of_le hz.neg_lt (by exact_mod_cast ht), htT⟩⟩
  have hTm : Tm = ⊥ := hL ⟨0, le_rfl, hz.neg_lt, fun t htT ht => hzK t
    ⟨htT, lt_of_le_of_lt (by exact_mod_cast ht) hz.pos_lt⟩⟩
  have hsol := hz.isSolution
  rw [hTp, hTm, KAM.ODE.eIoo_bot_top] at hsol
  refine ⟨z, hz.init, hsol, fun t => ?_⟩
  have := hzA t (by rw [hTp, hTm, KAM.ODE.eIoo_bot_top]; exact mem_univ t)
  rw [← this, ← sbSlow_amd_g I (z t)]
  rfl

end KAM.Planetary

end
