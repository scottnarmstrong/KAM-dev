/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness
public import KAM.Planetary.Spatial.ChartLift.Setting
public import KAM.Planetary.Spatial.Geometry

/-!
# The spatial chart lift on the stopped interval

Package LP-SP-LIFT, MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, the chart part) for `d = 3` with the
Lemma 18 alignment (`LP:MAIN L18 (595–597)`), amendments N2, N6; track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`spatialChartLift_of_stopped` mirrors the planar `lpChartLift_of_stopped`: the maximal solution
`y` of the pulled-back chart field through a chart preimage of `z 0` projects to the physical
solution, equals `z` by uniqueness, and stays over the compact zero-angle set `spatialLiftQ` of
the box `[I⁰ - r, I⁰ + r]` with `Σ(Γ + Z) ≤ B(I⁰) - δ/4` (alignment makes the chart deficit the
strong AMD), so the retyped uniform data and `gen_continuation` put the stopped interval inside
its maximal interval.  Only the strict stopped conditions and the alignment of `L(z₀)` with `e₃`
are used (no drift or confinement conclusion).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.ODE Set

variable {n : ℕ}

/-- The chart action of a point of the product domain is the Kepler action vector of its image. -/
theorem spatialActionVector_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialActionVector ν (spatialPoincareProd ν w) = fast w.2 := by
  funext i
  exact spatialKeplerAction_spatialPoincareProd hν hw i

/-- With the alignment `L = |L| e₃` the chart deficit is the strong AMD (MAIN (47), L18 line 595). -/
theorem spatialChartAMD_eq_of_aligned {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n)
    (hL : angularMomentum3 (spatialPoincareProd ν w) =
      spaceLength (angularMomentum3 (spatialPoincareProd ν w)) • e₃) :
    spatialChartAMD w = spatialStrongAMD ν (spatialPoincareProd ν w) := by
  rw [spatialChartAMD_eq_sum_body,
    spatialStrongAMD_spatialPoincareProd_of_aligned hν hw hL]

namespace SpatialLiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 3)} {δ r : ℝ}

private theorem lower_upper_of_norm' {I0 I : Fin n → ℝ} (h : ‖I - I0‖ ≤ r) (i : Fin n) :
    I0 i - r ≤ I i ∧ I i ≤ I0 i + r := by
  have := norm_le_pi_norm (I - I0) i
  rw [Real.norm_eq_abs] at this
  have := abs_le.1 (this.trans h)
  simp only [Pi.sub_apply] at this
  constructor <;> linarith [this.1, this.2]

private theorem norm_of_lower_upper' {I0 I : Fin n → ℝ} (hr : 0 ≤ r)
    (h : ∀ i, I0 i - r ≤ I i ∧ I i ≤ I0 i + r) : ‖I - I0‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have := h i
  simp only [Pi.sub_apply]
  constructor <;> linarith [this.1, this.2]

/-- Membership of the zero-angle point in the compact set `spatialLiftQ`. -/
theorem zeroAngle_mem_spatialLiftQ {w : Phase (n + (n + n))}
    (hact : ‖fast w.2 - spatialActionVector ν z₀‖ ≤ r)
    (hamd : spatialChartAMD w ≤ strongThreshold ν (spatialActionVector ν z₀) - δ / 4) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + (n + n))) ∈
      spatialLiftQ (spatialActionVector ν z₀) r
        (strongThreshold ν (spatialActionVector ν z₀) - δ / 4) := by
  refine ⟨funext fun i => udZeroFstCastAdd w i, fun i => ?_, ?_⟩
  · have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) :
        Phase (n + (n + n))).2 = fast w.2 := by
      rw [udZeroSnd]
    rw [h2]
    exact lower_upper_of_norm' hact i
  · rw [spatialChartAMD_zeroAngle]; exact hamd

/-- `hQW` of `uniformDataNM`: a point whose zero-angle point is in `spatialLiftQ` is in
`spatialChartSafe`.  The action is in the `r`-ball (so in `U ⊆ 𝒬`), `Γ_i + Z_i ≤ Σ(Γ + Z) ≤
B(Λ) - n r < Λ_i` puts it in the chart domain, and `Ψ w` is a barrier state with margin `n r`
(its strong AMD is at most the fixed-plane deficit), hence collision-free. -/
theorem mem_spatialChartSafe_of_liftQ (hd : SpatialLiftData ν U z₀ δ r) {w : Phase (n + (n + n))}
    (hw : (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + (n + n))) ∈
      spatialLiftQ (spatialActionVector ν z₀) r
        (strongThreshold ν (spatialActionVector ν z₀) - δ / 4)) :
    w ∈ spatialChartSafe ν := by
  have hν := hd.pos_mass
  obtain ⟨-, hb, hA⟩ := hw
  have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) :
      Phase (n + (n + n))).2 = fast w.2 := by
    rw [udZeroSnd]
  rw [h2] at hb
  rw [spatialChartAMD_zeroAngle] at hA
  have hact : ‖fast w.2 - spatialActionVector ν z₀‖ ≤ r := norm_of_lower_upper' hd.r_pos.le hb
  have hU : fast w.2 ∈ U := hd.ball _ hact
  have hamd : spatialChartAMD w ≤ strongThreshold ν (fast w.2) - n * r := by
    have := hd.threshold_ball_le hact
    linarith
  have hdom : w ∈ spatialPoincareProdDom n := by
    intro i
    have hIpos : 0 < fast w.2 i := (hd.subset_chamber hU).1 i
    have h0 : (spatialBlock w i).2 0 = fast w.2 i := spatialBlock_snd_zero w i
    have hle : spatialGammaBody w i + spatialZBody w i ≤ spatialChartAMD w := by
      rw [spatialChartAMD_eq_sum_body]
      exact Finset.single_le_sum (f := fun j => spatialGammaBody w j + spatialZBody w j)
        (fun j _ => add_nonneg (spatialGamma_nonneg _) (spatialZ_nonneg _)) (Finset.mem_univ i)
    have hB := strongThreshold_le_action ν (fast w.2) i
    refine ⟨by rw [h0]; exact hIpos, ?_⟩
    show spatialGammaBody w i + spatialZBody w i < (spatialBlock w i).2 0
    rw [h0]
    linarith [hd.n_mul_r_pos]
  obtain ⟨K, -, hKsub, hbar⟩ := exists_spatialBarrierCompact hν hd.two_le hd.compact
    hd.subset_chamber (m := n * r) hd.n_mul_r_pos
  have hact' : spatialActionVector ν (spatialPoincareProd ν w) = fast w.2 :=
    spatialActionVector_spatialPoincareProd hν hdom
  have hneg : SpatialNegativeEnergy ν (spatialPoincareProd ν w) := by
    intro i
    have hIpos : 0 < (spatialBlock w i).2 0 := (hdom i).1
    have hE : spatialKeplerEnergy ν (spatialPoincareProd ν w) i < 0 := by
      rw [spatialKeplerEnergy_spatialPoincareProd hν hdom i]
      have := hν i
      have : 0 < ν i ^ 3 := by positivity
      have : 0 < 2 * (spatialBlock w i).2 0 ^ 2 := by positivity
      rw [neg_div]
      exact neg_neg_of_pos (by positivity)
    refine ⟨hν i, ?_, hE⟩
    by_contra hq
    have hq0 : spaceLength (bodyVector3 (spatialPoincareProd ν w).1 i) = 0 :=
      le_antisymm (not_lt.1 hq) (spaceLength_nonneg _)
    have : 0 ≤ spatialKeplerEnergy ν (spatialPoincareProd ν w) i := by
      unfold spatialKeplerEnergy
      rw [hq0, div_zero, sub_zero]
      have := hν i
      exact div_nonneg (spaceSq_nonneg _) (by positivity)
    linarith
  have hbs : SpatialBarrierState ν U (n * r) (spatialPoincareProd ν w) := by
    refine ⟨hneg, by rw [hact']; exact hU, ?_⟩
    rw [hact']
    have h1 := spatialStrongAMD_le_spatialFixedPlaneDeficit ν (spatialPoincareProd ν w)
    rw [spatialFixedPlaneDeficit_spatialPoincareProd hν hdom, ← spatialChartAMD_eq_sum_body] at h1
    linarith
  exact ⟨hdom, hKsub (hbar _ hbs)⟩

/-- **Item 3 (`LP:MAIN L14 (477–483)`, `LP:MAIN L18 (595–597)`, N2, N6): the spatial chart lift on
the stopped interval.**  Let `z` be a spatial moving solution on the order-connected `J ∋ 0` with
`z 0 = z₀` (aligned: `L(z₀) = |L(z₀)| e₃`), `t ∈ J`, and the strict stopped conditions on
`uIcc 0 t`.  Then there are a chart curve `w` and an open interval `I ⊇ uIcc 0 t` on which `w`
stays in the collision-free chart domain `spatialChartSafe ν` and solves the chart field of
`spatialChartHam ν μ = spatialHProd ν + μ · fSpatial ν ∘ Ψ` (two-sided derivatives), with
`Ψ (w u) = z u` on `uIcc 0 t` and fast actions of `w 0` equal to `Λ z₀`. -/
theorem spatialChartLift_of_stopped (hd : SpatialLiftData ν U z₀ δ r) {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (hs : SpatialStoppedOn ν z₀ δ r z t) :
    ∃ (w : ℝ → Phase (n + (n + n))) (I : Set ℝ), IsOpen I ∧ I.OrdConnected ∧ uIcc 0 t ⊆ I ∧
      (∀ u ∈ I, w u ∈ spatialChartSafe ν ∧
        HasDerivAt w (hamiltonianVectorField (spatialChartHam ν μ) (w u)) u) ∧
      (∀ u ∈ uIcc 0 t, spatialPoincareProd ν (w u) = z u) ∧
      fast (w 0).2 = spatialActionVector ν z₀ := by
  have hν := hd.pos_mass
  have hW := isOpen_spatialChartSafe hν
  have hF := contDiffOn_spatialLiftField hν μ
  have hK0 : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  have hKJ : uIcc (0 : ℝ) t ⊆ J := hJ.uIcc_subset h0 ht
  have huI : ∀ s : ℝ, s ∈ uIcc (0 : ℝ) t ↔ min 0 t ≤ s ∧ s ≤ max 0 t := fun s => Iff.rfl
  -- initial chart point
  have hpro := hd.prograde_of_stopped hJ h0 hz hz0 ht hs
  obtain ⟨w0, hw0dom, hw0⟩ : ∃ w0 ∈ spatialPoincareProdDom n, spatialPoincareProd ν w0 = z 0 := by
    have := (spatialPoincareProd_image hν).symm.subset (hpro 0 hK0).2.2.2
    exact this
  have hw0W : w0 ∈ spatialChartSafe ν := by
    refine ⟨hw0dom, ?_⟩
    show spatialPoincareProd ν w0 ∈ spatialCollisionFreeDomain n
    rw [hw0]; exact hz.2 0 h0
  -- maximal chart solution
  obtain ⟨Tm, Tp, y, hy⟩ := ((gen_maximal hW hF hw0W).1)
  -- projection to a physical solution and uniqueness
  obtain ⟨hWo, hFmov, hiff⟩ := spatial_moving_ode ν μ
  have hx : IsSolutionIn (spatialMovingField ν μ) (spatialCollisionFreeDomain n) (eIoo Tm Tp)
      (spatialPoincareProd ν ∘ y) :=
    fun s hsT => ⟨(hy.isSolution s hsT).1.2, spatialLiftPhysicalDeriv hν μ
      (spatialChartSafe_subset_dom _ (hy.isSolution s hsT).1)
      (((analyticOnNhd_spatialPulledHam hν μ) _ (hy.isSolution s hsT).1).differentiableAt)
      (hy.isSolution s hsT).2⟩
  have hzs := ((hiff J z).1 hz).mono hKJ
  have heq := gen_uniqueness_inter hWo hFmov (ordConnected_eIoo Tm Tp) ordConnected_uIcc
    (t₀ := 0) ⟨zero_mem_eIoo hy, hK0⟩ hx hzs (by simp [hy.init, hw0, hz0])
  have hproj : ∀ s ∈ eIoo Tm Tp, s ∈ uIcc (0 : ℝ) t →
      spatialPoincareProd ν (y s) = z s :=
    fun s hsT hsK => heq ⟨hsT, hsK⟩
  -- continuation over the compact zero-angle set
  obtain ⟨delta, M, L, hU, -⟩ := uniformDataNM
    (Q := spatialLiftQ (spatialActionVector ν z₀) r
      (strongThreshold ν (spatialActionVector ν z₀) - δ / 4)) hW hF
    (spatialChartSafe_shift_iff hν) (fun k w hw => spatialLiftField_periodic hν μ k w hw)
    (spatialLiftQ_isCompact _ _ _) (fun w hw => hw.1)
    (fun w hw => hd.mem_spatialChartSafe_of_liftQ hw)
  have hmemΦ : ∀ s ∈ eIoo Tm Tp, s ∈ uIcc (0 : ℝ) t →
      y s ∈ {w : Phase (n + (n + n)) | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈
        spatialLiftQ (spatialActionVector ν z₀) r
          (strongThreshold ν (spatialActionVector ν z₀) - δ / 4)} := by
    intro s hsT hsK
    have hyW := spatialChartSafe_subset_dom _ (hy.isSolution s hsT).1
    have hp := hproj s hsT hsK
    refine SpatialLiftData.zeroAngle_mem_spatialLiftQ ?_ ?_
    · have : fast (y s).2 = spatialActionVector ν (z s) := by
        rw [← hp]; exact (spatialActionVector_spatialPoincareProd hν hyW).symm
      rw [this]
      exact (hs s hsK).2.1.le
    · have hal := (hpro s hsK).2.1
      rw [← hp] at hal
      rw [spatialChartAMD_eq_of_aligned hν hyW hal, hp]
      exact hd.strongAMD_le_of_stopped hs hsK
  have hTp : ((max 0 t : ℝ) : EReal) < Tp := by
    by_contra hle
    rw [not_lt] at hle
    have := (gen_continuation hW hF hy hU).1 ⟨0, le_rfl, hy.pos_lt, fun s hs0 hsT =>
      hmemΦ s ⟨lt_of_lt_of_le hy.neg_lt (by exact_mod_cast hs0), hsT⟩
        ((huI s).2 ⟨(min_le_left 0 t).trans hs0, EReal.coe_le_coe_iff.1 (hsT.le.trans hle)⟩)⟩
    rw [this] at hle
    exact absurd hle (by simp)
  have hTm : Tm < ((min 0 t : ℝ) : EReal) := by
    by_contra hle
    rw [not_lt] at hle
    have := (gen_continuation hW hF hy hU).2 ⟨0, le_rfl, hy.neg_lt, fun s hsT hs0 =>
      hmemΦ s ⟨hsT, lt_of_le_of_lt (by exact_mod_cast hs0) hy.pos_lt⟩
        ((huI s).2 ⟨EReal.coe_le_coe_iff.1 (hle.trans hsT.le), hs0.trans (le_max_left 0 t)⟩)⟩
    rw [this] at hle
    exact absurd hle (by simp)
  have hsub : uIcc (0 : ℝ) t ⊆ eIoo Tm Tp := fun s hsK =>
    ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 ((huI s).1 hsK).1),
      lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ((huI s).1 hsK).2) hTp⟩
  refine ⟨y, eIoo Tm Tp, isOpen_eIoo _ _, ordConnected_eIoo _ _, hsub,
    fun s hsT => ⟨(hy.isSolution s hsT).1, ?_⟩,
    fun s hsK => hproj s (hsub hsK) hsK, ?_⟩
  · rw [spatialChartHam_field_eq hν μ (hy.isSolution s hsT).1]
    exact (hy.isSolution s hsT).2
  · have hyW0 := spatialChartSafe_subset_dom _ (hy.isSolution 0 (zero_mem_eIoo hy)).1
    rw [← spatialActionVector_spatialPoincareProd hν hyW0, hproj 0 (zero_mem_eIoo hy) hK0, hz0]

end SpatialLiftData

end KAM.Planetary.Spatial

end
