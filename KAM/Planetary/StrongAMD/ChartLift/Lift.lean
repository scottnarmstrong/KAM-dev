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
public import KAM.Planetary.Exponential.Lift
public import KAM.Planetary.StrongAMD.ChartLift.Stopped

/-!
# The chart lift on the stopped interval

Source: MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, the chart part, with N2, N6), track LP,
non-frozen.

`lpChartLift_of_stopped` follows the template `KAM.Planetary.lift` (track P): the maximal solution
`y` of the pulled-back chart field through a chart preimage of `z 0` projects to the physical
solution (`liftPhysicalDeriv`), equals `z` by uniqueness, and stays over the compact zero-angle
set `liftQ` of the box `[I⁰ - r, I⁰ + r]` with `ΣΓ ≤ B(I⁰) - δ/4`, so `uniform_data` and
`gen_continuation` put the stopped interval inside its maximal interval.  Only the strict stopped
conditions are used (not any drift or confinement conclusion).

* `lpMovingSolutionOn_mono`: restriction of a moving solution to a sub-interval (two-sided
  derivatives, so it is legitimate on the closed stopped interval).

-/

@[expose] public noncomputable section

open Set KAM KAM.ODE KAM.Planetary

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- Restriction of a moving solution to a subset of its interval. -/
theorem lpMovingSolutionOn_mono {ν : Fin n → ℝ} {μ : ℝ} {J J' : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : IsMovingSolutionOn ν μ J z) (h : J' ⊆ J) : IsMovingSolutionOn ν μ J' z := by
  obtain ⟨-, -, hiff⟩ := moving_ode ν μ
  exact (hiff J' z).2 (((hiff J z).1 hz).mono h)

/-- The box `[I⁰ - r, I⁰ + r]` with outer chart AMD `B(I⁰) - δ/4`, used only through `liftQ`
(the other `AMDBox` fields are irrelevant to the compact zero-angle set). -/
def lpStoppedBox (ν : Fin n → ℝ) (I0 : Fin n → ℝ) (δ r : ℝ) : AMDBox n where
  mass := ν
  lower := fun i => I0 i - r
  innerLower := 0
  innerUpper := 0
  upper := fun i => I0 i + r
  ecc := 0
  initialAMD := 0
  outerAMD := strongThreshold ν I0 - δ / 4
  distance := 0
  radius := 0

namespace LiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 2)} {δ r : ℝ}

private theorem lower_upper_of_norm {I0 I : Fin n → ℝ} (h : ‖I - I0‖ ≤ r) (i : Fin n) :
    I0 i - r ≤ I i ∧ I i ≤ I0 i + r := by
  have := norm_le_pi_norm (I - I0) i
  rw [Real.norm_eq_abs] at this
  have := abs_le.1 (this.trans h)
  simp only [Pi.sub_apply] at this
  constructor <;> linarith [this.1, this.2]

private theorem norm_of_lower_upper {I0 I : Fin n → ℝ} (hr : 0 ≤ r)
    (h : ∀ i, I0 i - r ≤ I i ∧ I i ≤ I0 i + r) : ‖I - I0‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have := h i
  simp only [Pi.sub_apply]
  constructor <;> linarith [this.1, this.2]

/-- Membership of the zero-angle point in the compact set `liftQ`. -/
theorem zeroAngle_mem_liftQ {w : Phase (n + n)}
    (hact : ‖fast w.2 - actionVector ν z₀‖ ≤ r)
    (hamd : chartAMD w ≤ strongThreshold ν (actionVector ν z₀) - δ / 4) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)) ∈
      liftQ (lpStoppedBox ν (actionVector ν z₀) δ r) := by
  refine ⟨funext fun i => udZero_fst w i, fun i => ?_, ?_⟩
  · have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = fast w.2 := by
      rw [udZero_snd]
    rw [h2]
    exact lower_upper_of_norm hact i
  · rw [chartAMD_zeroAngle]; exact hamd

/-- `hQW` of `uniform_data`: a point whose zero-angle point is in `liftQ` is in `chartSafe`.  The
action is in the `r`-ball (so in `U ⊆ 𝒬`), `Γ_i ≤ ΣΓ ≤ B(Λ) - n r < Λ_i` puts it in the chart
domain, and `Ψ w` is a barrier state with margin `n r`, hence collision-free. -/
theorem mem_chartSafe_of_liftQ (hd : LiftData ν U z₀ δ r) {w : Phase (n + n)}
    (hw : (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)) ∈
      liftQ (lpStoppedBox ν (actionVector ν z₀) δ r)) : w ∈ chartSafe ν := by
  obtain ⟨-, hb, hA⟩ := hw
  have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = fast w.2 := by
    rw [udZero_snd]
  rw [h2] at hb
  rw [chartAMD_zeroAngle] at hA
  have hact : ‖fast w.2 - actionVector ν z₀‖ ≤ r := norm_of_lower_upper hd.r_pos.le hb
  have hU : fast w.2 ∈ U := hd.ball _ hact
  have hamd : chartAMD w ≤ strongThreshold ν (fast w.2) - n * r := by
    have := hd.threshold_ball_le hact
    have hA' : chartAMD w ≤ strongThreshold ν (actionVector ν z₀) - δ / 4 := hA
    linarith
  have hdom : w ∈ poincareProdDom n := by
    intro i
    have hIpos : 0 < fast w.2 i := (hd.subset_chamber hU).1 i
    have h0 : (planetBlock w i).2 0 = fast w.2 i := by simp [planetBlock]
    have hΓ : poincareGamma (planetBlock w i) = lpGamma w i := by
      simp [poincareGamma, lpGamma, planetBlock, slow]
    have hle : lpGamma w i ≤ chartAMD w := by
      rw [chartAMD_eq_sum_lpGamma]
      exact Finset.single_le_sum (f := lpGamma w) (fun j _ => by unfold lpGamma; positivity)
        (Finset.mem_univ i)
    have hB := strongThreshold_le_action ν (fast w.2) i
    refine ⟨by rw [h0]; exact hIpos, ?_⟩
    rw [hΓ, h0]
    linarith [hd.n_mul_r_pos]
  obtain ⟨K, -, hKsub, hbar⟩ := exists_barrierCompact hd.pos_mass hd.two_le hd.compact
    hd.subset_chamber (m := n * r) hd.n_mul_r_pos
  have hpro := (sec_domain_chart_facts hd.pos_mass hdom).1
  have hact' : actionVector ν (poincareProd ν 1 w) = fast w.2 := by
    funext i
    exact lpChart_action hd.pos_mass hdom i
  have hbs : BarrierState ν U (n * r) (poincareProd ν 1 w) := by
    refine ⟨fun i => ⟨(hpro i).2.1, (hpro i).2.2.1⟩, by rw [hact']; exact hU, ?_⟩
    rw [hact', lpChart_strongAMD hd.pos_mass hdom]
    exact hamd
  exact ⟨hdom, hKsub (hbar _ hbs)⟩

/-- **Item 3 (`LP:MAIN L14 (477–483)`, N2, N6): the chart lift on the stopped interval.**  Let `z`
be a moving solution on the order-connected `J ∋ 0` with `z 0 = z₀`, `t ∈ J`, and the strict
stopped conditions on `uIcc 0 t`.  Then there are a chart curve `w` and an open interval `I ⊇
uIcc 0 t` on which `w` stays in `chartSafe ν` and solves the chart field of `liftChartHam ν μ`
(two-sided derivatives), with `Ψ (w u) = z u` on `uIcc 0 t` and `Λ (w 0) = Λ z₀`. -/
theorem lpChartLift_of_stopped (hd : LiftData ν U z₀ δ r) {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 2)}
    (hz : IsMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (hs : StoppedOn ν z₀ δ r z t) :
    ∃ (w : ℝ → Phase (n + n)) (I : Set ℝ), IsOpen I ∧ I.OrdConnected ∧ uIcc 0 t ⊆ I ∧
      (∀ u ∈ I, w u ∈ chartSafe ν ∧
        HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u) ∧
      (∀ u ∈ uIcc 0 t, poincareProd ν 1 (w u) = z u) ∧
      fast (w 0).2 = actionVector ν z₀ := by
  have hν := hd.pos_mass
  have hW := isOpen_chartSafe hν
  have hF := contDiffOn_liftField hν μ
  have hK0 : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  have hKJ : uIcc (0 : ℝ) t ⊆ J := hJ.uIcc_subset h0 ht
  have huI : ∀ s : ℝ, s ∈ uIcc (0 : ℝ) t ↔ min 0 t ≤ s ∧ s ≤ max 0 t := fun s => Iff.rfl
  -- initial chart point
  have hpro := hd.prograde_of_stopped hJ h0 hz hz0 ht hs
  obtain ⟨w0, hw0dom, hw0, -⟩ := lpChart_inverse hν (hpro 0 hK0).1
  have hw0W : w0 ∈ chartSafe ν := by
    refine ⟨hw0dom, ?_⟩
    show poincareProd ν 1 w0 ∈ collisionFreeDomain n
    rw [hw0]; exact hz.2 0 h0
  -- maximal chart solution
  obtain ⟨Tm, Tp, y, hy⟩ := ((gen_maximal hW hF hw0W).1)
  -- projection to a physical solution and uniqueness
  obtain ⟨hWo, hFmov, hiff⟩ := moving_ode ν μ
  have hx : IsSolutionIn (hamiltonianVectorField (movingHamiltonian 1 1 ν μ))
      (collisionFreeDomain (n := n)) (eIoo Tm Tp) (poincareProd ν 1 ∘ y) :=
    fun s hsT => ⟨(hy.isSolution s hsT).1.2, liftPhysicalDeriv hν μ
      (chartSafe_subset_dom _ (hy.isSolution s hsT).1)
      (((analyticOnNhd_liftChartHam hν μ) _ (hy.isSolution s hsT).1).differentiableAt)
      (hy.isSolution s hsT).2⟩
  have hzs := ((hiff J z).1 hz).mono hKJ
  have heq := gen_uniqueness_inter hWo hFmov (ordConnected_eIoo Tm Tp) ordConnected_uIcc
    (t₀ := 0) ⟨zero_mem_eIoo hy, hK0⟩ hx hzs (by simp [hy.init, hw0, hz0])
  have hproj : ∀ s ∈ eIoo Tm Tp, s ∈ uIcc (0 : ℝ) t → poincareProd ν 1 (y s) = z s :=
    fun s hsT hsK => heq ⟨hsT, hsK⟩
  -- continuation over the compact zero-angle set
  obtain ⟨delta, M, L, hU, -⟩ := uniform_data
    (Q := liftQ (lpStoppedBox ν (actionVector ν z₀) δ r)) hW hF
    (lift_chartSafe_shift_iff hν) (fun k w hw => liftField_periodic hν μ k w hw)
    (liftQ_isCompact _) (fun w hw => hw.1) (fun w hw => hd.mem_chartSafe_of_liftQ hw)
  have hmemΦ : ∀ s ∈ eIoo Tm Tp, s ∈ uIcc (0 : ℝ) t →
      y s ∈ {w : Phase (n + n) | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈
        liftQ (lpStoppedBox ν (actionVector ν z₀) δ r)} := by
    intro s hsT hsK
    have hyW := chartSafe_subset_dom _ (hy.isSolution s hsT).1
    have hp := hproj s hsT hsK
    refine zeroAngle_mem_liftQ ?_ ?_
    · have : fast (y s).2 = actionVector ν (z s) := by
        funext i
        rw [← lpChart_action hν hyW i, hp]
        rfl
      rw [this]
      exact (hs s hsK).2.1.le
    · rw [← lpChart_strongAMD hν hyW, hp]
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
    fun s hsT => ⟨(hy.isSolution s hsT).1, (hy.isSolution s hsT).2⟩,
    fun s hsK => hproj s (hsub hsK) hsK, ?_⟩
  have hyW0 := chartSafe_subset_dom _ (hy.isSolution 0 (zero_mem_eIoo hy)).1
  funext i
  rw [← lpChart_action hν hyW0 i, hproj 0 (zero_mem_eIoo hy) hK0, hz0]
  rfl

end LiftData

end KAM.Planetary.StrongAMD

end
