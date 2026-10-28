/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.LowAMDRegion
public import KAM.ODE.Continuation
public import KAM.ODE.Hamiltonian
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness
public import KAM.Planetary.AMD.MovingODE
public import KAM.Planetary.AMD.Setting
public import KAM.Planetary.Exponential.Dictionary
public import KAM.Planetary.Exponential.Enlargement
public import KAM.Planetary.Exponential.RealDomain
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Exponential.UniformData
public import KAM.Planetary.Hamiltonian.Chart

/-!
# P14 package E9: lifting a physical solution segment to the Poincaré chart

Blueprint P, Part 14 (`bpP:p14:lift`, steps `li-init`, `li-max`, `li-proj`, `li-cont`,
`li-concl`).  A moving-frame solution `z` on `[l, r] ∋ 0` that stays in the outer AMD region is
the image under the product Poincaré chart `Ψ = poincareProd m 1` of a solution `y` of the
pulled-back Hamiltonian field on the safe chart domain `chartSafe`.

* `li-init`: the initial point is `w₀ ∈ chartSafe` with `Ψ w₀ = z 0` (chart onto prograde region);
* `li-max`: the pulled-back field is `C¹` on the open `chartSafe` and `2π`-periodic in the fast
  angles; `y` is the maximal solution through `w₀`;
* `li-proj`: `Ψ ∘ y` is a physical solution (`chart_orbit`) and equals `z` by uniqueness;
* `li-cont`: on `(Tm, Tp) ∩ [l, r]` the solution stays over the compact zero-angle set
  `liftQ B`, so uniform data (E8) forces `Tp = ⊤` and `Tm = ⊥` unless `[l, r] ⊂ (Tm, Tp)`;
* `li-concl`: the conclusion, with the action and AMD identities from the E1 dictionary.
-/

@[expose] public noncomputable section

open Set KAM KAM.ODE KAM.Kepler
open scoped NNReal

namespace KAM.Planetary

variable {n : ℕ}

/-- The pulled-back moving Hamiltonian `w ↦ H_mov (Ψ w)` for the product chart (`κ = 1`). -/
def liftChartHam (m : Fin n → ℝ) (mu : ℝ) : Phase (n + n) → ℝ :=
  fun w => movingHamiltonian 1 1 m mu (poincareProd m 1 w)

/-- The compact set of zero-angle points over the closed outer cylinder. -/
def liftQ (B : AMDBox n) : Set (Phase (n + n)) :=
  {w | fast w.1 = 0 ∧ (∀ i, B.lower i ≤ fast w.2 i ∧ fast w.2 i ≤ B.upper i) ∧
    chartAMD w ≤ B.outerAMD}

/-- Pointwise chart-orbit: a chart-field solution through the safe domain projects to a physical
solution.  `poincareProd` has type `Phase (n + n) → Phase (n * 2)`, so the equal-dimension chart
`poincareProdCast` of Part 1 is used through the reindexing `phaseCast`. -/
theorem liftPhysicalDeriv {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (mu : ℝ)
    {y : ℝ → Phase (n + n)} {t : ℝ} (hyO : y t ∈ poincareProdDom n)
    (hd : DifferentiableAt ℝ (liftChartHam m mu) (y t))
    (hy : HasDerivAt y (hamiltonianVectorField (liftChartHam m mu) (y t)) t) :
    HasDerivAt (poincareProd m 1 ∘ y)
      (hamiltonianVectorField (movingHamiltonian 1 1 m mu) (poincareProd m 1 (y t))) t := by
  set c := phaseCast (Nat.mul_two n) with hc
  have hchart : IsChart 1 (poincareProdCast m 1) (poincareProdCastDom n) :=
    ⟨analyticOnNhd_poincareProdCast hm one_pos, poincareProdCast_symplectic hm one_pos⟩
  have hG : chartPullback 1 (movingHamiltonian 1 1 m mu) (poincareProdCast m 1) =
      liftChartHam m mu ∘ c := by
    funext z
    simp [chartPullback, liftChartHam, poincareProdCast, hc]
  have hyO' : (c.symm ∘ y) t ∈ poincareProdCastDom n := by
    show c (c.symm (y t)) ∈ poincareProdDom n
    rwa [c.apply_symm_apply]
  have hy' : HasDerivAt (c.symm ∘ y)
      (c.symm (hamiltonianVectorField (liftChartHam m mu) (y t))) t :=
    c.symm.hasFDerivAt.comp_hasDerivAt t hy
  have hd' : DifferentiableAt ℝ (liftChartHam m mu) (c (c.symm (y t))) := by
    rwa [c.apply_symm_apply]
  have key := chart_orbit one_pos hchart (H := movingHamiltonian 1 1 m mu) (J := {t})
    (y := c.symm ∘ y) (fun s hs => by rw [mem_singleton_iff.1 hs]; exact hyO')
    (fun s hs => by
      rw [mem_singleton_iff.1 hs, hG]
      refine ⟨hd'.comp _ c.differentiableAt, ?_⟩
      rw [Function.comp_apply]
      have := phaseCast_hamiltonianVectorField (Nat.mul_two n) (liftChartHam m mu) (c.symm (y t))
      rw [← hc, c.apply_symm_apply] at this
      rw [this]; exact hy') t rfl
  have hfun : poincareProdCast m 1 ∘ (c.symm ∘ y) = poincareProd m 1 ∘ y := by
    funext s
    simp [poincareProdCast, hc]
  rw [hfun] at key
  have hpt : poincareProdCast m 1 ((c.symm ∘ y) t) = poincareProd m 1 (y t) := by
    simp [poincareProdCast, hc]
  rw [hpt] at key
  exact key.2

theorem isOpen_chartSafe {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) : IsOpen (chartSafe m) :=
  isOpen_poincareProd_preimage hm one_pos

theorem chartSafe_subset_dom (m : Fin n → ℝ) : chartSafe m ⊆ poincareProdDom n :=
  inter_subset_left

theorem analyticOnNhd_liftChartHam {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (mu : ℝ) :
    AnalyticOnNhd ℝ (liftChartHam m mu) (chartSafe m) :=
  (analyticOnNhd_movingHamiltonian 1 1 m mu).comp
    ((analyticOnNhd_poincareProd hm one_pos).mono inter_subset_left) fun _ hw => hw.2

theorem contDiffOn_liftField {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (mu : ℝ) :
    ContDiffOn ℝ 1 (hamiltonianVectorField (liftChartHam m mu)) (chartSafe m) :=
  ham_smooth_c1 (isOpen_chartSafe hm)
    ((analyticOnNhd_liftChartHam hm mu).contDiffOn (isOpen_chartSafe hm).uniqueDiffOn)

theorem liftFastShift_neg (k : Fin n → ℤ) :
    (fastShift (a := n) (b := n) (-k) : Phase (n + n)) = -fastShift (a := n) (b := n) k := by
  refine Prod.ext (funext fun j => ?_) ?_
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift, Fin.append_left]
  · simp [fastShift]

theorem lift_chartSafe_shift_iff {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (k : Fin n → ℤ)
    (w : Phase (n + n)) : w ∈ chartSafe m ↔ w + fastShift (a := n) (b := n) k ∈ chartSafe m := by
  have key : ∀ (k : Fin n → ℤ) (w : Phase (n + n)), w ∈ chartSafe m →
      w + fastShift (a := n) (b := n) k ∈ chartSafe m := by
    intro k w hw
    obtain ⟨h1, h2⟩ := poincareProd_lattice hm one_pos hw.1 k
    exact ⟨h1, by simpa [h2] using hw.2⟩
  refine ⟨key k w, fun h => ?_⟩
  have := key (-k) _ h
  rwa [liftFastShift_neg, add_neg_cancel_right] at this

theorem liftField_periodic {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (mu : ℝ) (k : Fin n → ℤ) :
    ∀ w ∈ chartSafe m, hamiltonianVectorField (liftChartHam m mu)
      (w + fastShift (a := n) (b := n) k) = hamiltonianVectorField (liftChartHam m mu) w := by
  intro x hx
  have hH : ∀ y ∈ chartSafe m, liftChartHam m mu (y + fastShift (a := n) (b := n) k) =
      liftChartHam m mu y := by
    intro y hy
    simp only [liftChartHam, (poincareProd_lattice hm one_pos hy.1 k).2]
  have hev : (fun y => liftChartHam m mu (y + fastShift (a := n) (b := n) k)) =ᶠ[nhds x]
      liftChartHam m mu :=
    Filter.eventuallyEq_of_mem ((isOpen_chartSafe hm).mem_nhds hx) hH
  have hf : fderiv ℝ (liftChartHam m mu) (x + fastShift (a := n) (b := n) k) =
      fderiv ℝ (liftChartHam m mu) x := by
    rw [← hev.fderiv_eq, fderiv_comp_add_right]
  simp only [hamiltonianVectorField, hf]

theorem liftQ_isClosed (B : AMDBox n) : IsClosed (liftQ B) := by
  have hc : Continuous (fun w : Phase (n + n) => chartAMD w) := by
    unfold chartAMD slow; fun_prop
  have hf1 : ∀ i, Continuous (fun w : Phase (n + n) => fast w.1 i) := fun i => by
    unfold fast; fun_prop
  have hf2 : ∀ i, Continuous (fun w : Phase (n + n) => fast w.2 i) := fun i => by
    unfold fast; fun_prop
  have h1 : IsClosed {w : Phase (n + n) | fast w.1 = 0} := by
    exact isClosed_eq (continuous_pi hf1) continuous_const
  have h2 : IsClosed {w : Phase (n + n) |
      ∀ i, B.lower i ≤ fast w.2 i ∧ fast w.2 i ≤ B.upper i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (hf2 i)).inter
      (isClosed_le (hf2 i) continuous_const)
  exact h1.inter (h2.inter (isClosed_le hc continuous_const))

theorem liftQ_slow_bound (B : AMDBox n) {w : Phase (n + n)} (hw : w ∈ liftQ B) (i : Fin n) :
    |slow w.1 i| ≤ 2 * |B.outerAMD| + 1 ∧ |slow w.2 i| ≤ 2 * |B.outerAMD| + 1 := by
  have h1 : ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 ≤ chartAMD w :=
    Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 := hw.2.2
  have h3 := le_abs_self B.outerAMD
  have a1 := sq_abs (slow w.1 i)
  have a2 := sq_abs (slow w.2 i)
  constructor <;> nlinarith [abs_nonneg (slow w.1 i), abs_nonneg (slow w.2 i),
    sq_nonneg (slow w.1 i), sq_nonneg (slow w.2 i), sq_nonneg (|slow w.1 i| - 1),
    sq_nonneg (|slow w.2 i| - 1)]

theorem liftQ_fast_bound (B : AMDBox n) {w : Phase (n + n)} (hw : w ∈ liftQ B) (i : Fin n) :
    |fast w.2 i| ≤ ∑ j, (|B.lower j| + |B.upper j|) := by
  obtain ⟨h1, h2⟩ := hw.2.1 i
  have : |fast w.2 i| ≤ |B.lower i| + |B.upper i| := by
    rw [abs_le']
    constructor <;> linarith [le_abs_self (B.upper i), neg_abs_le (B.lower i),
      abs_nonneg (B.upper i), abs_nonneg (B.lower i)]
  exact this.trans (Finset.single_le_sum (f := fun j => |B.lower j| + |B.upper j|)
    (fun j _ => by positivity) (Finset.mem_univ i))

theorem liftQ_isCompact (B : AMDBox n) : IsCompact (liftQ B) := by
  set R : ℝ := 2 * |B.outerAMD| + 1 + ∑ j, (|B.lower j| + |B.upper j|) with hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ ∑ j, (|B.lower j| + |B.upper j|) := Finset.sum_nonneg fun j _ => by positivity
    positivity
  refine Metric.isCompact_of_isClosed_isBounded (liftQ_isClosed B)
    (Metric.isBounded_closedBall (x := (0 : Phase (n + n))) (r := R) |>.subset fun w hw => ?_)
  have hS : 0 ≤ ∑ j, (|B.lower j| + |B.upper j|) :=
    Finset.sum_nonneg fun j _ => by positivity
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have h0 : w.1 (Fin.castAdd n i) = 0 := congrFun hw.1 i
      rw [h0]; simpa using hR0
    · have := (liftQ_slow_bound B hw i).1
      show ‖slow w.1 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith [abs_nonneg (B.outerAMD)]
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := liftQ_fast_bound B hw i
      show ‖fast w.2 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith [abs_nonneg (B.outerAMD)]
    · have := (liftQ_slow_bound B hw i).2
      show ‖slow w.2 i‖ ≤ R
      rw [Real.norm_eq_abs]; linarith [abs_nonneg (B.outerAMD)]

theorem chartAMD_zeroAngle (w : Phase (n + n)) :
    chartAMD (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)) = chartAMD w := by
  have h1 : slow (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).1 = slow w.1 :=
    funext fun i => udZero_fst_natAdd w i
  have h2 : slow (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = slow w.2 := by
    rw [udZero_snd]
  simp only [chartAMD, h1, h2]

/-- `li-cont` (membership): the chart point over a physical point of the outer region has its
zero-angle point in `liftQ B`. -/
theorem liftQ_of_orbit (B : AMDBox n) (hB : B.Admissible) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (hz : poincareProd B.mass 1 w ∈ amdOuter B) :
    assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ liftQ B := by
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  obtain ⟨-, hfacts, hamd⟩ := sec_domain_chart_facts hm hw
  obtain ⟨-, hact, hA⟩ := hz
  refine ⟨funext fun i => udZero_fst w i, fun i => ?_, ?_⟩
  · have := (hfacts i).1
    have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = fast w.2 := by
      rw [udZero_snd]
    rw [h2, ← this]
    exact ⟨(hact i).1.le, (hact i).2.le⟩
  · rw [chartAMD_zeroAngle, ← hamd]; exact hA.le

/-- `hQW` of `uniform_data` for `liftQ B`. -/
theorem liftQ_mem_chartSafe (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {w : Phase (n + n)}
    (hw : assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ liftQ B) : w ∈ chartSafe B.mass := by
  obtain ⟨-, hb, hA⟩ := hw
  have h2 : fast (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = fast w.2 := by
    rw [udZero_snd]
  rw [h2] at hb
  rw [chartAMD_zeroAngle] at hA
  exact (real_domain B hB hd).1 (original_cylinder_subset B hB hd ⟨hb, hA⟩)

theorem lift (B : AMDBox n) (hB : B.Admissible) (mu l r : ℝ)
    (hl : l ≤ 0) (hr : 0 ≤ r) {z : ℝ → Phase (n*2)}
    (hz : IsMovingSolutionOn B.mass mu (Icc l r) z) (hout : ∀ t ∈ Icc l r, z t ∈ amdOuter B) :
    ∃ y : ℝ → Phase (n+n), ∀ t ∈ Icc l r,
      y t ∈ chartSafe B.mass ∧ poincareProd B.mass 1 (y t) = z t ∧
      HasDerivAt y (KAM.hamiltonianVectorField
        (fun w => movingHamiltonian 1 1 B.mass mu (poincareProd B.mass 1 w)) (y t)) t ∧
      (∀ i, fast (y t).2 i = keplerAction B.mass (z t) i) ∧
      chartAMD (y t) = physicalAMD B.mass (z t) := by
  have hm : ∀ i, 0 < B.mass i := fun i => (hB.1 i).1
  obtain ⟨kappa, e, A, hd⟩ := enlarge B hB
  have hW := isOpen_chartSafe hm
  have hF := contDiffOn_liftField hm mu
  have h0 : (0 : ℝ) ∈ Icc l r := ⟨hl, hr⟩
  -- `stepP:p14:li-init`
  have hz0 : z 0 ∈ poincareProd B.mass 1 '' poincareProdDom n := by
    rw [poincareProd_image_prograde hm]; exact (hout 0 h0).1
  obtain ⟨w0, hw0dom, hw0⟩ := hz0
  have hw0W : w0 ∈ chartSafe B.mass := by
    refine ⟨hw0dom, ?_⟩
    show poincareProd B.mass 1 w0 ∈ collisionFreeDomain n
    rw [hw0]; exact hz.2 0 h0
  -- `stepP:p14:li-max`
  obtain ⟨Tm, Tp, y, hy⟩ := ((gen_maximal hW hF hw0W).1)
  -- `stepP:p14:li-proj`
  obtain ⟨hWo, hFmov, hiff⟩ := moving_ode B.mass mu
  have hx : IsSolutionIn (hamiltonianVectorField (movingHamiltonian 1 1 B.mass mu))
      (collisionFreeDomain (n := n)) (eIoo Tm Tp) (poincareProd B.mass 1 ∘ y) :=
    fun t ht => ⟨(hy.isSolution t ht).1.2, liftPhysicalDeriv hm mu
      (chartSafe_subset_dom _ (hy.isSolution t ht).1)
      (((analyticOnNhd_liftChartHam hm mu) _ (hy.isSolution t ht).1).differentiableAt)
      (hy.isSolution t ht).2⟩
  have hzs := (hiff _ _).1 hz
  have heq := gen_uniqueness_inter hWo hFmov (ordConnected_eIoo Tm Tp) ordConnected_Icc
    (t₀ := 0) ⟨zero_mem_eIoo hy, h0⟩ hx hzs (by simp [hy.init, hw0])
  have hproj : ∀ t ∈ eIoo Tm Tp, t ∈ Icc l r → poincareProd B.mass 1 (y t) = z t :=
    fun t ht htI => heq ⟨ht, htI⟩
  -- `stepP:p14:li-cont`
  obtain ⟨delta, M, L, hU, -⟩ := uniform_data (Q := liftQ B) hW hF
    (lift_chartSafe_shift_iff hm) (fun k w hw => liftField_periodic hm mu k w hw)
    (liftQ_isCompact B) (fun w hw => hw.1) (fun w hw => liftQ_mem_chartSafe B hB hd hw)
  have hmemΦ : ∀ t ∈ eIoo Tm Tp, t ∈ Icc l r →
      y t ∈ {w : Phase (n + n) | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ liftQ B} :=
    fun t ht htI => liftQ_of_orbit B hB (chartSafe_subset_dom _ (hy.isSolution t ht).1)
      (by rw [hproj t ht htI]; exact hout t htI)
  have hTp : (r : EReal) < Tp := by
    by_contra hle
    rw [not_lt] at hle
    have := (gen_continuation hW hF hy hU).1 ⟨0, le_rfl, hy.pos_lt, fun t ht0 htT =>
      hmemΦ t ⟨lt_of_lt_of_le hy.neg_lt (by exact_mod_cast ht0), htT⟩
        ⟨by linarith, EReal.coe_le_coe_iff.1 (htT.le.trans hle)⟩⟩
    rw [this] at hle
    exact absurd hle (by simp)
  have hTm : Tm < (l : EReal) := by
    by_contra hle
    rw [not_lt] at hle
    have := (gen_continuation hW hF hy hU).2 ⟨0, le_rfl, hy.neg_lt, fun t htT ht0 =>
      hmemΦ t ⟨htT, lt_of_le_of_lt (by exact_mod_cast ht0) hy.pos_lt⟩
        ⟨EReal.coe_le_coe_iff.1 (hle.trans htT.le), by linarith⟩⟩
    rw [this] at hle
    exact absurd hle (by simp)
  -- `stepP:p14:li-concl`
  refine ⟨y, fun t ht => ?_⟩
  have htJ : t ∈ eIoo Tm Tp :=
    ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 ht.1),
      lt_of_le_of_lt (EReal.coe_le_coe_iff.2 ht.2) hTp⟩
  have hyW := (hy.isSolution t htJ).1
  have hp := hproj t htJ ht
  obtain ⟨-, hfacts, hamd⟩ := sec_domain_chart_facts hm (chartSafe_subset_dom _ hyW)
  refine ⟨hyW, hp, (hy.isSolution t htJ).2, fun i => ?_, ?_⟩
  · rw [← hp]; exact ((hfacts i).1).symm
  · rw [← hp]; exact hamd.symm

end KAM.Planetary

end
