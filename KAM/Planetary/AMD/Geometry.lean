/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Planetary.AMD.Setting
public import KAM.Planetary.AMD.Elements
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.BarycentricPositions
public import KAM.Frozen.Planetary.Defs.NoCollision
public import KAM.Frozen.Planetary.Defs.PairBounds

/-!
# AMD geometry (P14, package A2)

Blueprint P, Part 14 (`bpP:p14:geometry`, steps `geo-a` to `geo-d`, `geo-k`).  On the outer low-AMD
region of an admissible box the axes, radii, momenta, eccentricities and pairwise distances obey
the box bounds (`geometry`), and the geometric compact set `amdCompact B` is compact and
collision free (`amd_compact`).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

private theorem continuous_planeLength_aux : Continuous planeLength := by
  have : planeSq = fun w : Fin 2 → ℝ => ∑ k, w k ^ 2 := rfl
  have h : Continuous planeSq := by rw [this]; fun_prop
  exact Real.continuous_sqrt.comp h

private theorem continuous_bodyVector_aux (i : Fin n) :
    Continuous (fun q : Fin (n * 2) → ℝ => bodyVector q i) := by
  unfold bodyVector; fun_prop

/-- Pair bounds for barycentric positions from the heliocentric radial and pair bounds. -/
private theorem pairBounds_bary {d R : ℝ} (hR : 0 < R) {m : Fin n → ℝ} {q : Fin (n * 2) → ℝ}
    (mu : ℝ)
    (h1 : ∀ i, d ≤ planeLength (bodyVector q i) ∧ planeLength (bodyVector q i) ≤ R)
    (h2 : ∀ i j, i ≠ j → d ≤ planeLength (bodyVector q i - bodyVector q j)) :
    PairBounds d (2 * R) (barycentricPositions 1 m mu q) := by
  have hup : ∀ i j, planeLength (bodyVector q i - bodyVector q j) ≤ 2 * R := fun i j => by
    have := KAM.Kepler.planeLength_add_le (bodyVector q i) (-bodyVector q j)
    rw [← sub_eq_add_neg, KAM.Kepler.planeLength_neg] at this
    linarith [(h1 i).2, (h1 j).2]
  intro i j hij
  unfold barycentricPositions
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ k =>
      simp only [Fin.cons_zero, Fin.cons_succ, add_sub_cancel_left]
      exact ⟨(h1 k).1, by linarith [(h1 k).2]⟩
  | succ k =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ, sub_add_cancel_left, KAM.Kepler.planeLength_neg]
      exact ⟨(h1 k).1, by linarith [(h1 k).2]⟩
    | succ l =>
      simp only [Fin.cons_succ, add_sub_add_left_eq_sub]
      exact ⟨h2 l k (fun h => hij (by rw [h])), hup l k⟩

/-- `bpP:p14:geometry`. -/
theorem geometry (B : AMDBox n) (hB : B.Admissible) {z : Phase (n * 2)}
    (hz : z ∈ amdOuter B) :
    (∀ i, (B.lower i / B.mass i)^2 < keplerAxis B.mass z i ∧
      keplerAxis B.mass z i < (B.upper i / B.mass i)^2 ∧
      planeLength (bodyVector z.2 i) < B.mass i * Real.sqrt (2 / B.distance)) ∧
    (∀ i j, i < j → B.distance ≤
      planeLength (bodyVector z.1 j) - planeLength (bodyVector z.1 i)) ∧
    z ∈ amdCompact B ∧ NoCollision z.1 ∧
    (∀ i, planeLength (keplerEccVector B.mass z i) < B.ecc ∧
      B.distance ≤ planeLength (bodyVector z.1 i) ∧
      planeLength (bodyVector z.1 i) ≤ B.radius) ∧
    ∀ mu : ℝ, PairBounds B.distance (2 * B.radius)
      (barycentricPositions 1 B.mass mu z.1) := by
  obtain ⟨hbox, he0, he1, -, -, hbar, hd, hR, hrad, hsep⟩ := hB
  obtain ⟨hpro, hact, hamd⟩ := hz
  have hecc := ecc_bound (A := B.outerAMD) (e := B.ecc) hpro (fun i => (hbox i).2.1)
    (fun i => (hact i).1) hamd he0 he1 (fun i => (hbar i).le)
  have hel := fun i => elements (m := B.mass) (z := z) i (hpro i)
  have hm : ∀ i, 0 < B.mass i := fun i => (hbox i).1
  have h1e : 0 < 1 - B.ecc := by linarith
  -- axis bounds
  have haxis : ∀ i, (B.lower i / B.mass i)^2 < keplerAxis B.mass z i ∧
      keplerAxis B.mass z i < (B.upper i / B.mass i)^2 := fun i => by
    obtain ⟨-, hΛ, hΛ2, -⟩ := hel i
    obtain ⟨hl, hu⟩ := hact i
    have hma := hm i
    have hlo := (hbox i).2.1
    have : keplerAxis B.mass z i = (keplerAction B.mass z i / B.mass i) ^ 2 := by
      rw [div_pow, eq_div_iff (by positivity)]; linarith [hΛ2]
    rw [this]
    refine ⟨?_, ?_⟩
    · exact pow_lt_pow_left₀ (div_lt_div_of_pos_right hl hma) (by have := hlo; positivity)
        two_ne_zero
    · exact pow_lt_pow_left₀ (div_lt_div_of_pos_right hu hma) (by positivity) two_ne_zero
  -- radial bounds
  have hrlow : ∀ i, (B.lower i / B.mass i)^2 * (1 - B.ecc) ≤
      planeLength (bodyVector z.1 i) := fun i => by
    obtain ⟨ha, -, -, -, -, -, -, -, hlow, -⟩ := hel i
    have h0 := (hecc i).1
    have := (haxis i).1
    calc (B.lower i / B.mass i)^2 * (1 - B.ecc)
        ≤ keplerAxis B.mass z i * (1 - B.ecc) := mul_le_mul_of_nonneg_right this.le h1e.le
      _ ≤ keplerAxis B.mass z i * (1 - planeLength (keplerEccVector B.mass z i)) :=
          mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ ≤ _ := hlow
  have hrup : ∀ i, planeLength (bodyVector z.1 i) ≤ (B.upper i / B.mass i)^2 * (1 + B.ecc) :=
    fun i => by
    obtain ⟨ha, -, -, -, -, -, -, -, -, hup, -⟩ := hel i
    have h0 := (hecc i).1
    have := (haxis i).2
    calc planeLength (bodyVector z.1 i)
        ≤ keplerAxis B.mass z i * (1 + planeLength (keplerEccVector B.mass z i)) := hup
      _ ≤ keplerAxis B.mass z i * (1 + B.ecc) :=
          mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ ≤ _ := mul_le_mul_of_nonneg_right this.le (by linarith)
  have hr1 : ∀ i, B.distance ≤ planeLength (bodyVector z.1 i) ∧
      planeLength (bodyVector z.1 i) ≤ B.radius := fun i =>
    ⟨(hrad i).1.trans (hrlow i), (hrup i).trans (hrad i).2⟩
  -- momentum
  have hmom : ∀ i, planeLength (bodyVector z.2 i) < B.mass i * Real.sqrt (2 / B.distance) :=
    fun i => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hel i
    have hr := (hr1 i).1
    have hsq : planeSq (bodyVector z.2 i) < (B.mass i) ^ 2 * (2 / B.distance) := by
      refine hs.trans_le ?_
      rw [mul_div_assoc', div_le_iff₀ (hpro i).2.1, mul_comm _ (planeLength _)]
      have : (B.mass i)^2 * 2 / B.distance * planeLength (bodyVector z.1 i) ≥
          (B.mass i)^2 * 2 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hd]
        exact mul_le_mul_of_nonneg_left hr (by positivity)
      nlinarith
    have hnn : 0 ≤ planeSq (bodyVector z.2 i) := Finset.sum_nonneg fun k _ => sq_nonneg _
    calc planeLength (bodyVector z.2 i) = Real.sqrt (planeSq (bodyVector z.2 i)) := rfl
      _ < Real.sqrt ((B.mass i) ^ 2 * (2 / B.distance)) := Real.sqrt_lt_sqrt hnn hsq
      _ = B.mass i * Real.sqrt (2 / B.distance) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hm i).le]
  -- ordering of radii
  have hord : ∀ i j, i < j → B.distance ≤
      planeLength (bodyVector z.1 j) - planeLength (bodyVector z.1 i) := fun i j hij => by
    have := hsep i j hij
    linarith [hrlow j, hrup i]
  have hpair : ∀ i j, i ≠ j → B.distance ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have := KAM.Kepler.abs_planeLength_sub_le (bodyVector z.1 i) (bodyVector z.1 j)
      have := hord i j h
      have := neg_abs_le (planeLength (bodyVector z.1 i) - planeLength (bodyVector z.1 j))
      linarith
    · have := KAM.Kepler.abs_planeLength_sub_le (bodyVector z.1 i) (bodyVector z.1 j)
      have := hord j i h
      have := le_abs_self (planeLength (bodyVector z.1 i) - planeLength (bodyVector z.1 j))
      linarith
  have hcomp : z ∈ amdCompact B :=
    ⟨fun i => ⟨(hr1 i).1, (hr1 i).2, (hmom i).le⟩, hpair⟩
  refine ⟨fun i => ⟨(haxis i).1, (haxis i).2, hmom i⟩, hord, hcomp, ?_,
    fun i => ⟨(hecc i).1, hr1 i⟩, fun mu => pairBounds_bary hR mu hr1 hpair⟩
  exact ⟨fun i => hd.trans_le (hr1 i).1,
    fun i j hij => hd.trans_le (hpair i j hij)⟩

/-- `bpP:p14:geometry` (`geo-k`): the geometric compact set is compact and collision free. -/
theorem amd_compact (B : AMDBox n) (hB : B.Admissible) :
    IsCompact (amdCompact B) ∧ amdCompact B ⊆ collisionFreeDomain n := by
  obtain ⟨-, -, -, -, -, -, hd, hR, -⟩ := hB
  have hcl : IsClosed (amdCompact B) := by
    have e : amdCompact B = (⋂ i,
        {z : Phase (n * 2) | B.distance ≤ planeLength (bodyVector z.1 i)} ∩
        {z | planeLength (bodyVector z.1 i) ≤ B.radius} ∩
        {z | planeLength (bodyVector z.2 i) ≤ B.mass i * Real.sqrt (2 / B.distance)}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
          {z : Phase (n * 2) | B.distance ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)} := by
      ext z
      simp only [amdCompact, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨⟨(h1 i).1, (h1 i).2.1⟩, (h1 i).2.2⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2⟩
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    · have c1 : Continuous fun z : Phase (n * 2) => planeLength (bodyVector z.1 i) :=
        continuous_planeLength_aux.comp ((continuous_bodyVector_aux i).comp continuous_fst)
      have c2 : Continuous fun z : Phase (n * 2) => planeLength (bodyVector z.2 i) :=
        continuous_planeLength_aux.comp ((continuous_bodyVector_aux i).comp continuous_snd)
      exact ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)).inter
        (isClosed_le c2 continuous_const)
    · exact isClosed_le continuous_const (continuous_planeLength_aux.comp
        (((continuous_bodyVector_aux i).comp continuous_fst).sub
          ((continuous_bodyVector_aux j).comp continuous_fst)))
  have hbd : Bornology.IsBounded (amdCompact B) := by
    refine isBounded_iff_forall_norm_le.2 ⟨max B.radius
      (∑ i, B.mass i * Real.sqrt (2 / B.distance)), fun z hz => ?_⟩
    have hcoord : ∀ (w : Fin (n * 2) → ℝ) (C : ℝ), 0 ≤ C →
        (∀ i, planeLength (bodyVector w i) ≤ C) → ‖w‖ ≤ C := by
      intro w C hC h
      refine (pi_norm_le_iff_of_nonneg hC).2 fun a => ?_
      have ha : finProdFinEquiv (finProdFinEquiv.symm a) = a := Equiv.apply_symm_apply _ _
      set p := finProdFinEquiv.symm a
      have hw : w a = bodyVector w p.1 p.2 := by unfold bodyVector; rw [← ha]
      rw [hw]
      exact (norm_le_pi_norm (bodyVector w p.1) p.2).trans
        ((KAM.Kepler.norm_le_planeLength _).trans (h p.1))
    have hterm : ∀ j, 0 ≤ B.mass j * Real.sqrt (2 / B.distance) := fun j =>
      (KAM.Kepler.planeLength_nonneg _).trans (hz.1 j).2.2
    have hS : 0 ≤ ∑ i, B.mass i * Real.sqrt (2 / B.distance) :=
      Finset.sum_nonneg fun j _ => hterm j
    rw [Prod.norm_def]
    refine max_le (le_max_of_le_left ?_) (le_max_of_le_right ?_)
    · exact hcoord _ _ hR.le fun i => (hz.1 i).2.1
    · refine hcoord _ _ hS fun i => ?_
      exact (hz.1 i).2.2.trans (Finset.single_le_sum (f := fun i => B.mass i *
        Real.sqrt (2 / B.distance)) (fun j _ => hterm j) (Finset.mem_univ i))
  exact ⟨Metric.isCompact_of_isClosed_isBounded hcl hbd, fun z hz =>
    ⟨fun i => hd.trans_le (hz.1 i).1, fun i j hij => hd.trans_le (hz.2 i j hij)⟩⟩

end KAM.Planetary

end
