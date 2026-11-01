/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Pair

/-!
# Strong AMD thresholds: the contact parameterization and continuity

Package LP-THR, `LP:MAIN L4 (141–160)`, parameterization (15) and continuity. Track LP, non-frozen;
the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`contactObjective` is the objective along the fixed-interval contact parameterization (15);
`pairThreshold_eq_sInf_contact` identifies `B_ij` with its infimum over `t ∈ [0,1]`, and
`continuousOn_pairThreshold` proves continuity on the chamber (jointly continuous integrand over a
compact interval, `IsCompact.continuous_sInf`). `isOpen_chamber` is also proved.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- `m(α) = min 1 ((1-α)/α)` of (15). -/
def contactScale (α : ℝ) : ℝ := min 1 ((1 - α) / α)

/-- The contact point `(m t, 1 - α - α m t)` of (15), with `α = a_i / a_j`. -/
def contactPoint (ν I : Fin n → ℝ) (i j : Fin n) (t : ℝ) : ℝ × ℝ :=
  let α := actionAxis ν I i / actionAxis ν I j
  (contactScale α * t, 1 - α - α * contactScale α * t)

/-- The objective along the contact parameterization (15). -/
def contactObjective (ν I : Fin n → ℝ) (i j : Fin n) (t : ℝ) : ℝ :=
  pairObjective I i j (contactPoint ν I i j t)

theorem continuous_actionAxis (ν : Fin n → ℝ) (i : Fin n) :
    Continuous fun I : Fin n → ℝ => actionAxis ν I i := by
  unfold actionAxis
  have : Continuous fun I : Fin n → ℝ => I i := continuous_apply i
  fun_prop

theorem isOpen_chamber (ν : Fin n → ℝ) : IsOpen (chamber ν) := by
  have h : chamber ν = (⋂ i, {I : Fin n → ℝ | 0 < I i}) ∩
      ⋂ i, ⋂ j, ⋂ (_ : i < j), {I : Fin n → ℝ | actionAxis ν I i < actionAxis ν I j} := by
    ext I; simp [chamber, Set.mem_iInter]
  rw [h]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    (continuous_apply i)) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_actionAxis ν i)
        (continuous_actionAxis ν j))

theorem contactScale_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 0 < contactScale α :=
  lt_min one_pos (div_pos (by linarith) h0)

theorem contactScale_le_one (α : ℝ) : contactScale α ≤ 1 := min_le_left _ _

theorem mul_contactScale_le {α : ℝ} (h0 : 0 < α) : α * contactScale α ≤ 1 - α := by
  have := min_le_right 1 ((1 - α) / α)
  calc α * contactScale α ≤ α * ((1 - α) / α) := by
        exact mul_le_mul_of_nonneg_left this h0.le
    _ = 1 - α := by field_simp

/-- Positivity data for `α = a_i / a_j` on the chamber. -/
theorem alpha_bounds {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    {i j : Fin n} (hij : i < j) :
    0 < actionAxis ν I i / actionAxis ν I j ∧ actionAxis ν I i / actionAxis ν I j < 1 ∧
      actionAxis ν I i = actionAxis ν I j * (actionAxis ν I i / actionAxis ν I j) := by
  have ha := actionAxis_pos hν hI i
  have hab := hI.2 i j hij
  have hb : 0 < actionAxis ν I j := ha.trans hab
  exact ⟨div_pos ha hb, (div_lt_one hb).2 hab, by field_simp⟩

theorem contactPoint_mem {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    {i j : Fin n} (hij : i < j) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    contactPoint ν I i j t ∈ pairFeasible ν I i j ∧
      actionAxis ν I j * (1 - (contactPoint ν I i j t).2) =
        actionAxis ν I i * (1 + (contactPoint ν I i j t).1) := by
  obtain ⟨hq0, hq, hab⟩ := alpha_bounds hν hI hij
  set α := actionAxis ν I i / actionAxis ν I j with hα
  have hm := contactScale_pos hq0 hq
  have hm1 := contactScale_le_one α
  have hmα := mul_contactScale_le hq0
  have hp : contactPoint ν I i j t =
      (contactScale α * t, 1 - α - α * contactScale α * t) := rfl
  rw [hp]
  obtain ⟨ht0, ht1⟩ := ht
  have hmt : 0 ≤ contactScale α * t := mul_nonneg hm.le ht0
  have hmt1 : contactScale α * t ≤ 1 := by nlinarith
  have hamt : α * contactScale α * t ≤ α * contactScale α := by
    have : 0 ≤ α * contactScale α := by positivity
    nlinarith
  have hamt0 : 0 ≤ α * contactScale α * t := by positivity
  have heq : actionAxis ν I j * (1 - (1 - α - α * contactScale α * t)) =
      actionAxis ν I i * (1 + contactScale α * t) := by
    rw [hab]; ring
  refine ⟨⟨⟨hmt, hmt1⟩, ⟨by simp only; linarith, by simp only; linarith⟩, heq.le⟩, heq⟩

/-- The infimum of the contact parameterization (15) is attained and equals `B_ij`:
`IsLeast` form (`LP:MAIN L4 (147–153)`). -/
theorem pairThreshold_isLeast_contact {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    (hI : I ∈ chamber ν) {i j : Fin n} (hij : i < j) :
    IsLeast (contactObjective ν I i j '' Set.Icc (0 : ℝ) 1) (pairThreshold ν I i j) := by
  obtain ⟨hq0, hq, hab⟩ := alpha_bounds hν hI hij
  set α := actionAxis ν I i / actionAxis ν I j with hα
  have hb : 0 < actionAxis ν I j := (actionAxis_pos hν hI i).trans (hI.2 i j hij)
  have hm := contactScale_pos hq0 hq
  constructor
  · obtain ⟨⟨u, v⟩, ⟨hu, hv, -⟩, hc, he⟩ := exists_contact_minimizer hν hI hij
    simp only at hu hv hc he
    have hv' : v = 1 - α - α * u := by
      have : actionAxis ν I j * (1 - v) = actionAxis ν I j * (α * (1 + u)) := by
        rw [hc]; nth_rewrite 1 [hab]; ring
      have := mul_left_cancel₀ hb.ne' this
      linarith
    have hum : u ≤ contactScale α := by
      refine le_min hu.2 ?_
      rw [le_div_iff₀ hq0]; nlinarith [hv.1]
    refine ⟨u / contactScale α, ⟨div_nonneg hu.1 hm.le, (div_le_one hm).2 hum⟩, ?_⟩
    have hpt : contactPoint ν I i j (u / contactScale α) = (u, v) := by
      show (contactScale α * (u / contactScale α),
        1 - α - α * contactScale α * (u / contactScale α)) = (u, v)
      have h1 : contactScale α * (u / contactScale α) = u := mul_div_cancel₀ _ hm.ne'
      rw [mul_assoc, h1, hv']
    unfold contactObjective
    rw [hpt]; exact he
  · rintro _ ⟨t, ht, rfl⟩
    exact (pairThreshold_isLeast ν I i j).2 ⟨_, (contactPoint_mem hν hI hij ht).1, rfl⟩

/-- Parameterization (15): `B_ij = inf_{t ∈ [0,1]} F(I,t)`. -/
theorem pairThreshold_eq_sInf_contact {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    (hI : I ∈ chamber ν) {i j : Fin n} (hij : i < j) :
    pairThreshold ν I i j = sInf (contactObjective ν I i j '' Set.Icc (0 : ℝ) 1) :=
  (pairThreshold_isLeast_contact hν hI hij).csInf_eq.symm

/-- Joint continuity of the contact objective in `(I, t)` on the chamber. -/
theorem continuous_contactObjective {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {i j : Fin n}
    (hij : i < j) :
    Continuous (fun p : chamber ν × ℝ => contactObjective ν p.1.1 i j p.2) := by
  have hca : ∀ k : Fin n, Continuous fun p : chamber ν × ℝ => actionAxis ν p.1.1 k := by
    intro k; unfold actionAxis
    have : Continuous fun p : chamber ν × ℝ => p.1.1 k :=
      (continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)
    fun_prop
  have hne : ∀ p : chamber ν × ℝ, actionAxis ν p.1.1 j ≠ 0 := fun p =>
    (actionAxis_pos hν p.1.2 j).ne'
  have hα : Continuous fun p : chamber ν × ℝ => actionAxis ν p.1.1 i / actionAxis ν p.1.1 j :=
    (hca i).div (hca j) hne
  have hαne : ∀ p : chamber ν × ℝ, actionAxis ν p.1.1 i / actionAxis ν p.1.1 j ≠ 0 :=
    fun p => (alpha_bounds hν p.1.2 hij).1.ne'
  have hm : Continuous fun p : chamber ν × ℝ =>
      contactScale (actionAxis ν p.1.1 i / actionAxis ν p.1.1 j) := by
    unfold contactScale
    exact continuous_const.min ((continuous_const.sub hα).div hα hαne)
  have hI' : ∀ k : Fin n, Continuous fun p : chamber ν × ℝ => p.1.1 k := fun k =>
    (continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)
  unfold contactObjective pairObjective contactPoint
  have hD := continuous_eccDeficit
  simp only
  fun_prop

/-- Continuity of `B_ij` on the chamber (`LP:MAIN L4 (151–153)`). -/
theorem continuousOn_pairThreshold {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {i j : Fin n}
    (hij : i < j) : ContinuousOn (fun I => pairThreshold ν I i j) (chamber ν) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (chamber ν).domRestrict (fun I => pairThreshold ν I i j) =
      fun x : chamber ν => sInf (contactObjective ν x.1 i j '' Set.Icc (0 : ℝ) 1) := by
    funext x; exact pairThreshold_eq_sInf_contact hν x.2 hij
  rw [this]
  exact isCompact_Icc.continuous_sInf
    (f := fun (x : chamber ν) (t : ℝ) => contactObjective ν x.1 i j t)
    (continuous_contactObjective hν hij)

end KAM.Planetary.StrongAMD
