/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold.Defs

/-!
# Strong AMD thresholds: attainment, contact, positivity, upper bound

Package LP-THR, `LP:MAIN L4 (141–160)`. Track LP, non-frozen; the statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL.md.

* `pairFeasible_nonempty`, `isCompact_pairFeasible`: the feasible set is nonempty and compact.
* `pairThreshold_isLeast`, `exists_pairThreshold_attained`: the characterization (attained minimum).
* `pairThreshold_le_of_feasible`: the feasibility consumer.
* `exists_contact_minimizer`: the minimum is attained at radial contact (`LP:MAIN L4 (147–150)`).
* `pairThreshold_pos`, `pairThreshold_lt`: positivity and `B_ij < I_j` (14).
-/

public section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

theorem eccDeficit_nonneg {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ eccDeficit u := by
  obtain ⟨h0, h1⟩ := hu
  have : Real.sqrt (1 - u ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  unfold eccDeficit; linarith

theorem eccDeficit_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    eccDeficit x ≤ eccDeficit y := by
  have _ := hy
  unfold eccDeficit
  have : Real.sqrt (1 - y ^ 2) ≤ Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem eccDeficit_eq_zero {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (h : eccDeficit u = 0) :
    u = 0 := by
  obtain ⟨h0, h1⟩ := hu
  unfold eccDeficit at h
  have h2 : Real.sqrt (1 - u ^ 2) = 1 := by linarith
  have h3 : 1 - u ^ 2 = 1 := by
    have := Real.sq_sqrt (show 0 ≤ 1 - u ^ 2 by nlinarith)
    rw [h2] at this; linarith
  nlinarith

theorem eccDeficit_lt_one {u : ℝ} (hu : u < 1) (h0 : 0 ≤ u) : eccDeficit u < 1 := by
  unfold eccDeficit
  have : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  linarith

theorem continuous_eccDeficit : Continuous eccDeficit := by
  unfold eccDeficit; fun_prop

theorem continuous_pairObjective (I : Fin n → ℝ) (i j : Fin n) :
    Continuous (pairObjective I i j) := by
  unfold pairObjective
  have := continuous_eccDeficit
  fun_prop

theorem isCompact_pairFeasible (ν I : Fin n → ℝ) (i j : Fin n) :
    IsCompact (pairFeasible ν I i j) := by
  have hc : IsClosed (pairFeasible ν I i j) := by
    unfold pairFeasible
    refine IsClosed.inter (isClosed_Icc.preimage continuous_fst) (IsClosed.inter
      (isClosed_Icc.preimage continuous_snd)
      (isClosed_le (continuous_const.mul (continuous_const.sub continuous_snd))
        (continuous_const.mul (continuous_const.add continuous_fst))))
  refine IsCompact.of_isClosed_subset
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))) hc ?_
  intro uv h; exact ⟨h.1, h.2.1⟩

theorem pairFeasible_nonempty (ν I : Fin n → ℝ) (i j : Fin n) :
    (pairFeasible ν I i j).Nonempty := by
  refine ⟨(1, 1), ⟨by simp, by simp, ?_⟩⟩
  have : 0 ≤ actionAxis ν I i := sq_nonneg _
  simp only [sub_self, mul_zero]; linarith

/-- Attained minimum (Lemma 4, characterization): `IsLeast` form. -/
theorem pairThreshold_isLeast (ν I : Fin n → ℝ) (i j : Fin n) :
    IsLeast (pairObjective I i j '' pairFeasible ν I i j) (pairThreshold ν I i j) := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_pairFeasible ν I i j).exists_isMinOn
    (pairFeasible_nonempty ν I i j) (continuous_pairObjective I i j).continuousOn
  have hl : IsLeast (pairObjective I i j '' pairFeasible ν I i j) (pairObjective I i j x) :=
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmin hy⟩
  have : pairThreshold ν I i j = pairObjective I i j x := hl.csInf_eq
  rw [this]; exact hl

/-- The characterization of `pairThreshold` as an attained minimum, for every `I`. -/
theorem exists_pairThreshold_attained (ν I : Fin n → ℝ) (i j : Fin n) :
    ∃ uv ∈ pairFeasible ν I i j, pairObjective I i j uv = pairThreshold ν I i j ∧
      ∀ vw ∈ pairFeasible ν I i j, pairThreshold ν I i j ≤ pairObjective I i j vw := by
  obtain ⟨⟨uv, huv, he⟩, hlb⟩ := pairThreshold_isLeast ν I i j
  exact ⟨uv, huv, he, fun vw hvw => hlb ⟨vw, hvw, rfl⟩⟩

/-- Feasibility consumer (for `LP:MAIN L5 (166)`). -/
theorem pairThreshold_le_of_feasible (ν I : Fin n → ℝ) (i j : Fin n) {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (h : actionAxis ν I j * (1 - v) ≤ actionAxis ν I i * (1 + u)) :
    pairThreshold ν I i j ≤ I i * eccDeficit u + I j * eccDeficit v :=
  (pairThreshold_isLeast ν I i j).2 ⟨(u, v), ⟨hu, hv, h⟩, rfl⟩

theorem actionAxis_pos {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν) (i : Fin n) :
    0 < actionAxis ν I i := by
  unfold actionAxis
  exact pow_pos (div_pos (hI.1 i) (hν i)) 2 

/-- Contact reduction (`LP:MAIN L4 (147–150)`): on the chamber the minimum is attained at a
feasible point of radial contact `a_j (1 - v) = a_i (1 + u)`. -/
theorem exists_contact_minimizer {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    {i j : Fin n} (hij : i < j) :
    ∃ uv ∈ pairFeasible ν I i j,
      actionAxis ν I j * (1 - uv.2) = actionAxis ν I i * (1 + uv.1) ∧
      pairObjective I i j uv = pairThreshold ν I i j := by
  obtain ⟨⟨u, v⟩, ⟨hu, hv, hf⟩, he, hmin⟩ := exists_pairThreshold_attained ν I i j
  simp only at hu hv hf he
  have ha := actionAxis_pos hν hI i
  have hab := hI.2 i j hij
  set a := actionAxis ν I i
  set b := actionAxis ν I j
  have hc : 0 < b - a := by linarith
  have hS : b - a ≤ a * u + b * v := by nlinarith
  have hSpos : 0 < a * u + b * v := lt_of_lt_of_le hc hS
  set t := (b - a) / (a * u + b * v) with ht
  have ht0 : 0 < t := div_pos hc hSpos
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hSpos]; exact hS
  have hcontact : a * (t * u) + b * (t * v) = b - a := by
    have : a * (t * u) + b * (t * v) = t * (a * u + b * v) := by ring
    rw [this, ht, div_mul_cancel₀ _ hSpos.ne']
  have htu : t * u ≤ u := by nlinarith [hu.1]
  have htv : t * v ≤ v := by nlinarith [hv.1]
  have hu' : t * u ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hu.1], by linarith [hu.2]⟩
  have hv' : t * v ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hv.1], by linarith [hv.2]⟩
  have hfeas : (t * u, t * v) ∈ pairFeasible ν I i j :=
    ⟨hu', hv', by show b * (1 - t * v) ≤ a * (1 + t * u); nlinarith⟩
  refine ⟨(t * u, t * v), hfeas, by show b * (1 - t * v) = a * (1 + t * u); nlinarith, ?_⟩
  apply le_antisymm
  · have h1 : pairObjective I i j (t * u, t * v) ≤ pairObjective I i j (u, v) := by
      unfold pairObjective
      have := eccDeficit_mono (le_trans (by nlinarith [hu.1] : (0:ℝ) ≤ t * u) le_rfl) htu hu.2
      have h2 := eccDeficit_mono (by nlinarith [hv.1] : (0:ℝ) ≤ t * v) htv hv.2
      have := (hI.1 i).le; have := (hI.1 j).le
      simp only
      nlinarith [mul_le_mul_of_nonneg_left ‹eccDeficit (t*u) ≤ eccDeficit u› (hI.1 i).le,
        mul_le_mul_of_nonneg_left h2 (hI.1 j).le]
    linarith
  · exact hmin _ hfeas

/-- Positivity of `B_ij` on the chamber. -/
theorem pairThreshold_pos {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    {i j : Fin n} (hij : i < j) : 0 < pairThreshold ν I i j := by
  obtain ⟨⟨u, v⟩, ⟨hu, hv, hf⟩, he, -⟩ := exists_pairThreshold_attained ν I i j
  simp only at hu hv hf he
  have ha := actionAxis_pos hν hI i
  have hab := hI.2 i j hij
  have h1 := eccDeficit_nonneg hu
  have h2 := eccDeficit_nonneg hv
  have hi := hI.1 i
  have hj := hI.1 j
  unfold pairObjective at he
  simp only at he
  by_contra hneg
  replace hneg := not_lt.1 hneg
  have hz1 : I i * eccDeficit u = 0 := by nlinarith [mul_nonneg hi.le h1, mul_nonneg hj.le h2]
  have hz2 : I j * eccDeficit v = 0 := by nlinarith [mul_nonneg hi.le h1, mul_nonneg hj.le h2]
  have e1 : eccDeficit u = 0 := (mul_eq_zero.1 hz1).resolve_left hi.ne'
  have e2 : eccDeficit v = 0 := (mul_eq_zero.1 hz2).resolve_left hj.ne'
  have := eccDeficit_eq_zero hu e1
  have := eccDeficit_eq_zero hv e2
  subst_vars
  nlinarith

/-- Strict upper bound `B_ij < I_j` (`LP:MAIN (14)`). -/
theorem pairThreshold_lt {ν I : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hI : I ∈ chamber ν)
    {i j : Fin n} (hij : i < j) : pairThreshold ν I i j < I j := by
  have ha := actionAxis_pos hν hI i
  have hab := hI.2 i j hij
  have hb : 0 < actionAxis ν I j := ha.trans hab
  have hj := hI.1 j
  have hq : actionAxis ν I i / actionAxis ν I j < 1 := (div_lt_one hb).2 hab
  have hq0 : 0 < actionAxis ν I i / actionAxis ν I j := div_pos ha hb
  have hfe := pairThreshold_le_of_feasible ν I i j (u := 0)
    (v := 1 - actionAxis ν I i / actionAxis ν I j)
    ⟨le_rfl, zero_le_one⟩ ⟨by linarith, by linarith⟩
    (by
      have : actionAxis ν I j * (1 - (1 - actionAxis ν I i / actionAxis ν I j))
          = actionAxis ν I i := by field_simp; ring
      rw [this]; linarith)
  have hD : eccDeficit (1 - actionAxis ν I i / actionAxis ν I j) < 1 :=
    eccDeficit_lt_one (by linarith) (by linarith)
  have h0 : eccDeficit 0 = 0 := by simp [eccDeficit]
  rw [h0, mul_zero, zero_add] at hfe
  nlinarith

end KAM.Planetary.StrongAMD
