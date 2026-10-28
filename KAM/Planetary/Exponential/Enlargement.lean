/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Planetary.Exponential.Setting

/-!
# P14 package E2: the enlarged data

Blueprint P, Part 14 (`bpP:p14:enlarge`): for an admissible box there are `κ > 0`,
`e ∈ (e_*, 1)` and `A > A₁` satisfying the source inequalities (E1)–(E3).  Proof: all inequalities
are strict at the limit point `(κ, e, A) = (0, e_*, A₁)` (`stepP:p14:en-lim`);
we follow the path `t ↦ (t, e_* + t, A₁ + t)` as `t → 0⁺` and use continuity to pick `t`
(`stepP:p14:en-choice`).  The positivity of the slow erosion `ε_D` is `A⁺ > A₁`,
i.e. the field `amd_lt`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Planetary

variable {n : ℕ}

theorem enlarge (B : AMDBox n) (hB : B.Admissible) :
    ∃ kappa e A, EnlargedData B kappa e A := by
  obtain ⟨hi, he0, he1, hA0, hA1, hdef, hd, hr, hrad, hgap⟩ := hB
  -- all eventually-statements are along `t → 0⁺`
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hnhds : ∀ {P : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), P t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), P t :=
    fun h => nhdsWithin_le_nhds h
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), B.ecc + t < 1 :=
    hnhds ((continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const
      (by simpa using he1))
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, t ≤ B.lower i / 8 := by
    refine hnhds (Filter.eventually_all.2 fun i => ?_)
    have := (hi i).2.1
    exact (continuousAt_id.eventually_lt (continuousAt_const (y := B.lower i / 8))
      (by simp only [id]; linarith)).mono fun t ht => ht.le
  have hdeficit : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, B.outerAMD + t <
      (B.lower i - 2 * t) * (1 - Real.sqrt (1 - (B.ecc + t) ^ 2)) := by
    refine hnhds (Filter.eventually_all.2 fun i => ?_)
    refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) ?_
    simpa using hdef i
  have hradii : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, B.distance / 2 ≤
      ((B.lower i - 2 * t) / B.mass i) ^ 2 * (1 - (B.ecc + t)) := by
    refine hnhds (Filter.eventually_all.2 fun i => ?_)
    have hm := (hi i).1
    refine (ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) ?_).mono fun t ht => ht.le
    have := (hrad i).1
    simp only [mul_zero, sub_zero]
    linarith
  have hgaps : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, i < j →
      ((B.upper i + 2 * t) / B.mass i) ^ 2 * (1 + (B.ecc + t)) + B.distance / 2 ≤
      ((B.lower j - 2 * t) / B.mass j) ^ 2 * (1 - (B.ecc + t)) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : i < j
    · have hmi := (hi i).1
      have hmj := (hi j).1
      refine hnhds ((ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) ?_).mono
        fun t ht _ => ht.le)
      have := hgap i j hij
      simp only [mul_zero, add_zero, sub_zero]
      linarith
    · exact Filter.Eventually.of_forall fun t h => absurd h hij
  obtain ⟨t, ht0, ht1, ht2, ht3, ht4, ht5⟩ :=
    (hpos.and (h1.and (hsmall.and (hdeficit.and (hradii.and hgaps))))).exists
  exact ⟨t, B.ecc + t, B.outerAMD + t,
    { kappa_pos := ht0
      ecc_lt := by linarith
      ecc_one := ht1
      amd_lt := by linarith
      small := ht2
      deficit := ht3
      radii := ht4
      gaps := ht5 }⟩

end KAM.Planetary
