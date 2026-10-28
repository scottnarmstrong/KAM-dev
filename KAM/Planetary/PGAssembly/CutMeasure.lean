/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 5: coordinate cuts of a finite measure (`bpP:p5:st-ivt`, helper)

`finite_measure_coordinate_cut`: for a finite measure `nu` on `Fin N → ℝ` giving no mass to any
coordinate slice `{x | x j = s}`, the cut mass `s ↦ nu {x | x j ≤ s}` is continuous.

Proof: right continuity from `tendsto_measure_biInter_gt`; left continuity from continuity from
below along `a - 1/(n+1)`, the union being `{x j < a}`, which differs from `{x j ≤ a}` by a slice;
monotonicity upgrades the sequential limit to the one-sided limit.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CUT.
-/

public section

open MeasureTheory Set Filter Topology

namespace KAM.Planetary.PGAssembly.CutMeasure

variable {N : ℕ} (j : Fin N) (nu : Measure (Fin N → ℝ))

lemma cut_measurableSet (s : ℝ) : MeasurableSet {x : Fin N → ℝ | x j ≤ s} :=
  measurableSet_le (measurable_pi_apply j) measurable_const

lemma cut_tendsto_right [IsFiniteMeasure nu] (a : ℝ) :
    Tendsto (fun s : ℝ => nu {x | x j ≤ s}) (𝓝[>] a) (𝓝 (nu {x | x j ≤ a})) := by
  have h := tendsto_measure_biInter_gt (μ := nu) (a := a)
    (s := fun r : ℝ => {x : Fin N → ℝ | x j ≤ r})
    (fun r _ => (cut_measurableSet j r).nullMeasurableSet)
    (fun i k _ hik => fun x hx => le_trans hx hik) ⟨a + 1, by linarith, measure_ne_top _ _⟩
  have hI : (⋂ r > a, {x : Fin N → ℝ | x j ≤ r}) = {x | x j ≤ a} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h r hr => h.trans hr.le⟩
    exact le_of_forall_gt_imp_ge_of_dense fun r hr => h r hr
  rw [hI] at h
  exact h

lemma cut_tendsto_left [IsFiniteMeasure nu]
    (hnull : ∀ s : ℝ, nu {x | x j = s} = 0) (a : ℝ) :
    Tendsto (fun s : ℝ => nu {x | x j ≤ s}) (𝓝[<] a) (𝓝 (nu {x | x j ≤ a})) := by
  set F : ℝ → ENNReal := fun s => nu {x | x j ≤ s} with hF
  have hmono : Monotone F := fun s t hst => measure_mono fun x hx => le_trans hx hst
  have hseq : Tendsto (fun n : ℕ => F (a - 1 / ((n : ℝ) + 1))) atTop (𝓝 (F a)) := by
    have h := tendsto_measure_iUnion_atTop (μ := nu)
      (s := fun n : ℕ => {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)})
      (fun m n hmn x (hx : x j ≤ a - 1 / ((m : ℝ) + 1)) => by
        show x j ≤ a - 1 / ((n : ℝ) + 1)
        refine le_trans hx ?_
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (by omega : m + 1 ≤ n + 1)
        linarith)
    have hU : nu (⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)}) = F a := by
      have hsub : (⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)}) ⊆ {x | x j ≤ a} := by
        intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.1 hx
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq] at hn ⊢
        linarith
      refine le_antisymm (measure_mono hsub) ?_
      have hcov : {x : Fin N → ℝ | x j ≤ a} ⊆
          (⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)}) ∪ {x | x j = a} := by
        intro x hx
        rcases lt_or_eq_of_le (show x j ≤ a from hx) with hlt | heq
        · left
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          exact mem_iUnion.2 ⟨n, by simp only [mem_ofPred_eq]; linarith⟩
        · right; exact heq
      calc F a ≤ nu ((⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)}) ∪ {x | x j = a}) :=
            measure_mono hcov
        _ ≤ nu (⋃ n : ℕ, {x : Fin N → ℝ | x j ≤ a - 1 / ((n : ℝ) + 1)}) + nu {x | x j = a} :=
            measure_union_le _ _
        _ = _ := by rw [hnull a, add_zero]
    rw [hU] at h
    exact h
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨n, hn⟩ := (hseq.eventually (lt_mem_nhds hb)).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsLT (show a - 1 / ((n : ℝ) + 1) < a by linarith)] with s hs
    exact lt_of_lt_of_le hn (hmono hs.1.le)
  · exact eventually_of_mem self_mem_nhdsWithin fun s hs => lt_of_le_of_lt (hmono (le_of_lt hs)) hb

end KAM.Planetary.PGAssembly.CutMeasure

open MeasureTheory in
/-- Real target dimension and finite measure; continuity uses atomless coordinate slices. -/
theorem finite_measure_coordinate_cut {N : ℕ} (j : Fin N) (nu : Measure (Fin N → ℝ))
    [IsFiniteMeasure nu] (hnull : ∀ s : ℝ, nu {x | x j=s} = 0) :
    Continuous (fun s : ℝ => (nu {x | x j ≤ s}).toReal) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have hlr : Tendsto (fun s : ℝ => nu {x | x j ≤ s}) (𝓝 a) (𝓝 (nu {x | x j ≤ a})) := by
    have hR : ContinuousWithinAt (fun s : ℝ => nu {x | x j ≤ s}) (Ici a) a :=
      continuousWithinAt_Ioi_iff_Ici.1
        (KAM.Planetary.PGAssembly.CutMeasure.cut_tendsto_right j nu a)
    rw [← nhdsLT_sup_nhdsGE a]
    exact (KAM.Planetary.PGAssembly.CutMeasure.cut_tendsto_left j nu hnull a).sup hR
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hlr
