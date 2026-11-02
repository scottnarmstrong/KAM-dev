/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Measure
public import KAM.Wave.Measure.Density

/-!
# W7: the shell estimate (blueprint `bpW:w7:shell-est`)

If on the `k`-th shell the good set `Γ` contains `R_k ∩ (Π_k ∖ ℰ_k)`, with `U_{-α_k} R_k ⊆ Π_k ⊆
(0, t_k)²` and `ℰ_k` the excluded set of an admissible family for `(Π_k, α_k)`, then
`volume (R_k ∖ Γ) / volume R_k ≤ (7 + C₇) α_k^{32/47} / ((1 - q²) t_k)`.
-/

@[expose] public noncomputable section

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KAM.Wave

/-- **Shell estimate** (blueprint `bpW:w7:shell-est`). -/
theorem shell_defect_le (m : ℝ) (hm : 0 < m) {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t0)
    (k : ℕ) {αk : ℝ} {Pk : Set (Fin 2 → ℝ)}
    (hS : MeasSetup m hm Pk αk) (hαt : αk ≤ shellT q t0 k)
    (hinner : shellInner q t0 k αk ⊆ Pk) (hPk : Pk ⊆ boxIoo 0 (shellT q t0 k))
    (F : AdmissibleFamily m hm Pk αk) {Γ : Set (Fin 2 → ℝ)}
    (hΓ : shellSet q t0 k ∩ (Pk \ exclSet m hm F) ⊆ Γ) :
    volume (shellSet q t0 k \ Γ) / volume (shellSet q t0 k) ≤
      ENNReal.ofReal ((7 + measC7 m hm) * αk ^ (32 / 47 : ℝ) / ((1 - q ^ 2) * shellT q t0 k)) := by
  have htk := shellT_pos hq ht k
  have hα := hS.alpha_pos
  have hα1 : αk ≤ 1 := by
    have := hS.alpha_le
    obtain ⟨-, -, hαhat, h27, -, -⟩ := alpha_facts m hm hα this
    linarith
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hsub : shellSet q t0 k \ Γ ⊆ (shellSet q t0 k \ shellInner q t0 k αk) ∪ exclSet m hm F := by
    intro x ⟨hxR, hxΓ⟩
    by_cases hxI : x ∈ shellInner q t0 k αk
    · right
      by_contra hxE
      exact hxΓ (hΓ ⟨hxR, hinner hxI, hxE⟩)
    · left; exact ⟨hxR, hxI⟩
  have h1 := volume_shell_diff_inner_le hq hq1 ht k hα hαt
  have hbdd : Bornology.IsBounded Pk := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1 / 2)).subset fun ξ hξ => ?_
    simpa using hS.sub ξ hξ
  have hdiam : Metric.diam Pk ≤ shellT q t0 k := by
    refine Metric.diam_le_of_forall_dist_le htk.le fun x hx y hy => ?_
    have h1 := hPk hx
    have h2 := hPk hy
    rw [dist_pi_le_iff htk.le]
    intro i
    rw [Real.dist_eq, abs_le]
    have a1 := h1 i (mem_univ i)
    have a2 := h2 i (mem_univ i)
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have h2 := (exclSet_measure_le m hm hS F).2
  have hC7 : 0 ≤ measC7 m hm := by
    unfold measC7 measCP measCI measZ3
    have := measLA_pos m hm
    have := measSigmaX_pos m hm
    have := measTheta_pos m hm
    have := measKstar_pos m hm
    have := measAKappa_pos hm
    have hi := inv_pos.2 (measTheta_pos m hm)
    have hj := inv_pos.2 (measSigmaX_pos m hm)
    positivity
  have hpos : 0 < αk ^ (32 / 47 : ℝ) := Real.rpow_pos_of_pos hα _
  have hαp : αk ≤ αk ^ (32 / 47 : ℝ) := by
    calc αk = αk ^ (1 : ℝ) := (Real.rpow_one αk).symm
      _ ≤ αk ^ (32 / 47 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have hvolR : volume (shellSet q t0 k) = ENNReal.ofReal ((1 - q ^ 2) * shellT q t0 k ^ 2) :=
    volume_shellSet hq hq1 ht k
  rw [hvolR]
  apply ENNReal.div_le_of_le_mul
  calc volume (shellSet q t0 k \ Γ) ≤ volume ((shellSet q t0 k \ shellInner q t0 k αk) ∪
        exclSet m hm F) := measure_mono hsub
    _ ≤ volume (shellSet q t0 k \ shellInner q t0 k αk) + volume (exclSet m hm F) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (7 * αk * shellT q t0 k) +
        ENNReal.ofReal (measC7 m hm * Metric.diam Pk * αk ^ (32 / 47 : ℝ)) := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (7 * αk * shellT q t0 k) +
        ENNReal.ofReal (measC7 m hm * shellT q t0 k * αk ^ (32 / 47 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (7 * αk * shellT q t0 k + measC7 m hm * shellT q t0 k *
          αk ^ (32 / 47 : ℝ)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((7 + measC7 m hm) * αk ^ (32 / 47 : ℝ) / ((1 - q ^ 2) * shellT q t0 k) *
          ((1 - q ^ 2) * shellT q t0 k ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (7 + measC7 m hm) * αk ^ (32 / 47 : ℝ) / ((1 - q ^ 2) * shellT q t0 k) *
            ((1 - q ^ 2) * shellT q t0 k ^ 2) =
            (7 + measC7 m hm) * αk ^ (32 / 47 : ℝ) * shellT q t0 k := by
          have : (1 - q ^ 2) ≠ 0 := (sub_pos.2 hq2).ne'
          field_simp
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_right hαp htk.le]
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]

end KAM.Wave

end
