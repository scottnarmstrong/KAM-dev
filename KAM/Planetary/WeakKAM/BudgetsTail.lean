/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Budgets

/-! # P11B weak-KAM budgets: the literal tail estimate (E3)

`exported_sums_es_3` is the graph step `stepP:p11a:es-3` of `bpP:p11a:exported-sums`: the tails
against the collars,
`t_{ν+1}⁻¹ ∑_{j≥ν} (A_{1,j} + A_{η,j}) ≤ 3 Q₀ Ξ / C_Q + Q₀ Ξ / 16 ≤ 2⁻¹⁰` and
`∑_{j≥ν} Λ_{ℝ,j} ≤ 2⁻¹²`. Append-only gap fill to `Budgets.lean` (which proves only the final
`≤ 2⁻¹⁰` of the first display).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Main
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
include c

/-- The tail quotient is dominated by `32/31` times the two geometric constants. -/
theorem wbudtail_quot (ν : ℕ) :
    (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1) ≤
      32 / 31 * ((2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) *
        (2 : ℝ) ^ (a.τ + 1) / a.t₀ + (selectionQ₀ a * a.s₀ / 32) * (2 : ℝ) ^ (a.τ + 1) / a.t₀) := by
  have h := c.hyp
  obtain ⟨hsu, -⟩ := wbud_lip c
  obtain ⟨hsA, hsα, -, -⟩ := wbud_sums_Aα c
  have hAα : Summable (fun j => selectionA a (j + ν) + selectionAlpha a (j + ν)) :=
    ((summable_nat_add_iff ν).2 hsA).add ((summable_nat_add_iff ν).2 hsα)
  have hsh := (summable_nat_add_iff ν).2 hsu
  have hnn : ∀ j, 0 ≤ selectionA a j + selectionAlpha a j := fun j => by
    obtain ⟨-, hA0, -, -, -, hα, -⟩ := wbud_stage h j
    have := wbud_s_pos h j
    have := (wbud_stage h j).2.2.2.1
    rw [hα]; positivity
  have hmono : ∀ j, selectiont a (j + ν + 1) ≤ selectiont a (ν + 1) := fun j => by
    rw [selectiont_eq, selectiont_eq]
    have hw : (2 : ℝ) ≤ (2 : ℝ) ^ (a.τ + 1) := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 : ℝ) ≤ a.τ + 1 by linarith [h.hτ])
      simpa using this
    have h1 : ((2 : ℝ) ^ (a.τ + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) h1 ?_) h.ht.le
    omega
  obtain ⟨hsg, hg⟩ := wbud_tsum_le_zero (fun j => (wbud_lip_term c j).1)
    (fun j => (wbud_lip_term c j).2)
  rw [← tsum_div_const]
  calc ∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν)) / selectiont a (ν + 1)
      ≤ ∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν)) /
          selectiont a (j + ν + 1) :=
        Summable.tsum_le_tsum (fun j => div_le_div_of_nonneg_left (hnn _)
          (wbud_t_pos c _) (hmono j)) (hAα.div_const _) hsh
    _ ≤ ∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) :=
        wbud_tsum_shift_le (fun j => div_nonneg (hnn j) (wbud_t_pos c _).le) hsu ν
    _ ≤ _ := hg

/-- `(E3)` (`stepP:p11a:es-3`) for a schedule with budget context. -/
theorem exported_sums_es_3_ctx (ν : ℕ) :
    (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1) ≤
      3 * selectionQ₀ a * selectionXi d / selectionCQ n + selectionQ₀ a * selectionXi d / 16 ∧
    3 * selectionQ₀ a * selectionXi d / selectionCQ n + selectionQ₀ a * selectionXi d / 16 ≤
      (2 : ℝ)⁻¹ ^ 10 ∧
    ∑' j, selectionRealBudget a (j + ν) ≤ (2 : ℝ)⁻¹ ^ 12 := by
  have h := c.hyp
  have hQ0 := wbud_Q₀_nonneg c
  obtain ⟨-, hX2, hX3, -⟩ := wbud_Xi_le c
  have hW := c.adm.weighted
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  have ht := h.ht
  have hs0 := h.hs
  have hst : a.s₀ ≤ a.t₀ := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    refine c.adm.radius.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h.ht]
  have hw0 : 0 < (2 : ℝ) ^ (a.τ + 1) := by positivity
  have hP : selectionQ₀ a * selectionXi d ≤ (2 : ℝ)⁻¹ ^ 10 := hW
  have hP0 : 0 ≤ selectionQ₀ a * selectionXi d := by
    have : 0 ≤ selectionXi d := le_trans (by positivity) hX3
    positivity
  have hA : (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * (2 : ℝ) ^ (a.τ + 1) / a.t₀ ≤
      2 * selectionQ₀ a * selectionXi d / selectionCQ n := by
    have e : (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * (2 : ℝ) ^ (a.τ + 1) / a.t₀ =
        2 * (selectionQ₀ a * ((2 : ℝ) ^ (a.τ + 1) * (a.strip / 24) / a.t₀)) / selectionCQ n := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hCQ0.le
    have := mul_le_mul_of_nonneg_left hX2 hQ0
    linarith
  have hB : (selectionQ₀ a * a.s₀ / 32) * (2 : ℝ) ^ (a.τ + 1) / a.t₀ ≤
      selectionQ₀ a * selectionXi d / 32 := by
    have e : (selectionQ₀ a * a.s₀ / 32) * (2 : ℝ) ^ (a.τ + 1) / a.t₀ =
        (selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1) / 32) * (a.s₀ / a.t₀) := by
      field_simp
    rw [e]
    have h1 : a.s₀ / a.t₀ ≤ 1 := (div_le_one ht).2 hst
    have h2 : selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1) ≤ selectionQ₀ a * selectionXi d :=
      mul_le_mul_of_nonneg_left hX3 hQ0
    have h3 : 0 ≤ selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1) / 32 := by positivity
    calc selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1) / 32 * (a.s₀ / a.t₀)
        ≤ selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1) / 32 * 1 := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ _ := by linarith
  have hE : 2 * selectionQ₀ a * selectionXi d / selectionCQ n =
      2 * (selectionQ₀ a * selectionXi d / selectionCQ n) := by ring
  have hE3 : 3 * selectionQ₀ a * selectionXi d / selectionCQ n =
      3 * (selectionQ₀ a * selectionXi d / selectionCQ n) := by ring
  have hF0 : 0 ≤ selectionQ₀ a * selectionXi d / selectionCQ n := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (wbudtail_quot c ν).trans ?_
    rw [hE3]
    rw [hE] at hA
    linarith
  · have h1 : selectionQ₀ a * selectionXi d / selectionCQ n ≤
        selectionQ₀ a * selectionXi d / 162 :=
      div_le_div_of_nonneg_left hP0 (by norm_num) hCQ
    rw [hE3]
    have : (2 : ℝ)⁻¹ ^ 10 = 1 / 1024 := by norm_num
    rw [this] at hP ⊢
    linarith
  · have hg := wbud_geo c
    have hh := wbud_nums c
    obtain ⟨hsR, hR⟩ := wbud_tsum_le_zero (fun j => (wbud_stage h j).2.2.2.2.2.2.1)
      (fun j => (hg j).2.2.2)
    exact (wbud_tsum_shift_le (fun j => (wbud_stage h j).2.2.2.2.2.2.1) hsR ν).trans
      (hR.trans hh.2.1)

end Main

/-- `stepP:p11a:es-3`, the tails against the collars (E3), for the selected schedule. -/
theorem exported_sums_es_3 (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := adm_params d ε
    ∀ ν, (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1) ≤
        3 * selectionQ₀ a * selectionXi d / selectionCQ n + selectionQ₀ a * selectionXi d / 16 ∧
      3 * selectionQ₀ a * selectionXi d / selectionCQ n + selectionQ₀ a * selectionXi d / 16 ≤
        (2 : ℝ)⁻¹ ^ 10 ∧
      ∑' j, selectionRealBudget a (j + ν) ≤ (2 : ℝ)⁻¹ ^ 12 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hL := selectionLambdaMax_pos d
  have hs : 0 < (adm_params d ε).s₀ := by
    show 0 < selectionLambdaMax d / (n * d.C₁)
    positivity
  have he' : 0 < (adm_params d ε).ε₀ := by
    show 0 < ε + n / 2 * d.C₁ * (selectionLambdaMax d / (n * d.C₁)) ^ 2
    positivity
  intro a ν
  exact exported_sums_es_3_ctx (weakBudgetCtx_of d (adm_params d ε)
    (adm_choice d ε he hsmall).2.1 rfl rfl rfl rfl rfl rfl hs he') ν

end KAM.Planetary
