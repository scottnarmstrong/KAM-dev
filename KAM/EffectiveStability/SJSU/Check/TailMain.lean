/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailCheck
public import KAM.EffectiveStability.SJSU.Initial.Main
public import Mathlib.Tactic.IntervalCases

/-!
# The remainder budget of `h̃` for the SJSU tube (T2-CONF, N9 (C))

For the Taylor remainder `R = hRem sjsuE sjsuN sjsuHwAll sjsuB 9` of N5a's `h̃` and every `(u, φ)`
in the box `|u_j| ≤ 2·10⁻⁶` (`sjsu_hRem_bounds`):

  `|∂_{u_i} R| ≤ sjsuRu i = Σ_{d=1}^{9} W_d TU_{2d,i}`,
  `|∂_{φ_a} R| ≤ sjsuRp = Σ_{d=1}^{9} (Wp_d TT_{2d} + W_d TP_{2d})`.

This is `hRem_bounds_rows` with the short-decimal box, N5c's `β`, the checked slot tables, and the
degree blocks `sjsuHw d` (total exponent `2d`), on which the tail factor is constant
(`block_le`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- `|∂_u R|` budget. -/
def sjsuRu (i : Fin 3) : ℚ :=
  ((List.range 9).map fun k => sjsuW (k + 1) * sjsuTU (2 * (k + 1)) i).sum

/-- `|∂_φ R|` budget. -/
def sjsuRp : ℚ :=
  ((List.range 9).map fun k =>
    sjsuWp (k + 1) * sjsuTT (2 * (k + 1)) + sjsuW (k + 1) * sjsuTP (2 * (k + 1))).sum

theorem sjsu_tail_nonneg : ∀ K < 19, 0 ≤ sjsuTT K ∧ 0 ≤ sjsuTP K ∧ ∀ i : Fin 3, 0 ≤ sjsuTU K i := by
  decide +kernel

/-- Both monomials of a row of `H_w` in degree `d` have degree `d`. -/
theorem sjsuHw_deg {d : ℕ} (h1 : 1 ≤ d) (h9 : d ≤ 9) :
    ∀ e ∈ sjsuHw d, Mon.deg e.1.1 = d ∧ Mon.deg e.1.2 = d := by
  have key : ∀ {A : List Mon} {H : List (List ℤ)} {d : ℕ}, (∀ b ∈ A, Mon.deg b = d) →
      ∀ e ∈ denseRows A H, Mon.deg e.1.1 = d ∧ Mon.deg e.1.2 = d := by
    intro A H d hA e he
    obtain ⟨ha, hb⟩ := mem_denseRows he
    exact ⟨hA _ ha, hA _ hb⟩
  interval_cases d
  · exact key sjsuA1_deg
  · exact key sjsuA2_deg
  · exact key sjsuA3_deg
  · exact key sjsuA4_deg
  · exact key sjsuA5_deg
  · exact key sjsuA6_deg
  · exact key sjsuA7_deg
  · exact key sjsuA8_deg
  · exact key sjsuA9_deg

/-- The rows of `H_w` in degree `d` have total exponent `2d`. -/
theorem sjsuHw_mdeg {d : ℕ} (h1 : 1 ≤ d) (h9 : d ≤ 9) :
    ∀ e ∈ sjsuHw d, mdeg (rowExp e) = 2 * d := by
  intro e he
  obtain ⟨d1, d2⟩ := sjsuHw_deg h1 h9 e he
  simp only [Mon.deg] at d1 d2
  simp only [mdeg, rowExp, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  omega

theorem sjsuHwAll_mem {e : (Mon × Mon) × ℤ} (he : e ∈ sjsuHwAll) :
    ∃ d, 1 ≤ d ∧ d ≤ 9 ∧ e ∈ sjsuHw d := by
  simp only [sjsuHwAll, List.mem_append] at he
  have h0 : sjsuHw 0 = [] := rfl
  rw [h0] at he
  rcases he with (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · simp at h
  all_goals exact ⟨_, by norm_num, by norm_num, h⟩

/-- A sum over all rows as the sum of its degree blocks. -/
theorem sjsuHwAll_sum (F : (Mon × Mon) × ℤ → ℝ) :
    (sjsuHwAll.map F).sum = ((List.range 9).map fun k => ((sjsuHw (k + 1)).map F).sum).sum := by
  have h0 : sjsuHw 0 = [] := rfl
  simp only [sjsuHwAll, h0, List.map_append, List.sum_append, List.map_nil, List.sum_nil,
    zero_add]
  simp [List.range_succ, add_assoc]

/-- On a block of constant total exponent `2d`, a `K`-dependent factor comes out. -/
theorem block_le {l : List ((Mon × Mon) × ℤ)} {d : ℕ}
    (hK : ∀ e ∈ l, mdeg (rowExp e) = 2 * d) (X : ℕ → ℝ) (wt : (Mon × Mon) × ℤ → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) {T W : ℝ} (hX : X (2 * d) ≤ T) (hT : 0 ≤ T)
    (hW : (l.map wt).sum ≤ W) :
    (l.map fun e => wt e * X (mdeg (rowExp e))).sum ≤ W * T := by
  calc (l.map fun e => wt e * X (mdeg (rowExp e))).sum
      ≤ (l.map fun e => wt e * T).sum :=
        list_sum_mono _ _ _ fun e he => by
          rw [hK e he]; exact mul_le_mul_of_nonneg_left hX (hwt e)
    _ = (l.map wt).sum * T := List.sum_map_mul_right _ _ _
    _ ≤ W * T := mul_le_mul_of_nonneg_right hW hT

theorem rowW_cast (e : (Mon × Mon) × ℤ) :
    |rowCoef sjsuE sjsuN e| * ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j =
      ((sjsuRowW e : ℚ) : ℝ) := by
  simp [sjsuRowW, ← rowCoefQ_cast]

theorem rowWp_cast (e : (Mon × Mon) × ℤ) :
    |rowCoef sjsuE sjsuN e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) *
      ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j = ((sjsuRowWp e : ℚ) : ℝ) := by
  simp [sjsuRowWp, ← rowCoefQ_cast]

theorem sjsu_W_ok : ∀ d, 1 ≤ d → d ≤ 9 →
    ((sjsuHw d).map sjsuRowW).sum ≤ sjsuW d ∧ ((sjsuHw d).map sjsuRowWp).sum ≤ sjsuWp d := by
  intro d h1 h9
  have hdeg := sjsuHw_deg h1 h9
  interval_cases d
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok1 sjsu_WpZ_ok1
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok2 sjsu_WpZ_ok2
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok3 sjsu_WpZ_ok3
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok4 sjsu_WpZ_ok4
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok5 sjsu_WpZ_ok5
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok6 sjsu_WpZ_ok6
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok7 sjsu_WpZ_ok7
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok8 sjsu_WpZ_ok8
  · exact sjsu_block_le (by norm_num) hdeg sjsu_WZ_ok9 sjsu_WpZ_ok9

theorem sjsuW_cast_sum {d : ℕ} (F : (Mon × Mon) × ℤ → ℚ) :
    (((sjsuHw d).map F).sum : ℝ) = ((sjsuHw d).map fun e => ((F e : ℚ) : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]; rfl

/-- **The remainder budget of `h̃`** on the SJSU box `|u_j| ≤ 2·10⁻⁶`. -/
theorem sjsu_hRem_bounds (φ : Fin 2 → ℝ) (u : Fin 3 → ℝ) (hu : ∀ j, |u j| ≤ 2 / 1000000) :
    (∀ i, |fderiv ℝ (fun v => hRem sjsuE sjsuN sjsuHwAll sjsuB 9 (v, φ)) u (Pi.single i 1)| ≤
      (sjsuRu i : ℝ)) ∧
    (∀ a, |fderiv ℝ (fun ψ => hRem sjsuE sjsuN sjsuHwAll sjsuB 9 (u, ψ)) φ (Pi.single a 1)| ≤
      (sjsuRp : ℝ)) := by
  have hbox := sjsu_tail_box
  have hR : ((sjsuTailR : ℚ) : ℝ) = 2 / 1000000 := by simp [sjsuTailR]
  have hBd : ∀ j, Differentiable ℝ fun φ => sjsuB φ j := fun j =>
    differentiable_pi.1 differentiable_sjsuB j
  have hβ : ∀ j φ a, |fderiv ℝ (fun φ => sjsuB φ j) φ (Pi.single a 1)| ≤ (sjsuBeta j : ℝ) := by
    intro j φ a
    have h : HasFDerivAt (fun φ => sjsuB φ j)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
          (fderiv ℝ sjsuB φ)) φ := by
      have := (hasFDerivAt_apply (𝕜 := ℝ) j (sjsuB φ)).comp φ (differentiable_sjsuB φ).hasFDerivAt
      exact this
    rw [h.fderiv]
    exact sjsu_hβ φ a j
  have hGT : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < 9 + 2 →
      slotHat ((nj : ℝ) / 2) 9 (sjsuTailBmin j) (sjsuTailBmax j) (sjsuTailR) m ≤
        (sjsuGT K j m : ℝ) := by
    intro K hK nj hnj j m hm
    rw [slotHat_ratCast]
    exact_mod_cast (sjsu_tab_ok K (by omega) nj (by omega) j m (by omega)).1
  have hGTD : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < 9 + 2 →
      slotHatDu ((nj : ℝ) / 2) 9 (sjsuTailBmin j) (sjsuTailBmax j) (sjsuTailR) m ≤
        (sjsuGTD K j m : ℝ) := by
    intro K hK nj hnj j m hm
    rw [slotHatDu_ratCast]
    exact_mod_cast (sjsu_tab_ok K (by omega) nj (by omega) j m (by omega)).2.1
  have hGTP : ∀ K : ℕ, K ≤ 18 → ∀ nj : ℕ, nj ≤ K → ∀ j m, m < 9 + 2 →
      slotHatP ((nj : ℝ) / 2) 9 (sjsuTailBmin j) (sjsuTailBmax j) (sjsuTailR) m ≤
        (sjsuGTP K j m : ℝ) := by
    intro K hK nj hnj j m hm
    rw [slotHatP_ratCast]
    exact_mod_cast (sjsu_tab_ok K (by omega) nj (by omega) j m (by omega)).2.2
  have hdeg : ∀ e ∈ sjsuHwAll, mdeg (rowExp e) ≤ 18 := by
    intro e he
    obtain ⟨d, h1, h9, hd⟩ := sjsuHwAll_mem he
    rw [sjsuHw_mdeg h1 h9 e hd]; omega
  obtain ⟨hU, hP⟩ := hRem_bounds_rows sjsuE sjsuN sjsuHwAll sjsuB 9
    (bmin := fun j => (sjsuTailBmin j : ℝ)) (bmax := fun j => (sjsuTailBmax j : ℝ))
    (β := fun j => (sjsuBeta j : ℝ)) (hi := fun j => (sjsuTailHi j : ℝ)) (r := (sjsuTailR : ℝ))
    (GT := fun K j m => (sjsuGT K j m : ℝ)) (GTD := fun K j m => (sjsuGTD K j m : ℝ))
    (GTP := fun K j m => (sjsuGTP K j m : ℝ)) hBd
    (by rw [hR]; norm_num) (fun j => by exact_mod_cast (hbox j).1)
    (fun j φ => (by exact_mod_cast (hbox j).2.1 : ((sjsuTailBmin j : ℚ) : ℝ) ≤ sjsuBmin j).trans
      (sjsuB_bounds φ j).1)
    (fun j φ => (sjsuB_bounds φ j).2.trans (by exact_mod_cast (hbox j).2.2.1))
    hβ (fun j => ⟨by exact_mod_cast (hbox j).2.2.2.1, by exact_mod_cast (hbox j).2.2.2.2⟩)
    hdeg hGT hGTD hGTP φ u (fun j => by rw [hR]; exact hu j)
  have hwt0 : ∀ e, 0 ≤ |rowCoef sjsuE sjsuN e| * ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j :=
    fun e => mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun j _ => pow_nonneg (by
      exact_mod_cast (hbox j).2.2.2.1) _)
  have hwt0' : ∀ e, 0 ≤ |rowCoef sjsuE sjsuN e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) *
      ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j := fun e => by
    have := hwt0 e
    have h0 : 0 ≤ |((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)| := by positivity
    calc (0 : ℝ) ≤ (|rowCoef sjsuE sjsuN e| * ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j) *
          (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) := mul_nonneg this h0
      _ = _ := by ring
  have hWd : ∀ d, 1 ≤ d → d ≤ 9 → ((sjsuHw d).map fun e =>
      |rowCoef sjsuE sjsuN e| * ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j).sum ≤
        (sjsuW d : ℝ) := by
    intro d h1 h9
    simp only [rowW_cast]
    rw [← sjsuW_cast_sum]
    exact_mod_cast (sjsu_W_ok d h1 h9).1
  have hWpd : ∀ d, 1 ≤ d → d ≤ 9 → ((sjsuHw d).map fun e =>
      |rowCoef sjsuE sjsuN e| * (|((rowMode e).1 : ℝ)| + |((rowMode e).2 : ℝ)|) *
        ∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp e j).sum ≤ (sjsuWp d : ℝ) := by
    intro d h1 h9
    simp only [rowWp_cast]
    rw [← sjsuW_cast_sum]
    exact_mod_cast (sjsu_W_ok d h1 h9).2
  refine ⟨fun i => (hU i).trans ?_, fun a => (hP a).trans ?_⟩
  · rw [sjsuHwAll_sum, sjsuRu, Rat.cast_list_sum, List.map_map]
    refine list_sum_mono _ _ _ fun k hk => ?_
    have hk9 : k < 9 := List.mem_range.1 hk
    simp only [Function.comp_apply, Rat.cast_mul]
    refine block_le (sjsuHw_mdeg (by omega) (by omega))
      (fun K => tailSum (Function.update (fun j m => (sjsuGT K j m : ℝ)) i
        (fun m => (sjsuGTD K i m : ℝ))) 9) _ hwt0 ?_ ?_ (hWd (k + 1) (by omega) (by omega))
    · show tailSum (Function.update (fun j m => (sjsuGT (2 * (k + 1)) j m : ℝ)) i
        (fun m => (sjsuGTD (2 * (k + 1)) i m : ℝ))) 9 ≤ _
      rw [update_ratCast, tailSum_ratCast]
      exact_mod_cast ((sjsu_tail_ok (k + 1) (by omega) (by omega)).2.1 i)
    · exact_mod_cast (sjsu_tail_nonneg (2 * (k + 1)) (by omega)).2.2 i
  · have e : ∀ x : (Mon × Mon) × ℤ,
        |rowCoef sjsuE sjsuN x| * (∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp x j) *
          ((|((rowMode x).1 : ℝ)| + |((rowMode x).2 : ℝ)|) *
            tailSum (fun j m => (sjsuGT (mdeg (rowExp x)) j m : ℝ)) 9 +
          ∑ i, (sjsuBeta i : ℝ) * tailSum (Function.update (fun j m =>
            (sjsuGT (mdeg (rowExp x)) j m : ℝ)) i (fun m => (sjsuGTP (mdeg (rowExp x)) i m : ℝ)))
              9) =
        |rowCoef sjsuE sjsuN x| * (|((rowMode x).1 : ℝ)| + |((rowMode x).2 : ℝ)|) *
            (∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp x j) *
          tailSum (fun j m => (sjsuGT (mdeg (rowExp x)) j m : ℝ)) 9 +
        |rowCoef sjsuE sjsuN x| * (∏ j, ((sjsuTailHi j : ℚ) : ℝ) ^ rowExp x j) *
          ∑ i, (sjsuBeta i : ℝ) * tailSum (Function.update (fun j m =>
            (sjsuGT (mdeg (rowExp x)) j m : ℝ)) i (fun m => (sjsuGTP (mdeg (rowExp x)) i m : ℝ)))
              9 := fun x => by ring
    simp only [e]
    rw [sjsuHwAll_sum, sjsuRp, Rat.cast_list_sum, List.map_map]
    refine list_sum_mono _ _ _ fun k hk => ?_
    have hk9 : k < 9 := List.mem_range.1 hk
    simp only [Function.comp_apply, Rat.cast_add, Rat.cast_mul]
    rw [List.sum_map_add]
    have ht := sjsu_tail_ok (k + 1) (by omega) (by omega)
    have hn := sjsu_tail_nonneg (2 * (k + 1)) (by omega)
    refine add_le_add ?_ ?_
    · refine block_le (sjsuHw_mdeg (by omega) (by omega))
        (fun K => tailSum (fun j m => (sjsuGT K j m : ℝ)) 9) _ hwt0' ?_ ?_
        (hWpd (k + 1) (by omega) (by omega))
      · show tailSum (fun j m => (sjsuGT (2 * (k + 1)) j m : ℝ)) 9 ≤ _
        rw [tailSum_ratCast]; exact_mod_cast ht.1
      · exact_mod_cast hn.1
    · refine block_le (sjsuHw_mdeg (by omega) (by omega))
        (fun K => ∑ i, (sjsuBeta i : ℝ) * tailSum (Function.update (fun j m =>
          (sjsuGT K j m : ℝ)) i (fun m => (sjsuGTP K i m : ℝ))) 9) _ hwt0 ?_ ?_
        (hWd (k + 1) (by omega) (by omega))
      · simp only [update_ratCast, tailSum_ratCast]
        exact_mod_cast ht.2.2
      · exact_mod_cast hn.2.1

end KAM.EffectiveStability.SJSU

end
