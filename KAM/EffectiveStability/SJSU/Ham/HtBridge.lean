/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Hw
public import KAM.EffectiveStability.SJSU.Ham.Center
public import KAM.EffectiveStability.Tube.Poly.HtBridge

/-!
# The SJSU data of the Horner bridge (T2-CONF, N5a-2)

The facts about the SJSU tube data that N7's Horner stage needs, independent of N7's ledger:
* `sjsuB_pos`: `B_j > 0` (kernel: `Ī_j - Σ |m_j σ| > 0`);
* `sjsuB_eq_denseCos`: `B_j = denseCos 30 (scatter 61² 0 (bPairs 30 …))` (kernel: the modes lie in
  the box and the pairs are strictly sorted);
* `sjsuTTerms_box`: every mode of `H_w` lies in the box `|k| ≤ 9`;
* `sjsuTn_eq_denseCos`: `T_n = denseCos 9 (pDense 9 (tTerms … n))`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- `Ī_j - Σ |m_j σ| > 0` for each `j` (kernel; the sum is balanced, `treeSumG`, so that the kernel
does not nest one frame per mode). -/
theorem sjsuB_margin_tree : ∀ j : Fin 3,
    0 < sjsuEccIbar j -
      treeSumG 64 (sjsuEccModes.map fun x => |((modeK x.1 x.2.1 j : ℤ) : ℚ) * x.2.2|) := by
  decide +kernel

theorem sjsuB_margin (j : Fin 3) :
    0 < sjsuEccIbar j -
      (sjsuEccModes.map fun x => |((modeK x.1 x.2.1 j : ℤ) : ℚ) * x.2.2|).sum := by
  rw [← treeSumG_eq 64]
  exact sjsuB_margin_tree j

/-- **`B_j > 0`.** -/
theorem sjsuB_pos (φ : Fin 2 → ℝ) (j : Fin 3) : 0 < sjsuB φ j := by
  have h := tubeCenter_ge sjsuEccModes sjsuEccIbar j φ
  have hm : (0 : ℝ) < ((sjsuEccIbar j - (sjsuEccModes.map fun x =>
      |((modeK x.1 x.2.1 j : ℤ) : ℚ) * x.2.2|).sum : ℚ) : ℝ) := by
    exact_mod_cast sjsuB_margin j
  exact lt_of_lt_of_le hm h

/-- The modes of `S` lie in the box `|k| ≤ 30` (kernel). -/
theorem sjsuEccModes_box : sjsuEccModes.all (fun x => inBox 30 (x.1, x.2.1)) = true := by
  decide +kernel

/-- The pairs of each `B_j` are strictly sorted (kernel). -/
theorem sjsuBPairs_inc : ∀ j : Fin 3, incFrom 0 (bPairs 30 sjsuEccModes sjsuEccIbar j) = true := by
  decide +kernel

/-- **`B_j` as N7's dense cosine series.** -/
theorem sjsuB_eq_denseCos (j : Fin 3) :
    (fun φ => sjsuB φ j) =
      denseCos 30
        (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar j)) := by
  funext φ
  exact tubeCenter_eq_denseCos 30 sjsuEccModes sjsuEccIbar j
    (fun x hx => List.all_eq_true.1 sjsuEccModes_box x hx) (sjsuBPairs_inc j) φ

/-- The exponents of every row of `H_w` are at most `9` in each mode. -/
theorem sjsuHwAll_le {e : (Mon × Mon) × ℤ} (he : e ∈ sjsuHwAll) :
    e.1.1.1 ≤ 9 ∧ e.1.1.2.1 ≤ 9 ∧ e.1.1.2.2 ≤ 9 ∧ e.1.2.1 ≤ 9 ∧ e.1.2.2.1 ≤ 9 ∧ e.1.2.2.2 ≤ 9 := by
  have key : ∀ {A : List Mon} {H : List (List ℤ)} {d : ℕ}, d ≤ 9 → (∀ b ∈ A, Mon.deg b = d) →
      e ∈ denseRows A H →
      e.1.1.1 ≤ 9 ∧ e.1.1.2.1 ≤ 9 ∧ e.1.1.2.2 ≤ 9 ∧ e.1.2.1 ≤ 9 ∧ e.1.2.2.1 ≤ 9 ∧
        e.1.2.2.2 ≤ 9 := by
    intro A H d hd hA h
    obtain ⟨h1, h2⟩ := mem_denseRows h
    have d1 := hA _ h1
    have d2 := hA _ h2
    simp only [Mon.deg] at d1 d2
    omega
  simp only [sjsuHwAll, sjsuHw, List.mem_append, List.not_mem_nil, false_or] at he
  rcases he with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact key (by norm_num) sjsuA1_deg h
  · exact key (by norm_num) sjsuA2_deg h
  · exact key (by norm_num) sjsuA3_deg h
  · exact key (by norm_num) sjsuA4_deg h
  · exact key (by norm_num) sjsuA5_deg h
  · exact key (by norm_num) sjsuA6_deg h
  · exact key (by norm_num) sjsuA7_deg h
  · exact key (by norm_num) sjsuA8_deg h
  · exact key (by norm_num) sjsuA9_deg h

/-- Every mode of `H_w` lies in the box `|k| ≤ 9`. -/
theorem sjsuTTerms_box (n : ℕ × ℕ × ℕ) :
    ∀ t ∈ tTerms sjsuE sjsuN sjsuHwAll n, inBox 9 t.1 = true := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
  have h := sjsuHwAll_le (List.mem_filter.1 he).1
  simp only [inBox, rowMode, Bool.and_eq_true, decide_eq_true_eq, abs_le]
  omega

/-- **`T_n` as N7's dense cosine series.** -/
theorem sjsuTn_eq_denseCos (n : ℕ × ℕ × ℕ) :
    Tn sjsuE sjsuN sjsuHwAll (ofTriple n) =
      denseCos 9 (pDense 9 (tTerms sjsuE sjsuN sjsuHwAll n)) :=
  funext fun φ => Tn_eq_denseCos sjsuE sjsuN 9 sjsuHwAll n (sjsuTTerms_box n) φ

end KAM.EffectiveStability.SJSU

end
