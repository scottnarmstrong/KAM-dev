/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Drop
public import KAM.EffectiveStability.Tube.Engine.BrChunk

/-!
# The dropped-part check in chunks (T2-CONF, N7)

The kernel check `dropCheck` of the dropped bracket terms is one exact nested sum `dropSum` over
the observable entries `Fl`; at full size (about 90 entries) one declaration needs more than 10 GB
of kernel memory. `dropSum` is additive in `Fl` (`dropSum_append`), so it is checked in chunks of
`m` consecutive entries (`dropCheckC`, one declaration each) against chunk claims whose sum is at
most the claim of `dropCheck` (`dropCheck_of_chunks`). No precision is lost beyond the rounding of
the chunk claims.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- An additive function of a list is the sum of its values on the chunks of length `m`. -/
theorem sum_chunks_of_additive {α : Type*} (S : List α → ℚ) (h0 : S [] = 0)
    (hadd : ∀ l₁ l₂, S (l₁ ++ l₂) = S l₁ + S l₂) (m : ℕ) :
    ∀ (n : ℕ) (l : List α), l.length ≤ m * n →
      S l = ((List.range n).map fun k => S (chunk l m k)).sum
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp [h0]
  | n + 1, l, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hc0 : chunk l m 0 = l.take m := by simp [chunk]
    rw [hc0]
    conv_lhs => rw [← List.take_append_drop m l]
    rw [hadd, sum_chunks_of_additive S h0 hadd m n (l.drop m)
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at h; omega)]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp only [Function.comp_apply, chunk_succ]

theorem dropSum_nil (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Hl : List (ℕ × ℕ × ℕ)) : dropSum Pb HL nH r L [] Hl = 0 := by
  simp [dropSum]

theorem dropSum_append (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (l₁ l₂ : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) :
    dropSum Pb HL nH r L (l₁ ++ l₂) Hl =
      dropSum Pb HL nH r L l₁ Hl + dropSum Pb HL nH r L l₂ Hl := by
  simp only [dropSum, List.map_append, List.sum_append, List.sum_map_add]

/-- **The kernel check of a chunk** of the dropped part: `dropSum` over the entries
`m k, …, m k + m - 1` of `Fl` is at most `Dk`. -/
def dropCheckC (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) (m k : ℕ) (Dk : ℚ) : Bool :=
  decide (dropSum Pb HL nH r L (chunk Fl m k) Hl ≤ Dk)

/-- **The dropped-part check from its chunks.** -/
theorem dropCheck_of_chunks {Pb : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ} {r : ℚ} {L : ℕ}
    {Fl : List ((ℕ × ℕ × ℕ) × SpD)} {Hl : List (ℕ × ℕ × ℕ)} {m n : ℕ} {Dc : ℕ → ℚ} {D : ℚ}
    (hr : 0 ≤ r) (hlen : Fl.length ≤ m * n)
    (hk : ∀ k < n, dropCheckC Pb HL nH r L Fl Hl m k (Dc k) = true)
    (hD : ((List.range n).map Dc).sum ≤ D) : dropCheck Pb HL nH r L Fl Hl D = true := by
  simp only [dropCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hr, ?_⟩
  rw [sum_chunks_of_additive (fun l => dropSum Pb HL nH r L l Hl) (dropSum_nil Pb HL nH r L Hl)
    (fun l₁ l₂ => dropSum_append Pb HL nH r L l₁ l₂ Hl) m n Fl hlen]
  refine le_trans (List.sum_le_sum fun k hk' => ?_) hD
  exact of_decide_eq_true (hk k (List.mem_range.mp hk'))

end KAM.EffectiveStability.Tube

end
