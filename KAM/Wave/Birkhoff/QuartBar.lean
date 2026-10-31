/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartPaired

/-!
# The resonant quartic `Ḡ`: sign patterns (blueprint-W `bpW:w3:quartic-ident`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic-ident`.

The quartic sum of `Ḡ` is split by sign pattern `s ∈ {±}⁴` (`birkV`); a pattern contributes only if it
has exactly two `+` (`birkV_eq_zero_of_pat`), all six such patterns contribute the same
(`birkV_perm`), so `16 Ḡ(w) = 6 · V(+,+,-,-)` (`birkQuartP_bar_eq_six`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The point `x_t = (s_t, m_t)` of `(ℤ ∖ {0})ⁿ`. -/
def birkMk {n : ℕ} (s : Fin n → Bool) (mm : Fin n → ℕ+) : Fin n → BirkIdx := fun t => (s t, mm t)

/-- The number of `+` signs of a pattern. -/
def birkPat (s : Fin 4 → Bool) : ℕ := (Finset.univ.filter fun t => s t = true).card

theorem card_birkPosAbs (s : Fin 4 → Bool) (mm : Fin 4 → ℕ+) :
    Multiset.card (birkPosAbs (birkMk s mm)) = birkPat s := by
  unfold birkPosAbs birkMk birkPat
  rw [map_sum Multiset.cardHom.toAddMonoidHom]
  simp [Finset.card_filter]

theorem card_pos_add_neg (x : Fin 4 → BirkIdx) :
    Multiset.card (birkPosAbs x) + Multiset.card (birkNegAbs x) = 4 := by
  unfold birkPosAbs birkNegAbs
  rw [map_sum Multiset.cardHom.toAddMonoidHom, map_sum Multiset.cardHom.toAddMonoidHom,
    ← Finset.sum_add_distrib]
  have : ∀ t : Fin 4, (Multiset.cardHom.toAddMonoidHom (if (x t).1 = true then
      ({(x t).2} : Multiset ℕ+) else 0)) + Multiset.cardHom.toAddMonoidHom (if (x t).1 = false then
      ({(x t).2} : Multiset ℕ+) else 0) = 1 := fun t => by
    obtain ⟨b, j⟩ := x t; cases b <;> simp
  simp only [this]; simp

theorem birkPat_eq_two_of_paired (s : Fin 4 → Bool) (mm : Fin 4 → ℕ+)
    (h : birkPaired (birkMk s mm)) : birkPat s = 2 := by
  have h1 := card_pos_add_neg (birkMk s mm)
  have h2 : Multiset.card (birkPosAbs (birkMk s mm)) = Multiset.card (birkNegAbs (birkMk s mm)) :=
    congrArg Multiset.card h
  rw [card_birkPosAbs] at h1 h2
  omega

end KAM.Wave

end
