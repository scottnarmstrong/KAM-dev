/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.QuarticCoeff
public import KAM.Wave.Normal.NonresAux

/-!
# Qualitative nonresonance of all quartic terms (blueprint `bpW:w0n:nonres`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

Let `m > 0`, `a b c d ≥ 1` with `g_{abcd} ≠ 0` and `σ ∈ {±1}⁴`. If
`σ₁ λ_a + σ₂ λ_b + σ₃ λ_c + σ₄ λ_d = 0`, then the indices with `σ = +1` and those with `σ = -1`
form equal multisets (`KAM.Wave.quartic_nonresonance`). The proof follows the blueprint: a signed
relation `g ≠ 0` (selection rule), then Step `stepW:w0n:31` (one sign against three) and Step
`stepW:w0n:22` (two against two, types (1), (2), (3)); the analytic facts are in
`KAM/Wave/Normal/NonresAux.lean`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The multiset of indices `v t` over the positions with sign `σ t = ε`. -/
def signSide (σ : Fin 4 → ℤˣ) (v : Fin 4 → ℕ+) (ε : ℤˣ) : Multiset ℕ+ :=
  ∑ t, if σ t = ε then {v t} else 0

/-- Two against two (Step `stepW:w0n:22`): under the selection rule, `λ_a + λ_b = λ_c + λ_d`
forces `{a, b} = {c, d}`. -/
theorem lamExt_two_two {m : ℝ} (hm : 0 < m) {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (hs : QuarticSel a b c d)
    (h : lamExt m a + lamExt m b = lamExt m c + lamExt m d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold QuarticSel at hs
  rcases hs with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · left
    exact lamExt_cross_eq hm h1 (by linarith)
  · right
    exact lamExt_cross_eq hm h1 h
  · exact lamExt_pair_eq hm h1 h
  · exfalso
    have := lamExt_big_lt (m := m) hm (X := a) (Y := b) (Z := c) (W := d) hb (by omega)
    linarith
  · exfalso
    have := lamExt_big_lt (m := m) hm (X := b) (Y := a) (Z := c) (W := d) ha (by omega)
    linarith
  · exfalso
    have := lamExt_big_lt (m := m) hm (X := c) (Y := d) (Z := a) (W := b) hd (by omega)
    linarith
  · exfalso
    have := lamExt_big_lt (m := m) hm (X := d) (Y := c) (Z := a) (W := b) hc (by omega)
    linarith

/-- Qualitative nonresonance of all quartic terms (blueprint `bpW:w0n:nonres`). -/
theorem quartic_nonresonance (m : ℝ) (hm : 0 < m) (v : Fin 4 → ℕ+)
    (hg : quarticCoeff (v 0) (v 1) (v 2) (v 3) ≠ 0) (σ : Fin 4 → ℤˣ)
    (hres : ∑ t, ((σ t : ℤ) : ℝ) * lam m hm (v t) = 0) :
    signSide σ v 1 = signSide σ v (-1) := by
  have hs := quarticSel_of_quarticCoeff_ne_zero _ _ _ _ hg
  simp only [Fin.sum_univ_four, lam_eq_lamExt] at hres
  unfold signSide
  simp only [Fin.sum_univ_four]
  have pa := (v 0).pos
  have pb := (v 1).pos
  have pc := (v 2).pos
  have pd := (v 3).pos
  generalize v 0 = a at *
  generalize v 1 = b at *
  generalize v 2 = c at *
  generalize v 3 = d at *
  have la := lamExt_pos hm ((a : ℕ) : ℝ)
  have lb := lamExt_pos hm ((b : ℕ) : ℝ)
  have lc := lamExt_pos hm ((c : ℕ) : ℝ)
  have ld := lamExt_pos hm ((d : ℕ) : ℝ)
  have n1 : ¬ ((1 : ℤˣ) = -1) := by decide
  have n2 : ¬ ((-1 : ℤˣ) = 1) := by decide
  rcases Int.units_eq_one_or (σ 0) with h0 | h0 <;> rcases Int.units_eq_one_or (σ 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (σ 2) with h2 | h2 <;> rcases Int.units_eq_one_or (σ 3) with h3 | h3 <;>
    simp only [h0, h1, h2, h3, n1, n2, ite_true, ite_false,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_mul] at hres ⊢
  · -- ++++
    exfalso; linarith
  · -- +++-
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((b : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) = lamExt m ((d : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (b : ℕ)) (c := (c : ℕ)) (d := (d : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- ++-+
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((b : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((c : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (b : ℕ)) (c := (d : ℕ)) (d := (c : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- ++--
    have hk := lamExt_two_two hm (a := (a : ℕ)) (b := (b : ℕ)) (c := (c : ℕ)) (d := (d : ℕ)) pa pb pc pd
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- +-++
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((b : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (c : ℕ)) (c := (d : ℕ)) (d := (b : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- +-+-
    have hk := lamExt_two_two hm (a := (a : ℕ)) (b := (c : ℕ)) (c := (b : ℕ)) (d := (d : ℕ)) pa pc pb pd
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- +--+
    have hk := lamExt_two_two hm (a := (a : ℕ)) (b := (d : ℕ)) (c := (b : ℕ)) (d := (c : ℕ)) pa pd pb pc
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- +---
    exact absurd (by linarith : lamExt m ((b : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((a : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (b : ℕ)) (b := (c : ℕ)) (c := (d : ℕ)) (d := (a : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- -+++
    exact absurd (by linarith : lamExt m ((b : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((a : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (b : ℕ)) (b := (c : ℕ)) (c := (d : ℕ)) (d := (a : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- -++-
    have hk := lamExt_two_two hm (a := (b : ℕ)) (b := (c : ℕ)) (c := (a : ℕ)) (d := (d : ℕ)) pb pc pa pd
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- -+-+
    have hk := lamExt_two_two hm (a := (b : ℕ)) (b := (d : ℕ)) (c := (a : ℕ)) (d := (c : ℕ)) pb pd pa pc
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- -+--
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((b : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (c : ℕ)) (c := (d : ℕ)) (d := (b : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- --++
    have hk := lamExt_two_two hm (a := (c : ℕ)) (b := (d : ℕ)) (c := (a : ℕ)) (d := (b : ℕ)) pc pd pa pb
      (by unfold QuarticSel at hs ⊢; omega) (by linarith)
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [PNat.coe_injective e1, PNat.coe_injective e2] <;> abel
  · -- --+-
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((b : ℕ) : ℝ) + lamExt m ((d : ℕ) : ℝ) = lamExt m ((c : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (b : ℕ)) (c := (d : ℕ)) (d := (c : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- ---+
    exact absurd (by linarith : lamExt m ((a : ℕ) : ℝ) + lamExt m ((b : ℕ) : ℝ) + lamExt m ((c : ℕ) : ℝ) = lamExt m ((d : ℕ) : ℝ))
      (lamExt_three_ne hm (a := (a : ℕ)) (b := (b : ℕ)) (c := (c : ℕ)) (d := (d : ℕ)) (by unfold QuarticSel at hs; omega))
  · -- ----
    exfalso; linarith

end KAM.Wave

end
