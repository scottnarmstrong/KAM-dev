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
  rw [Multiset.card_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : s t = true <;> simp [h]

theorem card_pos_add_neg (x : Fin 4 → BirkIdx) :
    Multiset.card (birkPosAbs x) + Multiset.card (birkNegAbs x) = 4 := by
  unfold birkPosAbs birkNegAbs
  rw [Multiset.card_sum, Multiset.card_sum, ← Finset.sum_add_distrib]
  have : ∀ t : Fin 4, Multiset.card (if (x t).1 = true then ({(x t).2} : Multiset ℕ+) else 0) +
      Multiset.card (if (x t).1 = false then ({(x t).2} : Multiset ℕ+) else 0) = 1 := fun t => by
    obtain ⟨b, j⟩ := x t; cases b <;> simp
  simp only [this]; simp

theorem birkPat_eq_two_of_paired (s : Fin 4 → Bool) (mm : Fin 4 → ℕ+)
    (h : birkPaired (birkMk s mm)) : birkPat s = 2 := by
  have h1 := card_pos_add_neg (birkMk s mm)
  have h2 : Multiset.card (birkPosAbs (birkMk s mm)) = Multiset.card (birkNegAbs (birkMk s mm)) :=
    congrArg Multiset.card h
  rw [card_birkPosAbs] at h1 h2
  omega

/-- The base pattern `(+, +, -, -)`. -/
def birkS0 : Fin 4 → Bool := ![true, true, false, false]

theorem birkPat_exists_perm : ∀ s : Fin 4 → Bool, birkPat s = 2 →
    ∃ π : Equiv.Perm (Fin 4), s = fun i => birkS0 (π i) := by
  unfold birkPat birkS0
  decide

theorem card_birkPat_two :
    (Finset.univ.filter fun s : Fin 4 → Bool => birkPat s = 2).card = 6 := by
  unfold birkPat
  decide

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The contribution `V(s) = Σ_{m ∈ (ℕ+)⁴} c_{(s,m)} ∏_t w_{(s_t, m_t)}` of the sign pattern `s`. -/
def birkV (a p : ℝ) (c : (Fin 4 → BirkIdx) → ℂ) (w : BirkSpace) (s : Fin 4 → Bool) : ℂ :=
  ∑' mm : Fin 4 → ℕ+, c (birkMk s mm) * ∏ t, birkCoord a p w (s t, mm t)

include ha hp in
/-- The quartic sum as a sum over the sign patterns. -/
theorem birkQuartP_eq_sum_V {c : (Fin 4 → BirkIdx) → ℂ} (hc : IsBirkQuartCoef m hm c)
    (w : BirkSpace) :
    birkQuartP m hm ha hp hc w = (1 / 16 : ℂ) * ∑ s : Fin 4 → Bool, birkV a p c w s := by
  unfold birkQuartP birkDiag
  rw [birkQuartForm_apply]
  unfold birkQuartSum
  congr 1
  have hsum := (summable_birkQuartTerm m hm ha hp hc.bound (fun _ => w)).of_norm
  have e : ∀ x : Fin 4 → BirkIdx, c x * birkAtom a p x (fun _ => w) =
      c x * ∏ t, birkCoord a p w (x t) := fun x => by rw [birkAtom_apply]
  simp only [e] at hsum ⊢
  rw [birk_tsum_pi hsum]
  rfl

theorem birkV_eq_zero_of_pat {w : BirkSpace} {s : Fin 4 → Bool} (hs : birkPat s ≠ 2) :
    birkV a p (birkCoefBar m hm) w s = 0 := by
  unfold birkV
  refine (tsum_congr fun mm => ?_).trans tsum_zero
  have : birkCoefBar m hm (birkMk s mm) = 0 := by
    have hmem : birkMk s mm ∉ birkBarSet := fun hmem =>
      hs (birkPat_eq_two_of_paired s mm hmem.2)
    simp [birkCoefBar, birkQuartCoefOn, hmem]
  simp [this]

/-- Permuting the sign pattern does not change `V`. -/
theorem birkV_perm {c : (Fin 4 → BirkIdx) → ℂ} (hc : IsBirkQuartCoef m hm c) (w : BirkSpace)
    (s : Fin 4 → Bool) (π : Equiv.Perm (Fin 4)) :
    birkV a p c w (fun i => s (π i)) = birkV a p c w s := by
  unfold birkV
  rw [← (Equiv.arrowCongr π.symm (Equiv.refl ℕ+)).tsum_eq
    (fun mm => c (birkMk (fun i => s (π i)) mm) * ∏ t, birkCoord a p w (s (π t), mm t))]
  refine tsum_congr fun mm => ?_
  have e1 : c (birkMk (fun i => s (π i)) (fun i => mm (π i))) = c (birkMk s mm) :=
    hc.perm π (birkMk s mm)
  have e2 : ∏ t, birkCoord a p w (s (π t), mm (π t)) = ∏ t, birkCoord a p w (s t, mm t) :=
    Equiv.prod_comp π (fun t => birkCoord a p w (s t, mm t))
  show c (birkMk (fun i => s (π i)) (fun i => mm (π i))) *
    ∏ t, birkCoord a p w (s (π t), mm (π t)) = _
  rw [e1, e2]

include ha hp in
theorem summable_birkV_term {c : (Fin 4 → BirkIdx) → ℂ} (hc : IsBirkQuartCoef m hm c)
    (w : BirkSpace) (s : Fin 4 → Bool) :
    Summable fun mm : Fin 4 → ℕ+ => c (birkMk s mm) * ∏ t, birkCoord a p w (s t, mm t) := by
  have hsum := (summable_birkQuartTerm m hm ha hp hc.bound (fun _ => w)).of_norm
  have e : ∀ x : Fin 4 → BirkIdx, c x * birkAtom a p x (fun _ => w) =
      c x * ∏ t, birkCoord a p w (x t) := fun x => by rw [birkAtom_apply]
  simp only [e] at hsum
  have hs' := (birkPiEquiv 4).summable_iff
    (f := fun x : Fin 4 → BirkIdx => c x * ∏ t, birkCoord a p w (x t)) |>.2 hsum
  exact (hs'.prod_factor s :)

omit ha hp in
/-- `Σ_s V(s) = 6 V(+,+,-,-)`. -/
theorem birkV_sum_eq_six (w : BirkSpace) :
    ∑ s : Fin 4 → Bool, birkV a p (birkCoefBar m hm) w s = 6 * birkV a p (birkCoefBar m hm) w birkS0 := by
  have hc := birkCoefBar_isCoef m hm
  have h : ∀ s : Fin 4 → Bool, birkV a p (birkCoefBar m hm) w s =
      if birkPat s = 2 then birkV a p (birkCoefBar m hm) w birkS0 else 0 := fun s => by
    by_cases hs : birkPat s = 2
    · obtain ⟨π, hπ⟩ := birkPat_exists_perm s hs
      simp only [hs, ↓reduceIte]
      rw [hπ, birkV_perm m hm hc]
    · simp only [hs, ↓reduceIte]; exact birkV_eq_zero_of_pat m hm hs
  rw [Finset.sum_congr rfl fun s _ => h s, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, card_birkPat_two]
  simp

/-- Two-element multisets: `{a, b} = {c, d}` iff `(a, b) = (c, d)` or `(a, b) = (d, c)`. -/
theorem birk_pair_eq_iff {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a} + {b} : Multiset α) = {c} + {d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c} + {d} : Multiset α) := h ▸ (by simp)
    simp only [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have := add_left_cancel h
      simpa using this
    · right
      refine ⟨rfl, ?_⟩
      rw [add_comm ({c} : Multiset α) {a}] at h
      have := add_left_cancel h
      simpa using this
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

theorem birkMk_s0_paired (mm : Fin 4 → ℕ+) :
    birkPaired (birkMk birkS0 mm) ↔
      (mm 0 = mm 2 ∧ mm 1 = mm 3) ∨ (mm 0 = mm 3 ∧ mm 1 = mm 2) := by
  unfold birkPaired birkPosAbs birkNegAbs
  simp [birkMk, birkS0, Fin.sum_univ_four]
  exact birk_pair_eq_iff _ _ _ _

/-- `I_j = w_j w_{-j}`. -/
def birkAction (a p : ℝ) (y : BirkSpace) (j : ℕ+) : ℂ :=
  birkCoord a p y (true, j) * birkCoord a p y (false, j)

theorem birkCoefBar_s0 (mm : Fin 4 → ℕ+) :
    birkCoefBar m hm (birkMk birkS0 mm) =
      if (∃ t, ((mm t : ℕ) ≤ 2)) ∧ ((mm 0 = mm 2 ∧ mm 1 = mm 3) ∨ (mm 0 = mm 3 ∧ mm 1 = mm 2))
      then ((waveTriCoef m hm (mm 0) (mm 1) (mm 2) (mm 3) : ℝ) : ℂ) else 0 := by
  classical
  unfold birkCoefBar birkQuartCoefOn
  have hmem : birkMk birkS0 mm ∈ birkBarSet ↔ (∃ t, ((mm t : ℕ) ≤ 2)) ∧
      ((mm 0 = mm 2 ∧ mm 1 = mm 3) ∨ (mm 0 = mm 3 ∧ mm 1 = mm 2)) := by
    unfold birkBarSet birkTanSet
    simp only [Set.mem_ofPred_eq, birkMk_s0_paired, birkMk]
  simp only [hmem, birkG, birkMk]


theorem waveTriCoef_swap_last (r s : ℕ+) :
    waveTriCoef m hm r s s r = waveTriCoef m hm r s r s := by
  unfold waveTriCoef waveQuartic
  rw [sineQuarticCoeff_pair_val_b, sineQuarticCoeff_pair_val_c]
  ring

include ha hp in
/-- `V(+,+,-,-)` as a sum over pairs `(r, s)`. -/
theorem birkV_s0_eq (w : BirkSpace) :
    birkV a p (birkCoefBar m hm) w birkS0 =
      ∑' rs : ℕ+ × ℕ+, (if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then
        (1 + (if rs.1 = rs.2 then 0 else 1)) *
          ((waveTriCoef m hm rs.1 rs.2 rs.1 rs.2 : ℝ) : ℂ) *
            (birkAction a p w rs.1 * birkAction a p w rs.2) else 0) := by
  classical
  set c := birkCoefBar m hm with hcdef
  set F : (Fin 4 → ℕ+) → ℂ := fun mm => c (birkMk birkS0 mm) *
      ∏ t, birkCoord a p w (birkS0 t, mm t) with hF
  have hFs : Summable F := summable_birkV_term m hm ha hp (birkCoefBar_isCoef m hm) w birkS0
  set F1 : (Fin 4 → ℕ+) → ℂ := fun mm => if (mm 0 = mm 2 ∧ mm 1 = mm 3) then F mm else 0 with hF1
  set F2 : (Fin 4 → ℕ+) → ℂ := fun mm =>
    if (mm 0 ≠ mm 1 ∧ mm 0 = mm 3 ∧ mm 1 = mm 2) then F mm else 0 with hF2
  have hsplit : ∀ mm, F mm = F1 mm + F2 mm := by
    intro mm
    by_cases h1 : mm 0 = mm 2 ∧ mm 1 = mm 3
    · have : ¬ (mm 0 ≠ mm 1 ∧ mm 0 = mm 3 ∧ mm 1 = mm 2) := by
        rintro ⟨hne, h3, -⟩; exact hne (h3.trans h1.2.symm)
      simp only [hF1, hF2]; rw [if_pos h1, if_neg this, add_zero]
    · by_cases h2 : mm 0 ≠ mm 1 ∧ mm 0 = mm 3 ∧ mm 1 = mm 2
      · simp only [hF1, hF2]; rw [if_neg h1, if_pos h2, zero_add]
      · have hc0 : c (birkMk birkS0 mm) = 0 := by
          rw [hcdef, birkCoefBar_s0]
          refine if_neg ?_
          rintro ⟨-, hp'⟩
          rcases hp' with hp' | hp'
          · exact h1 hp'
          · by_cases h01 : mm 0 = mm 1
            · exact h1 ⟨h01.trans hp'.2, h01.symm.trans hp'.1⟩
            · exact h2 ⟨h01, hp'.1, hp'.2⟩
        have : F mm = 0 := by simp [hF, hc0]
        simp only [hF1, hF2]; rw [if_neg h1, if_neg h2, this, add_zero]
  have hF1s : Summable F1 :=
    Summable.of_norm_bounded hFs.norm (fun mm => by simp only [hF1]; split_ifs <;> simp)
  have hF2s : Summable F2 :=
    Summable.of_norm_bounded hFs.norm (fun mm => by simp only [hF2]; split_ifs <;> simp)
  unfold birkV
  show ∑' mm, F mm = _
  rw [tsum_congr hsplit, hF1s.tsum_add hF2s]
  let ι1 : ℕ+ × ℕ+ → (Fin 4 → ℕ+) := fun rs => ![rs.1, rs.2, rs.1, rs.2]
  let ι2 : ℕ+ × ℕ+ → (Fin 4 → ℕ+) := fun rs => ![rs.1, rs.2, rs.2, rs.1]
  have i1 : Function.Injective ι1 := fun x y h =>
    Prod.ext (by simpa [ι1] using congrFun h 0) (by simpa [ι1] using congrFun h 1)
  have i2 : Function.Injective ι2 := fun x y h =>
    Prod.ext (by simpa [ι2] using congrFun h 0) (by simpa [ι2] using congrFun h 1)
  have hs1 : Function.support F1 ⊆ Set.range ι1 := by
    intro mm hmm
    have h : mm 0 = mm 2 ∧ mm 1 = mm 3 := by
      by_contra h; exact hmm (by simp only [hF1]; rw [if_neg h])
    refine ⟨(mm 0, mm 1), ?_⟩
    funext i; fin_cases i <;> simp [ι1, h.1, h.2]
  have hs2 : Function.support F2 ⊆ Set.range ι2 := by
    intro mm hmm
    have h : mm 0 ≠ mm 1 ∧ mm 0 = mm 3 ∧ mm 1 = mm 2 := by
      by_contra h; exact hmm (by simp only [hF2]; rw [if_neg h])
    refine ⟨(mm 0, mm 1), ?_⟩
    funext i; fin_cases i <;> simp [ι2, h.2.1, h.2.2]
  have hz1 : ∀ x ∉ Set.range ι1, F1 x = 0 := fun x hx => by
    by_contra h; exact hx (hs1 h)
  have hz2 : ∀ x ∉ Set.range ι2, F2 x = 0 := fun x hx => by
    by_contra h; exact hx (hs2 h)
  have hS1 : Summable (F1 ∘ ι1) := (i1.summable_iff hz1).2 hF1s
  have hS2 : Summable (F2 ∘ ι2) := (i2.summable_iff hz2).2 hF2s
  rw [← i1.tsum_eq hs1, ← i2.tsum_eq hs2]
  refine (Summable.tsum_add hS1 hS2).symm.trans ?_
  refine tsum_congr fun rs => ?_
  obtain ⟨r, s⟩ := rs
  have hc1 : ((∃ t : Fin 4, (((ι1 (r, s) t : ℕ+) : ℕ) ≤ 2)) ∧
      (((ι1 (r, s)) 0 = (ι1 (r, s)) 2 ∧ (ι1 (r, s)) 1 = (ι1 (r, s)) 3) ∨
        ((ι1 (r, s)) 0 = (ι1 (r, s)) 3 ∧ (ι1 (r, s)) 1 = (ι1 (r, s)) 2))) ↔
      (((r : ℕ) ≤ 2) ∨ ((s : ℕ) ≤ 2)) := by
    constructor
    · rintro ⟨⟨t, ht⟩, -⟩
      fin_cases t <;> simp [ι1] at ht <;> tauto
    · intro h
      refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
      rcases h with h | h
      · exact ⟨0, by simpa [ι1] using h⟩
      · exact ⟨1, by simpa [ι1] using h⟩
  have hc2 : ((∃ t : Fin 4, (((ι2 (r, s) t : ℕ+) : ℕ) ≤ 2)) ∧
      (((ι2 (r, s)) 0 = (ι2 (r, s)) 2 ∧ (ι2 (r, s)) 1 = (ι2 (r, s)) 3) ∨
        ((ι2 (r, s)) 0 = (ι2 (r, s)) 3 ∧ (ι2 (r, s)) 1 = (ι2 (r, s)) 2))) ↔
      (((r : ℕ) ≤ 2) ∨ ((s : ℕ) ≤ 2)) := by
    constructor
    · rintro ⟨⟨t, ht⟩, -⟩
      fin_cases t <;> simp [ι2] at ht <;> tauto
    · intro h
      refine ⟨?_, Or.inr ⟨rfl, rfl⟩⟩
      rcases h with h | h
      · exact ⟨0, by simpa [ι2] using h⟩
      · exact ⟨1, by simpa [ι2] using h⟩
  have hFi1 : F (ι1 (r, s)) = (if ((r : ℕ) ≤ 2 ∨ (s : ℕ) ≤ 2) then
      ((waveTriCoef m hm r s r s : ℝ) : ℂ) else 0) * (birkAction a p w r * birkAction a p w s) := by
    simp only [hF, hcdef, birkCoefBar_s0, hc1]
    have : (∏ t, birkCoord a p w (birkS0 t, ι1 (r, s) t)) =
        birkAction a p w r * birkAction a p w s := by
      simp [Fin.prod_univ_four, birkS0, ι1, birkAction]; ring
    rw [this]
    rfl
  have hFi2 : F (ι2 (r, s)) = (if ((r : ℕ) ≤ 2 ∨ (s : ℕ) ≤ 2) then
      ((waveTriCoef m hm r s r s : ℝ) : ℂ) else 0) * (birkAction a p w r * birkAction a p w s) := by
    simp only [hF, hcdef, birkCoefBar_s0, hc2]
    have : (∏ t, birkCoord a p w (birkS0 t, ι2 (r, s) t)) =
        birkAction a p w r * birkAction a p w s := by
      simp [Fin.prod_univ_four, birkS0, ι2, birkAction]; ring
    rw [this]
    show (if _ then ((waveTriCoef m hm r s s r : ℝ) : ℂ) else 0) * _ = _
    rw [waveTriCoef_swap_last]
  show F1 (ι1 (r, s)) + F2 (ι2 (r, s)) = _
  have e1 : (ι1 (r, s)) 0 = (ι1 (r, s)) 2 ∧ (ι1 (r, s)) 1 = (ι1 (r, s)) 3 := ⟨rfl, rfl⟩
  simp only [hF1, hF2]
  rw [if_pos e1]
  by_cases hrs : r = s
  · have : ¬ ((ι2 (r, s)) 0 ≠ (ι2 (r, s)) 1 ∧ (ι2 (r, s)) 0 = (ι2 (r, s)) 3 ∧
        (ι2 (r, s)) 1 = (ι2 (r, s)) 2) := fun h => h.1 (by simpa [ι2] using hrs)
    rw [if_neg this, add_zero, hFi1]
    simp only [hrs, if_true]
    split_ifs <;> simp
  · have : (ι2 (r, s)) 0 ≠ (ι2 (r, s)) 1 ∧ (ι2 (r, s)) 0 = (ι2 (r, s)) 3 ∧
        (ι2 (r, s)) 1 = (ι2 (r, s)) 2 := ⟨by simpa [ι2] using hrs, rfl, rfl⟩
    rw [if_pos this, hFi1, hFi2]
    simp only [hrs, if_false]
    split_ifs <;> ring

end

end KAM.Wave

end
