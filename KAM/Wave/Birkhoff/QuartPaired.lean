/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartNormal
public import KAM.Wave.Normal.ActionCoeff
public import KAM.Wave.Normal.Nonresonance

/-!
# Paired quadruples (blueprint-W `bpW:w3:quartic-ident`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic-ident`.

`birkPaired x`: the multiset `{x_t : x_t > 0}` equals `{-x_t : x_t < 0}` (as multisets of absolute
values); `birkTanSet` is `𝒯 = {x : min_t |x_t| ≤ 2}`. The sets `𝒯` and `{paired}` are invariant
under
permutations and `x ↦ -x` (`birkCoefBar_isCoef`: the coefficient `𝔤·1_{𝒯 ∩ paired}` of `Ḡ`).
`birkPaired_iff_divisor`: for `𝔤_x ≠ 0`, `δ_x = Σ_t λ'_{x_t} = 0` if and only if `x` is paired
(by the landed Lemma `quartic_nonresonance`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- The multiset of `|x_t|` over the positive entries. -/
def birkPosAbs (x : Fin 4 → BirkIdx) : Multiset ℕ+ :=
  ∑ t : Fin 4, if (x t).1 = true then ({(x t).2} : Multiset ℕ+) else 0

/-- The multiset of `|x_t|` over the negative entries. -/
def birkNegAbs (x : Fin 4 → BirkIdx) : Multiset ℕ+ :=
  ∑ t : Fin 4, if (x t).1 = false then ({(x t).2} : Multiset ℕ+) else 0

/-- `x` is *paired*: `{x_t : x_t > 0} = {-x_t : x_t < 0}`, i.e. `x` is a permutation of
`(r, -r, s, -s)`. -/
def birkPaired (x : Fin 4 → BirkIdx) : Prop := birkPosAbs x = birkNegAbs x

/-- `𝒯 = {x : min_t |x_t| ≤ 2}`: at least one tangential index. -/
def birkTanSet : Set (Fin 4 → BirkIdx) := {x | ∃ t, ((x t).2 : ℕ) ≤ 2}

/-- The set `𝒯 ∩ {paired}`. -/
def birkBarSet : Set (Fin 4 → BirkIdx) := {x | x ∈ birkTanSet ∧ birkPaired x}

theorem birkPosAbs_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkPosAbs (fun i => x (σ i)) = birkPosAbs x :=
  Equiv.sum_comp σ (fun t => if (x t).1 = true then ({(x t).2} : Multiset ℕ+) else 0)

theorem birkNegAbs_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkNegAbs (fun i => x (σ i)) = birkNegAbs x :=
  Equiv.sum_comp σ (fun t => if (x t).1 = false then ({(x t).2} : Multiset ℕ+) else 0)

theorem birkNeg_ite_pos (q : BirkIdx) :
    (if (birkNeg q).1 = true then ({(birkNeg q).2} : Multiset ℕ+) else 0) =
      if q.1 = false then ({q.2} : Multiset ℕ+) else 0 := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkNeg]

theorem birkNeg_ite_neg (q : BirkIdx) :
    (if (birkNeg q).1 = false then ({(birkNeg q).2} : Multiset ℕ+) else 0) =
      if q.1 = true then ({q.2} : Multiset ℕ+) else 0 := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkNeg]

theorem birkPosAbs_neg (x : Fin 4 → BirkIdx) : birkPosAbs (birkNegPi x) = birkNegAbs x := by
  unfold birkPosAbs birkNegAbs
  exact Finset.sum_congr rfl fun t _ => birkNeg_ite_pos (x t)

theorem birkNegAbs_neg (x : Fin 4 → BirkIdx) : birkNegAbs (birkNegPi x) = birkPosAbs x := by
  unfold birkPosAbs birkNegAbs
  exact Finset.sum_congr rfl fun t _ => birkNeg_ite_neg (x t)

theorem birkPaired_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkPaired (fun i => x (σ i)) ↔ birkPaired x := by
  unfold birkPaired
  rw [birkPosAbs_perm, birkNegAbs_perm]

theorem birkPaired_neg (x : Fin 4 → BirkIdx) : birkPaired (birkNegPi x) ↔ birkPaired x := by
  unfold birkPaired
  rw [birkPosAbs_neg, birkNegAbs_neg]
  exact eq_comm

theorem birkBarSet_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) (hx : x ∈ birkBarSet) :
    (fun i => x (σ i)) ∈ birkBarSet := by
  obtain ⟨⟨t, ht⟩, hp⟩ := hx
  exact ⟨⟨σ.symm t, by simpa using ht⟩, (birkPaired_perm σ x).2 hp⟩

theorem birkBarSet_neg (x : Fin 4 → BirkIdx) (hx : x ∈ birkBarSet) : birkNegPi x ∈ birkBarSet := by
  obtain ⟨⟨t, ht⟩, hp⟩ := hx
  exact ⟨⟨t, by simpa [birkNegPi] using ht⟩, (birkPaired_neg x).2 hp⟩

/-- The coefficient `𝔤 · 1_{𝒯 ∩ paired}` of `Ḡ`. -/
def birkCoefBar : (Fin 4 → BirkIdx) → ℂ := birkQuartCoefOn m hm birkBarSet

theorem birkCoefBar_isCoef : IsBirkQuartCoef m hm (birkCoefBar m hm) :=
  isBirkQuartCoef_on m hm birkBarSet birkBarSet_perm birkBarSet_neg

/-- The divisor `δ_x = Σ_t λ'_{x_t}`. -/
def birkDivisor (x : Fin 4 → BirkIdx) : ℝ := ∑ t, birkLam m hm (x t)

/-- `M ↦ Σ_{j ∈ M} λ_j` as an additive monoid homomorphism. -/
def birkLamSum : Multiset ℕ+ →+ ℝ :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom (lam m hm))

theorem birkLamSum_ite (b : Prop) [Decidable b] (j : ℕ+) :
    birkLamSum m hm (if b then ({j} : Multiset ℕ+) else 0) = if b then lam m hm j else 0 := by
  by_cases h : b <;> simp [h, birkLamSum]

theorem birkPaired_divisor_eq_zero (x : Fin 4 → BirkIdx) (hx : birkPaired x) :
    birkDivisor m hm x = 0 := by
  have h := congrArg (birkLamSum m hm) hx
  simp only [birkPosAbs, birkNegAbs, map_sum, birkLamSum_ite] at h
  unfold birkDivisor birkLam
  have e : ∀ t : Fin 4, (if (x t).1 then (1 : ℝ) else -1) * lam m hm (x t).2 =
      (if (x t).1 = true then lam m hm (x t).2 else 0) -
        (if (x t).1 = false then lam m hm (x t).2 else 0) := fun t => by
    obtain ⟨b, j⟩ := x t; cases b <;> simp
  simp only [e, Finset.sum_sub_distrib]
  rw [h]; ring

/-- The sign of `l` as a unit of `ℤ`. -/
def birkSgnU (q : BirkIdx) : ℤˣ := if q.1 then 1 else -1

theorem birkSgnU_cast (m : ℝ) (hm : 0 < m) (q : BirkIdx) :
    ((birkSgnU q : ℤ) : ℝ) * lam m hm q.2 = birkLam m hm q := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkSgnU, birkLam]

theorem birkSgnU_ite_pos (q : BirkIdx) :
    (if q.1 = true then ({q.2} : Multiset ℕ+) else 0) =
      if birkSgnU q = 1 then ({q.2} : Multiset ℕ+) else 0 := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkSgnU]

theorem birkSgnU_ite_neg (q : BirkIdx) :
    (if q.1 = false then ({q.2} : Multiset ℕ+) else 0) =
      if birkSgnU q = -1 then ({q.2} : Multiset ℕ+) else 0 := by
  obtain ⟨b, j⟩ := q; cases b <;> simp [birkSgnU]

/-- For `𝔤_x ≠ 0`: `δ_x = 0` forces `x` to be paired (landed Lemma `quartic_nonresonance`). -/
theorem birkPaired_of_divisor (x : Fin 4 → BirkIdx) (hg : birkG m hm x ≠ 0)
    (hd : birkDivisor m hm x = 0) : birkPaired x := by
  have hg' : sineQuarticCoeff (x 0).2 (x 1).2 (x 2).2 (x 3).2 ≠ 0 := by
    intro h; apply hg; unfold birkG waveTriCoef waveQuartic; rw [h]; simp
  have hres : ∑ t, ((birkSgnU (x t) : ℤ) : ℝ) * lam m hm (x t).2 = 0 := by
    rw [← hd]; unfold birkDivisor
    exact Finset.sum_congr rfl fun t _ => birkSgnU_cast m hm (x t)
  have h := quartic_nonresonance m hm (fun t => (x t).2) hg' (fun t => birkSgnU (x t)) hres
  unfold signSide at h
  unfold birkPaired birkPosAbs birkNegAbs
  simp only [birkSgnU_ite_pos, birkSgnU_ite_neg]
  exact h

/-- (`bpW:w3:quartic-ident`) For `𝔤_x ≠ 0`: `δ_x = 0` if and only if `x` is paired. -/
theorem birkPaired_iff_divisor (x : Fin 4 → BirkIdx) (hg : birkG m hm x ≠ 0) :
    birkDivisor m hm x = 0 ↔ birkPaired x :=
  ⟨birkPaired_of_divisor m hm x hg, birkPaired_divisor_eq_zero m hm x⟩

end KAM.Wave

end
