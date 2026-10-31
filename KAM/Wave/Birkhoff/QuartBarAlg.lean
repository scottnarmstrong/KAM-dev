/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartBar

/-!
# The resonant quartic `Ḡ` (blueprint-W `bpW:w3:quartic-ident`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:quartic-ident`.

`birkQuartP_bar`: for every `w ∈ 𝔚` (complex coordinates, no reality assumption),
`Ḡ(w) = ½ Σ_{i,i'∈J} A_{ii'} I_i I_{i'} + Σ_{j ≥ 3, i ∈ J} B_{ji} I_i I_j`, `I_j = w_j w_{-j}`, with the
corrected `A`, `B` of the landed `actionA` and `birkActionB` (`birkActionB_eq`: `actionB` for the
finite normal modes), where `Ḡ = P` of the coefficient `𝔤 · 1_{𝒯 ∩ paired}` (`birkCoefBar`).
The proof counts the paired terms: `24` orderings for `r ≠ s` (six sign patterns, each with the two
arrangements of the negative pair) and `6` for `r = s`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The coupling coefficient `B_{ji} = 3/(2π λ_j λ_i)` for `j ∈ ℕ+` and the tangential mode `i`. -/
def birkActionB (j : ℕ+) (i : Fin 2) : ℝ := 3 / (2 * Real.pi * lam m hm j * lamTan m hm i)

/-- `birkActionB` extends the landed `actionB` (finite normal modes `j ↦ j + 3`). -/
theorem birkActionB_eq {n : ℕ} (j : Fin n) (i : Fin 2) :
    actionB m hm j i = birkActionB m hm ⟨j.val + 3, Nat.succ_pos _⟩ i := rfl

theorem lamTan_eq (i : Fin 2) : lamTan m hm i = lam m hm (modeIdx i) := rfl

theorem exists_modeIdx_of_le (r : ℕ+) (h : (r : ℕ) ≤ 2) : ∃ i : Fin 2, modeIdx i = r :=
  ⟨⟨(r : ℕ) - 1, by have := r.pos; omega⟩, PNat.eq (by simp [modeIdx]; have := r.pos; omega)⟩

theorem modeIdx_le_two (i : Fin 2) : ((modeIdx i : ℕ+) : ℕ) ≤ 2 := by
  simp [modeIdx]
  have := i.is_lt
  omega

/-- Splitting a symmetric sum over `{(r,s) : min(r,s) ≤ 2}` into the tangential block and twice the
mixed part. -/
theorem tsum_tan_split (k : ℕ+ → ℕ+ → ℂ) (hsym : ∀ r s, k r s = k s r)
    (hK : Summable fun rs : ℕ+ × ℕ+ => if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0) :
    ∑' rs : ℕ+ × ℕ+, (if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0) =
      ∑ i : Fin 2, ∑ i' : Fin 2, k (modeIdx i) (modeIdx i') +
        2 * ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then k (modeIdx i) j else 0) := by
  classical
  let K : ℕ+ × ℕ+ → ℂ := fun rs => if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0
  let KTT : ℕ+ × ℕ+ → ℂ := fun rs => if ((rs.1 : ℕ) ≤ 2 ∧ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0
  let KTN : ℕ+ × ℕ+ → ℂ := fun rs => if ((rs.1 : ℕ) ≤ 2 ∧ 3 ≤ (rs.2 : ℕ)) then k rs.1 rs.2 else 0
  have hdec : ∀ rs, K rs = KTT rs + KTN rs + KTN (rs.2, rs.1) := by
    rintro ⟨r, s⟩
    simp only [K, KTT, KTN]
    rw [hsym s r]
    by_cases h1 : (r : ℕ) ≤ 2 <;> by_cases h2 : (s : ℕ) ≤ 2 <;>
      simp [h1, h2, show ∀ n : ℕ, 3 ≤ n ↔ ¬ n ≤ 2 from fun n => by omega]
  have hKTT : Summable KTT := Summable.of_norm_bounded hK.norm (fun rs => by
    simp only [KTT]; split_ifs <;> simp_all)
  have hKTN : Summable KTN := Summable.of_norm_bounded hK.norm (fun rs => by
    simp only [KTN]; split_ifs <;> simp_all)
  have hKNT : Summable fun rs : ℕ+ × ℕ+ => KTN (rs.2, rs.1) :=
    (Equiv.prodComm ℕ+ ℕ+).summable_iff.2 hKTN
  have e1 : ∑' rs : ℕ+ × ℕ+, K rs = ∑' rs : ℕ+ × ℕ+, KTT rs + ∑' rs : ℕ+ × ℕ+, KTN rs +
      ∑' rs : ℕ+ × ℕ+, KTN (rs.2, rs.1) := by
    rw [tsum_congr hdec, (hKTT.add hKTN).tsum_add hKNT, hKTT.tsum_add hKTN]
  have e2 : ∑' rs : ℕ+ × ℕ+, KTN (rs.2, rs.1) = ∑' rs : ℕ+ × ℕ+, KTN rs :=
    (Equiv.prodComm ℕ+ ℕ+).tsum_eq (fun rs : ℕ+ × ℕ+ => KTN rs)
  -- the tangential block
  have ιTT : Function.Injective (fun ii : Fin 2 × Fin 2 => (modeIdx ii.1, modeIdx ii.2)) :=
    fun x y h => Prod.ext (modeIdx_injective (Prod.mk.inj h).1) (modeIdx_injective (Prod.mk.inj h).2)
  have sTT : Function.support KTT ⊆ Set.range (fun ii : Fin 2 × Fin 2 => (modeIdx ii.1, modeIdx ii.2)) := by
    intro rs hrs
    have h : (rs.1 : ℕ) ≤ 2 ∧ (rs.2 : ℕ) ≤ 2 := by
      by_contra h; exact hrs (by simp only [KTT]; rw [if_neg h])
    obtain ⟨i, hi⟩ := exists_modeIdx_of_le rs.1 h.1
    obtain ⟨i', hi'⟩ := exists_modeIdx_of_le rs.2 h.2
    exact ⟨(i, i'), Prod.ext hi hi'⟩
  have eTT : ∑' rs, KTT rs = ∑ i : Fin 2, ∑ i' : Fin 2, k (modeIdx i) (modeIdx i') := by
    rw [← ιTT.tsum_eq sTT, tsum_fintype, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    simp only [KTT]
    rw [if_pos ⟨modeIdx_le_two i, modeIdx_le_two i'⟩]
  -- the mixed block
  have ιTN : Function.Injective (fun ij : Fin 2 × ℕ+ => (modeIdx ij.1, ij.2)) :=
    fun x y h => Prod.ext (modeIdx_injective (Prod.mk.inj h).1) (Prod.mk.inj h).2
  have sTN : Function.support KTN ⊆ Set.range (fun ij : Fin 2 × ℕ+ => (modeIdx ij.1, ij.2)) := by
    intro rs hrs
    have h : (rs.1 : ℕ) ≤ 2 ∧ 3 ≤ (rs.2 : ℕ) := by
      by_contra h; exact hrs (by simp only [KTN]; rw [if_neg h])
    obtain ⟨i, hi⟩ := exists_modeIdx_of_le rs.1 h.1
    exact ⟨(i, rs.2), Prod.ext hi rfl⟩
  have zTN : ∀ x ∉ Set.range (fun ij : Fin 2 × ℕ+ => (modeIdx ij.1, ij.2)), KTN x = 0 :=
    fun x hx => by by_contra h; exact hx (sTN h)
  have hKTN' : Summable fun ij : Fin 2 × ℕ+ => KTN (modeIdx ij.1, ij.2) :=
    (ιTN.summable_iff zTN).2 hKTN
  have eTN : ∑' rs, KTN rs = ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then k (modeIdx i) j else 0) := by
    rw [← ιTN.tsum_eq sTN, hKTN'.tsum_prod, tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => tsum_congr fun j => ?_
    simp only [KTN]
    by_cases hj : 3 ≤ (j : ℕ)
    · rw [if_pos ⟨modeIdx_le_two i, hj⟩, if_pos hj]
    · rw [if_neg (fun h => hj h.2), if_neg hj]
  show ∑' rs, K rs = _
  rw [e1, e2, eTT, eTN]
  ring

theorem waveTriCoef_rsrs (r s : ℕ+) :
    waveTriCoef m hm r s r s =
      (1 / Real.pi + (if r = s then 1 / (2 * Real.pi) else 0)) / (lam m hm r * lam m hm s) := by
  unfold waveTriCoef waveQuartic
  rw [sineQuarticCoeff_pair_val_b]
  have hr := Real.mul_self_sqrt (wave_lam_pos m hm r).le
  have hs := Real.mul_self_sqrt (wave_lam_pos m hm s).le
  have : Real.sqrt (lam m hm r) * Real.sqrt (lam m hm s) * Real.sqrt (lam m hm r) *
      Real.sqrt (lam m hm s) = lam m hm r * lam m hm s := by
    calc _ = (Real.sqrt (lam m hm r) * Real.sqrt (lam m hm r)) *
          (Real.sqrt (lam m hm s) * Real.sqrt (lam m hm s)) := by ring
      _ = _ := by rw [hr, hs]
  rw [this]

theorem waveTriCoef_rsrs_comm (r s : ℕ+) :
    waveTriCoef m hm r s r s = waveTriCoef m hm s r s r := by
  rw [waveTriCoef_rsrs, waveTriCoef_rsrs]
  have : (r = s) ↔ (s = r) := eq_comm
  simp only [this]
  rw [mul_comm (lam m hm r)]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:quartic-ident`) For every `w ∈ 𝔚`, with `I_j = w_j w_{-j}`:
`Ḡ(w) = ½ Σ_{i,i'∈J} A_{ii'} I_i I_{i'} + Σ_{j ≥ 3, i ∈ J} B_{ji} I_i I_j` with the corrected `A`, `B`. -/
theorem birkQuartP_bar (w : BirkSpace) :
    birkQuartP m hm ha hp (birkCoefBar_isCoef m hm) w =
      (1 / 2 : ℂ) * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
          (birkAction a p w (modeIdx i) * birkAction a p w (modeIdx i')) +
        ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then
          (birkActionB m hm j i : ℂ) * (birkAction a p w (modeIdx i) * birkAction a p w j) else 0) := by
  have hc := birkCoefBar_isCoef m hm
  rw [birkQuartP_eq_sum_V m hm ha hp hc, birkV_sum_eq_six m hm]
  obtain ⟨hKs, hV⟩ := birkV_s0_eq m hm ha hp w
  rw [hV]
  set k : ℕ+ → ℕ+ → ℂ := fun r s => (1 + (if r = s then 0 else 1)) *
    ((waveTriCoef m hm r s r s : ℝ) : ℂ) * (birkAction a p w r * birkAction a p w s) with hk
  have hsym : ∀ r s, k r s = k s r := fun r s => by
    simp only [hk]
    rw [waveTriCoef_rsrs_comm m hm r s]
    have : (r = s) ↔ (s = r) := eq_comm
    simp only [this]
    ring
  have hK : (fun rs : ℕ+ × ℕ+ => birkKterm m hm a p w rs) =
      fun rs => if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0 := rfl
  have hsplit := tsum_tan_split k hsym (by rw [← hK]; exact hKs)
  have hKt : ∑' rs : ℕ+ × ℕ+, birkKterm m hm a p w rs =
      ∑' rs : ℕ+ × ℕ+, (if ((rs.1 : ℕ) ≤ 2 ∨ (rs.2 : ℕ) ≤ 2) then k rs.1 rs.2 else 0) := rfl
  rw [hKt, hsplit]
  -- termwise identities
  have hTT : ∀ i i' : Fin 2, (6 / 16 : ℂ) * k (modeIdx i) (modeIdx i') =
      (1 / 2 : ℂ) * ((actionA m hm i i' : ℂ) *
        (birkAction a p w (modeIdx i) * birkAction a p w (modeIdx i'))) := fun i i' => by
    have hi := wave_lam_pos m hm (modeIdx i)
    have hi' := wave_lam_pos m hm (modeIdx i')
    simp only [hk, waveTriCoef_rsrs, actionA, lamTan_eq]
    show (6 / 16 : ℂ) * ((1 + (if modeIdx i = modeIdx i' then 0 else 1)) * ((_ : ℝ) : ℂ) * _) = _
    by_cases h : i = i'
    · subst h
      simp only [ite_true]
      push_cast
      field_simp
      ring
    · have h' : modeIdx i ≠ modeIdx i' := fun e => h (modeIdx_injective e)
      simp only [h, h', ite_false]
      push_cast
      field_simp
      ring
  have hTN : ∀ (i : Fin 2) (j : ℕ+), 3 ≤ (j : ℕ) → (6 / 16 : ℂ) * (2 * k (modeIdx i) j) =
      (birkActionB m hm j i : ℂ) * (birkAction a p w (modeIdx i) * birkAction a p w j) := fun i j hj => by
    have hi := wave_lam_pos m hm (modeIdx i)
    have hj' := wave_lam_pos m hm j
    have hne : modeIdx i ≠ j := fun e => by
      have := modeIdx_le_two i; rw [e] at this; omega
    simp only [hk, waveTriCoef_rsrs, birkActionB, hne, ite_false, lamTan_eq]
    push_cast
    field_simp
    ring
  have e1 : (6 / 16 : ℂ) * ∑ i : Fin 2, ∑ i' : Fin 2, k (modeIdx i) (modeIdx i') =
      (1 / 2 : ℂ) * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        (birkAction a p w (modeIdx i) * birkAction a p w (modeIdx i')) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => hTT i i'
  have e2 : (6 / 16 : ℂ) * (2 * ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then k (modeIdx i) j else 0)) =
      ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then
        (birkActionB m hm j i : ℂ) * (birkAction a p w (modeIdx i) * birkAction a p w j) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    by_cases hj : 3 ≤ (j : ℕ)
    · simp only [hj, ite_true]; exact hTN i j hj
    · simp only [hj, ite_false]; ring
  calc (1 / 16 : ℂ) * (6 * (∑ i : Fin 2, ∑ i' : Fin 2, k (modeIdx i) (modeIdx i') +
        2 * ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then k (modeIdx i) j else 0)))
      = (6 / 16 : ℂ) * ∑ i : Fin 2, ∑ i' : Fin 2, k (modeIdx i) (modeIdx i') +
        (6 / 16 : ℂ) * (2 * ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then k (modeIdx i) j else 0)) := by
        ring
    _ = _ := by rw [e1, e2]

end

/-! ### The decomposition `G = G^{tan} + G^{nor}` -/

/-- The coefficient `𝔤 · 1_𝒯` of `G^{tan}`. -/
def birkCoefTan : (Fin 4 → BirkIdx) → ℂ := birkQuartCoefOn m hm birkTanSet

theorem birkCoefTan_isCoef : IsBirkQuartCoef m hm (birkCoefTan m hm) :=
  isBirkQuartCoef_on m hm birkTanSet
    (fun σ x ⟨t, ht⟩ => ⟨σ.symm t, by simpa using ht⟩)
    (fun x ⟨t, ht⟩ => ⟨t, by simpa [birkNegPi] using ht⟩)

theorem birkCoefAll_eq_tan_add_nor (x : Fin 4 → BirkIdx) :
    birkCoefAll m hm x = birkCoefTan m hm x + birkCoefNor m hm x := by
  classical
  unfold birkCoefAll birkCoefTan birkCoefNor birkQuartCoefOn
  by_cases h : x ∈ birkTanSet
  · have : x ∉ birkNormalSet := fun hn => by
      obtain ⟨t, ht⟩ := h; have := hn t; omega
    simp [h, this]
  · have : x ∈ birkNormalSet := fun t => by
      by_contra hlt; exact h ⟨t, by omega⟩
    simp [h, this]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:quartic`) `G = G^{tan} + G^{nor}` as functions on `𝔚`. -/
theorem birkQuartP_all_eq_tan_add_nor (w : BirkSpace) :
    birkQuartP m hm ha hp (birkCoefAll_isCoef m hm) w =
      birkQuartP m hm ha hp (birkCoefTan_isCoef m hm) w +
        birkQuartP m hm ha hp (birkCoefNor_isCoef m hm) w := by
  unfold birkQuartP birkDiag
  rw [birkQuartForm_apply, birkQuartForm_apply, birkQuartForm_apply, ← mul_add]
  congr 1
  unfold birkQuartSum
  rw [← Summable.tsum_add (summable_birkQuartTerm m hm ha hp (birkCoefTan_isCoef m hm).bound
    (fun _ => w)).of_norm
    (summable_birkQuartTerm m hm ha hp (birkCoefNor_isCoef m hm).bound (fun _ => w)).of_norm]
  refine tsum_congr fun x => ?_
  rw [birkCoefAll_eq_tan_add_nor, add_mul]

end

end KAM.Wave

end
