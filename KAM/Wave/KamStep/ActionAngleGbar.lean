/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleNormal
public import KAM.Wave.Birkhoff.QuartMain
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coordinates of `X_Ḡ` (blueprint-W `bpW:w5:action-angle` (v), step `a-conj`, support)

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (v) (support for the conjugacy identity).

For every `w' ∈ 𝔚` (no reality assumption), with `I_k = w'_k w'_{-k}` and
`R_i = Σ_{J ≥ 3} B_{J i} I_J` (`aaGbarR`), from `Ḡ = ½⟨AI, I⟩ + Σ_i I_i R_i` (`birkHamBar_eq_aa`,
W3's `birkQuartP_bar`) and `X(w')_l = -i sgn(l) DḠ(w') e_{-l}` (`birkField_coord`):
* `birkCoord_birkHamBarX_tan`: `X_Ḡ(w')_{±i} = ∓ i w'_{±i} ((AI)_i + R_i)`;
* `birkCoord_birkHamBarX_nor`: `X_Ḡ(w')_{±J} = ∓ i w'_{±J} Σ_i B_{J i} I_i` (`J ≥ 3`).
The derivatives `DḠ(w') e_{-l}` are computed along the complex line `t ↦ w' + t e_{-l}`, on which
only `I_{|l|}` changes, by `t w'_l`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

variable (m : ℝ) (hm : 0 < m)

/-- `R_i(w') = Σ_{J ≥ 3} B_{J i} I_J(w')`. -/
def aaGbarR (a p : ℝ) (w' : BirkSpace) (i : Fin 2) : ℂ :=
  ∑' J : ℕ+, if 3 ≤ (J : ℕ) then (birkActionB m hm J i : ℂ) * birkAction a p w' J else 0

variable {m hm} {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

theorem birkHamBar_eq_aa (w' : BirkSpace) :
    birkHamBar m hm ha hp w' = 1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        (birkAction a p w' (modeIdx i) * birkAction a p w' (modeIdx i')) +
      ∑ i : Fin 2, birkAction a p w' (modeIdx i) * aaGbarR m hm a p w' i := by
  rw [birkHamBar, birkQuartP_bar]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aaGbarR, ← tsum_mul_left]
  refine tsum_congr fun J => ?_
  split_ifs <;> ring

theorem norm_birkActionB_le (J : ℕ+) (i : Fin 2) : ‖(birkActionB m hm J i : ℂ)‖ ≤ 1 := by
  have h1 := aa_one_le_lam (m := m) (hm := hm) J
  have h2 : (1 : ℝ) ≤ lamTan m hm i := aa_one_le_lam _
  have hpi := Real.pi_gt_three
  rw [Complex.norm_real, Real.norm_eq_abs, birkActionB, abs_of_pos (by positivity),
    div_le_one (by positivity)]
  nlinarith [mul_le_mul h1 h2 zero_le_one (by linarith)]

include ha hp in
theorem norm_birkAction_le (w' : BirkSpace) (J : ℕ+) :
    ‖birkAction a p w' J‖ ≤ ‖w' (true, J)‖ * ‖w' (false, J)‖ := by
  unfold birkAction
  rw [norm_mul]
  exact mul_le_mul (norm_birkCoord_le ha (by linarith) _ _) (norm_birkCoord_le ha (by linarith) _ _)
    (norm_nonneg _) (norm_nonneg _)

include ha hp in
theorem summable_aaGbarR (w' : BirkSpace) (i : Fin 2) (c : ℕ+ → ℂ) (hc : ∀ J, ‖c J‖ ≤ 1) :
    Summable fun J : ℕ+ => if 3 ≤ (J : ℕ) then c J * birkAction a p w' J else 0 := by
  refine Summable.of_norm_bounded (birkHalf_summable w' w').1 fun J => ?_
  split_ifs
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc J)).trans (norm_birkAction_le ha hp w' J)
  · rw [norm_zero]; positivity

/-! ### The line `t ↦ w' + t e_{-l}` -/

theorem birkCoord_add_unit (w' : BirkSpace) (t : ℂ) (l l' : BirkIdx) :
    birkCoord a p (w' + t • birkUnit a p l) l' =
      birkCoord a p w' l' + t * (if l' = l then 1 else 0) := by
  rw [birkCoord_add, birkCoord_smul, birkCoord_birkUnit]

theorem birkAction_add_unit (w' : BirkSpace) (l : BirkIdx) (t : ℂ) (k : ℕ+) :
    birkAction a p (w' + t • birkUnit a p (birkNeg l)) k =
      birkAction a p w' k + if k = l.2 then t * birkCoord a p w' l else 0 := by
  obtain ⟨b, K⟩ := l
  unfold birkAction
  rw [birkCoord_add_unit, birkCoord_add_unit]
  by_cases hk : k = K
  · subst hk
    cases b <;> simp [birkNeg] <;> ring
  · have h1 : ((true, k) : BirkIdx) ≠ birkNeg (b, K) := fun h => hk (congrArg Prod.snd h)
    have h2 : ((false, k) : BirkIdx) ≠ birkNeg (b, K) := fun h => hk (congrArg Prod.snd h)
    simp [h1, h2, hk]

include ha hp in
theorem hasDerivAt_birkHamBar_line (w' v : BirkSpace) :
    HasDerivAt (fun t : ℂ => birkHamBar m hm ha hp (w' + t • v))
      (fderiv ℂ (birkHamBar m hm ha hp) w' v) 0 := by
  have hG : DifferentiableAt ℂ (birkHamBar m hm ha hp) w' :=
    ((birkQuart_isClassA m hm ha hp (birkCoefBar_isCoef m hm)).analytic w' trivial).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => w' + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add w'
  have := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  exact this

/-- `DḠ(w') e_{-l}` at a tangential `l = (b, i₀)`. -/
theorem fderiv_birkHamBar_tan (w' : BirkSpace) (b : Bool) (i₀ : Fin 2) :
    fderiv ℂ (birkHamBar m hm ha hp) w' (birkUnit a p (birkNeg (b, modeIdx i₀))) =
      birkCoord a p w' (b, modeIdx i₀) * (∑ i' : Fin 2, (actionA m hm i₀ i' : ℂ) *
        birkAction a p w' (modeIdx i') + aaGbarR m hm a p w' i₀) := by
  set v := birkUnit a p (birkNeg (b, modeIdx i₀))
  set c := birkCoord a p w' (b, modeIdx i₀)
  set I : Fin 2 → ℂ := fun i => birkAction a p w' (modeIdx i)
  set d : Fin 2 → ℂ := fun i => if i = i₀ then c else 0
  have hI : ∀ (t : ℂ) (i : Fin 2), birkAction a p (w' + t • v) (modeIdx i) = I i + t * d i :=
    fun t i => by
      rw [birkAction_add_unit]
      simp only [I, d, (modeIdx_injective (N := 2)).eq_iff]
      split_ifs <;> ring
  have hR : ∀ (t : ℂ) (i : Fin 2), aaGbarR m hm a p (w' + t • v) i = aaGbarR m hm a p w' i :=
    fun t i => by
      unfold aaGbarR
      refine tsum_congr fun J => ?_
      by_cases h3 : 3 ≤ (J : ℕ)
      · have hJ : J ≠ modeIdx i₀ := fun h => by
          subst h; simp [modeIdx] at h3; have := i₀.is_lt; omega
        rw [if_pos h3, if_pos h3, birkAction_add_unit, if_neg hJ, add_zero]
      · rw [if_neg h3, if_neg h3]
  have hg : (fun t : ℂ => birkHamBar m hm ha hp (w' + t • v)) = fun t =>
      1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        ((I i + t * d i) * (I i' + t * d i')) +
      ∑ i : Fin 2, (I i + t * d i) * aaGbarR m hm a p w' i := by
    funext t
    rw [birkHamBar_eq_aa]
    simp only [hI, hR]
  have hD := hasDerivAt_birkHamBar_line (m := m) (hm := hm) ha hp w' v
  rw [hg] at hD
  have hP : HasDerivAt (fun t : ℂ =>
      1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        ((I i + t * d i) * (I i' + t * d i')) +
      ∑ i : Fin 2, (I i + t * d i) * aaGbarR m hm a p w' i)
      (1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        (d i * (I i' + 0 * d i') + (I i + 0 * d i) * d i') +
        ∑ i : Fin 2, d i * aaGbarR m hm a p w' i) 0 := by
    have hl : ∀ i, HasDerivAt (fun t : ℂ => I i + t * d i) (d i) 0 := fun i => by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (d i)).const_add (I i)
    refine HasDerivAt.add ?_ ?_
    · refine HasDerivAt.const_mul _ ?_
      refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun i' _ => ?_
      exact ((hl i).mul (hl i')).const_mul _
    · exact HasDerivAt.fun_sum fun i _ => (hl i).mul_const _
  rw [hD.unique hP]
  have h01 := actionA_symm (m := m) (hm := hm) 1 0
  simp only [Fin.sum_univ_two, d, I]
  fin_cases i₀ <;> simp <;> rw [h01] <;> ring

/-- `DḠ(w') e_{-l}` at a normal `l = (b, j + 2)`. -/
theorem fderiv_birkHamBar_nor (w' : BirkSpace) (b : Bool) (j : ℕ+) :
    fderiv ℂ (birkHamBar m hm ha hp) w' (birkUnit a p (birkNeg (b, j + 2))) =
      birkCoord a p w' (b, j + 2) * ∑ i : Fin 2, (birkActionB m hm (j + 2) i : ℂ) *
        birkAction a p w' (modeIdx i) := by
  set v := birkUnit a p (birkNeg (b, j + 2))
  set c := birkCoord a p w' (b, j + 2)
  set I : Fin 2 → ℂ := fun i => birkAction a p w' (modeIdx i)
  have hI : ∀ (t : ℂ) (i : Fin 2), birkAction a p (w' + t • v) (modeIdx i) = I i :=
    fun t i => by
      rw [birkAction_add_unit, if_neg (modeIdx_ne_add_two i j), add_zero]
  have hR : ∀ (t : ℂ) (i : Fin 2), aaGbarR m hm a p (w' + t • v) i =
      aaGbarR m hm a p w' i + t * c * (birkActionB m hm (j + 2) i : ℂ) := fun t i => by
    unfold aaGbarR
    have h3 : 3 ≤ ((j + 2 : ℕ+) : ℕ) := by rw [PNat.add_coe]; simp; exact j.pos
    have hs1 := summable_aaGbarR ha hp w' i (fun J : ℕ+ => (birkActionB m hm J i : ℂ))
      (fun J => norm_birkActionB_le J i)
    have hsplit : (fun J : ℕ+ => if 3 ≤ (J : ℕ) then (birkActionB m hm J i : ℂ) *
        birkAction a p (w' + t • v) J else 0) = fun J : ℕ+ =>
          (if 3 ≤ (J : ℕ) then (birkActionB m hm J i : ℂ) * birkAction a p w' J else 0) +
            (if J = j + 2 then t * c * (birkActionB m hm (j + 2) i : ℂ) else 0) := by
      funext J
      rw [birkAction_add_unit]
      by_cases hJ : J = j + 2
      · subst hJ; simp only [h3, if_true]; simp [birkNeg, c]; ring
      · by_cases h : 3 ≤ (J : ℕ) <;> simp [h, hJ]
    rw [hsplit, hs1.tsum_add (summable_of_ne_finset_zero (s := {j + 2}) fun J hJ => by
      simp only [Finset.mem_singleton] at hJ; simp [hJ]), tsum_ite_eq]
  have hg : (fun t : ℂ => birkHamBar m hm ha hp (w' + t • v)) = fun t =>
      1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) * (I i * I i') +
      ∑ i : Fin 2, I i * (aaGbarR m hm a p w' i + t * c * (birkActionB m hm (j + 2) i : ℂ)) := by
    funext t
    rw [birkHamBar_eq_aa]
    simp only [hI, hR]
  have hD := hasDerivAt_birkHamBar_line (m := m) (hm := hm) ha hp w' v
  rw [hg] at hD
  have hS : HasDerivAt (fun t : ℂ =>
      ∑ i : Fin 2, I i * (aaGbarR m hm a p w' i + t * c * (birkActionB m hm (j + 2) i : ℂ)))
      (∑ i : Fin 2, I i * (c * (birkActionB m hm (j + 2) i : ℂ))) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul _ ?_
    have := ((hasDerivAt_id (0 : ℂ)).mul_const (c * (birkActionB m hm (j + 2) i : ℂ))).const_add
      (aaGbarR m hm a p w' i)
    simpa [mul_assoc] using this
  have hP := (hasDerivAt_const (0 : ℂ) (1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2,
    (actionA m hm i i' : ℂ) * (I i * I i'))).add hS
  rw [hD.unique hP, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-! ### The coordinates of `X_Ḡ` -/

theorem birkHamBar_hamField :
    IsBirkHamFieldPlus a p ha (by linarith) Set.univ (birkHamBar m hm ha hp)
      (birkHamBarX m hm ha hp) :=
  (birkQuart_isClassA m hm ha hp (birkCoefBar_isCoef m hm)).hamField

/-- (`bpW:w5:action-angle` (v), support) `X_Ḡ(w')_{(b,i)} = -i sgn w'_{(b,i)} ((AI)_i + R_i)`. -/
theorem birkCoord_birkHamBarX_tan (w' : BirkSpace) (b : Bool) (i₀ : Fin 2) :
    birkCoord a (p + 1) (birkHamBarX m hm ha hp w') (b, modeIdx i₀) =
      -I * birkSgn (b, modeIdx i₀) * birkCoord a p w' (b, modeIdx i₀) *
        (∑ i' : Fin 2, (actionA m hm i₀ i' : ℂ) * birkAction a p w' (modeIdx i') +
          aaGbarR m hm a p w' i₀) := by
  rw [birkField_coord (birkHamBar_hamField ha hp) trivial, fderiv_birkHamBar_tan ha hp]
  ring

/-- (`bpW:w5:action-angle` (v), support) `X_Ḡ(w')_{(b,J)} = -i sgn w'_{(b,J)} Σ_i B_{J i} I_i`. -/
theorem birkCoord_birkHamBarX_nor (w' : BirkSpace) (b : Bool) (j : ℕ+) :
    birkCoord a (p + 1) (birkHamBarX m hm ha hp w') (b, j + 2) =
      -I * birkSgn (b, j + 2) * birkCoord a p w' (b, j + 2) *
        ∑ i : Fin 2, (birkActionB m hm (j + 2) i : ℂ) * birkAction a p w' (modeIdx i) := by
  rw [birkField_coord (birkHamBar_hamField ha hp) trivial, fderiv_birkHamBar_nor ha hp]
  ring

end KAM.Wave

end
