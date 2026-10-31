/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LiePlusNum
public import Mathlib.Analysis.Analytic.Basic

/-!
# Block composition of multilinear maps (blueprint-W `bpW:w3:lie-coeff`, Step Rec)

Package W3-FLOW, blueprint label `bpW:w3:lie-coeff`.

`lieBlock R f P h`: for a continuous trilinear `R : E³ → G` and continuous multilinear
`P j : E^{2 f_j + 1} → E`, the continuous multilinear map `E^n → G`,
`(v) ↦ R(P_0(v|block 0), P_1(v|block 1), P_2(v|block 2))` (`n = Σ_j (2 f_j + 1)`), with
`‖lieBlock R f P h‖ ≤ ‖R‖ ∏ ‖P_j‖` (`norm_lieBlock_le`) and the diagonal formula
`lieBlock_const`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The index equivalence `(Σ j, Fin (2 f_j + 1)) ≃ Fin n`. -/
def lieBlockEquiv (f : Fin 3 → ℕ) (n : ℕ) (h : ∑ j, (2 * f j + 1) = n) :
    (Σ j : Fin 3, Fin (2 * f j + 1)) ≃ Fin n :=
  (finSigmaFinEquiv (n := fun j => 2 * f j + 1)).trans (finCongr h)

/-- `v ↦ R(P_0(v|₀), P_1(v|₁), P_2(v|₂))`. -/
def lieBlock (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) G) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ)
    (h : ∑ j, (2 * f j + 1) = n) : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G where
  toMultilinearMap :=
    (R.toMultilinearMap.compMultilinearMap (fun j => (P j).toMultilinearMap)).domDomCongr
      (lieBlockEquiv f n h)
  cont := by
    show Continuous fun v : Fin n → E =>
      R fun j => P j (fun b => v (lieBlockEquiv f n h ⟨j, b⟩))
    refine R.cont.comp (continuous_pi fun j => (P j).cont.comp (continuous_pi fun b => ?_))
    exact continuous_apply _

theorem lieBlock_apply (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) G) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ)
    (h : ∑ j, (2 * f j + 1) = n) (v : Fin n → E) :
    lieBlock R f P n h v =
      R fun j => P j (fun b => v (lieBlockEquiv f n h ⟨j, b⟩)) := rfl

theorem lieBlock_const (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) G) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ)
    (h : ∑ j, (2 * f j + 1) = n) (w : E) :
    lieBlock R f P n h (fun _ => w) = R fun j => P j (fun _ => w) := rfl

theorem norm_lieBlock_le (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) G) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ)
    (h : ∑ j, (2 * f j + 1) = n) :
    ‖lieBlock R f P n h‖ ≤ ‖R‖ * ∏ j, ‖P j‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [lieBlock_apply]
  refine (R.le_opNorm _).trans ?_
  have hb : ∀ j : Fin 3, ‖P j (fun b => v (lieBlockEquiv f n h ⟨j, b⟩))‖ ≤
      ‖P j‖ * ∏ b, ‖v (lieBlockEquiv f n h ⟨j, b⟩)‖ := fun j => (P j).le_opNorm _
  have hprod : ∏ j : Fin 3, ‖P j (fun b => v (lieBlockEquiv f n h ⟨j, b⟩))‖ ≤
      ∏ j : Fin 3, (‖P j‖ * ∏ b, ‖v (lieBlockEquiv f n h ⟨j, b⟩)‖) :=
    by gcongr with j hj; exact hb j
  have hsig : ∏ j : Fin 3, ∏ b, ‖v (lieBlockEquiv f n h ⟨j, b⟩)‖ = ∏ i : Fin n, ‖v i‖ := by
    rw [← Fintype.prod_sigma' (fun j b => ‖v (lieBlockEquiv f n h ⟨j, b⟩)‖)]
    exact Equiv.prod_comp (lieBlockEquiv f n h) (fun i => ‖v i‖)
  calc ‖R‖ * ∏ j : Fin 3, ‖P j (fun b => v (lieBlockEquiv f n h ⟨j, b⟩))‖
      ≤ ‖R‖ * ∏ j : Fin 3, (‖P j‖ * ∏ b, ‖v (lieBlockEquiv f n h ⟨j, b⟩)‖) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖R‖ * (∏ j, ‖P j‖) * ∏ i : Fin n, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, hsig]; ring

/-- `lieBlock` when the index count is right, `0` otherwise (a total version). -/
def lieBlockT (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) G) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G :=
  if h : ∑ j, (2 * f j + 1) = n then lieBlock R f P n h else 0

theorem sum_blocks {k : ℕ} {x : Fin 3 → ℕ} (hx : x ∈ Finset.Nat.antidiagonalTuple 3 k) :
    ∑ j, (2 * x j + 1) = 2 * (k + 1) + 1 := by
  have h := Finset.Nat.mem_antidiagonalTuple.1 hx
  simp only [Fin.sum_univ_three] at h ⊢
  omega

variable (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

/-- The Lie coefficients `Φ_k : E^{2k+1} → E`: `Φ_0 = id` and
`(k+1) Φ_{k+1} = Σ_{a+b+c=k} T(Φ_a, Φ_b, Φ_c)` (block composition). -/
def lieMulti : (k : ℕ) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * k + 1) => E) E
  | 0 => ContinuousMultilinearMap.ofSubsingleton ℂ E E (0 : Fin 1) (ContinuousLinearMap.id ℂ E)
  | k + 1 => ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 k).attach,
        lieBlockT T x.1 (fun j => lieMulti (x.1 j)) (2 * (k + 1) + 1)
decreasing_by
  have h := Finset.Nat.mem_antidiagonalTuple.1 x.2
  simp only [Fin.sum_univ_three] at h
  fin_cases j <;> simp <;> omega

theorem lieMulti_succ (k : ℕ) :
    lieMulti T (k + 1) = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
        lieBlockT T x (fun j => lieMulti T (x j)) (2 * (k + 1) + 1) := by
  rw [lieMulti]
  congr 1
  exact sum_attach (Finset.Nat.antidiagonalTuple 3 k)
    (fun x => lieBlockT T x (fun j => lieMulti T (x j)) (2 * (k + 1) + 1))

theorem lieMulti_const (w : E) (k : ℕ) : lieMulti T k (fun _ => w) = lieSeq T w k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [lieMulti, lieSeq]
    | succ k =>
      rw [lieMulti_succ, lieSeq_succ]
      simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      rw [lieBlockT, dif_pos (sum_blocks hx), lieBlock_const, lieVec_eq]
      congr 1
      funext j
      exact ih (x j) (by fin_cases j <;> simp <;> omega)

theorem norm_lieMulti_le {C : ℝ} (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) (k : ℕ) :
    ‖lieMulti T k‖ ≤ birkLieM k * C ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [lieMulti, birkLieM, pow_zero, mul_one]
      exact ContinuousMultilinearMap.norm_ofSubsingleton_id_le ℂ E (0 : Fin 1)
    | succ k =>
      rw [lieMulti_succ]
      have := lie_step_A (G := ContinuousMultilinearMap ℂ (fun _ : Fin (2 * (k + 1) + 1) => E) E)
        k C 1 (fun x => lieBlockT T x (fun j => lieMulti T (x j)) (2 * (k + 1) + 1))
        (fun x hx => ?_)
      · simpa using this
      · have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        rw [lieBlockT, dif_pos (sum_blocks hx)]
        refine (norm_lieBlock_le T x _ _ _).trans ?_
        simp only [Fin.prod_univ_three, one_pow, mul_one]
        have u0 := ih (x 0) (by omega)
        have u1 := ih (x 1) (by omega)
        have u2 := ih (x 2) (by omega)
        have m0 := birkLieM_nonneg (x 0)
        have m1 := birkLieM_nonneg (x 1)
        have m2 := birkLieM_nonneg (x 2)
        have hb : ‖lieMulti T (x 0)‖ * ‖lieMulti T (x 1)‖ * ‖lieMulti T (x 2)‖ ≤
            (birkLieM (x 0) * C ^ x 0) * (birkLieM (x 1) * C ^ x 1) *
              (birkLieM (x 2) * C ^ x 2) :=
          mul_le_mul (mul_le_mul u0 u1 (norm_nonneg _) (by positivity)) u2 (norm_nonneg _)
            (by positivity)
        refine (mul_le_mul hT hb (by positivity) hC).trans (le_of_eq ?_)
        have : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
          rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
        rw [this]; ring

end KAM.Wave

end
