/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieSeq

/-!
# Derivatives of the Lie coefficients (blueprint-W `bpW:w3:leibniz`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:leibniz`.

`lieDer T w k = Dφ_k(w)` is given by the product rule
`(k+1) Dφ_{k+1}(w) = Σ_{a+b+c=k} Σ_i T(φ_a,…,Dφ_{x_i} ·,…)` (`lieDer_succ`); `hasFDerivAt_lieSeq`
shows it is the Fréchet derivative, and `norm_lieDer_le`: `‖Dφ_k(w)‖ ≤ (2k+1) m_k C^k ‖w‖^{2k}`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

theorem lieVec_eq (f : ℕ → E) (x : Fin 3 → ℕ) :
    (![f (x 0), f (x 1), f (x 2)] : Fin 3 → E) = fun j => f (x j) := by
  funext j; fin_cases j <;> rfl

/-- `Dφ_k(w)`. -/
def lieDer (w : E) : ℕ → (E →L[ℂ] E)
  | 0 => ContinuousLinearMap.id ℂ E
  | k + 1 => ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 k).attach, ∑ i : Fin 3,
        (T.toContinuousLinearMap (fun j => lieSeq T w (x.1 j)) i).comp (lieDer w (x.1 i))
decreasing_by
  have h := Finset.Nat.mem_antidiagonalTuple.1 x.2
  simp only [Fin.sum_univ_three] at h
  fin_cases i <;> simp <;> omega

theorem lieDer_succ (w : E) (k : ℕ) :
    lieDer T w (k + 1) = ((1 : ℂ) / ((k : ℂ) + 1)) •
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, ∑ i : Fin 3,
        (T.toContinuousLinearMap (fun j => lieSeq T w (x j)) i).comp (lieDer T w (x i)) := by
  rw [lieDer]
  congr 1
  exact sum_attach (Finset.Nat.antidiagonalTuple 3 k)
    (fun x => ∑ i : Fin 3, (T.toContinuousLinearMap (fun j => lieSeq T w (x j)) i).comp
      (lieDer T w (x i)))

@[simp] theorem lieDer_zero (w : E) : lieDer T w 0 = ContinuousLinearMap.id ℂ E := by rw [lieDer]

/-- `D φ_k(w)` is the Fréchet derivative of `w ↦ φ_k(w)`. -/
theorem hasFDerivAt_lieSeq (k : ℕ) (w : E) :
    HasFDerivAt (fun w => lieSeq T w k) (lieDer T w k) w := by
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [lieSeq_zero, lieDer_zero]
      exact hasFDerivAt_id w
    | succ k =>
      have hterm : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 k,
          HasFDerivAt (fun w => T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)])
            (∑ i : Fin 3, (T.toContinuousLinearMap (fun j => lieSeq T w (x j)) i).comp
              (lieDer T w (x i))) w := fun x hx => by
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        have h := HasFDerivAt.multilinear_comp (f := T) (g := fun (j : Fin 3) w => lieSeq T w (x j))
          (g' := fun j => lieDer T w (x j)) (x := w) (fun j => ih (x j) (by
            fin_cases j <;> simp <;> omega) w)
        simpa [lieVec_eq] using h
      have h := (HasFDerivAt.fun_sum hterm).const_smul ((1 : ℂ) / ((k : ℂ) + 1))
      have e : (fun w => lieSeq T w (k + 1)) = fun w => ((1 : ℂ) / ((k : ℂ) + 1)) •
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
            T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)] := by
        funext w; exact lieSeq_succ T w k
      rw [e, lieDer_succ]
      exact h

/-- The partial maps of a trilinear form: `‖T(…,v,…)‖ ≤ C ‖v‖ ∏_{j ≠ i} ‖m j‖`, i.e. the three
cases. -/
theorem norm_toCLM_le {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)
    (m : Fin 3 → E) (v : E) :
    ‖T.toContinuousLinearMap m 0 v‖ ≤ C * (‖v‖ * ‖m 1‖ * ‖m 2‖) ∧
    ‖T.toContinuousLinearMap m 1 v‖ ≤ C * (‖m 0‖ * ‖v‖ * ‖m 2‖) ∧
    ‖T.toContinuousLinearMap m 2 v‖ ≤ C * (‖m 0‖ * ‖m 1‖ * ‖v‖) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have := hT (Function.update m 0 v)
    simpa [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] using this
  · have := hT (Function.update m 1 v)
    simpa [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] using this
  · have := hT (Function.update m 2 v)
    simpa [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] using this

theorem opNorm_toCLM_le {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)
    (m : Fin 3 → E) :
    ‖T.toContinuousLinearMap m 0‖ ≤ C * (‖m 1‖ * ‖m 2‖) ∧
    ‖T.toContinuousLinearMap m 1‖ ≤ C * (‖m 0‖ * ‖m 2‖) ∧
    ‖T.toContinuousLinearMap m 2‖ ≤ C * (‖m 0‖ * ‖m 1‖) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := norm_toCLM_le T hC hT m v
    first
      | (have h := this.1; nlinarith [h])
      | (have h := this.2.1; nlinarith [h])
      | (have h := this.2.2; nlinarith [h])

/-- `‖Dφ_k(w)‖ ≤ (2k+1) m_k C^k ‖w‖^{2k}`. -/
theorem norm_lieDer_le {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)
    (w : E) (k : ℕ) :
    ‖lieDer T w k‖ ≤ (2 * k + 1) * birkLieM k * C ^ k * ‖w‖ ^ (2 * k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [lieDer_zero, birkLieM, Nat.cast_zero, mul_zero, zero_add, mul_one, pow_zero,
        one_mul]
      exact ContinuousLinearMap.norm_id_le
    | succ k =>
      rw [lieDer_succ, norm_smul]
      have hk : ‖((1 : ℂ) / ((k : ℂ) + 1))‖ = 1 / ((k : ℝ) + 1) := by
        rw [norm_div, norm_one]
        congr 1
        have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hk]
      set r := ‖w‖ with hr
      have hr0 : 0 ≤ r := norm_nonneg w
      -- bound for each `x`
      have hx : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 k,
          ‖∑ i : Fin 3, (T.toContinuousLinearMap (fun j => lieSeq T w (x j)) i).comp
            (lieDer T w (x i))‖ ≤ (2 * (k : ℝ) + 3) * (birkLieM (x 0) * birkLieM (x 1) *
              birkLieM (x 2)) * C ^ (k + 1) * r ^ (2 * k + 2) := fun x hx => by
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        have u0 := norm_lieSeq_le T hC hT w (x 0)
        have u1 := norm_lieSeq_le T hC hT w (x 1)
        have u2 := norm_lieSeq_le T hC hT w (x 2)
        have d0 := ih (x 0) (by omega)
        have d1 := ih (x 1) (by omega)
        have d2 := ih (x 2) (by omega)
        have m0 := birkLieM_nonneg (x 0)
        have m1 := birkLieM_nonneg (x 1)
        have m2 := birkLieM_nonneg (x 2)
        have ops := opNorm_toCLM_le T hC hT (fun j => lieSeq T w (x j))
        simp only [Fin.sum_univ_three]
        refine (norm_add₃_le).trans ?_
        have b0 : ‖(T.toContinuousLinearMap (fun j => lieSeq T w (x j)) 0).comp (lieDer T w (x 0))‖
            ≤ C * (‖lieSeq T w (x 1)‖ * ‖lieSeq T w (x 2)‖) * ‖lieDer T w (x 0)‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right ops.1 (norm_nonneg _))
        have b1 : ‖(T.toContinuousLinearMap (fun j => lieSeq T w (x j)) 1).comp (lieDer T w (x 1))‖
            ≤ C * (‖lieSeq T w (x 0)‖ * ‖lieSeq T w (x 2)‖) * ‖lieDer T w (x 1)‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right ops.2.1 (norm_nonneg _))
        have b2 : ‖(T.toContinuousLinearMap (fun j => lieSeq T w (x j)) 2).comp (lieDer T w (x 2))‖
            ≤ C * (‖lieSeq T w (x 0)‖ * ‖lieSeq T w (x 1)‖) * ‖lieDer T w (x 2)‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right ops.2.2 (norm_nonneg _))
        have pC : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
          rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
        have pr0 : r ^ (2 * k + 2) = r ^ (2 * x 0) * r ^ (2 * x 1 + 1) * r ^ (2 * x 2 + 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        have pr1 : r ^ (2 * k + 2) = r ^ (2 * x 0 + 1) * r ^ (2 * x 1) * r ^ (2 * x 2 + 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        have pr2 : r ^ (2 * k + 2) = r ^ (2 * x 0 + 1) * r ^ (2 * x 1 + 1) * r ^ (2 * x 2) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        have t0 : C * (‖lieSeq T w (x 1)‖ * ‖lieSeq T w (x 2)‖) * ‖lieDer T w (x 0)‖ ≤
            (2 * (x 0 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
              C ^ (k + 1) * r ^ (2 * k + 2) := by
          rw [pC, pr0]
          calc _ ≤ C * ((birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1 + 1)) *
                (birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2 + 1))) *
                ((2 * (x 0 : ℝ) + 1) * birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0)) := by
                gcongr
            _ = _ := by ring
        have t1 : C * (‖lieSeq T w (x 0)‖ * ‖lieSeq T w (x 2)‖) * ‖lieDer T w (x 1)‖ ≤
            (2 * (x 1 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
              C ^ (k + 1) * r ^ (2 * k + 2) := by
          rw [pC, pr1]
          calc _ ≤ C * ((birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0 + 1)) *
                (birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2 + 1))) *
                ((2 * (x 1 : ℝ) + 1) * birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1)) := by
                gcongr
            _ = _ := by ring
        have t2 : C * (‖lieSeq T w (x 0)‖ * ‖lieSeq T w (x 1)‖) * ‖lieDer T w (x 2)‖ ≤
            (2 * (x 2 : ℝ) + 1) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
              C ^ (k + 1) * r ^ (2 * k + 2) := by
          rw [pC, pr2]
          calc _ ≤ C * ((birkLieM (x 0) * C ^ x 0 * r ^ (2 * x 0 + 1)) *
                (birkLieM (x 1) * C ^ x 1 * r ^ (2 * x 1 + 1))) *
                ((2 * (x 2 : ℝ) + 1) * birkLieM (x 2) * C ^ x 2 * r ^ (2 * x 2)) := by
                gcongr
            _ = _ := by ring
        have hs : ((x 0 : ℝ)) + x 1 + x 2 = k := by exact_mod_cast hx'
        calc _ ≤ _ := add_le_add (add_le_add (b0.trans t0) (b1.trans t1)) (b2.trans t2)
          _ = (2 * (k : ℝ) + 3) * (birkLieM (x 0) * birkLieM (x 1) * birkLieM (x 2)) *
              C ^ (k + 1) * r ^ (2 * k + 2) := by
            have : (2 * (x 0 : ℝ) + 1) + (2 * (x 1 : ℝ) + 1) + (2 * (x 2 : ℝ) + 1) =
              2 * (k : ℝ) + 3 := by linarith
            rw [← this]; ring
      refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hx))
        (by positivity)).trans ?_
      rw [← sum_mul, ← sum_mul, ← mul_sum, ← birkLieM_succ' k]
      refine le_of_eq ?_
      push_cast
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      field_simp
      ring

end KAM.Wave

end
