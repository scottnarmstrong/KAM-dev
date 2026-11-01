/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieFlow3

/-!
# The flow `Γ_t`: the flow equation (blueprint-W `bpW:w3:flow` (ii))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`hasSum_lieCauchy`: the trilinear Cauchy product
`T(Γ_t w, Γ_t w, Γ_t w) = Σ_n t^n Σ_{a+b+c=n} T(φ_a, φ_b, φ_c)`;
`hasDerivAt_lieGamma_flow`: `∂_t Γ_t(w) = T(Γ_t w, Γ_t w, Γ_t w)`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}

/-- `(Fin 3 → ℕ) ≃ ℕ × ℕ × ℕ`. -/
def lieTupleEquiv : (Fin 3 → ℕ) ≃ ℕ × ℕ × ℕ where
  toFun x := (x 0, x 1, x 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem lie_tri_smul (a b c : ℝ) (u v w : E) :
    T ![a • u, b • v, c • w] = (a * b * c) • T ![u, v, w] := by
  have h := T.map_smul_univ ![(a : ℂ), (b : ℂ), (c : ℂ)] ![u, v, w]
  have e : (fun i => ![(a : ℂ), (b : ℂ), (c : ℂ)] i • (![u, v, w] : Fin 3 → E) i) =
      ![a • u, b • v, c • w] := by
    funext i; fin_cases i <;> simp [Complex.coe_smul]
  rw [e] at h
  rw [h, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [← Complex.coe_smul]; push_cast; rfl

theorem lie_clm_apply2 (u v x : E) : T.toContinuousLinearMap ![u, v, 0] 2 x = T ![u, v, x] := by
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1; funext i; fin_cases i <;> simp [Function.update]

theorem lie_clm_apply1 (u v x : E) : T.toContinuousLinearMap ![u, 0, v] 1 x = T ![u, x, v] := by
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1; funext i; fin_cases i <;> simp [Function.update]

theorem lie_clm_apply0 (u v x : E) : T.toContinuousLinearMap ![0, u, v] 0 x = T ![x, u, v] := by
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1; funext i; fin_cases i <;> simp [Function.update]

variable (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem hasSum_lieCauchy (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    HasSum (fun n : ℕ => (t ^ n) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)])
      (T ![lieGamma T t w, lieGamma T t w, lieGamma T t w]) := by
  set f : ℕ → E := fun k => (t ^ k) • lieSeq T w k with hfdef
  have hf : Summable f := summable_lieTerm T hC hT t w hq
  have hfn : Summable fun k => ‖f k‖ := summable_norm_lieTerm T hC hT t w hq
  set g : ℕ × ℕ × ℕ → E := fun p => T ![f p.1, f p.2.1, f p.2.2] with hgdef
  have hbound : ∀ p, ‖g p‖ ≤ C * (‖f p.1‖ * (‖f p.2.1‖ * ‖f p.2.2‖)) := fun p => by
    have := hT ![f p.1, f p.2.1, f p.2.2]
    simpa [Fin.prod_univ_three, mul_assoc] using this
  have hgn : Summable fun p => ‖g p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
    exact (hfn.mul_of_nonneg (hfn.mul_of_nonneg hfn (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)) (fun _ => norm_nonneg _) (fun _ => mul_nonneg (norm_nonneg _)
        (norm_nonneg _))).mul_left C
  have hg : Summable g := hgn.of_norm
  have hG : Summable fun x : Fin 3 → ℕ => T ![f (x 0), f (x 1), f (x 2)] :=
    (lieTupleEquiv.summable_iff (f := g)).2 hg
  have hval : ∑' p, g p = T ![lieGamma T t w, lieGamma T t w, lieGamma T t w] := by
    rw [hg.tsum_prod' (fun i => hg.prod_factor i)]
    have e1 : ∀ i, ∑' q : ℕ × ℕ, g (i, q) = T ![f i, lieGamma T t w, lieGamma T t w] := fun i => by
      rw [(hg.prod_factor i).tsum_prod' (fun j => (hg.prod_factor i).prod_factor j)]
      have e2 : ∀ j, ∑' k, g (i, j, k) = T ![f i, f j, lieGamma T t w] := fun j => by
        have := (T.toContinuousLinearMap ![f i, f j, 0] 2).map_tsum hf
        simp only [lie_clm_apply2] at this
        exact this.symm
      simp only [e2]
      have := (T.toContinuousLinearMap ![f i, 0, lieGamma T t w] 1).map_tsum hf
      simp only [lie_clm_apply1] at this
      exact this.symm
    simp only [e1]
    have := (T.toContinuousLinearMap ![0, lieGamma T t w, lieGamma T t w] 0).map_tsum hf
    simp only [lie_clm_apply0] at this
    exact this.symm
  have hs : HasSum (fun s : (Σ n, Finset.Nat.antidiagonalTuple 3 n) =>
      T ![f (s.2.1 0), f (s.2.1 1), f (s.2.1 2)]) (∑' p, g p) := by
    have h1 : HasSum (fun x : Fin 3 → ℕ => T ![f (x 0), f (x 1), f (x 2)]) (∑' p, g p) := by
      rw [← lieTupleEquiv.tsum_eq g]; exact hG.hasSum
    exact (Finset.Nat.sigmaAntidiagonalTupleEquivTuple 3).hasSum_iff.2 h1
  have hn := hs.sigma (g := fun n => ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![f (x 0), f (x 1), f (x 2)]) (fun n => by
    have := hasSum_fintype (fun c : Finset.Nat.antidiagonalTuple 3 n =>
      T ![f (c.1 0), f (c.1 1), f (c.1 2)])
    rwa [Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple 3 n)
      (fun x => T ![f (x 0), f (x 1), f (x 2)])] at this)
  have heq : (fun n : ℕ => (t ^ n) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)]) =
      fun n => ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, T ![f (x 0), f (x 1), f (x 2)] := by
    funext n
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at hx'
    simp only [hfdef]
    rw [lie_tri_smul, ← pow_add, ← pow_add, hx']
  rw [← hval, heq]
  exact hn

include hC hT in
/-- (`bpW:w3:flow`) The flow equation `∂_t Γ_t(w) = T(Γ_t w, Γ_t w, Γ_t w)`. -/
theorem hasDerivAt_lieGamma_flow (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun s : ℝ => lieGamma T s w)
      (T ![lieGamma T t w, lieGamma T t w, lieGamma T t w]) t := by
  have h := hasDerivAt_lieGamma_t T hC hT hCp t w ht hw
  have hc := hasSum_lieCauchy T hC hT t w (q_le_of_dom hCp t w ht hw)
  refine HasDerivAt.congr_deriv h ?_
  set f : ℕ → E := fun k => ((k : ℝ) * t ^ (k - 1)) • lieSeq T w k with hf
  have hshift : ∀ k : ℕ, f (k + 1) = (t ^ k) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
      T ![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)] := fun k => by
    simp only [hf]
    rw [lieSeq_succ, Nat.add_sub_cancel, ← Complex.coe_smul, ← Complex.coe_smul (t ^ k),
      smul_smul]
    congr 1
    push_cast
    field_simp
  have hs2 : Summable fun k : ℕ => f (k + 1) := by
    simp only [hshift]; exact hc.summable
  have hs3 : Summable f := (summable_nat_add_iff 1).1 hs2
  have h0 : f 0 = 0 := by simp [hf]
  rw [show (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • lieSeq T w k) = ∑' k, f k from rfl,
    hs3.tsum_eq_zero_add, h0, zero_add]
  simp only [hshift]
  exact hc.tsum_eq

end KAM.Wave

end
