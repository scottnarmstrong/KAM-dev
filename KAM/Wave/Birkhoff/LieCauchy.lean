/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieInv

/-!
# The trilinear Cauchy product (blueprint-W `bpW:w3:flow`, Steps Flow equation and Variational)

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`hasSum_tri_cauchy`: for absolutely summable `a, b, c : ℕ → E` and a continuous trilinear `T`,
`Σ_n Σ_{i+j+k=n} T(a_i, b_j, c_k) = T(Σ a, Σ b, Σ c)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

theorem hasSum_tri_cauchy (a b c : ℕ → E) (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) (hc : Summable fun k => ‖c k‖) :
    HasSum (fun n : ℕ => ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![a (x 0), b (x 1), c (x 2)]) (T ![∑' k, a k, ∑' k, b k, ∑' k, c k]) := by
  set g : ℕ × ℕ × ℕ → E := fun p => T ![a p.1, b p.2.1, c p.2.2] with hgdef
  have hbound : ∀ p, ‖g p‖ ≤ ‖T‖ * (‖a p.1‖ * (‖b p.2.1‖ * ‖c p.2.2‖)) := fun p => by
    have := T.le_opNorm ![a p.1, b p.2.1, c p.2.2]
    simpa [Fin.prod_univ_three, mul_assoc] using this
  have hgn : Summable fun p => ‖g p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
    exact (ha.mul_of_nonneg (hb.mul_of_nonneg hc (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)) (fun _ => norm_nonneg _) (fun _ => mul_nonneg (norm_nonneg _)
        (norm_nonneg _))).mul_left ‖T‖
  have hg : Summable g := hgn.of_norm
  have hG : Summable fun x : Fin 3 → ℕ => T ![a (x 0), b (x 1), c (x 2)] :=
    (lieTupleEquiv.summable_iff (f := g)).2 hg
  have hsa := ha.of_norm
  have hsb := hb.of_norm
  have hsc := hc.of_norm
  have hval : ∑' p, g p = T ![∑' k, a k, ∑' k, b k, ∑' k, c k] := by
    rw [hg.tsum_prod' (fun i => hg.prod_factor i)]
    have e1 : ∀ i, ∑' q : ℕ × ℕ, g (i, q) = T ![a i, ∑' k, b k, ∑' k, c k] := fun i => by
      rw [(hg.prod_factor i).tsum_prod' (fun j => (hg.prod_factor i).prod_factor j)]
      have e2 : ∀ j, ∑' k, g (i, j, k) = T ![a i, b j, ∑' k, c k] := fun j => by
        have := (T.toContinuousLinearMap ![a i, b j, 0] 2).map_tsum hsc
        simp only [lie_clm_apply2] at this
        exact this.symm
      simp only [e2]
      have := (T.toContinuousLinearMap ![a i, 0, ∑' k, c k] 1).map_tsum hsb
      simp only [lie_clm_apply1] at this
      exact this.symm
    simp only [e1]
    have := (T.toContinuousLinearMap ![0, ∑' k, b k, ∑' k, c k] 0).map_tsum hsa
    simp only [lie_clm_apply0] at this
    exact this.symm
  have hs : HasSum (fun s : (Σ n, Finset.Nat.antidiagonalTuple 3 n) =>
      T ![a (s.2.1 0), b (s.2.1 1), c (s.2.1 2)]) (∑' p, g p) := by
    have h1 : HasSum (fun x : Fin 3 → ℕ => T ![a (x 0), b (x 1), c (x 2)]) (∑' p, g p) := by
      rw [← lieTupleEquiv.tsum_eq g]; exact hG.hasSum
    exact (Finset.Nat.sigmaAntidiagonalTupleEquivTuple 3).hasSum_iff.2 h1
  have hn := hs.sigma (g := fun n => ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![a (x 0), b (x 1), c (x 2)]) (fun n => by
    have := hasSum_fintype (fun s : Finset.Nat.antidiagonalTuple 3 n =>
      T ![a (s.1 0), b (s.1 1), c (s.1 2)])
    rwa [Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple 3 n)
      (fun x => T ![a (x 0), b (x 1), c (x 2)])] at this)
  rw [← hval]
  exact hn

end KAM.Wave

end
