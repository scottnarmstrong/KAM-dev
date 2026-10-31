/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieCauchy

/-!
# The flow `Γ_t`: the variational equation (blueprint-W `bpW:w3:flow` (v))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`hasDerivAt_powSeries`: termwise `t`-derivative of a power series with
`Σ k τ^{k-1}‖u_k‖ < ∞`, `|t| < τ`. `hasDerivAt_lieGammaD_var`:
`∂_t (DΓ_t(w) v) = 3 T(DΓ_t(w) v, Γ_t(w), Γ_t(w))`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

theorem hasDerivAt_powSeries {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (u : ℕ → F) (t τ : ℝ) (htτ : |t| < τ)
    (hs : Summable fun k : ℕ => (k : ℝ) * τ ^ (k - 1) * ‖u k‖) :
    HasDerivAt (fun s : ℝ => ∑' k, s ^ k • u k) (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • u k) t := by
  have hτ : 0 < τ := lt_of_le_of_lt (abs_nonneg t) htτ
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun (k : ℕ) (s : ℝ) => s ^ k • u k)
    (g' := fun (k : ℕ) (s : ℝ) => ((k : ℝ) * s ^ (k - 1)) • u k) (t := Set.Ioo (-τ) τ)
    (u := fun k : ℕ => (k : ℝ) * τ ^ (k - 1) * ‖u k‖) (y₀ := 0) (y := t) hs isOpen_Ioo
    (convex_Ioo (-τ) τ).isPreconnected
    (fun k s _ => (hasDerivAt_pow k s).smul_const (u k))
    (fun k s hs' => by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
      have hsa : |s| ≤ τ := (abs_lt.2 hs').le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hsa _) (Nat.cast_nonneg _))
        (norm_nonneg _))
    ⟨by linarith, hτ⟩
    ((hasSum_single 0 (fun k hk => by simp [zero_pow hk])).summable)
    (abs_lt.1 htτ)
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}
  (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem summable_lieDer_deriv (τ : ℝ) (hτ : 0 < τ) (w v : E)
    (hx : 2 * τ * C * ‖w‖ ^ 2 < 1) :
    Summable fun k : ℕ => (k : ℝ) * τ ^ (k - 1) * ‖lieDer T w k v‖ := by
  set x : ℝ := 2 * τ * C * ‖w‖ ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have key : ∀ k : ℕ, (k : ℝ) * τ ^ (k - 1) * ‖lieDer T w k v‖ ≤
      (‖v‖ / τ) * (3 * ((k : ℝ) ^ 2 * x ^ k)) := by
    intro k
    cases k with
    | zero => simp
    | succ n =>
      have h1 : ‖lieDer T w (n + 1) v‖ ≤ ((2 * ((n + 1 : ℕ) : ℝ) + 1) * 2 ^ (n + 1) *
          C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1))) * ‖v‖ := by
        refine ((lieDer T w (n + 1)).le_opNorm v).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (norm_lieDer_le T hC hT w (n + 1)).trans ?_
        have hm := birkLieM_le_pow (n + 1)
        have h0 : 0 ≤ (2 * ((n + 1 : ℕ) : ℝ) + 1) * C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1)) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hm h0]
      have hxk : x ^ (n + 1) = 2 ^ (n + 1) * τ * τ ^ n * C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1)) := by
        rw [hxdef, mul_pow, mul_pow, mul_pow, ← pow_mul, pow_succ τ n]; ring
      have hk1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hkk : ((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 1) ≤ 3 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith
      have hP : 0 ≤ τ ^ n * 2 ^ (n + 1) * C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1)) * ‖v‖ := by positivity
      simp only [Nat.add_sub_cancel]
      calc ((n + 1 : ℕ) : ℝ) * τ ^ n * ‖lieDer T w (n + 1) v‖
          ≤ ((n + 1 : ℕ) : ℝ) * τ ^ n * (((2 * ((n + 1 : ℕ) : ℝ) + 1) * 2 ^ (n + 1) *
            C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1))) * ‖v‖) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 1)) *
            (τ ^ n * 2 ^ (n + 1) * C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1)) * ‖v‖) := by ring
        _ ≤ (3 * ((n + 1 : ℕ) : ℝ) ^ 2) *
            (τ ^ n * 2 ^ (n + 1) * C ^ (n + 1) * ‖w‖ ^ (2 * (n + 1)) * ‖v‖) :=
              mul_le_mul_of_nonneg_right hkk hP
        _ = (‖v‖ / τ) * (3 * (((n + 1 : ℕ) : ℝ) ^ 2 * x ^ (n + 1))) := by
              rw [hxk]; field_simp
  refine Summable.of_nonneg_of_le (fun k => by positivity) key ?_
  exact ((summable_pow_mul_geometric_of_norm_lt_one 2
    (by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]) : Summable fun n : ℕ => (n : ℝ) ^ 2 * x ^ n
    ).mul_left 3).mul_left _

include hC hT in
/-- (`bpW:w3:flow` (v)) `∂_t (DΓ_t(w) v) = 3 T(DΓ_t(w) v, Γ_t(w), Γ_t(w))`. -/
theorem hasDerivAt_lieGammaD_var
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (hCp : 0 < C) (t : ℝ) (w v : E) (ht : |t| < 2) (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun s : ℝ => lieGammaD T s w v)
      ((3 : ℂ) • T ![lieGammaD T t w v, lieGamma T t w, lieGamma T t w]) t := by
  set τ : ℝ := (|t| + 2) / 2 with hτdef
  have hτ1 : |t| < τ := by rw [hτdef]; linarith
  have hτ2 : τ < 2 := by rw [hτdef]; linarith
  have hτ0 : 0 < τ := lt_of_le_of_lt (abs_nonneg t) hτ1
  have hCw : 0 ≤ C * ‖w‖ ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hxτ : 2 * τ * C * ‖w‖ ^ 2 < 1 := by nlinarith
  have hq : ∀ s : ℝ, |s| < τ → 2 * |s| * C * ‖w‖ ^ 2 ≤ 1 / 10 := fun s hs => by
    nlinarith [abs_nonneg s]
  have hrep : ∀ s : ℝ, |s| < τ → lieGammaD T s w v = ∑' k, s ^ k • lieDer T w k v := fun s hs => by
    unfold lieGammaD
    rw [show (∑' k, (s ^ k) • lieDer T w k) v = ∑' k, ((s ^ k) • lieDer T w k) v from
      ((ContinuousLinearMap.apply ℂ E v).map_tsum (summable_lieDTerm T hC hT s w (hq s hs)))]
    exact tsum_congr fun k => by simp
  have hev : (fun s : ℝ => lieGammaD T s w v) =ᶠ[nhds t]
      fun s : ℝ => ∑' k, s ^ k • lieDer T w k v := by
    filter_upwards [(continuous_abs.continuousAt.eventually_lt continuousAt_const
      (by simpa using hτ1) : ∀ᶠ s in nhds t, |s| < τ)] with s hs using hrep s hs
  have hd := hasDerivAt_powSeries (fun k => lieDer T w k v) t τ hτ1
    (summable_lieDer_deriv T hC hT τ hτ0 w v hxτ)
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  -- identify the derivative
  have hqt := hq t hτ1
  have hna : Summable fun k : ℕ => ‖t ^ k • lieDer T w k v‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_norm_lieDTerm T hC hT t w hqt).mul_right ‖v‖)
    rw [show t ^ k • lieDer T w k v = ((t ^ k) • lieDer T w k) v by simp]
    exact ((t ^ k • lieDer T w k).le_opNorm v)
  have hnb := summable_norm_lieTerm T hC hT t w hqt
  have hc := hasSum_tri_cauchy T (fun k => t ^ k • lieDer T w k v)
    (fun k => t ^ k • lieSeq T w k) (fun k => t ^ k • lieSeq T w k) hna hnb hnb
  have hA : ∑' k, t ^ k • lieDer T w k v = lieGammaD T t w v := (hrep t hτ1).symm
  have hterm : ∀ n : ℕ, ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      T ![t ^ x 0 • lieDer T w (x 0) v, t ^ x 1 • lieSeq T w (x 1), t ^ x 2 • lieSeq T w (x 2)] =
      t ^ n • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
        T ![lieDer T w (x 0) v, lieSeq T w (x 1), lieSeq T w (x 2)] := fun n => by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at hx'
    rw [lie_tri_smul, ← pow_add, ← pow_add, hx']
  simp only [hterm, hA] at hc
  change HasSum _ (T ![lieGammaD T t w v, lieGamma T t w, lieGamma T t w]) at hc
  set f : ℕ → E := fun k => ((k : ℝ) * t ^ (k - 1)) • lieDer T w k v with hf
  have hshift : ∀ k : ℕ, f (k + 1) = (3 : ℂ) • (t ^ k • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
      T ![lieDer T w (x 0) v, lieSeq T w (x 1), lieSeq T w (x 2)]) := fun k => by
    simp only [hf, Nat.add_sub_cancel]
    rw [← Complex.coe_smul, ← Complex.coe_smul (t ^ k), smul_comm (3 : ℂ),
      ← lieDer_succ_sym T hsym w k v, smul_smul]
    congr 1
    push_cast
    ring
  have hs2 : HasSum (fun k : ℕ => f (k + 1)) ((3 : ℂ) • T ![lieGammaD T t w v, lieGamma T t w,
      lieGamma T t w]) := by
    simp only [hshift]; exact hc.const_smul (3 : ℂ)
  have hs3 : Summable f := (summable_nat_add_iff 1).1 hs2.summable
  have h0 : f 0 = 0 := by simp [hf]
  rw [show (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • lieDer T w k v) = ∑' k, f k from rfl,
    hs3.tsum_eq_zero_add, h0, zero_add]
  exact hs2.tsum_eq

end KAM.Wave

end
