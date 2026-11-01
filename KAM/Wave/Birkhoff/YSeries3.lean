/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.YSeries2

/-!
# The series identity `DΓ_t (ι V) = ι N(Γ_t)` (blueprint-W `bpW:w3:Yseries`)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

`hasSum_bil_cauchy`: Cauchy product for a continuous bilinear map. `lieV_identity`: for
`|t| ≤ 1`, `‖w‖ ≤ ρ`, `2Cρ² ≤ 1/80`: `V_t(w) = Σ_n t^n V_n(w,…,w)` converges absolutely and
`DΓ_t(w)(ι V_t(w)) = ι N(Γ_t w, Γ_t w, Γ_t w)`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

theorem hasSum_bil_cauchy {A B D : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D] (L : A →L[ℂ] B →L[ℂ] D)
    (a : ℕ → A) (b : ℕ → B) (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    HasSum (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n, L (a p.1) (b p.2))
      (L (∑' k, a k) (∑' k, b k)) := by
  set g : ℕ × ℕ → D := fun p => L (a p.1) (b p.2) with hgdef
  have hbound : ∀ p, ‖g p‖ ≤ ‖L‖ * (‖a p.1‖ * ‖b p.2‖) := fun p => by
    calc ‖g p‖ = ‖L (a p.1) (b p.2)‖ := rfl
      _ ≤ ‖L (a p.1)‖ * ‖b p.2‖ := (L (a p.1)).le_opNorm _
      _ ≤ (‖L‖ * ‖a p.1‖) * ‖b p.2‖ :=
          mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _ = ‖L‖ * (‖a p.1‖ * ‖b p.2‖) := by ring
  have hgn : Summable fun p => ‖g p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
    exact (ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖L‖
  have hg : Summable g := hgn.of_norm
  have hsa := ha.of_norm
  have hsb := hb.of_norm
  have hval : ∑' p, g p = L (∑' k, a k) (∑' k, b k) := by
    rw [hg.tsum_prod' (fun i => hg.prod_factor i)]
    have e1 : ∀ i, ∑' j, g (i, j) = L (a i) (∑' k, b k) := fun i => by
      have := (L (a i)).map_tsum hsb
      exact this.symm
    simp only [e1]
    have := (L.flip (∑' k, b k)).map_tsum hsa
    simpa using this.symm
  have hs : HasSum (fun s : (Σ n, Finset.antidiagonal n) => g s.2.1) (∑' p, g p) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := g)).2 hg.hasSum
  have hn := hs.sigma (g := fun n => ∑ p ∈ Finset.antidiagonal n, g p) (fun n => by
    have := hasSum_fintype (fun c : Finset.antidiagonal n => g c.1)
    rwa [Finset.sum_coe_sort (Finset.antidiagonal n) g] at this)
  rw [← hval]
  exact hn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S N : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_lieV_apply_le (n : ℕ) (w : E) :
    ‖lieV ι S N n (fun _ => w)‖ ≤ ‖lieV ι S N n‖ * ‖w‖ ^ (2 * n + 3) := by
  refine ((lieV ι S N n).le_opNorm _).trans (le_of_eq ?_)
  simp [Finset.prod_const]

variable {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ‖S‖ ≤ C)

include hC hι hS in
theorem summable_lieV (ρ : ℝ) (hρ : 0 < ρ) (hq : 2 * C * ρ ^ 2 ≤ 1 / 80) (t : ℝ) (ht : |t| ≤ 2)
    (w : E) (hw : ‖w‖ ≤ ρ) : Summable fun n : ℕ => ‖(t ^ n) • lieV ι S N n (fun _ => w)‖ := by
  have hq0 : 0 ≤ 2 * C * ρ ^ 2 := by positivity
  have hg : Summable fun n : ℕ => (4 * ‖N‖ * ρ ^ 3) * (20 * (2 * C * ρ ^ 2)) ^ n :=
    (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hg
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  have h1 := norm_lieV_apply_le ι S N n w
  have h2 := norm_lieV_le ι S N hC hι hS ρ hρ n
  have h3 : ‖w‖ ^ (2 * n + 3) ≤ ρ ^ (2 * n + 3) := pow_le_pow_left₀ (norm_nonneg _) hw _
  have h4 : |t| ^ n ≤ 2 ^ n := pow_le_pow_left₀ (abs_nonneg _) ht n
  calc |t| ^ n * ‖lieV ι S N n (fun _ => w)‖ ≤ 2 ^ n * (‖lieV ι S N n‖ * ρ ^ (2 * n + 3)) := by
        refine mul_le_mul h4 (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ n * ((‖lieV ι S N n‖ * ρ ^ (2 * n)) * ρ ^ 3) := by rw [pow_add]; ring
    _ ≤ 2 ^ n * ((4 * ‖N‖ * (10 * (2 * C * ρ ^ 2)) ^ n) * ρ ^ 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
    _ = (4 * ‖N‖ * ρ ^ 3) * (20 * (2 * C * ρ ^ 2)) ^ n := by
        have e : (20 * (2 * C * ρ ^ 2)) ^ n = 2 ^ n * (10 * (2 * C * ρ ^ 2)) ^ n := by
          rw [← mul_pow]; congr 1; ring
        rw [e]; ring

omit [CompleteSpace E] [CompleteSpace F] in
theorem clm_real_smul {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (L : G →L[ℂ] H) (r : ℝ) (v : G) :
    L (r • v) = r • L v := by
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

include hC hι hS in
theorem lieV_identity (ρ : ℝ) (hρ : 0 < ρ) (hq : 2 * C * ρ ^ 2 ≤ 1 / 80) (t : ℝ) (ht : |t| ≤ 2)
    (w : E) (hw : ‖w‖ ≤ ρ) :
    lieGammaD (lieT ι S) t w (ι (∑' n : ℕ, (t ^ n) • lieV ι S N n (fun _ => w))) =
      ι (N (fun _ => lieGamma (lieT ι S) t w)) := by
  have hT := norm_lieT_le' ι S hC hι hS
  have hT' : ∀ v : Fin 3 → E, ‖lieT ι S v‖ ≤ C * ∏ i, ‖v i‖ := fun v =>
    ((lieT ι S).le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (by positivity))
  have hq' : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10 := by
    have h1 : ‖w‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h2 : 0 ≤ 2 * C := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 : |t| * (2 * C * ρ ^ 2) ≤ 2 * (2 * C * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    nlinarith [abs_nonneg t]
  have hsV := summable_lieV ι S N hC hι hS ρ hρ hq t ht w hw
  set v : ℕ → F := fun n => lieV ι S N n (fun _ => w) with hv
  have ha := summable_norm_lieDTerm (lieT ι S) hC hT' t w hq'
  have hb : Summable fun m : ℕ => ‖(t ^ m) • ι (v m)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hsV
    rw [← clm_real_smul ι (t ^ m) (v m)]
    refine (ι.le_opNorm _).trans ?_
    calc ‖ι‖ * ‖(t ^ m) • v m‖ ≤ 1 * ‖(t ^ m) • v m‖ :=
          mul_le_mul_of_nonneg_right hι (norm_nonneg _)
      _ = _ := one_mul _
  have hcau := hasSum_bil_cauchy (ContinuousLinearMap.id ℂ (E →L[ℂ] E))
    (fun k => (t ^ k) • lieDer (lieT ι S) w k) (fun m => (t ^ m) • ι (v m)) ha hb
  have hsum_b : ∑' m, (t ^ m) • ι (v m) = ι (∑' n : ℕ, (t ^ n) • v n) := by
    rw [ι.map_tsum hsV.of_norm]
    exact tsum_congr fun m => (clm_real_smul ι (t ^ m) (v m)).symm
  have hterm : ∀ n : ℕ, ∑ p ∈ Finset.antidiagonal n,
      (ContinuousLinearMap.id ℂ (E →L[ℂ] E)) ((t ^ p.1) • lieDer (lieT ι S) w p.1)
        ((t ^ p.2) • ι (v p.2)) = (t ^ n) • ι (lieNsum ι S N n (fun _ => w)) := fun n => by
    have h1 : ∀ p ∈ Finset.antidiagonal n,
        (ContinuousLinearMap.id ℂ (E →L[ℂ] E)) ((t ^ p.1) • lieDer (lieT ι S) w p.1)
          ((t ^ p.2) • ι (v p.2)) = (t ^ n) • lieDer (lieT ι S) w p.1 (ι (v p.2)) := fun p hp => by
      have hp' := Finset.mem_antidiagonal.1 hp
      simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      rw [clm_real_smul, smul_smul, ← pow_add, hp']
    rw [Finset.sum_congr rfl h1, ← Finset.smul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    congr 1
    have h2 := lieV_eval ι S N w n
    have h3 : ι (v n) = ι (lieNsum ι S N n (fun _ => w)) - ∑ j ∈ Finset.range n,
        lieDer (lieT ι S) w (j + 1) (ι (v (n - 1 - j))) := by
      rw [hv]
      simp only []
      rw [h2, map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.1 hj
      simp only [hjn, if_true]
      exact map_lieSymF_cons ι S j w _
    have h4 : ∀ j ∈ Finset.range n, lieDer (lieT ι S) w (j + 1) (ι (v (n - (j + 1)))) =
        lieDer (lieT ι S) w (j + 1) (ι (v (n - 1 - j))) := fun j _ => by
      congr 3; omega
    rw [Finset.sum_congr rfl h4]
    simp only [lieDer_zero, ContinuousLinearMap.id_apply, Nat.sub_zero]
    rw [h3]; abel
  simp only [hterm] at hcau
  -- the limit via the triple Cauchy product for `ι ∘ N`
  have hnb := summable_norm_lieTerm (lieT ι S) hC hT' t w hq'
  have htri := hasSum_tri_cauchy (ι.compContinuousMultilinearMap N)
    (fun k => (t ^ k) • lieSeq (lieT ι S) w k) (fun k => (t ^ k) • lieSeq (lieT ι S) w k)
    (fun k => (t ^ k) • lieSeq (lieT ι S) w k) hnb hnb hnb
  have hnsum : ∀ n : ℕ, ι (lieNsum ι S N n (fun _ => w)) = ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      (ι.compContinuousMultilinearMap N) ![lieSeq (lieT ι S) w (x 0), lieSeq (lieT ι S) w (x 1),
        lieSeq (lieT ι S) w (x 2)] := fun n => by
    unfold lieNsum
    simp only [ContinuousMultilinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at hx'
    rw [lieBlockT, dif_pos (by simp only [Fin.sum_univ_three]; omega), lieBlock_const, lieVec_eq]
    simp only [lieMulti_const]
    rfl
  have htri' : HasSum (fun n : ℕ => (t ^ n) • ι (lieNsum ι S N n (fun _ => w)))
      ((ι.compContinuousMultilinearMap N) ![lieGamma (lieT ι S) t w, lieGamma (lieT ι S) t w,
        lieGamma (lieT ι S) t w]) := by
    have e : (fun n : ℕ => ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
        (ι.compContinuousMultilinearMap N) ![(t ^ x 0) • lieSeq (lieT ι S) w (x 0),
          (t ^ x 1) • lieSeq (lieT ι S) w (x 1), (t ^ x 2) • lieSeq (lieT ι S) w (x 2)]) =
        fun n => (t ^ n) • ι (lieNsum ι S N n (fun _ => w)) := by
      funext n
      rw [hnsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      rw [lie_tri_smul, ← pow_add, ← pow_add, hx']
    rw [← e]
    exact htri
  have hu := hcau.unique htri'
  rw [hsum_b] at hu
  have e2 : (fun _ : Fin 3 => lieGamma (lieT ι S) t w) = ![lieGamma (lieT ι S) t w,
      lieGamma (lieT ι S) t w, lieGamma (lieT ι S) t w] := by
    funext i; fin_cases i <;> rfl
  rw [e2]
  exact hu

end KAM.Wave

end
