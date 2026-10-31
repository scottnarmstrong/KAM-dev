/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieFlow2

/-!
# The flow `Γ_t`: partial derivatives (blueprint-W `bpW:w3:flow` (i), (ii))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:flow`.

`hasDerivAt_lieGamma_t`: `∂_t Γ_t(w) = Σ_k (k+1) t^k φ_{k+1}(w)` (termwise);
`hasFDerivAt_lieGamma_w`: `D_wΓ_t(w) = Σ_k t^k Dφ_k(w) = lieGammaD T t w`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}

theorem q_le_of_dom (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2) (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10 := by
  have h0 : 0 ≤ C * ‖w‖ ^ 2 := by positivity
  nlinarith [mul_nonneg h0 (abs_nonneg t), mul_nonneg h0 (sub_nonneg.2 ht.le)]

theorem shifted_term_eq
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (t : ℝ) (w : E) (k : ℕ) :
    ((t ^ k) • lieDer T w k) (T ![w, w, w]) =
      (((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1)) • lieSeq T w (k + 1) := by
  rw [ContinuousLinearMap.smul_apply, lieDer_apply_field T hsym w k, Nat.add_sub_cancel]
  rw [show ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul, smul_smul,
    mul_comm]

variable (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
/-- `∂_t Γ_t(w) = Σ_k k t^{k-1} φ_k(w)`. -/
theorem hasDerivAt_lieGamma_t (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun s : ℝ => lieGamma T s w)
      (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • lieSeq T w k) t := by
  obtain ⟨hD, hsum⟩ := hasFDerivAt_lieGamma T hC hT hCp t w ht hw
  have hc : HasDerivAt (fun s : ℝ => (s, w)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  have h := hD.comp_hasDerivAt t hc
  refine HasDerivAt.congr_deriv h ?_
  rw [show (∑' k, lieTermD T k (t, w)) ((1 : ℝ), (0 : E)) =
      ∑' k, lieTermD T k (t, w) ((1 : ℝ), (0 : E)) from
    ((ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : E))).map_tsum hsum)]
  refine tsum_congr fun k => ?_
  simp [lieTermD, powD]

include hC hT in
/-- `D_wΓ_t(w) = Σ_k t^k Dφ_k(w)`. -/
theorem hasFDerivAt_lieGamma_w (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasFDerivAt (fun w' : E => lieGamma T t w') ((lieGammaD T t w).restrictScalars ℝ) w := by
  obtain ⟨hD, hsum⟩ := hasFDerivAt_lieGamma T hC hT hCp t w ht hw
  have hc : HasFDerivAt (fun w' : E => (t, w')) (ContinuousLinearMap.inr ℝ ℝ E) w :=
    (hasFDerivAt_const t w).prodMk (hasFDerivAt_id w)
  have h := hD.comp w hc
  refine HasFDerivAt.congr_fderiv h ?_
  ext v
  have hq := q_le_of_dom hCp t w ht hw
  have hsD := summable_lieDTerm T hC hT t w hq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [show (∑' k, lieTermD T k (t, w)) ((0 : ℝ), v) = ∑' k, lieTermD T k (t, w) ((0 : ℝ), v) from
    ((ContinuousLinearMap.apply ℝ E ((0 : ℝ), v)).map_tsum hsum)]
  unfold lieGammaD
  rw [show (∑' k, (t ^ k) • lieDer T w k) v = ∑' k, ((t ^ k) • lieDer T w k) v from
    ((ContinuousLinearMap.apply ℂ E v).map_tsum hsD)]
  refine tsum_congr fun k => ?_
  simp [lieTermD, powD]

include hC hT in
/-- Transport equation: `∂_t Γ_t(w) = DΓ_t(w) X(w)`, `X(w) = T(w,w,w)`. -/
theorem hasDerivAt_lieGamma_transport
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2) (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun s : ℝ => lieGamma T s w) (lieGammaD T t w (T ![w, w, w])) t := by
  have h := hasDerivAt_lieGamma_t T hC hT hCp t w ht hw
  have hq := q_le_of_dom hCp t w ht hw
  have hsD := summable_lieDTerm T hC hT t w hq
  refine HasDerivAt.congr_deriv h ?_
  have hs1' := (ContinuousLinearMap.apply ℂ E (T ![w, w, w])).summable hsD
  have hs1 : Summable fun k : ℕ => ((t ^ k) • lieDer T w k) (T ![w, w, w]) := by
    simpa only [ContinuousLinearMap.apply_apply] using hs1'
  set f : ℕ → E := fun k => ((k : ℝ) * t ^ (k - 1)) • lieSeq T w k with hf
  have hs2 : Summable fun k : ℕ => f (k + 1) := by
    refine hs1.congr fun k => ?_
    rw [shifted_term_eq T hsym t w k]
  have hs3 : Summable f := (summable_nat_add_iff 1).1 hs2
  have h0 : f 0 = 0 := by simp [hf]
  rw [show (∑' k : ℕ, ((k : ℝ) * t ^ (k - 1)) • lieSeq T w k) = ∑' k, f k from rfl,
    hs3.tsum_eq_zero_add, h0, zero_add]
  unfold lieGammaD
  rw [show (∑' k, (t ^ k) • lieDer T w k) (T ![w, w, w]) =
      ∑' k, ((t ^ k) • lieDer T w k) (T ![w, w, w]) from
    ((ContinuousLinearMap.apply ℂ E (T ![w, w, w])).map_tsum hsD)]
  exact tsum_congr fun k => (shifted_term_eq T hsym t w k).symm

end KAM.Wave

end
