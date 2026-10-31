/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieFlow1
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The flow `Γ_t`: joint differentiability (blueprint-W `bpW:w3:flow` (i), (ii))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-FLOW, blueprint label `bpW:w3:flow`.

Each term `(t, w) ↦ t^k φ_k(w)` is jointly Fréchet differentiable over `ℝ` (`hasFDerivAt_lieTerm`),
and the termwise derivative series is dominated on `(-τ, τ) × B_ρ` (`2τCρ² < 1/10`), so
`(t, w) ↦ Γ_t(w)` is Fréchet differentiable with the termwise derivative (`hasFDerivAt_lieGamma`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

/-- The derivative of `p ↦ p.1 ^ k`. -/
def powD (k : ℕ) (p : ℝ × E) : ℝ × E →L[ℝ] ℝ :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((k : ℝ) * p.1 ^ (k - 1))).comp
    (ContinuousLinearMap.fst ℝ ℝ E)

/-- The derivative of `(t, w) ↦ t^k φ_k(w)` (over `ℝ`). -/
def lieTermD (k : ℕ) (p : ℝ × E) : ℝ × E →L[ℝ] E :=
  (powD k p).smulRight (lieSeq T p.2 k) +
    (p.1 ^ k) • ((lieDer T p.2 k).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)

theorem hasFDerivAt_pow_fst (k : ℕ) (p : ℝ × E) :
    HasFDerivAt (fun p : ℝ × E => p.1 ^ k) (powD k p) p :=
  (hasDerivAt_pow k p.1).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := E))

theorem hasFDerivAt_lieTerm (k : ℕ) (p : ℝ × E) :
    HasFDerivAt (fun p : ℝ × E => (p.1 ^ k) • lieSeq T p.2 k) (lieTermD T k p) p := by
  have h2 : HasFDerivAt (fun p : ℝ × E => lieSeq T p.2 k)
      (((lieDer T p.2 k).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)) p :=
    ((hasFDerivAt_lieSeq T k p.2).restrictScalars ℝ).comp p
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := E))
  exact ((hasFDerivAt_pow_fst k p).smul h2).congr_fderiv (by unfold lieTermD; rw [add_comm])

section Series

variable [CompleteSpace E] {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem norm_lieTermD_le (k : ℕ) (t : ℝ) (w : E) :
    ‖lieTermD T k (t, w)‖ ≤ (k : ℝ) * |t| ^ (k - 1) * (2 * C * ‖w‖ ^ 2) ^ k * ‖w‖ +
      (2 * k + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
  have hu := norm_lieSeq_le T hC hT w k
  have hD := norm_lieDer_le T hC hT w k
  have hm := birkLieM_le_pow k
  have h0 := birkLieM_nonneg k
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_fst_le p
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_snd_le p
  have hpow : ‖powD k (t, w)‖ ≤ (k : ℝ) * |t| ^ (k - 1) := by
    unfold powD
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((k : ℝ) * t ^ (k - 1))‖ ≤
        (k : ℝ) * |t| ^ (k - 1) := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      refine (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
      rw [one_mul, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
    calc _ ≤ ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((k : ℝ) * t ^ (k - 1))‖ * 1 :=
          mul_le_mul_of_nonneg_left hfst (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  unfold lieTermD
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    refine (mul_le_mul hpow hu (norm_nonneg _) (by positivity)).trans ?_
    have : (k : ℝ) * |t| ^ (k - 1) * (birkLieM k * C ^ k * ‖w‖ ^ (2 * k + 1)) ≤
        (k : ℝ) * |t| ^ (k - 1) * ((2 * C * ‖w‖ ^ 2) ^ k * ‖w‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc birkLieM k * C ^ k * ‖w‖ ^ (2 * k + 1) ≤ 2 ^ k * C ^ k * ‖w‖ ^ (2 * k + 1) := by gcongr
        _ = (2 * C * ‖w‖ ^ 2) ^ k * ‖w‖ := by
          rw [mul_pow, mul_pow, ← pow_mul]; ring
    linarith
  · rw [norm_smul, Real.norm_eq_abs, abs_pow]
    refine (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hsnd (norm_nonneg _))) (by positivity)).trans ?_
    rw [mul_one, ContinuousLinearMap.norm_restrictScalars]
    refine (mul_le_mul_of_nonneg_left hD (by positivity)).trans ?_
    calc |t| ^ k * ((2 * k + 1) * birkLieM k * C ^ k * ‖w‖ ^ (2 * k))
        ≤ |t| ^ k * ((2 * k + 1) * 2 ^ k * C ^ k * ‖w‖ ^ (2 * k)) := by gcongr
      _ = (2 * k + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring

include hC hT in
/-- The joint Fréchet derivative of `(t, w) ↦ Γ_t(w)` on `|t| < 2`, `‖w‖ < ρ₀ = (40C)^{-1/2}`. -/
theorem hasFDerivAt_lieGamma (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    HasFDerivAt (fun p : ℝ × E => lieGamma T p.1 p.2) (∑' k, lieTermD T k (t, w)) (t, w) ∧
      Summable fun k => lieTermD T k (t, w) := by
  set τ : ℝ := (|t| + 2) / 2 with hτ
  have hτ1 : |t| < τ := by rw [hτ]; linarith
  have hτ2 : τ < 2 := by rw [hτ]; linarith
  have hτ0 : 0 < τ := lt_of_le_of_lt (abs_nonneg t) hτ1
  set r2 : ℝ := (‖w‖ ^ 2 + 1 / (40 * C)) / 2 with hr2
  have h40 : 0 < 1 / (40 * C) := by positivity
  have hwC : ‖w‖ ^ 2 < 1 / (40 * C) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hr2a : ‖w‖ ^ 2 < r2 := by rw [hr2]; linarith
  have hr2b : 40 * C * r2 < 1 := by
    have h2 : 40 * C * (1 / (40 * C)) = 1 := by field_simp
    rw [hr2]; nlinarith
  have hr0 : 0 < r2 := lt_of_le_of_lt (by positivity) hr2a
  set ρ : ℝ := Real.sqrt r2 with hρ
  have hρ2 : ρ ^ 2 = r2 := Real.sq_sqrt hr0.le
  have hwρ : ‖w‖ < ρ := by
    refine lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) ?_
    rw [hρ2]; exact hr2a
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
  set a : ℝ := 2 * C * ρ ^ 2 with ha
  set q0 : ℝ := τ * a with hq0
  have ha0 : 0 < a := by positivity
  have hq0p : 0 < q0 := by positivity
  have hq01 : q0 < 1 / 10 := by
    rw [hq0, ha, hρ2]
    nlinarith [mul_pos hCp hr0]
  set s : Set (ℝ × E) := (Prod.fst ⁻¹' Metric.ball (0 : ℝ) τ) ∩
    (Prod.snd ⁻¹' Metric.ball (0 : E) ρ) with hs
  have hsopen : IsOpen s :=
    (Metric.isOpen_ball.preimage continuous_fst).inter (Metric.isOpen_ball.preimage continuous_snd)
  have hsconv : Convex ℝ s :=
    ((convex_ball (0 : ℝ) τ).linear_preimage (LinearMap.fst ℝ ℝ E)).inter
      ((convex_ball (0 : E) ρ).linear_preimage (LinearMap.snd ℝ ℝ E))
  have hmem : (t, w) ∈ s := ⟨by simpa [Real.norm_eq_abs] using hτ1, by simpa using hwρ⟩
  have hmem0 : ((0 : ℝ), (0 : E)) ∈ s := ⟨by simpa using hτ0, by simpa using hρ0⟩
  -- the majorant
  set u : ℕ → ℝ := fun k => (a * ρ / q0) * ((k : ℝ) * q0 ^ k) + (2 * k + 1) * q0 ^ k with hu
  have hgeo : Summable fun k : ℕ => q0 ^ k := summable_geometric_of_lt_one hq0p.le (by linarith)
  have hk1 : Summable fun k : ℕ => (k : ℝ) * q0 ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := q0)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0p.le]; linarith)
  have hus : Summable u := by
    refine (hk1.mul_left _).add ?_
    have : (fun k : ℕ => (2 * (k : ℝ) + 1) * q0 ^ k) =
        fun k : ℕ => 2 * ((k : ℝ) * q0 ^ k) + q0 ^ k := by funext k; ring
    rw [this]
    exact (hk1.mul_left 2).add hgeo
  have hbound : ∀ k : ℕ, ∀ p ∈ s, ‖lieTermD T k p‖ ≤ u k := by
    rintro k ⟨t', w'⟩ ⟨h1, h2⟩
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h1 h2
    refine (norm_lieTermD_le T hC hT k t' w').trans ?_
    have hw0 := norm_nonneg w'
    have hA : 2 * C * ‖w'‖ ^ 2 ≤ a := by rw [ha]; gcongr
    have hB : 2 * |t'| * C * ‖w'‖ ^ 2 ≤ q0 := by
      rw [hq0, ha]; nlinarith [mul_nonneg hCp.le (sq_nonneg ‖w'‖), abs_nonneg t', sq_nonneg ρ,
        mul_nonneg (mul_nonneg hCp.le (sq_nonneg ‖w'‖)) (sub_nonneg.2 h1.le),
        mul_nonneg (mul_nonneg hCp.le (abs_nonneg t'))
          (sub_nonneg.2 (sq_le_sq' (by linarith) h2.le))]
    have hq0n : (0 : ℝ) ≤ 2 * |t'| * C * ‖w'‖ ^ 2 := by positivity
    refine add_le_add ?_ ?_
    · cases k with
      | zero => simp [hu]
      | succ k =>
        have ht' : |t'| ^ k ≤ τ ^ k := pow_le_pow_left₀ (abs_nonneg _) h1.le k
        have hA' : (2 * C * ‖w'‖ ^ 2) ^ (k + 1) ≤ a ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) hA _
        have hrhs : (a * ρ / q0) * (((k + 1 : ℕ) : ℝ) * q0 ^ (k + 1)) =
            ((k + 1 : ℕ) : ℝ) * (τ ^ k * a ^ (k + 1) * ρ) := by
          rw [hq0]; field_simp; ring
        simp only [hu, Nat.add_sub_cancel]
        rw [hrhs]
        have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
        calc ((k + 1 : ℕ) : ℝ) * |t'| ^ k * (2 * C * ‖w'‖ ^ 2) ^ (k + 1) * ‖w'‖
            ≤ ((k + 1 : ℕ) : ℝ) * τ ^ k * a ^ (k + 1) * ρ := by gcongr
          _ = _ := by ring
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0n hB k) (by positivity)
  have hf0 : Summable fun k : ℕ =>
      (((0 : ℝ), (0 : E)).1 ^ k) • lieSeq T ((0 : ℝ), (0 : E)).2 k := by
    have := summable_lieTerm T hC hT 0 (0 : E) (by simp)
    exact this
  exact ⟨hasFDerivAt_tsum_of_isPreconnected (f := fun k (p : ℝ × E) => (p.1 ^ k) • lieSeq T p.2 k)
    (f' := fun k p => lieTermD T k p) hus hsopen hsconv.isPreconnected
    (fun k p _ => hasFDerivAt_lieTerm T k p) hbound hmem0 hf0 hmem,
    Summable.of_norm_bounded hus (fun k => hbound k _ hmem)⟩

end Series

end KAM.Wave

end
