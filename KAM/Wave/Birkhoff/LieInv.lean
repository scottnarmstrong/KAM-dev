/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieFlow4

/-!
# The flow `Γ_t`: the inverse (blueprint-W `bpW:w3:flow` (vi))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`lieGamma_zero`: `Γ_0 = id`. `hasDerivAt_lieGamma_inv`: `s ↦ Γ_{-s}(Γ_s w)` has derivative `0`
(chain rule, transport equation, flow equation). `lieGamma_neg_lieGamma`: `Γ_{-t}(Γ_t w) = w`
for `|t| < 2` and `‖w‖ < ρ₁ = ρ₀ / 2`, i.e. `160 C ‖w‖² < 1`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) {C : ℝ}

theorem lieGamma_zero (w : E) : lieGamma T 0 w = w := by
  unfold lieGamma
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp [lieSeq_zero]

variable (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem hasDerivAt_lieGamma_inv
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (hCp : 0 < C) (s : ℝ) (w : E) (hs : |s| < 2) (hw : 160 * C * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun r : ℝ => lieGamma T (-r) (lieGamma T r w)) 0 s := by
  have hw0 : 40 * C * ‖w‖ ^ 2 < 1 := by nlinarith [sq_nonneg ‖w‖, mul_nonneg hC (sq_nonneg ‖w‖)]
  have hq : 2 * |s| * C * ‖w‖ ^ 2 ≤ 1 / 10 := by
    have h0 : 0 ≤ C * ‖w‖ ^ 2 := mul_nonneg hC (sq_nonneg _)
    nlinarith [abs_nonneg s]
  have hy := norm_lieGamma_le T hC hT s w hq
  set y := lieGamma T s w with hydef
  have hy2 : 40 * C * ‖y‖ ^ 2 < 1 := by
    have h1 : ‖y‖ ^ 2 ≤ (10 / 9 * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    have h0 : 0 ≤ C * ‖w‖ ^ 2 := mul_nonneg hC (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 40 * C)]
  have hs' : |-s| < 2 := by rwa [abs_neg]
  obtain ⟨hD, -⟩ := hasFDerivAt_lieGamma T hC hT hCp (-s) y hs' hy2
  have hflow := hasDerivAt_lieGamma_flow T hC hT hCp s w hs hw0
  have hinner : HasDerivAt (fun r : ℝ => (-r, lieGamma T r w)) (-1, T ![y, y, y]) s :=
    (hasDerivAt_neg s).prodMk hflow
  have h : HasDerivAt (fun r : ℝ => lieGamma T (-r) (lieGamma T r w))
      ((∑' k, lieTermD T k (-s, y)) (-1, T ![y, y, y])) s :=
    HasFDerivAt.comp_hasDerivAt (l := fun p : ℝ × E => lieGamma T p.1 p.2) s hD hinner
  refine h.congr_deriv ?_
  set L := ∑' k, lieTermD T k (-s, y) with hL
  have hc : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) (-s) :=
    (hasDerivAt_id (-s)).prodMk (hasDerivAt_const (-s) y)
  have hA : HasDerivAt (fun r : ℝ => lieGamma T r y) (L ((1 : ℝ), (0 : E))) (-s) :=
    HasFDerivAt.comp_hasDerivAt (l := fun p : ℝ × E => lieGamma T p.1 p.2) (-s) hD hc
  have hA' := hasDerivAt_lieGamma_transport T hC hT hsym hCp (-s) y hs' hy2
  have hB : HasFDerivAt (fun x : E => lieGamma T (-s) x) (L.comp (ContinuousLinearMap.inr ℝ ℝ E))
      y := hD.comp y ((hasFDerivAt_const (-s) y).prodMk (hasFDerivAt_id y))
  have hB' := hasFDerivAt_lieGamma_w T hC hT hCp (-s) y hs' hy2
  have e1 := hA.unique hA'
  have e2 : ∀ v : E, L ((0 : ℝ), v) = lieGammaD T (-s) y v := fun v => by
    have := congrArg (fun f => f v) (hB.unique hB')
    simpa using this
  have hsplit : ((-1 : ℝ), T ![y, y, y]) =
      (-1 : ℝ) • ((1 : ℝ), (0 : E)) + ((0 : ℝ), T ![y, y, y]) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, e1, e2]
  simp

include hC hT in
/-- (`bpW:w3:flow` (vi)) `Γ_{-t}(Γ_t(w)) = w`. -/
theorem lieGamma_neg_lieGamma
    (hsym : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → E), T (fun i => v (σ i)) = T v)
    (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2) (hw : 160 * C * ‖w‖ ^ 2 < 1) :
    lieGamma T (-t) (lieGamma T t w) = w := by
  have hdiff : DifferentiableOn ℝ (fun r : ℝ => lieGamma T (-r) (lieGamma T r w))
      (Set.Ioo (-2) 2) := fun s hs =>
    (hasDerivAt_lieGamma_inv T hC hT hsym hCp s w (abs_lt.2 ⟨hs.1, hs.2⟩) hw).differentiableAt
      |>.differentiableWithinAt
  have h := (isOpen_Ioo (a := (-2 : ℝ)) (b := 2)).is_const_of_deriv_eq_zero
    (convex_Ioo (-2 : ℝ) 2).isPreconnected hdiff
    (fun s hs => (hasDerivAt_lieGamma_inv T hC hT hsym hCp s w (abs_lt.2 ⟨hs.1, hs.2⟩)
      hw).deriv) (x := t) (y := 0) (abs_lt.1 ht |> fun h => ⟨h.1, h.2⟩) (by simp)
  simpa [lieGamma_zero] using h

end KAM.Wave

end
