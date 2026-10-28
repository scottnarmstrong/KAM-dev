/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Canonical.Flow
public import KAM.Canonical.FlowRegular
public import KAM.Canonical.FlowInverse

/-!
# The canonical flow on the extended phase space (Part 11, package N11-E1)

Blueprint node `bpN:p11:flow`.

* `KAM.Nekhoroshev.ext_flow` (the signed name, renamed from `flow`, which Part 5's
  `Averaging/Flow` already owns): the generic Part 5 flow, consumed directly (membership
  in `Ω` and the gauge displacement bound).
* `KAM.Nekhoroshev.flow_real`: reality of the flow on the unequal product `EC n k`. Part 5
  `flow_e` is stated for `ℂⁿ × ℂⁿ`; its Picard-iteration proof is repeated here with the
  imaginary-part map `EC n k →L[ℝ] ER n k`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-- Generic Part 5 flow is consumed directly: no second choice of flow. -/
theorem ext_flow (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε) {z : EC n k}
    (hz : z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    KAM.Canonical.flow F Ω t z ∈ Ω ∧
    ‖W (KAM.Canonical.flow F Ω t z-z)‖ ≤ |t| *ε := by
  have htI : t ∈ Icc (-1 : ℝ) 1 := abs_le.1 ht
  exact ⟨(KAM.Canonical.flow_b hF).2.2.1 t htI z hz,
    (KAM.Canonical.flow_a hF hz).2.2.2 t htI⟩

/-- The componentwise imaginary part `EC n k →L[ℝ] ER n k`. -/
def extImCLM (n k : ℕ) : EC n k →L[ℝ] ER n k :=
  (KAM.Canonical.imCLM n).prodMap (KAM.Canonical.imCLM (n + (k + k)))

theorem extImCLM_apply (w : EC n k) :
    extImCLM n k w = (fun i => (w.1 i).im, fun i => (w.2 i).im) := rfl

theorem extImCLM_eq_zero_iff (w : EC n k) : extImCLM n k w = 0 ↔ extCx (extRe w) = w := by
  constructor
  · intro h
    have h1 : ∀ i, (w.1 i).im = 0 := fun i => congrFun (congrArg Prod.fst h) i
    have h2 : ∀ i, (w.2 i).im = 0 := fun i => congrFun (congrArg Prod.snd h) i
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp [extCx, extRe, Complex.ext_iff, h1, h2]
  · intro h
    have h1 := congrFun (congrArg Prod.fst h)
    have h2 := congrFun (congrArg Prod.snd h)
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := congrArg Complex.im (h1 i)
      simpa [extImCLM_apply, extCx, extRe] using this.symm
    · have := congrArg Complex.im (h2 i)
      simpa [extImCLM_apply, extCx, extRe] using this.symm

/-- Generic real-preservation wrapper: Part 5 flow_e needs coordinate regrouping. -/
theorem flow_real (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε)
    (hr : ∀ z : ER n k, extCx z ∈ Ω → extCx (extRe (F (extCx z))) = F (extCx z))
    {z : ER n k} (hz : extCx z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    extCx (extRe (KAM.Canonical.flow F Ω t (extCx z))) = KAM.Canonical.flow F Ω t (extCx z) := by
  open KAM.Canonical in
  have htI : t ∈ Icc (-1 : ℝ) 1 := abs_le.1 ht
  set x : EC n k := extCx z with hxdef
  have hxR : extImCLM n k x = 0 := (extImCLM_eq_zero_iff x).2 (by
    ext i <;> simp [hxdef, extCx, extRe])
  set Φ := KAM.Canonical.flow F Ω t x with hΦ
  rw [← extImCLM_eq_zero_iff]
  set T := extImCLM n k with hT
  have hFreal : ∀ w ∈ Ω, T w = 0 → T (F w) = 0 := by
    intro w hw hTw
    have hw' : extCx (extRe w) = w := (extImCLM_eq_zero_iff w).1 hTw
    have := hr (extRe w) (by rw [hw']; exact hw)
    rw [hw'] at this
    exact (extImCLM_eq_zero_iff _).2 this
  -- the Picard iterates stay real
  have hpic : ∀ j : ℕ, ∀ τ ∈ Icc (-1 : ℝ) 1, T (picard F j τ x) = 0 := by
    intro j
    induction j with
    | zero => intro τ _; simpa [picard_zero] using hxR
    | succ j ih =>
      intro τ hτ
      have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hsub : uIcc (0 : ℝ) τ ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 hτ
      have hint := intervalIntegrable_picard_field hF j hz hτ
      rw [picard_succ, map_add, hxR, zero_add, ← T.intervalIntegral_comp_comm hint]
      have hzz : ∀ s ∈ uIcc (0 : ℝ) τ, T (F (picard F j s x)) = 0 := by
        intro s hs
        have hsI := hsub hs
        have hΩ : picard F j s x ∈ Ω := mem_of_displacement hF hz hsI (by
          simpa using (picard_regular hF j).2 s hsI x hz)
        exact hFreal _ hΩ (ih s hsI)
      rw [intervalIntegral.integral_congr hzz]
      simp
  -- the flow is the limit
  obtain ⟨η, Λ, hη, hΛ, -, hest⟩ := picard_flow_estimate hF hz
  have hx0 : ‖W (x - x)‖ < η := by simpa using hη
  set C : ℝ := ‖T‖ * ‖W.symm.toContinuousLinearMap‖ with hC
  have hbd : ∀ j : ℕ, ‖T (Φ)‖ ≤ C * (ε * (Λ ^ j / (j.factorial : ℝ))) := by
    intro j
    have h1 : T (Φ) = - T (picard F j t x - Φ) := by
      rw [map_sub, hpic j t htI]; simp
    have h2 : ‖picard F j t x - Φ‖ ≤
        ‖W.symm.toContinuousLinearMap‖ * ‖W (picard F j t x - Φ)‖ := by
      have := W.symm.toContinuousLinearMap.le_opNorm (W (picard F j t x - Φ))
      simpa using this
    have h3 := (hest x hx0 j t htI).trans (picard_bound_le hF.eps_nonneg hΛ htI j)
    rw [h1, norm_neg]
    calc ‖T (picard F j t x - Φ)‖ ≤ ‖T‖ * ‖picard F j t x - Φ‖ :=
          T.le_opNorm _
      _ ≤ ‖T‖ * (‖W.symm.toContinuousLinearMap‖ * ‖W (picard F j t x - Φ)‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ ‖T‖ * (‖W.symm.toContinuousLinearMap‖ * (ε * (Λ ^ j / (j.factorial : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by rw [hC]; ring
  have hlim := ((FloorSemiring.tendsto_pow_div_factorial_atTop Λ).const_mul ε).const_mul C
  have hle : ‖T (Φ)‖ ≤ C * (ε * 0) := ge_of_tendsto' (by simpa using hlim) hbd
  simpa using hle

end KAM.Nekhoroshev

end
