/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealSmoothOnto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The flow of a real field is real (blueprint-W `bpW:w5:flow` (iv), step `f-real`)

* `holoFlow_real_of_field_real`: let the real points of `F` be the common zeros of a family of
  continuous real-linear functionals `L i`. If the field `X` maps real points of `V` to real
  vectors, the flow `holoFlow X t` maps real points of `U` to real points (`|t| ≤ 1`). Proof: every
  Picard iterate is real (induction; the integral of a real-valued curve is real), and the real
  points form a closed set.
* `stepRealFun`: the functionals `w ↦ im` of the coordinates of `w ∈ StepPhase r`;
  `stepReal_iff_stepRealFun`: `StepReal (toK w)` iff they all vanish.
* `stepReal_kamHomEmbed`: the inclusion `ι : 𝒫^{p_+} → 𝒫` (real diagonal) preserves real points.
* `stepFlow_real`: the concrete flow of `X_F` maps real points of `D(s-2σ, r/2)` to real points
  when `X_F` is real at the real points of `D(s-σ, r)`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

open KAM

section abstract

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} {κ : Type*} {L : κ → F →L[ℝ] ℝ}

/-- Every Picard iterate of a real field from a real point is real on `[-1, 1]`. -/
theorem wavePicard_real_of_field_real (h : FlowHyp X V U M δ)
    (hX : ∀ z ∈ V, (∀ i, L i z = 0) → ∀ i, L i (X z) = 0) {w : F} (hw : w ∈ U)
    (hwr : ∀ i, L i w = 0) (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (i : κ) :
    L i (wavePicard X w k t) = 0 := by
  induction k generalizing t i with
  | zero => simpa using hwr i
  | succ k ih =>
    rw [wavePicard_succ, map_add, hwr i, zero_add]
    have hint : IntervalIntegrable (fun σ => X (wavePicard X w k σ)) volume 0 t :=
      ((continuousOn_X_picard h hw k).mono (uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht))
        |>.intervalIntegrable
    rw [← (L i).intervalIntegral_comp_comm hint]
    have hz : ∀ σ ∈ uIcc (0 : ℝ) t, L i (X (wavePicard X w k σ)) = 0 := fun σ hσ => by
      have hσ' : σ ∈ Icc (-1 : ℝ) 1 := uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht hσ
      exact hX _ (h.mem_V_of_ball hw (picard_mem_ball h hw k hσ')) (fun j => ih hσ' j) i
    rw [intervalIntegral.integral_congr hz]
    simp

/-- **The flow of a real field is real** (`bpW:w5:flow` (iv)). -/
theorem holoFlow_real_of_field_real (h : FlowHyp X V U M δ)
    (hX : ∀ z ∈ V, (∀ i, L i z = 0) → ∀ i, L i (X z) = 0) {w : F} (hw : w ∈ U)
    (hwr : ∀ i, L i w = 0) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (i : κ) :
    L i (holoFlow X t w) = 0 := by
  have h1 : Tendsto (fun K => L i (wavePicard X w K t)) atTop (𝓝 (L i (holoFlow X t w))) :=
    ((L i).continuous.tendsto _).comp (tendsto_picard h hw ht)
  have h2 : (fun K => L i (wavePicard X w K t)) = fun _ => (0 : ℝ) :=
    funext fun K => wavePicard_real_of_field_real h hX hw hwr K ht i
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

end abstract

/-! ### Real points of `StepPhase r` -/

/-- Index set of the real coordinates of `KamPhase`: `Θ_i`, `Y_i`, `U_j`, `V_j`. -/
abbrev StepRealIdx : Type := Fin 2 ⊕ Fin 2 ⊕ ℕ+ ⊕ ℕ+

/-- The `ℂ`-linear coordinate functionals of `KamPhase`. -/
def stepCoordCLM : StepRealIdx → KamPhase →L[ℂ] ℂ
  | Sum.inl i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ _ _)
  | Sum.inr (Sum.inl i) => (ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))
  | Sum.inr (Sum.inr (Sum.inl j)) => (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp
      ((ContinuousLinearMap.fst ℂ _ _).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)))
  | Sum.inr (Sum.inr (Sum.inr j)) => (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp
      ((ContinuousLinearMap.snd ℂ _ _).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)))

/-- The functionals `w ↦ im (coordinate of w)` on `StepPhase r`. -/
def stepRealFun (r : ℝ) [Fact (0 < r)] (i : StepRealIdx) : StepPhase r →L[ℝ] ℝ :=
  Complex.imCLM.comp (((stepCoordCLM i).comp (stepToKCLM r)).restrictScalars ℝ)

theorem stepRealFun_apply (r : ℝ) [Fact (0 < r)] (i : StepRealIdx) (w : StepPhase r) :
    stepRealFun r i w = (stepCoordCLM i (StepPhase.toK w)).im := rfl

/-- `StepReal` is the vanishing of the functionals `stepRealFun`. -/
theorem stepReal_iff_stepRealFun (r : ℝ) [Fact (0 < r)] (w : StepPhase r) :
    StepReal (StepPhase.toK w) ↔ ∀ i, stepRealFun r i w = 0 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i
    rcases i with i | i | j | j
    · exact h1 i
    · exact h2 i
    · exact h3 j
    · exact h4 j
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr (Sum.inl i)),
      fun j => h (Sum.inr (Sum.inr (Sum.inl j))), fun j => h (Sum.inr (Sum.inr (Sum.inr j)))⟩

/-- The inclusion `ι : 𝒫^{p_+} → 𝒫` (real diagonal coefficients) preserves real points. -/
theorem stepReal_kamHomEmbed {a p pb : ℝ} (hpb : p ≤ pb) {W : KamPhase} (hW : StepReal W) :
    StepReal (kamHomEmbed a p pb hpb W) := by
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have hc : ∀ (x : HomL2) j, (x j).im = 0 → ((homEmbed_gen a p pb hpb x) j).im = 0 :=
    fun x j hx => by
      simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, hx]
      ring
  rw [kamHomEmbed_apply]
  exact ⟨h1, h2, fun j => hc _ j (h3 j), fun j => hc _ j (h4 j)⟩

variable {a p pb s r σ Mf : ℝ} [Fact (0 < r)]

/-- **The flow of `X_F` is real on real points** (`bpW:w5:flow` (iv)), when `X_F` is real at the
real points of `V = D(s-σ, r)`. -/
theorem stepFlow_real (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMδ : Mf < σ / 4)
    (hFr : ∀ z ∈ stepDomain r (s - σ) r, StepReal (StepPhase.toK z) →
      StepReal (StepPhase.toK (stepFieldS ha hp hpb FT r z)))
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) (hwr : StepReal (StepPhase.toK w))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    StepReal (StepPhase.toK
      (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t w)) := by
  have hFl := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 hσs le_rfl hF hMf0 hMδ
  rw [stepReal_iff_stepRealFun]
  refine holoFlow_real_of_field_real hFl (fun z hz hzr => ?_) hw
    ((stepReal_iff_stepRealFun r w).mp hwr) ht
  rw [← stepReal_iff_stepRealFun]
  show StepReal (kamHomEmbed a p pb hpb (StepPhase.toK (stepFieldS ha hp hpb FT r z)))
  exact stepReal_kamHomEmbed hpb (hFr z hz ((stepReal_iff_stepRealFun r z).mpr hzr))

end KAM.Wave
