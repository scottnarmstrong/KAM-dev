/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremMod
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `DΦ(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}` (blueprint-W `bpW:w5:flow-calc` (iii), `bpW:w5:step` (i))

In the representative model the smoothing space `𝒫^{p_+}` is `StepPhase r` read in the
`p_+`-representatives, and its inclusion into `𝒫 = 𝒫^p` is the diagonal map
`ι = stepEmbedCLM a p pb hpb r` (`‖ι‖ ≤ 1`). A vector of `𝒫` lies in `𝒫^{p_+}` iff it is `ι W'`.

* `fderiv_holoFlow_smooth_mapsTo`, `fderiv_holoFlow_smooth_onto`: for a smoothing flow
  (`Dφ^t = I + ι ∘ DΨ^t`, `fderiv_holoFlow_smooth`) with `‖DΨ^t(w)‖ < 1`, `Dφ^t(w)` maps `ι G`
  into and onto `ι G` (Neumann series for `I + DΨ^t(w) ∘ ι` on `G`).
* `stepFlow_dPhi_smooth_mapsTo`, `stepFlow_dPhi_smooth_onto`: the concrete flow of `X_F` on
  `D(s-3σ, r/4)` (`bpW:w5:flow-calc` (iii)).
* `StepCore.dPhi_smooth_mapsTo`, `StepCore.dPhi_smooth_onto` on `D_+ = D(s-5σ, ηr)`, and the
  instances `stepTheorem_dPhi_smooth_onto_of_eps0_pos` (`WaveStepHyp`, `bpW:w5:step` (i)) and
  `stepTheoremMod_dPhi_smooth_onto_of_eps0_pos` (`StepHypMod`); hypothesis-taking variants
  (`ε₀ > 0`, carried by `WaveStepHyp`, `StepHypMod`), the source-facing clause is a conjunct of
  `stepTheorem`, `stepTheoremMod` (`StepTheoremSrc.lean`).
* `stepEmbedCLM_injective`: `ι` is injective, so the preimage in `𝒫^{p_+}` is unique.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

section abstract

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}
  (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
  (hb : ∀ z ∈ V, ‖Z z‖ ≤ M)
include h hZ hb

/-- **`Dφ^t(w)` maps `ι G` into `ι G`**: `Dφ^t(w)(ι g) = ι (g + DΨ^t(w)(ι g))`. -/
theorem fderiv_holoFlow_smooth_mapsTo {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (g : G) :
    fderiv ℂ (holoFlow (smoothField ι Z) t) w (ι g) =
      ι (g + fderiv ℂ (smoothDisp ι Z t) w (ι g)) := by
  rw [fderiv_holoFlow_smooth h hZ hb hw ht, map_add]
  rfl

/-- **`Dφ^t(w)` maps `ι G` onto `ι G`** when `‖DΨ^t(w)‖ < 1` and `‖ι‖ ≤ 1`. -/
theorem fderiv_holoFlow_smooth_onto (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hD : ‖fderiv ℂ (smoothDisp ι Z t) w‖ < 1) (g'' : G) :
    ∃ g' : G, fderiv ℂ (holoFlow (smoothField ι Z) t) w (ι g') = ι g'' := by
  set T : G →L[ℂ] G := (fderiv ℂ (smoothDisp ι Z t) w).comp ι with hT
  have hι1 : ‖ι‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by rw [one_mul]; exact hι x)
  have hTn : ‖-T‖ < 1 := by
    rw [norm_neg]
    calc ‖T‖ ≤ ‖fderiv ℂ (smoothDisp ι Z t) w‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℂ (smoothDisp ι Z t) w‖ * 1 :=
          mul_le_mul_of_nonneg_left hι1 (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hD
  set u := Units.oneSub (-T) hTn with hu
  have hu1 : (u : G →L[ℂ] G) = 1 + T := by
    rw [hu, Units.val_oneSub, sub_neg_eq_add]
  refine ⟨(↑u⁻¹ : G →L[ℂ] G) g'', ?_⟩
  rw [fderiv_holoFlow_smooth_mapsTo h hZ hb hw ht]
  congr 1
  have h1 : (u : G →L[ℂ] G) ((↑u⁻¹ : G →L[ℂ] G) g'') = g'' := by
    have := congrArg (fun f : G →L[ℂ] G => f g'') u.mul_inv
    exact this
  rw [hu1] at h1
  simpa [hT] using h1

end abstract

/-- The inclusion `ι : 𝒫^{p_+} → 𝒫` (diagonal with nonzero real coefficients) is injective. -/
theorem stepEmbedCLM_injective {a p pb : ℝ} (hpb : p ≤ pb) (r : ℝ) [Fact (0 < r)] :
    Function.Injective (stepEmbedCLM a p pb hpb r) := by
  intro W W' hWW
  have hK : kamHomEmbed a p pb hpb (StepPhase.toK W) = kamHomEmbed a p pb hpb (StepPhase.toK W') :=
    hWW
  rw [kamHomEmbed_apply, kamHomEmbed_apply] at hK
  have hc : ∀ j, homEmbedCoef_gen a p pb j ≠ 0 := fun j => by
    unfold homEmbedCoef_gen
    exact_mod_cast (div_pos (homWt_pos a p j) (homWt_pos a pb j)).ne'
  have hemb : ∀ x y : HomL2, homEmbed_gen a p pb hpb x = homEmbed_gen a p pb hpb y → x = y :=
    fun x y hxy => by
      ext j
      have := congrArg (fun z : HomL2 => z j) hxy
      simp only [homEmbed_gen, weightedDiagCLM_apply] at this
      exact mul_left_cancel₀ (hc j) this
  obtain ⟨h1, h2, h3, h4⟩ := Prod.ext_iff.mp hK |>.imp id fun h =>
    (Prod.ext_iff.mp h).imp id fun h => Prod.ext_iff.mp h
  show StepPhase.toK W = StepPhase.toK W'
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext (hemb _ _ h3) (hemb _ _ h4)))

section concrete

variable {a p pb s r σ Mf : ℝ} [Fact (0 < r)]

/-- **`DΦ` maps `𝒫^{p_+}` into itself** on `D(s-3σ, r/4)` (`bpW:w5:flow-calc` (iii)). -/
theorem stepFlow_dPhi_smooth_mapsTo (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (W' : StepPhase r) :
    ∃ W'' : StepPhase r,
      fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t) w
          (stepEmbedCLM a p pb hpb r W') = stepEmbedCLM a p pb hpb r W'' := by
  have hMδ : Mf < σ / 4 := by linarith
  have hFl := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ := (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVθ
  have hb : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf := fun z hz =>
    stepFieldS_bound ha hp hpb FT r hF le_rfl hz
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := stepDomain_mono' (by linarith)
    (by have := Fact.out (p := 0 < r); positivity)
    (by have := Fact.out (p := 0 < r); linarith) hw
  exact ⟨_, fderiv_holoFlow_smooth_mapsTo hFl hZ hb hU ht W'⟩

/-- **`DΦ` maps `𝒫^{p_+}` onto itself** on `D(s-3σ, r/4)` (`bpW:w5:flow-calc` (iii)). -/
theorem stepFlow_dPhi_smooth_onto (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (W'' : StepPhase r) :
    ∃ W' : StepPhase r,
      fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t) w
          (stepEmbedCLM a p pb hpb r W') = stepEmbedCLM a p pb hpb r W'' := by
  have hMδ : Mf < σ / 4 := by linarith
  have hFl := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ := (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVθ
  have hb : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf := fun z hz =>
    stepFieldS_bound ha hp hpb FT r hF le_rfl hz
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := stepDomain_mono' (by linarith)
    (by have := Fact.out (p := 0 < r); positivity)
    (by have := Fact.out (p := 0 < r); linarith) hw
  have hball := stepDomain_U_margin hσ hσ1 hσs hw
  have hD := flowII_deriv hFl hZ hb (by positivity : (0 : ℝ) < σ / 8) hball ht
  have hD1 : ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) t) w‖
      < 1 := by
    refine hD.trans_lt ?_
    rw [div_lt_one (by positivity)]
    linarith
  exact fderiv_holoFlow_smooth_onto hFl hZ hb (norm_stepEmbedCLM_apply_le a p pb hpb r) hU ht hD1
    W''

end concrete

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
  [Fact (0 < r)]
include H

/-- `DΦ(w)` maps `𝒫^{p_+}` into `𝒫^{p_+}` on `D_+` (`bpW:w5:step` (i)). -/
theorem dPhi_smooth_mapsTo {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W' : StepPhase r) :
    ∃ W'' : StepPhase r, fderiv ℂ (H.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
      stepEmbedCLM a p pb H.hpb r W'' :=
  stepFlow_dPhi_smooth_mapsTo H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (FT ξ)
    (H.F_field ξ hξ) H.M₀_pos H.mf_le_sigma (H.Dplus_sub_small hw) ⟨by norm_num, le_rfl⟩ W'

/-- `DΦ(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}` on `D_+` (`bpW:w5:step` (i)). -/
theorem dPhi_smooth_onto {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W'' : StepPhase r) :
    ∃ W' : StepPhase r, fderiv ℂ (H.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
      stepEmbedCLM a p pb H.hpb r W'' :=
  stepFlow_dPhi_smooth_onto H.ha H.hp H.hpb H.hσ H.hσ1 (by linarith [H.hσs, H.hσ]) (FT ξ)
    (H.F_field ξ hξ) H.M₀_pos H.mf_le_sigma (H.Dplus_sub_small hw) ⟨by norm_num, le_rfl⟩ W''

end StepCore

/-- **`DΦ(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}`** (blueprint `bpW:w5:step` (i), non-modified case):
for `ξ ∈ Π` and `w ∈ D_+`, `DΦ(w)` sends every `ι W'` to some `ι W''`, and every `ι W''` is the
image of some `ι W'` (`ι : 𝒫^{p_+} → 𝒫` the inclusion, `Φ = H.core.Phi ξ`). -/
theorem stepTheorem_dPhi_smooth_onto_of_eps0_pos
    (H : WaveStepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W'' : StepPhase r, ∃ W' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') :=
  ⟨H.core.dPhi_smooth_mapsTo hξ hw, H.core.dPhi_smooth_onto hξ hw⟩

/-- **`DΦ(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}`**, modified case (blueprint `bpW:w5:step` (i) for
`StepHypMod`; `Φ = H.core.Phi ξ`). -/
theorem stepTheoremMod_dPhi_smooth_onto_of_eps0_pos {β : ℝ}
    (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W'' : StepPhase r, ∃ W' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') :=
  ⟨H.core.dPhi_smooth_mapsTo hξ hw, H.core.dPhi_smooth_onto hξ hw⟩

end KAM.Wave
