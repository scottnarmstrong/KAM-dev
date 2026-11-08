/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamConcrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weak conjugacy (blueprint-W `bpW:w5:new-ham` (iii))

`stepWeakConj`: differentiating `H ∘ Φ = N + N̂ + â₀ + P_+` (`stepNewHam_concrete`) at `w ∈ D_+`:
`(DN(Φw) + ϖ(X_P(Φw), ·)) ∘ DΦ(w) = DN(w) + ϖ(X_{N̂}(w), ·) + ϖ(X_{P_+}(w), ·)`.
Here `DN(w')` is the (bounded) derivative of the quadratic form `N`, whose Riesz representative
is the unbounded field `X_N` (see `stepXN_pairing` for the representation).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf : ℝ} [Fact (0 < r)]

/-- **Weak conjugacy** (`bpW:w5:new-ham` (iii)) in derivative form on `StepPhase r`. -/
theorem stepWeakConj {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    {e₁ : ℝ} (he₁ : 0 ≤ e₁) (hT : HomFieldBound_gen ha hp hpb r e₁ T)
    (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    (a0 : ℂ)
    (heq : ∀ w : KamPhase, w.1 ∈ complexStrip 2 (s - σ) →
      waveStepFun ha (homPP hp hpb) T w +
        ((homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb hpb (stepField ha hp hpb FT w)) =
      waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen T) w + a0)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (W : StepPhase r) :
    let ι := stepEmbedCLM a p pb hpb r
    let Z := stepFieldS ha hp hpb FT r
    let Φ := holoFlow (smoothField ι Z) 1
    let DN : StepPhase r → StepPhase r →L[ℂ] ℂ := fun z =>
      ((homDN hG hK0 hΩ ω (stepToHom (StepPhase.toK z))).comp stepToHom).comp (stepToKCLM r)
    let B := stepSympCLM (q := p) (q' := p) ha (by linarith) r
    DN (Φ w) (fderiv ℂ Φ w W) + B (ι (stepXPS X r (Φ w))) (fderiv ℂ Φ w W) =
      DN w W + B (ι (stepFieldS ha hp hpb (homNhatTaylor_gen T) r w)) W +
        B (ι (stepXplusS ha hp hpb X T FT w)) W := by
  intro ι Z Φ DN B
  have hr : 0 < r := Fact.out
  have hMδ : Mf < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hφV : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), Φ w ∈ stepDomain r (s - σ) r := fun w hw =>
    hFlow.mem_V_of_ball (hU'U hw) (holoFlow_mem_ball hFlow (hU'U hw) h1)
  have hφD : ∀ w ∈ stepDomain r (s - σ) r, StepPhase.toK w ∈ kamDomain s r := fun w hw =>
    kamDomain_mono (by linarith) hr le_rfl hw
  have hφd : DifferentiableAt ℂ Φ w :=
    (holomorphicOn_holoFlow hFlow h1).differentiableAt (hFlow.isOpen_U.mem_nhds (hU'U hw))
  have hz := hφV w hw
  -- the left side
  have hN : HasFDerivAt (fun z => stepNfun hG hK0 hΩ ω (StepPhase.toK z)) (DN (Φ w)) (Φ w) :=
    (stepNfun_hasFDerivAt hG hK0 hΩ ω (StepPhase.toK (Φ w))).comp (Φ w)
      (stepToKCLM r).hasFDerivAt
  have hPd := stepPS_hasFDerivAt ha hp hpb hP (hφD _ hz)
  have hL : HasFDerivAt (fun w' => stepNfun hG hK0 hΩ ω (StepPhase.toK (Φ w')) + stepPS P r (Φ w'))
      ((DN (Φ w) + B (ι (stepXPS X r (Φ w)))).comp (fderiv ℂ Φ w)) w :=
    (hN.add hPd).comp w hφd.hasFDerivAt
  -- the right side
  have hVθ : (StepPhase.toK w).1 ∈ complexStrip 2 s := stepDomain_theta_mem (by linarith) hw
  have hN1 : HasFDerivAt (fun z => stepNfun hG hK0 hΩ ω (StepPhase.toK z)) (DN w) w :=
    (stepNfun_hasFDerivAt hG hK0 hΩ ω (StepPhase.toK w)).comp w (stepToKCLM r).hasFDerivAt
  have hN2 := stepFS_hasFDerivAt ha hp hpb (homNhatTaylor_gen T) r hVθ
  have hPp := stepPplusS_hasFDerivAt ha hp hpb hσ hσ1 hσs hη0 hη hP T FT he₁ hT hTn hF hMf0 hMf
    w hw
  have hR : HasFDerivAt (fun w' => stepNfun hG hK0 hΩ ω (StepPhase.toK w') +
      stepFS ha hp hpb (homNhatTaylor_gen T) r w' + a0 + stepPplusS ha hp hpb P T FT w')
      (DN w + B (ι (stepFieldS ha hp hpb (homNhatTaylor_gen T) r w)) +
        B (ι (stepXplusS ha hp hpb X T FT w))) w :=
    (((hN1.add hN2).add_const a0).add hPp)
  have hev : (fun w' => stepNfun hG hK0 hΩ ω (StepPhase.toK (Φ w')) + stepPS P r (Φ w')) =ᶠ[nhds w]
      fun w' => stepNfun hG hK0 hΩ ω (StepPhase.toK w') +
        stepFS ha hp hpb (homNhatTaylor_gen T) r w' + a0 + stepPplusS ha hp hpb P T FT w' := by
    filter_upwards [(stepDomain_isOpen r (s - 5 * σ) (η * r)).mem_nhds hw] with w' hw'
    exact stepNewHam_concrete hG hK0 hΩ ω ha hp hpb hσ hσ1 hσs hη0 hη P T FT hF hMf0 hMf a0
      (hP.holoP.comp (stepToKCLM r).differentiable.differentiableOn (fun z hz => hφD z hz) |>.mono
        (fun z hz => hz)) heq hw'
  have hfd := hL.unique ((hR.congr_of_eventuallyEq hev))
  have := congrArg (fun L => L W) hfd
  simpa using this

end KAM.Wave
