/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPeriodic
public import KAM.Wave.KamStep.StepPlusAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Translation equivariance of `Φ` and periodicity of `P_+` (blueprint-W `bpW:w5:flow` (iv),
`bpW:w5:new-ham` (ii), "periodic")

`stepFlow_translate`: `Φ(w + τ_k) = Φ(w) + τ_k` for `w ∈ D(s-2σ, r/2)`;
`stepPplusS_periodic`: `P_+(w + τ_k) = P_+(w)` on `D_+` when `P` is periodic.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf : ℝ} [Fact (0 < r)]

/-- The angle translation on `StepPhase r`. -/
def stepTauS (r : ℝ) (k : Fin 2) : StepPhase r := StepPhase.ofK (stepTau k)

theorem toK_add_tauS (w : StepPhase r) (k : Fin 2) :
    StepPhase.toK (w + stepTauS r k) = StepPhase.toK w + stepTau k := rfl

theorem stepDomain_add_tauS {ρ S r' : ℝ} {w : StepPhase ρ} (hw : w ∈ stepDomain ρ S r') (k : Fin 2)
    :
    w + stepTauS ρ k ∈ stepDomain ρ S r' := kamDomain_add_tau hw k

theorem stepFieldS_add_tau (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    {w : StepPhase r} (hw : (StepPhase.toK w).1 ∈ complexStrip 2 s) (k : Fin 2) :
    stepFieldS ha hp hpb T r (w + stepTauS r k) = stepFieldS ha hp hpb T r w := by
  unfold stepFieldS
  rw [toK_add_tauS, stepField_add_tau ha hp hpb T hw k]

theorem stepFS_add_tau (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    {w : StepPhase r} (hw : (StepPhase.toK w).1 ∈ complexStrip 2 s) (k : Fin 2) :
    stepFS ha hp hpb T r (w + stepTauS r k) = stepFS ha hp hpb T r w := by
  unfold stepFS
  rw [toK_add_tauS, stepFun_add_tau ha (homPP hp hpb) T hw k]

theorem stepBrG_add_tau (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 ≤ σ)
    (TG : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ)) {w : StepPhase r}
    (hw : (StepPhase.toK w).1 ∈ complexStrip 2 (s - σ)) (k : Fin 2) :
    stepBrG ha hp hpb TG FT (w + stepTauS r k) = stepBrG ha hp hpb TG FT w := by
  have hw' : (StepPhase.toK w).1 ∈ complexStrip 2 s := fun i => (hw i).trans_le (by linarith)
  unfold stepBrG
  rw [stepFieldS_add_tau ha hp hpb TG hw' k, stepFieldS_add_tau ha hp hpb FT hw k]

/-- **Translation equivariance of `Φ`** (`bpW:w5:flow` (iv)). -/
theorem stepFlow_translate (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMδ : Mf < σ / 4)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) (k : Fin 2) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t
        (w + stepTauS r k) =
      holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t w +
        stepTauS r k := by
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 hσs le_rfl hF hMf0 hMδ
  refine holoFlow_translate hFlow (stepTauS r k) (fun z hz => ?_)
    (fun z hz => stepDomain_add_tauS hz k) (fun z hz => stepDomain_add_tauS hz k) hw ht
  simp only [smoothField]
  rw [stepFieldS_add_tau ha hp hpb FT (stepDomain_theta_mem le_rfl hz) k]

/-- **`P_+` is periodic** (`bpW:w5:new-ham` (ii)) when `P` is. -/
theorem stepPplusS_periodic (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8) {P : KamPhase → ℂ}
    (hPper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) (k : Fin 2) :
    stepPplusS ha hp hpb P T FT (w + stepTauS r k) = stepPplusS ha hp hpb P T FT w := by
  have hr : 0 < r := Fact.out
  have hMδ : Mf < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hU := hU'U hw
  have hφV : ∀ t ∈ Icc (0 : ℝ) 1,
      holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t w ∈
        stepDomain r (s - σ) r := fun t ht =>
    hFlow.mem_V_of_ball hU (holoFlow_mem_ball hFlow hU ⟨by linarith [ht.1], ht.2⟩)
  have hD : ∀ z ∈ stepDomain r (s - σ) r, StepPhase.toK z ∈ kamDomain s r := fun z hz =>
    kamDomain_mono (by linarith) hr le_rfl hz
  have hθ : ∀ z ∈ stepDomain r (s - σ) r, (StepPhase.toK z).1 ∈ complexStrip 2 s := fun z hz =>
    fun i => (hD z hz).1 i
  have hΦ := stepFlow_translate (Mf := Mf) ha hp hpb hσ hσ1 (by linarith : 2 * σ < s) FT hF hMf0
    hMδ hU k (t := 1) ⟨by norm_num, le_rfl⟩
  have h1 := hφV 1 ⟨by norm_num, le_rfl⟩
  unfold stepPplusS
  rw [hΦ]
  have e1 : stepPS P r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
      (stepFieldS ha hp hpb FT r)) 1 w + stepTauS r k) =
      stepPS P r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
      (stepFieldS ha hp hpb FT r)) 1 w) := by
    unfold stepPS; rw [toK_add_tauS]; exact hPper k _ (hD _ h1)
  rw [e1, stepFS_add_tau ha hp hpb T (hθ _ h1) k]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hΦt := stepFlow_translate (Mf := Mf) ha hp hpb hσ hσ1 (by linarith : 2 * σ < s) FT hF hMf0
    hMδ hU k (t := t) ⟨by linarith [ht.1], ht.2⟩
  have hz := hφV t ht
  show stepGfam ha hp hpb T FT t (holoFlow _ t (w + stepTauS r k)) = stepGfam ha hp hpb T FT t _
  rw [hΦt]
  unfold stepGfam
  rw [stepBrG_add_tau ha hp hpb hσ.le _ FT (by exact stepDomain_theta_mem le_rfl hz) k,
    stepBrG_add_tau ha hp hpb hσ.le _ FT (by exact stepDomain_theta_mem le_rfl hz) k]

end KAM.Wave
