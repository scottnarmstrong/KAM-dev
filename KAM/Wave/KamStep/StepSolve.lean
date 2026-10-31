/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFieldBound
public import KAM.Wave.KamStep.Class
public import KAM.Wave.Homological.TaylorSub
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linearity of the field of a Taylor polynomial (blueprint-W `bpW:w5:solve`, `bpW:w5:flow`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepField_sub`: `stepField (T₁ - T₂) = stepField T₁ - stepField T₂` on `θ ∈ T_s`, used to turn
W4's parameter-Lipschitz bounds (stated for `homSub`) into bounds for differences of fields.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem stepField_sub (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T₁ T₂ : HomTaylor_gen a p pb s)
    {w : KamPhase} (hw : w.1 ∈ complexStrip 2 s) :
    stepField ha hp hpb (T₁.homSub T₂) w = stepField ha hp hpb T₁ w - stepField ha hp hpb T₂ w := by
  have hn : complexStrip 2 s ∈ nhds w.1 := (isOpen_complexStrip 2 s).mem_nhds hw
  have e : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {f g : (Fin 2 → ℂ) → E}, IsHomComp s f → IsHomComp s g → ∀ i,
      homPartial i (fun z => f z - g z) w.1 = homPartial i f w.1 - homPartial i g w.1 :=
    fun hf hg i => homPartial_sub (hf.1.differentiableAt hn) (hg.1.differentiableAt hn) i
  have ha0 := e T₁.comp_a0 T₂.comp_a0
  have hb := e T₁.comp_b T₂.comp_b
  have hcp := e T₁.comp_cp T₂.comp_cp
  have hcm := e T₁.comp_cm T₂.comp_cm
  have hP := e T₁.comp_P T₂.comp_P
  have hQ := e T₁.comp_Q T₂.comp_Q
  have hP' := e T₁.comp_P' T₂.comp_P'
  have hRz : homRz_gen (T₁.homSub T₂) w.1 (stepZ w) (stepZb w) =
      homRz_gen T₁ w.1 (stepZ w) (stepZb w) - homRz_gen T₂ w.1 (stepZ w) (stepZb w) := by
    unfold homRz_gen
    simp only [HomTaylor_gen.homSub, sub_apply, map_sub, smul_sub]
    abel
  have hRzb : homRzb_gen (T₁.homSub T₂) w.1 (stepZ w) (stepZb w) =
      homRzb_gen T₁ w.1 (stepZ w) (stepZb w) - homRzb_gen T₂ w.1 (stepZ w) (stepZb w) := by
    unfold homRzb_gen
    simp only [HomTaylor_gen.homSub, sub_apply, map_sub, smul_sub]
    abel
  have hRθ : ∀ i, homRtheta_gen ha hp hpb (T₁.homSub T₂) i w.1 w.2.1 (stepZ w) (stepZb w) =
      homRtheta_gen ha hp hpb T₁ i w.1 w.2.1 (stepZ w) (stepZb w) -
        homRtheta_gen ha hp hpb T₂ i w.1 w.2.1 (stepZ w) (stepZb w) := by
    intro i
    unfold homRtheta_gen
    have e : ∀ c z, homPairRep_gen ha (homPP hp hpb) c z = stepPr ha (homPP hp hpb) c z :=
      fun _ _ => rfl
    simp only [e, HomTaylor_gen.homSub, ha0, hb, hcp, hcm, hP, hQ, hP', Pi.sub_apply, sub_apply,
      map_sub, mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext ?_ ?_))
  · simp [stepField, HomTaylor_gen.homSub, mul_sub]
  · simp only [stepField, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, hRθ]
    ring
  · simp only [stepField, Prod.snd_sub, Prod.fst_sub]
    unfold homRv_gen
    rw [hRz, hRzb]
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · simp only [stepField, Prod.snd_sub, Prod.fst_sub]
    unfold homRu_gen
    rw [hRz, hRzb]
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_sub, lp.coeFn_add, lp.coeFn_neg, Pi.smul_apply,
      Pi.sub_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    ring

section Fam

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α : ℝ}

/-- **The `λ`-bound for `X_F`** (`bpW:w5:solve`, field part, via W4 `homLemma1_fieldBound_gen`,
`homLemma1_lipschitz_gen`, `homLemma2`): for the family `F_ξ` of solutions of the homological
equation for a family `R_ξ` with `|X_{R_ξ}| ≤ ε` and `|X_{R_ξ} - X_{R_ζ}| ≤ ε^L |ξ-ζ|`,
`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^W_σ/α)(ε + λε^L)`. -/
theorem stepSolve_fam (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL lam σ : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσs : σ < s) (hM : 0 < Mω + MΩ) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ α / (Mω + MΩ)) (hε : 0 ≤ ε) (hεL : 0 ≤ εL)
    (R : (Fin 2 → ℝ) → HomTaylor_gen a p pb s)
    (F : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ))
    (hF : ∀ ξ (hξ : ξ ∈ Par),
      F ξ = homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) (R ξ))
    (hR : ∀ ξ ∈ Par, HomFieldBound_gen ha hp hpb r ε (R ξ))
    (hRL : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
      HomFieldBound_gen ha hp hpb r (εL * ‖ξ - ζ‖) ((R ξ).homSub (R ζ))) :
    FamBound Par (kamDomain (s - σ) r) r lam
      (3 * (7 + 10 * homKS) * waveBW τ σ / α * (ε + lam * εL))
      (fun ξ w => stepField ha hp hpb (F ξ) w) := by
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hC : 0 ≤ (7 + 10 * homKS) * waveBW τ σ / α := by positivity
  refine ⟨(7 + 10 * homKS) * (waveBW τ σ * ε / α),
    (7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α)), by positivity,
    by positivity, ?_, ?_, ?_⟩
  · have := (homLemma2 (α := α) (M := Mω + MΩ) (lam := lam) (σ := σ) (ε := ε) (εL := εL) hτ hα hM
      hlam0 hlam hσ hσ1 hε hεL).2.1
    unfold homLamNorm at this
    exact this
  · intro ξ hξ w hw
    have hb := homLemma1_fieldBound_gen h hH ha hp hpb hr hτ hα hσ hσs hξ (R ξ) (hR ξ hξ)
    rw [← hF ξ hξ] at hb
    have hw' := homDomain_stepZ hw
    rw [kamNorm_stepField ha hp hpb _ hr]
    exact hb _ _ _ _ hw'
  · intro ξ hξ ζ hζ w hw
    have hb := homLemma1_lipschitz_gen h hH ha hp hpb hr hτ hα hεL hσ hσs hξ hζ (R ξ) (R ζ)
      (hR ξ hξ) (hR ζ hζ) (hRL ξ hξ ζ hζ)
    rw [← hF ξ hξ, ← hF ζ hζ] at hb
    have hθ : w.1 ∈ complexStrip 2 (s - σ) := fun i => hw.1 i
    rw [← stepField_sub ha hp hpb _ _ hθ, kamNorm_stepField ha hp hpb _ hr]
    have := hb _ _ _ _ (homDomain_stepZ hw)
    refine this.trans (le_of_eq ?_)
    ring

end Fam

end KAM.Wave
