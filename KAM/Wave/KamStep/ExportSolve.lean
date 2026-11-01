/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremSrc
public import KAM.Wave.KamStep.RealStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The solution of the homological equation in the step as one statement (blueprint `bpW:w5:solve`)

Off-frontier, source-faithful infrastructure (W-GRAPH-CLOSE); the dependency graph is still being
built.

Lemma `bpW:w5:solve` (`w5-kamstep.tex:352-363`): under the step data, with `R` the Taylor polynomial
of `bpW:w5:taylor` and `F`, `N̂`, `â₀` the W4 objects for `R`: `F ∈ T_{s-σ} ∩ S_{p_+}(D(s-σ,r))`,
`N̂ ∈ S_{p_+}(𝒫)`, both real, `R + DN·X_F = N̂ + â₀` on `D(s-σ,r)`, `|X_F|^λ_{r,D(s-σ,r)} ≤ M_F`,
`|X_N̂|^λ_{r,D(s,r)} ≤ 6ε`, `|ω̂| + λ|ω̂|^L ≤ 6πε`, `sup_j (j+2)^{p_+-p}(|Ω̂_j| + λ|Ω̂_j|^L) ≤ 3ε`.

* `stepSolveLemma` (`StepHypSrc`, non-modified case) and `stepSolveLemmaMod` (`StepHypModSrc`,
  modified case, `M_F` read with `c^♮_F`, `t^♮`; the data carry `2β ≤ p+1-p_+`) state the lemma
  for the objects of the step theorem: `R = H.hyp.core.R ξ`, `F = H.hyp.FT ξ` (a member of
  `HomTaylor_gen a p p_+ (s-σ)`, i.e. of `T_{s-σ}`), `N̂ = homNhatTaylor_gen R`,
  `â₀ = H.hyp.core.a0 ξ`, `ω̂ = stepOmegaHat R`, `Ω̂ = stepOmegaTail R`. The `λ`-norms are
  `FamBound` (sup plus `λ` times `ξ`-Lipschitz) and, for `ω̂`, `Ω̂`, a sup bound and a Lipschitz
  bound uniform in `j` whose weighted sum is bounded.
* Reality of `F`: `WaveStepHyp.FT_isRealTaylor`, `StepHypMod.FT_isRealTaylor` (`RealStep.lean`);
  reality of `N̂`: `homNhatTaylor_isReal_gen`.
* `stepNhat_isSmoothing_univ`: `N̂ ∈ S_{p_+}(𝒫)` on all of `𝒫` (its coefficients are constant in
  `θ`, so it is a Taylor polynomial on every strip, `homNhatTaylorWide`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

section Wide

variable {a p pb s : ℝ}

/-- `N̂` of `R`, read on the strip of an arbitrary width `s'` (its coefficients do not depend on
`θ`); it has the same fields as `homNhatTaylor_gen R`. -/
def homNhatTaylorWide (R : HomTaylor_gen a p pb s) (s' : ℝ) : HomTaylor_gen a p pb s' where
  a0 := fun _ => 0
  b := fun _ => homCoeff R.b 0
  cp := fun _ => 0
  cm := fun _ => 0
  P := fun _ => 0
  P' := fun _ => 0
  Q := fun _ => kamEntryDiagCLM (homCoeff R.Q 0)
  Qt := fun _ => kamEntryDiagCLM (homCoeff R.Q 0)
  comp_a0 := isHomComp_const s' _
  comp_b := isHomComp_const s' _
  comp_cp := isHomComp_const s' _
  comp_cm := isHomComp_const s' _
  comp_P := isHomComp_const s' _
  comp_P' := isHomComp_const s' _
  comp_Q := isHomComp_const s' _
  comp_Qt := isHomComp_const s' _
  symP := fun _ _ i j => by simp [homNormalEntry_gen, kamEntry]
  symP' := fun _ _ i j => by simp [homNormalEntry_gen, kamEntry]
  transQ := fun _ _ i j => by
    by_cases hij : i = j
    · subst hij; rfl
    · simp [homNormalEntry_gen, kamEntry_diagCLM, hij, Ne.symm hij]

theorem mem_complexStrip_sum_abs (θ : Fin 2 → ℂ) :
    θ ∈ complexStrip 2 (∑ i, |(θ i).im| + 1) := fun i => by
  have := Finset.single_le_sum (f := fun j => |(θ j).im|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  linarith

/-- **`N̂ ∈ S_{p_+}(𝒫)`** (`bpW:w5:solve`): `N̂` is holomorphic with holomorphic field on all of
`𝒫`, and `DN̂ · W = ϖ(X_N̂, W)` everywhere. -/
theorem stepNhat_isSmoothing_univ (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (R : HomTaylor_gen a p pb s) :
    IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) univ
      (waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen R))
      (stepField ha hp hpb (homNhatTaylor_gen R)) := by
  have e1 : ∀ w : KamPhase, waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen R) =
      waveStepFun ha (homPP hp hpb) (homNhatTaylorWide R (∑ i, |(w.1 i).im| + 1)) := fun _ => rfl
  have e2 : ∀ w : KamPhase, stepField ha hp hpb (homNhatTaylor_gen R) =
      stepField ha hp hpb (homNhatTaylorWide R (∑ i, |(w.1 i).im| + 1)) := fun _ => rfl
  refine ⟨fun w _ => ?_, fun w _ => ?_, fun w _ W => ?_⟩
  · rw [e1 w]
    obtain ⟨D, hD, -⟩ := stepFun_field ha hp hpb _ (mem_complexStrip_sum_abs w.1)
    exact hD.differentiableAt.differentiableWithinAt
  · rw [e2 w]
    exact (stepField_differentiableAt ha hp hpb _
      (mem_complexStrip_sum_abs w.1)).differentiableWithinAt
  · rw [e1 w, e2 w]
    obtain ⟨D, hD, hDW⟩ := stepFun_field ha hp hpb _ (mem_complexStrip_sum_abs w.1)
    rw [hD.fderiv, hDW, stepSymp_comm_weights ha (by linarith) (by linarith)]

end Wide

variable {a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
include H

/-- `F ∈ S_{p_+}(D(s-σ, r))`. -/
theorem solve_F_isSmoothing (ξ : Fin 2 → ℝ) :
    IsSmoothing (p := p) H.ha H.pb_pos (kamDomain (s - σ) r)
      (waveStepFun H.ha (homPP H.hp H.hpb) (FT ξ)) (stepField H.ha H.hp H.hpb (FT ξ)) :=
  stepFun_isSmoothing H.ha H.hp H.hpb (FT ξ) le_rfl

/-- `|X_F|^λ_{r, D(s-σ, r)} ≤ M_F`. -/
theorem solve_F_famBound : FamBound Par (kamDomain (s - σ) r) r lam (stepMF cF tF α σ ε)
    (fun ξ w => stepField H.ha H.hp H.hpb (FT ξ) w) := by
  have hr := H.hr
  refine ⟨M₀, M₁, H.M₀_pos.le, H.M₁_nonneg, H.M_sum, fun ξ hξ w hw => ?_,
    fun ξ hξ ζ hζ w hw => ?_⟩
  · rw [kamNorm_stepField H.ha H.hp H.hpb _ hr]
    exact H.F_field ξ hξ _ _ _ _ (homDomain_stepZ hw)
  · have hθ : w.1 ∈ complexStrip 2 (s - σ) := fun i => hw.1 i
    rw [← stepField_sub H.ha H.hp H.hpb _ _ hθ, kamNorm_stepField H.ha H.hp H.hpb _ hr]
    exact H.F_sub ξ hξ ζ hζ _ _ _ _ (homDomain_stepZ hw)

/-- `|X_N̂|^λ_{r, D(s, r)} ≤ 6ε`. -/
theorem solve_Nhat_famBound : FamBound Par (kamDomain s r) r lam (6 * ε)
    (fun ξ w => stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.R ξ)) w) := by
  have h0 := H.hε₀
  have h1 := H.hε₁
  refine (stepNhat_fam H.ha H.hp H.hpb H.hr H.hs H.hlam0 (by linarith : 0 ≤ 3 * ε₀)
    (by linarith : 0 ≤ 3 * ε₁) H.R H.R_field H.R_sub).famMono subset_rfl ?_
  have e : 2 * (3 * ε₀ + lam * (3 * ε₁)) = 6 * (ε₀ + lam * ε₁) := by ring
  rw [e]; linarith [H.hε]

/-- `|ω̂| + λ|ω̂|^L ≤ 6πε`. -/
theorem solve_omegaHat : ∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + lam * b₁ ≤ 6 * Real.pi * ε ∧
    (∀ ξ ∈ Par, ‖stepOmegaHat (H.R ξ)‖ ≤ b₀) ∧
    ∀ ξ ∈ Par, ∀ ζ ∈ Par, ‖stepOmegaHat (H.R ξ) - stepOmegaHat (H.R ζ)‖ ≤ b₁ * ‖ξ - ζ‖ := by
  have h0 := H.hε₀.le
  have h1 := H.hε₁
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * (3 * ε₀), 2 * Real.pi * (3 * ε₁), by positivity, by positivity, ?_,
    fun ξ hξ => stepOmegaHat_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_field ξ hξ),
    fun ξ hξ ζ hζ => ?_⟩
  · have e : 2 * Real.pi * (3 * ε₀) + lam * (2 * Real.pi * (3 * ε₁)) =
        6 * Real.pi * (ε₀ + lam * ε₁) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left H.hε (by positivity)
  · rw [stepOmegaHat_sub H.hs]
    exact (stepOmegaHat_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_sub ξ hξ ζ hζ)).trans_eq (by ring)

/-- `sup_j (j+2)^{p_+-p}(|Ω̂_j| + λ|Ω̂_j|^L) ≤ 3ε`. -/
theorem solve_OmegaTail : ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + lam * c₁ ≤ 3 * ε ∧
    (∀ ξ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.R ξ) j| ≤ c₀) ∧
    ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+,
      ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.R ξ) j - stepOmegaTail (H.R ζ) j| ≤
        c₁ * ‖ξ - ζ‖ := by
  have h0 := H.hε₀.le
  have h1 := H.hε₁
  refine ⟨3 * ε₀, 3 * ε₁, by positivity, by positivity, ?_,
    fun ξ hξ j => stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_field ξ hξ) j,
    fun ξ hξ ζ hζ j => ?_⟩
  · have e : 3 * ε₀ + lam * (3 * ε₁) = 3 * (ε₀ + lam * ε₁) := by ring
    rw [e]; linarith [H.hε]
  · rw [stepOmegaTail_sub H.hs]
    exact stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_sub ξ hξ ζ hζ) j

/-- `R + DN·X_F = N̂ + â₀` on `D(s-σ, r)`. -/
theorem solve_equation {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : KamPhase}
    (hw : w ∈ kamDomain (s - σ) r) :
    waveStepFun H.ha (homPP H.hp H.hpb) (H.R ξ) w +
        ((homDN H.hG (by linarith [H.freq.consts_nonneg.1] : 0 ≤ 1 + M0)
            (homOmega_le H.freq hξ) (ω ξ) (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb H.hpb (stepField H.ha H.hp H.hpb (FT ξ) w)) =
      waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.R ξ)) w + H.a0 ξ :=
  H.equation ξ hξ w fun i => hw.1 i

end StepCore

/-- **The solution of the homological equation in the step** (blueprint Lemma `bpW:w5:solve`,
non-modified case). Under the step data, for `R = H.hyp.core.R ξ` (the Taylor polynomial of
`bpW:w5:taylor`) and `F = H.hyp.FT ξ`, `N̂ = homNhatTaylor_gen R`, `â₀ = H.hyp.core.a0 ξ` (the W4
objects for `R`): `F ∈ T_{s-σ} ∩ S_{p_+}(D(s-σ, r))`, `N̂ ∈ S_{p_+}(𝒫)`, both real,
`R + DN·X_F = N̂ + â₀` on `D(s-σ, r)`, `|X_F|^λ_{r,D(s-σ,r)} ≤ M_F`, `|X_N̂|^λ_{r,D(s,r)} ≤ 6ε`,
`|ω̂| + λ|ω̂|^L ≤ 6πε` and `sup_j (j+2)^{p_+-p}(|Ω̂_j| + λ|Ω̂_j|^L) ≤ 3ε`. -/
theorem stepSolveLemma
    (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) :
    (∀ ξ (hξ : ξ ∈ Par),
      IsSmoothing (p := p) H.ha H.hyp.core.pb_pos (kamDomain (s - σ) r)
        (waveStepFun H.ha (homPP H.hp H.hpb) (H.hyp.FT ξ))
        (stepField H.ha H.hp H.hpb (H.hyp.FT ξ)) ∧
      IsSmoothing (p := p) H.ha H.hyp.core.pb_pos univ
        (waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.hyp.core.R ξ)))
        (stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ))) ∧
      (H.hyp.FT ξ).isRealTaylor ∧ (homNhatTaylor_gen (H.hyp.core.R ξ)).isRealTaylor ∧
      ∀ w ∈ kamDomain (s - σ) r,
        waveStepFun H.ha (homPP H.hp H.hpb) (H.hyp.core.R ξ) w +
            ((homDN H.hG (by linarith [H.freq.consts_nonneg.1] : 0 ≤ 1 + M0)
              (homOmega_le H.freq hξ) (ω ξ) (stepToHom w)).comp
              stepToHom) (kamHomEmbed a p pb H.hpb (stepField H.ha H.hp H.hpb (H.hyp.FT ξ) w)) =
          waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.hyp.core.R ξ)) w +
            H.hyp.core.a0 ξ) ∧
    FamBound Par (kamDomain (s - σ) r) r lam (stepMF (stepCF τ) (stepExpT τ) α σ ε)
      (fun ξ w => stepField H.ha H.hp H.hpb (H.hyp.FT ξ) w) ∧
    FamBound Par (kamDomain s r) r lam (6 * ε)
      (fun ξ w => stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ)) w) ∧
    (∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + lam * b₁ ≤ 6 * Real.pi * ε ∧
      (∀ ξ ∈ Par, ‖stepOmegaHat (H.hyp.core.R ξ)‖ ≤ b₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par,
        ‖stepOmegaHat (H.hyp.core.R ξ) - stepOmegaHat (H.hyp.core.R ζ)‖ ≤ b₁ * ‖ξ - ζ‖) ∧
    (∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + lam * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Par, ∀ j : ℕ+,
        ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.hyp.core.R ξ) j| ≤ c₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |stepOmegaTail (H.hyp.core.R ξ) j - stepOmegaTail (H.hyp.core.R ζ) j| ≤
          c₁ * ‖ξ - ζ‖) :=
  ⟨fun ξ hξ => ⟨H.hyp.core.solve_F_isSmoothing ξ,
      stepNhat_isSmoothing_univ H.ha H.hp H.hpb (H.hyp.core.R ξ),
      WaveStepHyp.FT_isRealTaylor H.hyp ξ hξ,
      homNhatTaylor_isReal_gen H.hs (H.hyp.core.R ξ) (H.hyp.core.R_isRealTaylor hξ),
      fun _ hw => H.hyp.core.solve_equation hξ hw⟩,
    H.hyp.core.solve_F_famBound, H.hyp.core.solve_Nhat_famBound, H.hyp.core.solve_omegaHat,
    H.hyp.core.solve_OmegaTail⟩

/-- **The solution of the homological equation in the step** (blueprint Lemma `bpW:w5:solve`,
modified case). Under the step data, for `R = H.hyp.core.R ξ` (the Taylor polynomial of
`bpW:w5:taylor`) and `F = H.hyp.FT ξ`, `N̂ = homNhatTaylor_gen R`, `â₀ = H.hyp.core.a0 ξ` (the W4
objects for `R`): `F ∈ T_{s-σ} ∩ S_{p_+}(D(s-σ, r))`, `N̂ ∈ S_{p_+}(𝒫)`, both real,
`R + DN·X_F = N̂ + â₀` on `D(s-σ, r)`, `|X_F|^λ_{r,D(s-σ,r)} ≤ M_F`, `|X_N̂|^λ_{r,D(s,r)} ≤ 6ε`,
`|ω̂| + λ|ω̂|^L ≤ 6πε` and `sup_j (j+2)^{p_+-p}(|Ω̂_j| + λ|Ω̂_j|^L) ≤ 3ε`. -/
theorem stepSolveLemmaMod
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) :
    (∀ ξ (hξ : ξ ∈ Par),
      IsSmoothing (p := p) H.ha H.hyp.core.pb_pos (kamDomain (s - σ) r)
        (waveStepFun H.ha (homPP H.hp H.hpb) (H.hyp.FT ξ))
        (stepField H.ha H.hp H.hpb (H.hyp.FT ξ)) ∧
      IsSmoothing (p := p) H.ha H.hyp.core.pb_pos univ
        (waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.hyp.core.R ξ)))
        (stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ))) ∧
      (H.hyp.FT ξ).isRealTaylor ∧ (homNhatTaylor_gen (H.hyp.core.R ξ)).isRealTaylor ∧
      ∀ w ∈ kamDomain (s - σ) r,
        waveStepFun H.ha (homPP H.hp H.hpb) (H.hyp.core.R ξ) w +
            ((homDN H.hG (by linarith [H.freq.consts_nonneg.1] : 0 ≤ 1 + M0)
              (homOmega_le H.freq hξ) (ω ξ) (stepToHom w)).comp
              stepToHom) (kamHomEmbed a p pb H.hpb (stepField H.ha H.hp H.hpb (H.hyp.FT ξ) w)) =
          waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.hyp.core.R ξ)) w +
            H.hyp.core.a0 ξ) ∧
    FamBound Par (kamDomain (s - σ) r) r lam (stepMF (stepCFn τ) (stepTn τ) α σ ε)
      (fun ξ w => stepField H.ha H.hp H.hpb (H.hyp.FT ξ) w) ∧
    FamBound Par (kamDomain s r) r lam (6 * ε)
      (fun ξ w => stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ)) w) ∧
    (∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + lam * b₁ ≤ 6 * Real.pi * ε ∧
      (∀ ξ ∈ Par, ‖stepOmegaHat (H.hyp.core.R ξ)‖ ≤ b₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par,
        ‖stepOmegaHat (H.hyp.core.R ξ) - stepOmegaHat (H.hyp.core.R ζ)‖ ≤ b₁ * ‖ξ - ζ‖) ∧
    (∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + lam * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Par, ∀ j : ℕ+,
        ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.hyp.core.R ξ) j| ≤ c₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |stepOmegaTail (H.hyp.core.R ξ) j - stepOmegaTail (H.hyp.core.R ζ) j| ≤
          c₁ * ‖ξ - ζ‖) :=
  ⟨fun ξ hξ => ⟨H.hyp.core.solve_F_isSmoothing ξ,
      stepNhat_isSmoothing_univ H.ha H.hp H.hpb (H.hyp.core.R ξ),
      StepHypMod.FT_isRealTaylor H.hyp ξ hξ,
      homNhatTaylor_isReal_gen H.hs (H.hyp.core.R ξ) (H.hyp.core.R_isRealTaylor hξ),
      fun _ hw => H.hyp.core.solve_equation hξ hw⟩,
    H.hyp.core.solve_F_famBound, H.hyp.core.solve_Nhat_famBound, H.hyp.core.solve_omegaHat,
    H.hyp.core.solve_OmegaTail⟩

end KAM.Wave
