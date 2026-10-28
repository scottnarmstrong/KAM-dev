/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationStage
public import KAM.Planetary.WeakKAM.IterationParam

/-! # P11B iteration: the step fields (`O2`–`O5`, the map)

Everything one inductive step contributes: the increments on the whole collar (`stage_delta`),
the scalar bridges between the schedule budgets and the canonical-step constants, and the fields
of `IterPost` for the extended chain (`iterPost_step`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Bridge
variable {d : SelectionData n} {a : SelectionSchedule n} {ch : SelectionChain n} {ν : ℕ}
  (hf : StepFacts a d.C₁ ν)

theorem selectionA_eq_stage : selectionA a ν = p11StepA (stageS d a ch ν hf) := by
  unfold selectionA p11StepA
  simp only [selectionΛ_eq_p11Lambda, selectionCutoffError_eq_p11Error]
  rfl

theorem selectionKappa_eq_stage : selectionKappa a ν = p11StepKappa (stageS d a ch ν hf) := by
  unfold selectionKappa p11StepKappa
  rw [selectionA_eq_stage hf (ch := ch)]
  rfl

theorem selectionAlpha_eq_stage : selectionAlpha a ν =
    (n + 1) * (stageS d a ch ν hf).s * p11StepA (stageS d a ch ν hf) /
      (stageS d a ch ν hf).sigma := by
  unfold selectionAlpha
  rw [selectionA_eq_stage hf (ch := ch)]
  rfl

theorem selectionMapBudget_eq_stage : selectionMapBudget a ν =
    2 * p11StepKappa (stageS d a ch ν hf) + p11StepKappa (stageS d a ch ν hf) *
      (stageS d a ch ν hf).s / (stageS d a ch ν hf).sigma := by
  unfold selectionMapBudget
  rw [selectionKappa_eq_stage hf (ch := ch)]
  rfl

theorem selectionRealBudget_eq_stage : selectionRealBudget a ν =
    2 * (stageS d a ch ν hf).T * (1 + p11Error n (stageS d a ch ν hf).T (stageS d a ch ν hf).d) *
      (stageS d a ch ν hf).eps * p11Lambda n ((stageS d a ch ν hf).r - (stageS d a ch ν hf).d) /
        ((stageS d a ch ν hf).D * (stageS d a ch ν hf).s) := by
  unfold selectionRealBudget
  simp only [selectionΛ_eq_p11Lambda, selectionCutoffError_eq_p11Error]
  rfl

end Bridge

section Delta
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
  (c : WeakBudgetCtx d a) {ch : SelectionChain n} {ν : ℕ}

include c in
/-- The increments of stage `ν` on the whole collar `B_ν` (`stepP:p11a:il-inc`). -/
theorem stage_delta (hpre : IterPre d f a ch ν) (hf : StepFacts a d.C₁ ν) :
    let B := actionNbhd (ch.K ν) (selectiont a ν)
    DifferentiableOn ℂ (p11DeltaH (selectionT a ν) (ch.R ν)) B ∧
    DifferentiableOn ℂ (p11DeltaW (selectionT a ν) (ch.R ν)) B ∧
    p11Bound B (p11DeltaH (selectionT a ν) (ch.R ν))
      ((1 + p11Error n (selectionT a ν) (selectiond a ν)) * selectionε a ν) ∧
    p11Bound B (p11DeltaW (selectionT a ν) (ch.R ν))
      ((1 + p11Error n (selectionT a ν) (selectiond a ν)) * selectionε a ν / selections a ν) ∧
    ∀ b : SelectionR n, selectionReal b ∈ B →
      (p11DeltaH (selectionT a ν) (ch.R ν) (selectionReal b)).im = 0 ∧
      ∀ i, (p11DeltaW (selectionT a ν) (ch.R ν) (selectionReal b) i).im = 0 := by
  intro B
  have hadm := iterPre_admissible hpre
  have hdr : selectiond a ν < selectionr a ν := by
    linarith [hf.radius, hf.σ_pos]
  have hB : IsOpen B := p11_isOpen_actionNbhd _ _
  obtain ⟨h1, h2, h3, h4⟩ := cutoff_delta hf.n_pos (iter_r_pos c ν) hf.s_pos hf.T_pos.le
    hf.d_pos hdr hf.eps_nonneg hB hadm.1 hadm.2.1
  refine ⟨h1, h2, h3, h4, fun b hb => ?_⟩
  rw [selectionReal_eq_realInclusion] at hb ⊢
  exact cutoff_delta_real hf.n_pos (iter_r_pos c ν) hf.s_pos hf.T_pos.le hf.d_pos hdr
    hf.eps_nonneg hB hadm.1 hadm.2.1 hadm.2.2 hb

end Delta

section Post
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
  (c : WeakBudgetCtx d a) {ch : SelectionChain n} {ν : ℕ} (hf : StepFacts a d.C₁ ν)
include c

theorem stage_domain_eq :
    domain_def n (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1))) =
    domain_def n ((stageS d a ch ν hf).r - (stageS d a ch ν hf).d - (stageS d a ch ν hf).delta -
      2 * (stageS d a ch ν hf).sigma) ((stageS d a ch ν hf).q * (stageS d a ch ν hf).s)
      (actionNbhd (stageS d a ch ν hf).E (stageS d a ch ν hf).t) := by
  show domain_def n (selectionr a (ν + 1)) (selections a (ν + 1)) _ =
    domain_def n (selectionr a ν - selectiond a ν - selectionσ a ν - 2 * selectionσ a ν)
      (selectionQ n a.μ a.τ * selections a ν) _
  rw [iter_rr c ν, iter_s_succ]
  rfl

theorem stage_domain_eq' :
    domain_def n (selectionr a (ν + 1) + selectionσ a ν) (selections a ν)
      (actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1))) =
    domain_def n (((stageS d a ch ν hf).r - (stageS d a ch ν hf).d - (stageS d a ch ν hf).delta -
      2 * (stageS d a ch ν hf).sigma) + (stageS d a ch ν hf).sigma) (stageS d a ch ν hf).s
      (actionNbhd (stageS d a ch ν hf).E (stageS d a ch ν hf).t) := by
  show domain_def n (selectionr a (ν + 1) + selectionσ a ν) (selections a ν) _ =
    domain_def n ((selectionr a ν - selectiond a ν - selectionσ a ν - 2 * selectionσ a ν) +
      selectionσ a ν) (selections a ν) _
  rw [iter_rr c ν]
  rfl

theorem iterPost_step (hpre : IterPre d f a ch ν) :
    IterPost d a (stepChain d a ch ν hf) ν := by
  have hext := hpre.chain.toSelectionExtensionChain
  have H := stage_hyp c hpre hf
  have hsub := retained_collar_sub c (ch := ch) (ν := ν)
  have hadm := iterPre_admissible hpre
  have hreal := p11Real_mono hsub hadm.2.2
  have cs := canonical_step H
  have csi := canonical_step_simple_inverse H
  have csr := canonical_step_real H hreal
  have hdel := stage_delta c hpre hf
  have hU := stage_domain_eq c (ch := ch) hf
  have hU2 := stage_domain_eq' c (ch := ch) hf
  have hAe := selectionA_eq_stage hf (ch := ch)
  have hαe := selectionAlpha_eq_stage hf (ch := ch)
  dsimp only at cs csi csr hdel
  obtain ⟨-, -, -, -, hF, hmaps, hdisp, -, hder, hsymp, hper, -, -, -, -⟩ := cs
  obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hdel
  have hF' : DifferentiableOn ℂ (p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν)
      (ch.R ν)) (domain_def n (selectionr a (ν + 1)) (selections a (ν + 1))
      (actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1)))) := by
    rw [hU]; exact hF
  have hmemU : ∀ (z : SelectionPhaseC n) (b : SelectionC n),
      z.1 ∈ complexStrip n (selectionr a (ν + 1)) → ‖z.2‖ < selections a (ν + 1) →
      b ∈ actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1)) →
      ((z, b) : P11Family n) ∈ domain_def n (selectionr a (ν + 1)) (selections a (ν + 1))
        (actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1))) :=
    fun z b h1 h2 h3 => p11_mem_domain_def.2 ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stepChain_Δh_self, stepChain_K_self]; exact hd1
  · intro b hb
    simp only [stepChain_Δh_self, stepChain_K_self] at hb ⊢
    exact (hd5 b hb).1
  · intro b hb
    simp only [stepChain_Δh_self, stepChain_K_self] at hb ⊢
    have := hd3 b hb
    have hE := iter_E_le_one c ν
    have := hf.eps_nonneg
    nlinarith
  · simp only [stepChain_X_self, stepChain_K_succ]
    rw [selectionDomain_eq_domain_def, hU]
    exact hF
  · intro x hx
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    rw [selectionDomain_eq_domain_def, hU2]
    exact hmaps x hx
  · intro x hx k
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    have e : x.1 + ((fun i => (k i : ℂ)), (0 : SelectionC n)) =
        (x.1.1 + (fun i => (k i : ℂ)), x.1.2) := by ext <;> simp
    rw [e]
    exact hper x hx k
  · intro z b hz
    simp only [stepChain_X_self, stepChain_K_succ] at hz ⊢
    rw [selectionDomain_eq_domain_def, hU] at hz
    have hre := csr.1 z b (by
      rw [← phaseToC_eq_realInclusion₂, ← selectionReal_eq_realInclusion]; exact hz)
    rw [phaseToC_eq_realInclusion₂, selectionReal_eq_realInclusion]
    refine ⟨((fun i => ((p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν) (ch.R ν)
      (KAM.realInclusion₂ n z, KAM.realInclusion n b)).1 i).re),
      (fun i => ((p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν) (ch.R ν)
      (KAM.realInclusion₂ n z, KAM.realInclusion n b)).2 i).re)), ?_⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact Complex.ext (by simp [phaseToC]) (by simpa [phaseToC] using (hre i).1)
    · exact Complex.ext (by simp [phaseToC]) (by simpa [phaseToC] using (hre i).2)
  · intro x hx u v
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    exact hsymp x hx u v
  · intro x hx
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    rw [hAe]
    exact (hdisp x hx).1
  · intro x hx
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    rw [hαe]
    exact (hdisp x hx).2
  · intro x hx
    simp only [stepChain_X_self, stepChain_K_succ] at hx ⊢
    rw [selectionDomain_eq_domain_def, hU] at hx
    rw [selectionMapBudget_eq_stage hf (ch := ch)]
    exact hder x hx
  · intro t' ht' htt z hz1 hz2 b hb j
    simp only [stepChain_X_self, stepChain_K_succ] at hb ⊢
    have hzd : z ∈ KAM.Weighted.Dom n {0} (selections a (ν + 1)) (selectionr a (ν + 1)) :=
      (mem_Dom_iff z).2 ⟨hz1, hz2⟩
    have hd := (step_slice_diff hF' hzd).sub_const z
    have hbd : ∀ b' ∈ actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1)),
        ‖(fun b'' => p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν) (ch.R ν)
          (z, b'') - z) b'‖ ≤ max (p11StepA (stageS d a ch ν hf))
          ((n + 1) * (stageS d a ch ν hf).s * p11StepA (stageS d a ch ν hf) /
            (stageS d a ch ν hf).sigma) := by
      intro b' hb'
      have h1 := hdisp (z, b') (by rw [← hU]; exact hmemU z b' hz1 hz2 hb')
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
      exact max_le_max h1.1 h1.2
    have := param_cauchy_gen (E := selectionRetained a d ch ν) (t := selectiont a (ν + 1))
      (tp := t') ht' htt hd hbd j b hb
    rw [hAe, hαe]
    exact this
  · intro b hb
    simp only [stepChain_K_succ] at hb
    obtain ⟨⟨Th, M, v, hv⟩, -⟩ := csi
    refine ⟨fun θ => Th (θ, b), fun θ => M (θ, b), fun θ => v (θ, b), ?_⟩
    intro z hz1 hz2
    have hzU : ((z, b) : P11Family n) ∈ domain_def n (selectionr a (ν + 1))
        (selections a (ν + 1)) (actionNbhd (selectionRetained a d ch ν)
          (selectiont a (ν + 1))) := hmemU z b hz1 hz2 hb
    rw [hU] at hzU
    rw [stepChain_X_self]
    exact (hv (z, b) hzU).1
  · intro b hb z hz z' hz' heq
    simp only [stepChain_K_succ] at hb
    obtain ⟨-, hinv⟩ := csi
    have hzU : ((z, b) : P11Family n) ∈ domain_def n (selectionr a (ν + 1))
        (selections a (ν + 1)) (actionNbhd (selectionRetained a d ch ν)
          (selectiont a (ν + 1))) := hmemU z b hz.1 hz.2 hb
    have hzU' : ((z', b) : P11Family n) ∈ domain_def n (selectionr a (ν + 1))
        (selections a (ν + 1)) (actionNbhd (selectionRetained a d ch ν)
          (selectiont a (ν + 1))) := hmemU z' b hz'.1 hz'.2 hb
    rw [hU] at hzU hzU'
    have h1 := (hinv (z, b) hzU).1
    have h2 := (hinv (z', b) hzU').1
    rw [stepChain_X_self] at heq
    dsimp only at heq h1 h2
    rw [← h1, ← h2, heq]
  · intro b hb θ
    simp only [stepChain_K_succ] at hb
    have hb' : KAM.realInclusion n b ∈ actionNbhd (stageS d a ch ν hf).E
        (stageS d a ch ν hf).t := by
      rw [← selectionReal_eq_realInclusion]; exact hb
    have key := step_real_lipschitz_collar H hb' θ hreal
    have hfun : (fun v : SelectionR n => selectionRe
        ((stepChain d a ch ν hf).X ν (selectionReal b) (selectionReal v, 0)).1) =
        fun x : SelectionR n => fun i => ((p11StepMap (stageS d a ch ν hf)
          (selectionFrequency d ch ν) (ch.R ν)
          ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re := by
      funext v
      simp only [stepChain_X_self, selectionReal_eq_realInclusion]
      rfl
    rw [hfun, selectionRealBudget_eq_stage hf (ch := ch)]
    exact key

end Post

end KAM.Planetary

end
