/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ConvSource
public import KAM.Wave.Iteration.StrongConj
public import KAM.Wave.Iteration.StepSmooth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the factors `Φ_{ν+1}` of the compositions on one carrier (blueprint `bpW:w6:convergence`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:convergence` (steps `c-dom`, `c-op`), from
`bpW:w6:iter-lemma` and `bpW:w5:step`.

The step of stage `ν` acts on `StepPhase r_ν` (the carrier `KamPhase` with the norm `|·|_{r_ν}`).
All these norms are equivalent to the product norm of `KamPhase`, so the compositions
`Φ^ν = Φ_1 ∘ ⋯ ∘ Φ_ν` are formed on `KamPhase` (product norm; derivatives do not depend on the
choice of an equivalent norm) and estimated with the norms `kamNorm r_μ`.

* `hasFDerivAt_stepK`, `hasFDerivAt_stepMix`: transfer of derivatives between `StepPhase r` and
  `KamPhase`;
* `w6Iota = ι : 𝒫^{p_+} → 𝒫` (`p = 1`, `p_+ = 3/2`, `kamHomEmbed`);
* `W6State.stepPsiN`: the smoothing displacement `Ψ_{ν+1}` of the step (`Φ_{ν+1} = id + ι Ψ_{ν+1}`);
* `w6PhiK`, `w6PsiK`: `Φ_{ν+1}`, `Ψ_{ν+1}` along the iteration started at `S₀`, on `KamPhase`;
* `w6StepK_smooth`, `w6StepK_clauses`: their properties at stage `ν` (W5's `stepTheorem` and
  `StepHypSrc.phi_smooth_of`, transported to `KamPhase`). Everything using `Ψ` or `DΦ` is
  conditional on the W5 dependency `W6StepSmooth` (argument `hS`).
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Wave

open KAM

/-- Transfer of a derivative from `StepPhase r` to `KamPhase`. -/
theorem hasFDerivAt_stepK {r : ℝ} [Fact (0 < r)] {f : StepPhase r → StepPhase r}
    {w : StepPhase r} (hf : DifferentiableAt ℂ f w) :
    HasFDerivAt (fun z : KamPhase => StepPhase.toK (f (StepPhase.ofK z)))
      ((stepToKCLM r).comp ((fderiv ℂ f w).comp (stepOfKCLM r))) (StepPhase.toK w) :=
  (stepToKCLM r).hasFDerivAt.comp (StepPhase.toK w)
    (hf.hasFDerivAt.comp (StepPhase.toK w) (stepOfKCLM r).hasFDerivAt)

/-- Transfer of a derivative from `KamPhase` to `StepPhase r → StepPhase r'`. -/
theorem hasFDerivAt_stepMix {r r' : ℝ} [Fact (0 < r)] [Fact (0 < r')] {f : KamPhase → KamPhase}
    {L : KamPhase →L[ℂ] KamPhase} {z : KamPhase} (hf : HasFDerivAt f L z) :
    HasFDerivAt (fun W : StepPhase r => (StepPhase.ofK (f (StepPhase.toK W)) : StepPhase r'))
      ((stepOfKCLM r').comp (L.comp (stepToKCLM r))) (StepPhase.ofK z) :=
  (stepOfKCLM r').hasFDerivAt.comp (StepPhase.ofK z)
    (hf.comp (StepPhase.ofK z) (stepToKCLM r).hasFDerivAt)

theorem w6_one_le_three_halves : (1 : ℝ) ≤ 3 / 2 := by norm_num

/-- `ι : 𝒫^{p_+} → 𝒫` for `a = p = 1`, `p_+ = 3/2` (in the representatives). -/
def w6Iota : KamPhase →L[ℂ] KamPhase := kamHomEmbed 1 1 (3 / 2) w6_one_le_three_halves

theorem kamNorm_w6Iota_le {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    kamNorm r (w6Iota W) ≤ kamNorm r W :=
  kamNorm_kamHomEmbed_le 1 1 (3 / 2) _ hr W

theorem w6Iota_injective : Function.Injective w6Iota := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact stepEmbedCLM_injective (a := 1) w6_one_le_three_halves 1

/-- `|W|_{r} ≤ |W|_{r'}` for `0 < r' ≤ r` (radii of the iteration decrease). -/
theorem kamNorm_anti {r r' : ℝ} (hr' : 0 < r') (hr : r' ≤ r) (W : KamPhase) :
    kamNorm r W ≤ kamNorm r' W := kamNorm_le_of_le_radius hr' hr W

namespace W6SeqData

variable {d : W6SeqData}

theorem rNu_succ_le (hd : W6State.Std d) (ν : ℕ) : d.rNu (ν + 1) ≤ d.rNu ν := by
  rw [rNu_succ]
  have := eta_le hd.1 hd.2 ν
  have := w6r_pos hd.1 ν
  nlinarith

theorem rNu_anti (hd : W6State.Std d) : Antitone d.rNu :=
  antitone_nat_of_succ_le (rNu_succ_le hd)

theorem rNu_le_r0 (hd : W6State.Std d) (ν : ℕ) : d.rNu ν ≤ d.rNu 0 :=
  rNu_anti hd (Nat.zero_le ν)

/-- `D_{ν+1} ⊆ D_ν`. -/
theorem domNu_succ_subset (hd : W6State.Std d) (ν : ℕ) : d.domNu (ν + 1) ⊆ d.domNu ν :=
  kamDomain_mono (by
      rw [show d.s (ν + 1) = d.s ν - 5 * d.sigma ν from rfl]
      linarith [sigmaNu_pos hd.1 ν]) (w6r_pos hd.1 (ν + 1)) (rNu_succ_le hd ν)

theorem domNu_anti (hd : W6State.Std d) : Antitone d.domNu :=
  antitone_nat_of_succ_le (domNu_succ_subset hd)

end W6SeqData

namespace W6State

variable {d : W6SeqData}

/-- `Ψ_{ν+1}`: the smoothing displacement of `Φ_{ν+1}` (`0` if the hypotheses of stage `ν` fail).
-/
def stepPsiN (d : W6SeqData) (ν : ℕ) (S : W6State) (ξ : Fin 2 → ℝ) :
    StepPhase (d.rNu ν) → StepPhase (d.rNu ν) :=
  open Classical in
  if h : Std d ∧ S.w6Stage d ν then
    haveI := W6Stage.factRPos h.1.1 ν
    (W6Stage.stageStepHyp h.1.1 h.1.2 h.2).w6Psi ξ
  else fun _ => 0

theorem stepPsiN_eq {S : W6State} {ν : ℕ} (hd : Std d) (h : S.w6Stage d ν) :
    S.stepPsiN d ν = fun ξ =>
      haveI := W6Stage.factRPos hd.1 ν
      (W6Stage.stageStepHyp hd.1 hd.2 h).w6Psi ξ := by
  funext ξ
  unfold stepPsiN
  rw [dite_eq_left ⟨hd, h⟩]

end W6State

/-- `Φ_{ν+1}` along the iteration started at `S₀`, on `KamPhase`. -/
def w6PhiK (d : W6SeqData) (S0 : W6State) (ν : ℕ) (ξ : Fin 2 → ℝ) (w : KamPhase) : KamPhase :=
  StepPhase.toK ((w6Seq d S0 ν).phi d ν ξ (StepPhase.ofK w))

/-- `Ψ_{ν+1}` along the iteration started at `S₀`, on `KamPhase` (`p_+`-representatives). -/
def w6PsiK (d : W6SeqData) (S0 : W6State) (ν : ℕ) (ξ : Fin 2 → ℝ) (w : KamPhase) : KamPhase :=
  StepPhase.toK ((w6Seq d S0 ν).stepPsiN d ν ξ (StepPhase.ofK w))

/-- The open set `D_{ν+1} = D(s_ν - 5σ_ν, η_ν r_ν)` on which `Φ_{ν+1}` is holomorphic. -/
def w6Ubig (d : W6SeqData) (ν : ℕ) : Set KamPhase :=
  kamDomain (d.s ν - 5 * d.sigma ν) (d.etaNu ν * d.rNu ν)

section step

variable {d : W6SeqData} {S0 : W6State} {ν : ℕ} {ξ : Fin 2 → ℝ}

/-- `8 M_{F,ν}/σ_ν ≤ 2^{-ν-3}`. -/
theorem w6_eight_MF_le (hd : W6State.Std d) (ν : ℕ) :
    8 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ≤ 1 / 2 ^ (ν + 3) := by
  have h := W6SeqData.transf_arith hd.1 hd.2 ν
  have e : 8 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν =
      (16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν) / 2 := by ring
  have e2 : (1 : ℝ) / 2 ^ (ν + 3) = 1 / 2 ^ (ν + 2) / 2 := by rw [pow_succ]; ring
  rw [e, e2]
  linarith

theorem w6PhiK_eq (hd : W6State.Std d) (hs : (w6Seq d S0 ν).w6Stage d ν) :
    w6PhiK d S0 ν ξ = fun w =>
      haveI := W6Stage.factRPos hd.1 ν
      StepPhase.toK ((W6Stage.stageStepHyp hd.1 hd.2 hs).hyp.core.Phi ξ (StepPhase.ofK w)) := by
  unfold w6PhiK
  rw [W6State.phi_eq hd.1 hd.2 hs]
  rfl

theorem w6PsiK_eq (hd : W6State.Std d) (hs : (w6Seq d S0 ν).w6Stage d ν) :
    w6PsiK d S0 ν ξ = fun w =>
      haveI := W6Stage.factRPos hd.1 ν
      StepPhase.toK ((W6Stage.stageStepHyp hd.1 hd.2 hs).w6Psi ξ (StepPhase.ofK w)) := by
  unfold w6PsiK
  rw [W6State.stepPsiN_eq hd hs]

/-- **The factor `Φ_{ν+1}` on `KamPhase`** (steps `il-tr`, `c-dom`): for `ξ ∈ Π_ν`, `Φ_{ν+1}` and
`Ψ_{ν+1}` are holomorphic on the open `D_{ν+1}`, and on `D_{ν+1}` (conditional on the W5
dependency `W6StepSmooth`):
`Φ_{ν+1}(w) ∈ D(s_ν - 4σ_ν, 2η_ν r_ν) ⊆ D_ν`, `Φ_{ν+1}(w) = w + ι Ψ_{ν+1}(w)`,
`|Ψ_{ν+1}(w)|_{r_ν} ≤ M_{F,ν}`, `DΦ_{ν+1}(w) = I + ι ∘ DΨ_{ν+1}(w)` and
`|DΨ_{ν+1}(w) W|_{r_ν} ≤ 2^{-ν-3} |W|_{r_ν}`. -/
theorem w6StepK_smooth (hS : W6StepSmooth) (hd : W6State.Std d) (hs : (w6Seq d S0 ν).w6Stage d ν)
    (hξ : ξ ∈ (w6Seq d S0 ν).Pi) :
    d.domNu (ν + 1) ⊆ w6Ubig d ν ∧
    (∀ w ∈ w6Ubig d ν, DifferentiableAt ℂ (w6PhiK d S0 ν ξ) w) ∧
    (∀ w ∈ w6Ubig d ν, DifferentiableAt ℂ (w6PsiK d S0 ν ξ) w) ∧
    ∀ w ∈ d.domNu (ν + 1),
      w6PhiK d S0 ν ξ w ∈ kamDomain (d.s ν - 4 * d.sigma ν) (2 * d.etaNu ν * d.rNu ν) ∧
      w6PhiK d S0 ν ξ w ∈ d.domNu ν ∧
      w6PhiK d S0 ν ξ w = w + w6Iota (w6PsiK d S0 ν ξ w) ∧
      kamNorm (d.rNu ν) (w6PsiK d S0 ν ξ w) ≤
        stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) ∧
      fderiv ℂ (w6PhiK d S0 ν ξ) w =
        ContinuousLinearMap.id ℂ _ + w6Iota.comp (fderiv ℂ (w6PsiK d S0 ν ξ) w) ∧
      ∀ W, kamNorm (d.rNu ν) (fderiv ℂ (w6PsiK d S0 ν ξ) w W) ≤
        1 / 2 ^ (ν + 3) * kamNorm (d.rNu ν) W := by
  have := W6Stage.factRPos hd.1 ν
  set H := W6Stage.stageStepHyp hd.1 hd.2 hs
  obtain ⟨hdΦ, hdΨ, hall⟩ := H.phi_smooth_of hS hξ
  have hsub : stepDomain (d.rNu ν) (d.s ν - 5 * d.sigma ν) (d.etaNu ν * d.rNu ν) ⊆
      stepDomain (d.rNu ν) (d.s ν - 5 * d.sigma ν) (d.etaNu ν * d.rNu ν) := subset_rfl
  have hU : IsOpen (w6Ubig d ν) := kamDomain_isOpen _ _
  have hΦ : ∀ w ∈ w6Ubig d ν, HasFDerivAt (w6PhiK d S0 ν ξ)
      ((stepToKCLM _).comp ((fderiv ℂ (H.hyp.core.Phi ξ) (StepPhase.ofK w)).comp
        (stepOfKCLM _))) w := by
    intro w hw
    rw [w6PhiK_eq hd hs]
    exact hasFDerivAt_stepK ((hdΦ _ hw).differentiableAt
      ((stepDomain_isOpen _ _ _).mem_nhds hw))
  have hΨ : ∀ w ∈ w6Ubig d ν, HasFDerivAt (w6PsiK d S0 ν ξ)
      ((stepToKCLM _).comp ((fderiv ℂ (H.w6Psi ξ) (StepPhase.ofK w)).comp
        (stepOfKCLM _))) w := by
    intro w hw
    rw [w6PsiK_eq hd hs]
    exact hasFDerivAt_stepK ((hdΨ _ hw).differentiableAt
      ((stepDomain_isOpen _ _ _).mem_nhds hw))
  have hmaps := W6Stage.phiN_mapsTo hd.1 hd.2 hs
  refine ⟨fun w hw => hsub hw, fun w hw => (hΦ w hw).differentiableAt,
    fun w hw => (hΨ w hw).differentiableAt, fun w hw => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hall (StepPhase.ofK w) hw
  have hm := hmaps ξ hξ (StepPhase.ofK w) hw
  have hwU : w ∈ w6Ubig d ν := hsub hw
  refine ⟨?_, ?_, ?_, ?_, ?_, fun W => ?_⟩
  · rw [w6PhiK_eq hd hs]; exact hm.1
  · rw [w6PhiK_eq hd hs]; exact hm.2
  · rw [w6PhiK_eq hd hs, w6PsiK_eq hd hs]
    simp only
    rw [e1]
    rfl
  · rw [w6PsiK_eq hd hs]; exact e2
  · rw [(hΦ w hwU).fderiv, (hΨ w hwU).fderiv, e3]
    rfl
  · rw [(hΨ w hwU).fderiv]
    have h8 := w6_eight_MF_le hd ν
    have hle : ‖fderiv ℂ (H.w6Psi ξ) (StepPhase.ofK w)‖ ≤ 1 / 2 ^ (ν + 3) :=
      e4.trans h8
    have := (fderiv ℂ (H.w6Psi ξ) (StepPhase.ofK w)).le_opNorm (StepPhase.ofK W)
    calc kamNorm (d.rNu ν) _ = ‖fderiv ℂ (H.w6Psi ξ) (StepPhase.ofK w)
          (StepPhase.ofK W)‖ := rfl
      _ ≤ ‖fderiv ℂ (H.w6Psi ξ) (StepPhase.ofK w)‖ * ‖(StepPhase.ofK W :
          StepPhase (d.rNu ν))‖ := this
      _ ≤ 1 / 2 ^ (ν + 3) * kamNorm (d.rNu ν) W :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- The derivative of `Φ_{ν+1}` on `KamPhase` is W5's `DΦ` transported. -/
theorem w6PhiK_fderiv_apply (hS : W6StepSmooth) (hd : W6State.Std d)
    (hs : (w6Seq d S0 ν).w6Stage d ν)
    (hξ : ξ ∈ (w6Seq d S0 ν).Pi) {w : KamPhase} (hw : w ∈ w6Ubig d ν) (W : KamPhase) :
    fderiv ℂ (w6PhiK d S0 ν ξ) w W =
      haveI := W6Stage.factRPos hd.1 ν
      StepPhase.toK (fderiv ℂ ((W6Stage.stageStepHyp hd.1 hd.2 hs).hyp.core.Phi ξ)
        (StepPhase.ofK w) (StepPhase.ofK W)) := by
  have := W6Stage.factRPos hd.1 ν
  set H := W6Stage.stageStepHyp hd.1 hd.2 hs
  obtain ⟨hdΦ, -, -⟩ := H.phi_smooth_of hS hξ
  have h : HasFDerivAt (w6PhiK d S0 ν ξ)
      ((stepToKCLM _).comp ((fderiv ℂ (H.hyp.core.Phi ξ) (StepPhase.ofK w)).comp
        (stepOfKCLM _))) w := by
    rw [w6PhiK_eq hd hs]
    exact hasFDerivAt_stepK ((hdΦ _ hw).differentiableAt
      ((stepDomain_isOpen _ _ _).mem_nhds hw))
  rw [h.fderiv]
  rfl

theorem w6_two_nonneg : (0 : ℝ) ≤ 1 + 1 := by norm_num

theorem w6_pred_nonneg : (0 : ℝ) ≤ (1 - 1) + 3 / 2 := by norm_num

theorem w6_pred_le : (1 : ℝ) - 1 ≤ 3 / 2 := by norm_num

/-- The pairing `ϖ_{p,p}` of `𝒫` (`a = p = 1`). -/
def w6Symp (W W' : KamPhase) : ℂ :=
  stepSymp (a := 1) (q := 1) (q' := 1) zero_le_one w6_two_nonneg W W'

/-- The pairing `ϖ_{p-1,p_+}` of `𝒫^{p-1}` with `𝒫^{p_+}` (`a = p = 1`, `p_+ = 3/2`). -/
def w6SympPred (W W' : KamPhase) : ℂ :=
  stepSymp (a := 1) (q := 1 - 1) (q' := 3 / 2) zero_le_one w6_pred_nonneg W W'

/-- A Hamiltonian field `X_H = X_N + ι_{p_+ → p-1} X_P` in the `(p-1)`-representatives, for
`N` with frequencies `(ω, Ω)` and `P` with field `X` (`a = p = 1`, `p_+ = 3/2`). -/
def w6Field {K0 : ℝ} {Ω : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (ω : Fin 2 → ℝ) (X : KamPhase → KamPhase) (w : KamPhase) : KamPhase :=
  stepXN (a := 1) (p := 1) hΩ ω w + kamHomEmbed 1 (1 - 1) (3 / 2) w6_pred_le (X w)

theorem w6Field_irrel {K0 K1 : ℝ} {Ω : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (hΩ' : ∀ j : ℕ+, |Ω j| ≤ K1 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ) (X : KamPhase → KamPhase)
    (w : KamPhase) : w6Field hΩ ω X w = w6Field hΩ' ω X w := rfl

/-- **The clauses of `Φ_{ν+1}` on `KamPhase`** (`bpW:w5:step` (i)): on `D_{ν+1}`, for `ξ ∈ Π_ν`:
real on real points, `Φ(w + τ_i) = Φ(w) + τ_i`, `DΦ(w)` symplectic, `DΦ(w)` maps `𝒫^{p_+}` into
and onto `𝒫^{p_+}`, and `Φ_{ν+1}(·, ξ)` is Lipschitz in `ξ ∈ Π_ν` uniformly in `w`. -/
theorem w6StepK_clauses (hS : W6StepSmooth) (hd : W6State.Std d) (hs : (w6Seq d S0 ν).w6Stage d ν)
    (hξ : ξ ∈ (w6Seq d S0 ν).Pi) :
    (∃ A : ℝ, 0 ≤ A ∧ ∀ ζ ∈ (w6Seq d S0 ν).Pi, ∀ w ∈ d.domNu (ν + 1),
      kamNorm (d.rNu ν) (w6PhiK d S0 ν ξ w - w6PhiK d S0 ν ζ w) ≤ A * ‖ξ - ζ‖) ∧
    ∀ w ∈ d.domNu (ν + 1),
      (StepReal w → StepReal (w6PhiK d S0 ν ξ w)) ∧
      (∀ i : Fin 2, w6PhiK d S0 ν ξ (w + stepTau i) = w6PhiK d S0 ν ξ w + stepTau i) ∧
      (∀ W W', w6Symp (fderiv ℂ (w6PhiK d S0 ν ξ) w W) (fderiv ℂ (w6PhiK d S0 ν ξ) w W') =
        w6Symp W W') ∧
      (∀ W', ∃ W'', fderiv ℂ (w6PhiK d S0 ν ξ) w (w6Iota W') = w6Iota W'') ∧
      (∀ W'', ∃ W', fderiv ℂ (w6PhiK d S0 ν ξ) w (w6Iota W') = w6Iota W'') := by
  have := W6Stage.factRPos hd.1 ν
  set H := W6Stage.stageStepHyp hd.1 hd.2 hs
  obtain ⟨-, -, -, c4, c5, c6, c7, -, -, -, -, -, -, -, -, -, c17⟩ := stepTheorem_clauses H
  have hsub : d.domNu (ν + 1) ⊆ w6Ubig d ν := fun _ hw => hw
  obtain ⟨A₀, A₁, B₀, B₁, -, a1, -, -, -, -, hb⟩ := c17
  refine ⟨⟨A₁, a1, fun ζ hζ w hw => ?_⟩, fun w hw => ⟨fun hr => ?_, fun i => ?_, fun W W' => ?_,
    fun W' => ?_, fun W'' => ?_⟩⟩
  · have h := (hb ξ hξ ζ hζ (StepPhase.ofK w) hw).2.1
    rw [w6PhiK_eq hd hs, w6PhiK_eq hd hs]
    have e : H.hyp.core.Phi ξ (StepPhase.ofK w) - StepPhase.ofK w -
        (H.hyp.core.Phi ζ (StepPhase.ofK w) - StepPhase.ofK w) =
        H.hyp.core.Phi ξ (StepPhase.ofK w) - H.hyp.core.Phi ζ (StepPhase.ofK w) := by abel
    rw [e] at h
    exact h
  · rw [w6PhiK_eq hd hs]; exact c6 ξ hξ (StepPhase.ofK w) hw hr
  · rw [w6PhiK_eq hd hs]; exact c5 ξ hξ (StepPhase.ofK w) hw i
  · rw [w6PhiK_fderiv_apply hS hd hs hξ (hsub hw), w6PhiK_fderiv_apply hS hd hs hξ (hsub hw)]
    exact c4 ξ hξ (StepPhase.ofK w) hw (StepPhase.ofK W) (StepPhase.ofK W')
  · obtain ⟨W'', h⟩ := (c7 ξ hξ (StepPhase.ofK w) hw).1 (StepPhase.ofK W')
    refine ⟨StepPhase.toK W'', ?_⟩
    rw [w6PhiK_fderiv_apply hS hd hs hξ (hsub hw)]
    exact congrArg StepPhase.toK h
  · obtain ⟨W', h⟩ := (c7 ξ hξ (StepPhase.ofK w) hw).2 (StepPhase.ofK W'')
    refine ⟨StepPhase.toK W', ?_⟩
    rw [w6PhiK_fderiv_apply hS hd hs hξ (hsub hw)]
    exact congrArg StepPhase.toK h

/-- **Weak conjugacy of `Φ_{ν+1}` in field form** (`bpW:w5:new-ham` (iii), `bpW:w5:step` (i)) on
`KamPhase`: on `D_{ν+1}`, for `ξ ∈ Π_ν`, if `DΦ_{ν+1}(w)(ι W') = ι W''` then
`ϖ_{p-1,p_+}(X_{H_ν}(Φ_{ν+1} w), W'') = ϖ_{p-1,p_+}(X_{H_{ν+1}}(w), W')`, with
`X_{H_μ} = X_{N_μ} + ι X_{P_μ}` (`w6Field`, any bounds for the normal frequencies). -/
theorem w6StepK_weakConj (hS : W6StepSmooth) (hd : W6State.Std d) (hs : (w6Seq d S0 ν).w6Stage d ν)
    (hξ : ξ ∈ (w6Seq d S0 ν).Pi) {K0 K1 : ℝ}
    (hΩ0 : ∀ j : ℕ+, |(w6Seq d S0 ν).Om ξ j| ≤ K0 * ((j : ℝ) + 2))
    (hΩ1 : ∀ j : ℕ+, |(w6Seq d S0 (ν + 1)).Om ξ j| ≤ K1 * ((j : ℝ) + 2))
    {w : KamPhase} (hw : w ∈ d.domNu (ν + 1)) (W' W'' : KamPhase)
    (hW : fderiv ℂ (w6PhiK d S0 ν ξ) w (w6Iota W') = w6Iota W'') :
    w6SympPred (w6Field hΩ0 ((w6Seq d S0 ν).om ξ) ((w6Seq d S0 ν).X ξ) (w6PhiK d S0 ν ξ w)) W'' =
      w6SympPred (w6Field hΩ1 ((w6Seq d S0 (ν + 1)).om ξ) ((w6Seq d S0 (ν + 1)).X ξ) w) W' := by
  have := W6Stage.factRPos hd.1 ν
  set H := W6Stage.stageStepHyp hd.1 hd.2 hs
  obtain ⟨-, -, -, -, -, -, -, c8, -⟩ := stepTheorem_clauses H
  have hsub : d.domNu (ν + 1) ⊆ w6Ubig d ν := fun _ hw => hw
  have e1 : w6Seq d S0 (ν + 1) = _ :=
    (w6Seq_succ d S0 ν).trans (W6State.w6next_eq hd.1 hd.2 hs)
  rw [w6PhiK_fderiv_apply hS hd hs hξ (hsub hw)] at hW
  have h := c8 ξ hξ (StepPhase.ofK w) hw (StepPhase.ofK W') (StepPhase.ofK W'') hW
  have hO : (w6Seq d S0 (ν + 1)).om = W6Stage.omN hd.1 hd.2 hs := by rw [e1]
  have hX : (w6Seq d S0 (ν + 1)).X = W6Stage.XN hd.1 hd.2 hs := by rw [e1]
  have hOm : (w6Seq d S0 (ν + 1)).Om = W6Stage.OmN hd.1 hd.2 hs := by rw [e1]
  revert hΩ1
  rw [hO, hX, hOm]
  intro hΩ1
  rw [w6PhiK_eq hd hs]
  exact h

end step

end KAM.Wave
