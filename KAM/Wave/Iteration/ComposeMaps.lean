/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ComposeStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the compositions `Φ^ν = Φ_1 ∘ ⋯ ∘ Φ_ν` (blueprint `bpW:w6:convergence` (iv))

Blueprint label `bpW:w6:convergence` (steps `c-dom`, `c-op`; clause (iv)).

Along the iteration started at `S₀` (with the hypotheses of every stage), for `ξ ∈ Π_{ν-1}`:

* `w6PhiC ν ξ = Φ^ν` (`Φ^0 = id`, `Φ^{ν+1} = Φ^ν ∘ Φ_{ν+1}`) and its smoothing displacement
  `w6PsiC ν ξ = Ψ^ν` (`Ψ^{ν+1} = Ψ_{ν+1} + Ψ^ν ∘ Φ_{ν+1}`), with `Φ^ν = id + ι ∘ Ψ^ν` on `D_ν`;
* `w6Compose_main`: `Φ^ν(D_ν) ⊆ D_0`, `Φ^ν`, `Ψ^ν` holomorphic on `D_ν`,
  `DΦ^ν = I + ι ∘ DΨ^ν`, `|DΨ^ν(w) W|_{r_0} ≤ (c_ν - 1)|W|_{r_ν}`,
  `c_ν = ∏_{μ<ν}(1 + 2^{-μ-2}) ≤ 2`;
* `w6Compose_ops` (`bpW:w6:convergence` (iv)): `|DΦ^ν(w) W|_{q,r_0} ≤ 2|W|_{q,r_ν}` for
  `q ∈ {p, p_+}`, `DΦ^ν(w)` symplectic and maps `𝒫^{p_+}` onto `𝒫^{p_+}`;
* `w6Compose_real_periodic`: `Φ^ν` is real on real points and `Φ^ν(w + τ_i) = Φ^ν(w) + τ_i`;
* `w6Compose_weak`: the composed weak conjugacy `ϖ(X_{H_0}(Φ^ν w), W'') = ϖ(X_{H_ν}(w), W')`
  whenever `DΦ^ν(w)(ι W') = ι W''` (step `i-weak` of `bpW:w6:invariance`).
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Wave

open KAM

/-- `Φ^ν = Φ_1 ∘ ⋯ ∘ Φ_ν` (`Φ^0 = id`, `Φ^{ν+1} = Φ^ν ∘ Φ_{ν+1}`) on `KamPhase`. -/
def w6PhiC (d : W6SeqData) (S0 : W6State) : ℕ → (Fin 2 → ℝ) → KamPhase → KamPhase
  | 0, _ => id
  | ν + 1, ξ => fun w => w6PhiC d S0 ν ξ (w6PhiK d S0 ν ξ w)

/-- The smoothing displacement `Ψ^ν` of `Φ^ν` (`Ψ^0 = 0`, `Ψ^{ν+1} = Ψ_{ν+1} + Ψ^ν ∘ Φ_{ν+1}`). -/
def w6PsiC (d : W6SeqData) (S0 : W6State) : ℕ → (Fin 2 → ℝ) → KamPhase → KamPhase
  | 0, _ => fun _ => 0
  | ν + 1, ξ => fun w => w6PsiK d S0 ν ξ w + w6PsiC d S0 ν ξ (w6PhiK d S0 ν ξ w)

/-- `c_ν = ∏_{μ<ν} (1 + 2^{-μ-2})`. -/
def w6Cp (ν : ℕ) : ℝ := ∏ μ ∈ Finset.range ν, (1 + 1 / (2 : ℝ) ^ (μ + 2))

theorem w6Cp_le_two (ν : ℕ) : w6Cp ν ≤ 2 := w6prod_le_two ν

theorem one_le_w6Cp (ν : ℕ) : 1 ≤ w6Cp ν := by
  induction ν with
  | zero => simp [w6Cp]
  | succ ν ih =>
    unfold w6Cp at *
    rw [Finset.prod_range_succ]
    have : (0 : ℝ) ≤ 1 / 2 ^ (ν + 2) := by positivity
    exact one_le_mul_of_one_le_of_one_le ih (by linarith)

theorem w6Cp_succ (ν : ℕ) : w6Cp (ν + 1) = w6Cp ν * (1 + 1 / (2 : ℝ) ^ (ν + 2)) := by
  unfold w6Cp; rw [Finset.prod_range_succ]

section compose

variable {d : W6SeqData} {S0 : W6State}

/-- The standing hypotheses on the iteration: `Std d`, the hypotheses of every stage, and the W5
dependency `W6StepSmooth` (the `p_+` smoothing of each step's transformation, being added to W5 on
`inp-w5aa`); every theorem taking `W6IterHyp` is conditional on that dependency. -/
structure W6IterHyp (d : W6SeqData) (S0 : W6State) : Prop where
  std : W6State.Std d
  stage : ∀ ν, (w6Seq d S0 ν).w6Stage d ν
  smooth : W6StepSmooth

theorem kamNorm_add_le' {r : ℝ} (hr : 0 < r) (W W' : KamPhase) :
    kamNorm r (W + W') ≤ kamNorm r W + kamNorm r W' := kamNorm_add_le hr W W'

/-- **Main invariant of the compositions** (steps `c-dom`, `c-op`): for `ξ ∈ Π_μ` (`μ < ν`) and
`w ∈ D_ν`: `Φ^ν(w) = w + ι Ψ^ν(w)`, `Φ^ν(w) ∈ D_0`, `Φ^ν`, `Ψ^ν` are differentiable at `w`,
`DΦ^ν(w) = I + ι ∘ DΨ^ν(w)` and `|DΨ^ν(w) W|_{r_0} ≤ (c_ν - 1) |W|_{r_ν}`. -/
theorem w6Compose_main (hI : W6IterHyp d S0) (ν : ℕ) :
    ∀ ξ, (∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) → ∀ w ∈ d.domNu ν,
      w6PhiC d S0 ν ξ w = w + w6Iota (w6PsiC d S0 ν ξ w) ∧
      w6PhiC d S0 ν ξ w ∈ d.domNu 0 ∧
      DifferentiableAt ℂ (w6PhiC d S0 ν ξ) w ∧
      DifferentiableAt ℂ (w6PsiC d S0 ν ξ) w ∧
      fderiv ℂ (w6PhiC d S0 ν ξ) w =
        ContinuousLinearMap.id ℂ _ + w6Iota.comp (fderiv ℂ (w6PsiC d S0 ν ξ) w) ∧
      ∀ W, kamNorm (d.rNu 0) (fderiv ℂ (w6PsiC d S0 ν ξ) w W) ≤
        (w6Cp ν - 1) * kamNorm (d.rNu ν) W := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  induction ν with
  | zero =>
    intro ξ _ w hw
    have e1 : w6PhiC d S0 0 ξ = id := rfl
    have e2 : w6PsiC d S0 0 ξ = fun _ => 0 := rfl
    rw [e1, e2]
    refine ⟨by simp, hw, differentiableAt_id, differentiableAt_const _, ?_, fun W => ?_⟩
    · rw [fderiv_id, fderiv_const_apply, ContinuousLinearMap.comp_zero, add_zero]
    · rw [fderiv_const_apply]
      simp [w6Cp, kamNorm]
  | succ ν ih =>
    intro ξ hξ w hw
    have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
    obtain ⟨hsubU, hdK, hdP, hall⟩ := w6StepK_smooth hI.smooth hd (hI.stage ν) hξν
    obtain ⟨-, hz, eK, hPsiK, eDK, hDK⟩ := hall w hw
    set z := w6PhiK d S0 ν ξ w with hzdef
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) z hz
    have hwU := hsubU hw
    have eΦ : w6PhiC d S0 (ν + 1) ξ = fun w => w6PhiC d S0 ν ξ (w6PhiK d S0 ν ξ w) := rfl
    have eΨ : w6PsiC d S0 (ν + 1) ξ =
        fun w => w6PsiK d S0 ν ξ w + w6PsiC d S0 ν ξ (w6PhiK d S0 ν ξ w) := rfl
    have hΦd : HasFDerivAt (w6PhiC d S0 (ν + 1) ξ)
        ((fderiv ℂ (w6PhiC d S0 ν ξ) z).comp (fderiv ℂ (w6PhiK d S0 ν ξ) w)) w := by
      rw [eΦ]
      exact a3.hasFDerivAt.comp w (hdK w hwU).hasFDerivAt
    have hΨd : HasFDerivAt (w6PsiC d S0 (ν + 1) ξ)
        (fderiv ℂ (w6PsiK d S0 ν ξ) w +
          (fderiv ℂ (w6PsiC d S0 ν ξ) z).comp (fderiv ℂ (w6PhiK d S0 ν ξ) w)) w := by
      rw [eΨ]
      exact (hdP w hwU).hasFDerivAt.add (a4.hasFDerivAt.comp w (hdK w hwU).hasFDerivAt)
    refine ⟨?_, a2, hΦd.differentiableAt, hΨd.differentiableAt, ?_, fun W => ?_⟩
    · rw [eΦ, eΨ]
      show w6PhiC d S0 ν ξ z = w + w6Iota (w6PsiK d S0 ν ξ w + w6PsiC d S0 ν ξ z)
      rw [a1, map_add, ← add_assoc, ← eK]
    · rw [hΦd.fderiv, hΨd.fderiv, a5, eDK]
      refine ContinuousLinearMap.ext fun W => ?_
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.id_apply, map_add]
      abel
    · rw [hΨd.fderiv]
      simp only [add_apply, ContinuousLinearMap.comp_apply]
      rw [eDK]
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply]
      have hrν := W6SeqData.w6r_pos hd.1 ν
      have hrν1 := W6SeqData.w6r_pos hd.1 (ν + 1)
      have h0ν := W6SeqData.rNu_le_r0 hd ν
      have hνν := W6SeqData.rNu_succ_le hd ν
      set V := fderiv ℂ (w6PsiK d S0 ν ξ) w W
      have hV : kamNorm (d.rNu ν) V ≤ 1 / 2 ^ (ν + 3) * kamNorm (d.rNu ν) W := hDK W
      have hWW : kamNorm (d.rNu ν) W ≤ kamNorm (d.rNu (ν + 1)) W := kamNorm_anti hrν1 hνν W
      have hV0 : kamNorm (d.rNu 0) V ≤ kamNorm (d.rNu ν) V := kamNorm_anti hrν h0ν V
      have hι : kamNorm (d.rNu ν) (w6Iota V) ≤ kamNorm (d.rNu ν) V := kamNorm_w6Iota_le hrν V
      have h6 := a6 (W + w6Iota V)
      have hsum := kamNorm_add_le hrν W (w6Iota V)
      have hsum0 := kamNorm_add_le hr0 V
        (fderiv ℂ (w6PsiC d S0 ν ξ) z (W + w6Iota V))
      have hc1 := one_le_w6Cp ν
      have hW0 : 0 ≤ kamNorm (d.rNu ν) W := kamNorm_nonneg hrν.le W
      have hp3 : (1 : ℝ) / 2 ^ (ν + 3) ≤ 1 / 2 ^ (ν + 2) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      have hp0 : (0 : ℝ) ≤ 1 / 2 ^ (ν + 3) := by positivity
      rw [w6Cp_succ]
      -- `|V'|_{r_0} ≤ (c_ν - 1)(1 + 2^{-ν-3}) |W|_{r_ν}` and `|V|_{r_0} ≤ 2^{-ν-3} |W|_{r_ν}`
      have hA : kamNorm (d.rNu ν) (W + w6Iota V) ≤ (1 + 1 / 2 ^ (ν + 3)) * kamNorm (d.rNu ν) W := by
        nlinarith
      have hB : kamNorm (d.rNu 0) (fderiv ℂ (w6PsiC d S0 ν ξ) z (W + w6Iota V)) ≤
          (w6Cp ν - 1) * ((1 + 1 / 2 ^ (ν + 3)) * kamNorm (d.rNu ν) W) :=
        h6.trans (mul_le_mul_of_nonneg_left hA (by linarith))
      have hC : kamNorm (d.rNu 0) V + kamNorm (d.rNu 0)
          (fderiv ℂ (w6PsiC d S0 ν ξ) z (W + w6Iota V)) ≤
          (w6Cp ν * (1 + 1 / 2 ^ (ν + 2)) - 1) * kamNorm (d.rNu ν) W := by
        have : 1 / 2 ^ (ν + 3) * kamNorm (d.rNu ν) W +
            (w6Cp ν - 1) * ((1 + 1 / 2 ^ (ν + 3)) * kamNorm (d.rNu ν) W) ≤
            (w6Cp ν * (1 + 1 / 2 ^ (ν + 2)) - 1) * kamNorm (d.rNu ν) W := by
          have : 1 / 2 ^ (ν + 3) + (w6Cp ν - 1) * (1 + 1 / 2 ^ (ν + 3)) ≤
              w6Cp ν * (1 + 1 / 2 ^ (ν + 2)) - 1 := by nlinarith
          nlinarith
        linarith
      have hK : 0 ≤ w6Cp ν * (1 + 1 / 2 ^ (ν + 2)) - 1 := by nlinarith
      calc _ ≤ _ := hsum0
        _ ≤ _ := hC
        _ ≤ _ := mul_le_mul_of_nonneg_left hWW hK

/-- The chain rule for `Φ^{ν+1} = Φ^ν ∘ Φ_{ν+1}` on `D_{ν+1}`. -/
theorem w6PhiC_succ_fderiv (hI : W6IterHyp d S0) {ν : ℕ} {ξ : Fin 2 → ℝ}
    (hξ : ∀ μ < ν + 1, ξ ∈ (w6Seq d S0 μ).Pi) {w : KamPhase} (hw : w ∈ d.domNu (ν + 1)) :
    fderiv ℂ (w6PhiC d S0 (ν + 1) ξ) w =
      (fderiv ℂ (w6PhiC d S0 ν ξ) (w6PhiK d S0 ν ξ w)).comp (fderiv ℂ (w6PhiK d S0 ν ξ) w) := by
  have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
  obtain ⟨hsubU, hdK, -, hall⟩ := w6StepK_smooth hI.smooth hI.std (hI.stage ν) hξν
  obtain ⟨-, hz, -⟩ := hall w hw
  have a3 := (w6Compose_main hI ν ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) _ hz).2.2.1
  exact (a3.hasFDerivAt.comp w (hdK w (hsubU hw)).hasFDerivAt).fderiv

/-- `Φ^{ν+1}(D_{ν+1}) ⊆ D(s_0 - 4σ_0, 2η_0 r_0)` (step `c-lim`, image bound). -/
theorem w6PhiC_mem_image (hI : W6IterHyp d S0) (ν : ℕ) :
    ∀ ξ, (∀ μ < ν + 1, ξ ∈ (w6Seq d S0 μ).Pi) → ∀ w ∈ d.domNu (ν + 1),
      w6PhiC d S0 (ν + 1) ξ w ∈ kamDomain (d.s 0 - 4 * d.sigma 0) (2 * d.etaNu 0 * d.rNu 0) := by
  induction ν with
  | zero =>
    intro ξ hξ w hw
    exact ((w6StepK_smooth hI.smooth hI.std (hI.stage 0) (hξ 0 (Nat.zero_lt_one))).2.2.2 w hw).1
  | succ ν ih =>
    intro ξ hξ w hw
    have hξν : ξ ∈ (w6Seq d S0 (ν + 1)).Pi := hξ (ν + 1) (Nat.lt_succ_self _)
    have hz := ((w6StepK_smooth hI.smooth hI.std (hI.stage (ν + 1)) hξν).2.2.2 w hw).2.1
    exact ih ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) _ hz

/-- **Operator bounds, symplecticity, surjectivity** (`bpW:w6:convergence` (iv), step `c-op`): for
`ξ ∈ Π_μ` (`μ < ν`): `Φ^ν` is holomorphic on `D_ν`, and for `w ∈ D_ν`,
`|DΦ^ν(w) W|_{p,r_0} ≤ 2|W|_{p,r_ν}`; `DΦ^ν(w)` maps `𝒫^{p_+}` into `𝒫^{p_+}` with
`|DΦ^ν(w) W|_{p_+,r_0} ≤ 2|W|_{p_+,r_ν}`; `DΦ^ν(w)` is symplectic; `DΦ^ν(w)` maps `𝒫^{p_+}` onto
`𝒫^{p_+}`. -/
theorem w6Compose_ops (hI : W6IterHyp d S0) (ν : ℕ) :
    ∀ ξ, (∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) →
      DifferentiableOn ℂ (w6PhiC d S0 ν ξ) (d.domNu ν) ∧
      ∀ w ∈ d.domNu ν,
        (∀ W, kamNorm (d.rNu 0) (fderiv ℂ (w6PhiC d S0 ν ξ) w W) ≤ 2 * kamNorm (d.rNu ν) W) ∧
        (∀ W', ∃ W'', fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'' ∧
          kamNorm (d.rNu 0) W'' ≤ 2 * kamNorm (d.rNu ν) W') ∧
        (∀ W W', w6Symp (fderiv ℂ (w6PhiC d S0 ν ξ) w W) (fderiv ℂ (w6PhiC d S0 ν ξ) w W') =
          w6Symp W W') ∧
        (∀ W'', ∃ W', fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'') := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  have hrν := W6SeqData.w6r_pos hd.1 ν
  have h0ν := W6SeqData.rNu_le_r0 hd ν
  have hc2 := w6Cp_le_two ν
  have hc1 := one_le_w6Cp ν
  -- symplecticity and surjectivity, by induction
  have hSO : ∀ ν, ∀ ξ, (∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) → ∀ w ∈ d.domNu ν,
      (∀ W W', w6Symp (fderiv ℂ (w6PhiC d S0 ν ξ) w W) (fderiv ℂ (w6PhiC d S0 ν ξ) w W') =
        w6Symp W W') ∧
      (∀ W'', ∃ W', fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'') := by
    intro ν
    induction ν with
    | zero =>
      intro ξ _ w _
      have e : w6PhiC d S0 0 ξ = id := rfl
      rw [e, fderiv_id]
      exact ⟨fun W W' => rfl, fun W'' => ⟨W'', rfl⟩⟩
    | succ ν ih =>
      intro ξ hξ w hw
      have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
      obtain ⟨-, hz, -⟩ := (w6StepK_smooth hI.smooth hd (hI.stage ν) hξν).2.2.2 w hw
      obtain ⟨-, hcl⟩ := w6StepK_clauses hI.smooth hd (hI.stage ν) hξν
      obtain ⟨-, -, hsK, hinK, honK⟩ := hcl w hw
      obtain ⟨hs, hon⟩ := ih ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) _ hz
      rw [w6PhiC_succ_fderiv hI hξ hw]
      refine ⟨fun W W' => ?_, fun W'' => ?_⟩
      · simp only [ContinuousLinearMap.comp_apply]
        rw [hs, hsK]
      · obtain ⟨W1, h1⟩ := hon W''
        obtain ⟨W', h2⟩ := honK W1
        exact ⟨W', by rw [ContinuousLinearMap.comp_apply, h2, h1]⟩
  intro ξ hξ
  refine ⟨fun w hw => ((w6Compose_main hI ν ξ hξ w hw).2.2.1).differentiableWithinAt,
    fun w hw => ?_⟩
  obtain ⟨-, -, -, -, a5, a6⟩ := w6Compose_main hI ν ξ hξ w hw
  obtain ⟨hs, hon⟩ := hSO ν ξ hξ w hw
  refine ⟨fun W => ?_, fun W' => ?_, hs, hon⟩
  · rw [a5]
    simp only [add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply]
    have h1 := kamNorm_add_le hr0 W (w6Iota (fderiv ℂ (w6PsiC d S0 ν ξ) w W))
    have h2 := kamNorm_w6Iota_le hr0 (fderiv ℂ (w6PsiC d S0 ν ξ) w W)
    have h3 := a6 W
    have h4 : kamNorm (d.rNu 0) W ≤ kamNorm (d.rNu ν) W := kamNorm_anti hrν h0ν W
    have h5 : 0 ≤ kamNorm (d.rNu ν) W := kamNorm_nonneg hrν.le W
    nlinarith
  · refine ⟨W' + fderiv ℂ (w6PsiC d S0 ν ξ) w (w6Iota W'), ?_, ?_⟩
    · rw [a5]
      simp only [add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, map_add]
    · have h1 := kamNorm_add_le hr0 W' (fderiv ℂ (w6PsiC d S0 ν ξ) w (w6Iota W'))
      have h3 := a6 (w6Iota W')
      have h2 := kamNorm_w6Iota_le hrν W'
      have h4 : kamNorm (d.rNu 0) W' ≤ kamNorm (d.rNu ν) W' := kamNorm_anti hrν h0ν W'
      have h5 : 0 ≤ kamNorm (d.rNu ν) W' := kamNorm_nonneg hrν.le W'
      have h6 : (w6Cp ν - 1) * kamNorm (d.rNu ν) (w6Iota W') ≤
          (w6Cp ν - 1) * kamNorm (d.rNu ν) W' := mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith

/-- **Reality and periodicity of `Φ^ν`** (step `c-dom`): for `ξ ∈ Π_μ` (`μ < ν`) and `w ∈ D_ν`,
`Φ^ν(w)` is real if `w` is, and `Φ^ν(w + τ_i) = Φ^ν(w) + τ_i`. -/
theorem w6Compose_real_periodic (hI : W6IterHyp d S0) (ν : ℕ) :
    ∀ ξ, (∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) → ∀ w ∈ d.domNu ν,
      (StepReal w → StepReal (w6PhiC d S0 ν ξ w)) ∧
      ∀ i : Fin 2, w6PhiC d S0 ν ξ (w + stepTau i) = w6PhiC d S0 ν ξ w + stepTau i := by
  induction ν with
  | zero => exact fun ξ _ w _ => ⟨id, fun i => rfl⟩
  | succ ν ih =>
    intro ξ hξ w hw
    have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
    obtain ⟨-, hz, -⟩ := (w6StepK_smooth hI.smooth hI.std (hI.stage ν) hξν).2.2.2 w hw
    obtain ⟨-, hcl⟩ := w6StepK_clauses hI.smooth hI.std (hI.stage ν) hξν
    obtain ⟨hrK, hpK, -⟩ := hcl w hw
    obtain ⟨hr, hp⟩ := ih ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) _ hz
    refine ⟨fun h => hr (hrK h), fun i => ?_⟩
    show w6PhiC d S0 ν ξ (w6PhiK d S0 ν ξ (w + stepTau i)) =
      w6PhiC d S0 ν ξ (w6PhiK d S0 ν ξ w) + stepTau i
    rw [hpK i, hp i]

/-- **Composed weak conjugacy** (`bpW:w6:invariance`, step `i-weak`): for `ξ ∈ Π_μ` (`μ < ν`),
`w ∈ D_ν` and `W', W''` with `DΦ^ν(w)(ι W') = ι W''`:
`ϖ_{p-1,p_+}(X_{H_0}(Φ^ν w), W'') = ϖ_{p-1,p_+}(X_{H_ν}(w), W')`, where
`X_{H_μ} = X_{N_μ} + ι X_{P_μ}` (`w6Field`, any bounds for the normal frequencies). -/
theorem w6Compose_weak (hI : W6IterHyp d S0) (ν : ℕ) :
    ∀ ξ, (∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) → ∀ {K0 K1 : ℝ}
      (hΩ0 : ∀ j : ℕ+, |(w6Seq d S0 0).Om ξ j| ≤ K0 * ((j : ℝ) + 2))
      (hΩ1 : ∀ j : ℕ+, |(w6Seq d S0 ν).Om ξ j| ≤ K1 * ((j : ℝ) + 2)),
      ∀ w ∈ d.domNu ν, ∀ W' W'' : KamPhase,
        fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'' →
        w6SympPred (w6Field hΩ0 ((w6Seq d S0 0).om ξ) ((w6Seq d S0 0).X ξ)
            (w6PhiC d S0 ν ξ w)) W'' =
          w6SympPred (w6Field hΩ1 ((w6Seq d S0 ν).om ξ) ((w6Seq d S0 ν).X ξ) w) W' := by
  induction ν with
  | zero =>
    intro ξ _ K0 K1 hΩ0 hΩ1 w _ W' W'' h
    have e : w6PhiC d S0 0 ξ = id := rfl
    rw [e, fderiv_id] at h
    have h' : W' = W'' := w6Iota_injective h
    rw [e, h']
    rfl
  | succ ν ih =>
    intro ξ hξ K0 K1 hΩ0 hΩ1 w hw W' W'' h
    have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
    obtain ⟨-, hz, -⟩ := (w6StepK_smooth hI.smooth hI.std (hI.stage ν) hξν).2.2.2 w hw
    obtain ⟨-, hcl⟩ := w6StepK_clauses hI.smooth hI.std (hI.stage ν) hξν
    obtain ⟨-, -, -, hinK, -⟩ := hcl w hw
    rw [w6PhiC_succ_fderiv hI hξ hw, ContinuousLinearMap.comp_apply] at h
    obtain ⟨W1, h1⟩ := hinK W'
    rw [h1] at h
    have hΩm := homOmega_le (hI.stage ν).freq_spec hξν
    have e1 := ih ξ (fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)) hΩ0 hΩm _ hz W1 W'' h
    have e2 := w6StepK_weakConj hI.smooth hI.std (hI.stage ν) hξν hΩm hΩ1 hw W' W1 h1
    exact e1.trans e2

end compose

end KAM.Wave
