/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedLipDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The field bounds with modified divisors (`bpW:w5:w4-modified` (ii))

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

* `homModF_sub_compBounds`: the component bounds of `F(ξ) - F(ζ)` with `K = K_S` and
  `E^♮ = B^♮_σ(ε^L + 2Mε/α)d/α` (step `m-ass`);
* `homModLemma_lipschitz`: **(ii)** `|X_{F(ξ)} - X_{F(ζ)}|_{p₊,r} ≤
  (C₁B^♮_σ/α)(ε^L + 2Mε/α)|ξ-ζ|` on `D(s-σ,r)` when `2β ≤ p+1-p₊`;
* `homModLemma2`: the `λ`-form `|X_F|^λ ≤ (3C₁B^♮_σ/α)|X_R|^λ` for `0 ≤ λ ≤ α/M`, and
  `B^W_σ ≤ B^♮_σ ≤ b^♮(τ) σ^{-(2τ+4)}` (part (iii), `waveBN_le`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

section assemble

variable {a p pb s σ τ α M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}

/-- **Component bounds of `F(ξ) - F(ζ)`** (`bpW:w5:w4-modified` (ii), steps `m-lip`, `m-act`,
`m-ass`). -/
theorem homModF_sub_compBounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1)
    {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s) (hm₁ : HomModMultBounds a p pb τ α w₁ W₁)
    (hm₂ : HomModMultBounds a p pb τ α w₂ W₂) (hL : HomModMultLip a p pb τ α M d w₁ W₁ w₂ W₂)
    (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₁)
    (hX₂ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₂)
    (hXL : HomFieldBound_gen ha hp (homModPP1 p) r (εL * d) (R₁.homSub R₂))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    HomCompBounds_gen ha hp hpb r homKS (waveBN τ σ / α * (εL + 2 * M * ε / α) * d)
      ((homModSolveTaylor hτ hα hσ hσs hc hm₁ R₁).homSub
        (homModSolveTaylor hτ hα hσ hσs hc hm₂ R₂)) θ := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hX₁' := homFieldBound_reweight ha hp hpb hc hr R₁ hX₁
  have hX₂' := homFieldBound_reweight ha hp hpb hc hr R₂ hX₂
  have hXL' : HomFieldBound_gen ha hp hpb r (εL * d)
      ((homReweight hc R₁).homSub (homReweight hc R₂)) := by
    rw [← homReweight_homSub]; exact homFieldBound_reweight ha hp hpb hc hr _ hXL
  set F₁ := homModSolveTaylor hτ hα hσ hσs hc hm₁ R₁ with hF₁
  set F₂ := homModSolveTaylor hτ hα hσ hσs hc hm₂ R₂ with hF₂
  have hK1 := one_le_homKS
  have hπ := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hE : waveBW τ σ / α * (εL + 2 * M * ε / α) * d ≤
      waveBN τ σ / α * (εL + 2 * M * ε / α) * d := by
    have := waveBW_le_waveBN hτ hσ
    have h0 : 0 ≤ (εL + 2 * M * ε / α) * d := by positivity
    have e1 : waveBW τ σ / α * (εL + 2 * M * ε / α) * d =
        waveBW τ σ / α * ((εL + 2 * M * ε / α) * d) := by ring
    have e2 : waveBN τ σ / α * (εL + 2 * M * ε / α) * d =
        waveBN τ σ / α * ((εL + 2 * M * ε / α) * d) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this hα.le) h0
  have hpart : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      {f g : (Fin 2 → ℂ) → E}, IsHomComp (s - σ) f → IsHomComp (s - σ) g → ∀ i : Fin 2,
      homPartial i (fun z => f z - g z) θ = homPartial i f θ - homPartial i g θ :=
    fun hf hg i => homPartial_sub_comp_gen hf hg hθ i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, fun i y => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact (homModLip_b ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂').trans (by gcongr)
  · exact (homModLip_cp ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂').trans (by gcongr)
  · exact (homModLip_cm ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂').trans (by gcongr)
  · exact (homModLip_P ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂').trans (by gcongr)
  · exact (homModLip_Q ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ R₁ R₂ hX₁ hXL
      hX₂).trans (by gcongr)
  · exact (homModLip_Qt ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ R₁ R₂ hX₁ hXL
      hX₂).trans (by gcongr)
  · exact (homModLip_P' ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂').trans (by gcongr)
  · show ‖homPartial i (fun z => F₁.a0 z - F₂.a0 z) θ‖ ≤ _
    rw [hpart F₁.comp_a0 F₂.comp_a0 i]
    exact (homModLip_da ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i).trans (by gcongr)
  · show ‖∑ k, homPartial i (fun z => F₁.b z - F₂.b z) θ k * y k‖ ≤ _
    rw [hpart F₁.comp_b F₂.comp_b i]
    exact (homModLip_db ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i y).trans (by gcongr)
  · show homDualNorm_gen ha (homPP hp hpb) (homPartial i (fun z => F₁.cp z - F₂.cp z) θ) ≤ _
    rw [hpart F₁.comp_cp F₂.comp_cp i]
    exact (homModLip_dcp ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i).trans (by gcongr)
  · show homDualNorm_gen ha (homPP hp hpb) (homPartial i (fun z => F₁.cm z - F₂.cm z) θ) ≤ _
    rw [hpart F₁.comp_cm F₂.comp_cm i]
    exact (homModLip_dcm ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i).trans (by gcongr)
  · show ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (fun z => F₁.P z - F₂.P z) θ)‖ ≤ _
    rw [hpart F₁.comp_P F₂.comp_P i]
    exact (homModLip_dP ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i).trans (by gcongr)
  · show ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (fun z => F₁.P' z - F₂.P' z) θ)‖ ≤ _
    rw [hpart F₁.comp_P' F₂.comp_P' i]
    exact (homModLip_dP' ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ _ _ hX₁' hXL'
      hX₂' i).trans (by gcongr)
  · show ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (fun z => F₁.Q z - F₂.Q z) θ)‖ ≤ _
    rw [hpart F₁.comp_Q F₂.comp_Q i]
    exact homModLip_dQ ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ R₁ R₂ hX₁ hXL hX₂ i

/-- CONDITIONAL helper for `bpW:w5:w4-modified` (ii): assumes the gates `HomModMultBounds`,
`HomModMultLip`. The source-premise export is `homModLemma_lipschitz`. -/
theorem homModLemma_lipschitz_of_gates (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hc : pb ≤ p + 1) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hM : 0 ≤ M)
    (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    (hm₁ : HomModMultBounds a p pb τ α w₁ W₁) (hm₂ : HomModMultBounds a p pb τ α w₂ W₂)
    (hL : HomModMultLip a p pb τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₁)
    (hX₂ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₂)
    (hXL : HomFieldBound_gen ha hp (homModPP1 p) r (εL * d) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * M * ε / α) * d))
      ((homModSolveTaylor hτ hα hσ hσs hc hm₁ R₁).homSub
        (homModSolveTaylor hτ hα hσ hσs hc hm₂ R₂)) := by
  intro θ y z zb hdom
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hE0 : 0 ≤ waveBN τ σ / α * (εL + 2 * M * ε / α) * d := by
    have := (waveBW_nonneg τ σ).trans (waveBW_le_waveBN hτ hσ); positivity
  exact homXnorm_le_of_components_gen ha hp hpb hr one_le_homKS hE0 _
    (homModF_sub_compBounds ha hp hpb hc hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL
      hdom.1) hdom.2.1.le hdom.2.2

end assemble

/-- **`bpW:w5:w4-modified` (ii), Lipschitz bound** from the source premises (`HomFreqHyp`
(`bpW:w5:freq`), `HomMelnikovMod` with `0 ≤ β`, `2β ≤ p+1-p₊`, `α > 0`, `ξ, ζ ∈ Π`): for
`R(ξ), R(ζ) ∈ 𝒯_s` (`p̄ = p+1`) with `|X_{R(·)}|_{p+1,r} ≤ ε` and
`|X_{R(ξ)} - X_{R(ζ)}|_{p+1,r} ≤ ε^L|ξ-ζ|` on `D(s,r)`, the solutions with modified divisors satisfy
`|X_{F(ξ)} - X_{F(ζ)}|_{p₊,r} ≤ (C₁B^♮_σ/α)(ε^L + 2Mε/α)|ξ-ζ|` on `D(s-σ,r)`, `M = M_ω + M_Ω`,
`C₁ = 7 + 10K_S`. -/
theorem homModLemma_lipschitz {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α β a p pb s σ : ℝ}
    (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikovMod τ α β Par ω Ω) (hβ0 : 0 ≤ β)
    (h2β : 2 * β ≤ p + 1 - pb) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL : ℝ}
    (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₁)
    (hX₂ : HomFieldBound_gen ha hp (homModPP1 p) r ε R₂)
    (hXL : HomFieldBound_gen ha hp (homModPP1 p) r (εL * ‖ξ - ζ‖) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r
      ((7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α) * ‖ξ - ζ‖))
      ((homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 (homMod_beta_le hβ0 h2β))
          (homModMultBounds_of hα hβ0 (homMod_beta_le hβ0 h2β) hH hξ) R₁).homSub
        (homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 (homMod_beta_le hβ0 h2β))
          (homModMultBounds_of hα hβ0 (homMod_beta_le hβ0 h2β) hH hζ) R₂)) :=
  homModLemma_lipschitz_of_gates ha hp hpb (by linarith) hr hτ hα
    (by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]) (norm_nonneg _) hεL hσ hσs
    (homModMultBounds_of hα hβ0 (by linarith) hH hξ)
    (homModMultBounds_of hα hβ0 (by linarith) hH hζ)
    (homModMultLip_of h hα hβ0 h2β hH hξ hζ) R₁ R₂ hX₁ hX₂ hXL

/-- **`bpW:w5:w4-modified` (ii), `λ`-form, and (iii)**: for `M > 0`, `0 ≤ λ ≤ α/M`, with
`(ε, ε^L)` the uniform and Lipschitz bounds of `X_R` and `C₁ = 7 + 10K_S`, the bounds
`C₁B^W_σε/α` of (i) and `C₁B^♮_σ(ε^L + 2Mε/α)/α` of (ii) combine to
`|X_F|^λ ≤ (3C₁B^♮_σ/α)|X_R|^λ`; moreover `B^W_σ ≤ B^♮_σ ≤ b^♮(τ) σ^{-(2τ+4)}` for
`0 < σ ≤ 1`. -/
theorem homModLemma2 {τ α M lam σ ε εL : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hM : 0 < M)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ α / M) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 ≤ ε)
    (hεL : 0 ≤ εL) :
    homLamNorm lam ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
        ((7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * M * ε / α))) ≤
        3 * (7 + 10 * homKS) * waveBN τ σ / α * homLamNorm lam ε εL ∧
      waveBW τ σ ≤ waveBN τ σ ∧ waveBN τ σ ≤ waveBNconst τ / σ ^ (2 * τ + 4) := by
  have hWN := waveBW_le_waveBN hτ hσ
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  refine ⟨?_, hWN, waveBN_le hτ hσ hσ1⟩
  have h1 := (homLemma2 (α := α) (M := M) (lam := lam) (σ := σ) (ε := ε) (εL := εL) hτ hα hM hlam0
    hlam hσ hσ1 hε hεL).2.1
  unfold homLamNorm at h1 ⊢
  have hC : 0 ≤ 7 + 10 * homKS := by linarith
  have hBN : 0 ≤ waveBN τ σ := hB.trans hWN
  have hlM : lam * M / α ≤ 1 := by
    rw [div_le_one hα]
    have := mul_le_mul_of_nonneg_right hlam hM.le
    rwa [div_mul_cancel₀ _ hM.ne'] at this
  have key : ε + lam * (εL + 2 * M * ε / α) ≤ 3 * (ε + lam * εL) := by
    have e1 : lam * (2 * M * ε / α) = 2 * ε * (lam * M / α) := by ring
    have e2 : 2 * ε * (lam * M / α) ≤ 2 * ε := by nlinarith
    nlinarith [mul_nonneg hlam0 hεL]
  have hfirst : (7 + 10 * homKS) * (waveBW τ σ * ε / α) ≤
      (7 + 10 * homKS) * (waveBN τ σ * ε / α) := by
    gcongr
  have hS : 0 ≤ εL + 2 * M * ε / α := by positivity
  calc (7 + 10 * homKS) * (waveBW τ σ * ε / α) +
        lam * ((7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * M * ε / α)))
      ≤ (7 + 10 * homKS) * (waveBN τ σ * ε / α) +
        lam * ((7 + 10 * homKS) * (waveBN τ σ / α * (εL + 2 * M * ε / α))) := by linarith
    _ = (7 + 10 * homKS) * waveBN τ σ / α * (ε + lam * (εL + 2 * M * ε / α)) := by ring
    _ ≤ (7 + 10 * homKS) * waveBN τ σ / α * (3 * (ε + lam * εL)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end KAM.Wave
