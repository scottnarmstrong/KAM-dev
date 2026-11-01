/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.PrepStep
public import KAM.Wave.Iteration.ConvFreq
public import KAM.Wave.Iteration.FreqLip
public import KAM.Wave.Iteration.Applicable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the wave iteration, applicability and the frequency pairs (`bpW:w6:applicable`,
`bpW:w6:freq-lip`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:wave-iteration`, `bpW:w6:applicable`,
`bpW:w6:freq-lip` (milestone W6).

* `W6StepRealMod`: W5's reality clause for `P_+` in the modified case (branch inp-w5r,
  `stepTheoremMod_reality`); a hypothesis of the conditional helpers only.
* `w6applicable_k0_of_shift_half`: the `k = 0` clause of `applicable` from the shift bound with the
  weight `J^{1/2}` (the weight that W5's `stepTheoremMod` (iii) provides).
* `w6Applicable_of_stepRealMod` (conditional helper): the hypotheses `W6ConvHyp` of Proposition
  `bpW:w6:convergence` hold for the wave iteration (Definition `bpW:w6:wave-iteration`), for every
  starting size `ε₀ ∈ [ε^♭_0, γ₁ α̌]`. Every hypothesis except the reality of `P_0` is proved from
  the prep-step outputs.
* `w6IsFreqPair_of_bounds_half`: W6-PREP's `w6IsFreqPair_of_bounds` with the shift bound at
  the weight `J^{1/2}`; the normal shift then enters `ε₂` instead of `ε₁`
  (`ε₁ = 0`, `ε₂ = 3γα + 4ε₀`; deviation forced by W5's interface, see the handoff).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- W5's reality clause for `P_+` in the modified case (blueprint `bpW:w5:step` (ii)), for the data
of the preparatory step (`a = p = 1`, `p_+ = 3/2`, `τ = 24`, `β = 1/4`, `γ_G = w6GamG`); proved in
branch inp-w5r as `stepTheoremMod_reality`. -/
def W6StepRealMod : Prop :=
  ∀ (s r σ η α lam ε ε₀ ε₁ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) (P : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    (H : StepHypMod 1 1 (3 / 2) s r σ η w6Tau α (1 / 4) lam ε ε₀ ε₁ w6GamG M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)],
    ∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.core.Pplus ξ w).im = 0

section

variable {m : ℝ} {hm : 0 < m}

/-- **`k = 0` clause of `bpW:w6:applicable`** from the shift bound with weight `J^{1/2}`:
`|⟨l, Ω_0⟩| ≥ 2β_*⟨l⟩` for `l ∈ Λ`. -/
theorem w6applicable_k0_of_shift_half {α ε : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm)
    (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α) {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2)
    {Ωh Ω0 : ℕ → ℝ} (hΩ0 : ∀ j, Ω0 j = omegaNor m hm ξ j + Ωh j)
    (hΩh : ∀ j, normLab j ^ (1 / 2 : ℝ) * |Ωh j| ≤ 3 * ε) {l : ℕ →₀ ℤ} (hl : IsLam l) :
    2 * measBetaStar m * japL l ≤ |linF l Ω0| := by
  have h3 := three_betaStar_japL_le m hm hξ hl
  have hj : ∀ j, |Ωh j| ≤ 3 * ε := by
    intro j
    have h := hΩh j
    have hJ := one_le_normLab_rpow_half j
    have := abs_nonneg (Ωh j)
    nlinarith
  have hlin := abs_linF_le_l1Norm_mul l Ωh hj
  have hl2 : (l1Norm l : ℝ) ≤ 2 := by exact_mod_cast hl.2
  have hsh : |linF l Ωh| ≤ 6 * ε := by nlinarith
  obtain ⟨-, -, hαh, -, hhβ, -⟩ := alpha_facts m hm hα hα0
  have hg := w6Gamma_le_fortieth m hm
  have hgp := w6Gamma_pos m hm
  have hβ0 := measBetaStar_pos hm
  have h6 : 6 * ε ≤ measBetaStar m := by nlinarith
  have hJ := japL_ge_one l
  have e : linF l Ω0 = linF l (omegaNor m hm ξ) + linF l Ωh := by
    have : Ω0 = fun j => omegaNor m hm ξ j - (-Ωh j) := funext fun j => by rw [hΩ0]; ring
    rw [this, linF_sub']
    have : linF l (fun j => -Ωh j) = -linF l Ωh := by
      unfold linF Finsupp.sum; rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  rw [e]
  have htri := abs_sub_abs_le_abs_sub (linF l (omegaNor m hm ξ)) (-linF l Ωh)
  rw [sub_neg_eq_add, abs_neg] at htri
  have : measBetaStar m ≤ measBetaStar m * japL l := le_mul_of_one_le_right hβ0.le hJ
  nlinarith

end

section

variable {m : ℝ} {hm : 0 < m}

/-- **Lipschitz frequencies, conditional helper with the shift at weight `J^{1/2}`**
(blueprint `bpW:w6:freq-lip`, steps `fl-size`, `fl-lip`): the shift bounds
`J^{1/2}(|Ω̂_J| + λ|Ω̂_J|^ℒ) ≤ 3ε`, `|ω̂| + λ|ω̂|^ℒ ≤ 6πε` and the drift bounds of
`bpW:w6:convergence` (ii) give (H1)–(H2) with `ε_ω = 6πγα + 8πε₀`, `ε₁ = 0`, `ε₂ = 3γα + 4ε₀`,
`θ = 425(1+M)max(γ,γ₁)`. -/
theorem w6IsFreqPair_of_bounds_half {Pi D : Set (Fin 2 → ℝ)} {α ε ε₀ : ℝ}
    (hDm : MeasurableSet D) (hDsub : D ⊆ Pi) (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm)
    (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α) (hε₀ : 0 ≤ ε₀)
    (hε₀γ : ε₀ ≤ w6Gamma1 m hm * alphaCheck α)
    {ωh ω0 ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ωh Ω0 Ω : (Fin 2 → ℝ) → ℕ → ℝ}
    (hω0 : ∀ ξ ∈ D, ω0 ξ = omegaTan m hm ξ + ωh ξ)
    (hΩ0 : ∀ ξ ∈ D, ∀ j, Ω0 ξ j = omegaNor m hm ξ j + Ωh ξ j)
    (hωh : ∀ ξ ∈ D, ‖ωh ξ‖ ≤ 6 * π * ε)
    (hωhL : ∀ ξ ∈ D, ∀ ζ ∈ D, α / w6M m hm * ‖ωh ξ - ωh ζ‖ ≤ 6 * π * ε * ‖ξ - ζ‖)
    (hΩh : ∀ ξ ∈ D, ∀ j, normLab j ^ (1 / 2 : ℝ) * |Ωh ξ j| ≤ 3 * ε)
    (hΩhL : ∀ ξ ∈ D, ∀ ζ ∈ D, ∀ j,
      α / w6M m hm * (normLab j ^ (1 / 2 : ℝ) * |Ωh ξ j - Ωh ζ j|) ≤ 3 * ε * ‖ξ - ζ‖)
    (hω : ∀ ξ ∈ D, ‖ω ξ - ω0 ξ‖ ≤ 8 * π * ε₀)
    (hωL : ∀ ξ ∈ D, ∀ ζ ∈ D, alphaCheck α / w6M0 m hm * ‖(ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)‖ ≤
      64 * π * ε₀ * ‖ξ - ζ‖)
    (hΩ : ∀ ξ ∈ D, ∀ j, normLab j ^ (1 / 2 : ℝ) * |Ω ξ j - Ω0 ξ j| ≤ 4 * ε₀)
    (hΩL : ∀ ξ ∈ D, ∀ ζ ∈ D, ∀ j, alphaCheck α / w6M0 m hm *
      (normLab j ^ (1 / 2 : ℝ) * |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)|) ≤ 16 * ε₀ * ‖ξ - ζ‖) :
    IsFreqPair m hm Pi α D ω Ω (6 * π * w6Gamma m hm * α + 8 * π * ε₀) 0
      (3 * w6Gamma m hm * α + 4 * ε₀) (w6Theta m hm) := by
  obtain ⟨hεω, -, -, hθ⟩ := w6freqLip_consts (m := m) (hm := hm) hα hα0 hε₀ hε₀γ
  obtain ⟨hc0, hcα, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hM := w6M_pos m hm
  have hM0 := w6M0_pos m hm
  have hlam : 0 < α / w6M m hm := div_pos hα hM
  have hlam0 : 0 < alphaCheck α / w6M0 m hm := div_pos hc0 hM0
  have hπ := Real.pi_pos
  have hcω := w6_lipcoef_omega (m := m) (hm := hm) hα hα0 hεγ hε₀γ
  have hcΩ := w6_lipcoef_Omega (m := m) (hm := hm) hα hα0 hε hεγ hε₀ hε₀γ
  have hgα : 6 * π * ε ≤ 6 * π * w6Gamma m hm * α := by
    have := mul_le_mul_of_nonneg_left hεγ (by positivity : (0 : ℝ) ≤ 6 * π); linarith
  have hg := w6Gamma_le_fortieth m hm
  have hgp := w6Gamma_pos m hm
  have hg1 := w6Gamma1_le_small m hm
  have hg1p := w6Gamma1_pos m hm
  have hε2 : 3 * w6Gamma m hm * α + 4 * ε₀ ∈ Set.Icc 0 α := by
    have h4 : 4 * ε₀ ≤ α / 2 := by
      have : w6Gamma1 m hm * alphaCheck α ≤ w6Gamma1 m hm * α :=
        mul_le_mul_of_nonneg_left hcα hg1p.le
      have : w6Gamma1 m hm ≤ 1 / 8 := hg1.trans (by norm_num)
      nlinarith
    constructor <;> nlinarith
  refine ⟨hDm, hDsub, hεω, ⟨le_rfl, hα.le⟩, hε2, hθ, ?_, ?_, ?_, ?_⟩
  · -- (H1), sup
    intro ξ hξ
    have e : ω ξ - omegaTan m hm ξ = (ω ξ - ω0 ξ) + ωh ξ := by rw [hω0 ξ hξ]; abel
    rw [e]
    calc ‖(ω ξ - ω0 ξ) + ωh ξ‖ ≤ ‖ω ξ - ω0 ξ‖ + ‖ωh ξ‖ := norm_add_le _ _
      _ ≤ 8 * π * ε₀ + 6 * π * ε := add_le_add (hω ξ hξ) (hωh ξ hξ)
      _ ≤ 6 * π * w6Gamma m hm * α + 8 * π * ε₀ := by linarith
  · -- (H1), Lipschitz
    intro ξ hξ ζ hζ
    have e : (ω ξ - omegaTan m hm ξ) - (ω ζ - omegaTan m hm ζ) =
        ((ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)) + (ωh ξ - ωh ζ) := by
      rw [hω0 ξ hξ, hω0 ζ hζ]; abel
    rw [e]
    have h1 := w6_le_div_mul_of_mul_le hlam0 (hωL ξ hξ ζ hζ)
    have h2 := w6_le_div_mul_of_mul_le hlam (hωhL ξ hξ ζ hζ)
    have hn := norm_nonneg (ξ - ζ)
    calc _ ≤ ‖(ω ξ - ω0 ξ) - (ω ζ - ω0 ζ)‖ + ‖ωh ξ - ωh ζ‖ := norm_add_le _ _
      _ ≤ 64 * π * ε₀ / (alphaCheck α / w6M0 m hm) * ‖ξ - ζ‖ +
          6 * π * ε / (α / w6M m hm) * ‖ξ - ζ‖ := add_le_add h1 h2
      _ = (6 * π * ε / (α / w6M m hm) + 64 * π * ε₀ / (alphaCheck α / w6M0 m hm)) *
          ‖ξ - ζ‖ := by ring
      _ ≤ w6Theta m hm * ‖ξ - ζ‖ := mul_le_mul_of_nonneg_right hcω hn
  · -- (H2), sup
    intro ξ hξ j
    have e : Ω ξ j - omegaNor m hm ξ j = (Ω ξ j - Ω0 ξ j) + Ωh ξ j := by rw [hΩ0 ξ hξ j]; ring
    rw [e]
    have h1 := rpow_half_mul_le (hΩ ξ hξ j)
    have h2 := rpow_half_mul_le (hΩh ξ hξ j)
    have hJp : 0 ≤ normLab j ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (normLab_pos j).le _
    have h3 : 3 * ε * normLab j ^ (-(1 / 2 : ℝ)) ≤
        3 * w6Gamma m hm * α * normLab j ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hJp
    calc |(Ω ξ j - Ω0 ξ j) + Ωh ξ j| ≤ |Ω ξ j - Ω0 ξ j| + |Ωh ξ j| := abs_add_le _ _
      _ ≤ 4 * ε₀ * normLab j ^ (-(1 / 2 : ℝ)) + 3 * w6Gamma m hm * α *
          normLab j ^ (-(1 / 2 : ℝ)) := by linarith
      _ = _ := by ring
  · -- (H2), Lipschitz
    intro ξ hξ ζ hζ j
    have hn := norm_nonneg (ξ - ζ)
    have hJp : 0 ≤ normLab j ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (normLab_pos j).le _
    have e : (Ω ξ j - omegaNor m hm ξ j) - (Ω ζ j - omegaNor m hm ζ j) =
        ((Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)) + (Ωh ξ j - Ωh ζ j) := by
      rw [hΩ0 ξ hξ j, hΩ0 ζ hζ j]; ring
    rw [e]
    have h1 : |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)| ≤
        16 * ε₀ / (alphaCheck α / w6M0 m hm) * ‖ξ - ζ‖ * normLab j ^ (-(1 / 2 : ℝ)) := by
      apply rpow_half_mul_le
      exact w6_le_div_mul_of_mul_le hlam0 (by linarith [hΩL ξ hξ ζ hζ j])
    have h2 : |Ωh ξ j - Ωh ζ j| ≤
        3 * ε / (α / w6M m hm) * ‖ξ - ζ‖ * normLab j ^ (-(1 / 2 : ℝ)) := by
      apply rpow_half_mul_le
      exact w6_le_div_mul_of_mul_le hlam (by linarith [hΩhL ξ hξ ζ hζ j])
    calc _ ≤ |(Ω ξ j - Ω0 ξ j) - (Ω ζ j - Ω0 ζ j)| + |Ωh ξ j - Ωh ζ j| := abs_add_le _ _
      _ ≤ (3 * ε / (α / w6M m hm) + 16 * ε₀ / (alphaCheck α / w6M0 m hm)) *
          (normLab j ^ (-(1 / 2 : ℝ)) * ‖ξ - ζ‖) := by nlinarith
      _ ≤ w6Theta m hm * (normLab j ^ (-(1 / 2 : ℝ)) * ‖ξ - ζ‖) :=
          mul_le_mul_of_nonneg_right hcΩ (by positivity)
      _ = _ := by ring

end

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

theorem waveSeq_lam_zero (r ε ε₀ : ℝ) :
    (w6WaveSeq m hm α r ε ε₀).lam 0 = alphaCheck α / w6M0 m hm := by
  unfold W6SeqData.lam
  rw [W6SeqData.alpha_zero, W6SeqData.M_zero]
  rfl

/-- The hypotheses of Proposition `bpW:w6:convergence` for the wave iteration, except the reality
of `P_0` (`W6ConvHyp` minus `real`), for `ε₀ ∈ [ε^♭_0, γ₁ α̌]`. -/
theorem waveConv_parts (H : W6PrepHyp m hm Pi α r ε P X) {ε₀ : ℝ}
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    (w6WaveSeq m hm α r ε ε₀).Valid ∧
    (w6WaveSeq m hm α r ε ε₀).eps0 ≤ w6Gamma0 * (w6WaveSeq m hm α r ε ε₀).al0 *
      (w6WaveSeq m hm α r ε ε₀).sigma 0 ^ w6T ∧
    (∃ T Mω MΩ : ℝ, HomFreqHyp (Pi \ prepSet m hm Pi α) H.om0 H.Om0 T Mω MΩ ∧
      Mω + MΩ ≤ (w6WaveSeq m hm α r ε ε₀).M0) ∧
    (w6WaveSeq m hm α r ε ε₀).al0 ≤ measBetaStar m ∧
    8 * (w6WaveSeq m hm α r ε ε₀).eps0 ≤ measBetaStar m ∧
    (∀ ξ ∈ Pi \ prepSet m hm Pi α, ∀ l : ℕ →₀ ℤ, IsLam l →
      2 * measBetaStar m * japL l ≤ |linF l (w6Om7 (H.Om0 ξ))|) ∧
    FamBound (Pi \ prepSet m hm Pi α) ((w6WaveSeq m hm α r ε ε₀).dom 0)
      ((w6WaveSeq m hm α r ε ε₀).r 0) ((w6WaveSeq m hm α r ε ε₀).lam 0)
      ((w6WaveSeq m hm α r ε ε₀).eps 0) H.X0 := by
  have hflat := w6EpsFlat_pos H.hα H.hε
  have hε₀ : 0 < ε₀ := lt_of_lt_of_le hflat hlo
  obtain ⟨-, h8, -, hcβ⟩ := w6applicable_arith (m := m) (hm := hm) H.hα H.hα0
  obtain ⟨c₀, c₁, hc0, hc1, hcs, hcb, -⟩ := H.shift_Omega
  have hlam := div_pos H.hα (w6M_pos m hm)
  refine ⟨w6WaveSeq_valid H.hα H.hα0 H.hr H.hε hε₀, w6WaveSeq_small H.hα H.hα0 hhi, H.freq0,
    hcβ, by show 8 * ε₀ ≤ _; linarith, fun ξ hξ l hl => ?_, ?_⟩
  · refine w6applicable_k0_of_shift_half H.hα H.hα0 H.hε.le H.hεγ (H.sub ξ hξ.1)
      (Ωh := fun j => w6Om7 (H.Om0 ξ) j - omegaNor m hm ξ j) (fun j => by ring) (fun j => ?_) hl
    have := hcb ξ hξ j
    have : 0 ≤ α / w6M m hm * c₁ := mul_nonneg hlam.le hc1
    linarith
  · rw [waveSeq_lam_zero]
    exact (H.w6size.2.2.2.1).mono_lam subset_rfl subset_rfl le_rfl hlo

/-- **Applicability** (blueprint `bpW:w6:applicable`; conditional helper on W5's reality clause
`W6StepRealMod`, not the label): the hypotheses of Proposition `bpW:w6:convergence` hold for the
wave iteration (Definition `bpW:w6:wave-iteration`, `β₀ = β_*`), for every starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`. -/
theorem w6Applicable_of_stepRealMod (hRm : W6StepRealMod) (H : W6PrepHyp m hm Pi α r ε P X)
    {ε₀ : ℝ} (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    W6ConvHyp (w6WaveSeq m hm α r ε ε₀) (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0
      (measBetaStar m) := by
  have := H.factR
  obtain ⟨hv, hs, hf, hb, h8, hk, hfb⟩ := H.waveConv_parts hlo hhi
  obtain ⟨hsm, hper, -⟩ := H.w6size
  exact ⟨hv, hs, hf, hb, h8, hk, hsm, hper, fun ξ hξ w hw hwr =>
    hRm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H.stepHyp.hyp ξ hξ (StepPhase.ofK w) hw hwr, hfb⟩

end W6PrepHyp

end KAM.Wave
