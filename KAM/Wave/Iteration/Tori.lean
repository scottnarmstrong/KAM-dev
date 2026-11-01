/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ToriBk
public import KAM.Wave.Birkhoff.MainGamma
public import KAM.Wave.Analytic.TorusAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: invariant tori in Birkhoff coordinates (`bpW:w6:tori`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:tori` (steps `t-cont`, `t-prep`, `t-bk`, `t-an`).

For the wave iteration (Definition `bpW:w6:wave-iteration`) with `H_in = N_ξ + P_ξ` of
`bpW:w5:action-angle` (iv) on `D(s, r)` (`P = w6InP`, `X_P = w6InX`; `bpW:w5:initial` supplies the
hypotheses through `w6PrepHyp_initial`), starting size `ε₀ ∈ [ε^♭_0, γ₁ α̌]`, and
`Ψ̃_ξ(θ) = 𝒜_ξ(Φ_P(Φ_*(θ)))` (`W6PrepHyp.w6TorusBk`), `ν_* = ω_*/(2π)` (`W6PrepHyp.w6NuStar`):

* `W6PrepHyp.w6NuStar_lipschitz`: `ν_*` is Lipschitz on `Π_*` (`bpW:w6:final-freq`);
* `W6PrepHyp.w6TorusBk_invariance_strip`: the invariance (iii) for `θ ∈ T_{s_0/2}` (steps
  `t-prep`: W6's `w6ToriKam`; `t-bk`: W5's `aaConjugacy` at `w = Φ_P Φ_* θ` and the chain rule);
* `W6PrepHyp.w6TorusBk_analytic`: (v), `θ ↦ 𝒵⁻¹ Γ(Ψ̃_ξ(θ))` restricted to `ℝ²` is real analytic into
  `WaveSpace` (W3's `Γ = birkGamma … 1` holomorphic on `B_{ρ₁}` and real, W1's `torus_analytic`);
* **`W6PrepHyp.w6Tori`**: the theorem, clauses (i)-(v).

The hypotheses beyond the wave iteration are those of `bpW:w5:action-angle` (ii) on `Π`:
`|ξ|_∞ ≤ t`, `ξ_i ≥ 2r²` (implied by the `ρ_ξ`-neighbourhood condition of `bpW:w5:initial`), and
`c_A(t + r²) < ρ₁²` (so that `Ψ̃_ξ` takes values in `B_{ρ₁}`, where `X_{H'}` and `Γ` are defined).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology Complex

namespace KAM.Wave

open KAM

variable {m : ℝ} {hm : 0 < m}

theorem w6_half_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num

theorem w6_strip_sub_single {s : ℝ} {z : Fin 2 → ℂ} (hz : z ∈ complexStrip 2 s) (i : Fin 2) :
    z + _root_.Pi.single i 1 ∈ complexStrip 2 s ∧ z - _root_.Pi.single i 1 ∈ complexStrip 2 s := by
  have h1 := w6_strip_add_single hz i 1
  have h2 := w6_strip_add_single hz i (-1)
  rw [Complex.ofReal_one] at h1
  rw [Complex.ofReal_neg, Complex.ofReal_one, Pi.single_neg, ← sub_eq_add_neg] at h2
  exact ⟨h1, h2⟩

namespace W6PrepHyp

variable {Pi : Set (Fin 2 → ℝ)} {α r ε ε₀ t : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **`ν_*` is Lipschitz on `Π_*`** (`bpW:w6:tori` (ii), by `bpW:w6:final-freq`). -/
theorem w6NuStar_lipschitz (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    ∃ K : NNReal, LipschitzOnWith K (H.w6NuStar ε₀) (H.wavePiStar ε₀) := by
  have hS : MeasSetup m hm Pi α := ⟨H.meas, H.sub, H.hα, H.hα0⟩
  obtain ⟨-, -, hl⟩ := H.w6FinalFreq hS hlo hhi
  have hπ : 0 < 2 * π := by positivity
  refine ⟨Real.toNNReal ((measNA m hm + w6Theta m hm) / (2 * π)),
    LipschitzOnWith.of_dist_le_mul fun ξ hξ ζ hζ => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have e : H.w6NuStar ε₀ ξ - H.w6NuStar ε₀ ζ =
      (2 * π)⁻¹ • (H.w6OmStarW ε₀ ξ - H.w6OmStarW ε₀ ζ) := by
    ext i; simp only [w6NuStar, _root_.Pi.sub_apply, _root_.Pi.smul_apply, smul_eq_mul]; ring
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hπ]
  have h1 : ‖H.w6OmStarW ε₀ ξ - H.w6OmStarW ε₀ ζ‖ ≤ (measNA m hm + w6Theta m hm) * ‖ξ - ζ‖ :=
    hl ξ hξ ζ hζ
  calc (2 * π)⁻¹ * ‖H.w6OmStarW ε₀ ξ - H.w6OmStarW ε₀ ζ‖
      ≤ (2 * π)⁻¹ * ((measNA m hm + w6Theta m hm) * ‖ξ - ζ‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (measNA m hm + w6Theta m hm) / (2 * π) * ‖ξ - ζ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)

/-- **Invariance** (`bpW:w6:tori` (iii), steps `t-prep`, `t-bk`), for `θ ∈ T_{s_0/2}`:
`∂_θ Ψ̃_ξ(θ) ν_* = X_{H'}(Ψ̃_ξ(θ))` in `𝔚^{p-1}`, `X_{H'} = X_Λ + X_Ḡ + X_{G^{nor}} + X_K`
(`bpW:w5:action-angle` (v); `X_K` takes the membership `Ψ̃_ξ(θ) ∈ B_{ρ₁}` as typing data). -/
theorem w6TorusBk_invariance_strip (H : W6PrepHyp m hm Pi α r ε (w6InP m hm) (w6InX m hm))
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ H.wavePiStar ε₀)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (w6S0 / 2))
    (hB : H.w6TorusBk ε₀ θ ξ ∈ birkBall1 m 1) :
    birkEmbed 1 1 (1 - 1) (by norm_num)
        (fderiv ℂ (fun θ' => H.w6TorusBk ε₀ θ' ξ) θ (aaOfReal (H.w6NuStar ε₀ ξ))) =
      birkXLam m hm (H.w6TorusBk ε₀ θ ξ) + birkEmbed 1 (1 + 1) (1 - 1) (by norm_num)
        (birkHamBarX m hm (zero_le_one' ℝ) w6_half_le_one (H.w6TorusBk ε₀ θ ξ) +
          birkHamNorX m hm (zero_le_one' ℝ) w6_half_le_one (H.w6TorusBk ε₀ θ ξ) +
          birkXK m hm (zero_le_one' ℝ) w6_half_le_one ⟨H.w6TorusBk ε₀ θ ξ, hB⟩) := by
  obtain ⟨hi, -, -, hinv⟩ := H.w6ToriKam hlo hhi
  have hT := w6_strip_half_subset (w6WaveSeq m hm α r ε ε₀) rfl
  have hθT := hT hθ
  set w := H.w6TorusKam ε₀ θ ξ with hwdef
  have hpos : ∀ i, 0 < (aaOfReal ξ i + w.2.1 i).re := fun i =>
    lt_of_le_of_lt (sq_nonneg r) ((H.w6TorusKam_aaDom hlo hhi ht hPi hρ₁ hθT hξ).1 i)
  have hξ' := H.mem_of_mem_wavePiStar hξ
  have hΩ0 := homOmega_le H.prepStepHyp.freq hξ'
  have hk := hinv ξ hξ θ hθ hΩ0
  have hconj := aaConjugacy (m := m) (hm := hm) (zero_le_one' ℝ) w6_half_le_one (aaOfReal ξ)
    hpos hB
  have hX' : H.prepStepHyp.hyp.X' ξ w = stepRhoK 1 1 (3 / 2) (by norm_num)
      (aaXP m hm (zero_le_one' ℝ) w6_half_le_one (aaOfReal ξ) w) := rfl
  have hF : aaXN m hm (aaOfReal ξ) w + kamHomEmbed 1 (1 - 1) (1 + 1) (by norm_num)
      (aaXP m hm (zero_le_one' ℝ) w6_half_le_one (aaOfReal ξ) w) =
      w6Field hΩ0 (waveFreqTan m hm ξ) (H.prepStepHyp.hyp.X' ξ) w := by
    unfold w6Field
    rw [aaXN_ofReal_eq_stepXN ξ hΩ0, hX', kamHomEmbed_stepRhoK]
  have hdΨ : HasFDerivAt (fun θ' => H.w6TorusKam ε₀ θ' ξ)
      (fderiv ℂ (fun θ' => H.w6TorusKam ε₀ θ' ξ) θ) θ :=
    ((hi ξ hξ).1.differentiableAt ((isOpen_complexStrip 2 _).mem_nhds hθT)).hasFDerivAt
  have hc : HasFDerivAt (fun θ' => H.w6TorusBk ε₀ θ' ξ)
      ((aaDer 1 1 (aaOfReal ξ) w).comp (fderiv ℂ (fun θ' => H.w6TorusKam ε₀ θ' ξ) θ)) θ :=
    (hasFDerivAt_aaMap 1 1 hpos).comp θ hdΨ
  have step1 : birkEmbed 1 1 (1 - 1) (by norm_num)
      (fderiv ℂ (fun θ' => H.w6TorusBk ε₀ θ' ξ) θ (aaOfReal (H.w6NuStar ε₀ ξ))) =
      aaDer 1 (1 - 1) (aaOfReal ξ) w (w6Field hΩ0 (waveFreqTan m hm ξ) (H.prepStepHyp.hyp.X' ξ) w)
      := by
    rw [hc.fderiv, ContinuousLinearMap.comp_apply, birkEmbed_aaDer, hk]
    rfl
  rw [step1, ← hF]
  exact hconj.symm

/-- **Real analyticity** (`bpW:w6:tori` (v), step `t-an`): with W3's map `Γ = Γ_1`
(`birkGamma … 1`), `θ ↦ 𝒵⁻¹ Γ(Ψ̃_ξ(θ))` restricted to `ℝ²` is real analytic into `WaveSpace`
(`E_{1,1}` in weighted coordinates). -/
theorem w6TorusBk_analytic (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ H.wavePiStar ε₀) :
    AnalyticOnNhd ℝ (fun θ : Fin 2 → ℝ => reWave (birkZinv (birkGamma m hm (zero_le_one' ℝ)
      w6_half_le_one 1 (H.w6TorusBk ε₀ (KAM.realInclusion 2 θ) ξ)))) univ := by
  obtain ⟨hd, hB, hper, hreal, -⟩ := H.w6TorusBk_hol hlo hhi ht hPi hρ₁ hξ
  have hs : 0 < w6S0 / 2 := by rw [w6S0_val]; norm_num
  have hGd : ∀ w ∈ birkBall1 m 1,
      DifferentiableAt ℂ (birkGamma m hm (zero_le_one' ℝ) w6_half_le_one 1) w := fun w hw => by
    have hw0 : 40 * birkCF m 1 * ‖w‖ ^ 2 < 1 := birkBall1_subset_birkBall0 m hm w6_half_le_one hw
    have h := birkGamma_hasFDerivAt (m := m) (hm := hm) (ha := zero_le_one' ℝ)
      (hp := w6_half_le_one) 1 w (by norm_num) hw0
    exact (differentiableAt_iff_restrictScalars ℝ h.differentiableAt).2 ⟨_, h.fderiv.symm⟩
  have hK : DifferentiableOn ℂ (fun θ => birkZinv (birkGamma m hm (zero_le_one' ℝ)
      w6_half_le_one 1 (H.w6TorusBk ε₀ θ ξ))) (complexStrip 2 (w6S0 / 2)) := fun θ hθ => by
    have h1 := hd.differentiableAt ((isOpen_complexStrip 2 _).mem_nhds hθ)
    exact (birkZinv.differentiableAt.comp θ ((hGd _ (hB θ hθ)).comp θ h1)).differentiableWithinAt
  have hrealK : ∀ θ : Fin 2 → ℝ, ∃ x : WaveSpace, birkZinv (birkGamma m hm (zero_le_one' ℝ)
      w6_half_le_one 1 (H.w6TorusBk ε₀ (KAM.realInclusion 2 θ) ξ)) = complexifyWave x :=
      fun θ => by
    have e : KAM.realInclusion 2 θ = aaOfReal θ := rfl
    rw [e]
    have hy := birkGamma_one_fixed (m := m) (hm := hm) (ha := zero_le_one' ℝ)
      (hp := w6_half_le_one) _ (hreal θ) (hB _ (w6_real_mem_strip_half θ))
    obtain ⟨x, hx⟩ := exists_birkZ_of_birkRho_eq _ hy
    refine ⟨x, ?_⟩
    rw [← hx, birkZinv_birkZ]
    rfl
  have hper1 : ∀ i : Fin 2, ∀ n : ℤ, ∀ z ∈ complexStrip 2 (w6S0 / 2),
      z + n • _root_.Pi.single i (1 : ℂ) ∈ complexStrip 2 (w6S0 / 2) ∧
        H.w6TorusBk ε₀ (z + n • _root_.Pi.single i (1 : ℂ)) ξ = H.w6TorusBk ε₀ z ξ := fun i =>
    w6_periodic_zsmul (f := fun θ => H.w6TorusBk ε₀ θ ξ)
      (fun z hz => w6_strip_sub_single hz i) (fun z hz => hper z hz i)
  have hperK : ∀ z ∈ complexStrip 2 (w6S0 / 2), ∀ k : Fin 2 → ℤ,
      birkZinv (birkGamma m hm (zero_le_one' ℝ) w6_half_le_one 1
        (H.w6TorusBk ε₀ (z + fun i => (k i : ℂ)) ξ)) =
      birkZinv (birkGamma m hm (zero_le_one' ℝ) w6_half_le_one 1 (H.w6TorusBk ε₀ z ξ)) := by
    intro z hz k
    have hk : (fun i => (k i : ℂ)) =
        k 0 • _root_.Pi.single 0 (1 : ℂ) + k 1 • _root_.Pi.single 1 (1 : ℂ) := by
      ext i; fin_cases i <;> simp
    obtain ⟨m0, e0⟩ := hper1 0 (k 0) z hz
    rw [hk, ← add_assoc, (hper1 1 (k 1) _ m0).2, e0]
  exact (torus_analytic hs hK hrealK hperK).1

/-- **Invariant tori in Birkhoff coordinates** (blueprint `bpW:w6:tori`). For the wave iteration
(Definition `bpW:w6:wave-iteration`, starting size `ε₀ ∈ [ε^♭_0, γ₁ α̌]`) with
`H_in = N_ξ + P_ξ` of `bpW:w5:action-angle` (iv) on `D(s, r)` (`H : W6PrepHyp … (w6InP m hm)
(w6InX m hm)`, e.g. from `bpW:w5:initial` via `w6PrepHyp_initial`), `|ξ|_∞ ≤ t`, `ξ_i ≥ 2r²` on `Π`
and `c_A(t + r²) < ρ₁²`, let `Ψ̃_ξ(θ) = 𝒜_ξ(Φ_P(Φ_*(θ)))` (`w6TorusBk`), `ν_* = ω_*/(2π)`
(`w6NuStar`), `ξ ∈ Π_* = wavePiStar`:
* (i) `Ψ̃_ξ` is holomorphic on `T_{s_0/2}` with values in `B_{ρ₁}`, `1`-periodic, real on real `θ`
  (`ϱ Ψ̃ = Ψ̃`), and its normal part lies in `𝔚^{p+1/2}`;
* (ii) `(ξ, θ) ↦ Ψ̃_ξ(θ)` is continuous on `Π_* × ℝ²`, and `ν_*` is Lipschitz on `Π_*`;
* (iii) for `θ ∈ ℝ²`: `∂_θ Ψ̃_ξ(θ) ν_* = X_{H'}(Ψ̃_ξ(θ))` in `𝔚^{p-1}`,
  `X_{H'} = X_Λ + X_Ḡ + X_{G^{nor}} + X_K`;
* (iv) on `T_{s_0/2}`: `Φ_P(Φ_*(θ)) = (θ + X, y, u, v)` with `|X| ≤ e_tor`, `|y| ≤ r² e_tor`,
  `‖u‖_{a,p+1/2} + ‖v‖_{a,p+1/2} ≤ r e_tor`, `e_tor = M_{F,P} + e_Φ` (`w6Etor`); hence
  `Ψ̃_{±i} = √(ξ_i + y_i) e^{∓2πi(θ_i + X_i)}` and `‖Ψ̃̂‖ ≤ r e_tor`;
* (v) `θ ↦ 𝒵⁻¹ Γ(Ψ̃_ξ(θ))` restricted to `ℝ²` is `AnalyticOnNhd ℝ` into `WaveSpace`. -/
theorem w6Tori (H : W6PrepHyp m hm Pi α r ε (w6InP m hm) (w6InX m hm))
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) :
    -- (i)
    (∀ ξ ∈ H.wavePiStar ε₀,
      DifferentiableOn ℂ (fun θ => H.w6TorusBk ε₀ θ ξ) (complexStrip 2 (w6S0 / 2)) ∧
      (∀ θ ∈ complexStrip 2 (w6S0 / 2), H.w6TorusBk ε₀ θ ξ ∈ birkBall1 m 1) ∧
      (∀ θ ∈ complexStrip 2 (w6S0 / 2), ∀ i : Fin 2,
        H.w6TorusBk ε₀ (θ + _root_.Pi.single i 1) ξ = H.w6TorusBk ε₀ θ ξ) ∧
      (∀ x : Fin 2 → ℝ,
        birkRho (H.w6TorusBk ε₀ (aaOfReal x) ξ) = H.w6TorusBk ε₀ (aaOfReal x) ξ) ∧
      ∀ θ ∈ complexStrip 2 (w6S0 / 2), ∃ y : BirkSpace,
        birkNormalPart (H.w6TorusBk ε₀ θ ξ) = birkEmbed 1 (3 / 2) 1 (by norm_num) y) ∧
    -- (ii)
    ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => H.w6TorusBk ε₀ (aaOfReal q.2) q.1)
      (H.wavePiStar ε₀ ×ˢ univ) ∧
    (∃ K : NNReal, LipschitzOnWith K (H.w6NuStar ε₀) (H.wavePiStar ε₀)) ∧
    -- (iii)
    (∀ ξ ∈ H.wavePiStar ε₀, ∀ θ : Fin 2 → ℝ,
      ∀ hB : H.w6TorusBk ε₀ (aaOfReal θ) ξ ∈ birkBall1 m 1,
      birkEmbed 1 1 (1 - 1) (by norm_num)
          (fderiv ℂ (fun θ' => H.w6TorusBk ε₀ θ' ξ) (aaOfReal θ) (aaOfReal (H.w6NuStar ε₀ ξ))) =
        birkXLam m hm (H.w6TorusBk ε₀ (aaOfReal θ) ξ) + birkEmbed 1 (1 + 1) (1 - 1) (by norm_num)
          (birkHamBarX m hm (zero_le_one' ℝ) w6_half_le_one (H.w6TorusBk ε₀ (aaOfReal θ) ξ) +
            birkHamNorX m hm (zero_le_one' ℝ) w6_half_le_one (H.w6TorusBk ε₀ (aaOfReal θ) ξ) +
            birkXK m hm (zero_le_one' ℝ) w6_half_le_one ⟨H.w6TorusBk ε₀ (aaOfReal θ) ξ, hB⟩)) ∧
    -- (iv)
    (∀ ξ ∈ H.wavePiStar ε₀, ∀ θ ∈ complexStrip 2 (w6S0 / 2),
      ∃ V : KamPhase, H.w6TorusKam ε₀ θ ξ = w6TorusPt θ + w6Iota V ∧
        ‖V.1‖ ≤ w6Etor m hm α r ε ε₀ ∧ ‖V.2.1‖ ≤ r ^ 2 * w6Etor m hm α r ε ε₀ ∧
        ‖V.2.2.1‖ + ‖V.2.2.2‖ ≤ r * w6Etor m hm α r ε ε₀ ∧
        (∀ (b : Bool) (i : Fin 2), birkCoord 1 1 (H.w6TorusBk ε₀ θ ξ) (b, modeIdx i) =
          aaSqrt ((ξ i : ℂ) + V.2.1 i) *
            cexp (-(birkSgn (b, modeIdx i)) * (2 * π * I * (θ i + V.1 i)))) ∧
        ‖birkNormalPart (H.w6TorusBk ε₀ θ ξ)‖ ≤ r * w6Etor m hm α r ε ε₀) ∧
    -- (v)
    ∀ ξ ∈ H.wavePiStar ε₀,
      AnalyticOnNhd ℝ (fun θ : Fin 2 → ℝ => reWave (birkZinv (birkGamma m hm (zero_le_one' ℝ)
        w6_half_le_one 1 (H.w6TorusBk ε₀ (KAM.realInclusion 2 θ) ξ)))) univ :=
  ⟨fun _ hξ => H.w6TorusBk_hol hlo hhi ht hPi hρ₁ hξ, H.w6TorusBk_cont hlo hhi ht hPi hρ₁,
    H.w6NuStar_lipschitz hlo hhi,
    fun _ hξ θ hB => H.w6TorusBk_invariance_strip hlo hhi ht hPi hρ₁ hξ
      (w6_real_mem_strip_half θ) hB,
    fun _ hξ _ hθ => H.w6TorusBk_close hlo hhi hξ hθ,
    fun _ hξ => H.w6TorusBk_analytic hlo hhi ht hPi hρ₁ hξ⟩

end W6PrepHyp

end KAM.Wave
