/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.Etor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: frequencies on one shell (blueprint `bpW:w8:freq-shell`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w8:freq-shell` (milestone W8).

For the shell iteration of a prep-step bundle `H : W8ShellPrep m hm n P X` (`bpW:w8:shell-iter`):
* `w8ShellGamma_subset_D`, `w8ShellOmega_tendsto` (Step `stepW:w8:fs-lim`): `Γ_n ⊆ D^{(n)}_μ` for
  every `μ` and `ω^{(n)}_μ → ω^{(n)}_*` on `Γ_n`;
* `w8_freqShell` (`bpW:w8:freq-shell`): (i) `ω^{(n)}_* - ω⁰` is `θ₀`-Lipschitz on `Γ_n`;
  (ii) `|ω^{(n)}_*(ξ) - ω^{(n)}_*(ξ')| ≥ (7/(8L_A)) |ξ - ξ'|`; (iii) `|ω^{(n)}_* - ω⁰| ≤ ε^{(n)}_ω ≤
  α_n/(70 L_A)` and `|⟨k, ω^{(n)}_*⟩| ≥ α̌_n/(2A_k)` for `k ≠ 0`; (iv) `ν^{(n)}_*` is Lipschitz,
  hence continuous, on `Γ_n`, and `Γ_n` is Borel.
Also `w8ShellGamma_subset_Pi`: `Γ_n ⊆ Π_n ∖ Ξ ⊆ Π_n` (construction, `Π_* ⊆ Π_{-1}`).
-/

@[expose] public noncomputable section

open Set Real Filter Topology

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {n : ℕ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

local notation "𝔱" => w8T0W m hm

/-- `Γ_n ⊆ Π_{-1} = Π_n ∖ Ξ` (blueprint `bpW:w8:patch-local`, Step `stepW:w8:pl-dis`). -/
theorem w8ShellGamma_subset (H : W8ShellPrep m hm n P X) :
    w8ShellGamma H ⊆ w8Pi 𝔱 n \ prepSet m hm (w8Pi 𝔱 n) (w8alpha 𝔱 n) := fun _ hξ =>
  w6Pi0_subset (mem_iInter.1 hξ 0)

/-- `Γ_n ⊆ Π_n`. -/
theorem w8ShellGamma_subset_Pi (H : W8ShellPrep m hm n P X) : w8ShellGamma H ⊆ w8Pi 𝔱 n :=
  fun _ hξ => (w8ShellGamma_subset H hξ).1

/-- `Γ_n = ⋂_μ Π_μ ⊆ D^{(n)}_μ = Π_{μ-1}` (Step `stepW:w8:fs-lim`). -/
theorem w8ShellGamma_subset_D (H : W8ShellPrep m hm n P X) (ν : ℕ) :
    w8ShellGamma H ⊆ (w8ShellFamily H).D ν := by
  obtain ⟨-, hlo, hhi⟩ := w8_epsFlat_shell hm n
  have hC := H.w6Applicable hlo hhi
  show _ ⊆ H.waveD (w8Eps0W m hm n) ν
  unfold w8ShellGamma W6PrepHyp.wavePiStar W6PrepHyp.waveD W6PrepHyp.waveSeq
  rw [w6PiStarIt_eq hC]
  exact w6PiStar_subset_seq _ _ _ _ _ ν

/-- `ω^{(n)}_μ → ω^{(n)}_*` on `Γ_n` (Proposition `bpW:w6:convergence` (ii), Step
`stepW:w8:fs-lim`). -/
theorem w8ShellOmega_tendsto (H : W8ShellPrep m hm n P X) :
    ∀ ξ ∈ w8ShellGamma H,
      Tendsto (fun ν => (w8ShellFamily H).ω ν ξ) atTop (𝓝 (w8ShellOmega H ξ)) := by
  obtain ⟨-, hlo, hhi⟩ := w8_epsFlat_shell hm n
  have hC := H.w6Applicable hlo hhi
  exact (w6Seq_om_limit w6StepReal_holds hC).1

/-- `Γ_n` is Borel (Proposition `bpW:w6:convergence` (i), Step `stepW:w8:fs-reg`). -/
theorem w8ShellGamma_measurableSet (H : W8ShellPrep m hm n P X) :
    MeasurableSet (w8ShellGamma H) := by
  obtain ⟨-, hlo, hhi⟩ := w8_epsFlat_shell hm n
  have hC := H.w6Applicable hlo hhi
  exact (w6ConvBorel hC (w6PiMinus_measurableSet m hm (w8MeasSetup hm n))).2

/-- **Frequencies on one shell** (blueprint `bpW:w8:freq-shell`): for `ξ, ξ' ∈ Γ_n`,
* (i) `|(ω^{(n)}_* - ω⁰)(ξ) - (ω^{(n)}_* - ω⁰)(ξ')| ≤ θ₀ |ξ - ξ'|`;
* (ii) `|ω^{(n)}_*(ξ) - ω^{(n)}_*(ξ')| ≥ (7/(8L_A)) |ξ - ξ'|`;
* (iii) `|ω^{(n)}_*(ξ) - ω⁰(ξ)| ≤ ε^{(n)}_ω ≤ α_n/(70 L_A)`, and `|⟨k, ω^{(n)}_*(ξ)⟩| ≥ α̌_n/(2A_k)`
  for `k ∈ ℤ² ∖ 0`;
* (iv) `ν^{(n)}_*` is Lipschitz (hence continuous) on `Γ_n`, and `Γ_n` is Borel. -/
theorem w8_freqShell (H : W8ShellPrep m hm n P X) :
    (∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
      ‖(w8ShellOmega H ξ - omegaTan m hm ξ) - (w8ShellOmega H ξ' - omegaTan m hm ξ')‖ ≤
        measTheta0 m hm * ‖ξ - ξ'‖) ∧
    (∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
      7 / (8 * measLA m hm) * ‖ξ - ξ'‖ ≤ ‖w8ShellOmega H ξ - w8ShellOmega H ξ'‖) ∧
    ((∀ ξ ∈ w8ShellGamma H, ‖w8ShellOmega H ξ - omegaTan m hm ξ‖ ≤ w8ShellEpsOm m hm n) ∧
      w8ShellEpsOm m hm n ≤ w8alpha 𝔱 n / (70 * measLA m hm) ∧
      ∀ ξ ∈ w8ShellGamma H, ∀ k : Fin 2 → ℤ, k ≠ 0 →
        alphaCheck (w8alpha 𝔱 n) / (2 * kAk k) ≤ |∑ i, (k i : ℝ) * w8ShellOmega H ξ i|) ∧
    ((∃ L : ℝ, ∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
        ‖w8ShellNu H ξ - w8ShellNu H ξ'‖ ≤ L * ‖ξ - ξ'‖) ∧
      ContinuousOn (w8ShellNu H) (w8ShellGamma H) ∧ MeasurableSet (w8ShellGamma H)) := by
  obtain ⟨-, ⟨hpair, hθ⟩, -, f1, f2, f3⟩ := w8_w6General H
  have hθ0 := w6Theta_nonneg m hm
  have hlim := w8ShellOmega_tendsto H
  have hD := w8ShellGamma_subset_D H
  -- (i): pass `(H1)` to the limit
  have hi : ∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
      ‖(w8ShellOmega H ξ - omegaTan m hm ξ) - (w8ShellOmega H ξ' - omegaTan m hm ξ')‖ ≤
        measTheta0 m hm * ‖ξ - ξ'‖ := by
    intro ξ hξ ξ' hξ'
    have hL : Tendsto (fun ν => ‖((w8ShellFamily H).ω ν ξ - omegaTan m hm ξ) -
        ((w8ShellFamily H).ω ν ξ' - omegaTan m hm ξ')‖) atTop
        (𝓝 ‖(w8ShellOmega H ξ - omegaTan m hm ξ) - (w8ShellOmega H ξ' - omegaTan m hm ξ')‖) :=
      (((hlim ξ hξ).sub tendsto_const_nhds).sub ((hlim ξ' hξ').sub tendsto_const_nhds)).norm
    have h1 := le_of_tendsto' hL fun ν => (hpair ν).h1_lip ξ (hD ν hξ) ξ' (hD ν hξ')
    exact h1.trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
  -- (ii): the lower bound
  have hL := measLA_pos m hm
  have hθL := measTheta0_le_inv_eight_LA hm
  have hii : ∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
      7 / (8 * measLA m hm) * ‖ξ - ξ'‖ ≤ ‖w8ShellOmega H ξ - w8ShellOmega H ξ'‖ := by
    intro ξ hξ ξ' hξ'
    have h1 := norm_sub_le_measLA_mul m hm ξ ξ'
    have e : omegaTan m hm ξ - omegaTan m hm ξ' = (w8ShellOmega H ξ - w8ShellOmega H ξ') -
        ((w8ShellOmega H ξ - omegaTan m hm ξ) - (w8ShellOmega H ξ' - omegaTan m hm ξ')) := by
      abel
    have h2 : ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤
        ‖w8ShellOmega H ξ - w8ShellOmega H ξ'‖ + measTheta0 m hm * ‖ξ - ξ'‖ := by
      rw [e]; exact (norm_sub_le _ _).trans (add_le_add le_rfl (hi ξ hξ ξ' hξ'))
    have hn := norm_nonneg (ξ - ξ')
    have h3 : measTheta0 m hm * ‖ξ - ξ'‖ ≤ 1 / (8 * measLA m hm) * ‖ξ - ξ'‖ :=
      mul_le_mul_of_nonneg_right hθL hn
    have h4 : ‖ξ - ξ'‖ / measLA m hm ≤ ‖w8ShellOmega H ξ - w8ShellOmega H ξ'‖ +
        1 / (8 * measLA m hm) * ‖ξ - ξ'‖ := by
      rw [div_le_iff₀ hL]; nlinarith
    have e7 : 7 / (8 * measLA m hm) * ‖ξ - ξ'‖ =
        ‖ξ - ξ'‖ / measLA m hm - 1 / (8 * measLA m hm) * ‖ξ - ξ'‖ := by
      field_simp; ring
    rw [e7]; linarith
  -- (iv): Lipschitz `ν`
  have hlip : ∀ ξ ∈ w8ShellGamma H, ∀ ξ' ∈ w8ShellGamma H,
      ‖w8ShellNu H ξ - w8ShellNu H ξ'‖ ≤ (2 * π)⁻¹ * (measNA m hm + w6Theta m hm) * ‖ξ - ξ'‖ := by
    intro ξ hξ ξ' hξ'
    unfold w8ShellNu
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left (f3 ξ hξ ξ' hξ') (by positivity)
  exact ⟨hi, hii, ⟨f2, (w8_etor hm n).2.2.2.1, f1⟩, ⟨⟨_, hlip⟩, w6_continuousOn_of_lip hlip,
    w8ShellGamma_measurableSet H⟩⟩

end KAM.Wave

end
