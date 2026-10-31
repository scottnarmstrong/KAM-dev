/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneAll
public import KAM.Wave.Homological.LieDeriv
public import KAM.Wave.Homological.RealF
public import KAM.Wave.Homological.Wave
import Mathlib.Tactic.Linarith

/-!
# W4 at `p_+ = p + 1` (`bpW:w4:lemma1`, `bpW:w4:lie` as originally stated)

The W4 modules are parametrized by the smoothing exponent `p_+ = pb` (blueprint
    `bpW:w5:w4-general`):
`HomTaylor a p pb s`, `homNormalEntry a p pb`, `homLamD a p pb`, `homEmbed a p pb`, with the
    frequency
hypothesis `HomFreqHyp` (tail weight `j^{1/2}`, blueprint `bpW:w5:freq`). This module records the
original statements (`p_+ = p + 1`) as one-line corollaries `<name>_succ`; the original frequency
hypothesis is `HomFreqHyp1` and implies `HomFreqHyp` (`HomFreqHyp1.toHyp`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- The class `𝒯_s` with `p_+ = p + 1` (original W4 definition). -/
abbrev HomTaylorSucc (a p s : ℝ) : Type := HomTaylor a p (p + 1) s

theorem homPlusOne_le (p : ℝ) : p ≤ p + 1 := by linarith

/-- **Lemma 1 (iii)**, `p_+ = p+1`. -/
theorem homLemma1_fieldBound_succ (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylorSucc a p s)
    (hX : HomFieldBound ha hp (homPlusOne_le p) r ε R) :
    HomFieldBound ha hp (homPlusOne_le p) r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homSolveTaylor hτ hα hσ hσs hm R) :=
  homLemma1_fieldBound ha hp (homPlusOne_le p) hr hτ hα hσ hσs hm R hX

/-- **Lemma 1 (ii) for all `(z, \bar z)`**, `p_+ = p+1`. -/
theorem homLemma1_equation_all_succ {K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W)
    (hK0 : 0 ≤ K0) (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2)) (R : HomTaylorSucc a p s)
    (hX : HomFieldBound ha hp (homPlusOne_le p) r ε R) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN ha hp (homPlusOne_le p) w W (homSolveTaylor hτ hα hσ hσs hm R) θ y z zb +
        homNhat R y z zb =
      homRval ha hp (homPlusOne_le p) R θ y z zb - homCoeff R.a0 0 :=
  homLemma1_equation_all ha hp (homPlusOne_le p) (by linarith) hr hτ hα hσ hσs hm hK0 hΩ R hX hθ y
    z zb

/-- **Lemma 1 (iv), coefficients**, `p_+ = p+1`: `(j+2)|Ω̂_j| ≤ ε`. -/
theorem homNhat_coeff_bounds_succ (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (R : HomTaylorSucc a p s) (hX : HomFieldBound ha hp (homPlusOne_le p) r ε R) :
    ‖homCoeff R.b 0‖ ≤ 2 * Real.pi * ε ∧ ‖homCoeff R.Q 0‖ ≤ ε ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) * ‖homNormalEntry a p (p + 1) (homCoeff R.Q 0) j j‖ ≤ ε := by
  obtain ⟨h1, h2, h3⟩ := homNhat_coeff_bounds ha hp (homPlusOne_le p) hr hs R hX
  refine ⟨h1, h2, fun j => ?_⟩
  simpa using h3 j

/-- **Lemma 1 (iv), field of `N̂`**, `p_+ = p+1`. -/
theorem homNhat_fieldBound_succ (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (R : HomTaylorSucc a p s) (hX : HomFieldBound ha hp (homPlusOne_le p) r ε R) :
    HomFieldBound ha hp (homPlusOne_le p) r (2 * ε) (homNhatTaylor R) :=
  homNhat_fieldBound ha hp (homPlusOne_le p) hr hs R hX

/-- **Reality of the solution**, `p_+ = p+1`. -/
theorem homSolveTaylor_isReal_succ (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylorSucc a p s) (hR : R.IsReal) :
    (homSolveTaylor hτ hα hσ hσs hm R).IsReal :=
  homSolveTaylor_isReal hτ hα hσ hσs hm R hR

/-- **Lemma 1 (iii), Lipschitz bound**, `p_+ = p+1`. -/
theorem homLemma1_lipschitz_succ {M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ} (ha : 0 ≤ a)
    (hp : 0 ≤ p) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s) (hm₁ : HomMultBounds τ α w₁ W₁)
    (hm₂ : HomMultBounds τ α w₂ W₂) (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂)
    (R₁ R₂ : HomTaylorSucc a p s) (hX₁ : HomFieldBound ha hp (homPlusOne_le p) r ε R₁)
    (hX₂ : HomFieldBound ha hp (homPlusOne_le p) r ε R₂)
    (hXL : HomFieldBound ha hp (homPlusOne_le p) r (εL * d) (R₁.sub R₂)) :
    HomFieldBound ha hp (homPlusOne_le p) r
      ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d))
      ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)) :=
  homLemma1_lipschitz ha hp (homPlusOne_le p) hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂
    hXL

/-- **Lemma 1 (iv), Lipschitz bound of `N̂`**, `p_+ = p+1`. -/
theorem homNhat_lipschitz_succ {d : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r εL : ℝ} (hr : 0 < r)
    (hs : 0 < s) (R₁ R₂ : HomTaylorSucc a p s)
    (hXL : HomFieldBound ha hp (homPlusOne_le p) r (εL * d) (R₁.sub R₂)) :
    HomFieldBound ha hp (homPlusOne_le p) r (2 * (εL * d))
      ((homNhatTaylor R₁).sub (homNhatTaylor R₂)) :=
  homNhat_lipschitz ha hp (homPlusOne_le p) hr hs R₁ R₂ hXL

/-- **`bpW:w4:lie` (iv)**, `p_+ = p+1`. -/
theorem homLemma_lie_iv_succ {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (T : HomTaylorSucc a p s) (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homDN hG hK0 hΩ ω (θ, y, z, zb)
        ((0 : Fin 2 → ℂ), (fun i => -(2 * Real.pi : ℂ)⁻¹ * homRtheta ha hp (homPlusOne_le p) T i θ
            y z zb),
          (-Complex.I) • homEmbed a p (p + 1) (homPlusOne_le p) (homRzb T θ z zb),
          Complex.I • homEmbed a p (p + 1) (homPlusOne_le p) (homRz T θ z zb)) =
      -homLieN ha hp (homPlusOne_le p) ω Ω T θ y z zb :=
  homLemma_lie_iv hG hK0 hΩ ω ha hp (homPlusOne_le p) T θ y z zb

end KAM.Wave
