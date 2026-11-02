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
# W4 at `p_+ = p + 1`: the original names (`bpW:w4:lemma1`, `bpW:w4:lie`)

The W4 modules are parametrized by the smoothing exponent `p_+ = pb` (blueprint
    `bpW:w5:w4-general`);
every declaration whose statement mentions `p_+` carries the suffix `_gen` (`HomTaylor_gen a p pb
    s`,
`homLemma1_fieldBound_gen`, …) and takes `hpb : p ≤ pb`. This module gives the original names back
their original meaning (`p_+ = p + 1`): definitions are `abbrev`s at `pb := p + 1`, theorems are
one-line corollaries of the `_gen` versions with the original statements.

The frequency hypothesis `HomFreqHyp` is the general one (`j^{1/2}` tail, `bpW:w5:freq`); the
    original
(tail weight `j`) is `HomFreqHyp1`, with `HomFreqHyp1.toHyp`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p s σ τ α M d K0 : ℝ} {w w₁ w₂ : Fin 2 → ℝ} {W W₁ W₂ : ℕ+ → ℝ}

theorem homPlusOne_le (p : ℝ) : p ≤ p + 1 := by linarith

theorem homPlusOne_pp {p : ℝ} (hp : 0 ≤ p) : 0 ≤ p + (p + 1) := by linarith

/-- The class `𝒯_s` (original `bpW:w4:taylor`, `p_+ = p + 1`). -/
abbrev HomTaylor (a p s : ℝ) : Type := HomTaylor_gen a p (p + 1) s

/-- The matrix entry `M_ij` (original `p_+ = p+1`). -/
abbrev homNormalEntry (a p : ℝ) (A : HomOp) (i j : ℕ+) : ℂ := homNormalEntry_gen a p (p + 1) A i j

abbrev homNormEntryCLM (a p : ℝ) (i j : ℕ+) : HomOp →L[ℂ] ℂ := homNormEntryCLM_gen a p (p + 1) i j

abbrev homLamD (a p : ℝ) (j : ℕ+) : ℂ := homLamD_gen a p (p + 1) j

abbrev homLamDiag {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) : HomOp :=
  homLamDiag_gen ha (homPlusOne_pp hp)

abbrev homLamCLM {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) : HomOp →L[ℂ] HomOp :=
  homLamCLM_gen ha (homPlusOne_pp hp)

abbrev homPairRep {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c z : HomL2) : ℂ :=
  homPairRep_gen ha (homPlusOne_pp hp) c z

abbrev homDualNorm {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c : HomL2) : ℝ :=
  homDualNorm_gen ha (homPlusOne_pp hp) c

abbrev homRy (T : HomTaylor a p s) (θ : Fin 2 → ℂ) : Fin 2 → ℂ := homRy_gen T θ

abbrev homRz (T : HomTaylor a p s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 := homRz_gen T θ z zb

abbrev homRzb (T : HomTaylor a p s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 := homRzb_gen T θ z zb

abbrev homRu (T : HomTaylor a p s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 := homRu_gen T θ z zb

abbrev homRv (T : HomTaylor a p s) (θ : Fin 2 → ℂ) (z zb : HomL2) : HomL2 := homRv_gen T θ z zb

abbrev homRtheta {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (T : HomTaylor a p s) (i : Fin 2)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homRtheta_gen ha hp (homPlusOne_le p) T i θ y z zb

abbrev homXnorm {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (r : ℝ) (T : HomTaylor a p s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℝ :=
  homXnorm_gen ha hp (homPlusOne_le p) r T θ y z zb

abbrev HomFieldBound {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (r ε : ℝ) (T : HomTaylor a p s) : Prop :=
  HomFieldBound_gen ha hp (homPlusOne_le p) r ε T

abbrev HomTaylor.homSub (R₁ R₂ : HomTaylor a p s) : HomTaylor a p s := HomTaylor_gen.homSub R₁ R₂

abbrev HomTaylor.isRealTaylor (R : HomTaylor a p s) : Prop := HomTaylor_gen.isRealTaylor R

abbrev homRval {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (T : HomTaylor a p s) (θ y : Fin 2 → ℂ)
    (z zb : HomL2) : ℂ :=
  homRval_gen ha hp (homPlusOne_le p) T θ y z zb

abbrev homLieNRaw {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (w : Fin 2 → ℝ) (W : ℕ+ → ℝ)
    (T : HomTaylor a p s) (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homLieNRaw_gen ha hp (homPlusOne_le p) w W T θ y z zb

abbrev homNhat {a p s : ℝ} (R : HomTaylor a p s) (y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homNhat_gen R y z zb

abbrev homPairOmegaRaw {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (W : ℕ+ → ℝ) (c z : HomL2) : ℂ :=
  homPairOmegaRaw_gen ha hp (homPlusOne_le p) W c z

abbrev homSent {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (M : HomOp) (i j : ℕ+) : ℂ :=
  homSent_gen ha hp (homPlusOne_le p) M i j

abbrev homSolveTaylor {a p s σ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) : HomTaylor a p (s - σ) :=
  homSolveTaylor_gen hτ hα hσ hσs hm R

abbrev homNhatTaylor (R : HomTaylor a p s) : HomTaylor a p s := homNhatTaylor_gen R

abbrev homEmbed {a p : ℝ} : HomOp := homEmbed_gen a p (p + 1) (homPlusOne_le p)

abbrev HomCompBounds {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (r K E0 : ℝ) (T : HomTaylor a p s)
    (θ : Fin 2 → ℂ) : Prop :=
  HomCompBounds_gen ha hp (homPlusOne_le p) r K E0 T θ

theorem homComp_angle {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (T : HomTaylor a p s) (hX : HomFieldBound ha hp r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) :
    ‖homPartial i T.a0 θ‖ ≤ 2 * Real.pi * r ^ 2 * ε ∧
      ∑ k, ‖homPartial i T.b θ k‖ ≤ 2 * Real.pi * ε ∧
      homDualNorm ha hp (homPartial i T.cp θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * ε ∧
      homDualNorm ha hp (homPartial i T.cm θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * ε ∧
      ‖homLamCLM ha hp (homPartial i T.P θ)‖ ≤ 4 * Real.pi * ε ∧
      ‖homLamCLM ha hp (homPartial i T.P' θ)‖ ≤ 4 * Real.pi * ε ∧
      ‖homLamCLM ha hp (homPartial i T.Q θ)‖ ≤ 16 * Real.pi * ε := by
  apply homComp_angle_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

theorem homComp_first {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (T : HomTaylor a p s) (hX : HomFieldBound ha hp r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) :
    ‖T.b θ‖ ≤ 2 * Real.pi * ε ∧ ‖T.cp θ‖ ≤ r * ε / Real.sqrt 2 ∧ ‖T.cm θ‖ ≤ r * ε / Real.sqrt 2 ∧
      ‖(2 : ℂ) • T.P θ‖ ≤ ε ∧ ‖T.Q θ‖ ≤ ε ∧ ‖T.Qt θ‖ ≤ ε ∧ ‖(2 : ℂ) • T.P' θ‖ ≤ ε := by
  apply homComp_first_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

/-- Hypothesis-taking variant (assumes the gates `HomMultBounds`, `HomMultLip`); the source-premise
export is `homLemma1_lipschitz`. -/
theorem homLemma1_lipschitz_of_gates (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤
  τ)
    (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor a p s)
    (hX₁ : HomFieldBound ha hp r ε R₁) (hX₂ : HomFieldBound ha hp r ε R₂)
    (hXL : HomFieldBound ha hp r (εL * d) (R₁.homSub R₂)) :
    HomFieldBound ha hp r ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d))
      ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).homSub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)) := by
  apply homLemma1_lipschitz_of_gates_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

theorem homNhat_lipschitz (ha : 0 ≤ a) (hp : 0 ≤ p) {r εL : ℝ} (hr : 0 < r) (hs : 0 < s)
    (R₁ R₂ : HomTaylor a p s) (hXL : HomFieldBound ha hp r (εL * d) (R₁.homSub R₂)) :
    HomFieldBound ha hp r (2 * (εL * d)) ((homNhatTaylor R₁).homSub (homNhatTaylor R₂)) := by
  apply homNhat_lipschitz_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem norm_homLamD_mul_le {a p K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (j : ℕ+) :
    ‖homLamD a p j * (Ω j : ℂ)‖ ≤ K0 := by
  apply norm_homLamD_mul_le_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

/-- Hypothesis-taking variant (assumes the gate `HomMultBounds`); the source-premise export is
`homLemma1_equation_all`. -/
theorem homLemma1_equation_all_of_gates (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2)) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp (homPlusOne_le p)
        (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith) hK0 hΩ) w
        (homSolveTaylor hτ hα hσ hσs hm R) θ y z zb + homNhat R y z zb =
      homRval ha hp R θ y z zb - homCoeff R.a0 0 :=
  homLemma1_equation_all_of_gates_gen ha hp (homPlusOne_le p) (by linarith) hr hτ hα hσ hσs hm
    hK0 hΩ R hX hθ y z zb

section source

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ : ℝ}

/-- **Lemma 1 (ii), all `(z, \bar z)`, `p_+ = p+1`** from the source premises. -/
theorem homLemma1_equation_all (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ)
    (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp (homPlusOne_le p)
        (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
          (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb
      + homNhat R y z zb = homRval ha hp R θ y z zb - homCoeff R.a0 0 :=
  homLemma1_equation_all_gen h hH ha hp (homPlusOne_le p) (by linarith) hr hτ hα hσ hσs hξ R hX
    hθ y z zb

/-- **Lemma 1 (iii), uniform bound, `p_+ = p+1`** from the source premises. -/
theorem homLemma1_fieldBound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ)
    (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) :
    HomFieldBound ha hp r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) :=
  homLemma1_fieldBound_gen h hH ha hp (homPlusOne_le p) hr hτ hα hσ hσs hξ R hX

/-- **Lemma 1 (iii), Lipschitz bound, `p_+ = p+1`** from the source premises. -/
theorem homLemma1_lipschitz (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par)
    (R₁ R₂ : HomTaylor a p s) (hX₁ : HomFieldBound ha hp r ε R₁)
    (hX₂ : HomFieldBound ha hp r ε R₂)
    (hXL : HomFieldBound ha hp r (εL * ‖ξ - ζ‖) (R₁.homSub R₂)) :
    HomFieldBound ha hp r
      ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α) * ‖ξ - ζ‖))
      ((homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R₁).homSub
        (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hζ) R₂)) :=
  homLemma1_lipschitz_gen h hH ha hp (homPlusOne_le p) hr hτ hα hεL hσ hσs hξ hζ R₁ R₂ hX₁ hX₂
    hXL

end source

theorem homXnorm_le_of_components {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r K E0 : ℝ}
    (hr : 0 < r) (hK : 1 ≤ K) (hE0 : 0 ≤ E0) (T : HomTaylor a p s) {θ y : Fin 2 → ℂ}
    {z zb : HomL2} (hb : HomCompBounds ha hp r K E0 T θ) (hy : ‖y‖ ≤ r ^ 2)
    (hdom : ‖homU z zb‖ + ‖homV z zb‖ < r) :
    homXnorm ha hp r T θ y z zb ≤ (7 + 10 * K) * E0 := by
  apply homXnorm_le_of_components_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

theorem homF_compBounds {a p s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    HomCompBounds ha hp r homKS (waveBW τ σ * ε / α) (homSolveTaylor hτ hα hσ hσs hm R) θ := by
  apply homF_compBounds_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

/-- Hypothesis-taking variant (assumes the gate `HomMultBounds`); the source-premise export is
`homLemma1_fieldBound`. -/
theorem homLemma1_fieldBound_of_gates {a p s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a)
    (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R) :
    HomFieldBound ha hp r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homSolveTaylor hτ hα hσ hσs hm R) := by
  apply homLemma1_fieldBound_of_gates_gen (pb := p + 1) <;>
    first | assumption | exact homPlusOne_le p | linarith

theorem homLam_comm_homTQ {a p τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    (homLamCLM ha hp).comp (homTQ hm k) = (homTQ hm k).comp (homLamCLM ha hp) := by
  apply homLam_comm_homTQ_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homNhatTaylor_val {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (R : HomTaylor a p s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval ha hp (homNhatTaylor R) θ y z zb = homNhat R y z zb := by
  apply homNhatTaylor_val_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homNhat_fieldBound {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hs : 0 < s) (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R) :
    HomFieldBound ha hp r (2 * ε) (homNhatTaylor R) := by
  apply homNhat_fieldBound_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homLemma1_zero_modes {a p s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) :
    homCoeff (homSolveTaylor hτ hα hσ hσs hm R).a0 0 = 0 ∧
      homCoeff (homSolveTaylor hτ hα hσ hσs hm R).b 0 = 0 ∧
      ∀ j : ℕ+, kamEntry (homCoeff (homSolveTaylor hτ hα hσ hσs hm R).Q 0) j j = 0 := by
  apply homLemma1_zero_modes_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem norm_homLamCLM_apply_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (A : HomOp) :
    ‖homLamCLM ha hp A‖ ≤ ‖A‖ := by
  apply norm_homLamCLM_apply_le_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homHadamardOp_lam {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {d : ℕ+ → ℕ+ → ℂ} {c : ℝ}
    (h : HomHadamardBound d c) (A : HomOp) :
    homHadamardOp h (homLamCLM ha hp A) = homLamCLM ha hp (homHadamardOp h A) := by
  apply homHadamardOp_lam_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem norm_homLam_hadamard_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {d : ℕ+ → ℕ+ → ℂ} {c : ℝ}
    (h : HomHadamardBound d c) (A : HomOp) :
    ‖homLamCLM ha hp (homHadamardOp h A)‖ ≤ c * homKS * ‖homLamCLM ha hp A‖ := by
  apply norm_homLam_hadamard_le_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homSolveTaylor_isReal (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) (hR : R.isRealTaylor) :
    (homSolveTaylor hτ hα hσ hσs hm R).isRealTaylor := by
  apply homSolveTaylor_isReal_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

theorem homNhatTaylor_isReal (hs : 0 < s) (R : HomTaylor a p s) (hR : R.isRealTaylor) :
    (homNhatTaylor R).isRealTaylor := by
  apply homNhatTaylor_isReal_gen (pb := p + 1) <;> first | assumption | exact homPlusOne_le p |
      linarith

/-- The finitely supported homological equation (`bpW:w4:lemma1` (ii)), `p_+ = p+1`. -/
theorem homLemma1_equation {r ε : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2} (hz : ∀ j ∉ S, z j = 0)
    (hzb : ∀ j ∉ S, zb j = 0) :
    homLieNRaw ha hp w W (homSolveTaylor hτ hα hσ hσs hm R) θ y z zb + homNhat R y z zb =
      homRval ha hp R θ y z zb - homCoeff R.a0 0 :=
  homLemma1_equation_gen ha hp (homPlusOne_le p) hr hτ hα hσ hσs hm R hX hθ y hz hzb

theorem homEq_Q {r ε : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent ha hp (homPartial l
        (homSolveTaylor hτ hα hσ hσs hm R).Q θ) i j)
      - Complex.I * ((W j - W i : ℝ) : ℂ) * homSent ha hp
        ((homSolveTaylor hτ hα hσ hσs hm R).Q θ) i j =
      homSent ha hp (R.Q θ) i j -
        (if i = j then homSent ha hp (homCoeff R.Q 0) i j else 0) :=
  homEq_Q_gen ha hp (homPlusOne_le p) hr hτ hα hσ hσs hm R hX hθ i j

theorem homLipField_dQ {r ε εL : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor a p s)
    (hX₁ : HomFieldBound ha hp r ε R₁) (hX₂ : HomFieldBound ha hp r ε R₂)
    (hXL : HomFieldBound ha hp r (εL * d) (R₁.homSub R₂)) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (i : Fin 2) :
    ‖homLamCLM ha hp (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).homSub
        (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).Q θ)‖ ≤
      homKS * (16 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d)) :=
  homLipField_dQ_gen ha hp (homPlusOne_le p) hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂
    hXL hθ i

theorem homF_sub_compBounds {r ε εL : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hM : 0 ≤ M) (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
    (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor a p s)
    (hX₁ : HomFieldBound ha hp r ε R₁) (hX₂ : HomFieldBound ha hp r ε R₂)
    (hXL : HomFieldBound ha hp r (εL * d) (R₁.homSub R₂)) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    HomCompBounds ha hp r homKS (waveBW τ σ / α * (εL + 2 * M * ε / α) * d)
      ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).homSub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)) θ :=
  homF_sub_compBounds_gen ha hp (homPlusOne_le p) hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁
    hX₂ hXL hθ

theorem homLemma_lie_iv {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (T : HomTaylor a p s) (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homDN hG hK0 hΩ ω (θ, y, z, zb)
        ((0 : Fin 2 → ℂ), (fun i => -(2 * Real.pi : ℂ)⁻¹ * homRtheta ha hp T i θ y z zb),
          (-Complex.I) • homEmbed (a := a) (p := p) (homRzb T θ z zb),
          Complex.I • homEmbed (a := a) (p := p) (homRz T θ z zb)) =
      -homLieNRaw ha hp ω Ω T θ y z zb :=
  homLemma_lie_iv_gen hG hK0 hΩ ω ha hp (homPlusOne_le p) T θ y z zb

theorem homDiagonal_bound (a p : ℝ) (A : HomOp) (i : ℕ+) :
    ((i : ℝ) + 2) * ‖homNormalEntry a p A i i‖ ≤ ‖A‖ := by
  simpa using homDiagonal_bound_gen a p (p + 1) A i

theorem homNhat_coeff_bounds {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r)
    (hs : 0 < s) (R : HomTaylor a p s) (hX : HomFieldBound ha hp r ε R) :
    ‖homCoeff R.b 0‖ ≤ 2 * Real.pi * ε ∧ ‖homCoeff R.Q 0‖ ≤ ε ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) * ‖homNormalEntry a p (homCoeff R.Q 0) j j‖ ≤ ε := by
  obtain ⟨h1, h2, h3⟩ := homNhat_coeff_bounds_gen ha hp (homPlusOne_le p) hr hs R hX
  exact ⟨h1, h2, fun j => by simpa using h3 j⟩

theorem homLie_pairing_summable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {F z : ℕ+ → ℂ}
    (hF : HomNormal a (p + 1) F) (hz : HomNormal a p z) :
    Summable (fun j => ‖F j * ((Ω ξ j : ℂ) * z j)‖) ∧
      ‖∑' j, F j * ((Ω ξ j : ℂ) * z j)‖ ≤ (1 + M0) * (homNorm hF * homNorm hz) :=
  homLie_pairing_summable_gen h hξ ha (by linarith) hF hz

end KAM.Wave
