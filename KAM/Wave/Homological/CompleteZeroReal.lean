/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.PPlusOne
import Mathlib.Tactic.Linarith

/-!
# Lemma 1 (i) from the source premises: zero modes and reality (`bpW:w4:lemma1` (i))

Blueprint label: `bpW:w4:lemma1` (i), steps `stepW:w4:class` and `stepW:w4:real`.

The landed W4 modules prove the vanishing coefficients (`homLemma1_zero_modes_gen`) and the
reality of `F` (`homSolveTaylor_isReal_gen`) for the solve under the intermediate gate
`HomMultBounds`. Here the gate is supplied by `homMultBounds_of` from the source premises of
Theorem `bpW:w4:lemma1` (the frequency hypotheses `HomFreqHyp`, the Melnikov conditions
`HomMelnikov`, `α > 0`, `ξ ∈ Π`), so the statements are unconditional:

* `homLemma1Complete_zero_modes_gen`: `F(·,ξ) ∈ 𝒯_{s-σ}` (its type) with `â_{F,0} = 0`,
  `\hat b_{F,0} = 0` and `(Q̂_{F,0})_{jj} = 0` (true matrix entries `homNormalEntry_gen`);
* `homLemma1Complete_real_gen`: if `R` is real, so are `F` and `N̂`, and `\hat ω = [b] ∈ ℝ²`,
  `\hat Ω_j = ([Q])_{jj} ∈ ℝ`;
* `homLemma1Complete_zero_modes`, `homLemma1Complete_real`: the same at `p_+ = p + 1` (the
  original W4 setting).
-/

public section

namespace KAM.Wave

open KAM

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ a p pb s σ τ α : ℝ}

/-- The true matrix entry vanishes when the weighted (representative) entry does. -/
theorem homNormalEntry_gen_eq_zero_of_kamEntry {A : HomOp} {i j : ℕ+} (h : kamEntry A i j = 0) :
    homNormalEntry_gen a p pb A i j = 0 := by
  unfold homNormalEntry_gen
  rw [h, mul_zero]

/-- **Lemma 1 (i), zero modes, from the source premises** (blueprint `bpW:w4:lemma1` (i), step
`stepW:w4:class`; general `p_+`): for every `ξ ∈ Π` the solution
`F(·,ξ) = homSolveTaylor_gen … R ∈ 𝒯_{s-σ}` has `â_{F,0} = 0`, `\hat b_{F,0} = 0` and
`(Q̂_{F,0})_{jj} = 0` for all `j`. -/
theorem homLemma1Complete_zero_modes_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s) :
    homCoeff (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).a0 0 = 0 ∧
      homCoeff (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).b 0 = 0 ∧
      ∀ j : ℕ+, homNormalEntry_gen a p pb
        (homCoeff (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).Q 0) j j =
          0 := by
  obtain ⟨h1, h2, h3⟩ :=
    homLemma1_zero_modes_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R
  exact ⟨h1, h2, fun j => homNormalEntry_gen_eq_zero_of_kamEntry (h3 j)⟩

/-- `\hat ω ∈ ℝ²` and `\hat Ω_j ∈ ℝ` when `N̂` is real. -/
theorem homNhat_coeffs_real_of_isReal (R : HomTaylor_gen a p pb s)
    (hN : (homNhatTaylor_gen R).isRealTaylor) :
    (∀ k : Fin 2, (homCoeff R.b 0 k).im = 0) ∧
      ∀ j : ℕ+, (homNormalEntry_gen a p pb (homCoeff R.Q 0) j j).im = 0 := by
  obtain ⟨-, hb, -, -, hq⟩ := hN 0
  refine ⟨fun k => by simpa [homNhatTaylor_gen] using hb k, fun j => ?_⟩
  have e : homNormalEntry_gen a p pb (kamEntryDiagCLM (homCoeff R.Q 0)) j j =
      homNormalEntry_gen a p pb (homCoeff R.Q 0) j j := by
    simp [homNormalEntry_gen, kamEntry_diagCLM]
  have hj := hq j j
  simp only [homNhatTaylor_gen, e] at hj
  exact (Complex.conj_eq_iff_im).mp hj.symm

/-- **Lemma 1 (i), reality, from the source premises** (blueprint `bpW:w4:lemma1` (i), step
`stepW:w4:real`; general `p_+`): if `R` is real, then `F(·,ξ)` and `N̂` are real, and
`\hat ω = [b] ∈ ℝ²`, `\hat Ω_j = ([Q])_{jj} ∈ ℝ`. -/
theorem homLemma1Complete_real_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s) (hR : R.isRealTaylor) :
    (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).isRealTaylor ∧
      (homNhatTaylor_gen R).isRealTaylor ∧
      (∀ k : Fin 2, (homCoeff R.b 0 k).im = 0) ∧
      ∀ j : ℕ+, (homNormalEntry_gen a p pb (homCoeff R.Q 0) j j).im = 0 := by
  have hN := homNhatTaylor_isReal_gen (hσ.trans hσs) R hR
  exact ⟨homSolveTaylor_isReal_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R hR, hN,
    homNhat_coeffs_real_of_isReal R hN⟩

/-- **Lemma 1 (i), zero modes, from the source premises, `p_+ = p + 1`** (blueprint
`bpW:w4:lemma1` (i), step `stepW:w4:class`). -/
theorem homLemma1Complete_zero_modes (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor a p s) :
    homCoeff (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).a0 0 = 0 ∧
      homCoeff (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).b 0 = 0 ∧
      ∀ j : ℕ+, homNormalEntry a p
        (homCoeff (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).Q 0) j j = 0 :=
  homLemma1Complete_zero_modes_gen h hH hτ hα hσ hσs hξ R

/-- **Lemma 1 (i), reality, from the source premises, `p_+ = p + 1`** (blueprint
`bpW:w4:lemma1` (i), step `stepW:w4:real`). -/
theorem homLemma1Complete_real (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor a p s) (hR : R.isRealTaylor) :
    (homSolveTaylor hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R).isRealTaylor ∧
      (homNhatTaylor R).isRealTaylor ∧
      (∀ k : Fin 2, (homCoeff R.b 0 k).im = 0) ∧
      ∀ j : ℕ+, (homNormalEntry a p (homCoeff R.Q 0) j j).im = 0 :=
  homLemma1Complete_real_gen h hH hτ hα hσ hσs hξ R hR

end KAM.Wave
