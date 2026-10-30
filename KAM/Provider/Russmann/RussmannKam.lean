/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.FundamentalDomain
public import KAM.Frozen.Russmann.Defs.RussmannCover
import KAM.Russmann.AssemblyStrong

/-!
# Provider for the frozen theorem `KAM.Russmann.russmann_kam`

The proof of `KAM.Russmann.russmann_kam` is assembled here as
`KAM.Provider.Russmann.russmann_kam`, from graph predecessors and approved external inputs only.
While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.

* `KAM.Provider.Russmann.russmann_kam` has exactly the type of the frozen
  `KAM.Russmann.russmann_kam`. It is `KAM.Russmann.russmann_tori_strong`
  (`KAM/Russmann/AssemblyStrong.lean`), whose conclusion is the frozen one with the frozen cover
  `KAM.Russmann.russmannCover` written out as its defining set-builder (equal by definition).
  This module does not import the frozen theorem.
-/

public section

open MeasureTheory

namespace KAM.Provider.Russmann

open KAM KAM.Russmann

/-- **R-HEAD.** Rüssmann's KAM theorem (Rus01 Thm 1.7, maximal case), strong form: the provider of
the frozen `KAM.Russmann.russmann_kam`, with exactly its type. -/
theorem russmann_kam {n : ℕ} (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_conn : IsConnected B)
    (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ τ : ℝ, (n : ℝ) - 1 < τ ∧ ∀ δ : ℝ, 0 < δ → ∀ κ : ℝ, 0 < κ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        volume (fundamentalDomain B \ russmannCover h f B r₀ τ δ) ≤
          ENNReal.ofReal κ * volume (fundamentalDomain B) :=
  russmann_tori_strong hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real h_russmann

end KAM.Provider.Russmann

end
