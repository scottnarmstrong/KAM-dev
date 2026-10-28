/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepAvg

/-!
# Two-scale KAM step: monotonicity in the base set, and the zero coefficient

The new domain `D₊` is not contained in `D` as a set of real points, only its complex neighbourhood
is contained in a neighbourhood of `D`. These helpers move the class `InClass`, the bound `WBound`
and reality between such neighbourhoods. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {n m : ℕ}

theorem polyNbhd_realBase_subset {D D' : Set (Fin n → ℝ)} {r r' : ℝ}
    (h : KAM.actionNbhd D' r' ⊆ KAM.actionNbhd D r) :
    polyNbhd (realBase D') r' ⊆ polyNbhd (realBase D) r := by
  rw [(conv_data D' r' 0).1, (conv_data D r 0).1]; exact h

theorem dom_mono_set {D D' : Set (Fin m → ℂ)} {r r' s s' : ℝ}
    (hsub : polyNbhd D' r' ⊆ polyNbhd D r) (hs : s' ≤ s) : Dom n D' r' s' ⊆ Dom n D r s :=
  fun z hz => ⟨fun i => by
    have := hz.1 i
    simp only [abs_lt] at this ⊢
    constructor <;> linarith [this.1, this.2], hsub hz.2⟩

theorem coefficientDom_mono {D D' : Set (Fin n → ℝ)} {r r' σ σ' : ℝ}
    (h : KAM.actionNbhd D' r' ⊆ KAM.actionNbhd D r) (hσ : σ' ≤ σ) :
    coefficientDom D' r' σ' ⊆ coefficientDom D r σ :=
  dom_mono_set (polyNbhd_realBase_subset h)
    (by unfold geometricWidth; gcongr)

theorem wbound_mono_set {D D' : Set (Fin m → ℂ)} {r r' s s' M M' : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (h : WBound D r s u M)
    (hsub : polyNbhd D' r' ⊆ polyNbhd D r) (hs : s' ≤ s) (hM : M ≤ M') : WBound D' r' s' u M' := by
  intro I hI
  have := (h.mono (le_refl r) hs hM) I (hsub hI)
  exact this

theorem inClass_mono_set {D D' : Set (Fin m → ℂ)} {r r' s s' : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (h : InClass D r s u)
    (hsub : polyNbhd D' r' ⊆ polyNbhd D r) (hs : s' ≤ s) : InClass D' r' s' u :=
  ⟨h.differentiableOn.mono (dom_mono_set hsub hs), fun j z hz =>
    h.periodic j z (dom_mono_set hsub hs hz)⟩

theorem norm_coeff_zero_le {D : Set (Fin m → ℂ)} {r s M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (h : WBound D r s u M) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) : ‖coeff u I 0‖ ≤ M := by
  obtain ⟨hs, hle⟩ := h I hI
  have h0 : ‖coeff u I 0‖ * modeWeight s 0 ≤ ∑' k, ‖coeff u I k‖ * modeWeight s k :=
    hs.le_tsum 0 fun k _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hw : modeWeight s (0 : Fin n → ℤ) = 1 := by
    simp [modeWeight, KAM.Fourier.modeSize]
  rw [hw, mul_one] at h0
  exact h0.trans hle

end KAM.Planetary

end
