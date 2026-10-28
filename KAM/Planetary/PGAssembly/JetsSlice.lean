/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Regularity
public import KAM.Strip.Bridges
public import KAM.Planetary.PGAssembly.JetsPolar
public import KAM.Planetary.PGAssembly.JetsFamily

/-!
# P Part 5: partial jets of a jointly holomorphic function (`bpP:p5:be-an`)

For `F` holomorphic on an open `U ⊆ E₁ × E₂`, the iterated derivative in the second variable at
`(I, x)` is the iterated derivative of `F` composed with `inr` (`iteratedFDeriv_slice`); hence
`I ↦ iteratedFDeriv ℂ k (F (I, ·)) 0 w` is holomorphic (`differentiableOn_slice_jet`), and for a
holomorphic family it is jointly continuous (`continuousOn_slice_jet`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Planetary

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂]

theorem iteratedFDeriv_slice {F : E₁ × E₂ → ℂ} {U : Set (E₁ × E₂)} (hU : IsOpen U) {n : ℕ}
    (hF : ContDiffOn ℂ n F U) {I : E₁} {x : E₂} (hx : (I, x) ∈ U) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℂ i (fun y => F (I, y)) x =
      (iteratedFDeriv ℂ i F (I, x)).compContinuousLinearMap
        fun _ => ContinuousLinearMap.inr ℂ E₁ E₂ := by
  set T : E₁ × E₂ → E₁ × E₂ := fun z => z + (I, 0) with hT
  have hTc : Continuous T := continuous_id.add continuous_const
  have hU' : IsOpen (T ⁻¹' U) := hU.preimage hTc
  have hG : ContDiffOn ℂ n (F ∘ T) (T ⁻¹' U) :=
    hF.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hxU : ContinuousLinearMap.inr ℂ E₁ E₂ x ∈ T ⁻¹' U := by
    simpa [hT] using hx
  have h := iteratedFDeriv_comp_clm_of_isOpen hU' hG (ContinuousLinearMap.inr ℂ E₁ E₂) hxU hi
  have e1 : (fun y => F (I, y)) = (F ∘ T) ∘ ContinuousLinearMap.inr ℂ E₁ E₂ := by
    funext y; simp [hT]
  have e2 : iteratedFDeriv ℂ i (F ∘ T) (ContinuousLinearMap.inr ℂ E₁ E₂ x) =
      iteratedFDeriv ℂ i F (I, x) := by
    have := iteratedFDeriv_comp_add_right (𝕜 := ℂ) (f := F) i (I, (0 : E₂))
      (ContinuousLinearMap.inr ℂ E₁ E₂ x)
    simpa [hT, Function.comp_def] using this
  rw [e1, h, e2]

section FiniteDim

open scoped ContDiff

variable [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂]

theorem differentiableOn_slice_jet {F : E₁ × E₂ → ℂ} {U : Set (E₁ × E₂)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (k : ℕ) (w : Fin k → E₂) :
    DifferentiableOn ℂ (fun I => iteratedFDeriv ℂ k (fun y => F (I, y)) 0 w)
      {I | (I, (0 : E₂)) ∈ U} := by
  have hcd : ContDiffOn ℂ (k : ℕ∞) F U :=
    (KAM.contDiffOn_infty_of_differentiableOn hU hF).of_le (by exact_mod_cast le_top)
  have hD := KAM.differentiableOn_iteratedFDeriv_of_differentiableOn hU hF k
  have hcomp : DifferentiableOn ℂ (fun I : E₁ => iteratedFDeriv ℂ k F (I, (0 : E₂)))
      {I | (I, (0 : E₂)) ∈ U} :=
    hD.comp (differentiable_id.prodMk (differentiable_const _)).differentiableOn
      (fun I hI => hI)
  have happ := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => E₁ × E₂) ℂ
    (fun i => ContinuousLinearMap.inr ℂ E₁ E₂ (w i))).differentiable.comp_differentiableOn hcomp
  refine happ.congr fun I hI => ?_
  rw [iteratedFDeriv_slice hU hcd hI le_rfl]
  rfl

theorem continuousOn_slice_jet {T : Set ℝ} (hT : IsCompact T) {U : Set (E₁ × E₂)}
    (hU : IsOpen U) {F : ℝ → E₁ × E₂ → ℂ} (hd : ∀ μ ∈ T, DifferentiableOn ℂ (F μ) U)
    (hc : ContinuousOn (fun p : ℝ × (E₁ × E₂) => F p.1 p.2) (T ×ˢ U)) (k : ℕ) (w : Fin k → E₂) :
    ContinuousOn (fun p : ℝ × E₁ => iteratedFDeriv ℂ k (fun y => F p.1 (p.2, y)) 0 w)
      (T ×ˢ {I | (I, (0 : E₂)) ∈ U}) := by
  have hfam := continuousOn_iteratedFDeriv_family hT hU k hd hc
    (fun i => ContinuousLinearMap.inr ℂ E₁ E₂ (w i))
  have hmap : ContinuousOn (fun p : ℝ × E₁ => (p.1, (p.2, (0 : E₂))))
      (T ×ˢ {I | (I, (0 : E₂)) ∈ U}) :=
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
  refine (hfam.comp hmap (fun p hp => ⟨hp.1, hp.2⟩)).congr fun p hp => ?_
  have hcd : ContDiffOn ℂ (k : ℕ∞) (F p.1) U :=
    (KAM.contDiffOn_infty_of_differentiableOn hU (hd _ hp.1)).of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_slice hU hcd hp.2 le_rfl]
  rfl

end FiniteDim

end KAM.Planetary

end
