/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.FhatClause
public import KAM.Planetary.PlanarTorsion.Birkhoff.Compose
public import KAM.Planetary.PlanarTorsion.Birkhoff.Choice
public import KAM.Planetary.PlanarTorsion.Birkhoff.Defs

/-!
# Planar quartic torsion: assembly of `PlanarBirkhoffResult` for a given neighbourhood (package T16)

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form`).  Given the radius, constant and the data of the
normal form (quartic family `F₀`, homological solution `chi`, the lift chart on a fixed tube, the
flow bound, the Lie estimate and the physical radius) which are chosen *before* the good axis
neighbourhood `Oa`, `p11cB_result` shrinks to an action neighbourhood `O'` whose closure is compact
inside `p.actions '' Oa` and proves every clause of `PlanarBirkhoffResult`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem p11cB_tube_mono {O O' : Set (Fin 2 → ℝ)} {r r' : ℝ} (hO : O ⊆ O') (hr : r ≤ r') :
    p11c_tube O r ⊆ p11c_tube O' r' :=
  fun _ hw => ⟨hO hw.1, hw.2.trans_le hr⟩

theorem p11cB_result (p : PlanarData) (hp : p.Valid) (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hKax : closedBall a0 rho ⊆ p11c_axes) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hcax : cthickening ε0 (closedBall a0 rho) ⊆ p11c_axes)
    {Og : Set (Fin 2 → ℝ)} (hOgF : ∀ I ∈ Og, I ∈ p11c_frameActionDomain p)
    (hK₁Og : p.actions '' cthickening ε0 (closedBall a0 rho) ⊆ Og)
    (F₀ : QuarticFamily Og)
    (hF₀ : ∀ I z, F₀.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
      (p11c_rotateSlow (p11c_frame p (p.axes I)) z))
    (chi : QuarticFamily Og) (hchi : ∀ I ∈ Og, chi.eval I = p11c_chi F₀ (p11cB_freq p) I)
    {rL r1 rl A δ r C : ℝ}
    (hchL : IsChart 1 (p11c_liftFlow chi.eval) (p11c_tube (p11cB_O p (closedBall a0 rho) ε0) rL))
    (hinjL : InjOn (p11c_liftFlow chi.eval) (p11c_tube (p11cB_O p (closedBall a0 rho) ε0) rL))
    (htrL : ∀ w ∈ p11c_tube (p11cB_O p (closedBall a0 rho) ε0) rL, ∀ c : Fin 2 → ℝ,
      p11c_liftFlow chi.eval (w + (Fin.append c 0, 0)) =
        p11c_liftFlow chi.eval w + (Fin.append c 0, 0))
    (hflow1 : ∀ I ∈ p.actions '' cthickening ε0 (closedBall a0 rho), ∀ z : Phase 2,
      p11c_slowLength z < r1 →
        p11c_slowLength (p11c_flow chi.eval I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2)
    (hlie : ∀ I ∈ p.actions '' cthickening ε0 (closedBall a0 rho), ∀ z : Phase 2,
      p11c_slowLength z < rl →
      |(p11cB_C p I + p11c_n0 (p11cB_freq p) I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        F₀.eval I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        p11cB_R p I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z)) -
        (p11cB_C p I + p11c_n0 (p11cB_freq p) I z + p11c_average F₀.eval I z)| ≤
          A * p11c_slowLength z ^ 6)
    (hδ : 0 < δ)
    (hdom : ∀ w : Phase (2 + 2),
      (fun i => w.2 (Fin.castAdd 2 i)) ∈ p.actions '' cthickening ε0 (closedBall a0 rho) →
      (∀ i, |w.1 (Fin.natAdd 2 i)| < δ) → (∀ i, |w.2 (Fin.natAdd 2 i)| < δ) → w ∈ p11cB_good p)
    (hr0 : 0 < r) (hrL : r ≤ rL) (hr1 : r ≤ r1) (hrl : r ≤ rl) (hrδ : 2 * r ≤ δ)
    (hAC : A ≤ C) (hC : 0 < C)
    (Oa : Set (Fin 2 → ℝ)) (hOa : IsOpen Oa) (hKOa : closedBall a0 rho ⊆ Oa) :
    PlanarBirkhoffResult p a0 rho Oa r C := by
  set Kc := closedBall a0 rho with hKc
  have hKcc : IsCompact Kc := isCompact_closedBall _ _
  set K₁ := p.actions '' cthickening ε0 Kc with hK₁
  have hK₁d : K₁ ⊆ p11c_frameActionDomain p := fun I hI => hOgF I (hK₁Og hI)
  have hK₁pos : ∀ I ∈ K₁, ∀ i, 0 < I i := by
    rintro _ ⟨a, ha, rfl⟩ i
    exact p11cB_actions_pos p hp (hcax ha) i
  obtain ⟨δ', hδ', hsub'⟩ := hKcc.exists_thickening_subset_open hOa hKOa
  set ε' := min ε0 (δ' / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε0 (by positivity)
  have hε'0 : ε' ≤ ε0 := min_le_left _ _
  have hcax' : cthickening ε' Kc ⊆ p11c_axes := (cthickening_mono hε'0 Kc).trans hcax
  obtain ⟨hc', hcl'⟩ := p11cB_O_closure p hp hKcc hε'pos hcax'
  obtain ⟨hc0, hcl0⟩ := p11cB_O_closure p hp hKcc hε0 hcax
  set O' := p11cB_O p Kc ε' with hO'
  have hO'O₀ : O' ⊆ p11cB_O p Kc ε0 := p11cB_O_mono p Kc hε'0
  have hO'K₁ : O' ⊆ K₁ := fun I hI => hcl0 (subset_closure (hO'O₀ hI))
  have hO'Og : O' ⊆ Og := hO'K₁.trans hK₁Og
  have hKimg : p.actions '' Kc ⊆ O' := by
    rintro _ ⟨a, ha, rfl⟩
    exact p11cB_actions_mem_O p hp hKax hε'pos ha
  have hclOa : closure O' ⊆ p.actions '' Oa := by
    refine hcl'.trans ?_
    refine image_mono ?_
    exact (cthickening_subset_thickening' hδ' (by have := min_le_right ε0 (δ' / 2); linarith)
      Kc).trans hsub'
  -- the tube data
  have hS : ∀ w ∈ p11c_tube O' r, p11cL_act w ∈ p11c_frameActionDomain p :=
    fun w hw => hOgF _ (hO'Og hw.1)
  have hsubtube : p11c_tube O' r ⊆ p11c_tube (p11cB_O p Kc ε0) rL :=
    p11cB_tube_mono hO'O₀ hrL
  obtain ⟨hch, hinj, hact, htr⟩ := p11cB_T_props p hp chi.eval hS (hchL.mono hsubtube)
    (hinjL.mono hsubtube) fun w hw c => htrL w (hsubtube hw) c
  have hTg : ∀ w ∈ p11c_tube O' r,
      (p11c_rotationLift p ∘ p11c_liftFlow chi.eval) w ∈ p11cB_good p := fun w hw =>
    p11cB_T_good p hp chi.eval hK₁d hδ hdom hrδ
      (fun I hI z hz => hflow1 I hI z (hz.trans_le hr1)) w ⟨hO'K₁ hw.1, hw.2⟩
  have hfl : ∀ I ∈ K₁, ∀ z : Phase 2, p11c_slowLength z < r →
      p11c_slowLength (p11c_flow chi.eval I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2 :=
    fun I hI z hz => hflow1 I hI z (hz.trans_le hr1)
  refine ⟨O', p11cB_O_isOpen p Kc ε', hKimg, hc'.of_isClosed_subset isClosed_closure hcl', hclOa,
    p11cB_restrict F₀ hO'Og, p11cB_restrict chi hO'Og, fun I _ z => hF₀ I z,
    fun I hI => hchi I (hO'Og hI), p11c_rotationLift p ∘ p11c_liftFlow chi.eval, rfl, ?_, hch, hinj,
    hact, htr, fun w hw => hTg w hw, ?_⟩
  · intro I hI j
    have := p11c_sigma_neg p hp (hK₁d (hO'K₁ hI)) j
    linarith
  · intro fhat hf
    rcases hf with rfl | rfl
    · exact p11cB_fhat_clause p hp false (p11c_hatFix p) (fun w => rfl)
        (analyticOnNhd_fFix_poincareProd hp.2.2 (mul_pos hp.1 hp.2.1)) hOgF hK₁Og hK₁pos F₀ hF₀
        chi hchi hlie hδ hdom hrδ hrl hr0 hAC hC hfl hO'K₁ hKimg hch
    · exact p11cB_fhat_clause p hp true (p11c_hatMov p) (fun w => rfl)
        (analyticOnNhd_fMov_poincareProd hp.2.2 (mul_pos hp.1 hp.2.1)) hOgF hK₁Og hK₁pos F₀ hF₀
        chi hchi hlie hδ hdom hrδ hrl hr0 hAC hC hfl hO'K₁ hKimg hch

end KAM.Planetary

end
