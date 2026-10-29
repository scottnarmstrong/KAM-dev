/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Result
public import KAM.Planetary.PlanarTorsion.NormalForm
public import KAM.Planetary.PlanarTorsion.Lift
public import KAM.Planetary.PlanarTorsion.QuarticFlow

/-!
# Planar quartic torsion: the constants of the Birkhoff theorem (package T16)

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form`).  The slow radius `r` and the remainder constant
`C` are chosen before the good axis neighbourhood `Oa`, depending only on the physical data and the
compact cube: take a `δ₀`-thickening of the cube inside the good axis set (open, since `p11c_phi4`
is continuous), the family `F₀` and the homological solution `chi` on the corresponding action
neighbourhood, and the radii of the lift (`lift_map`), the flow (`flow`), the Lie estimate (`lie`)
and the physical domain (`p11cB_domain`) on the compact action image of the `δ₀/2`-thickening.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem p11cB_main (p : PlanarData) (hp : p.Valid) (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hgoodK : closedBall a0 rho ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0}) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ Oa : Set (Fin 2 → ℝ),
      IsOpen Oa → closedBall a0 rho ⊆ Oa → PlanarBirkhoffResult p a0 rho Oa r C := by
  set Kc := closedBall a0 rho with hKc
  have hKcc : IsCompact Kc := isCompact_closedBall _ _
  have hAo := p11cB_goodA_isOpen p hp
  obtain ⟨δ0, hδ0, hsub0⟩ := hKcc.exists_thickening_subset_open hAo hgoodK
  set ε0 := δ0 / 2 with hε0
  have hε0pos : 0 < ε0 := by positivity
  have hcth : cthickening ε0 Kc ⊆ thickening δ0 Kc :=
    cthickening_subset_thickening' hδ0 (by linarith) Kc
  have hcax : cthickening ε0 Kc ⊆ p11c_axes := fun a ha => (hsub0 (hcth ha)).1
  have hKax : Kc ⊆ p11c_axes := fun a ha => (hgoodK ha).1
  obtain ⟨hK₁c, hcl₀⟩ := p11cB_O_closure p hp hKcc hε0pos hcax
  set K₁ := p.actions '' cthickening ε0 Kc with hK₁
  set O₀ := p11cB_O p Kc ε0 with hO₀
  set Og := p11cB_O p Kc δ0 with hOg
  have hOgo : IsOpen Og := p11cB_O_isOpen p Kc δ0
  have hOgF : ∀ I ∈ Og, I ∈ p11c_frameActionDomain p := fun I hI => (hsub0 hI.2).1
  have hOgphi : ∀ I ∈ Og, p11c_phi4 p (p.axes I) ≠ 0 := fun I hI => (hsub0 hI.2).2
  have hK₁Og : K₁ ⊆ Og := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨p11cB_actions_pos p hp (hcax ha), ?_⟩
    rw [p11cB_axes_actions p hp (hcax ha)]
    exact hcth ha
  have hK₁d : K₁ ⊆ p11c_frameActionDomain p := fun I hI => hOgF I (hK₁Og hI)
  have hK₁pos : ∀ I ∈ K₁, ∀ i, 0 < I i := by
    rintro _ ⟨a, ha, rfl⟩ i
    exact p11cB_actions_pos p hp (hcax ha) i
  have hO₀K₁ : O₀ ⊆ K₁ := fun I hI => hcl₀ (subset_closure hI)
  have hclOg : closure O₀ ⊆ Og := hcl₀.trans hK₁Og
  have hclc : IsCompact (closure O₀) := hK₁c.of_isClosed_subset isClosed_closure hcl₀
  obtain ⟨F₀, hF₀⟩ := p11cB_family p hp hOgF
  have hnr := p11cB_NR4 p hOgphi
  have hfreq := p11cB_freq_analyticOnNhd p hp hOgF
  obtain ⟨⟨chi, hchi⟩, -⟩ := homological hOgo F₀ (p11cB_freq p) hfreq hnr
  obtain ⟨rL, hrL, hchL, hinjL, htrL⟩ := lift_map hOgo (p11cB_O_isOpen p Kc ε0) hclc hclOg chi
  obtain ⟨Cf, r1, hCf, hr1, -, hfl⟩ := flow hOgo chi K₁ hK₁c hK₁Og
  have hflow1 : ∀ I ∈ K₁, ∀ z : Phase 2, p11c_slowLength z < r1 →
      p11c_slowLength (p11c_flow chi.eval I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2 :=
    fun I hI z hz => (hfl I hI z hz).2.2.1 1 ⟨by norm_num, le_rfl⟩
  obtain ⟨A, rl, hA, hrl, hlie⟩ := lie hOgo F₀ (p11cB_freq p) hfreq hnr (p11cB_C p)
    (fun u => p11cB_R p u.1 u.2)
    (fun I hI => p11cB_R_analyticAt p hp (hOgF I hI) (fun i => hI.1 i))
    (fun I hI => p11cB_R_jetEq p hp (hOgF I hI) (fun i => hI.1 i)) K₁ hK₁c hK₁Og
  obtain ⟨δ, hδ, hdom⟩ := p11cB_domain p hp hK₁c hK₁d hK₁pos
  set r := min (min rL r1) (min rl (δ / 2)) with hr
  have hrpos : 0 < r := lt_min (lt_min hrL hr1) (lt_min hrl (by positivity))
  refine ⟨r, max A 1, hrpos, lt_max_of_lt_right one_pos, fun Oa hOa hKOa => ?_⟩
  refine p11cB_result p hp a0 rho hKax hε0pos hcax hOgF hK₁Og F₀ hF₀ chi hchi hchL hinjL htrL
    hflow1 hlie hδ hdom hrpos ?_ ?_ ?_ ?_ (le_max_left _ _) (lt_max_of_lt_right one_pos) Oa hOa hKOa
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · have h1 : r ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith

end KAM.Planetary

end
