/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Iso.Confinement.PatchConst
public import KAM.Iso.Confinement.RealHam
public import KAM.Iso.Confinement.Separation

/-!
# Part 5: confinement and global existence

Blueprint `bpI:p5:confinement`, steps
`cf-conf`, `cf-cont`. Keep the notation of `§sec-sep` (`SepSetting`). The maximal solution
`z` of `ż = X_ℝ(z)` in `W_B = ℝ² × B` through `z₀` (`IsMaximalSolution`, a source premise; its
existence is `gen_maximal`) satisfies `T_± = ±∞`, `z(t) ∈ 𝒱` and `z(t)₂ ∈ 𝒦` for all `t`, and
`‖z(t)₂ - I₀‖ < η₁/2`.

* `confinement_prop_of_invariant`: conditional helper, takes the invariance of `𝒯₊ ∪ 𝒯₋` as a
  premise (distinct name).
* `confinement_prop`: source-facing; takes the named Part 3 output (`TorusOutput` for both tori)
  and the identifications `𝒯_± = graph Y_±` and derives the invariance through
  `separation_confined`.

Both are two-line instances of the private `confinement_core`: the barrier `z(t) ∈ 𝒱` on the
maximal interval (supplied by `separation_confined(_of_invariant)`), the compactness of `𝒦`, the
continuation criterion `gen_continuation_periodic` (`cf-cont`), and the geometry of the patch.
-/

public section

open Set Metric

namespace KAM.Iso.Confinement

open KAM KAM.ODE

section Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε η₁ F₁ C_K : ℝ} {p : EnergyPatch (realPart h) B η₁}
  {r Lm LΦ κ E : ℝ} {Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Ip Im : Fin 2 → ℝ}

/-- Step `cf-cont`: on the maximal interval a solution that stays in `𝒱` (hence in `𝒦`) is global,
and stays within `η₁/2` of its initial action. -/
private theorem confinement_core
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    (hB : IsOpen B) {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) {Tm Tp : EReal} {z : ℝ → P2}
    (hz : IsMaximalSolution (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) z₀ Tm Tp z)
    (hsep : ∀ t ∈ eIoo Tm Tp, z t ∈ sepRegion p Yp Ym) :
    Tm = ⊥ ∧ Tp = ⊤ ∧ (∀ t, z t ∈ sepRegion p Yp Ym) ∧ (∀ t, (z t).2 ∈ p.K) ∧
      ∀ t, ‖(z t).2 - z₀.2‖ < η₁ / 2 := by
  have hK : ∀ t ∈ eIoo Tm Tp, (z t).2 ∈ p.K := fun t ht => p.Omega_subset_K (hsep t ht).1
  have hKB : p.K ⊆ B := fun I hI => p.W_subset_B hI.1
  obtain ⟨hcp, hcm⟩ := gen_continuation_periodic hB (realHam_field_contDiffOn S.base S.perturb)
    (fun k _ hx => realHam_field_periodic S.base S.perturb k hx) hz p.isCompact_K hKB
  have hTp : Tp = ⊤ := hcp ⟨0, le_rfl, by simpa using hz.pos_lt, fun t ht0 htT =>
    hK t ⟨lt_of_lt_of_le hz.neg_lt (by exact_mod_cast ht0), htT⟩⟩
  have hTm : Tm = ⊥ := hcm ⟨0, le_rfl, by simpa using hz.neg_lt, fun t htT ht0 =>
    hK t ⟨htT, lt_of_le_of_lt (by exact_mod_cast ht0) hz.pos_lt⟩⟩
  subst hTp hTm
  have hall : ∀ t : ℝ, t ∈ eIoo ⊥ ⊤ := fun t => by rw [eIoo_bot_top]; exact mem_univ t
  have hz0 : z₀.2 ∈ ball p.c (η₁ / 4) :=
    ball_subset_ball p.ρc_le (by rwa [mem_ball, dist_eq_norm])
  refine ⟨rfl, rfl, fun t => hsep t (hall t), fun t => hK t (hall t), fun t => ?_⟩
  have h1 : (z t).2 ∈ ball p.c (η₁ / 4) := p.W_subset_ball (hK t (hall t)).1
  rw [mem_ball, dist_eq_norm] at h1 hz0
  calc ‖(z t).2 - z₀.2‖ = ‖((z t).2 - p.c) - (z₀.2 - p.c)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖(z t).2 - p.c‖ + ‖z₀.2 - p.c‖ := norm_sub_le _ _
    _ < η₁ / 2 := by linarith

/-- `bpI:p5:confinement`: for the maximal solution `z` of `ż = X_ℝ(z)` in `W_B` through `z₀`
(`IsMaximalSolution`, a source premise), `T_± = ±∞`, `z(t) ∈ 𝒱`, `z(t)₂ ∈ 𝒦`, and
`‖z(t)₂ - I₀‖ < η₁/2`. -/
theorem confinement_prop_of_invariant
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    (hB : IsOpen B) {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀)
    (hinv : IsInvariantSet (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B)
      (graphSet Yp ∪ graphSet Ym))
    {Tm Tp : EReal} {z : ℝ → P2}
    (hz : IsMaximalSolution (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) z₀ Tm Tp z) :
    Tm = ⊥ ∧ Tp = ⊤ ∧ (∀ t, z t ∈ sepRegion p Yp Ym) ∧ (∀ t, (z t).2 ∈ p.K) ∧
      ∀ t, ‖(z t).2 - z₀.2‖ < η₁ / 2 :=
  confinement_core S hB hz₀ hz
    (separation_confined_of_invariant S hz₀ hE hinv (ordConnected_eIoo Tm Tp) (zero_mem_eIoo hz)
      hz.isSolution hz.init)

/-- SOURCE-FACING `bpI:p5:confinement`: as `confinement_prop_of_invariant`, with the
named Part 3 output and the graph identifications instead of `hinv`. -/
theorem confinement_prop (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    {Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {ωp ωm : Fin 2 → ℝ}
    (Tp : TorusOutput h f ε C_K s₀ E Kp Ip ωp) (Tm : TorusOutput h f ε C_K s₀ E Km Im ωm)
    (hgp : Set.range (realRestriction Kp) = graphSet Yp)
    (hgm : Set.range (realRestriction Km) = graphSet Ym)
    (hB : IsOpen B) {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc)
    (hE : E = realHamiltonian h f z₀) {Tm' Tp' : EReal} {z : ℝ → P2}
    (hz : IsMaximalSolution (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) z₀ Tm' Tp'
      z) :
    Tm' = ⊥ ∧ Tp' = ⊤ ∧ (∀ t, z t ∈ sepRegion p Yp Ym) ∧ (∀ t, (z t).2 ∈ p.K) ∧
      ∀ t, ‖(z t).2 - z₀.2‖ < η₁ / 2 :=
  confinement_core S hB hz₀ hz
    (separation_confined S Tp Tm hgp hgm hz₀ hE (ordConnected_eIoo Tm' Tp')
      (zero_mem_eIoo hz) hz.isSolution hz.init)

end Confinement

end KAM.Iso.Confinement
