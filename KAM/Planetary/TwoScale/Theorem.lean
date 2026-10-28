/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.TheoremInverse
public import KAM.Planetary.TwoScale.TheoremTorus
public import KAM.Planetary.TwoScale.Measure

/-!
# Two-scale KAM: the signed theorem `two_scale_kam` (`bpP:p3:two-scale-kam`)

The joint construction: on the witnesses of one application of `iterative`
(`tori_limit_of_iterative`), with the limit maps `(i, Φinf)`, the source inverse locus
`I₀ : Ω → D₀` (`KamHyp.exists_inverse_locus`) and `K ω θ = Φinf (θ, i (I₀ ω))`, every clause of the
signed statement is supplied by the private helpers of P23-17..21 applied to the same witnesses:
the action clauses by `limit_actions_of_steps`, the map clauses by `ToriLimit`, the tori by
`lattice_torus_of_limit` and `tori_estimates_of_limit`, the inverse-frequency estimates by
`KamHyp.inverse_local`/`inverse_global`, and the measure clause by `meas_torus_final`. No premise
beyond `KamHyp` and `hL`. Design package P23-22.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Main joint construction, frozen phase order. No witness selection definition.
The source torus (v,theta+u) is represented as (theta+u,v), so this is the exact
unscaled input for P1 cyl_pipeline, with the same frequency. -/
theorem two_scale_kam {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f)
    (hL : p.L = initialL p.M p.Mhat p.Mbar) :
    ∃ (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (Φ : Phase (a + b) → Phase (a + b))
      (K : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) → Phase (a + b))
      (I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (KC : (Fin (a + b) → ℝ) → (Fin (a + b) → ℂ) → CPhase (a + b)),
      let D₀ := dioBase D h p
      let Ω := omegaSet D h p
      let Dstar := i '' D₀
      let r := 32 * eHat p * rhoHat p
      let Hr := fun z : Phase (a + b) =>
        (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re
      let KO := ⋃ ω ∈ Ω, range (K ω)
      (∀ ω ∈ Ω, I₀ ω ∈ D₀ ∧ realFreq h (I₀ ω) = ω ∧ ∀ I ∈ D₀, realFreq h I = ω → I = I₀ ω) ∧
      (∀ I ∈ D₀,
        ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
        ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p) ∧
      (∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
          768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
        Φ (x + KAM.ODE.angleShift k) = Φ x + KAM.ODE.angleShift k) ∧
      (∀ ω ∈ Ω, ∀ θ, K ω θ = Φ (θ, i (I₀ ω))) ∧
      (∀ ω ∈ Ω,
        IsLatticeTorus KAM.ODE.angleShift Hr (univ ×ˢ realTube D r) ω (K ω) ∧
        DifferentiableOn ℂ (KC ω) (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
        (∀ θ, KC ω (KAM.realInclusion (a + b) θ) = KAM.realInclusion₂ (a + b) (K ω θ)) ∧
        (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
          ‖(KC ω θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) ∧
        (∀ θ,
          ‖firstBlock (b := b) ((K ω θ).2 - I₀ ω)‖ ≤
            20 * (p.Mbar₁ / p.Mbar + p.Mhat / p.M) * eHat p * rhoHat p ∧
          ‖lastBlock (a := a) ((K ω θ).2 - I₀ ω)‖ ≤
            20 * (p.Mbar₂ / p.Mbar + 1) * eHat p * rhoHat p ∧
          ‖fderiv ℝ (fun θ => (K ω θ).1 - θ) θ‖ ≤ 3 / 4 * (a + b) * eHat p)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ∀ θ θ', ∀ k : Fin (a + b) → ℤ,
        K ω θ = K ω' θ' + KAM.ODE.angleShift k → ω = ω' ∧ θ = θ' + fun j => (k j : ℝ)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ‖ω - ω'‖ < p.ρ / p.Mbar → ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * ‖ω - ω'‖) ∧
      (Bornology.IsBounded D → ∀ ω ∈ Ω, ∀ ω' ∈ Ω,
        ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * max 1 (Metric.diam D / p.ρ) * ‖ω - ω'‖) ∧
      volume (((univ ×ˢ realTube D r) \ KO) ∩ {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico 0 1}) ≤
        ENNReal.ofReal (complementConstant (a + b)) *
          (volume (D \ D₀) + volume (realTube D r \ D)) := by
  classical
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, i, Φinf, h0, S, P, Q, T⟩ := tori_limit_of_iterative H
  have hD0 : Ds 0 ⊆ D := by rw [h0]; exact Set.inter_subset_left
  have hmemD : ∀ I, I ∈ dioBase D h p → I ∈ Ds 0 := fun I hI => by rw [h0]; exact hI
  obtain ⟨i', hconv', -, -, -, -, hLip', -, -, -, -⟩ := limit_actions_of_steps S
  have hii : ∀ I ∈ Ds 0, i' I = i I := fun I hI =>
    tendsto_nhds_unique (hconv'.tendsto_at hI) (T.i_conv.tendsto_at hI)
  have hLip : ∀ I ∈ Ds 0, ∀ J ∈ Ds 0,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖ := by
    intro I hI J hJ
    have := hLip' I hI J hJ
    rwa [hii I hI, hii J hJ] at this
  obtain ⟨I₀, hI₀⟩ : ∃ I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ), ∀ ω ∈ omegaSet D h p,
      I₀ ω ∈ dioBase D h p ∧ realFreq h (I₀ ω) = ω ∧
        ∀ J ∈ dioBase D h p, realFreq h J = ω → J = I₀ ω := by
    choose! I₀ hI₀ using H.exists_inverse_locus
    exact ⟨I₀, hI₀⟩
  have hΩ0 : ∀ ω ∈ omegaSet D h p, I₀ ω ∈ Ds 0 := fun ω hω => hmemD _ (hI₀ ω hω).1
  have hKCex : ∀ ω ∈ omegaSet D h p, ∃ KC : (Fin (a + b) → ℂ) → CPhase (a + b),
      DifferentiableOn ℂ KC (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
      (∀ θ, KC (KAM.realInclusion (a + b) θ) =
        KAM.realInclusion₂ (a + b) (Φinf (θ, i (I₀ ω)))) ∧
      (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
        ‖(KC θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) :=
    fun ω hω => (tori_estimates_of_limit H hD0 T (hΩ0 ω hω)).1
  choose! KCω hKCω using hKCex
  have hlipΦ : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
        768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y) := by
    rw [← h0]; exact T.phi_lip
  have hsup : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ‖firstBlock (b := b) ((Φinf x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φinf x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
      2 * π * ‖(Φinf x - x).1‖ ≤ 3 / 2 * eHat p * p.s := by
    rw [← h0]; exact T.phi_block
  have hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p :=
    fun I hI => ⟨(T.i_block I (hmemD I hI)).1, (T.i_block I (hmemD I hI)).2.1⟩
  have hlipI : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖ :=
    fun I hI J hJ => hLip I (hmemD I hI) J (hmemD J hJ)
  have hinjΦ : InjOn Φinf (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))) :=
    H.phi_injOn hlipΦ
  have hinjI : InjOn i (dioBase D h p) := H.i_injOn hlipI
  refine ⟨i, Φinf, fun ω θ => Φinf (θ, i (I₀ ω)), I₀, KCω, ?_⟩
  dsimp only
  refine ⟨fun ω hω => hI₀ ω hω, hblk, hlipI, ?_, ?_, fun ω _ θ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have := hlipΦ x hx y hy
    rwa [Nat.cast_add] at this
  · intro x hx k
    rw [← h0] at hx
    exact T.phi_per x hx k
  · intro ω hω
    obtain ⟨-, e2, -⟩ := tori_estimates_of_limit H hD0 T (hΩ0 ω hω)
    obtain ⟨-, hd, -, -⟩ := tori_lagr_of_limit H T (hΩ0 ω hω)
    have hlt := lattice_torus_of_limit H P Q hD0 T (hΩ0 ω hω)
    rw [(hI₀ ω hω).2.1] at hlt
    refine ⟨hlt, (hKCω ω hω).1, (hKCω ω hω).2.1,
      (hKCω ω hω).2.2, fun θ => ⟨(e2 θ).1, (e2 θ).2, ?_⟩⟩
    have := hd θ
    rwa [Nat.cast_add] at this
  · intro ω hω ω' hω' θ θ' k hk
    have hx : (θ, i (I₀ ω)) ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))) :=
      ⟨trivial, I₀ ω, (hI₀ ω hω).1, rfl⟩
    have hy : (θ', i (I₀ ω')) ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))) :=
      ⟨trivial, I₀ ω', (hI₀ ω' hω').1, rfl⟩
    have hy' : (θ', i (I₀ ω')) + KAM.ODE.angleShift k ∈
        (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))) :=
      ⟨trivial, I₀ ω', (hI₀ ω' hω').1, by simp [KAM.ODE.angleShift]⟩
    have hper : Φinf ((θ', i (I₀ ω')) + KAM.ODE.angleShift k) =
        Φinf (θ', i (I₀ ω')) + KAM.ODE.angleShift k := by
      exact T.phi_per _ (h0 ▸ hy : (θ', i (I₀ ω')) ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b)))) k
    have heq := hinjΦ hx hy' (by rw [hper]; exact hk)
    have h1 : θ = θ' + fun j => (k j : ℝ) := congrArg Prod.fst heq
    have h2 : i (I₀ ω) = i (I₀ ω') := by
      have := congrArg Prod.snd heq
      simpa [KAM.ODE.angleShift] using this
    have h3 := hinjI (hI₀ ω hω).1 (hI₀ ω' hω').1 h2
    refine ⟨?_, h1⟩
    rw [← (hI₀ ω hω).2.1, ← (hI₀ ω' hω').2.1, h3]
  · intro ω hω ω' hω' hlt
    have hl := H.inverse_local (hI₀ ω hω).1.1 (hI₀ ω' hω').1.1 (by
      rw [(hI₀ ω hω).2.1, (hI₀ ω' hω').2.1]; exact hlt)
    rwa [(hI₀ ω hω).2.1, (hI₀ ω' hω').2.1] at hl
  · intro hb ω hω ω' hω'
    have hl := H.inverse_global hb (hI₀ ω hω).1.1 (hI₀ ω' hω').1.1
    rwa [(hI₀ ω hω).2.1, (hI₀ ω' hω').2.1] at hl
  · have hlipΦ' : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
        ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
          768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y) := by
      intro x hx y hy
      have := hlipΦ x hx y hy
      rwa [Nat.cast_add] at this
    exact meas_torus_final H hblk hlipI hlipΦ' hsup hI₀ (K := fun ω θ => Φinf (θ, i (I₀ ω)))
      (fun ω _ θ => rfl)

#print axioms two_scale_kam

end KAM.Planetary

end
