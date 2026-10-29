/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Planetary.PlanarTorsion.Generic
public import KAM.Planetary.PlanarTorsion.TorsionBound
public import KAM.Planetary.PlanarTorsion.Birkhoff
public import KAM.Planetary.Nondegeneracy.Interface

/-!
# Planar quartic torsion: the good patch (P11C, package T21)

Blueprint P, Part 11b (`bpP:p11b:patch`): `PlanarFrequencyPatch`, `patch` and the geometric helper
`torsion_patch_geometry`.  The upstream interface `Nondegeneracy.interface` is applied to the
nonresonance polynomial `p11c_phi4` and the torsion determinant (analytic and not identically zero
on the axis cone by T20), which gives a closed ball `closedBall a0 (2 * r)` of good axes in the
prescribed neighbourhood on which both are nonzero, together with the frequency data.  The
determinant has a positive minimum on the compact inner ball (T17 `remain`), and `birkhoff_form`
(T16) is applied with the open outer ball.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter
namespace KAM.Planetary
open KAM KAM.Kepler

/-- The source's combined fast/slow frequency, in frozen actions. -/
def p11c_combinedFrequency (p : PlanarData) (I : Fin 2 → ℝ) : Fin (2 + 2) → ℝ :=
  Fin.append (fun i => p.kappa ^ 2 * p.m i ^ 3 / I i ^ 3)
    (fun i => 2 * p11c_sigma p (p.axes I) i)

/-- Output projection needed from Part 10's interface, not an invented upstream theorem. -/
def PlanarFrequencyPatch (p : PlanarData) (a0 : Fin 2 → ℝ) (r : ℝ) : Prop :=
  let O := p.actions '' ball a0 (2 * r)
  let K := p.actions '' closedBall a0 r
  IsOpen O ∧ IsConnected O ∧ IsCompact K ∧ 0 < volume K ∧
  AnalyticOnNhd ℝ (p11c_combinedFrequency p) O ∧
  (∀ c : Fin (2 + 2) → ℝ, c ≠ 0 → ∃ I ∈ O, ∑ j, c j * p11c_combinedFrequency p I j ≠ 0) ∧
  (∃ alpha : ℝ, 0 < alpha ∧ ∀ a ∈ closedBall a0 r, ∀ k : Fin 2 → ℤ,
    k ≠ 0 → (∑ j, |(k j : ℝ)|) ≤ 4 → alpha ≤ |∑ j, (k j : ℝ) * (2 * p11c_sigma p a j)|) ∧
  ∃ mu0 : ℕ, 1 ≤ mu0 ∧ ∃ beta : ℝ, 0 < beta ∧ ∀ mu : ℕ, mu0 ≤ mu →
    ∀ c : Fin (2 + 2) → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ I ∈ K,
      ∃ j ≤ mu, ∃ v : Fin 2 → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
        beta ≤ |iteratedFDeriv ℝ j (fun J => (∑ k, c k * p11c_combinedFrequency p J k) ^ 2)
          I (fun _ => v)|

/-! ### Bridges to the Part-8/10 data -/

theorem p11cPa_action_eq (p : PlanarData) (hp : p.Valid) :
    SecularForm.action (p11cSecularData p hp) = p.actions := rfl

theorem p11cPa_axis_eq (p : PlanarData) (hp : p.Valid) :
    SecularForm.axis (p11cSecularData p hp) = p.axes := rfl

theorem p11cPa_axes_actions (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : p.axes (p.actions a) = a := by
  have := Nondegeneracy.axis_action (p11cSecularData p hp) a (p11c_axes_mem ha)
  rwa [p11cPa_action_eq, p11cPa_axis_eq] at this

theorem p11cPa_freq_eq (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    Nondegeneracy.frequency (p11cSecularData p hp) (p.actions a) =
      p11c_combinedFrequency p (p.actions a) := by
  unfold Nondegeneracy.frequency p11c_combinedFrequency
  congr 1
  funext j
  rw [p11cPa_axis_eq, p11cPa_axes_actions p hp ha, p11c_sigma_eq_sigma p hp ha]

theorem p11cPa_euclid {n : ℕ} (x : Fin n → ℝ) :
    KAM.Nekhoroshev.euclid x = SecularSpectrum.length2 x := by
  simp [KAM.Nekhoroshev.euclid, SecularSpectrum.length2, sq_abs]

theorem p11cPa_unit : SecularSpectrum.length2 (Pi.single 0 1 : Fin 2 → ℝ) = 1 := by
  simp [SecularSpectrum.length2, Pi.single_apply]

/-- A strict lower bound for the jet maximum is attained, up to the bound, by one jet order and
one unit direction. -/
theorem p11cPa_jet_attain {g : (Fin 2 → ℝ) → ℝ} {y : Fin 2 → ℝ} {μ : ℕ} {b : ℝ}
    (h : b < Nondegeneracy.jetMax g μ y) :
    ∃ j ≤ μ, ∃ v : Fin 2 → ℝ, SecularSpectrum.length2 v = 1 ∧
      b < |iteratedFDeriv ℝ j g y (fun _ => v)| := by
  unfold Nondegeneracy.jetMax at h
  obtain ⟨_, ⟨j, hj, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
    (Set.Nonempty.image _ ⟨0, Nat.zero_le μ⟩) h
  refine ⟨j, hj, ?_⟩
  unfold Nondegeneracy.scalarJet at hlt
  beta_reduce at hlt
  split_ifs at hlt with h0
  · subst h0
    exact ⟨Pi.single 0 1, p11cPa_unit, by simpa using hlt⟩
  · have hne : {r | ∃ v : Fin 2 → ℝ, SecularSpectrum.length2 v = 1 ∧
        r = |iteratedFDeriv ℝ j g y (fun _ => v)|}.Nonempty :=
      ⟨_, Pi.single 0 1, p11cPa_unit, rfl⟩
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt'⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨v, hv, hlt'⟩

/-- Full patch node: includes the retained Part-10 attachment and the Birkhoff map. -/
theorem patch (p : PlanarData) (hp : p.Valid) (aStar : Fin 2 → ℝ)
    (ha : aStar ∈ p11c_axes) (eta : ℝ) (he : 0 < eta) :
    ∃ a0 : Fin 2 → ℝ, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧
      closedBall a0 (2 * r) ⊆ ball aStar eta ∩
        {a ∈ p11c_axes | p11c_phi4 p a ≠ 0 ∧ (p11c_beta p a).det ≠ 0} ∧
      (∀ a ∈ closedBall a0 r, B ≤ |(p11c_beta p a).det| ∧ (p11c_beta p a).IsSymm) ∧
      PlanarFrequencyPatch p a0 r ∧
      ∃ rStar CStar : ℝ, 0 < rStar ∧ 0 < CStar ∧
        PlanarBirkhoffResult p a0 r (ball a0 (2 * r)) rStar CStar := by
  classical
  have han := p11cGe_det_analytic p hp
  obtain ⟨a1, ha1, hd⟩ := p11cGe_det_neg p hp
  obtain ⟨a2, ha2, hph⟩ := p11cGe_phi4_exists p hp
  obtain ⟨a0, r0, α, β, μ0, hr0, hα, hβ, hμ0, hsub, hfne, -, hαall, hB⟩ :=
    Nondegeneracy.interface (p11cSecularData p hp) le_rfl (p11c_axes_mem ha) he
      (f := ![fun a => p11c_phi4 p a, fun a => (p11c_beta p a).det])
      (by
        rw [← p11cGe_axes_eq, Fin.forall_fin_two]
        exact ⟨p11cGe_phi4_analytic p hp, han⟩)
      (by
        rw [← p11cGe_axes_eq, Fin.forall_fin_two]
        exact ⟨⟨a2, ha2, hph⟩, ⟨a1, ha1, hd.ne⟩⟩)
  obtain ⟨hBo, hBc, hKc, hKB, hKv, hAn, hrnd, hβdef, hμ, hmono, hjet⟩ := hB
  have haxes : ∀ a ∈ closedBall a0 (2 * r0), a ∈ p11c_axes := fun a h => by
    rw [p11cGe_axes_eq]; exact (hsub h).1.1
  have hgood : closedBall a0 (2 * r0) ⊆ ball aStar eta ∩
      {a ∈ p11c_axes | p11c_phi4 p a ≠ 0 ∧ (p11c_beta p a).det ≠ 0} := fun a h =>
    ⟨(hsub h).2, haxes a h, hfne a h 0, hfne a h 1⟩
  have hrr : closedBall a0 r0 ⊆ closedBall a0 (2 * r0) :=
    closedBall_subset_closedBall (by linarith)
  have hbb : ball a0 (2 * r0) ⊆ closedBall a0 (2 * r0) := ball_subset_closedBall
  obtain ⟨B, hB0, hBle⟩ := remain p _ (isCompact_closedBall a0 r0)
    (fun a h => (hgood (hrr h)).2.2.2)
    (han.continuousOn.mono fun a h => haxes a (hrr h))
  have hsymm := (beta_properties p hp).2
  refine ⟨a0, r0, B, hr0, hB0, hgood, fun a h => ⟨hBle a h, hsymm a⟩, ?_, ?_⟩
  · unfold PlanarFrequencyPatch
    dsimp only
    rw [p11cPa_action_eq] at hBo hBc hKB hKc hKv hAn hrnd hβdef hmono hjet
    have heq : EqOn (Nondegeneracy.frequency (p11cSecularData p hp)) (p11c_combinedFrequency p)
        (p.actions '' ball a0 (2 * r0)) := by
      rintro _ ⟨a, h, rfl⟩
      exact p11cPa_freq_eq p hp (haxes a (hbb h))
    refine ⟨hBo, hBc, hKc, hKv, hAn.congr hBo heq, ?_, ?_, μ0, hμ0, β / 2, by linarith, ?_⟩
    · intro c hc
      obtain ⟨I, hI, hne⟩ := hrnd c hc
      exact ⟨I, hI, by rwa [← heq hI]⟩
    · refine ⟨α, hα, fun a h k hk0 hk4 => ?_⟩
      have hpos : 0 < ∑ i, |k i| := by
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hk0
        exact Finset.sum_pos' (fun i _ => abs_nonneg (k i))
          ⟨j, Finset.mem_univ j, abs_pos.2 hj⟩
      have hmem := hαall a h k ⟨hpos, by exact_mod_cast hk4⟩
      rwa [← p11c_sigma_eq_sigma p hp (haxes a (hrr h))] at hmem
    · intro μ hμ' c hc I hI
      have hc' : SecularSpectrum.length2 c = 1 := (p11cPa_euclid c).symm.trans hc
      have hle : Nondegeneracy.betaMu (Nondegeneracy.frequency (p11cSecularData p hp))
          (p.actions '' closedBall a0 r0) μ ≤
          Nondegeneracy.jetMax (Nondegeneracy.squaredForm
            (Nondegeneracy.frequency (p11cSecularData p hp)) c) μ I := by
        unfold Nondegeneracy.betaMu Nondegeneracy.betaFamily
        exact csInf_le ⟨0, by rintro _ ⟨z, -, rfl⟩; exact Nondegeneracy.jetMax_nonneg _ _ _⟩
          ⟨(c, I), ⟨hc', hI⟩, rfl⟩
      obtain ⟨j, hj, v, hv, hlt⟩ := p11cPa_jet_attain (b := β / 2)
        (lt_of_lt_of_le (half_lt_self hβ) ((hmono μ hμ').trans hle))
      refine ⟨j, hj, v, (p11cPa_euclid v).trans hv, ?_⟩
      have hev : (Nondegeneracy.squaredForm (Nondegeneracy.frequency (p11cSecularData p hp)) c)
          =ᶠ[nhds I] fun J => (∑ k, c k * p11c_combinedFrequency p J k) ^ 2 := by
        filter_upwards [hBo.mem_nhds (hKB hI)] with J hJ
        simp only [Nondegeneracy.squaredForm, heq hJ]
      rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds] at hlt
      exact hlt.le
  · obtain ⟨rS, C, hrS, hC, hres⟩ := birkhoff_form p hp a0 r0
      (fun a h => ⟨haxes a (hrr h), (hgood (hrr h)).2.2.1⟩)
    refine ⟨rS, C, hrS, hC, hres _ isOpen_ball (closedBall_subset_ball (by linarith)) ?_⟩
    exact fun a h => ⟨haxes a (hbb h), (hgood (hbb h)).2.2.1⟩

/-- The geometric part of `patch`, a distinct helper name. -/
theorem torsion_patch_geometry (p : PlanarData) (hp : p.Valid) (aStar : Fin 2 → ℝ)
    (ha : aStar ∈ p11c_axes) (eta : ℝ) (he : 0 < eta) :
    ∃ a0 : Fin 2 → ℝ, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧
      closedBall a0 (2 * r) ⊆ ball aStar eta ∩
        {a ∈ p11c_axes | p11c_phi4 p a ≠ 0 ∧ (p11c_beta p a).det ≠ 0} ∧
      (∀ a ∈ closedBall a0 r, B ≤ |(p11c_beta p a).det| ∧ (p11c_beta p a).IsSymm) := by
  obtain ⟨a0, r, B, hr, hB, h1, h2, -⟩ := patch p hp aStar ha eta he
  exact ⟨a0, r, B, hr, hB, h1, h2⟩

end KAM.Planetary

end
