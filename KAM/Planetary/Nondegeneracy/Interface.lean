/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.Frequency
public import KAM.Planetary.Nondegeneracy.FiniteType
public import KAM.Planetary.Nondegeneracy.AnalyticZeros

/-!
# The good-patch interface

Blueprint P, Part 10 (`bpP:p10:interface`, `stepP:p10:if-a` to `if-d`): a closed cube in the good
axes inside a prescribed neighbourhood, on which finitely many further analytic functions of the
axes stay nonzero, together with the non-resonance constant `α`, the image `B`, `K` in the action
variable, and the index `μ0` and amount `β` of the frequency map.  No coupling parameter occurs.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

lemma image_action_open (D : Data n) {U : Set (Vec n)} (hU : IsOpen U) (hUA : U ⊆ axes n) :
    IsOpen (action D '' U) := by
  have hc : Continuous (axis D) :=
    continuous_pi fun i => ((continuous_apply i).pow 2).div_const _
  have : action D '' U = actionDomain D ∩ axis D ⁻¹' U := by
    ext I
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hUA ha, rfl⟩, by simpa [axis_action D a (hUA ha)] using ha⟩
    · rintro ⟨hI, hU'⟩
      obtain ⟨a, ha, rfl⟩ := hI
      exact ⟨a, by simpa [axis_action D a ha] using hU', rfl⟩
  rw [this]
  exact (action_diffeomorphism D).2.2.2.1.inter (hU.preimage hc)

lemma exists_good_patch (D : Data n) (hn : 2 ≤ n) {aStar : Vec n} (ha : aStar ∈ axes n)
    {η : ℝ} (hη : 0 < η) {r : ℕ} (f : Fin r → Vec n → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) (axes n)) (hne : ∀ j, ∃ a ∈ axes n, f j a ≠ 0) :
    ∃ a0 : Vec n, ∃ r0 : ℝ, 0 < r0 ∧
      Metric.closedBall a0 (2*r0) ⊆ goodAxes D ∩ Metric.ball aStar η ∧
      ∀ a ∈ Metric.closedBall a0 (2*r0), ∀ j, f j a ≠ 0 := by
  have hgne : ∃ a ∈ axes n, good (sigma D a) ≠ 0 := by
    obtain ⟨a, ha, -, hnr⟩ := good_point D hn (ε := 1/2) (by norm_num) (by norm_num)
    exact ⟨a, ha, ((SecularSpectrum.good_set D).2.1 a ha).2 hnr⟩
  let F : Fin (r+1) → Vec n → ℝ := Fin.cons (fun a => good (sigma D a)) f
  have hF : ∀ j, AnalyticOnNhd ℝ (F j) (axes n) := fun j =>
    Fin.cases (motive := fun j => AnalyticOnNhd ℝ (F j) (axes n))
      (by simpa [F] using (SecularSpectrum.good_set D).1) (fun j => by simpa [F] using hf j) j
  have hFne : ∀ j, ∃ a ∈ axes n, F j a ≠ 0 := fun j =>
    Fin.cases (motive := fun j => ∃ a ∈ axes n, F j a ≠ 0)
      (by simpa [F] using hgne) (fun j => by simpa [F] using hne j) j
  obtain ⟨hopen, hdense, -⟩ := generic (isOpen_axes n) (isConnected_axes n) hF hFne
  obtain ⟨b, hbB, hbU⟩ := mem_closure_iff.1 (hdense ha) _ Metric.isOpen_ball
    (Metric.mem_ball_self hη)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 (hopen.inter Metric.isOpen_ball) b ⟨hbU, hbB⟩
  refine ⟨b, ρ / 4, by positivity, fun x hx => ?_, fun x hx j => ?_⟩
  · have hx' := hsub (Metric.closedBall_subset_ball (show 2 * (ρ / 4) < ρ by linarith) hx)
    exact ⟨⟨hx'.1.1, by simpa [F] using hx'.1.2 0⟩, hx'.2⟩
  · have hx' := hsub (Metric.closedBall_subset_ball (show 2 * (ρ / 4) < ρ by linarith) hx)
    simpa [F] using hx'.1.2 j.succ

/-- Joint good patch: all witnesses precede every coupling parameter (none occurs). -/
theorem interface (D : Data n) (hn : 2 ≤ n) {aStar : Vec n} (ha : aStar ∈ axes n)
    {η : ℝ} (hη : 0 < η) {r : ℕ} (f : Fin r → Vec n → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) (axes n)) (hne : ∀ j, ∃ a ∈ axes n, f j a ≠ 0) :
    ∃ a0 : Vec n, ∃ r0 α β : ℝ, ∃ μ0 : ℕ,
      0 < r0 ∧ 0 < α ∧ 0 < β ∧ 0 < μ0 ∧
      Metric.closedBall a0 (2*r0) ⊆ goodAxes D ∩ Metric.ball aStar η ∧
      (∀ a ∈ Metric.closedBall a0 (2*r0), ∀ j, f j a ≠ 0) ∧
      α = sInf {q : ℝ | ∃ a ∈ Metric.closedBall a0 r0, ∃ k ∈ k4 n,
        q = |∑ j, (k j : ℝ)*(2*sigma D a j)|} ∧
      (∀ a ∈ Metric.closedBall a0 r0, ∀ k ∈ k4 n,
        α ≤ |∑ j, (k j : ℝ)*(2*sigma D a j)|) ∧
      (let B := action D '' Metric.ball a0 (2*r0)
       let K := action D '' Metric.closedBall a0 r0
       IsOpen B ∧ IsConnected B ∧ IsCompact K ∧ K ⊆ B ∧ 0 < volume K ∧
       AnalyticOnNhd ℝ (frequency D) B ∧ rnd_def B (frequency D) ∧
       β = betaMu (frequency D) K μ0 ∧
       (∀ μ, 0 < μ → 0 < betaMu (frequency D) K μ → μ0 ≤ μ) ∧
       (∀ μ, μ0 ≤ μ → β ≤ betaMu (frequency D) K μ) ∧
       ∀ c ∈ sphere (n+n), ∀ I ∈ K, β ≤ jetMax (squaredForm (frequency D) c) μ0 I) := by
  classical
  obtain ⟨a0, r0, hr0, hsub, hfne⟩ := exists_good_patch D hn ha hη f hf hne
  have hsubG : Metric.closedBall a0 (2*r0) ⊆ goodAxes D := fun x hx => (hsub hx).1
  have hsubA : Metric.closedBall a0 (2*r0) ⊆ axes n := fun x hx => (hsubG hx).1
  have hsimple : Metric.closedBall a0 (2*r0) ⊆ simpleAxes D := fun x hx =>
    ⟨(hsubG hx).1, (discriminant_ne_zero_iff _).2 ((good_ne_zero_iff _).1 (hsubG hx).2).1⟩
  have hr : Metric.closedBall a0 r0 ⊆ Metric.closedBall a0 (2*r0) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hbb : Metric.ball a0 (2*r0) ⊆ Metric.closedBall a0 (2*r0) := Metric.ball_subset_closedBall
  have hsig : ContinuousOn (sigma D) (Metric.closedBall a0 (2*r0)) :=
    (sorted_analytic D).continuousOn.mono hsimple
  -- (b) the non-resonance constant
  set S : Set ℝ := {q : ℝ | ∃ a ∈ Metric.closedBall a0 r0, ∃ k ∈ k4 n,
    q = |∑ j, (k j : ℝ)*(2*sigma D a j)|} with hS
  have hSimg : S = (fun z : Vec n × (Fin n → ℤ) => |∑ j, (z.2 j : ℝ)*(2*sigma D z.1 j)|) ''
      (Metric.closedBall a0 r0 ×ˢ k4 n) := by
    ext q
    constructor
    · rintro ⟨a, haB, k, hk, rfl⟩; exact ⟨(a, k), ⟨haB, hk⟩, rfl⟩
    · rintro ⟨⟨a, k⟩, ⟨haB, hk⟩, rfl⟩; exact ⟨a, haB, k, hk, rfl⟩
  have hcont : ContinuousOn
      (fun z : Vec n × (Fin n → ℤ) => |∑ j, (z.2 j : ℝ)*(2*sigma D z.1 j)|)
      (Metric.closedBall a0 r0 ×ˢ k4 n) := by
    refine continuous_abs.comp_continuousOn (continuousOn_finsetSum _ fun j _ => ?_)
    have h1 : Continuous (fun z : Vec n × (Fin n → ℤ) => (z.2 j : ℝ)) :=
      (continuous_of_discreteTopology (f := fun k : Fin n → ℤ => (k j : ℝ))).comp continuous_snd
    have h2 : ContinuousOn (fun z : Vec n × (Fin n → ℤ) => sigma D z.1 j)
        (Metric.closedBall a0 r0 ×ˢ k4 n) :=
      ((continuous_apply j).comp_continuousOn
        (hsig.comp continuousOn_fst (fun z hz => hr hz.1)))
    exact h1.continuousOn.mul (continuousOn_const.mul h2)
  have hScpt : IsCompact S := by
    rw [hSimg]
    exact ((isCompact_closedBall a0 r0).prod (k4_finite n).isCompact).image_of_continuousOn hcont
  have hk0 : (Pi.single ⟨0, by omega⟩ 1 : Fin n → ℤ) ∈ k4 n := by
    have h1 : ∑ i, |(Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℤ) : Fin n → ℤ) i| = 1 := by
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    rw [show (k4 n) = {k | 0 < ∑ i, |k i| ∧ ∑ i, |k i| ≤ 4} from rfl]
    exact ⟨by rw [h1]; exact one_pos, by rw [h1]; norm_num⟩
  have hSne : S.Nonempty :=
    ⟨_, a0, Metric.mem_closedBall_self hr0.le, _, hk0, rfl⟩
  obtain ⟨a1, ha1, k1, hk1, hα⟩ := hScpt.sInf_mem hSne
  have hαpos : 0 < sInf S := by
    rw [hα]
    have hnr := ((good_ne_zero_iff _).1 (hsubG (hr ha1)).2).2 k1 hk1
    have : ∑ j, (k1 j : ℝ)*(2*sigma D a1 j) = 2 * ∑ j, (k1 j : ℝ)*sigma D a1 j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, abs_pos]
    exact mul_ne_zero two_ne_zero (by simpa using hnr)
  have hαle : ∀ a ∈ Metric.closedBall a0 r0, ∀ k ∈ k4 n,
      sInf S ≤ |∑ j, (k j : ℝ)*(2*sigma D a j)| := fun a haB k hk =>
    csInf_le (hScpt.bddBelow) ⟨a, haB, k, hk, rfl⟩
  -- (c) the action-variable patch
  have hballA : Metric.ball a0 (2*r0) ⊆ axes n := hbb.trans hsubA
  have hcontA : ContinuousOn (action D) (axes n) :=
    (action_diffeomorphism D).2.2.2.2.1.continuousOn
  have hBopen : IsOpen (action D '' Metric.ball a0 (2*r0)) :=
    image_action_open D Metric.isOpen_ball hballA
  have hBconn : IsConnected (action D '' Metric.ball a0 (2*r0)) :=
    (IsConnected.image ⟨⟨a0, Metric.mem_ball_self (by linarith)⟩,
      (convex_ball a0 (2*r0)).isPreconnected⟩ _ (hcontA.mono hballA))
  have hKcpt : IsCompact (action D '' Metric.closedBall a0 r0) :=
    (isCompact_closedBall a0 r0).image_of_continuousOn (hcontA.mono (hr.trans hsubA))
  have hKB : action D '' Metric.closedBall a0 r0 ⊆ action D '' Metric.ball a0 (2*r0) :=
    image_mono (Metric.closedBall_subset_ball (by linarith))
  have hKvol : 0 < volume (action D '' Metric.closedBall a0 r0) := by
    have hV : IsOpen (action D '' Metric.ball a0 r0) :=
      image_action_open D Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans (hr.trans hsubA))
    exact lt_of_lt_of_le (hV.measure_pos volume ⟨_, a0, Metric.mem_ball_self hr0, rfl⟩)
      (measure_mono (image_mono Metric.ball_subset_closedBall))
  have hKne : (action D '' Metric.closedBall a0 r0).Nonempty :=
    ⟨_, a0, Metric.mem_closedBall_self hr0.le, rfl⟩
  have hballS : Metric.ball a0 (2*r0) ⊆ simpleAxes D := hbb.trans hsimple
  obtain ⟨-, -, hAn, hRnd, -, -⟩ := rnd D hn Metric.isOpen_ball
    ⟨⟨a0, Metric.mem_ball_self (by linarith)⟩, (convex_ball a0 (2*r0)).isPreconnected⟩ hballS
  -- (d) index and amount
  have hm : 0 < n + n := by omega
  have hex : ∃ μ : ℕ, 0 < μ ∧ 0 < betaMu (frequency D) (action D '' Metric.closedBall a0 r0) μ := by
    obtain ⟨μ, hμ, hβ, -⟩ := cp09_lemma1 hm hBopen hBconn hKcpt hKne hKB hAn hRnd
    exact ⟨μ, hμ, hβ⟩
  have hspec := Nat.find_spec hex
  have hmono : Monotone (betaMu (frequency D) (action D '' Metric.closedBall a0 r0)) :=
    betaFamily_mono (sphere_nonempty hm) hKne
  refine ⟨a0, r0, sInf S, betaMu (frequency D) (action D '' Metric.closedBall a0 r0) (Nat.find hex),
    Nat.find hex, hr0, hαpos, hspec.2, hspec.1, hsub, hfne, rfl, hαle, ?_⟩
  dsimp only
  refine ⟨hBopen, hBconn, hKcpt, hKB, hKvol, hAn, hRnd, rfl,
    fun μ hμ hβ => Nat.find_min' hex ⟨hμ, hβ⟩, fun μ hμ => hmono hμ, ?_⟩
  intro c hc I hI
  exact betaFamily_le hc hI

end Nondegeneracy
end KAM.Planetary
end
