/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes.N2
public import KAM.Planetary.Nondegeneracy.GoodAxes.SortedAnalytic
public import KAM.Planetary.Nondegeneracy.GoodAxes.Induction

/-!
# Good axes

Blueprint P, Part 10 (`bpP:p10:n2`, `bpP:p10:sorted-analytic`, `bpP:p10:good-point`,
`bpP:p10:good-set`).  This facade imports `GoodAxes.N2` (`n2`), `GoodAxes.SortedAnalytic`
(`sorted_analytic`) and `GoodAxes.Induction` (`good_point`), and proves `good_set`: the good set
`{Φ₄ ≠ 0}` is open, dense, of full measure in the connected set `axes n`, and contains closed cubes
inside every ball.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

lemma convex_axes (n : ℕ) : Convex ℝ (axes n) := by
  intro a ha b hb s t hs ht hst
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := ha.1 i; have := hb.1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.eq_or_lt with h | h
    · subst h; have : t = 1 := by linarith
      subst this; simpa using hb.1 i
    · nlinarith
  · have h1 := ha.2 hij; have h2 := hb.2 hij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.eq_or_lt with h | h
    · subst h; have : t = 1 := by linarith
      subst this; simpa using h2
    · nlinarith

lemma isConnected_axes (n : ℕ) : IsConnected (axes n) :=
  ⟨⟨fun i => (i.val : ℝ) + 1, fun i => by positivity, fun i j hij => by
    simp only; exact_mod_cast Nat.add_lt_add_right hij 1⟩,
    (convex_axes n).isPreconnected⟩

theorem good_set (D : Data n) (hn : 2 ≤ n) :
    IsOpen (goodAxes D) ∧ axes n ⊆ closure (goodAxes D) ∧
    volume (axes n \ goodAxes D) = 0 ∧
    ∀ a ∈ axes n, ∀ η : ℝ, 0 < η → ∃ a0 : ℝ, ∃ r : Vec n,
      0 < a0 ∧ Metric.closedBall r (2*a0) ⊆ goodAxes D ∩ Metric.ball a η := by
  have hne : ∃ a ∈ axes n, good (sigma D a) ≠ 0 := by
    obtain ⟨a, ha, -, hnr⟩ := good_point D hn (ε := 1/2) (by norm_num) (by norm_num)
    exact ⟨a, ha, ((SecularSpectrum.good_set D).2.1 a ha).2 hnr⟩
  have hdi := good_set_dichotomy D (isOpen_axes n) (isConnected_axes n) subset_rfl
  have h3 : IsOpen (goodAxes D) ∧ axes n ⊆ closure (goodAxes D) ∧
      volume (axes n \ goodAxes D) = 0 := by
    rcases hdi with h | ⟨ho, hc, hv⟩
    · obtain ⟨a, ha, hg⟩ := hne
      exact absurd (h a ha) hg
    · refine ⟨ho, hc, ?_⟩
      convert hv using 2
      ext a; simp [goodAxes]
  obtain ⟨hopen, hcl, hvol⟩ := h3
  refine ⟨hopen, hcl, hvol, fun a ha η hη => ?_⟩
  obtain ⟨b, hbB, hbG⟩ := mem_closure_iff.1 (hcl ha) _ Metric.isOpen_ball
    (Metric.mem_ball_self hη)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 (hopen.inter Metric.isOpen_ball) b ⟨hbG, hbB⟩
  refine ⟨ρ / 4, b, by positivity, fun x hx => hsub ?_⟩
  exact Metric.closedBall_subset_ball (show 2 * (ρ / 4) < ρ by linarith) hx

end Nondegeneracy
end KAM.Planetary
end
