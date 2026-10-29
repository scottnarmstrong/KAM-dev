/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Defs
public import KAM.Iso.Linear.Tools
public import KAM.Apost.Frame

/-!
# Part 2 (isoenergetic iteration): the standing data, the ray, the frequency bound

Blueprint nodes `bpI:p2:standing#k-bridge`,
`bpI:p2:ray` and the display `bpI:p2:freq` of `bpI:p2:admissible`.

* `IsoStanding.setting` (`bpI:p2:standing#k-bridge`): for `s ≥ 1` the Part 1 setting (hence track
  K's `Standing`, through `Setting.toStanding`) holds at `s ω*`.
* `ray` (`bpI:p2:ray` (a), (b)): the Diophantine class of `s ω*`, the coordinate bound
  `γ ≤ |ω*₁| ≤ ‖ω*‖`, the distance identity `‖s' ω* - s ω*‖ = |s' - s| ‖ω*‖` and the Lipschitz
  property of the endpoint margin `rayMargin` (`ν(s)`), with the "in particular" clause.
* `IsoAdmissible.freq` (`bpI:p2:admissible`, display `bpI:p2:freq`): `γ ≤ ‖s ω*‖ ≤ Θ`, from
  `KAM.Apost.frequency` (`bp:p2:frequency`).

The definitions `IsoStanding`, `rayMargin`, `IsoAdmissible` live in `KAM.Iso.Apost.Defs`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

variable {n : ℕ}

/-- `bpI:p2:standing#k-bridge`: for `s ≥ 1` the Part 1 setting (hence K's standing) holds at
`sω*`. -/
theorem IsoStanding.setting {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
    {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {s : ℝ} (hs : 1 ≤ s) :
    Setting n τ M σK σB σT D H (s • ωstar) γ :=
  { toParams := hS.toParams
    isOpen := hS.isOpen
    transl_mem := hS.transl_mem
    holo := hS.holo
    periodic := hS.periodic
    real := hS.real
    bounds := fun z hz =>
      ⟨(hS.bounds z hz).2.1, (hS.bounds z hz).2.2.1, (hS.bounds z hz).2.2.2.1⟩
    gamma_pos := hS.gamma_pos
    dio := isDiophantine_smul hS.dio hs
    dH_le := fun z hz => (hS.bounds z hz).1 }

/-- `bpI:p2:ray` (a), (b). -/
theorem ray {γ τ σω : ℝ} {ωstar : Fin n → ℝ} (hdio : IsDiophantine γ τ ωstar) :
    (∀ s : ℝ, 0 < s → IsDiophantine (γ * s) τ (s • ωstar)) ∧
    (∀ s : ℝ, 1 ≤ s → IsDiophantine γ τ (s • ωstar)) ∧
    (∀ hn : 0 < n, γ ≤ |ωstar ⟨0, hn⟩| ∧ |ωstar ⟨0, hn⟩| ≤ ‖ωstar‖) ∧
    (∀ s s' : ℝ, ‖s' • ωstar - s • ωstar‖ = |s' - s| * ‖ωstar‖) ∧
    (∀ s s' : ℝ, rayMargin σω ωstar s - ‖s' • ωstar - s • ωstar‖ ≤ rayMargin σω ωstar s') ∧
    ∀ s s' ν' d : ℝ, ν' ≤ rayMargin σω ωstar s → ‖s' • ωstar - s • ωstar‖ ≤ d → d < ν' →
      1 < s' ∧ s' < σω ∧ ν' - d ≤ rayMargin σω ωstar s' := by
  -- the distance identity, used twice
  have hdist : ∀ s s' : ℝ, ‖s' • ωstar - s • ωstar‖ = |s' - s| * ‖ωstar‖ := fun s s' => by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  -- the margin is Lipschitz along the ray
  have hlip : ∀ s s' : ℝ, rayMargin σω ωstar s - ‖s' • ωstar - s • ωstar‖ ≤
      rayMargin σω ωstar s' := fun s s' => by
    rw [hdist, rayMargin, rayMargin, ← sub_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : s - 1 - |s' - s| ≤ s' - 1 := by
      have := neg_abs_le (s' - s)
      linarith
    have h2 : σω - s - |s' - s| ≤ σω - s' := by
      have := le_abs_self (s' - s)
      linarith
    refine le_min ?_ ?_
    · linarith [min_le_left (s - 1) (σω - s)]
    · linarith [min_le_right (s - 1) (σω - s)]
  refine ⟨?_, fun s hs => isDiophantine_smul hdio hs, ?_, hdist, hlip, ?_⟩
  · -- (a): scaling by `s > 0`
    intro s hs k hk
    have hsum : ∑ i, (k i : ℝ) * (s • ωstar) i = s * ∑ i, (k i : ℝ) * ωstar i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsum, abs_mul, abs_of_pos hs, mul_div_right_comm]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hdio k hk) hs.le
  · -- (c): the first coordinate, the Diophantine inequality at `k = e₁`
    intro hn
    refine ⟨?_, by simpa using norm_le_pi_norm ωstar ⟨0, hn⟩⟩
    set i₀ : Fin n := ⟨0, hn⟩ with hi₀
    have hk : (Pi.single i₀ (1 : ℤ) : Fin n → ℤ) ≠ 0 := by
      intro h0
      have := congrFun h0 i₀
      simp at this
    have h1 := hdio _ hk
    have hsum : (∑ i, |(((Pi.single i₀ (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ)|) = 1 := by
      rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have hsum2 : (∑ i, (((Pi.single i₀ (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) * ωstar i) =
        ωstar i₀ := by
      simp [Pi.single_apply]
    rwa [hsum, hsum2, Real.one_rpow, div_one] at h1
  · -- (b), the "in particular" clause
    intro s s' ν' d hν' hd hdν
    have hmargin : ν' - d ≤ rayMargin σω ωstar s' := by
      have := hlip s s'
      linarith
    have hpos : 0 < rayMargin σω ωstar s' := by linarith
    have hmin : 0 < min (s' - 1) (σω - s') := by
      by_contra hneg
      exact absurd (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (norm_nonneg ωstar))
        (not_le.2 hpos)
    exact ⟨by linarith [(lt_min_iff.1 hmin).1], by linarith [(lt_min_iff.1 hmin).2], hmargin⟩

/-- The display `bpI:p2:freq` of Definition `bpI:p2:admissible`: `γ ≤ |ω| ≤ Θ`. -/
theorem IsoAdmissible.freq {τ M σK σB σT σω ν γ E₀ r β ε s : ℝ} {ωstar : Fin n → ℝ}
    {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) :
    γ ≤ ‖s • ωstar‖ ∧ ‖s • ωstar‖ ≤ Theta n M σK σB σT := by
  obtain ⟨h1, h2, h3⟩ := frequency (hS.setting hK.s_gt.le).toStanding hK.r_pos hK.ε_le_one
    (fun θ hθ => hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)) hK.deriv_le hK.gram
    hK.error_le
  exact ⟨h1, h2.trans h3⟩

end KAM.Iso.Apost
