/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Injective

/-!
# Planar quartic torsion: the lift of the slow flow (package T11)

Blueprint P, Part 11b (`bpP:p11b:lift-map`, with `stepP:p11b:lm-ham` and `stepP:p11b:lm-prop`):
the signed theorems `full_lift_hamiltonian` and `lift_map`, with the signed definitions
`p11c_liftFlow` and `p11c_tube` (in `Lift/Defs`).

* `full_lift_hamiltonian` verifies the full Hamilton equations (including the angle shift
  `∫ ∂_I chi`) for the Hamiltonian `(φ, q; I, p) ↦ chi I (q, p)` along an explicit orbit that
  starts at an assembled point and ends at its `p11c_liftFlow` image (`Lift/Field`, `Lift/Orbit`);
* `lift_map` proves that `p11c_liftFlow chi.eval` is an analytic symplectic injective map on
  `p11c_tube O' r` commuting with all angle translations.  Analyticity and symplecticity come from
  the real variational theory of package R3 applied to the full field (`Lift/Iterate`,
  `Lift/Inverse`); injectivity from the explicit inverse, the lift of `-chi` (`Lift/Injective`).
  The composition with the rotation lift is left to `PlanarBirkhoffResult` (design audit).

No complex `SmallField` hypothesis and no `KAM.Canonical` theorem is used.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- Same domain and physical Hamiltonian, the slow remainder bound cannot be assumed here. -/
theorem full_lift_hamiltonian {O O' : Set (Fin 2 → ℝ)} (hO : IsOpen O) (hO' : IsOpen O')
    (hK : IsCompact (closure O')) (hKO : closure O' ⊆ O) (chi : QuarticFamily O) :
    ∃ r : ℝ, 0 < r ∧ ∀ I ∈ O', ∀ lam : Fin 2 → ℝ, ∀ z : Phase 2,
      p11c_slowLength z < r → ∃ g : ℝ → Phase (2 + 2), g 0 = assemble I lam z.2 z.1 ∧
        g 1 = p11c_liftFlow chi.eval (assemble I lam z.2 z.1) ∧
        IsSolutionIn (hamiltonianVectorField (fun w : Phase (2 + 2) =>
          chi.eval (fun i => w.2 (Fin.castAdd 2 i))
            (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))))
          (p11c_tube O (2 * r)) (Icc (0 : ℝ) 1) g := by
  obtain ⟨C, r₁, hC, hr₁, -, hfl⟩ := flow hO chi (closure O') hK hKO
  have hfs : p11cL_FlowSpec chi.eval (closure O') (2 * (r₁ / 2)) := by
    rw [mul_div_cancel₀ _ two_ne_zero]
    exact fun I hI z hz => ⟨(hfl I hI z hz).1, (hfl I hI z hz).2.1, (hfl I hI z hz).2.2.1⟩
  obtain ⟨D, hD0, hD⟩ := p11cL_exists_bound chi hK hKO (2 * (r₁ / 2))
  refine ⟨r₁ / 2, by positivity, fun I hI lam z hz => ?_⟩
  obtain ⟨g, hg, hg0, hg1, hgb⟩ := p11cL_orbit_exists chi hKO (by positivity) hfs hD0 hD
    subset_closure (w := assemble I lam z.2 z.1) (by rw [p11cL_act_assemble]; exact hI)
    (by rw [p11cL_slow_assemble]; exact hz)
  refine ⟨g, hg0, hg1, fun t ht => ?_⟩
  have ht' : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hA, -, -, hen⟩ := hgb t ht
  refine ⟨⟨?_, ?_⟩, (hg t ht').2⟩
  · show p11cL_act (g t) ∈ O
    rw [hA, p11cL_act_assemble]; exact hKO (subset_closure hI)
  · show p11c_slowLength (p11cL_slow (g t)) < 2 * (r₁ / 2)
    rw [p11cL_slow_assemble] at hen
    have h0 : (0 : ℝ) ≤ p11c_slowLength z := Real.sqrt_nonneg _
    by_contra hc
    push_neg at hc
    nlinarith [mul_self_lt_mul_self h0 hz]

theorem lift_map {O O' : Set (Fin 2 → ℝ)} (hO : IsOpen O) (hO' : IsOpen O')
    (hK : IsCompact (closure O')) (hKO : closure O' ⊆ O) (chi : QuarticFamily O) :
    ∃ r : ℝ, 0 < r ∧ IsChart 1 (p11c_liftFlow chi.eval) (p11c_tube O' r) ∧
      InjOn (p11c_liftFlow chi.eval) (p11c_tube O' r) ∧
      ∀ w ∈ p11c_tube O' r, ∀ c : Fin 2 → ℝ,
        p11c_liftFlow chi.eval (w + (Fin.append c 0, 0)) =
          p11c_liftFlow chi.eval w + (Fin.append c 0, 0) := by
  obtain ⟨C, r₁, hC, hr₁, -, hfl⟩ := flow hO chi (closure O') hK hKO
  obtain ⟨C₂, r₂, hC₂, hr₂, -, hfl₂⟩ := flow hO (p11cL_negFamily chi) (closure O') hK hKO
  set r : ℝ := min (r₁ / 2) (r₂ / 2) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have h1 : 2 * r ≤ r₁ := by
    have := min_le_left (r₁ / 2) (r₂ / 2); linarith
  have h2 : 2 * r ≤ r₂ := by
    have := min_le_right (r₁ / 2) (r₂ / 2); linarith
  have hfs : p11cL_FlowSpec chi.eval (closure O') (2 * r) := fun I hI z hz =>
    ⟨(hfl I hI z (hz.trans_le h1)).1, (hfl I hI z (hz.trans_le h1)).2.1,
      (hfl I hI z (hz.trans_le h1)).2.2.1⟩
  have hfsn : p11cL_FlowSpec (fun J w => -chi.eval J w) (closure O') (2 * r) := by
    intro I hI z hz
    have h := hfl₂ I hI z (hz.trans_le h2)
    rw [p11cL_negFamily_eval] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hinv : ∀ I ∈ closure O', ∀ z : Phase 2, p11c_slowLength z < 2 * r →
      p11c_flow (fun J w => -chi.eval J w) I 1 (p11c_flow chi.eval I 1 z) = z :=
    fun I hI z hz => (hfl I hI z (hz.trans_le h1)).2.2.2.2
  exact ⟨r, hr0, p11cL_chart_tube hO hO' hK hKO chi hr0 hfs,
    p11cL_injOn chi hKO hr0 subset_closure hfs hfsn hinv,
    fun w _ c => p11cL_liftFlow_translate _ w c⟩

end KAM.Planetary

end
