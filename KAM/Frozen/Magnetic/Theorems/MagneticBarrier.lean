/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Analytic.Basic
public import KAM.Frozen.Magnetic.Defs.MagField
public import KAM.Frozen.Magnetic.Defs.MagAlpha
public import KAM.Frozen.Magnetic.Defs.MagHamC
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.InvarianceError
import KAM.Provider.Magnetic.MagneticBarrier

/-!
# Frozen theorem `KAM.Magnetic.magnetic_barrier`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432, with the `ℝ × ℝ × ℝ` state-type exception). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Magnetic.magnetic_barrier` when the provider `KAM.Provider.Magnetic.MagneticBarrier`
is complete (sealing).
-/

@[expose] public section

namespace KAM.Magnetic

/-- **Magnetic transport barrier.** The field-line flow of the controlled model at `ε = 3/2500`
has a real-analytic invariant graph `p = P(q, φ)`, one-periodic in both angles, with
`8/25 ≤ P ≤ 39/100`, which no field line crosses: every initial point has a global field line,
which every local field line through it on an interval containing `0` agrees with, and the side
of the graph (below, on, above) is the same at every real time. The graph is the action component of
an analytic primary invariant torus `K∞` of the extended Hamiltonian `magHamC`, holomorphic on the
strip of width `3/1000000`, real on real angles, with frequency `(α, 1)` (`α = magAlpha`), energy
zero and clock `φ = θ₁` (plan-magnetic-barrier §1.2). -/
theorem magnetic_barrier :
    ∃ P : ℝ → ℝ → ℝ,
      AnalyticOnNhd ℝ (fun x : ℝ × ℝ => P x.1 x.2) Set.univ ∧
      (∀ q φ, P (q + 1) φ = P q φ) ∧ (∀ q φ, P q (φ + 1) = P q φ) ∧
      (∀ q φ, 8 / 25 ≤ P q φ ∧ P q φ ≤ 39 / 100) ∧
      (∃ K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
        DifferentiableOn ℂ K (complexStrip 2 (3 / 1000000)) ∧
        IsPrimaryOnStrip K (3 / 1000000) ∧ IsRealOnReals K ∧
        (∀ θ ∈ complexStrip 2 (3 / 1000000), invarianceError magHamC K ![magAlpha, 1] θ = 0) ∧
        (∀ θ ∈ complexStrip 2 (3 / 1000000), magHamC (K θ) = 0) ∧
        ∀ θ : Fin 2 → ℝ,
          (K (fun i => (θ i : ℂ))).1 1 = θ 1 ∧
          (K (fun i => (θ i : ℂ))).2 0 = (P ((K (fun i => (θ i : ℂ))).1 0).re (θ 1) : ℂ)) ∧
      ∀ x₀ : ℝ × ℝ × ℝ, ∃ z : ℝ → ℝ × ℝ × ℝ,
        z 0 = x₀ ∧ (∀ t, HasDerivAt z (magField (z t)) t) ∧
        (∀ (I : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = x₀ →
          (∀ t ∈ I, HasDerivAt y (magField (y t)) t) → ∀ t ∈ I, y t = z t) ∧
        ∀ t : ℝ,
          (x₀.2.1 < P x₀.1 x₀.2.2 → (z t).2.1 < P (z t).1 (z t).2.2) ∧
          (x₀.2.1 = P x₀.1 x₀.2.2 → (z t).2.1 = P (z t).1 (z t).2.2) ∧
          (P x₀.1 x₀.2.2 < x₀.2.1 → P (z t).1 (z t).2.2 < (z t).2.1) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Magnetic

end
-- FROZEN_ANCHOR_SUFFIX_END
