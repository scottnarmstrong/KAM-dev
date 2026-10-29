/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Assembly
public import KAM.Planetary.Quantitative.Budget

/-!
# Quantitative weak KAM: the joint statement (K1)-(K6) (GAP-E)

`weak_kam_quantitative_full` (`bpP:p11a:weak-kam-quantitative`, `stepP:p11a:qt-k6`): for one
family `Q` (clauses K1-K4), the literal composed displacement bound (K6)
`sup |u_b| <= Delta <= cD * eps ^ (1/2) * beta ^ (-G0)`, with `cD` fixed after every entry but
`beta`, together with the polynomial threshold lower bound (K5).
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
namespace KAM.Planetary
open KAM

variable {N : ℕ}

/-- (K1)-(K6) for one family: `cDelta` depends on `(N, mu, tau, s, C1)` only, `cD` on every
entry but `beta` (the data `d` carries a reference `beta`, replaced by `b`). -/
theorem weak_kam_quantitative_full (N mu : ℕ) (tau s C1 : ℝ) :
    ∃ cDelta : ℝ, 0 < cDelta ∧ ∀ d : QuantitativeData N,
      d.Valid → d.mu = mu → d.tau = tau → d.s = s → d.C1 = C1 →
      ∃ cD : ℝ, 0 < cD ∧
        (∃ c : ℝ, 0 < c ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
          c * b ^ p11c_B0 d ≤ thresholds { d with beta := b }) ∧
        ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
          ∀ h f, QuantitativeInput { d with beta := b } h f → ∀ eps : ℝ, 0 ≤ eps →
          eps ≤ thresholds { d with beta := b } →
          (∀ z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ eps) →
          ∃ Q : QuantitativeFamily { d with beta := b } (realHamiltonian h f) cDelta eps,
            ∀ b' ∈ Q.good, ∀ θ,
              ‖Q.torus b' θ - (θ, b')‖ ≤ cD * eps ^ (1 / 2 : ℝ) * b ^ (-p11c_G0 d) := by
  obtain ⟨cDelta, hc, hQ⟩ := weak_kam_quantitative N mu tau s C1
  refine ⟨cDelta, hc, fun d hd hmu htau hs hC1 => ?_⟩
  obtain ⟨cD, hcD, hflat⟩ := displacement_power_flat d hd cDelta hc
  refine ⟨cD, hcD, qb_beta d hd.1, fun b hb h f hh eps he0 heps hf => ?_⟩
  have hbM : b ≤ d.M := hb.2.trans (min_le_right _ _)
  have hvalid : ({ d with beta := b } : QuantitativeData N).Valid :=
    ⟨qbBeta_valid hd.1 hb.1 hbM, hd.2.1, hb.2.trans (min_le_left _ _)⟩
  obtain ⟨Q⟩ := hQ { d with beta := b } hvalid hmu htau hs hC1 h f hh eps he0 heps hf
  exact ⟨Q, fun b' hb' θ => (Q.displacement b' hb' θ).trans (hflat b hb eps he0)⟩

end KAM.Planetary

end
