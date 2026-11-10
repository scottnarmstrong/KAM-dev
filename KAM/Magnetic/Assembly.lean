/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.TorusCert
public import KAM.Magnetic.Flow
public import KAM.Magnetic.Freq
public import KAM.Frozen.Magnetic.Defs.MagField
public import KAM.Frozen.Magnetic.Defs.MagHamC
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.InvarianceError

/-!
# The magnetic barrier from a passing v2 certificate

`magnetic_barrier_of_V2`: the statement of the frozen `KAM.Magnetic.magnetic_barrier`, for any
magnetic graph certificate `g` (backend `MagBackend`) whose Hamiltonian is `magHamExpr`, whose
parameters are `magParams err disp`, which passes the v2 certifier `routeAV2` at the witness `w`
and the graph check, whose frequency box encloses `algFreq 2 magCoeffs √5`, and whose graph range
widened by `disp` lies in `[8/25, 39/100]`. It is a conditional helper over certificate data (not a
source result): the provider discharges every hypothesis by kernel computations on the emitted data.

* the torus, graph and field-line conjuncts: `magnetic_torus_of_V2` (`TorusCert.lean`), with the
  Diophantine premise `magFreq_isDiophantine` (`Freq.lean`);
* the flow conjunct: `magnetic_flow_of_invariant` (`Flow.lean`), with the graph's invariance from
  its field lines (`magGraphInvariant_of_orbits`) and its continuity from analyticity.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit

/-- **The magnetic barrier from a passing v2 certificate** (conditional helper): the frozen
statement of `magnetic_barrier`, from the signed data conclusions of a magnetic certificate. -/
theorem magnetic_barrier_of_V2 (g : SoGraphCert MagBackend) (w : routeAV2.Wit) (err disp : ℚ)
    (hham : g.base.ham = magHamExpr) (hpar : g.base.params = magParams err disp)
    (hc : checkTorusCertificateV2 routeAV2 g.base w = true) (hg : checkSoGraph g = true)
    (hω : FreqEncloses 2 g.base.freqBox (algFreq 2 magCoeffs (Real.sqrt 5)))
    (hlo : 8 / 25 ≤ g.pLo - disp) (hhi : g.pHi + disp ≤ 39 / 100) :
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
          (P x₀.1 x₀.2.2 < x₀.2.1 → P (z t).1 (z t).2.2 < (z t).2.1) := by
  obtain ⟨P, han, hq, hφ, hb, hK, horb⟩ := magnetic_torus_of_V2 g w err disp hham hpar hc hg hω
    magFreq_isDiophantine hlo hhi
  exact ⟨P, han, hq, hφ, hb, hK,
    magnetic_flow_of_invariant han.continuous (magGraphInvariant_of_orbits horb)⟩

end KAM.Magnetic

end
