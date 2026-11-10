/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import KAM.Frozen.Magnetic.Defs.MagField
public import KAM.Frozen.Magnetic.Defs.MagAlpha
public import KAM.Frozen.Magnetic.Defs.MagHamC
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Magnetic.Assembly
public import KAM.Magnetic.Data.Mag.Passes

/-!
# Provider for the frozen theorem `KAM.Magnetic.magnetic_barrier`

The proof of `KAM.Magnetic.magnetic_barrier` is assembled here as
`KAM.Provider.Magnetic.magnetic_barrier`, from graph predecessors and approved external inputs only.
While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.

* `KAM.Provider.Magnetic.magnetic_barrier` has exactly the type of the frozen theorem. It is one
  application of the conditional helper `KAM.Magnetic.magnetic_barrier_of_V2`
  (`KAM/Magnetic/Assembly.lean`) to the generated certificate `KAM.Magnetic.Data.Mag.cert`
  (`CertFixed 128`, route A refined with classical sites, `err = 7.3·10⁻²²`, `disp = 5.11·10⁻¹³`)
  and its kernel-checked data conclusions (`KAM/Magnetic/Data/Mag/Passes.lean`): the Hamiltonian
  and parameters by `rfl`, the v2 check and the graph check by the segmented kernel proof, the
  frequency box by `algFreq_encloses` from `checkAlgBox` and the √5 enclosure, and the two band
  inequalities `8/25 ≤ pLo − disp`, `pHi + disp ≤ 39/100` by `decide +kernel` on the literals.
-/

public section

namespace KAM.Provider.Magnetic

open KAM KAM.Certificate KAM.Magnetic KAM.Magnetic.Data.Mag

/-- The two band inequalities on the graph literals of the certificate. -/
theorem mag_band : (8 / 25 : ℚ) ≤ cert.pLo - magDisp ∧ cert.pHi + magDisp ≤ 39 / 100 := by
  decide +kernel

/-- **The magnetic transport barrier**: the provider of the frozen `KAM.Magnetic.magnetic_barrier`,
with exactly its type. -/
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
  magnetic_barrier_of_V2 cert (.inr (.inr refinedWit)) magErr magDisp mag_ham mag_params mag_passes
    magGraph_passes (algFreq_encloses mag_sqrtFive_mem mag_algBox) mag_band.1 mag_band.2

end KAM.Provider.Magnetic

end
