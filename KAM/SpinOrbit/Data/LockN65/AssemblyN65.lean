/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Passes
public import KAM.SpinOrbit.Lock.Graph
public import KAM.SpinOrbit.Data.LockN65.LockGraphK
public import KAM.SpinOrbit.Lock.Assembly

/-!
# The Moon locked in synchronous rotation: the N = 65 librational certificate

`lunar_sync_lock_N65` is the conclusion of the frozen `KAM.SpinOrbit.lunar_sync_lock`, proved from
the kernel-checked N = 65 lock certificate:

* `lockBarrier_of_certV2K` (`lockBarrier_of_certV2` with the graph check `checkSoGraphK`) turns the
  passing v2 certificate (`lock_passes`), the passing graph certificate (`lockGraph_passes`), the
  frequency enclosure (`lock_freq`) and the Diophantine property of `lunarRotFreq (lunarNuPlusN 65)
  1` (`lunarRotFreqPlusN_isDiophantine_65`, with the certificate's `γ = 1/67`, `τ = 1`) into a
  librational barrier for `Ω = 8/65` around `lunarLockCentre`, with action range `[pLo - disp, pHi +
  disp]`;
* `lunar_sync_lock_of_barrier_check` (the conditional helper of `Lock/Assembly.lean`) gives the
  headline shape on the window `[13155/1000000, 163/10000]` with a passing literal check.

The only hypothesis is the frozen statement's own
`libAction lunarOmega lunarSyncOrbit … < 129/10000`.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith
open KAM.SpinOrbit.Lock

/-- The literal check on the certified window `[13155/1000000, 163/10000]`. -/
theorem lock_literalCheck65 :
    lockLiteralCheck lunarOmega lunarLockCentre (13155 / 1000000) (163 / 10000) (17 / 1000000)
      (27 / 200000) (129 / 10000) (21 / 100) (26 / 1000) = true := by
  decide +kernel

/-- The Diophantine property of the certified frequency, at the certificate's `γ` and `τ`. -/
theorem lock_dio :
    IsDiophantine ((cert.graph.base.params.γ : ℚ) : ℝ) ((cert.graph.base.params.tau : ℚ) : ℝ)
      (lunarRotFreq (lunarNuPlusN 65) 1) := by
  have h := lunarRotFreqPlusN_isDiophantine_65 (κ := 1) one_pos
  have hγ : ((cert.graph.base.params.γ : ℚ) : ℝ) = ((1 : ℚ) : ℝ) / 67 := by
    rw [show cert.graph.base.params.γ = 1 / 67 from rfl]
    push_cast
    ring
  have hτ : ((cert.graph.base.params.tau : ℚ) : ℝ) = 1 := by
    rw [show cert.graph.base.params.tau = 1 from rfl]
    push_cast
    rfl
  rw [hγ, hτ]
  exact h

/-- The librational barrier of the N = 65 lock certificate. (The centre map is named in full:
inside this namespace `lockCentre` is the certificate's data `List ℚ` of `Domain`.) -/
theorem lock_barrier :
    Nonempty (LockBarrier ((cert.Ω : ℚ) : ℝ) (KAM.SpinOrbit.Lock.lockCentre cert.cs)
      ((cert.graph.pLo : ℝ) - cert.graph.base.params.disp)
      ((cert.graph.pHi : ℝ) + cert.graph.base.params.disp)) :=
  lockBarrier_of_certV2K cert (by decide +kernel) (by decide +kernel) rfl (by
      have h : (0 : ℚ) < cert.graph.pLo - cert.graph.base.params.disp := by decide +kernel
      exact_mod_cast h)
    lock_passes lockGraph_passes lock_freq lock_dio

/-- **The Moon locked in synchronous rotation** (the conclusion of the frozen
`KAM.SpinOrbit.lunar_sync_lock`), from the N = 65 certificate. -/
theorem lunar_sync_lock_N65 (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  obtain ⟨B⟩ := lock_barrier
  have hlo : (13155 / 1000000 : ℚ) ≤ cert.graph.pLo - cert.graph.base.params.disp := by
    decide +kernel
  have hhi : cert.graph.pHi + cert.graph.base.params.disp ≤ (163 / 10000 : ℚ) := by
    decide +kernel
  have := lunar_sync_lock_of_barrier_check (Ω := lunarOmega) (cs := lunarLockCentre)
    (lo := 13155 / 1000000) (hi := 163 / 10000) B (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    lock_literalCheck65 q₀ p₀ φ₀ (by push_cast; exact h₀)
  push_cast at this
  exact this

end KAM.SpinOrbit.Data.LockN65
