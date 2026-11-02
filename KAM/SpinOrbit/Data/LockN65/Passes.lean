/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.Data.LockN65.Core
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.RotFreqN
public import KAM.SpinOrbit.Data.LockN65.Pass.Static
public import KAM.SpinOrbit.Data.LockN65.Pass.HamBounds
public import KAM.SpinOrbit.Data.LockN65.Pass.Embedding
public import KAM.SpinOrbit.Data.LockN65.Pass.HamClaim
public import KAM.SpinOrbit.Data.LockN65.Pass.FrameL
public import KAM.SpinOrbit.Data.LockN65.Pass.FrameOm
public import KAM.SpinOrbit.Data.LockN65.Pass.GraphS
public import KAM.SpinOrbit.Data.LockN65.Pass.GraphM
public import KAM.SpinOrbit.Data.LockN65.Pass.GraphL
public import KAM.SpinOrbit.Data.LockN65.Pass.GraphH
public import KAM.SpinOrbit.Data.LockN65.GraphK
public import KAM.SpinOrbit.Data.LockN65.Seg.Checks
public import KAM.SpinOrbit.Data.LockN65.Seg.Checks.Torsion
public import KAM.SpinOrbit.Data.LockN65.Seg.Checks.FrameN
public import KAM.SpinOrbit.Data.LockN65.Seg.Checks.FrameT

/-!
# The N = 65 lock: the passing checks

The v2 certifier at the refined-route witness (`checkTorusCertificateV2 routeAV2 base
(Sum.inr (Sum.inr refinedWit)) = true`), the graph certifier (`checkSoGraphK graph = true`, a key
per SOS square) and
the frequency enclosure, assembled from the kernel-checked parts: the static, Hamiltonian,
embedding, claim and frame checks (`Pass/*`), the refined core (`Core`), and the segmented
invariance, energy, Gram and torsion checks (`Seg/Checks*`), as `Data/Upper/Passes.lean` for the
band data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

/-- The √5 enclosure of the data: `rootLo ≤ √5 ≤ rootHi`. -/
theorem lock_sqrtFive_mem :
    ((rootLo : ℚ) : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ ((rootHi : ℚ) : ℝ) := by
  have h1 : (0 : ℚ) ≤ rootLo := by decide +kernel
  have h2 : rootLo ^ 2 ≤ 5 := by decide +kernel
  have h3 : (0 : ℚ) ≤ rootHi := by decide +kernel
  have h4 : (5 : ℚ) ≤ rootHi ^ 2 := by decide +kernel
  constructor
  · rw [Real.le_sqrt (by exact_mod_cast h1) (by norm_num)]
    exact_mod_cast h2
  · rw [Real.sqrt_le_left (by exact_mod_cast h3)]
    exact_mod_cast h4

/-- The certificate's box encloses the frequency `lunarRotFreq (lunarNuPlusN 65) 1`. -/
theorem lock_freq : FreqEncloses 2 base.freqBox (lunarRotFreq (lunarNuPlusN 65) 1) := by
  rw [lunarRotFreqPlusN_eq]
  exact algFreq_encloses lock_sqrtFive_mem (by decide +kernel)

/-- The frame majorants of the claim, from the four parts. -/
theorem lock_frame : checkFrameMajorants base (refinedWit.R.frame base.freqBox) = true := by
  simp only [checkFrameMajorants, Bool.and_eq_true]
  exact ⟨⟨⟨lock_frameL, lock_csFrameN⟩, lock_csFrameT⟩, lock_frameOm⟩

/-- The v2 certifier at the refined-route witness. -/
theorem lock_passes :
    checkTorusCertificateV2 routeAV2 base (Sum.inr (Sum.inr refinedWit)) = true :=
  checkTorusCertificateV2_refined_of
    (landedBase_check_of lock_static lock_hamBounds lock_embedding lock_csInvariance
      lock_csEnergy lock_csGram lock_csTorsion)
    lock_hamClaim lock_frame lock_core

/-- The graph certifier, from its four conjuncts. -/
theorem lockGraph_passes : checkSoGraphK graph = true := by
  simp only [checkSoGraphK, Bool.and_eq_true]
  exact ⟨⟨⟨lock_graphS, lock_graphM⟩, lock_graphL⟩, lock_graphH⟩

end KAM.SpinOrbit.Data.LockN65
