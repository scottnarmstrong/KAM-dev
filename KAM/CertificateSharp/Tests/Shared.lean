/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.Shared
public import KAM.Certificate.Tests.Toy2
public import KAM.Certificate.Tests.Toy3
public import KAM.Certificate.Tests.Toy2d

/-!
# The pruned and shared compose on the toy certificates

For T2, T3 and T2d (`Tests/Toy2`, `Tests/Toy3`, `Tests/Toy2d`, read-only), kernel evaluation of:

* the live closure of `v0 :: d1Slots` is verified (`pruneOk`) and strictly smaller than the jet
  program (T2d: 156 operations, 60 live, of which 29 of 92 products, exps and reciprocals);
* `checkInvEnShared` and the full `checkTorusCertificateShared oldEngine` pass;
* the landed `checkInvariance && checkEnergy` pass (`toyCert{2,3}_passes`, in the toy files), so
  the shared check agrees with them on the toys.

`toyCert2_shared_sound` instantiates the soundness theorem.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- The jet program of `c` and the number of operations the shared compose runs. -/
def liveCount {n : ℕ} (c : TorusCertificate n ℚ) : ℕ × ℕ :=
  (c.ham.jet.prog.ops.length, (liveSet c.ham.jet.prog.ops (wantedInvEn n c.ham.jet)).length)

theorem toyCert2_prune_ok : pruneOk toyCert2.ham.jet.prog.ops (wantedInvEn 2 toyCert2.ham.jet)
    (liveSet toyCert2.ham.jet.prog.ops (wantedInvEn 2 toyCert2.ham.jet)) = true := by
  decide +kernel

theorem toyCert3_prune_ok : pruneOk toyCert3.ham.jet.prog.ops (wantedInvEn 3 toyCert3.ham.jet)
    (liveSet toyCert3.ham.jet.prog.ops (wantedInvEn 3 toyCert3.ham.jet)) = true := by
  decide +kernel

theorem toyCert2_shared : checkInvEnShared toyCert2 = true := by decide +kernel
theorem toyCert3_shared : checkInvEnShared toyCert3 = true := by decide +kernel

theorem toyCert2_shared_passes : checkTorusCertificateShared oldEngine toyCert2 = true := by
  decide +kernel
theorem toyCert3_shared_passes : checkTorusCertificateShared oldEngine toyCert3 = true := by
  decide +kernel

theorem toyCert2d_prune_ok : pruneOk toyCert2d.ham.jet.prog.ops (wantedInvEn 2 toyCert2d.ham.jet)
    (liveSet toyCert2d.ham.jet.prog.ops (wantedInvEn 2 toyCert2d.ham.jet)) = true := by
  decide +kernel

/-- T2d: the jet has 156 operations, the shared compose runs 60. -/
theorem toyCert2d_liveCount : liveCount toyCert2d = (156, 60) := by decide +kernel

theorem toyCert2d_shared : checkInvEnShared toyCert2d = true := by decide +kernel

theorem toyCert2d_shared_passes : checkTorusCertificateShared oldEngine toyCert2d = true := by
  decide +kernel

/-- Soundness instantiated on T2: the conclusion is about the real torus data. -/
theorem toyCert2_shared_sound {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 toyCert2.freqBox ωstar)
    (hdio : KAM.IsDiophantine (toyCert2.params.γ : ℝ) (toyCert2.params.tau : ℝ) ωstar) :
    CertifiedTorus toyCert2 ωstar :=
  checkTorusCertificateShared_sound oldEngine toyCert2_shared_passes hω hdio

end KAM.CertificateSharp
