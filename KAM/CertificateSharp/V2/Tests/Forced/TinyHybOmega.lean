/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1HybData
public import KAM.CertificateSharp.Hybrid.Claims

/-!
# The Lagrange matrices of the hybrid step on the forced toy `Tiny`

`(S6)`, `(S7)` of `Hybrid.hybStepOk` at the Newton step `hybDK` (`TinyL1HybData`), by one kernel
run: `‖Ω_K‖` and `‖Ω_{K + ΔK}‖` (`Mᵀ Ω₀ M` for `M = DK`, `D(K + ΔK)`, from the entry models at the
weight of the torsion strip and of `T_{ρ∞}`, the latter bounded on the real torus) against the
claims `o0`, `o1`, `o0R`, `o1R` (direct products of the derivative models).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem hyb_omega : Hybrid.hybOmegaOk cert hybWit.step = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
