/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotData
public import KAM.CertificateSharp.V2.Tests.Forced.MicroFreq
public import KAM.CertificateSharp.LinearShear

/-!
# The reference frequency of the rotated forced toy `MicroRot`

`ω' = A ω* = (ω*₀ - ω*₁, ω*₁)` for `ω* = Micro.ωstar`, `A` the angle block of `shearMap⁻¹`. The
box of `MicroRot.cert` is the exact image of `Micro`'s (`box_eq`, `shearBox`), so it encloses `ω'`
(`freq`, from `Micro.freq` by `freqEncloses_shear`), and `ω'` is `(γ / 2, 1)`-Diophantine for the
`(γ, 1)` of `Micro` (`dio`, from `Micro.dio` by the transfer `isDiophantine_shear`), which is the
certificate's `(γ, τ)`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp.Linear

/-- The reference vector `A ω* = (ω*₀ - ω*₁, ω*₁)` of the rotated variables. -/
noncomputable def ωstar : Fin 2 → ℝ := ![Micro.ωstar 0 - Micro.ωstar 1, Micro.ωstar 1]

/-- The box is the exact image of `Micro`'s box. -/
theorem box_eq : cert.freqBox = shearBox Micro.cert.freqBox := by decide +kernel

theorem freq : FreqEncloses 2 cert.freqBox ωstar := by
  rw [box_eq]
  exact freqEncloses_shear Micro.freq

theorem dio : IsDiophantine ((cert.params.γ : ℚ) : ℝ) ((cert.params.tau : ℕ) : ℝ) ωstar := by
  have hγ0 : (0 : ℝ) ≤ ((Micro.cert.params.γ : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ Micro.cert.params.γ := by decide +kernel
    exact_mod_cast this
  have h := isDiophantine_shear Micro.dio hγ0 (Nat.cast_nonneg _)
  have hτ : cert.params.tau = Micro.cert.params.tau := by decide +kernel
  have hγ : ((cert.params.γ : ℚ) : ℝ) =
      ((Micro.cert.params.γ : ℚ) : ℝ) / 2 ^ ((Micro.cert.params.tau : ℕ) : ℝ) := by
    rw [show cert.params.γ = Micro.cert.params.γ / 2 by decide +kernel,
      show Micro.cert.params.tau = 1 by decide +kernel]
    push_cast
    norm_num
  rw [hγ, hτ]
  exact h

end KAM.CertificateSharp.V2.Forced.MicroRot

end
