/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Frame.Majorants
public import KAM.Certificate.Tests.Toy2
public import KAM.Certificate.Tests.Toy3
public import KAM.CertificateSharp.Tests.Corner

/-!
# The frame majorants on the toys

The toys T2 and T3 are flat (`U ≡ 0`, constant `A`): `L = DK` has column sums `1`, `N = Ω₀ L G⁻¹`
has norms `1` (up to the Gram radius `< 10⁻⁴⁰`), the torsion block has sup `1`, and the landed
per-entry `ℓ¹` sums and the corner sums agree exactly (measured in `.drafts`, reported in the
handoff). The checks pass with the rational majorants `1.01`, and fail at `0.99`; for T2 the whole
soundness theorem is instantiated at the reference frequency `(ν₋/2, 1/2)`.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- The claimed majorants of the toys. -/
def toyFrameBounds2 : FrameBounds := ⟨101 / 100, 101 / 100, 101 / 100, 101 / 100, 51 / 100⟩
def toyFrameBounds3 : FrameBounds := ⟨101 / 100, 101 / 100, 101 / 100, 101 / 100, 80 / 100⟩

theorem toyCert2_frame_passes : checkFrameMajorants toyCert2 toyFrameBounds2 = true := by
  decide +kernel

theorem toyCert3_frame_passes : checkFrameMajorants toyCert3 toyFrameBounds3 = true := by
  decide +kernel

/-- A too-small majorant of `|Lᵀ|` is rejected. -/
theorem toyCert2_frame_rejects : checkFrameL toyCert2 (99 / 100) = false := by decide +kernel

theorem toyCert2_frameMajorants :
    FrameMajorants toyCert2 toyFrameBounds2 ![lunarNuMinus / 2, 1 / 2] := by
  have h := toyCert2_passes
  simp only [checkTorusCertificate, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact checkFrameMajorants_sound hs (checkHamBounds_sound hs hh) (checkEmbedding_sound hs he)
    toyCert2_frame_passes toyCert2_freq

/-- A non-flat column: the entries `e_{(1,1)}` and `e_{(1,-1)}` (`ρ = 1/100`, `w = 1.065`). The
landed `ℓ¹` of sups is `2 w² = 2.268`, the joint corner sum is `w² + 1 = 2.134`: the corner row
check passes at `2.2`, the landed per-entry sum does not. -/
def colModels : List (CertModel ℚ) :=
  [⟨0, ⟨[([1, 1], ⟨1, 0⟩)]⟩, 0⟩, ⟨0, ⟨[([1, -1], ⟨1, 0⟩)]⟩, 0⟩]

theorem col_corner_passes :
    rowCornerLeq cornerW (wloOf cornerW 24) 2 colModels (22 / 10 : ℚ) = true := by
  decide +kernel

theorem col_landed_fails :
    CertArith.ble (sumUp (fun m : CertModel ℚ => m.supBound cornerW) colModels)
      (22 / 10 : ℚ) = false := by
  decide +kernel

end KAM.CertificateSharp
