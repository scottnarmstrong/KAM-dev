/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Torsion
import Mathlib.Tactic.Linarith

/-!
# The exact rational mirror of the frame transfer (package C8c)

The transfer numbers of the certified first step are rational functions of rational data (no `π`,
no exponential): `c_Th = 2M₁`, `c_DTh = 2M₂` and the bounds of the step. The checker evaluates them
exactly; the casts are equalities.

* `FrameQ`, `FrameQ.toNum` and the casts of `g`, `β₁`, `b`, `n_Δ`, `n_Δᵗ` (Lemma `bp:p2s2hc:frames`,
  `KAM.Sharp2.Hybrid.FrameNum`);
* `dABQ`, `cast_dAB` (`KAM.Sharp2.Hybrid.dAB`).
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM.Sharp2.Hybrid

/-- The rational numbers of Lemma `bp:p2s2hc:frames`. -/
structure FrameQ where
  ℓ : ℚ
  ℓt : ℚ
  β : ℚ
  ν : ℚ
  νt : ℚ
  d1 : ℚ
  d1t : ℚ

namespace FrameQ

variable (F : FrameQ)

/-- The real numbers. -/
noncomputable def toNum : FrameNum := ⟨F.ℓ, F.ℓt, F.β, F.ν, F.νt, F.d1, F.d1t⟩

def g : ℚ := F.ℓt * F.d1 + F.d1t * F.ℓ + F.d1t * F.d1
def β1 : ℚ := F.β / (1 - F.β * F.g)
def b : ℚ := F.β ^ 2 * F.g / (1 - F.β * F.g)
def nΔ : ℚ := F.β1 * F.d1 + F.ℓ * F.b
def nΔt : ℚ := F.β1 * F.d1t + F.ℓt * F.b

theorem cast_g : F.toNum.g = (F.g : ℝ) := by
  simp only [FrameNum.g, g, toNum]; push_cast; ring
theorem cast_β1 : F.toNum.β1 = (F.β1 : ℝ) := by
  simp only [FrameNum.β1, β1, cast_g]; simp only [toNum]; push_cast; ring
theorem cast_b : F.toNum.b = (F.b : ℝ) := by
  simp only [FrameNum.b, b, cast_g]; simp only [toNum]; push_cast; ring
theorem cast_nΔ : F.toNum.nΔ = (F.nΔ : ℝ) := by
  simp only [FrameNum.nΔ, nΔ, cast_β1, cast_b]; simp only [toNum]; push_cast; ring
theorem cast_nΔt : F.toNum.nΔt = (F.nΔt : ℝ) := by
  simp only [FrameNum.nΔt, nΔt, cast_β1, cast_b]; simp only [toNum]; push_cast; ring

end FrameQ

/-- `Δ_ab` over `ℚ`. -/
def dABQ (F : FrameQ) (cTh cDTh d : ℚ) : ℚ :=
  F.nΔt * cTh * (F.ν + F.nΔ) + F.νt * (cDTh * d) * (F.ν + F.nΔ) + F.νt * cTh * F.nΔ

theorem cast_dAB (F : FrameQ) (cTh cDTh d : ℚ) :
    dAB F.toNum cTh cDTh d = (dABQ F cTh cDTh d : ℝ) := by
  simp only [dAB, dABQ, FrameQ.cast_nΔ, FrameQ.cast_nΔt]
  simp only [FrameQ.toNum]
  push_cast
  ring

end KAM.CertificateSharp.Hybrid

end
