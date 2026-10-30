/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.Toy2Data
public import KAM.Certificate.Soundness
public import KAM.Certificate.QuadraticDiophantine

/-!
# The positive toy T2 through the whole checker (SO design §8)

* **T2**: `H = J + p²/2` (`p = I₀`, `J = I₁`), `K(θ) = (θ, (ν̃, -ν̃²/2))` with a rational
  `ν̃ ≈ ν₋` (`|ν̃ - ν₋| ≤ 10^{-42}`), reference vector `(ν₋/2, 1/2)`, `s = 2`, positive residual.

`toyCert2_passes` is `decide +kernel` on the whole checker. The frequency box encloses
`(ν₋/2, 1/2)` by a root enclosure of `√5` and `checkAlgBox` (both `decide +kernel`), and
`toyCert2_torus` applies `checkTorusCertificate_sound` with `lunarNuMinus_half_isDiophantine`.
The toy T2d (the same Hamiltonian written with a division) is in `Tests/Toy2d`.
-/

@[expose] public section

namespace KAM.Certificate

/-- Toy T2 (data in `Tests/Toy2Data`). -/
def toyCert2 : TorusCertificate 2 ℚ := toyT2Cert

theorem toyCert2_passes : checkTorusCertificate toyCert2 = true := by decide +kernel

/-- `(ν₋/2, 1/2) = (3039/6236 + x/6236, 1/2)` at `x = √5`. -/
theorem toyLunarFreq_eq_algFreq (cs : List (List ℚ))
    (hcs : cs = [[3039 / 6236, 1 / 6236], [1 / 2]]) :
    algFreq 2 cs (Real.sqrt (5 : ℕ)) = ![lunarNuMinus / 2, 1 / 2] := by
  subst hcs
  funext i
  fin_cases i
  · simp [algFreq, Finset.sum_range_succ, lunarNuMinus_eq]; ring
  · simp [algFreq]

theorem toyCert2_freq : FreqEncloses 2 toyCert2.freqBox ![lunarNuMinus / 2, 1 / 2] := by
  have hx := sqrt_mem_of_checkRootEnclosure
    (show checkRootEnclosure 2 5 toyT2RootLo toyT2RootHi = true by decide +kernel)
  rw [← toyLunarFreq_eq_algFreq toyT2AlgCoeffs (by decide +kernel)]
  exact algFreq_encloses hx
    (show checkAlgBox 2 toyT2AlgCoeffs toyT2RootLo toyT2RootHi toyCert2.freqBox = true by
      decide +kernel)

theorem toyCert2_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificate_sound toyCert2_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

end KAM.Certificate
