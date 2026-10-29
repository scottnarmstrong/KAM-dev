/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.Toy2Data
public import KAM.Certificate.Tests.Toy2dData
public import KAM.Certificate.Soundness
public import KAM.Certificate.QuadraticDiophantine

/-!
# The positive toys T2 and T2d through the whole checker (SO design §8)

* **T2**: `H = J + p²/2` (`p = I₀`, `J = I₁`), `K(θ) = (θ, (ν̃, -ν̃²/2))` with a rational
  `ν̃ ≈ ν₋` (`|ν̃ - ν₋| ≤ 10^{-42}`), reference vector `(ν₋/2, 1/2)`, `s = 2`, positive residual.
* **T2d**: the same Hamiltonian written with a division,
  `J + (p²/2)·((3 + cos 2πq)/(3 + cos 2πq))`: it exercises `div`, the ball pass and a reciprocal
  witness (`531` terms), a character witness and a nonempty advice book (`34` keys per stage, the
  `[0, slot]` keys and `[2, 0]`; no `[5, a, l]` key: `freqModel` is constant, so the invariance
  products take the scalar route). `cfgFull.cutoff = 10^6` (no truncation of the full stage).

`toyCert2_passes` is `decide +kernel` on the whole checker. For T2d only the light sub-checks
are proved: its composition (products up to `531 × 1591` terms, `|k|₁ ≤ 1064`) costs the kernel
`12` GB in `checkEnergy` and more than `6` GB in `checkTorsion` and `18` GB in `checkInvariance`
(handoff SO-TEST-A: a design signal). The frequency box encloses
`(ν₋/2, 1/2)` by a root enclosure of `√5` and `checkAlgBox` (both `decide +kernel`), and
`toyCert2_torus` applies `checkTorusCertificate_sound` with `lunarNuMinus_half_isDiophantine`.
-/

@[expose] public section

namespace KAM.Certificate

/-- Toy T2 (data in `Tests/Toy2Data`). -/
def toyCert2 : TorusCertificate 2 ℚ := toyT2Cert

/-- Toy T2d (data in `Tests/Toy2dData`). -/
def toyCert2d : TorusCertificate 2 ℚ := toyT2dCert

theorem toyCert2_passes : checkTorusCertificate toyCert2 = true := by decide +kernel

/-! T2d: the five light sub-checks only. `checkInvariance`, `checkEnergy` and `checkTorsion` (hence
`toyCert2d_passes` and `toyCert2d_torus`) are beyond a bounded kernel run as built (handoff
SO-TEST-A: a design signal). -/

theorem toyCert2d_static : checkStatic toyCert2d = true := by decide +kernel

theorem toyCert2d_hamBounds : checkHamBounds toyCert2d = true := by decide +kernel

theorem toyCert2d_embedding : checkEmbedding toyCert2d = true := by decide +kernel

theorem toyCert2d_gram : checkGram toyCert2d = true := by decide +kernel

theorem toyCert2d_smallness : checkSmallness toyCert2d = true := by decide +kernel

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

theorem toyCert2d_freq : FreqEncloses 2 toyCert2d.freqBox ![lunarNuMinus / 2, 1 / 2] := by
  have hx := sqrt_mem_of_checkRootEnclosure
    (show checkRootEnclosure 2 5 toyT2dRootLo toyT2dRootHi = true by decide +kernel)
  rw [← toyLunarFreq_eq_algFreq toyT2dAlgCoeffs (by decide +kernel)]
  exact algFreq_encloses hx
    (show checkAlgBox 2 toyT2dAlgCoeffs toyT2dRootLo toyT2dRootHi toyCert2d.freqBox = true by
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
