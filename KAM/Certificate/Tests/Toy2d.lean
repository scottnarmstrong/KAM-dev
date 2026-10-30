/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.Toy2
public import KAM.Certificate.Tests.Toy2dData

/-!
# The positive toy T2d through the whole checker (SO design §8)

T2d is T2 with its Hamiltonian written with a division,
`H = J + (p²/2)·((a + cos 2πq)/(a + cos 2πq))` with `a = 10^30`. It exercises `div`, the ball
pass with a certified denominator, a reciprocal witness of `1/(a + cos 2πq)` (`15` terms, `|k| ≤ 9`,
dyadic at `2^{-895}`), a character witness and a nonempty advice book (`34` keys per stage).
Because the denominator is analytic on a wide strip (SO-TOYFIX2 ruling), T2d keeps T2's strip
`ρ = 9`, threshold `≈ 10^{-38.2}` and `err = 10^{-42}`. Both stages run at cutoff `10^6` with no
truncation.

Each sub-check is a separate `decide +kernel`, so every kernel run stays below a `6` GB cap.
`toyCert2d_passes` assembles them (`checkTorusCertificate` is their conjunction), and
`toyCert2d_torus` applies `checkTorusCertificate_sound` with `lunarNuMinus_half_isDiophantine`.
-/

@[expose] public section

namespace KAM.Certificate

/-- Toy T2d (data in `Tests/Toy2dData`). -/
def toyCert2d : TorusCertificate 2 ℚ := toyT2dCert

theorem toyCert2d_static : checkStatic toyCert2d = true := by decide +kernel

theorem toyCert2d_hamBounds : checkHamBounds toyCert2d = true := by decide +kernel

theorem toyCert2d_embedding : checkEmbedding toyCert2d = true := by decide +kernel

theorem toyCert2d_invariance : checkInvariance toyCert2d = true := by decide +kernel

theorem toyCert2d_energy : checkEnergy toyCert2d = true := by decide +kernel

theorem toyCert2d_gram : checkGram toyCert2d = true := by decide +kernel

theorem toyCert2d_torsion : checkTorsion toyCert2d = true := by decide +kernel

theorem toyCert2d_smallness : checkSmallness toyCert2d = true := by decide +kernel

theorem toyCert2d_passes : checkTorusCertificate toyCert2d = true := by
  simp only [checkTorusCertificate, toyCert2d_static, toyCert2d_hamBounds, toyCert2d_embedding,
    toyCert2d_invariance, toyCert2d_energy, toyCert2d_gram, toyCert2d_torsion,
    toyCert2d_smallness, Bool.and_self]

theorem toyCert2d_freq : FreqEncloses 2 toyCert2d.freqBox ![lunarNuMinus / 2, 1 / 2] := by
  have hx := sqrt_mem_of_checkRootEnclosure
    (show checkRootEnclosure 2 5 toyT2dRootLo toyT2dRootHi = true by decide +kernel)
  rw [← toyLunarFreq_eq_algFreq toyT2dAlgCoeffs (by decide +kernel)]
  exact algFreq_encloses hx
    (show checkAlgBox 2 toyT2dAlgCoeffs toyT2dRootLo toyT2dRootHi toyCert2d.freqBox = true by
      decide +kernel)

theorem toyCert2d_torus : CertifiedTorus toyCert2d ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificate_sound toyCert2d_passes toyCert2d_freq (by
    have h : ((toyCert2d.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2d.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2d.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2d.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

end KAM.Certificate
