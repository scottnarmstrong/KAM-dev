/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.Toy3Data
public import KAM.Certificate.Soundness
public import KAM.Certificate.CubicDiophantine

/-!
# The positive toy T3 through the whole checker (SO design §8, finding F1 example)

`n = 3`, `τ = 2`: `H = I₂ + I₀²/2 + I₁²/2` (`toyHam3`), `K(θ) = (θ, (a, b, -(a² + b²)/2))` with
rational `a ≈ ∛2`, `b ≈ ∛4` (`|a - ∛2|, |b - ∛4| ≤ 10^{-63}`), `s = 2`, a box of `cubicFreq`, a
positive residual. `toyCert3_passes` is `decide +kernel` on the whole checker; the box encloses
`cubicFreq` by a root enclosure of `∛2` and `checkAlgBox`; `toyCert3_torus` applies
`checkTorusCertificate_sound` with `cubicFreq_isDiophantine`.
-/

@[expose] public section

namespace KAM.Certificate

/-- Toy Hamiltonian `I₂ + I₀²/2 + I₁²/2` (isoenergetically nondegenerate; no perturbation). -/
def toyHam3 : HamExpr 3 :=
  .add (.action 2) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    (.mul (.const (1 / 2)) (.pow (.action 1) 2)))

/-- Toy T3 (data in `Tests/Toy3Data`). -/
def toyCert3 : TorusCertificate 3 ℚ := toyT3Cert

theorem toyCert3_ham : toyCert3.ham = toyHam3 := rfl

theorem toyCert3_err_pos : 0 < toyCert3.params.err := by decide +kernel

theorem toyCert3_passes : checkTorusCertificate toyCert3 = true := by decide +kernel

theorem toyCert3_freq : FreqEncloses 3 toyCert3.freqBox cubicFreq := by
  have hx := rpow_mem_of_checkRootEnclosure (by norm_num)
    (show checkRootEnclosure 3 2 toyT3RootLo toyT3RootHi = true by decide +kernel)
  have hc : (((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) = cbrtTwo := by
    simp [cbrtTwo]
  rw [hc] at hx
  rw [cubicFreq_eq_algFreq,
    show [[0, 1 / 2], [0, 0, 1 / 2], [1 / 2]] = toyT3AlgCoeffs by decide +kernel]
  exact algFreq_encloses hx
    (show checkAlgBox 3 toyT3AlgCoeffs toyT3RootLo toyT3RootHi toyCert3.freqBox = true by
      decide +kernel)

/-- The genuine `n = 3` black-box application (external Diophantine premise discharged). -/
theorem toyCert3_torus : CertifiedTorus toyCert3 cubicFreq :=
  checkTorusCertificate_sound toyCert3_passes toyCert3_freq (by
    have h : ((toyCert3.params.γ : ℚ) : ℝ) = 1 / 12 := by
      rw [show toyCert3.params.γ = 1 / 12 by decide +kernel]; norm_num
    have ht : ((toyCert3.params.tau : ℕ) : ℝ) = 2 := by
      rw [show toyCert3.params.tau = 2 by decide +kernel]; norm_num
    rw [h, ht]
    exact cubicFreq_isDiophantine)

end KAM.Certificate
