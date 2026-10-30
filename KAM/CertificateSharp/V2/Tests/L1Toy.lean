/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Engine
public import KAM.CertificateSharp.V2.Tests.Refined

/-!
# Route A with the ℓ¹ entry on the toy T2, in the kernel (package C6L1)

The toy T2 (`H = J + p²/2`, a full torus at `ρ = 9`, `ρ∞ = 1`) passes the whole v2 certifier with
`routeAL1`, by `decide +kernel`, and the soundness theorem is instantiated at its reference
frequency: a `CertifiedTorus`.

* The ℓ¹ data are computed from the certificate's own models on `T_{ρ'}`, `ρ' = 8` (the torsion on
  `T_7`): `|E|₁ ≤ 2 e`, the column and row sums of `|L|₁` and `|N|₁` at most `1.1`, the torsion rows
  at most `1.1` (`toyCert2_l1Claim`); a claim `|E|₁ ≤ e/10` is rejected (`toyCert2_l1Claim_rejects`).
* `Γ_∞(sω*, 1) ≤ 0.0025` and `Γ_∞(sω*, 8) ≤ 1.2·10⁻⁶` are certified by the fibered test on the clock
  box (one fiber each side).
* The run is C6's refined toy run (`toyRefinedWit`); its small-divisor sites are unchanged, since
  `δ₀ = min {1, (ρ' - ρ∞)/6} = 1` as in C6.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The ℓ¹ claim of T2. -/
def toyL1Claim : L1Claim where
  W1 := CertWeight.mk 8 toyT2Weight.w
  WT := CertWeight.mk 7 toyT2Weight.w
  aE := 2 / 3118000000000000000000000000000000000000000
  aLt := 11 / 10
  aNt := 11 / 10
  nuK := 11 / 10
  nuN := 11 / 10
  t1 := 11 / 10

/-- The witness of T2 for route A with the ℓ¹ entry. -/
def toyL1Wit : L1Wit where
  base := toyRefinedWit
  L := toyL1Claim
  E := { aN := 3, aL := 3, t1 := 11 / 10, tR := 101 / 100, G0 := 25 / 10000, Gρ := 12 / 10 ^ 7,
         frame := some (11 / 10, 11 / 10), ei := 3679 / 10000 }
  g0 := ⟨1, 76 / 10000, 25 / 10000⟩
  gρ := ⟨1, 35 / 10 ^ 7, 12 / 10 ^ 7⟩

/-- The ℓ¹ data of T2 from its models. -/
theorem toyCert2_l1Claim : checkL1Claim toyCert2 toyL1Claim = true := by decide +kernel

/-- A too-small claim on `|E|₁` is rejected. -/
theorem toyCert2_l1Claim_rejects :
    checkL1Claim toyCert2 { toyL1Claim with aE := 1 / 31180000000000000000000000000000000000000000 }
      = false := by
  decide +kernel

/-- The numbers of the run. -/
def toyL1Q : NumQ := toyL1Wit.num 2 toyCert2.params toyCert2.freqBox

theorem toyL1_wf : toyL1Q.wfOk = true := by decide +kernel

theorem toyL1_ok : okL1 toyL1Q toyL1Wit.E (capQ toyL1Q toyCert2.params.μ toyCert2.params.nuRay)
    (initQ toyRefinedWit.R.bL toyRefinedWit.R.bN toyRefinedWit.R.bNt toyRefinedWit.R.bT
      toyCert2.params.σK toyCert2.params.σB toyCert2.params.σT toyCert2.params.μ)
    toyRefinedWit.core.Xs = true := by decide +kernel

theorem toyL1_sites : sitesOk toyL1Q toyRefinedWit.core.J toyCert2.freqBox toyRefinedWit.κ
    toyCert2.params.γ toyRefinedWit.sites = true := by decide +kernel

theorem toyL1_tail : classicalOk 2 toyCert2.params.tau toyRefinedWit.core.J
    (toyL1Q.δ toyRefinedWit.core.kp) toyL1Q.ctail = true := by decide +kernel

theorem toyL1_entry : entryOk 2 toyL1Q toyCert2.params toyCert2.freqBox toyL1Wit = true := by
  decide +kernel

theorem toyL1_final : finalL1 toyL1Q toyL1Wit.E toyCert2.params toyCert2.freqBox
    toyRefinedWit.core.Xs = true := by decide +kernel

theorem toyCert2_l1Core : l1Core 2 toyCert2.params toyCert2.freqBox toyL1Wit = true :=
  l1Core_of (by decide +kernel) toyL1_wf toyL1_ok toyL1_sites toyL1_tail toyL1_entry toyL1_final

/-- The landed sub-checks on T2. -/
theorem toyCert2_base : landedBase.check toyCert2 = true := by decide +kernel

theorem toyCert2_frame :
    checkFrameMajorants toyCert2 (toyRefinedWit.R.frame toyCert2.freqBox) = true := by
  decide +kernel

/-- The whole v2 certifier on T2, with the ℓ¹ entry. -/
theorem toyCert2_l1_passes : checkTorusCertificateV2 routeAL1 toyCert2 toyL1Wit = true := by
  have h1 : checkHamClaim toyCert2 toyL1Wit.base.R = true := toyCert2_hamClaim
  have h2 : checkFrameMajorants toyCert2 (toyL1Wit.base.R.frame toyCert2.freqBox) = true :=
    toyCert2_frame
  have h3 : checkL1Claim toyCert2 toyL1Wit.L = true := toyCert2_l1Claim
  rw [checkTorusCertificateV2_routeAL1]
  simp only [l1Test, toyCert2_base, h1, h2, h3, toyCert2_l1Core, Bool.and_self]

/-- The combined engine with the witness of the ℓ¹ route. -/
theorem toyCert2_routeAV2L1_passes :
    checkTorusCertificateV2 routeAV2L1 toyCert2 (Sum.inr (Sum.inr toyL1Wit)) = true := by
  rw [checkTorusCertificateV2_routeAV2L1_l1]
  exact toyCert2_l1_passes

/-- **The toy torus through route A with the ℓ¹ entry.** -/
theorem toyCert2_l1_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeAL1 toyCert2_l1_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

end KAM.CertificateSharp.V2.L1

end
