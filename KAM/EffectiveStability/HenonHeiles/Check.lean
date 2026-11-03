/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Shard.Lie1
public import KAM.EffectiveStability.HenonHeiles.Shard.Lie2
public import KAM.EffectiveStability.HenonHeiles.Shard.Lie3
public import KAM.EffectiveStability.HenonHeiles.Shard.Fin
public import KAM.EffectiveStability.HenonHeiles.Shard.Bound1
public import KAM.EffectiveStability.HenonHeiles.Shard.Bound2
public import KAM.EffectiveStability.HenonHeiles.Shard.Bound3

/-!
# The kernel check of the Hénon–Heiles certificate (track B, B3-CERT)

`hhCert_check : checkOscChain hhCert = true`. The four big polynomial identities (the three Lie
identities and the final identity `Q₃ = Nact(I) + P`) are the chunked shard theorems
`hhLie1_check`, `hhLie2_check`, `hhLie3_check`, `hhFin_check`; the remainder majorant
`oscChainBound` (a sum over unmerged `ad` lists of up to ~10⁵ monomials) is the chunked
`hhBound1..3`; the remaining conjuncts (typing, step bounds, domains, scalar inequalities) are one
`decide +kernel`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

/-- The three per-step conjuncts `oscStepOKB`. -/
theorem hhSteps_ok :
    (oscStepOKB 2 hhStep1 && oscStepOKB 2 hhStep2 && oscStepOKB 2 hhStep3) = true := by
  decide +kernel

/-- The step chain conjunct of `checkOscChain`, from the four polynomial-identity shards. -/
theorem hhCert_chain :
    oscChainOKB 2 hhCert.Nact hhCert.P hhCert.steps hhCert.H = true := by
  have hs := hhSteps_ok
  simp only [Bool.and_eq_true] at hs
  simp only [hhCert, oscChainOKB, hs.1.1, hs.1.2, hs.2, hhLie1_check, hhLie2_check, hhLie3_check,
    hhFin_check, Bool.and_self]

/-- The value of `oscChainBound` for the Hénon–Heiles certificate, from the chunked shards. -/
def hhBoundTotal : ℚ :=
  hhBs1_0 / ((hhStep1.order.factorial : ℕ) : ℚ) +
    (hhBs2_0 / ((hhStep2.order.factorial : ℕ) : ℚ) +
      (hhBs3_0 / ((hhStep3.order.factorial : ℕ) : ℚ) + 0))

theorem hhCert_bound : oscChainBound 2 hhCert.steps hhCert.H = hhBoundTotal := by
  show cartSupBound hhZ1 (List.replicate 2 hhStep1.ρ) (List.replicate 2 hhStep1.ρ) /
      ((hhStep1.order.factorial : ℕ) : ℚ) +
    (cartSupBound hhZ2 (List.replicate 2 hhStep2.ρ) (List.replicate 2 hhStep2.ρ) /
      ((hhStep2.order.factorial : ℕ) : ℚ) +
    (cartSupBound hhZ3 (List.replicate 2 hhStep3.ρ) (List.replicate 2 hhStep3.ρ) /
      ((hhStep3.order.factorial : ℕ) : ℚ) + 0)) = hhBoundTotal
  rw [hhBound1, hhBound2, hhBound3]
  rfl

/-- **The kernel check of the Hénon–Heiles certificate.** -/
theorem hhCert_check : checkOscChain hhCert = true := by
  unfold checkOscChain
  rw [hhCert_chain, hhCert_bound]
  decide +kernel

end KAM.EffectiveStability.HenonHeiles

end
