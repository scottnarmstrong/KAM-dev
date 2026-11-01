/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyRouteA
public import KAM.CertificateSharp.V2.Tests.Forced.TinyRouteB

/-!
# Mutations of the forced toy `Tiny` that must be rejected (claims, cores, sites, ball pass)

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it, alone in the kernel. The families and the producer's mirror verdicts
are listed in `scripts/certifier/forced/forced_mutations.py` and
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: the frame bound `bL` times `0.99` (frame bounds). -/
theorem mut_frameL : checkFrameL cert (Rclaim.bL * 99 / 100) = false := by
  decide +kernel

/-- Rejected: the frame bound `bT` times `0.99` (frame bounds). -/
theorem mut_frameT : checkFrameT cert (Rclaim.bT * 99 / 100) = false := by
  rw [checkFrameT_eq_of gram_eq T_eq]
  decide +kernel

/-- Rejected: the frame bound `bN` times `0.99` (frame bounds). -/
theorem mut_frameN : checkFrameN cert (Rclaim.bN * 99 / 100) Rclaim.bNt = false := by
  rw [checkFrameN_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

/-- Rejected: the Hamiltonian claim `dx` times `0.99` (frame bounds). -/
theorem mut_hamClaim : checkHamClaim cert { Rclaim with dx := Rclaim.dx * 99 / 100 } = false := by
  decide +kernel

/-- Rejected: `nuRay = 10⁻⁵`, above `(s - 1)|ω*| ≈ 10⁻⁶` (ray room). -/
theorem mut_nuRay : checkStatic { cert with params := { cert.params with nuRay := 1 / 10 ^ 5 } } =
    false := by
  decide +kernel

/-- Rejected: `disp = 1`, above the room `(σω - s)|ω*|` of the ray (ray room). -/
theorem mut_dispRoom : refinedCore 2 { cert.params with disp := 1 } cert.freqBox refinedWit = false
    := by
  decide +kernel

/-- Rejected: route A with `θ = 1` (schedules). -/
theorem mut_theta : refinedCore 2 cert.params cert.freqBox { refinedWit with core := {
    refinedWit.core with th := 1 } } = false := by
  decide +kernel

/-- Rejected: route A with ten times the passing `X⋆` (schedules). -/
theorem mut_Xs : refinedCore 2 cert.params cert.freqBox { refinedWit with core := { refinedWit.core
    with Xs := refinedWit.core.Xs * 10 } } = false := by
  decide +kernel

/-- Rejected: route B with the schedule ratio `a = 1` (schedules). -/
theorem mut_scheduleB : refinedBCore 2 cert.params cert.freqBox { refinedBWit with core := {
    refinedBWit.core with a := 1 } } = false := by
  decide +kernel

/-- The box with radius `1/20` in coordinate 0. -/
def boxWide : FreqBox :=
  [((cert.freqBox.getD 0 (0, 0)).1, 1 / 20), cert.freqBox.getD 1 (0, 0)]

/-- Rejected: the frequency box widened to radius `1/20`: the fibers reach the resonance, the sites
fail (denominator separation). -/
theorem mut_boxFiber : sitesOk (refinedWit.num 2 cert.params boxWide) refinedWit.core.J boxWide
    refinedWit.κ cert.params.γ refinedWit.sites = false := by
  decide +kernel

/-- Rejected: the first site with its bound `B` halved (denominator separation). -/
theorem mut_siteBound : siteOk 2 1 refinedWit.core.J cert.freqBox refinedWit.κ cert.params.γ
    ((refinedWit.num 2 cert.params cert.freqBox).δ 0) (refinedWit.core.c.getD 0 0) (some ⟨(773227 /
    1000000), 6, 8, (4522 / 25)⟩) = false := by
  decide +kernel

/-- Rejected: a term `10⁻⁹ / (p - p_c)` whose denominator ball contains `0` on the domain
(denominator separation). -/
theorem mut_denominator : checkHamBounds { cert with ham := .add ham (.div (.const (1 / 10 ^ 9))
    (.add (.action 0) (.const (63791325795 / 549755813888)))) } = false := by
  decide +kernel

/-- Rejected: a term `10⁻⁹ √(p - p_c)` whose operand reaches `Re ≤ 0` on the domain (square-root
domains). -/
theorem mut_sqrtDomain : checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9))
    (.sqrt (.add (.action 0) (.const (63791325795 / 549755813888))))) } = false := by
  decide +kernel

/-- Control: the same term with the separated denominator `p + 1` passes. -/
theorem ctl_denominator : checkHamBounds { cert with ham := .add ham (.div (.const (1 / 10 ^ 9))
    (.add (.action 0) (.const 1))) } = true := by
  decide +kernel

/-- Control: the same term with the operand `p + 1` passes. -/
theorem ctl_sqrtDomain : checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9))
    (.sqrt (.add (.action 0) (.const 1)))) } = true := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
