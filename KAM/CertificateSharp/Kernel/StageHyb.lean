/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Check

/-!
# Stage memoization and sharding for the hybrid checker

`hybCompOk` (`Hybrid/Claims.lean`) recomputes the three compositions of the landed checks: the
first derivatives of `H` along `K` (full stage, `checkInvariance`'s), the first and second
derivatives (low stage, `checkTorsion`'s) and `H` itself (full stage, `checkEnergy`'s). Given those
compositions as literals proved by their own kernel runs (as the stages of `Kernel/Stage.lean`),
`hybCompOk_eq_of` reduces the check to its residual, the products with the step `ΔK̂`. The other
lemmas assemble `hybStepOk`, `refinedCoreR` and `checkHybrid` from their conjuncts, so each can be
decided by its own kernel run:

* `hybCompOk_eq_of`: the three compositions memoized;
* `hybStepOk_of`, `checkHybrid_of`: the checks from their parts;
* `sitesOk_congr`: `sitesOk` reads only `n`, `τ`, `kp`, `ρ`, `ρ∞`, `c`, `c̄` of the run, so a
  restart at `ρ₁ = ρ` reuses the certified sites of the base run.

Computation-only: no landed definition changes.
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Certificate KAM.CertificateSharp CertArith KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

/-- `hybCompOk` with its three compositions memoized. -/
theorem hybCompOk_eq_of {c : TorusCertificate n α} {w : HybStep} {ms mt : List (CertModel α)}
    {mv : CertModel α}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms)
    (ht : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some mt)
    (hv : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      [c.ham.jet.v0] = some [mv]) :
    hybCompOk c w = (linOk c w.W1 w.s1 (ratE w.dK) ms mt w.cl.lE &&
      energyLinOk c (ratE w.dK) mv ms w.lH) := by
  simp only [hybCompOk, hc, ht, hv]

/-- **Sharding**: `hybStepOk` from its six conjuncts. -/
theorem hybStepOk_of {c : TorusCertificate n α} {w : HybStep} {ρ₁ ρi ρT : ℚ}
    (h1 : hybWeightsOk c w ρ₁ ρi ρT = true) (h2 : hybPolyOk (n := n) w c.piEnc = true)
    (h3 : hybOmegaOk c w = true) (h4 : hybCauchyOk c w ρT = true) (h5 : hybCompOk c w = true)
    (h6 : decide (|w.s1 - c.params.s| * boxNormUp c.freqBox ≤ w.dw) = true) :
    hybStepOk c w ρ₁ ρi ρT = true := by
  simp only [hybStepOk, h1, h2, h3, h4, h5, h6, Bool.and_self]

/-- **Sharding**: `checkHybrid` from the transfer, the step checks and the restarted core. -/
theorem checkHybrid_of {c : TorusCertificate n α} {w : HybWit}
    (hT : transferOk n c.params c.freqBox w = true)
    (hS : hybStepOk c w.step w.p1.rho w.p1.rhoInf (w.ρT n c.freqBox) = true)
    (hR : refinedCoreR n w.p1 c.freqBox w.w1 = true) : checkHybrid c w = true := by
  simp only [checkHybrid, hT, hS, hR, Bool.and_self]

/-- `sitesOk` reads only `n`, `τ`, `kp`, `ρ`, `ρ∞`, `c` and `c̄` of the run. -/
theorem sitesOk_congr {Q Q' : NumQ} {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    {sites : List (Option BiteWit × Option BiteWit)} (hn : Q.n = Q'.n) (hτ : Q.τ = Q'.τ)
    (hkp : Q.kp = Q'.kp) (hρ : Q.ρ = Q'.ρ) (hρi : Q.ρinf = Q'.ρinf) (hc : Q.c = Q'.c)
    (hcb : Q.cbar = Q'.cbar) : sitesOk Q J box κ γ sites = sitesOk Q' J box κ γ sites := by
  simp only [sitesOk, NumQ.δ, NumQ.δ0, NumQ.b, NumQ.r, hn, hτ, hkp, hρ, hρi, hc, hcb]

end KAM.CertificateSharp.Hybrid

end
