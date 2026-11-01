/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk2
public import KAM.CertificateSharp.V2.Fiber.BulkSite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Three-frequency sites with the extended bulk walk

`bulk2SiteOk` is `bulkSiteOk` (`Fiber/BulkSite.lean`) with the extended walk `walkB2`
(`Fiber/Bulk2.lean`): tent runs, crossing runs and a computed crossing cut. Its witness carries no
geometric table (each run's weight sum is computed at its own length) and needs `e < 2^P`
strictly. `sdConst_ray_of_bulk2SiteOk` goes through the shared `sdConst_ray_of_snocBound`.

**Shards.** `walkB2` is `balFold` over its rows: `balFold_succ_of` (`Fiber/Shard.lean`) assembles it
from row blocks, and `bulk2SiteOk_of` is the test from its cheap part `bulk2PreOk`, the walk's value
and the bound.

`SiteWitK` adds the extended test to `SiteWitH` (`.h` is every `SiteWitH`); `siteOkK` and
`sdConst_of_siteOkK` have the shape of `siteOkH` and `sdConst_of_siteOkH`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- The witness of an extended bulk site. -/
structure Bulk2Wit where
  /-- The mode cut-off of `ω' ∈ ℝ²`. -/
  N : ℕ
  /-- `2N + 1 ≤ 2^l`. -/
  l : ℕ
  /-- The degree of the exponential lower polynomial. -/
  J : ℕ
  /-- The fixed-point precision. -/
  P : ℕ
  /-- The fixed-point upper bound `e/2^P` of `e^{-4πb}`, `e < 2^P`. -/
  e : ℕ
  /-- The dyadic box of `ω'`. -/
  D : DBox2
  /-- The claimed bound of `S((ω', 1), b)`. -/
  B : ℚ
  /-- The acceptance ratio numerator. -/
  rn : ℕ
  /-- The acceptance ratio denominator. -/
  rd : ℕ
  /-- The acceptance tolerance (times `2^P`). -/
  tol : ℕ
  /-- The half-width of the single fibres around a crossing, and the crossing runs' distance. -/
  s : ℕ
  /-- The recursion depth of a half-row. -/
  fuel : ℕ

/-- The `FibWit` of the same data (for `fibBound`). -/
def Bulk2Wit.toFib (w : Bulk2Wit) : FibWit := ⟨w.N, w.l, w.J, w.P, w.e, w.D, w.B⟩

/-- The walk of the site. -/
def Bulk2Wit.walk (w : Bulk2Wit) : Option ℕ :=
  walkB2 w.D w.e w.P w.rn w.rd w.tol w.s w.fuel w.N w.l

/-- The bound test of the extended walk. -/
def bulk2SumOk (box : FreqBox) (γ b : ℚ) (τ : ℕ) (w : Bulk2Wit) : Bool :=
  match w.walk with
  | none => false
  | some s => decide (fibBound box γ b τ w.toFib s ≤ w.B)

/-- **The extended bulk test at a site**, `n = 3`, any `τ`. -/
def bulk2SiteOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : Bulk2Wit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e < 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) && bulk2SumOk box γ b τ w &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- **Soundness of the extended bulk test**: `SDConst` on the ray. -/
theorem sdConst_ray_of_bulk2SiteOk {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : Bulk2Wit}
    (h : bulk2SiteOk n τ box γ b c w = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) : SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  simp only [bulk2SiteOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hc⟩, hb⟩, hγ⟩, hlo⟩, hD⟩, hcl⟩, he⟩, hE⟩, hl⟩, hsum⟩, hnum⟩ := h
  refine sdConst_ray_of_snocBound hc hb hγ hlo hD (fun ω' hγd hbox hdio' => ?_) hnum hω hdio
  unfold bulk2SumOk at hsum
  split at hsum
  · exact absurd hsum (by simp)
  rename_i s hs
  have hB : fibBound box γ b τ w.toFib s ≤ w.B := by simpa only [decide_eq_true_eq] using hsum
  have hS := smallDivisorSum_snoc2_le_bulk2 (γ := fibGamma box γ) (δ := 2 * b) he hE hγd
    (by positivity) hcl hl hs hbox hdio'
  have e : (((2 * b : ℚ)) : ℝ) = 2 * (b : ℝ) := by push_cast; ring
  rw [e] at hS
  refine hS.trans ?_
  exact (Rat.cast_le (K := ℝ)).mpr hB

/-- The cheap conjuncts of `bulk2SiteOk` (everything but the walk and its bound). -/
def bulk2PreOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : Bulk2Wit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e < 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- **Sharding of an extended bulk site**: the test from its cheap part, the walk's value (proved
by shards and `balFold_succ_of`) and the bound. -/
theorem bulk2SiteOk_of {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : Bulk2Wit} {s : ℕ}
    (hpre : bulk2PreOk n τ box γ b c w = true) (hs : w.walk = some s)
    (hB : fibBound box γ b τ w.toFib s ≤ w.B) : bulk2SiteOk n τ box γ b c w = true := by
  simp only [bulk2PreOk, Bool.and_eq_true, decide_eq_true_eq] at hpre
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hpre
  have hsum : bulk2SumOk box γ b τ w = true := by
    simp only [bulk2SumOk, hs, decide_eq_true_eq]
    exact hB
  simp only [bulk2SiteOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, hsum⟩, h11⟩

/-- The test of a site: every test of `siteOkH` (`.h`), or the extended bulk test (`n = 3`). -/
inductive SiteWitK where
  /-- A test of `siteOkH` (landed sites, bulk sites). -/
  | h (w : SiteWitH)
  /-- The extended bulk test of `bulk2SiteOk`. -/
  | bulk2 (w : Bulk2Wit)

/-- The test at a site. It contains `siteOkH`. -/
def siteOkK (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) : SiteWitK → Bool
  | .h w => siteOkH n τ J box κ γ b c w
  | .bulk2 w => bulk2SiteOk n τ box γ b c w

/-- **Soundness of the test at a site**, for a bite `b ≤ 1` (the shape of `sdConst_of_siteOkH`). -/
theorem sdConst_of_siteOkK {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {o : SiteWitK}
    (hn : 1 ≤ n) (hτ : 1 ≤ τ) (hγ : 0 < γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (h : siteOkK n τ J box κ γ b c o = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  cases o with
  | h w => exact sdConst_of_siteOkH hn hτ hγ hb hb1 h hω hdio
  | bulk2 w => exact sdConst_ray_of_bulk2SiteOk h hω hdio

/-- A test of `siteOkH` is a test of `siteOkK`, with the same verdict. -/
theorem siteOkK_h (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) (w : SiteWitH) :
    siteOkK n τ J box κ γ b c (.h w) = siteOkH n τ J box κ γ b c w := rfl

/-- A site of the engines from a (sharded) extended bulk test. -/
theorem siteOkK_bulk2_of {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {w : Bulk2Wit}
    (h : bulk2SiteOk n τ box γ b c w = true) : siteOkK n τ J box κ γ b c (.bulk2 w) = true := h

end KAM.CertificateSharp.V2

end
