/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk
public import KAM.CertificateSharp.V2.Fiber.Shard
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Three-frequency sites with the bulk walk

`bulkSiteOk` is `fiberSiteOk` (`Fiber/Site3.lean`) with the bulk walk `walkB` (`Fiber/Bulk.lean`)
in place of `walk2`: the same clock reduction, dyadic box, tail and constant test, and two more
checks (the geometric table `gTabOk0` and `l < gs.length`). `sdConst_ray_of_bulkSiteOk` gives
`SDConst n τ γ b c (ray ω*)`.

`sdConst_ray_of_snocBound` is the part shared by both tests: from a bound of `S((ω', 1), 2b)` for
every `ω'` of the dyadic box with `(ω', 1)` Diophantine at `fibGamma`, the constant on the ray.

`SiteWitH` adds the bulk test to the landed site tests (`.g` is every `SiteWitG`); `siteOkH` and
`sdConst_of_siteOkH` have the shape of `siteOkG` and `sdConst_of_siteOkG`.

**Shards.** `walkB` is `balFold` over its rows, so `balFold_succ_of` (`Fiber/Shard.lean`) assembles
it from separately decided row blocks; `bulkSiteOk_of` is the test from its cheap part
(`bulkPreOk`), the walk's value and the bound.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- The witness of a bulk site: the data of `FibWit`, the geometric table `gs` (`G_t`, `t ≤ l`) and
the acceptance rule (`rn/rd`, `tol`) of `walkB`. -/
structure BulkWit where
  /-- The mode cut-off of `ω' ∈ ℝ²`. -/
  N : ℕ
  /-- `2N + 1 ≤ 2^l`. -/
  l : ℕ
  /-- The degree of the exponential lower polynomial. -/
  J : ℕ
  /-- The fixed-point precision. -/
  P : ℕ
  /-- The fixed-point upper bound `e/2^P` of `e^{-4πb}`. -/
  e : ℕ
  /-- The dyadic box of `ω'`. -/
  D : DBox2
  /-- The claimed bound of `S((ω', 1), b)`. -/
  B : ℚ
  /-- The geometric table: `gs[t] ≥ 2^P Σ_{j<2^t} (e/2^P)^j`. -/
  gs : List ℕ
  /-- The acceptance ratio numerator. -/
  rn : ℕ
  /-- The acceptance ratio denominator. -/
  rd : ℕ
  /-- The acceptance tolerance (times `2^P`). -/
  tol : ℕ

/-- The `FibWit` of the same data (for `fibBound`). -/
def BulkWit.toFib (w : BulkWit) : FibWit := ⟨w.N, w.l, w.J, w.P, w.e, w.D, w.B⟩

/-- The bound test of the bulk walk. -/
def bulkSumOk (box : FreqBox) (γ b : ℚ) (τ : ℕ) (w : BulkWit) : Bool :=
  match walkB w.D w.e w.P (fun t => w.gs.getD t 0) w.rn w.rd w.tol w.N w.l with
  | none => false
  | some s => decide (fibBound box γ b τ w.toFib s ≤ w.B)

/-- **The bulk test at a site**, `n = 3`, any `τ`. -/
def bulkSiteOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : BulkWit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e ≤ 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) && decide (w.l < w.gs.length) && gTabOk0 w.e w.P w.gs &&
    bulkSumOk box γ b τ w &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- **`SDConst` on the ray from a bound of the normalized sum**: if every `ω'` of the dyadic box
with `(ω', 1)` Diophantine at `fibGamma box γ` has `S((ω', 1), 2b) ≤ B`, the constant test
`2^n B κlo⁻² (γ b^τ)² ≤ (2 · 3.1415 · c)²` gives `SDConst` at every `ω*` of the box. -/
theorem sdConst_ray_of_snocBound {τ : ℕ} {box : FreqBox} {γ b c B : ℚ} {D : DBox2}
    (hc : 0 < c) (hb : 0 < b) (hγ : 0 < γ) (hlo : 0 < clockC box - clockR box)
    (hD : dboxOk box D = true)
    (hS : ∀ ω' : Fin 2 → ℝ, 0 < fibGamma box γ → FreqEncloses 2 D.toBox ω' →
      IsDiophantine ((fibGamma box γ : ℚ) : ℝ) τ (Fin.snoc ω' 1 : Fin 3 → ℝ) →
      smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ)) ≤ (B : ℝ))
    (hnum : 2 ^ 3 * B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)
    {ωstar : Fin 3 → ℝ} (hω : FreqEncloses 3 box ωstar) (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst 3 τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hlo' : (0 : ℝ) < ((clockC box - clockR box : ℚ) : ℝ) := by exact_mod_cast hlo
  obtain ⟨ω', hsnoc, hbox, hdio', hκ⟩ := clock_reduce hγ hlo hω hdio
  have hr0 : 0 ≤ clockR box := by
    have : (0 : ℝ) ≤ clockR box := (abs_nonneg _).trans (hω 2)
    exact_mod_cast this
  have hγd : 0 < fibGamma box γ := div_pos hγ (by linarith)
  have hSB := hS ω' hγd (encloses_dbox hD hbox) hdio'
  have hS0 : 0 ≤ smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ)) :=
    smallDivisorSum_nonneg _ _
  have hsd : sdSum ωstar b ≤ (B : ℝ) * (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ := by
    rw [sdSum_eq_smallDivisorSum, hsnoc, smallDivisorSum_smul]
    have hw2 : 0 < ωstar 2 := lt_of_lt_of_le hlo' hκ
    have hsq : ((clockC box - clockR box : ℚ) : ℝ) ^ 2 ≤ (ωstar 2) ^ 2 :=
      pow_le_pow_left₀ hlo'.le hκ 2
    have hinv : ((ωstar 2) ^ 2)⁻¹ ≤ (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have hB0 : (0 : ℝ) ≤ B := hS0.trans hSB
    calc ((ωstar 2) ^ 2)⁻¹ * smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (2 * (b : ℝ))
        ≤ (((clockC box - clockR box : ℚ) : ℝ) ^ 2)⁻¹ * (B : ℝ) :=
          mul_le_mul hinv hSB hS0 (by positivity)
      _ = _ := mul_comm _ _
  refine sdConst_ray_of_sdSum_le hγ' hb' hc' hdio hsd ?_
  have := (Rat.cast_le (K := ℝ)).mpr hnum
  push_cast at this ⊢
  linarith

/-- **Soundness of the bulk test**: `SDConst` on the ray. -/
theorem sdConst_ray_of_bulkSiteOk {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : BulkWit}
    (h : bulkSiteOk n τ box γ b c w = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) : SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  simp only [bulkSiteOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hc⟩, hb⟩, hγ⟩, hlo⟩, hD⟩, hcl⟩, he⟩, hE⟩, hl⟩, hgl⟩, hgs⟩, hsum⟩,
    hnum⟩ := h
  refine sdConst_ray_of_snocBound hc hb hγ hlo hD (fun ω' hγd hbox hdio' => ?_) hnum hω hdio
  unfold bulkSumOk at hsum
  split at hsum
  · exact absurd hsum (by simp)
  rename_i s hs
  have hB : fibBound box γ b τ w.toFib s ≤ w.B := by simpa only [decide_eq_true_eq] using hsum
  have hG : ∀ t ≤ w.l, ∑ j ∈ Finset.range (2 ^ t), ((w.e : ℝ) / 2 ^ w.P) ^ j ≤
      ((w.gs.getD t 0 : ℕ) : ℝ) / 2 ^ w.P := fun t ht =>
    gTabOk0_spec he hgs (by omega)
  have hS := smallDivisorSum_snoc2_le_bulk (γ := fibGamma box γ) (δ := 2 * b) he hE hγd
    (by positivity) hcl hl hG hs hbox hdio'
  have e : (((2 * b : ℚ)) : ℝ) = 2 * (b : ℝ) := by push_cast; ring
  rw [e] at hS
  refine hS.trans ?_
  exact (Rat.cast_le (K := ℝ)).mpr hB

/-- The cheap conjuncts of `bulkSiteOk` (everything but the walk and its bound). -/
def bulkPreOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : BulkWit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e ≤ 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) && decide (w.l < w.gs.length) && gTabOk0 w.e w.P w.gs &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- **Sharding of a bulk site**: the test from its cheap part, the walk's value (proved by shards
and `balFold_succ_of`) and the bound. -/
theorem bulkSiteOk_of {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : BulkWit} {s : ℕ}
    (hpre : bulkPreOk n τ box γ b c w = true)
    (hs : walkB w.D w.e w.P (fun t => w.gs.getD t 0) w.rn w.rd w.tol w.N w.l = some s)
    (hB : fibBound box γ b τ w.toFib s ≤ w.B) : bulkSiteOk n τ box γ b c w = true := by
  simp only [bulkPreOk, Bool.and_eq_true, decide_eq_true_eq] at hpre
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hpre
  have hsum : bulkSumOk box γ b τ w = true := by
    simp only [bulkSumOk, hs, decide_eq_true_eq]
    exact hB
  simp only [bulkSiteOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, hsum⟩, h13⟩

/-- The test of a site: every landed test (`.g`), or the bulk test (`n = 3`). -/
inductive SiteWitH where
  /-- A landed site test (classical, lunar bite, fibered). -/
  | g (w : SiteWitG)
  /-- The bulk test of `bulkSiteOk`. -/
  | bulk (w : BulkWit)

/-- The test at a site. It contains `siteOkG`. -/
def siteOkH (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) : SiteWitH → Bool
  | .g w => siteOkG n τ J box κ γ b c w
  | .bulk w => bulkSiteOk n τ box γ b c w

/-- **Soundness of the test at a site**, for a bite `b ≤ 1` (the shape of `sdConst_of_siteOkG`). -/
theorem sdConst_of_siteOkH {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {o : SiteWitH}
    (hn : 1 ≤ n) (hτ : 1 ≤ τ) (hγ : 0 < γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (h : siteOkH n τ J box κ γ b c o = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) τ ωstar) :
    SDConst n τ (γ : ℝ) (b : ℝ) (c : ℝ) (ray ωstar) := by
  cases o with
  | g w => exact sdConst_of_siteOkG hn hτ hγ hb hb1 h hω hdio
  | bulk w => exact sdConst_ray_of_bulkSiteOk h hω hdio

/-- A landed site test is a test of `siteOkH`, with the same verdict. -/
theorem siteOkH_g (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) (w : SiteWitG) :
    siteOkH n τ J box κ γ b c (.g w) = siteOkG n τ J box κ γ b c w := rfl

/-- A site of the engines from a (sharded) bulk test. -/
theorem siteOkH_bulk_of {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {w : BulkWit}
    (h : bulkSiteOk n τ box γ b c w = true) : siteOkH n τ J box κ γ b c (.bulk w) = true := h

end KAM.CertificateSharp.V2

end
