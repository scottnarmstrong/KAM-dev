/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.BulkSite
public import KAM.CertificateSharp.Freq.CubicNorm
public import KAM.Certificate.Tests.Toy3Data
public import KAM.Certificate.CubicDiophantine
import Mathlib.Tactic.FinCases

/-!
# The bulk walk in the kernel, on a cubic frequency with a slow coordinate

`bkFreq = (θ - 1, 3θ² + 24θ - 35, 1)`, `θ = ∛2`: the clock is exactly `1` and the middle
coordinate is slow, `3.08·10⁻⁴` (as the secular frequency of SJS over its fast clock,
`2.2·10⁻⁴`). Along a row `a` of the fibres, `x_b = aω'₀ + bω'₁` moves by `3.08·10⁻⁴` per step, so
the bulk walk (`Fiber/Bulk.lean`) bounds long runs at once.

* **The premise.** `cubicDioOk` proves `bkFreq` `(77/250000, 2)`-Diophantine
  (`bkFreq_isDiophantine`; the norm bound is `γ = 3.0835·10⁻⁴`, attained near `k = (0, 1, 0)`).
* **The enclosure.** `bkBox` (centres to 40 digits, radii `10⁻³⁸`, exact clock) contains `bkFreq`
  (`bkFreq_encloses`, from the landed enclosure of `∛2` and `abs_poly_le`).
* **The site** at the bite `b = 1/32` (`N = 65`, `l = 8`, `8 580` fibres): the bulk walk visits
  `452` nodes (`18` single fibres, `317` runs) and certifies `c = 5.726·10⁻⁴`
  (`bkSite_ok`, `bkSite_sdConst`), against the classical `c♮(3, 2, 1/32) = 0.0437` (factor `76`).
  The landed walk on the same data gives `c = 5.721·10⁻⁴` (the bulk loss is `0.17 %` of `S`).
  As a module its `8 580` fibres fit under the `4 GB` cap only narrowly (audit AUDIT-V2-BULK-1:
  `3.68 GB`, `27 s`); this module, with a second sharded proof of the site, builds in `4–8 s` at
  `1.65 GB`.
* **Shards.** `bkSite_ok_sharded` is the same site from two row blocks of the walk, assembled by
  `balFold_succ_of`, and the cheap part `bulkPreOk` (`bulkSiteOk_of`).
* `bkSite_rejects`: a constant `1 %` below is rejected.

The witness is produced by `scripts/certifier/fiber3_bulk.py` (`toy`, `check`), its exact mirror.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber
  KAM.CertificateSharp.Cubic

/-! ### The frequency and its Diophantine premise -/

/-- `bkFreq = A (1, θ, θ²)`. -/
def bkA : Fin 3 → Fin 3 → ℤ := ![![-1, 1, 0], ![-35, 24, 3], ![1, 0, 0]]

/-- The centre of the enclosure of `∛2`. -/
def bkθc : ℚ := (toyT3RootLo + toyT3RootHi) / 2

/-- The radius of the enclosure of `∛2`. -/
def bkθr : ℚ := (toyT3RootHi - toyT3RootLo) / 2

/-- The toy frequency `(θ - 1, 3θ² + 24θ - 35, 1)`, `θ = ∛2`. -/
noncomputable def bkFreq : Fin 3 → ℝ := cubicVec bkA 1 cbrtTwo

theorem bk_cubicDioOk : cubicDioOk (-2) 0 0 bkθc bkθr bkA 1 (77 / 250000) = true := by
  decide +kernel

theorem cbrtTwo_mem_bk : |cbrtTwo - (bkθc : ℝ)| ≤ (bkθr : ℝ) := by
  have hx := rpow_mem_of_checkRootEnclosure (by norm_num)
    (show checkRootEnclosure 3 2 toyT3RootLo toyT3RootHi = true by decide +kernel)
  have hc : (((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) = cbrtTwo := by simp [cbrtTwo]
  rw [hc] at hx
  rw [abs_le]
  simp only [bkθc, bkθr]
  push_cast
  constructor <;> linarith [hx.1, hx.2]

/-- **The premise**: `bkFreq` is `(77/250000, 2)`-Diophantine. -/
theorem bkFreq_isDiophantine : IsDiophantine ((77 / 250000 : ℚ) : ℝ) 2 bkFreq := by
  have hcube : cbrtTwo ^ 3 = 2 := by
    unfold cbrtTwo
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact isDiophantine_of_cubicDioOk bk_cubicDioOk (θ := cbrtTwo)
    (by push_cast; rw [hcube]; ring) cbrtTwo_mem_bk

/-! ### The box -/

/-- The certificate's box of `bkFreq`: centres to 40 digits, radii `10⁻³⁸`, the exact clock `1`. -/
def bkBox : FreqBox :=
  [(2599210498948731647672106072782283505703 / 10000000000000000000000000000000000000000,
      1 / 100000000000000000000000000000000000000),
    (616706763108757336342984988810389721 / 2000000000000000000000000000000000000000,
      1 / 100000000000000000000000000000000000000),
    (1, 0)]

theorem bkBox_coords : ∀ i : Fin 3,
    polyAbsUp ((bkA i 0 : ℚ) - (bkBox.getD i.val (0, 0)).1) (bkA i 1) (bkA i 2) bkθc bkθr ≤
      (bkBox.getD i.val (0, 0)).2 := by
  intro i
  fin_cases i <;> decide +kernel

/-- **The enclosure**: `bkBox` contains `bkFreq`. -/
theorem bkFreq_encloses : FreqEncloses 3 bkBox bkFreq := by
  intro i
  have h := abs_poly_le (w0 := (bkA i 0 : ℚ) - (bkBox.getD i.val (0, 0)).1) (w1 := bkA i 1)
    (w2 := bkA i 2) cbrtTwo_mem_bk
  have e : ((((bkA i 0 : ℚ) - (bkBox.getD i.val (0, 0)).1 : ℚ) : ℝ) +
      ((bkA i 1 : ℚ) : ℝ) * cbrtTwo + ((bkA i 2 : ℚ) : ℝ) * cbrtTwo ^ 2) =
      bkFreq i - ((bkBox.getD i.val (0, 0)).1 : ℝ) := by
    simp only [bkFreq, cubicVec]
    push_cast
    ring
  rw [e] at h
  exact h.trans (by exact_mod_cast bkBox_coords i)

/-! ### The site -/

/-- The bulk site at the bite `1/32`. -/
def bkWit : BulkWit :=
  { N := 65, l := 8, J := 9, P := 64, e := 12458310147371035356,
    D := { q := 64, C0 := 4794697086780616226, C1 := 5688115913796535, R0 := 1, R1 := 1 },
    B := 17880200,
    gs := [18446744073709551616, 30905054221080586972, 45001458336540984073,
      54363794943125628117, 56716812093148074112, 56823065402654247868,
      56823264830577248318, 56823264831277168957, 56823264831277168961],
    rn := 5, rd := 4, tol := 328855130085325568 }

/-- **The bulk site**, decided by the kernel. -/
theorem bkSite_ok : bulkSiteOk 3 2 bkBox (77 / 250000) (1 / 32) (2863 / 5000000) bkWit = true := by
  decide +kernel

/-- **The constant on the ray** of `bkFreq` at the bite `1/32`. -/
theorem bkSite_sdConst :
    SDConst 3 2 ((77 / 250000 : ℚ) : ℝ) ((1 / 32 : ℚ) : ℝ) ((2863 / 5000000 : ℚ) : ℝ)
      (ray bkFreq) :=
  sdConst_ray_of_bulkSiteOk bkSite_ok bkFreq_encloses bkFreq_isDiophantine

/-- A constant `1 %` below is rejected. -/
theorem bkSite_rejects :
    bulkSiteOk 3 2 bkBox (77 / 250000) (1 / 32) (5669 / 10000000) bkWit = false := by
  decide +kernel

/-! ### The same site from shards -/

/-- The rows of the bulk walk of `bkWit`. -/
def bkRows (i : ℕ) : Option ℕ :=
  rowB bkWit.D bkWit.e bkWit.P (fun t => bkWit.gs.getD t 0) bkWit.rn bkWit.rd bkWit.tol bkWit.N
    bkWit.l (rowA bkWit.N i)

theorem bkShard0 : balFold bkRows 7 0 = some 329502561009905755145711749 := by
  decide +kernel

theorem bkShard1 : balFold bkRows 7 (0 + pow2 7) = some 16790702964 := by
  decide +kernel

theorem bkPre : bulkPreOk 3 2 bkBox (77 / 250000) (1 / 32) (2863 / 5000000) bkWit = true := by
  decide +kernel

theorem bkBound :
    fibBound bkBox (77 / 250000) (1 / 32) 2 bkWit.toFib
      (329502561009905755145711749 + 16790702964) ≤ bkWit.B := by
  decide +kernel

/-- **The site from two shards** of its walk (`balFold_succ_of`, `bulkSiteOk_of`). -/
theorem bkSite_ok_sharded :
    bulkSiteOk 3 2 bkBox (77 / 250000) (1 / 32) (2863 / 5000000) bkWit = true :=
  bulkSiteOk_of bkPre (balFold_succ_of bkShard0 bkShard1) bkBound

end KAM.CertificateSharp.V2

end
