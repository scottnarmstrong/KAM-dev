/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk2Site
public import KAM.CertificateSharp.V2.Tests.BulkToy

/-!
# The extended bulk walk in the kernel, on the slow toy frequency

The frequency, box and Diophantine premise are those of `Tests/BulkToy.lean`:
`bkFreq = (θ - 1, 3θ² + 24θ - 35, 1)`, `θ = ∛2`, `γ = 77/250000`.

* **The site at `b = 1/64`** (`N = 146`, `42 924` fibres): the extended walk (`Fiber/Bulk2.lean`)
  visits `916` nodes (`87` single fibres, `641` plain runs, `12` tent runs, `56` crossing runs,
  `12` crossing cuts), against `1 546` for `walkB`. It certifies `c = 1.648·10⁻⁴`, the constant
  `walkB` certifies at this bite, against the classical `c♮(3, 2, 1/64) = 0.0429`
  (`bk2Site64_ok`, `bk2Site64_sdConst`).
* **The site at `b = 1/32`** (`N = 65`): `334` nodes against `452`, `c = 5.727·10⁻⁴`; a constant
  `1 %` below is rejected (`bk2Site32_rejects`).

Witnesses from `scripts/certifier/fiber3_bulk2.py` (`toy`), the exact mirror of `walkB2`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- The extended bulk site at the bite `1/64`. -/
def bk2Wit64 : Bulk2Wit :=
  { N := 146, l := 9, J := 8, P := 64, e := 15159658930070367826,
    D := { q := 64, C0 := 4794697086780616226, C1 := 5688115913796535, R0 := 1, R1 := 1 },
    B := 23682300, rn := 5, rd := 4, tol := 434496657203001536, s := 2, fuel := 64 }

/-- The extended bulk site at the bite `1/32`. -/
def bk2Wit32 : Bulk2Wit :=
  { N := 65, l := 8, J := 9, P := 64, e := 12458310147371035356,
    D := { q := 64, C0 := 4794697086780616226, C1 := 5688115913796535, R0 := 1, R1 := 1 },
    B := 17884400, rn := 5, rd := 4, tol := 328855130085325568, s := 2, fuel := 64 }

/-- **The extended bulk site at `b = 1/64`**, decided by the kernel. -/
theorem bk2Site64_ok :
    bulk2SiteOk 3 2 bkBox (77 / 250000) (1 / 64) (103 / 625000) bk2Wit64 = true := by
  decide +kernel

/-- **The constant on the ray** of `bkFreq` at the bite `1/64`. -/
theorem bk2Site64_sdConst :
    SDConst 3 2 ((77 / 250000 : ℚ) : ℝ) ((1 / 64 : ℚ) : ℝ) ((103 / 625000 : ℚ) : ℝ)
      (ray bkFreq) :=
  sdConst_ray_of_bulk2SiteOk bk2Site64_ok bkFreq_encloses bkFreq_isDiophantine

theorem bk2Site32_ok :
    bulk2SiteOk 3 2 bkBox (77 / 250000) (1 / 32) (5727 / 10000000) bk2Wit32 = true := by
  decide +kernel

/-- A constant `1 %` below is rejected. -/
theorem bk2Site32_rejects :
    bulk2SiteOk 3 2 bkBox (77 / 250000) (1 / 32) (567 / 1000000) bk2Wit32 = false := by
  decide +kernel

end KAM.CertificateSharp.V2

end
