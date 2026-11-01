/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Bulk2Site

/-!
# Cross-language test of the extended bulk walk (generated)

Written by `scripts/certifier/fiber3_bulk2_xlang.py` from the Python mirror
`scripts/certifier/fiber3_bulk2.py`; do not edit by hand. Each theorem is a value the mirror
computed, decided by the kernel: `powDownK`, `gsumK`, tent and crossing runs that the mirror's walk
accepted and rejected (receding and approaching), a crossing cut, `rowB2` and `walkB2` on the toy
box of `Tests/BulkToy.lean`, `bulk2SiteOk` on both sides of the exact bound and constant, and three
rows of the SJS-plan frequencies at `P = 128`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLangBulk2

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber

def xD : DBox2 where
  q := 64
  C0 := 4794697086780616226
  C1 := 5688115913796535
  R0 := 1
  R1 := 1

def xe : ℕ := 12458310147371035356

def xBox : FreqBox :=
  [
    (2599210498948731647672106072782283505703 /
        10000000000000000000000000000000000000000,
      1 / 100000000000000000000000000000000000000),
    (616706763108757336342984988810389721 /
        2000000000000000000000000000000000000000,
      1 / 100000000000000000000000000000000000000),
    (1 /
        1,
      0 / 1)]

def xW : Bulk2Wit where
  N := 65
  l := 8
  J := 9
  P := 64
  e := 12458310147371035356
  D := xD
  B := 1011729675223731027165463136222499 /
    56570630050845081940787200
  rn := 5
  rd := 4
  tol := 328855130085325568
  s := 2
  fuel := 64

def xWlow : Bulk2Wit where
  N := 65
  l := 8
  J := 9
  P := 64
  e := 12458310147371035356
  D := xD
  B := 368065111696971517509323579805822737398557364938585283014587 /
    20580275322880000000000000000000000000000000000000000
  rn := 5
  rd := 4
  tol := 328855130085325568
  s := 2
  fuel := 64

def xc : ℚ :=
  14315464316033353 /
    25000000000000000000

def xcLow : ℚ :=
  57261857264133411 /
    100000000000000000000

def sD : DBox2 where
  q := 64
  C0 := 7431879174714169321
  C1 := (-4065032337688588)
  R0 := 1
  R1 := 1

def se : ℕ := 329143111507102215117200415767567212277

theorem xl_pdown_0 :
    powDownK xe 64 64 0 = 18446744073709551616 := by
  decide +kernel

theorem xl_gsum_0 :
    gsumK xe 64 0 = 0 := by
  decide +kernel

theorem xl_pdown_1 :
    powDownK xe 64 64 1 = 12458310147371035356 := by
  decide +kernel

theorem xl_gsum_1 :
    gsumK xe 64 1 = 18446744073709551616 := by
  decide +kernel

theorem xl_pdown_2 :
    powDownK xe 64 64 2 = 8413923406098202864 := by
  decide +kernel

theorem xl_gsum_2 :
    gsumK xe 64 2 = 30905054221080586973 := by
  decide +kernel

theorem xl_pdown_7 :
    powDownK xe 64 64 7 = 1182212735498696710 := by
  decide +kernel

theorem xl_gsum_7 :
    gsumK xe 64 7 = 53181582207626931403 := by
  decide +kernel

theorem xl_pdown_64 :
    powDownK xe 64 64 64 = 227217793 := by
  decide +kernel

theorem xl_gsum_64 :
    gsumK xe 64 64 = 56823264830577248303 := by
  decide +kernel

theorem xl_pdown_1000 :
    powDownK xe 64 64 1000 = 0 := by
  decide +kernel

theorem xl_gsum_1000 :
    gsumK xe 64 1000 = 56823264831277168938 := by
  decide +kernel

theorem xl_tent_acc :
    tentK xD xe 64 56823256199448386023 (accOk 5 4 328855130085325568) (-25) (-1) 1 0 39
      = some 11273224290335830 := by
  decide +kernel

theorem xl_tent_rej :
    tentK xD xe 64 56665642618233498789 (accOk 5 4 328855130085325568) (-50) (-1) 1 0 14
      = none := by
  decide +kernel

theorem xl_ap_app :
    apK xD xe 64 56065630305702714009 2 5 4 328855130085325568 (-50) (-1) 1 0 10
      = some 1641878037515347 := by
  decide +kernel

theorem xl_ap_rec :
    apK xD xe 64 56823262172260469330 2 5 4 328855130085325568 (-23) 1 0 0 42
      = some 1355639238684423234 := by
  decide +kernel

theorem xl_ap_rej :
    apK xD xe 64 56665642618233498789 2 5 4 328855130085325568 (-50) (-1) 1 0 14 = none := by
  decide +kernel

theorem xl_cut :
    crossCut xD 2 (-50) (-1) 1 0 14 = some (9, 14, 11) := by
  decide +kernel

theorem xl_row_0 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 0 = some 329554064047862581561298968 := by
  decide +kernel

theorem xl_row_4 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 4 = some 9634454348286916331669 := by
  decide +kernel

theorem xl_row_m23 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 (-23) = some 2675183053917977481 := by
  decide +kernel

theorem xl_row_27 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 27 = some 581290321673534280 := by
  decide +kernel

theorem xl_row_65 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 65 = some 775468588 := by
  decide +kernel

theorem xl_row_66 :
    rowB2 xD xe 64 5 4 328855130085325568 2 64 65 66 = some 0 := by
  decide +kernel

theorem xl_walk_toy :
    walkB2 xD xe 64 5 4 328855130085325568 2 64 65 8 = some 329580666839633155576369995 := by
  decide +kernel

theorem xl_site_exact :
    bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xW = true := by
  decide +kernel

theorem xl_site_low :
    bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xWlow = false := by
  decide +kernel

theorem xl_site_c_low :
    bulk2SiteOk 3 2 xBox (77 / 250000) (1 / 32) xcLow xW = false := by
  decide +kernel

theorem xl_sjs_row_5 :
    rowB2 sD se 128 5 4 169164056156203523876981724517719080960 2 64 1298 5
      = some 6847261709160397795634571520199664386978139759 := by
  decide +kernel

theorem xl_sjs_row_m400 :
    rowB2 sD se 128 5 4 169164056156203523876981724517719080960 2 64 1298 (-400)
      = some 79283275874688326025117032319382108172 := by
  decide +kernel

theorem xl_sjs_row_900 :
    rowB2 sD se 128 5 4 169164056156203523876981724517719080960 2 64 1298 900
      = some 14151256121287797584548271645 := by
  decide +kernel

end KAM.CertificateSharp.V2.XLangBulk2

end
