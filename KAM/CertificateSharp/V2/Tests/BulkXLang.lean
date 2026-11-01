/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.BulkSite

/-!
# Cross-language test of the bulk walk (generated)

Written by `scripts/certifier/fiber3_bulk_xlang.py` from the Python mirror
`scripts/certifier/fiber3_bulk.py`; do not edit by hand. Each theorem is a value the mirror
computed, decided by the kernel: `gTabOk0`, `blkValK`, `blkK` on single fibres (where it equals
`mode3K`) and on runs, `hrow`, `rowB` and `walkB` on the toy box of `Tests/BulkToy.lean`,
`bulkSiteOk` on both sides of the exact bound and constant, and three rows of the SJS-plan
frequencies at `P = 128`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLangBulk

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber

def xD : DBox2 where
  q := 64
  C0 := 4794697086780616226
  C1 := 5688115913796535
  R0 := 1
  R1 := 1

def xe : ℕ := 12458310147371035356

def xgs : List ℕ :=
  [18446744073709551616,
    30905054221080586972,
    45001458336540984073,
    54363794943125628117,
    56716812093148074112,
    56823065402654247868,
    56823264830577248318,
    56823264831277168957,
    56823264831277168961]

def xgsBad : List ℕ :=
  [18446744073709551616,
    30905054221080586972,
    45001458336540984073,
    54363794943125628117,
    56716812093148074112,
    56823065402654247868,
    56823264830577248318,
    56823264831277168957,
    56823264831277168960]

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

def xW : BulkWit where
  N := 65
  l := 8
  J := 9
  P := 64
  e := 12458310147371035356
  D := xD
  B := 1011490148075706059756812272913099 /
    56570630050845081940787200
  gs := xgs
  rn := 5
  rd := 4
  tol := 328855130085325568

def xWlow : BulkWit where
  N := 65
  l := 8
  J := 9
  P := 64
  e := 12458310147371035356
  D := xD
  B := 367977972228147722401195013994983673910610377786485673639587 /
    20580275322880000000000000000000000000000000000000000
  gs := xgs
  rn := 5
  rd := 4
  tol := 328855130085325568

def xc : ℚ :=
  14313769621591287 /
    25000000000000000000

def xcLow : ℚ :=
  57255078486365147 /
    100000000000000000000

def sD : DBox2 where
  q := 64
  C0 := 7431879174714169321
  C1 := (-4065032337688588)
  R0 := 1
  R1 := 1

def se : ℕ := 329143111507102215117200415767567212277

def sgs : List ℕ :=
  [340282366920938463463374607431768211456,
    669425478428040678580575023199335423733,
    1295740587141280273509381466481009034669,
    2429965975105657297210566442678434207368,
    4291893600259888840558473350296646081390,
    6811740488664334816563701581880133120093,
    9159796788962541572418722665656465503028,
    10248192101752351568967226083645371842620,
    10392885562936671574915879470906604291299,
    10394957322922745436953222311886033284170,
    10394957735998116695621697067346385131604,
    10394957735998133110433592905387730703370,
    10394957735998133110433592905413651544652]

theorem xl_gtab_ok :
    gTabOk0 xe 64 xgs = true := by
  decide +kernel

theorem xl_gtab_bad :
    gTabOk0 xe 64 xgsBad = false := by
  decide +kernel

theorem xl_val_1_0 :
    blkValK xD xe 64 1 18446744073709551616 3000000000000000 0 = 471038202016141022871437615 := by
  decide +kernel

theorem xl_val_7_3 :
    blkValK xD xe 64 7 54363794943125628117 50000000000000000 (-2) = 216322441336197104864748 := by
  decide +kernel

theorem xl_val_40_6 :
    blkValK xD xe 64 40 56823264830577248318 1000000000000 11 = 39162989550266176250719329 := by
  decide +kernel

theorem xl_fibre_3_p_5 :
    blkK xD xe 64 (pow2 64) (fun _ _ _ => true) 3 1 0 5 5 = some 18408611359651146288 := by
  decide +kernel

theorem xl_mode_3_p_5 :
    mode3K xD xe 64 3 5 = some 18408611359651146288 := by
  decide +kernel

theorem xl_fibre_4_m_2 :
    blkK xD xe 64 (pow2 64) (fun _ _ _ => true) (-4) (-1) 1 2 2 = some 494718892114763390443 := by
  decide +kernel

theorem xl_mode_4_m_2 :
    mode3K xD xe 64 (-4) (-3) = some 494718892114763390443 := by
  decide +kernel

theorem xl_fibre_0_p_0 :
    blkK xD xe 64 (pow2 64) (fun _ _ _ => true) 0 1 1 0 0 = some 131027336001597966103384948 := by
  decide +kernel

theorem xl_mode_0_p_0 :
    mode3K xD xe 64 0 1 = some 131027336001597966103384948 := by
  decide +kernel

theorem xl_fibre_17_m_30 :
    blkK xD xe 64 (pow2 64) (fun _ _ _ => true) 17 (-1) 1 30 30 = some 759247018213 := by
  decide +kernel

theorem xl_mode_17_m_30 :
    mode3K xD xe 64 17 (-31) = some 759247018213 := by
  decide +kernel

theorem xl_run_acc :
    blkK xD xe 64 56823264831277168961 (accOk 5 4 328855130085325568) 1 1 0 0 64
      = some 757442261382924390229 := by
  decide +kernel

theorem xl_run_rej :
    blkK xD xe 64 56823264831277168961 (accOk 5 4 328855130085325568) 4 1 0 0 61 = none := by
  decide +kernel

theorem xl_row_0 :
    rowB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8 0
      = some 329475814363222560474717814 := by
  decide +kernel

theorem xl_row_4 :
    rowB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8 4
      = some 9714934936319554993953 := by
  decide +kernel

theorem xl_row_m23 :
    rowB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8 (-23)
      = some 2602784887084666534 := by
  decide +kernel

theorem xl_row_65 :
    rowB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8 65 = some 2388749905 := by
  decide +kernel

theorem xl_row_66 :
    rowB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8 66 = some 0 := by
  decide +kernel

theorem xl_hrow_4m :
    hrow xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 4 (-1) 1 61 8 0
      = some 4539543506449646168293 := by
  decide +kernel

theorem xl_walk_toy :
    walkB xD xe 64 (fun t => xgs.getD t 0) 5 4 328855130085325568 65 8
      = some 329502561009905771936414713 := by
  decide +kernel

theorem xl_site_exact :
    bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xW = true := by
  decide +kernel

theorem xl_site_low :
    bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xc xWlow = false := by
  decide +kernel

theorem xl_site_c_low :
    bulkSiteOk 3 2 xBox (77 / 250000) (1 / 32) xcLow xW = false := by
  decide +kernel

theorem xl_sjs_row_5 :
    rowB sD se 128 (fun t => sgs.getD t 0) 5 4 169164056156203523876981724517719080960 1298 12 5
      = some 6825857840458407778931524396476838545468141829 := by
  decide +kernel

theorem xl_sjs_row_m400 :
    rowB sD se 128 (fun t => sgs.getD t 0) 5 4 169164056156203523876981724517719080960 1298 12
      (-400) = some 290307988944867800894601822142200379 := by
  decide +kernel

theorem xl_sjs_row_900 :
    rowB sD se 128 (fun t => sgs.getD t 0) 5 4 169164056156203523876981724517719080960 1298 12 900
      = some 14151280699358185278252685780 := by
  decide +kernel

end KAM.CertificateSharp.V2.XLangBulk

end
