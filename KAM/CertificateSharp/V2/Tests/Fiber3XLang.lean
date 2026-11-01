/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Shard
public import KAM.CertificateSharp.Freq.CubicNorm

/-!
# Cross-language test of the three-frequency site (generated)

Written by `scripts/certifier/fiber3_xlang.py` from the Python mirror `scripts/certifier/fiber3.py`;
do not edit by hand. Each theorem is a value the mirror computed (`powUpK`, `mode3K`, the walk,
`fiberSiteOk` at an enclosed clock on both sides of the exact bound, `noIntRootIn`, `cubicDioOk` on
both sides of the plastic number's constant `γ = 1/W̄ ≈ 1.000000`), decided by the kernel.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.XLang3

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Fiber
  KAM.CertificateSharp.Cubic

def xD : DBox2 where
  q := 64
  C0 := 23241441160490167842
  C1 := 29282380947994691627
  R0 := 1
  R1 := 1

def xe : ℕ := 798426701374636497

def xDw : DBox2 where
  q := 64
  C0 := 23241441160490167842
  C1 := 29282380947994691627
  R0 := 288230376151711745
  R1 := 1

def xBox : FreqBox :=
  [
    (100000000000000000000000000 /
        94622711231767573282922061,
      1 / 100000000000000),
    (50000000000000000000000000000000000000000000000000000 /
        62674202365953312858911031967565729526105590203414047,
      1 / 100000000000000),
    (7 /
        5,
      1 / 1000000000000000)]

def xD2 : DBox2 where
  q := 64
  C0 := 13925035116211876495
  C1 := 10511698010929265437
  R0 := 141710
  R1 := 139271

def xW : FibWit where
  N := 7
  l := 4
  J := 17
  P := 64
  e := 798426701374636497
  D := xD2
  B := 1123370021854346505413086506453650217106613633 /
    990791918021509120000000000000000000000000000

def xWlow : FibWit where
  N := 7
  l := 4
  J := 17
  P := 64
  e := 798426701374636497
  D := xD2
  B := 274260259241783814798116822864660697535770154738329553 /
    241892558110720000000000000000000000000000000000000000

def xc : ℚ :=
  213993263922674361 /
    100000000000000000000

def xcLow : ℚ :=
  5349831598066859 /
    2500000000000000000

def xθ : ℚ :=
  662358978622373012980454427 /
    500000000000000000000000000

def xθr : ℚ :=
  1 /
    100000000000000000000000000

def xI : Fin 3 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

theorem xl_pow_0 :
    powUpK xe 64 64 0 = 18446744073709551616 := by
  decide +kernel

theorem xl_pow_1 :
    powUpK xe 64 64 1 = 798426701374636497 := by
  decide +kernel

theorem xl_pow_2 :
    powUpK xe 64 64 2 = 34558141801106897 := by
  decide +kernel

theorem xl_pow_7 :
    powUpK xe 64 64 7 = 5249609899 := by
  decide +kernel

theorem xl_pow_63 :
    powUpK xe 64 64 63 = 1 := by
  decide +kernel

theorem xl_pow_200 :
    powUpK xe 64 64 200 = 1 := by
  decide +kernel

theorem xl_mode_1_0 :
    mode3K xD xe 64 1 0 = some 3957766148864965025 := by
  decide +kernel

theorem xl_mode_0_1 :
    mode3K xD xe 64 0 1 = some 616176302767346545 := by
  decide +kernel

theorem xl_mode_3_m2 :
    mode3K xD xe 64 3 (-2) = some 12872226722496 := by
  decide +kernel

theorem xl_mode_m5_7 :
    mode3K xD xe 64 (-5) 7 = some 322 := by
  decide +kernel

theorem xl_mode_2_2 :
    mode3K xD xe 64 2 2 = some 22617157511605 := by
  decide +kernel

theorem xl_mode_wide :
    mode3K xDw xe 64 3 (-2) = some 13095590592242 := by
  decide +kernel

theorem xl_walk_t3 :
    walk2 (mode3K xD xe 64) 7 4 = some 9963506458319161756 := by
  decide +kernel

theorem xl_shard_lo :
    balFold (row2 (mode3K xD xe 64) 7 4) 3 0 = some 5615051464188665581 := by
  decide +kernel

theorem xl_shard_hi :
    balFold (row2 (mode3K xD xe 64) 7 4) 3 (0 + pow2 3) = some 4348454994130496175 := by
  decide +kernel

theorem xl_shard_walk :
    walk2 (mode3K xD xe 64) 7 4 = some (5615051464188665581 + 4348454994130496175) :=
  balFold_succ_of xl_shard_lo xl_shard_hi

theorem xl_walk_clock :
    walk2 (mode3K xD2 798426701374636497 64) 7 4 = some 18266388425585659688 := by
  decide +kernel

theorem xl_site_exact :
    fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xc xW = true := by
  decide +kernel

theorem xl_site_low :
    fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xc xWlow = false := by
  decide +kernel

theorem xl_site_c_low :
    fiberSiteOk 3 2 xBox (1 / 10) (1 / 4) xcLow xW = false := by
  decide +kernel

theorem xl_cubic_ok :
    cubicDioOk (-1) (-1) 0 xθ xθr xI 1 (1 : ℚ) = true := by
  decide +kernel

theorem xl_cubic_bad :
    cubicDioOk (-1) (-1) 0 xθ xθr xI 1 (1000000001 / 1000000000 : ℚ) = false := by
  decide +kernel

theorem xl_noroot_2_0_0 :
    noIntRootIn (-2) 0 0 = true := by
  decide +kernel

theorem xl_noroot_1_1_0 :
    noIntRootIn (-1) (-1) 0 = true := by
  decide +kernel

theorem xl_noroot_8_0_0 :
    noIntRootIn (-8) 0 0 = false := by
  decide +kernel

theorem xl_noroot_6_5_2 :
    noIntRootIn 6 (-5) (-2) = false := by
  decide +kernel

end KAM.CertificateSharp.V2.XLang3

end
