/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.CsegJet
public import KAM.SpinOrbit.Data.CsegSupport
public import KAM.SpinOrbit.Data.Lower.Cert
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow00
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow01
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow02
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow03
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow04
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow05
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow06
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow07
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow08
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow09
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow10
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow100
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow101
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow102
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow103
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow104
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow105
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow106
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow107
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow108
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow109
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow11
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow110
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow111
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow112
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow113
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow114
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow115
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow116
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow117
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow118
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow119
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow12
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow120
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow121
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow122
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow123
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow13
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow14
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow15
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow16
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow17
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow18
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow19
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow20
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow21
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow22
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow23
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow24
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow25
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow26
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow27
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow28
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow29
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow30
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow31
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow32
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow33
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow34
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow35
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow36
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow37
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow38
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow39
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow40
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow41
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow42
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow43
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow44
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow45
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow46
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow47
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow48
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow49
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow50
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow51
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow52
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow53
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow54
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow55
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow56
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow57
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow58
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow59
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow60
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow61
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow62
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow63
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow64
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow65
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow66
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow67
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow68
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow69
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow70
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow71
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow72
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow73
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow74
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow75
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow76
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow77
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow78
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow79
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow80
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow81
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow82
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow83
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow84
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow85
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow86
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow87
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow88
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow89
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow90
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow91
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow92
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow93
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow94
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow95
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow96
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow97
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow98
public import KAM.SpinOrbit.Data.Lower.Seg.LedgerLow99

/-!
# The lower plan of the cfgLow chain (generated)

Segments, boundary metadata and ledger (untrusted data; `planOk`/`segOk` check them).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.Lower

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

/-- The segments of the cfgLow chain. -/
def lowerLowCkptSegs : List SegSpec := [
  ⟨0, 28,
    [0, 1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22, 24, 26, 27],
    [],
    [0, 1, 3, 19, 26, 27]⟩,
  ⟨28, 29, [28], [], [28]⟩,
  ⟨29, 86,
    [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
      68, 69],
    [28],
    [30, 32, 34, 36, 38, 40, 59, 61, 63, 65, 67, 69]⟩,
  ⟨86, 109,
    [86, 88, 89, 90, 91, 92, 93, 102, 104, 105, 106, 107, 108],
    [30, 32, 34, 36, 38, 40, 59, 61, 63, 65, 67],
    [88, 89, 90, 91, 92, 93, 102, 104, 105, 106, 107, 108]⟩,
  ⟨109, 148,
    [109, 119, 120, 121, 122, 123, 124, 134, 135, 136, 137, 138, 139],
    [27, 69, 88, 89, 90, 91, 92, 93, 102, 104, 105, 106, 107, 108],
    [134, 135, 136, 137, 138, 139]⟩,
  ⟨148, 182,
    [148, 149, 150, 151, 152, 153, 156, 157, 158, 159, 160, 163, 165, 166, 168, 170, 171, 174, 175,
      178, 179, 181],
    [],
    [178, 179, 181]⟩,
  ⟨182, 240,
    [182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 211, 212, 213, 214, 215, 216,
      217, 218, 219, 220, 221, 222, 223],
    [],
    [184, 186, 188, 190, 192, 194, 213, 215, 217, 219, 221, 223]⟩,
  ⟨240, 263,
    [240, 242, 243, 244, 245, 246, 247, 256, 258, 259, 260, 261, 262],
    [184, 186, 188, 190, 192, 194, 213, 215, 217, 219, 221],
    [242, 243, 244, 245, 246, 247, 256, 258, 259, 260, 261, 262]⟩,
  ⟨263, 303,
    [263, 273, 274, 275, 276, 277, 278, 288, 289, 290, 291, 292, 293, 302],
    [181, 223, 242, 243, 244, 245, 246, 247, 256, 258, 259, 260, 261, 262],
    [288, 289, 290, 291, 292, 293, 302]⟩,
  ⟨303, 361,
    [303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 332, 333, 334, 335, 336, 337,
      338, 339, 340, 341, 342, 343, 344],
    [],
    [305, 307, 309, 311, 313, 315, 334, 336, 338, 340, 342, 344]⟩,
  ⟨361, 395,
    [361, 363, 364, 365, 366, 367, 368, 377, 379, 380, 381, 382, 383, 384, 394],
    [305, 307, 309, 311, 313, 315, 334, 336, 338, 340, 342, 344],
    [364, 365, 366, 367, 368, 380, 381, 382, 383, 384, 394]⟩,
  ⟨395, 424,
    [395, 396, 397, 398, 399, 409, 410, 411, 412, 413, 414, 423],
    [302, 364, 365, 366, 367, 368, 380, 381, 382, 383, 384, 394],
    [409, 410, 411, 412, 413, 414, 423]⟩,
  ⟨424, 482,
    [424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 453, 454, 455, 456, 457, 458,
      459, 460, 461, 462, 463, 464, 465],
    [],
    [426, 428, 430, 432, 434, 436, 455, 457, 459, 461, 463, 465]⟩,
  ⟨482, 516,
    [482, 484, 485, 486, 487, 488, 489, 498, 500, 501, 502, 503, 504, 505, 515],
    [426, 428, 430, 432, 434, 436, 455, 457, 459, 461, 463, 465],
    [485, 486, 487, 488, 489, 501, 502, 503, 504, 505, 515]⟩,
  ⟨516, 545,
    [516, 517, 518, 519, 520, 530, 531, 532, 533, 534, 535, 544],
    [423, 485, 486, 487, 488, 489, 501, 502, 503, 504, 505, 515],
    [530, 531, 532, 533, 534, 535, 544]⟩,
  ⟨545, 603,
    [545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 574, 575, 576, 577, 578, 579,
      580, 581, 582, 583, 584, 585, 586],
    [],
    [547, 549, 551, 553, 555, 557, 576, 578, 580, 582, 584, 586]⟩,
  ⟨603, 606, [603, 605], [547], [603, 605]⟩,
  ⟨606, 638,
    [606, 607, 608, 609, 610, 619, 621, 622, 623, 624, 625, 626, 636, 637],
    [549, 551, 553, 555, 557, 576, 578, 580, 582, 584, 586, 603, 605],
    [607, 608, 609, 610, 623, 624, 625, 626, 636, 637]⟩,
  ⟨638, 666,
    [638, 639, 640, 641, 651, 652, 653, 654, 655, 656, 665],
    [544, 607, 608, 609, 610, 623, 624, 625, 626, 636, 637],
    [651, 652, 653, 654, 655, 656, 665]⟩,
  ⟨666, 724,
    [666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 695, 696, 697, 698, 699, 700,
      701, 702, 703, 704, 705, 706, 707],
    [],
    [668, 670, 672, 674, 676, 678, 697, 699, 701, 703, 705, 707]⟩,
  ⟨724, 743,
    [724, 726, 727, 728, 729, 730, 731, 740, 742],
    [668, 670, 672, 674, 676, 678, 697],
    [726, 727, 728, 729, 730, 731, 740, 742]⟩,
  ⟨743, 774,
    [743, 744, 745, 746, 747, 757, 758, 759, 760, 761, 762, 772, 773],
    [665, 699, 701, 703, 705, 707, 726, 727, 728, 729, 730, 731, 740, 742],
    [759, 760, 761, 762, 772, 773]⟩,
  ⟨774, 804,
    [774, 775, 776, 777, 789, 790, 791, 792, 793, 794],
    [651, 652, 653, 654, 655, 656, 665, 759, 760, 761, 762, 772, 773],
    [789, 790, 791, 792, 793, 794]⟩,
  ⟨804, 836,
    [804, 805, 806, 807, 808, 809, 819, 820, 821, 822, 823, 824, 834, 835],
    [288, 289, 409, 410, 411, 412, 413, 414, 530, 531, 532, 533, 534, 535, 789, 790, 791, 792, 793,
      794],
    [821, 822, 823, 824, 834, 835]⟩,
  ⟨836, 871,
    [836, 837, 838, 839, 849, 850, 853, 854, 855, 856, 857, 858, 870],
    [1, 134, 135, 136, 137, 138, 139, 178, 179, 290, 291, 292, 293, 821, 822, 823, 824, 834, 835],
    [854, 855, 856, 857, 858, 870]⟩,
  ⟨871, 887,
    [871, 872, 873, 874, 875, 876, 877, 878],
    [1, 3, 19, 26, 854, 855, 856, 857, 858],
    [871, 872, 873, 874, 875, 876, 877, 878]⟩]

/-- The boundary metadata. -/
def lowerLowCkptMetas : List (ComposeMeta SoBackendV2) := [
  ⟨0, 0, 0, []⟩,
  ⟨28, 0, 0, []⟩,
  ⟨29, 0, 0, [([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨86, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨109, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨148, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨182, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨240, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨263, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨303, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨361, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨395, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨424, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨482, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨516, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨545, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨603, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨606, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨638, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨666, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨724, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨743, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨774, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨804, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨836, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨871, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩,
  ⟨887, 0, 0, [([-2, 0], (⟨charE⟩ : CertPoly SoBackendV2).reflectSorted, (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2)), ([2, 0], (⟨charE⟩ : CertPoly SoBackendV2), (⟨0x3dcd6d8044972fd53fb⟩ :
    SoBackendV2))]⟩]

/-- The ledger. -/
def lowerLowCkptLedger : List (ℕ × (CertModel SoBackendV2 × SoBackendV2)) := [
  (0, (lowerL0, lowerL0N)),
  (1, (lowerL1, lowerL1N)),
  (3, (lowerL3, lowerL3N)),
  (19, (lowerL19, lowerL19N)),
  (26, (lowerL26, lowerL26N)),
  (27, (lowerL27, lowerL27N)),
  (28, (lowerL28, lowerL28N)),
  (30, (lowerL30, lowerL30N)),
  (32, (lowerL32, lowerL32N)),
  (34, (lowerL34, lowerL34N)),
  (36, (lowerL36, lowerL36N)),
  (38, (lowerL38, lowerL38N)),
  (40, (lowerL40, lowerL40N)),
  (59, (lowerL59, lowerL59N)),
  (61, (lowerL61, lowerL61N)),
  (63, (lowerL63, lowerL63N)),
  (65, (lowerL65, lowerL65N)),
  (67, (lowerL67, lowerL67N)),
  (69, (lowerL69, lowerL69N)),
  (88, (lowerL88, lowerL88N)),
  (89, (lowerL89, lowerL89N)),
  (90, (lowerL90, lowerL90N)),
  (91, (lowerL91, lowerL91N)),
  (92, (lowerL92, lowerL92N)),
  (93, (lowerL93, lowerL93N)),
  (102, (lowerL102, lowerL102N)),
  (104, (lowerL104, lowerL104N)),
  (105, (lowerL105, lowerL105N)),
  (106, (lowerL106, lowerL106N)),
  (107, (lowerL107, lowerL107N)),
  (108, (lowerL108, lowerL108N)),
  (134, (lowerL134, lowerL134N)),
  (135, (lowerL135, lowerL135N)),
  (136, (lowerL136, lowerL136N)),
  (137, (lowerL137, lowerL137N)),
  (138, (lowerL138, lowerL138N)),
  (139, (lowerL139, lowerL139N)),
  (178, (lowerL178, lowerL178N)),
  (179, (lowerL179, lowerL179N)),
  (181, (lowerL181, lowerL181N)),
  (184, (lowerL184, lowerL184N)),
  (186, (lowerL186, lowerL186N)),
  (188, (lowerL188, lowerL188N)),
  (190, (lowerL190, lowerL190N)),
  (192, (lowerL192, lowerL192N)),
  (194, (lowerL194, lowerL194N)),
  (213, (lowerL213, lowerL213N)),
  (215, (lowerL215, lowerL215N)),
  (217, (lowerL217, lowerL217N)),
  (219, (lowerL219, lowerL219N)),
  (221, (lowerL221, lowerL221N)),
  (223, (lowerL223, lowerL223N)),
  (242, (lowerL242, lowerL242N)),
  (243, (lowerL243, lowerL243N)),
  (244, (lowerL244, lowerL244N)),
  (245, (lowerL245, lowerL245N)),
  (246, (lowerL246, lowerL246N)),
  (247, (lowerL247, lowerL247N)),
  (256, (lowerL256, lowerL256N)),
  (258, (lowerL258, lowerL258N)),
  (259, (lowerL259, lowerL259N)),
  (260, (lowerL260, lowerL260N)),
  (261, (lowerL261, lowerL261N)),
  (262, (lowerL262, lowerL262N)),
  (288, (lowerL288, lowerL288N)),
  (289, (lowerL289, lowerL289N)),
  (290, (lowerL290, lowerL290N)),
  (291, (lowerL291, lowerL291N)),
  (292, (lowerL292, lowerL292N)),
  (293, (lowerL293, lowerL293N)),
  (302, (lowerL302, lowerL302N)),
  (305, (lowerL305, lowerL305N)),
  (307, (lowerL307, lowerL307N)),
  (309, (lowerL309, lowerL309N)),
  (311, (lowerL311, lowerL311N)),
  (313, (lowerL313, lowerL313N)),
  (315, (lowerL315, lowerL315N)),
  (334, (lowerL334, lowerL334N)),
  (336, (lowerL336, lowerL336N)),
  (338, (lowerL338, lowerL338N)),
  (340, (lowerL340, lowerL340N)),
  (342, (lowerL342, lowerL342N)),
  (344, (lowerL344, lowerL344N)),
  (364, (lowerL364, lowerL364N)),
  (365, (lowerL365, lowerL365N)),
  (366, (lowerL366, lowerL366N)),
  (367, (lowerL367, lowerL367N)),
  (368, (lowerL368, lowerL368N)),
  (380, (lowerL380, lowerL380N)),
  (381, (lowerL381, lowerL381N)),
  (382, (lowerL382, lowerL382N)),
  (383, (lowerL383, lowerL383N)),
  (384, (lowerL384, lowerL384N)),
  (394, (lowerL394, lowerL394N)),
  (409, (lowerL409, lowerL409N)),
  (410, (lowerL410, lowerL410N)),
  (411, (lowerL411, lowerL411N)),
  (412, (lowerL412, lowerL412N)),
  (413, (lowerL413, lowerL413N)),
  (414, (lowerL414, lowerL414N)),
  (423, (lowerL423, lowerL423N)),
  (426, (lowerL426, lowerL426N)),
  (428, (lowerL428, lowerL428N)),
  (430, (lowerL430, lowerL430N)),
  (432, (lowerL432, lowerL432N)),
  (434, (lowerL434, lowerL434N)),
  (436, (lowerL436, lowerL436N)),
  (455, (lowerL455, lowerL455N)),
  (457, (lowerL457, lowerL457N)),
  (459, (lowerL459, lowerL459N)),
  (461, (lowerL461, lowerL461N)),
  (463, (lowerL463, lowerL463N)),
  (465, (lowerL465, lowerL465N)),
  (485, (lowerL485, lowerL485N)),
  (486, (lowerL486, lowerL486N)),
  (487, (lowerL487, lowerL487N)),
  (488, (lowerL488, lowerL488N)),
  (489, (lowerL489, lowerL489N)),
  (501, (lowerL501, lowerL501N)),
  (502, (lowerL502, lowerL502N)),
  (503, (lowerL503, lowerL503N)),
  (504, (lowerL504, lowerL504N)),
  (505, (lowerL505, lowerL505N)),
  (515, (lowerL515, lowerL515N)),
  (530, (lowerL530, lowerL530N)),
  (531, (lowerL531, lowerL531N)),
  (532, (lowerL532, lowerL532N)),
  (533, (lowerL533, lowerL533N)),
  (534, (lowerL534, lowerL534N)),
  (535, (lowerL535, lowerL535N)),
  (544, (lowerL544, lowerL544N)),
  (547, (lowerL547, lowerL547N)),
  (549, (lowerL549, lowerL549N)),
  (551, (lowerL551, lowerL551N)),
  (553, (lowerL553, lowerL553N)),
  (555, (lowerL555, lowerL555N)),
  (557, (lowerL557, lowerL557N)),
  (576, (lowerL576, lowerL576N)),
  (578, (lowerL578, lowerL578N)),
  (580, (lowerL580, lowerL580N)),
  (582, (lowerL582, lowerL582N)),
  (584, (lowerL584, lowerL584N)),
  (586, (lowerL586, lowerL586N)),
  (603, (lowerL603, lowerL603N)),
  (605, (lowerL605, lowerL605N)),
  (607, (lowerL607, lowerL607N)),
  (608, (lowerL608, lowerL608N)),
  (609, (lowerL609, lowerL609N)),
  (610, (lowerL610, lowerL610N)),
  (623, (lowerL623, lowerL623N)),
  (624, (lowerL624, lowerL624N)),
  (625, (lowerL625, lowerL625N)),
  (626, (lowerL626, lowerL626N)),
  (636, (lowerL636, lowerL636N)),
  (637, (lowerL637, lowerL637N)),
  (651, (lowerL651, lowerL651N)),
  (652, (lowerL652, lowerL652N)),
  (653, (lowerL653, lowerL653N)),
  (654, (lowerL654, lowerL654N)),
  (655, (lowerL655, lowerL655N)),
  (656, (lowerL656, lowerL656N)),
  (665, (lowerL665, lowerL665N)),
  (668, (lowerL668, lowerL668N)),
  (670, (lowerL670, lowerL670N)),
  (672, (lowerL672, lowerL672N)),
  (674, (lowerL674, lowerL674N)),
  (676, (lowerL676, lowerL676N)),
  (678, (lowerL678, lowerL678N)),
  (697, (lowerL697, lowerL697N)),
  (699, (lowerL699, lowerL699N)),
  (701, (lowerL701, lowerL701N)),
  (703, (lowerL703, lowerL703N)),
  (705, (lowerL705, lowerL705N)),
  (707, (lowerL707, lowerL707N)),
  (726, (lowerL726, lowerL726N)),
  (727, (lowerL727, lowerL727N)),
  (728, (lowerL728, lowerL728N)),
  (729, (lowerL729, lowerL729N)),
  (730, (lowerL730, lowerL730N)),
  (731, (lowerL731, lowerL731N)),
  (740, (lowerL740, lowerL740N)),
  (742, (lowerL742, lowerL742N)),
  (759, (lowerL759, lowerL759N)),
  (760, (lowerL760, lowerL760N)),
  (761, (lowerL761, lowerL761N)),
  (762, (lowerL762, lowerL762N)),
  (772, (lowerL772, lowerL772N)),
  (773, (lowerL773, lowerL773N)),
  (789, (lowerL789, lowerL789N)),
  (790, (lowerL790, lowerL790N)),
  (791, (lowerL791, lowerL791N)),
  (792, (lowerL792, lowerL792N)),
  (793, (lowerL793, lowerL793N)),
  (794, (lowerL794, lowerL794N)),
  (821, (lowerL821, lowerL821N)),
  (822, (lowerL822, lowerL822N)),
  (823, (lowerL823, lowerL823N)),
  (824, (lowerL824, lowerL824N)),
  (834, (lowerL834, lowerL834N)),
  (835, (lowerL835, lowerL835N)),
  (854, (lowerL854, lowerL854N)),
  (855, (lowerL855, lowerL855N)),
  (856, (lowerL856, lowerL856N)),
  (857, (lowerL857, lowerL857N)),
  (858, (lowerL858, lowerL858N)),
  (870, (lowerL870, lowerL870N)),
  (871, (lowerL871, lowerL871N)),
  (872, (lowerL872, lowerL872N)),
  (873, (lowerL873, lowerL873N)),
  (874, (lowerL874, lowerL874N)),
  (875, (lowerL875, lowerL875N)),
  (876, (lowerL876, lowerL876N)),
  (877, (lowerL877, lowerL877N)),
  (878, (lowerL878, lowerL878N))]

/-- The checkpointed cfgLow composition. -/
def lowerLowCkpt : ComposeCkpt SoBackendV2 := ⟨lowerLowCkptSegs, lowerLowCkptMetas,
    lowerLowCkptLedger⟩

end KAM.SpinOrbit.Data.Lower
