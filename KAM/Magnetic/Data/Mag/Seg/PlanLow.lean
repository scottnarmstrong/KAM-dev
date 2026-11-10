/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Data.CsegJet
public import KAM.Magnetic.Data.Mag.Cert
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow00
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow01
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow02
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow03
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow04
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow05
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow06
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow07
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow08
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow09
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow10
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow100
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow101
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow102
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow103
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow104
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow105
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow106
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow107
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow108
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow109
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow11
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow110
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow111
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow112
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow113
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow114
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow115
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow116
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow117
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow118
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow119
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow12
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow120
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow121
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow122
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow123
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow124
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow125
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow126
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow127
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow128
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow129
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow13
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow130
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow131
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow132
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow133
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow134
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow135
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow136
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow137
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow138
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow139
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow14
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow140
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow141
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow142
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow143
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow144
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow145
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow146
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow147
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow148
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow149
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow15
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow150
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow151
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow152
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow153
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow154
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow155
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow156
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow157
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow158
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow159
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow16
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow160
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow161
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow162
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow163
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow164
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow165
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow166
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow167
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow168
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow169
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow17
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow170
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow171
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow172
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow173
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow174
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow175
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow176
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow177
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow178
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow179
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow18
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow180
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow181
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow182
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow183
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow184
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow185
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow186
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow187
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow188
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow189
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow19
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow190
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow191
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow192
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow193
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow194
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow195
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow196
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow197
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow198
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow199
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow20
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow200
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow201
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow202
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow203
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow204
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow205
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow206
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow207
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow208
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow209
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow21
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow210
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow211
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow212
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow213
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow214
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow215
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow216
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow217
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow218
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow219
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow22
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow220
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow221
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow222
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow223
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow224
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow225
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow226
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow227
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow228
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow229
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow23
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow230
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow231
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow232
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow233
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow234
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow235
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow236
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow237
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow238
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow239
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow24
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow240
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow241
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow242
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow243
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow244
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow245
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow246
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow247
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow248
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow249
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow25
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow250
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow251
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow252
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow253
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow254
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow255
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow256
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow257
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow258
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow259
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow26
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow260
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow261
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow262
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow263
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow264
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow265
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow266
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow267
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow268
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow269
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow27
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow270
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow271
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow272
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow273
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow274
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow275
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow276
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow277
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow278
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow279
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow28
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow280
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow281
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow282
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow283
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow284
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow285
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow29
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow30
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow31
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow32
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow33
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow34
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow35
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow36
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow37
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow38
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow39
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow40
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow41
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow42
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow43
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow44
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow45
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow46
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow47
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow48
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow49
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow50
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow51
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow52
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow53
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow54
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow55
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow56
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow57
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow58
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow59
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow60
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow61
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow62
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow63
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow64
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow65
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow66
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow67
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow68
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow69
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow70
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow71
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow72
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow73
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow74
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow75
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow76
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow77
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow78
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow79
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow80
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow81
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow82
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow83
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow84
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow85
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow86
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow87
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow88
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow89
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow90
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow91
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow92
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow93
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow94
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow95
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow96
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow97
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow98
public import KAM.Magnetic.Data.Mag.Seg.LedgerLow99
public import KAM.Magnetic.Support.CsegSupport

/-!
# The mag plan of the cfgLow chain (generated)

Segments, boundary metadata and ledger (untrusted data; `planOk`/`segOk` check them).
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

/-- The segments of the cfgLow chain. -/
def magLowCkptSegs : List SegSpec := [
  ⟨0, 19, [0, 2, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17], [], [0, 2, 4, 5, 14, 17]⟩,
  ⟨19, 27, [19, 20, 21, 22, 23, 24, 25, 26], [5, 14, 17], [19, 20, 21, 22, 23, 25, 26]⟩,
  ⟨27, 28, [27], [22, 25], [27]⟩,
  ⟨28, 35, [28, 29, 30, 31, 32, 33], [22, 23, 25, 26], [30, 33]⟩,
  ⟨35, 36, [35], [22, 30], [35]⟩,
  ⟨36, 41, [36, 37, 38, 39, 40], [22, 23, 27, 30, 33, 35], [37, 40]⟩,
  ⟨41, 53, [41, 42, 49, 50, 52], [21, 23, 30, 37, 40], [49, 50, 52]⟩,
  ⟨53, 58, [53, 54, 55, 56, 57], [], [53, 54, 56, 57]⟩,
  ⟨58, 59, [58], [53, 56], [58]⟩,
  ⟨59, 65, [59, 60, 61, 62, 63, 64], [53, 54, 56, 57], [61, 64]⟩,
  ⟨65, 66, [65], [53, 58], [65]⟩,
  ⟨66, 67, [66], [53, 61], [66]⟩,
  ⟨67, 70, [67, 68, 69], [53, 54, 58, 64, 66], [68, 69]⟩,
  ⟨70, 80, [70, 71, 72, 73], [54, 61, 69], [73]⟩,
  ⟨80, 81, [80], [53, 68], [80]⟩,
  ⟨81, 83, [81, 82], [54, 65, 80], [82]⟩,
  ⟨83, 84, [83], [53, 73], [83]⟩,
  ⟨84, 109,
    [84, 85, 86, 87, 96, 97, 100, 101, 104, 105, 107, 108],
    [4, 19, 20, 49, 50, 52, 54, 68, 82, 83],
    [105, 107, 108]⟩,
  ⟨109, 110, [109], [], [109]⟩,
  ⟨110, 116, [110, 111, 112, 113, 114, 115], [109], [111, 113, 115]⟩,
  ⟨116, 138, [116, 117, 118, 119, 120, 121], [109], [117, 119, 121]⟩,
  ⟨138, 145, [138, 139, 140, 141, 142, 143, 144], [], [138, 140, 142, 144]⟩,
  ⟨145, 167, [145, 146, 147, 148, 149, 150], [138], [146, 148, 150]⟩,
  ⟨167, 172, [167, 169, 170, 171], [111, 113, 115], [167, 169, 170, 171]⟩,
  ⟨172, 183, [172, 173, 174], [117, 119, 121, 167], [172, 173, 174]⟩,
  ⟨183, 188, [183, 185, 186, 187], [140, 142, 144], [183, 185, 186, 187]⟩,
  ⟨188, 201, [188, 189, 190, 200], [146, 148, 150, 169, 183, 185], [188, 189, 190, 200]⟩,
  ⟨201, 214,
    [201, 202, 203, 204, 205],
    [170, 171, 172, 173, 174, 186, 187, 188, 189, 190],
    [201, 202, 203, 204, 205]⟩,
  ⟨214, 215, [214], [], [214]⟩,
  ⟨215, 221, [215, 216, 217, 218, 219, 220], [214], [216, 218, 220]⟩,
  ⟨221, 243, [221, 222, 223, 224, 225, 226], [214], [222, 224, 226]⟩,
  ⟨243, 250, [243, 244, 245, 246, 247, 248, 249], [], [243, 245, 247, 249]⟩,
  ⟨250, 272, [250, 251, 252, 253, 254, 255], [243], [251, 253, 255]⟩,
  ⟨272, 277, [272, 274, 275, 276], [216, 218, 220], [272, 274, 275, 276]⟩,
  ⟨277, 288, [277, 278, 279], [222, 224, 226, 272], [277, 278, 279]⟩,
  ⟨288, 293, [288, 290, 291, 292], [245, 247, 249], [288, 290, 291, 292]⟩,
  ⟨293, 305, [293, 294, 295], [251, 253, 255, 288], [293, 294, 295]⟩,
  ⟨305, 321,
    [305, 306, 307, 308, 309, 310, 320],
    [200, 274, 275, 276, 277, 278, 279, 290, 291, 292, 293, 294, 295],
    [306, 307, 308, 309, 310, 320]⟩,
  ⟨321, 335,
    [321, 322, 323, 324, 325],
    [201, 202, 203, 204, 205, 306, 307, 308, 309, 310],
    [321, 322, 323, 324, 325]⟩,
  ⟨335, 338, [335, 336, 337], [108, 320, 321, 322], [335, 336, 337]⟩,
  ⟨338, 351, [338, 339, 340, 349, 350], [108, 323, 324, 325], [338, 339, 340, 349, 350]⟩,
  ⟨351, 358, [351, 352, 353, 354, 355, 356, 357], [], [351, 353, 355, 357]⟩,
  ⟨358, 380, [358, 359, 360, 361, 362, 363], [351], [359, 361, 363]⟩,
  ⟨380, 387, [380, 381, 382, 383, 384, 385, 386], [], [380, 382, 384, 386]⟩,
  ⟨387, 409, [387, 388, 389, 390, 391, 392], [380], [388, 390, 392]⟩,
  ⟨409, 413, [409, 410, 411, 412], [351, 353, 355], [409, 410, 411, 412]⟩,
  ⟨413, 416, [413, 414, 415], [357, 359, 361, 409], [413, 414, 415]⟩,
  ⟨416, 428, [416, 425, 426, 427], [363, 380, 382, 409], [416, 425, 426, 427]⟩,
  ⟨428, 431, [428, 429, 430], [384, 386, 388, 425], [428, 429, 430]⟩,
  ⟨431, 444,
    [431, 432, 441, 442, 443],
    [390, 392, 410, 411, 412, 425, 426, 427, 428],
    [431, 432, 441, 442, 443]⟩,
  ⟨444, 457,
    [444, 445, 446, 447, 456],
    [350, 413, 414, 415, 416, 429, 430, 431, 432, 441],
    [444, 445, 446, 447, 456]⟩,
  ⟨457, 460, [457, 458, 459], [350, 442, 443, 444], [457, 458, 459]⟩,
  ⟨460, 472, [460, 461, 462, 471], [350, 445, 446, 447], [460, 461, 462, 471]⟩,
  ⟨472, 479, [472, 473, 474, 475, 476, 477, 478], [], [472, 474, 476, 478]⟩,
  ⟨479, 501, [479, 480, 481, 482, 483, 484], [472], [480, 482, 484]⟩,
  ⟨501, 508, [501, 502, 503, 504, 505, 506, 507], [], [501, 503, 505, 507]⟩,
  ⟨508, 530, [508, 509, 510, 511, 512, 513], [501], [509, 511, 513]⟩,
  ⟨530, 534, [530, 531, 532, 533], [472, 474, 476], [530, 531, 532, 533]⟩,
  ⟨534, 537, [534, 535, 536], [478, 480, 482, 530], [534, 535, 536]⟩,
  ⟨537, 549, [537, 546, 547, 548], [484, 501, 503, 530], [537, 546, 547, 548]⟩,
  ⟨549, 552, [549, 550, 551], [505, 507, 509, 546], [549, 550, 551]⟩,
  ⟨552, 565,
    [552, 553, 562, 563, 564],
    [511, 513, 531, 532, 533, 546, 547, 548, 549],
    [552, 553, 562, 563, 564]⟩,
  ⟨565, 578,
    [565, 566, 567, 568, 577],
    [471, 534, 535, 536, 537, 550, 551, 552, 553, 562],
    [565, 566, 567, 568, 577]⟩,
  ⟨578, 581, [578, 579, 580], [471, 563, 564, 565], [578, 579, 580]⟩,
  ⟨581, 592, [581, 582, 583], [471, 566, 567, 568], [581, 582, 583]⟩,
  ⟨592, 598,
    [592, 593, 594, 595, 596, 597],
    [456, 457, 458, 459, 460, 461, 577, 578, 579, 580, 581, 582],
    [592, 593, 594, 595, 596, 597]⟩,
  ⟨598, 610, [598, 607, 608, 609], [462, 583, 592, 593], [598, 607, 608, 609]⟩,
  ⟨610, 613, [610, 611, 612], [594, 595, 596, 607], [610, 611, 612]⟩,
  ⟨613, 624, [613, 614], [597, 598, 607], [613, 614]⟩,
  ⟨624, 625, [624], [592, 609], [624]⟩,
  ⟨625, 626, [625], [593, 608], [625]⟩,
  ⟨626, 627, [626], [624, 625], [626]⟩,
  ⟨627, 628, [627], [592, 610], [627]⟩,
  ⟨628, 629, [628], [594, 608], [628]⟩,
  ⟨629, 630, [629], [627, 628], [629]⟩,
  ⟨630, 631, [630], [592, 611], [630]⟩,
  ⟨631, 632, [631], [593, 609], [631]⟩,
  ⟨632, 633, [632], [630, 631], [632]⟩,
  ⟨633, 634, [633], [593, 609], [633]⟩,
  ⟨634, 635, [634], [595, 608], [634]⟩,
  ⟨635, 637, [635, 636], [632, 633, 634], [636]⟩,
  ⟨637, 638, [637], [592, 612], [637]⟩,
  ⟨638, 639, [638], [593, 610], [638]⟩,
  ⟨639, 640, [639], [637, 638], [639]⟩,
  ⟨640, 641, [640], [594, 609], [640]⟩,
  ⟨641, 642, [641], [596, 608], [641]⟩,
  ⟨642, 644, [642, 643], [639, 640, 641], [643]⟩,
  ⟨644, 645, [644], [592, 613], [644]⟩,
  ⟨645, 646, [645], [594, 609], [645]⟩,
  ⟨646, 647, [646], [644, 645], [646]⟩,
  ⟨647, 648, [647], [593, 610], [647]⟩,
  ⟨648, 649, [648], [597, 608], [648]⟩,
  ⟨649, 651, [649, 650], [646, 647, 648], [650]⟩,
  ⟨651, 652, [651], [592, 614], [651]⟩,
  ⟨652, 653, [652], [594, 610], [652]⟩,
  ⟨653, 654, [653], [651, 652], [653]⟩,
  ⟨654, 655, [654], [594, 610], [654]⟩,
  ⟨655, 656, [655], [598, 608], [655]⟩,
  ⟨656, 783,
    [656, 657, 779, 780, 781, 782],
    [349, 626, 629, 636, 643, 653, 654, 655],
    [657, 779, 780, 781, 782]⟩,
  ⟨783, 810,
    [783, 784, 794, 795, 796, 797, 798, 799],
    [335, 336, 337, 338, 339, 340, 349, 650, 657, 779, 780, 781, 782],
    [794, 795, 796, 797, 798, 799]⟩]

/-- The boundary metadata. -/
def magLowCkptMetas : List (ComposeMeta MagBackend) := [
  ⟨0, 0, 0, []⟩,
  ⟨19, 0, 0, []⟩,
  ⟨27, 0, 0, []⟩,
  ⟨28, 0, 0, []⟩,
  ⟨35, 0, 0, []⟩,
  ⟨36, 0, 0, []⟩,
  ⟨41, 0, 0, []⟩,
  ⟨53, 0, 0, []⟩,
  ⟨58, 0, 0, []⟩,
  ⟨59, 0, 0, []⟩,
  ⟨65, 0, 0, []⟩,
  ⟨66, 0, 0, []⟩,
  ⟨67, 0, 0, []⟩,
  ⟨70, 0, 0, []⟩,
  ⟨80, 0, 0, []⟩,
  ⟨81, 0, 0, []⟩,
  ⟨83, 0, 0, []⟩,
  ⟨84, 0, 0, []⟩,
  ⟨109, 0, 0, []⟩,
  ⟨110, 0, 0, [([2, 0], (⟨charE2⟩ : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ :
    MagBackend))]⟩,
  ⟨116, 0, 0, [([2, 0], (⟨charE2⟩ : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ :
    MagBackend))]⟩,
  ⟨138, 0, 0, [([2, 0], (⟨charE2⟩ : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ :
    MagBackend))]⟩,
  ⟨145, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨167, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨172, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨183, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨188, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨201, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨214, 0, 0, [([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨215, 0, 0, [([3, 0], (⟨charE3⟩ : CertPoly MagBackend), (⟨0x1f86f7c523a870da9c2a39ae158⟩ :
    MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨221, 0, 0, [([3, 0], (⟨charE3⟩ : CertPoly MagBackend), (⟨0x1f86f7c523a870da9c2a39ae158⟩ :
    MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨243, 0, 0, [([3, 0], (⟨charE3⟩ : CertPoly MagBackend), (⟨0x1f86f7c523a870da9c2a39ae158⟩ :
    MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩ : CertPoly MagBackend),
    (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨250, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨272, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨277, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨288, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨293, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨305, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨321, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨335, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨338, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨351, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨358, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨380, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨387, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨409, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨413, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨416, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨428, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨431, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨444, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨457, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨460, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨472, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨479, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨501, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨508, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨530, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨534, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨537, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨549, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨552, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨565, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨578, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨581, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨592, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨598, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨610, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨613, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨624, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨625, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨626, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨627, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨628, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨629, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨630, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨631, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨632, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨633, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨634, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨635, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨637, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨638, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨639, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨640, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨641, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨642, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨644, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨645, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨646, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨647, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨648, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨649, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨651, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨652, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨653, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨654, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨655, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨656, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨783, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩,
  ⟨810, 0, 0, [([-3, 0], (⟨charE3⟩ : CertPoly MagBackend).reflectSorted,
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([3, 0], (⟨charE3⟩ : CertPoly MagBackend),
    (⟨0x1f86f7c523a870da9c2a39ae158⟩ : MagBackend)), ([-2, 0], (⟨charE2⟩ : CertPoly
    MagBackend).reflectSorted, (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend)), ([2, 0], (⟨charE2⟩
    : CertPoly MagBackend), (⟨0x16ccfefb2903c6c5a7f32708c48⟩ : MagBackend))]⟩]

/-- The ledger. -/
def magLowCkptLedger : List (ℕ × (CertModel MagBackend × MagBackend)) := [
  (0, (magL0, magL0N)),
  (2, (magL2, magL2N)),
  (4, (magL4, magL4N)),
  (5, (magL5, magL5N)),
  (14, (magL14, magL14N)),
  (17, (magL17, magL17N)),
  (19, (magL19, magL19N)),
  (20, (magL20, magL20N)),
  (21, (magL21, magL21N)),
  (22, (magL22, magL22N)),
  (23, (magL23, magL23N)),
  (25, (magL25, magL25N)),
  (26, (magL26, magL26N)),
  (27, (magL27, magL27N)),
  (30, (magL30, magL30N)),
  (33, (magL33, magL33N)),
  (35, (magL35, magL35N)),
  (37, (magL37, magL37N)),
  (40, (magL40, magL40N)),
  (49, (magL49, magL49N)),
  (50, (magL50, magL50N)),
  (52, (magL52, magL52N)),
  (53, (magL53, magL53N)),
  (54, (magL54, magL54N)),
  (56, (magL56, magL56N)),
  (57, (magL57, magL57N)),
  (58, (magL58, magL58N)),
  (61, (magL61, magL61N)),
  (64, (magL64, magL64N)),
  (65, (magL65, magL65N)),
  (66, (magL66, magL66N)),
  (68, (magL68, magL68N)),
  (69, (magL69, magL69N)),
  (73, (magL73, magL73N)),
  (80, (magL80, magL80N)),
  (82, (magL82, magL82N)),
  (83, (magL83, magL83N)),
  (105, (magL105, magL105N)),
  (107, (magL107, magL107N)),
  (108, (magL108, magL108N)),
  (109, (magL109, magL109N)),
  (111, (magL111, magL111N)),
  (113, (magL113, magL113N)),
  (115, (magL115, magL115N)),
  (117, (magL117, magL117N)),
  (119, (magL119, magL119N)),
  (121, (magL121, magL121N)),
  (138, (magL138, magL138N)),
  (140, (magL140, magL140N)),
  (142, (magL142, magL142N)),
  (144, (magL144, magL144N)),
  (146, (magL146, magL146N)),
  (148, (magL148, magL148N)),
  (150, (magL150, magL150N)),
  (167, (magL167, magL167N)),
  (169, (magL169, magL169N)),
  (170, (magL170, magL170N)),
  (171, (magL171, magL171N)),
  (172, (magL172, magL172N)),
  (173, (magL173, magL173N)),
  (174, (magL174, magL174N)),
  (183, (magL183, magL183N)),
  (185, (magL185, magL185N)),
  (186, (magL186, magL186N)),
  (187, (magL187, magL187N)),
  (188, (magL188, magL188N)),
  (189, (magL189, magL189N)),
  (190, (magL190, magL190N)),
  (200, (magL200, magL200N)),
  (201, (magL201, magL201N)),
  (202, (magL202, magL202N)),
  (203, (magL203, magL203N)),
  (204, (magL204, magL204N)),
  (205, (magL205, magL205N)),
  (214, (magL214, magL214N)),
  (216, (magL216, magL216N)),
  (218, (magL218, magL218N)),
  (220, (magL220, magL220N)),
  (222, (magL222, magL222N)),
  (224, (magL224, magL224N)),
  (226, (magL226, magL226N)),
  (243, (magL243, magL243N)),
  (245, (magL245, magL245N)),
  (247, (magL247, magL247N)),
  (249, (magL249, magL249N)),
  (251, (magL251, magL251N)),
  (253, (magL253, magL253N)),
  (255, (magL255, magL255N)),
  (272, (magL272, magL272N)),
  (274, (magL274, magL274N)),
  (275, (magL275, magL275N)),
  (276, (magL276, magL276N)),
  (277, (magL277, magL277N)),
  (278, (magL278, magL278N)),
  (279, (magL279, magL279N)),
  (288, (magL288, magL288N)),
  (290, (magL290, magL290N)),
  (291, (magL291, magL291N)),
  (292, (magL292, magL292N)),
  (293, (magL293, magL293N)),
  (294, (magL294, magL294N)),
  (295, (magL295, magL295N)),
  (306, (magL306, magL306N)),
  (307, (magL307, magL307N)),
  (308, (magL308, magL308N)),
  (309, (magL309, magL309N)),
  (310, (magL310, magL310N)),
  (320, (magL320, magL320N)),
  (321, (magL321, magL321N)),
  (322, (magL322, magL322N)),
  (323, (magL323, magL323N)),
  (324, (magL324, magL324N)),
  (325, (magL325, magL325N)),
  (335, (magL335, magL335N)),
  (336, (magL336, magL336N)),
  (337, (magL337, magL337N)),
  (338, (magL338, magL338N)),
  (339, (magL339, magL339N)),
  (340, (magL340, magL340N)),
  (349, (magL349, magL349N)),
  (350, (magL350, magL350N)),
  (351, (magL351, magL351N)),
  (353, (magL353, magL353N)),
  (355, (magL355, magL355N)),
  (357, (magL357, magL357N)),
  (359, (magL359, magL359N)),
  (361, (magL361, magL361N)),
  (363, (magL363, magL363N)),
  (380, (magL380, magL380N)),
  (382, (magL382, magL382N)),
  (384, (magL384, magL384N)),
  (386, (magL386, magL386N)),
  (388, (magL388, magL388N)),
  (390, (magL390, magL390N)),
  (392, (magL392, magL392N)),
  (409, (magL409, magL409N)),
  (410, (magL410, magL410N)),
  (411, (magL411, magL411N)),
  (412, (magL412, magL412N)),
  (413, (magL413, magL413N)),
  (414, (magL414, magL414N)),
  (415, (magL415, magL415N)),
  (416, (magL416, magL416N)),
  (425, (magL425, magL425N)),
  (426, (magL426, magL426N)),
  (427, (magL427, magL427N)),
  (428, (magL428, magL428N)),
  (429, (magL429, magL429N)),
  (430, (magL430, magL430N)),
  (431, (magL431, magL431N)),
  (432, (magL432, magL432N)),
  (441, (magL441, magL441N)),
  (442, (magL442, magL442N)),
  (443, (magL443, magL443N)),
  (444, (magL444, magL444N)),
  (445, (magL445, magL445N)),
  (446, (magL446, magL446N)),
  (447, (magL447, magL447N)),
  (456, (magL456, magL456N)),
  (457, (magL457, magL457N)),
  (458, (magL458, magL458N)),
  (459, (magL459, magL459N)),
  (460, (magL460, magL460N)),
  (461, (magL461, magL461N)),
  (462, (magL462, magL462N)),
  (471, (magL471, magL471N)),
  (472, (magL472, magL472N)),
  (474, (magL474, magL474N)),
  (476, (magL476, magL476N)),
  (478, (magL478, magL478N)),
  (480, (magL480, magL480N)),
  (482, (magL482, magL482N)),
  (484, (magL484, magL484N)),
  (501, (magL501, magL501N)),
  (503, (magL503, magL503N)),
  (505, (magL505, magL505N)),
  (507, (magL507, magL507N)),
  (509, (magL509, magL509N)),
  (511, (magL511, magL511N)),
  (513, (magL513, magL513N)),
  (530, (magL530, magL530N)),
  (531, (magL531, magL531N)),
  (532, (magL532, magL532N)),
  (533, (magL533, magL533N)),
  (534, (magL534, magL534N)),
  (535, (magL535, magL535N)),
  (536, (magL536, magL536N)),
  (537, (magL537, magL537N)),
  (546, (magL546, magL546N)),
  (547, (magL547, magL547N)),
  (548, (magL548, magL548N)),
  (549, (magL549, magL549N)),
  (550, (magL550, magL550N)),
  (551, (magL551, magL551N)),
  (552, (magL552, magL552N)),
  (553, (magL553, magL553N)),
  (562, (magL562, magL562N)),
  (563, (magL563, magL563N)),
  (564, (magL564, magL564N)),
  (565, (magL565, magL565N)),
  (566, (magL566, magL566N)),
  (567, (magL567, magL567N)),
  (568, (magL568, magL568N)),
  (577, (magL577, magL577N)),
  (578, (magL578, magL578N)),
  (579, (magL579, magL579N)),
  (580, (magL580, magL580N)),
  (581, (magL581, magL581N)),
  (582, (magL582, magL582N)),
  (583, (magL583, magL583N)),
  (592, (magL592, magL592N)),
  (593, (magL593, magL593N)),
  (594, (magL594, magL594N)),
  (595, (magL595, magL595N)),
  (596, (magL596, magL596N)),
  (597, (magL597, magL597N)),
  (598, (magL598, magL598N)),
  (607, (magL607, magL607N)),
  (608, (magL608, magL608N)),
  (609, (magL609, magL609N)),
  (610, (magL610, magL610N)),
  (611, (magL611, magL611N)),
  (612, (magL612, magL612N)),
  (613, (magL613, magL613N)),
  (614, (magL614, magL614N)),
  (624, (magL624, magL624N)),
  (625, (magL625, magL625N)),
  (626, (magL626, magL626N)),
  (627, (magL627, magL627N)),
  (628, (magL628, magL628N)),
  (629, (magL629, magL629N)),
  (630, (magL630, magL630N)),
  (631, (magL631, magL631N)),
  (632, (magL632, magL632N)),
  (633, (magL633, magL633N)),
  (634, (magL634, magL634N)),
  (636, (magL636, magL636N)),
  (637, (magL637, magL637N)),
  (638, (magL638, magL638N)),
  (639, (magL639, magL639N)),
  (640, (magL640, magL640N)),
  (641, (magL641, magL641N)),
  (643, (magL643, magL643N)),
  (644, (magL644, magL644N)),
  (645, (magL645, magL645N)),
  (646, (magL646, magL646N)),
  (647, (magL647, magL647N)),
  (648, (magL648, magL648N)),
  (650, (magL650, magL650N)),
  (651, (magL651, magL651N)),
  (652, (magL652, magL652N)),
  (653, (magL653, magL653N)),
  (654, (magL654, magL654N)),
  (655, (magL655, magL655N)),
  (657, (magL657, magL657N)),
  (779, (magL779, magL779N)),
  (780, (magL780, magL780N)),
  (781, (magL781, magL781N)),
  (782, (magL782, magL782N)),
  (794, (magL794, magL794N)),
  (795, (magL795, magL795N)),
  (796, (magL796, magL796N)),
  (797, (magL797, magL797N)),
  (798, (magL798, magL798N)),
  (799, (magL799, magL799N))]

/-- The checkpointed cfgLow composition. -/
def magLowCkpt : ComposeCkpt MagBackend := ⟨magLowCkptSegs, magLowCkptMetas, magLowCkptLedger⟩

end KAM.Magnetic.Data.Mag
