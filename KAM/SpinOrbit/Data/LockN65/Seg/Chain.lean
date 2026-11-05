/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Jet
public import KAM.SpinOrbit.Data.LockN65.JetEq
public import KAM.SpinOrbit.Data.LockN65.Seg.CharE
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S0
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S1
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S10
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S100
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S101
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S102
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S103
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S104
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S105
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S106
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S107
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S108
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S109
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S11
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S110
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S111
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S112
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S113
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S114
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S115
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S116
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S117
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S118
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S119
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S12
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S120
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S121
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S122
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S123
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S124
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S125
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S126
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S127
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S128
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S129
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S13
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S130
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S131
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S132
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S133
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S134
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S135
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S136
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S137
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S138
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S139
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S14
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S140
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S141
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S142
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S143
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S144
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S145
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S146
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S147
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S148
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S149
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S15
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S150
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S151
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S152
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S153
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S154
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S155
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S156
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S157
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S158
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S159
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S16
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S160
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S161
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S162
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S163
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S164
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S165
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S166
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S167
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S168
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S169
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S17
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S170
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S171
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S172
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S173
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S174
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S175
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S176
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S177
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S178
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S179
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S18
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S180
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S181
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S182
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S183
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S184
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S185
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S186
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S19
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S2
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S20
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S21
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S22
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S23
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S24
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S25
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S26
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S27
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S28
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S29
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S3
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S30
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S31
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S32
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S33
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S34
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S35
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S36
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S37
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S38
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S39
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S4
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S40
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S41
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S42
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S43
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S44
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S45
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S46
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S47
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S48
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S49
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S5
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S50
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S51
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S52
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S53
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S54
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S55
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S56
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S57
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S58
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S59
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S6
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S60
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S61
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S62
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S63
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S64
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S65
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S66
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S67
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S68
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S69
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S7
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S70
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S71
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S72
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S73
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S74
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S75
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S76
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S77
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S78
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S79
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S8
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S80
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S81
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S82
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S83
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S84
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S85
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S86
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S87
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S88
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S89
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S9
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S90
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S91
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S92
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S93
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S94
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S95
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S96
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S97
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S98
public import KAM.SpinOrbit.Data.LockN65.Seg.Full.S99
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S0
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S1
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S10
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S100
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S101
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S102
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S103
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S104
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S105
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S106
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S107
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S108
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S109
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S11
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S110
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S111
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S112
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S113
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S114
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S115
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S116
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S117
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S118
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S119
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S12
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S120
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S121
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S122
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S123
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S124
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S125
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S126
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S127
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S128
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S129
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S13
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S130
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S131
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S132
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S133
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S134
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S135
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S136
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S137
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S138
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S139
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S14
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S140
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S141
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S142
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S143
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S144
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S145
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S146
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S147
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S148
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S149
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S15
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S150
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S151
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S152
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S153
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S154
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S155
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S156
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S157
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S158
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S159
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S16
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S160
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S161
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S162
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S163
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S164
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S165
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S166
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S167
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S168
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S169
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S17
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S170
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S171
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S172
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S173
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S174
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S175
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S176
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S177
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S178
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S179
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S18
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S180
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S181
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S182
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S183
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S184
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S185
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S186
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S187
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S188
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S189
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S19
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S190
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S191
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S192
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S193
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S194
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S195
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S196
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S197
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S198
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S199
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S2
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S20
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S200
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S201
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S202
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S203
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S204
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S205
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S206
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S207
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S208
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S209
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S21
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S210
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S211
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S212
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S213
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S214
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S215
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S216
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S217
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S218
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S219
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S22
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S220
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S221
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S222
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S223
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S224
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S225
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S226
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S227
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S228
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S229
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S23
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S230
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S231
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S232
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S233
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S234
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S235
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S236
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S237
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S238
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S239
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S24
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S240
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S241
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S242
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S243
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S244
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S245
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S246
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S247
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S248
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S249
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S25
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S250
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S251
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S252
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S253
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S254
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S255
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S256
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S257
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S258
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S259
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S26
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S260
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S261
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S262
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S263
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S264
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S265
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S266
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S267
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S268
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S269
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S27
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S270
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S271
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S272
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S273
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S274
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S275
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S276
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S277
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S278
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S279
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S28
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S280
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S281
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S282
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S283
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S284
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S285
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S286
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S287
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S288
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S289
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S29
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S290
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S291
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S292
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S293
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S294
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S295
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S296
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S297
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S298
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S299
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S3
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S30
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S300
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S301
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S302
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S303
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S304
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S305
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S306
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S307
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S308
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S309
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S31
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S310
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S311
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S312
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S313
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S314
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S315
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S316
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S317
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S318
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S319
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S32
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S320
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S321
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S322
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S323
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S324
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S325
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S326
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S327
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S328
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S329
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S33
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S330
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S331
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S332
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S333
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S334
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S335
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S336
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S337
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S338
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S339
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S34
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S340
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S341
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S342
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S343
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S344
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S345
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S346
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S347
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S348
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S349
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S35
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S350
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S351
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S352
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S353
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S354
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S355
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S356
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S357
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S358
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S359
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S36
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S360
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S361
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S362
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S363
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S364
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S365
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S366
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S367
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S368
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S369
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S37
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S370
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S371
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S372
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S373
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S374
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S375
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S376
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S377
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S378
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S379
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S38
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S380
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S381
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S382
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S383
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S384
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S385
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S39
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S4
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S40
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S41
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S42
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S43
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S44
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S45
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S46
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S47
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S48
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S49
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S5
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S50
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S51
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S52
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S53
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S54
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S55
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S56
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S57
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S58
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S59
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S6
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S60
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S61
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S62
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S63
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S64
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S65
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S66
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S67
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S68
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S69
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S7
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S70
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S71
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S72
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S73
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S74
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S75
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S76
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S77
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S78
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S79
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S8
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S80
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S81
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S82
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S83
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S84
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S85
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S86
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S87
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S88
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S89
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S9
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S90
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S91
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S92
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S93
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S94
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S95
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S96
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S97
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S98
public import KAM.SpinOrbit.Data.LockN65.Seg.Low.S99
public import KAM.SpinOrbit.Data.LockN65.Seg.PlanFull
public import KAM.SpinOrbit.Data.LockN65.Seg.PlanLow
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# The two composition chains (generated)

`planOk`, every `segOk`, `wantedOk`, and the cfgLow `compose_eq` instance.
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

theorem lock_jetB : base.ham.jet = lockJetLit := lock_jet

theorem lockFullCkpt_segs_length : lockFullCkpt.segs.length = 187 := by decide +kernel

theorem lock_fullPlan : lockFullCkpt.planOk lockJetLit.prog.ops.length = true := by decide +kernel

theorem lock_fullSegs :
    ∀ j < lockFullCkpt.segs.length,
      lockFullCkpt.segOk 2 lockJetLit.prog.ops base.emb base.wit base.weight base.cfgFull base.piEnc
          j = true :=
  fun j hj => match j, hj with
    | 0, _ => lockFull_seg0
    | 1, _ => lockFull_seg1
    | 2, _ => lockFull_seg2
    | 3, _ => lockFull_seg3
    | 4, _ => lockFull_seg4
    | 5, _ => lockFull_seg5
    | 6, _ => lockFull_seg6
    | 7, _ => lockFull_seg7
    | 8, _ => lockFull_seg8
    | 9, _ => lockFull_seg9
    | 10, _ => lockFull_seg10
    | 11, _ => lockFull_seg11
    | 12, _ => lockFull_seg12
    | 13, _ => lockFull_seg13
    | 14, _ => lockFull_seg14
    | 15, _ => lockFull_seg15
    | 16, _ => lockFull_seg16
    | 17, _ => lockFull_seg17
    | 18, _ => lockFull_seg18
    | 19, _ => lockFull_seg19
    | 20, _ => lockFull_seg20
    | 21, _ => lockFull_seg21
    | 22, _ => lockFull_seg22
    | 23, _ => lockFull_seg23
    | 24, _ => lockFull_seg24
    | 25, _ => lockFull_seg25
    | 26, _ => lockFull_seg26
    | 27, _ => lockFull_seg27
    | 28, _ => lockFull_seg28
    | 29, _ => lockFull_seg29
    | 30, _ => lockFull_seg30
    | 31, _ => lockFull_seg31
    | 32, _ => lockFull_seg32
    | 33, _ => lockFull_seg33
    | 34, _ => lockFull_seg34
    | 35, _ => lockFull_seg35
    | 36, _ => lockFull_seg36
    | 37, _ => lockFull_seg37
    | 38, _ => lockFull_seg38
    | 39, _ => lockFull_seg39
    | 40, _ => lockFull_seg40
    | 41, _ => lockFull_seg41
    | 42, _ => lockFull_seg42
    | 43, _ => lockFull_seg43
    | 44, _ => lockFull_seg44
    | 45, _ => lockFull_seg45
    | 46, _ => lockFull_seg46
    | 47, _ => lockFull_seg47
    | 48, _ => lockFull_seg48
    | 49, _ => lockFull_seg49
    | 50, _ => lockFull_seg50
    | 51, _ => lockFull_seg51
    | 52, _ => lockFull_seg52
    | 53, _ => lockFull_seg53
    | 54, _ => lockFull_seg54
    | 55, _ => lockFull_seg55
    | 56, _ => lockFull_seg56
    | 57, _ => lockFull_seg57
    | 58, _ => lockFull_seg58
    | 59, _ => lockFull_seg59
    | 60, _ => lockFull_seg60
    | 61, _ => lockFull_seg61
    | 62, _ => lockFull_seg62
    | 63, _ => lockFull_seg63
    | 64, _ => lockFull_seg64
    | 65, _ => lockFull_seg65
    | 66, _ => lockFull_seg66
    | 67, _ => lockFull_seg67
    | 68, _ => lockFull_seg68
    | 69, _ => lockFull_seg69
    | 70, _ => lockFull_seg70
    | 71, _ => lockFull_seg71
    | 72, _ => lockFull_seg72
    | 73, _ => lockFull_seg73
    | 74, _ => lockFull_seg74
    | 75, _ => lockFull_seg75
    | 76, _ => lockFull_seg76
    | 77, _ => lockFull_seg77
    | 78, _ => lockFull_seg78
    | 79, _ => lockFull_seg79
    | 80, _ => lockFull_seg80
    | 81, _ => lockFull_seg81
    | 82, _ => lockFull_seg82
    | 83, _ => lockFull_seg83
    | 84, _ => lockFull_seg84
    | 85, _ => lockFull_seg85
    | 86, _ => lockFull_seg86
    | 87, _ => lockFull_seg87
    | 88, _ => lockFull_seg88
    | 89, _ => lockFull_seg89
    | 90, _ => lockFull_seg90
    | 91, _ => lockFull_seg91
    | 92, _ => lockFull_seg92
    | 93, _ => lockFull_seg93
    | 94, _ => lockFull_seg94
    | 95, _ => lockFull_seg95
    | 96, _ => lockFull_seg96
    | 97, _ => lockFull_seg97
    | 98, _ => lockFull_seg98
    | 99, _ => lockFull_seg99
    | 100, _ => lockFull_seg100
    | 101, _ => lockFull_seg101
    | 102, _ => lockFull_seg102
    | 103, _ => lockFull_seg103
    | 104, _ => lockFull_seg104
    | 105, _ => lockFull_seg105
    | 106, _ => lockFull_seg106
    | 107, _ => lockFull_seg107
    | 108, _ => lockFull_seg108
    | 109, _ => lockFull_seg109
    | 110, _ => lockFull_seg110
    | 111, _ => lockFull_seg111
    | 112, _ => lockFull_seg112
    | 113, _ => lockFull_seg113
    | 114, _ => lockFull_seg114
    | 115, _ => lockFull_seg115
    | 116, _ => lockFull_seg116
    | 117, _ => lockFull_seg117
    | 118, _ => lockFull_seg118
    | 119, _ => lockFull_seg119
    | 120, _ => lockFull_seg120
    | 121, _ => lockFull_seg121
    | 122, _ => lockFull_seg122
    | 123, _ => lockFull_seg123
    | 124, _ => lockFull_seg124
    | 125, _ => lockFull_seg125
    | 126, _ => lockFull_seg126
    | 127, _ => lockFull_seg127
    | 128, _ => lockFull_seg128
    | 129, _ => lockFull_seg129
    | 130, _ => lockFull_seg130
    | 131, _ => lockFull_seg131
    | 132, _ => lockFull_seg132
    | 133, _ => lockFull_seg133
    | 134, _ => lockFull_seg134
    | 135, _ => lockFull_seg135
    | 136, _ => lockFull_seg136
    | 137, _ => lockFull_seg137
    | 138, _ => lockFull_seg138
    | 139, _ => lockFull_seg139
    | 140, _ => lockFull_seg140
    | 141, _ => lockFull_seg141
    | 142, _ => lockFull_seg142
    | 143, _ => lockFull_seg143
    | 144, _ => lockFull_seg144
    | 145, _ => lockFull_seg145
    | 146, _ => lockFull_seg146
    | 147, _ => lockFull_seg147
    | 148, _ => lockFull_seg148
    | 149, _ => lockFull_seg149
    | 150, _ => lockFull_seg150
    | 151, _ => lockFull_seg151
    | 152, _ => lockFull_seg152
    | 153, _ => lockFull_seg153
    | 154, _ => lockFull_seg154
    | 155, _ => lockFull_seg155
    | 156, _ => lockFull_seg156
    | 157, _ => lockFull_seg157
    | 158, _ => lockFull_seg158
    | 159, _ => lockFull_seg159
    | 160, _ => lockFull_seg160
    | 161, _ => lockFull_seg161
    | 162, _ => lockFull_seg162
    | 163, _ => lockFull_seg163
    | 164, _ => lockFull_seg164
    | 165, _ => lockFull_seg165
    | 166, _ => lockFull_seg166
    | 167, _ => lockFull_seg167
    | 168, _ => lockFull_seg168
    | 169, _ => lockFull_seg169
    | 170, _ => lockFull_seg170
    | 171, _ => lockFull_seg171
    | 172, _ => lockFull_seg172
    | 173, _ => lockFull_seg173
    | 174, _ => lockFull_seg174
    | 175, _ => lockFull_seg175
    | 176, _ => lockFull_seg176
    | 177, _ => lockFull_seg177
    | 178, _ => lockFull_seg178
    | 179, _ => lockFull_seg179
    | 180, _ => lockFull_seg180
    | 181, _ => lockFull_seg181
    | 182, _ => lockFull_seg182
    | 183, _ => lockFull_seg183
    | 184, _ => lockFull_seg184
    | 185, _ => lockFull_seg185
    | 186, _ => lockFull_seg186
    | j + 187, h => absurd h (by rw [lockFullCkpt_segs_length]; omega)

theorem lockLowCkpt_segs_length : lockLowCkpt.segs.length = 386 := by decide +kernel

theorem lock_lowPlan : lockLowCkpt.planOk lockJetLit.prog.ops.length = true := by decide +kernel

theorem lock_lowSegs :
    ∀ j < lockLowCkpt.segs.length,
      lockLowCkpt.segOk 2 lockJetLit.prog.ops base.emb base.wit base.weight base.cfgLow base.piEnc j
          = true :=
  fun j hj => match j, hj with
    | 0, _ => lockLow_seg0
    | 1, _ => lockLow_seg1
    | 2, _ => lockLow_seg2
    | 3, _ => lockLow_seg3
    | 4, _ => lockLow_seg4
    | 5, _ => lockLow_seg5
    | 6, _ => lockLow_seg6
    | 7, _ => lockLow_seg7
    | 8, _ => lockLow_seg8
    | 9, _ => lockLow_seg9
    | 10, _ => lockLow_seg10
    | 11, _ => lockLow_seg11
    | 12, _ => lockLow_seg12
    | 13, _ => lockLow_seg13
    | 14, _ => lockLow_seg14
    | 15, _ => lockLow_seg15
    | 16, _ => lockLow_seg16
    | 17, _ => lockLow_seg17
    | 18, _ => lockLow_seg18
    | 19, _ => lockLow_seg19
    | 20, _ => lockLow_seg20
    | 21, _ => lockLow_seg21
    | 22, _ => lockLow_seg22
    | 23, _ => lockLow_seg23
    | 24, _ => lockLow_seg24
    | 25, _ => lockLow_seg25
    | 26, _ => lockLow_seg26
    | 27, _ => lockLow_seg27
    | 28, _ => lockLow_seg28
    | 29, _ => lockLow_seg29
    | 30, _ => lockLow_seg30
    | 31, _ => lockLow_seg31
    | 32, _ => lockLow_seg32
    | 33, _ => lockLow_seg33
    | 34, _ => lockLow_seg34
    | 35, _ => lockLow_seg35
    | 36, _ => lockLow_seg36
    | 37, _ => lockLow_seg37
    | 38, _ => lockLow_seg38
    | 39, _ => lockLow_seg39
    | 40, _ => lockLow_seg40
    | 41, _ => lockLow_seg41
    | 42, _ => lockLow_seg42
    | 43, _ => lockLow_seg43
    | 44, _ => lockLow_seg44
    | 45, _ => lockLow_seg45
    | 46, _ => lockLow_seg46
    | 47, _ => lockLow_seg47
    | 48, _ => lockLow_seg48
    | 49, _ => lockLow_seg49
    | 50, _ => lockLow_seg50
    | 51, _ => lockLow_seg51
    | 52, _ => lockLow_seg52
    | 53, _ => lockLow_seg53
    | 54, _ => lockLow_seg54
    | 55, _ => lockLow_seg55
    | 56, _ => lockLow_seg56
    | 57, _ => lockLow_seg57
    | 58, _ => lockLow_seg58
    | 59, _ => lockLow_seg59
    | 60, _ => lockLow_seg60
    | 61, _ => lockLow_seg61
    | 62, _ => lockLow_seg62
    | 63, _ => lockLow_seg63
    | 64, _ => lockLow_seg64
    | 65, _ => lockLow_seg65
    | 66, _ => lockLow_seg66
    | 67, _ => lockLow_seg67
    | 68, _ => lockLow_seg68
    | 69, _ => lockLow_seg69
    | 70, _ => lockLow_seg70
    | 71, _ => lockLow_seg71
    | 72, _ => lockLow_seg72
    | 73, _ => lockLow_seg73
    | 74, _ => lockLow_seg74
    | 75, _ => lockLow_seg75
    | 76, _ => lockLow_seg76
    | 77, _ => lockLow_seg77
    | 78, _ => lockLow_seg78
    | 79, _ => lockLow_seg79
    | 80, _ => lockLow_seg80
    | 81, _ => lockLow_seg81
    | 82, _ => lockLow_seg82
    | 83, _ => lockLow_seg83
    | 84, _ => lockLow_seg84
    | 85, _ => lockLow_seg85
    | 86, _ => lockLow_seg86
    | 87, _ => lockLow_seg87
    | 88, _ => lockLow_seg88
    | 89, _ => lockLow_seg89
    | 90, _ => lockLow_seg90
    | 91, _ => lockLow_seg91
    | 92, _ => lockLow_seg92
    | 93, _ => lockLow_seg93
    | 94, _ => lockLow_seg94
    | 95, _ => lockLow_seg95
    | 96, _ => lockLow_seg96
    | 97, _ => lockLow_seg97
    | 98, _ => lockLow_seg98
    | 99, _ => lockLow_seg99
    | 100, _ => lockLow_seg100
    | 101, _ => lockLow_seg101
    | 102, _ => lockLow_seg102
    | 103, _ => lockLow_seg103
    | 104, _ => lockLow_seg104
    | 105, _ => lockLow_seg105
    | 106, _ => lockLow_seg106
    | 107, _ => lockLow_seg107
    | 108, _ => lockLow_seg108
    | 109, _ => lockLow_seg109
    | 110, _ => lockLow_seg110
    | 111, _ => lockLow_seg111
    | 112, _ => lockLow_seg112
    | 113, _ => lockLow_seg113
    | 114, _ => lockLow_seg114
    | 115, _ => lockLow_seg115
    | 116, _ => lockLow_seg116
    | 117, _ => lockLow_seg117
    | 118, _ => lockLow_seg118
    | 119, _ => lockLow_seg119
    | 120, _ => lockLow_seg120
    | 121, _ => lockLow_seg121
    | 122, _ => lockLow_seg122
    | 123, _ => lockLow_seg123
    | 124, _ => lockLow_seg124
    | 125, _ => lockLow_seg125
    | 126, _ => lockLow_seg126
    | 127, _ => lockLow_seg127
    | 128, _ => lockLow_seg128
    | 129, _ => lockLow_seg129
    | 130, _ => lockLow_seg130
    | 131, _ => lockLow_seg131
    | 132, _ => lockLow_seg132
    | 133, _ => lockLow_seg133
    | 134, _ => lockLow_seg134
    | 135, _ => lockLow_seg135
    | 136, _ => lockLow_seg136
    | 137, _ => lockLow_seg137
    | 138, _ => lockLow_seg138
    | 139, _ => lockLow_seg139
    | 140, _ => lockLow_seg140
    | 141, _ => lockLow_seg141
    | 142, _ => lockLow_seg142
    | 143, _ => lockLow_seg143
    | 144, _ => lockLow_seg144
    | 145, _ => lockLow_seg145
    | 146, _ => lockLow_seg146
    | 147, _ => lockLow_seg147
    | 148, _ => lockLow_seg148
    | 149, _ => lockLow_seg149
    | 150, _ => lockLow_seg150
    | 151, _ => lockLow_seg151
    | 152, _ => lockLow_seg152
    | 153, _ => lockLow_seg153
    | 154, _ => lockLow_seg154
    | 155, _ => lockLow_seg155
    | 156, _ => lockLow_seg156
    | 157, _ => lockLow_seg157
    | 158, _ => lockLow_seg158
    | 159, _ => lockLow_seg159
    | 160, _ => lockLow_seg160
    | 161, _ => lockLow_seg161
    | 162, _ => lockLow_seg162
    | 163, _ => lockLow_seg163
    | 164, _ => lockLow_seg164
    | 165, _ => lockLow_seg165
    | 166, _ => lockLow_seg166
    | 167, _ => lockLow_seg167
    | 168, _ => lockLow_seg168
    | 169, _ => lockLow_seg169
    | 170, _ => lockLow_seg170
    | 171, _ => lockLow_seg171
    | 172, _ => lockLow_seg172
    | 173, _ => lockLow_seg173
    | 174, _ => lockLow_seg174
    | 175, _ => lockLow_seg175
    | 176, _ => lockLow_seg176
    | 177, _ => lockLow_seg177
    | 178, _ => lockLow_seg178
    | 179, _ => lockLow_seg179
    | 180, _ => lockLow_seg180
    | 181, _ => lockLow_seg181
    | 182, _ => lockLow_seg182
    | 183, _ => lockLow_seg183
    | 184, _ => lockLow_seg184
    | 185, _ => lockLow_seg185
    | 186, _ => lockLow_seg186
    | 187, _ => lockLow_seg187
    | 188, _ => lockLow_seg188
    | 189, _ => lockLow_seg189
    | 190, _ => lockLow_seg190
    | 191, _ => lockLow_seg191
    | 192, _ => lockLow_seg192
    | 193, _ => lockLow_seg193
    | 194, _ => lockLow_seg194
    | 195, _ => lockLow_seg195
    | 196, _ => lockLow_seg196
    | 197, _ => lockLow_seg197
    | 198, _ => lockLow_seg198
    | 199, _ => lockLow_seg199
    | 200, _ => lockLow_seg200
    | 201, _ => lockLow_seg201
    | 202, _ => lockLow_seg202
    | 203, _ => lockLow_seg203
    | 204, _ => lockLow_seg204
    | 205, _ => lockLow_seg205
    | 206, _ => lockLow_seg206
    | 207, _ => lockLow_seg207
    | 208, _ => lockLow_seg208
    | 209, _ => lockLow_seg209
    | 210, _ => lockLow_seg210
    | 211, _ => lockLow_seg211
    | 212, _ => lockLow_seg212
    | 213, _ => lockLow_seg213
    | 214, _ => lockLow_seg214
    | 215, _ => lockLow_seg215
    | 216, _ => lockLow_seg216
    | 217, _ => lockLow_seg217
    | 218, _ => lockLow_seg218
    | 219, _ => lockLow_seg219
    | 220, _ => lockLow_seg220
    | 221, _ => lockLow_seg221
    | 222, _ => lockLow_seg222
    | 223, _ => lockLow_seg223
    | 224, _ => lockLow_seg224
    | 225, _ => lockLow_seg225
    | 226, _ => lockLow_seg226
    | 227, _ => lockLow_seg227
    | 228, _ => lockLow_seg228
    | 229, _ => lockLow_seg229
    | 230, _ => lockLow_seg230
    | 231, _ => lockLow_seg231
    | 232, _ => lockLow_seg232
    | 233, _ => lockLow_seg233
    | 234, _ => lockLow_seg234
    | 235, _ => lockLow_seg235
    | 236, _ => lockLow_seg236
    | 237, _ => lockLow_seg237
    | 238, _ => lockLow_seg238
    | 239, _ => lockLow_seg239
    | 240, _ => lockLow_seg240
    | 241, _ => lockLow_seg241
    | 242, _ => lockLow_seg242
    | 243, _ => lockLow_seg243
    | 244, _ => lockLow_seg244
    | 245, _ => lockLow_seg245
    | 246, _ => lockLow_seg246
    | 247, _ => lockLow_seg247
    | 248, _ => lockLow_seg248
    | 249, _ => lockLow_seg249
    | 250, _ => lockLow_seg250
    | 251, _ => lockLow_seg251
    | 252, _ => lockLow_seg252
    | 253, _ => lockLow_seg253
    | 254, _ => lockLow_seg254
    | 255, _ => lockLow_seg255
    | 256, _ => lockLow_seg256
    | 257, _ => lockLow_seg257
    | 258, _ => lockLow_seg258
    | 259, _ => lockLow_seg259
    | 260, _ => lockLow_seg260
    | 261, _ => lockLow_seg261
    | 262, _ => lockLow_seg262
    | 263, _ => lockLow_seg263
    | 264, _ => lockLow_seg264
    | 265, _ => lockLow_seg265
    | 266, _ => lockLow_seg266
    | 267, _ => lockLow_seg267
    | 268, _ => lockLow_seg268
    | 269, _ => lockLow_seg269
    | 270, _ => lockLow_seg270
    | 271, _ => lockLow_seg271
    | 272, _ => lockLow_seg272
    | 273, _ => lockLow_seg273
    | 274, _ => lockLow_seg274
    | 275, _ => lockLow_seg275
    | 276, _ => lockLow_seg276
    | 277, _ => lockLow_seg277
    | 278, _ => lockLow_seg278
    | 279, _ => lockLow_seg279
    | 280, _ => lockLow_seg280
    | 281, _ => lockLow_seg281
    | 282, _ => lockLow_seg282
    | 283, _ => lockLow_seg283
    | 284, _ => lockLow_seg284
    | 285, _ => lockLow_seg285
    | 286, _ => lockLow_seg286
    | 287, _ => lockLow_seg287
    | 288, _ => lockLow_seg288
    | 289, _ => lockLow_seg289
    | 290, _ => lockLow_seg290
    | 291, _ => lockLow_seg291
    | 292, _ => lockLow_seg292
    | 293, _ => lockLow_seg293
    | 294, _ => lockLow_seg294
    | 295, _ => lockLow_seg295
    | 296, _ => lockLow_seg296
    | 297, _ => lockLow_seg297
    | 298, _ => lockLow_seg298
    | 299, _ => lockLow_seg299
    | 300, _ => lockLow_seg300
    | 301, _ => lockLow_seg301
    | 302, _ => lockLow_seg302
    | 303, _ => lockLow_seg303
    | 304, _ => lockLow_seg304
    | 305, _ => lockLow_seg305
    | 306, _ => lockLow_seg306
    | 307, _ => lockLow_seg307
    | 308, _ => lockLow_seg308
    | 309, _ => lockLow_seg309
    | 310, _ => lockLow_seg310
    | 311, _ => lockLow_seg311
    | 312, _ => lockLow_seg312
    | 313, _ => lockLow_seg313
    | 314, _ => lockLow_seg314
    | 315, _ => lockLow_seg315
    | 316, _ => lockLow_seg316
    | 317, _ => lockLow_seg317
    | 318, _ => lockLow_seg318
    | 319, _ => lockLow_seg319
    | 320, _ => lockLow_seg320
    | 321, _ => lockLow_seg321
    | 322, _ => lockLow_seg322
    | 323, _ => lockLow_seg323
    | 324, _ => lockLow_seg324
    | 325, _ => lockLow_seg325
    | 326, _ => lockLow_seg326
    | 327, _ => lockLow_seg327
    | 328, _ => lockLow_seg328
    | 329, _ => lockLow_seg329
    | 330, _ => lockLow_seg330
    | 331, _ => lockLow_seg331
    | 332, _ => lockLow_seg332
    | 333, _ => lockLow_seg333
    | 334, _ => lockLow_seg334
    | 335, _ => lockLow_seg335
    | 336, _ => lockLow_seg336
    | 337, _ => lockLow_seg337
    | 338, _ => lockLow_seg338
    | 339, _ => lockLow_seg339
    | 340, _ => lockLow_seg340
    | 341, _ => lockLow_seg341
    | 342, _ => lockLow_seg342
    | 343, _ => lockLow_seg343
    | 344, _ => lockLow_seg344
    | 345, _ => lockLow_seg345
    | 346, _ => lockLow_seg346
    | 347, _ => lockLow_seg347
    | 348, _ => lockLow_seg348
    | 349, _ => lockLow_seg349
    | 350, _ => lockLow_seg350
    | 351, _ => lockLow_seg351
    | 352, _ => lockLow_seg352
    | 353, _ => lockLow_seg353
    | 354, _ => lockLow_seg354
    | 355, _ => lockLow_seg355
    | 356, _ => lockLow_seg356
    | 357, _ => lockLow_seg357
    | 358, _ => lockLow_seg358
    | 359, _ => lockLow_seg359
    | 360, _ => lockLow_seg360
    | 361, _ => lockLow_seg361
    | 362, _ => lockLow_seg362
    | 363, _ => lockLow_seg363
    | 364, _ => lockLow_seg364
    | 365, _ => lockLow_seg365
    | 366, _ => lockLow_seg366
    | 367, _ => lockLow_seg367
    | 368, _ => lockLow_seg368
    | 369, _ => lockLow_seg369
    | 370, _ => lockLow_seg370
    | 371, _ => lockLow_seg371
    | 372, _ => lockLow_seg372
    | 373, _ => lockLow_seg373
    | 374, _ => lockLow_seg374
    | 375, _ => lockLow_seg375
    | 376, _ => lockLow_seg376
    | 377, _ => lockLow_seg377
    | 378, _ => lockLow_seg378
    | 379, _ => lockLow_seg379
    | 380, _ => lockLow_seg380
    | 381, _ => lockLow_seg381
    | 382, _ => lockLow_seg382
    | 383, _ => lockLow_seg383
    | 384, _ => lockLow_seg384
    | 385, _ => lockLow_seg385
    | j + 386, h => absurd h (by rw [lockLowCkpt_segs_length]; omega)

theorem lock_fullWantedE : lockFullCkpt.wantedOk [lockJetLit.v0] = true := by decide +kernel
theorem lock_fullWantedI : lockFullCkpt.wantedOk (d1Slots 2 lockJetLit) = true := by decide +kernel
theorem lock_lowWanted : lockLowCkpt.wantedOk (torsionSlots 2 lockJetLit) = true := by
    decide +kernel

theorem lock_lowCompose :
    Slp.compose 2 base.ham.jet.prog base.emb base.wit base.weight base.cfgLow base.piEnc
      (torsionSlots 2 base.ham.jet) = some lockMS := by
  rw [lock_jetB]
  exact ComposeCkpt.compose_eq 2 base.emb base.wit base.weight base.cfgLow base.piEnc lockLowCkpt
      lock_lowPlan
    lock_lowSegs lock_lowWanted

end KAM.SpinOrbit.Data.LockN65
