/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs2

/-!
# Ledger inputs (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

def sjsuTsp_34 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 10, 0), [(180, (mkQ true (
  Nat.add (Nat.add 0x775c2e3c4e10213122df3321be6536b1276251abc0b9c2d07dd572e0f17659b2340d2f35 (
  Nat.shiftLeft 0xb347220d897dce7b38f47da8c3a22d9cd9c5140d56ea09c562ef10a30d0886ec8e321bc2 288)) (
  Nat.shiftLeft (Nat.add 0xa7dafcdb5b103f5ee06df9433949c77049ba413eac937d500f3ae02c5eebddeb756038c6
  (Nat.shiftLeft 0x358d50a3950232c3a8fac7ca 288)) 576)) (Nat.add (Nat.add
  0x343359c7f893910db5ee567fcf4f3f74768b668ce86ca1643499ea92756e607d48400000 (Nat.shiftLeft
  0xbc68a702fe84112cd7ef6b425277c766b36f02ef4aba4c5885b306f66bc760de434c8075 288)) (Nat.shiftLeft (
  Nat.add 0x5e033901ecefeb76d872cff619ad549f20c407c1d33344a681240d7394df744d1a69e0b (Nat.shiftLeft
  0x1008896bcf57ac08839547edd 288)) 576))))]), ((0, 10, 2), [(142, (mkQ true (Nat.add (Nat.add
  0xf55036053020eeb3c3420233a2a1cddd6cf7b114ddb55efdecc99020f7df0180f3731a5d (Nat.shiftLeft
  0xa89fa27ff5b6acabf22fa9f38c6a3e2f347a80248dd1c9d32fb867dd39bc77316fe27571 288)) (Nat.shiftLeft (
  Nat.add 0xee07c33e3d7d1fcc075730369392c08fce01c31be910da55692c60f615a31db75b49e78b (Nat.shiftLeft
  0x2b21e42bdbd6474edfdf8eabdf9fe4febd9ed791f1804233e804e214a096d1bbb16 288)) 576)) (Nat.add (
  Nat.add 0x2701b78a40f72680b121f72b15eeb971ae3d354687f98cd9afbec1bab38b3a9de1a40000 (Nat.shiftLeft
  0xab4e4b99e57949ad62f04402a3f17dd8a6ac28c87725c6813ddab30a2dcf655cd2db2406 288)) (Nat.shiftLeft (
  Nat.add 0xa3c2e6e5d85b7c0a2b02f603f60184340b734feca32cceaad8e0c93663bdac832d0e110e (Nat.shiftLeft
  0x11242f37d23dfc9f3fca08d7878f13abe96a590427715f649d313b8a228decd139 288)) 576)))), (180, (mkQ
  true (Nat.add (Nat.add 0x830e6d65fedb0511292d754740cc95436e3b5935127d45798eebf0cf690001eff032ce6b
  (Nat.shiftLeft 0xb41b31049b6ac77543df106064b7c791346d048b2549bc78cc5cf942c9a83b99e082417d 288)) (
  Nat.shiftLeft (Nat.add 0xe10ccb8a3fe6a137910e1b1a89e0e55bc40ab23b6a8b4a4a348c88d274ca53d7a046c93c
  (Nat.shiftLeft 0x34f996c5e413eef2d8c66947a5bdff838d2526a5b2e0699b1dcf35a1ad92e54a06a6 288)) 576))
  (Nat.add (Nat.add 0x380dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d200000 (
  Nat.shiftLeft 0x5a725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d92031 288)) (
  Nat.shiftLeft (Nat.add 0x1e17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded641968708875
  (Nat.shiftLeft 0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd 288)) 576)))),
  (218, (mkQ true (Nat.add (Nat.add
  0xf55036053020eeb3c3420233a2a1cddd6cf7b114ddb55efdecc99020f7df0180f3731a5d (Nat.shiftLeft
  0xa89fa27ff5b6acabf22fa9f38c6a3e2f347a80248dd1c9d32fb867dd39bc77316fe27571 288)) (Nat.shiftLeft (
  Nat.add 0xee07c33e3d7d1fcc075730369392c08fce01c31be910da55692c60f615a31db75b49e78b (Nat.shiftLeft
  0x2b21e42bdbd6474edfdf8eabdf9fe4febd9ed791f1804233e804e214a096d1bbb16 288)) 576)) (Nat.add (
  Nat.add 0x2701b78a40f72680b121f72b15eeb971ae3d354687f98cd9afbec1bab38b3a9de1a40000 (Nat.shiftLeft
  0xab4e4b99e57949ad62f04402a3f17dd8a6ac28c87725c6813ddab30a2dcf655cd2db2406 288)) (Nat.shiftLeft (
  Nat.add 0xa3c2e6e5d85b7c0a2b02f603f60184340b734feca32cceaad8e0c93663bdac832d0e110e (Nat.shiftLeft
  0x11242f37d23dfc9f3fca08d7878f13abe96a590427715f649d313b8a228decd139 288)) 576))))]), ((0, 10, 4),
  [(104, (mkQ false (Nat.add (Nat.add
  0xee99d02ad5a1d2979c59064e3b22c7048466556bd08a2607cd8717bf700fdc602a0644d1 (Nat.shiftLeft
  0x26ae5937f9f13eeb2823dad6b83b1b1cd5c489c4553fa5ce8893bc1e32e1ed9d7799a892 288)) (Nat.shiftLeft (
  Nat.add 0xfec1bca96f0acf11a120b0affd9b4d4dcf637404dd846924d41fc23374cb6943e5dd24f6 (Nat.shiftLeft
  (Nat.add 0xf73edeaaa4dc0d930c427fb0a0743b45b035f5be870bf4ab2deee3d77a10ebb13117d8a1 (Nat.shiftLeft
  0x104940562305d587f0099cc0876673e989d7560 288)) 288)) 576)) (Nat.add (Nat.add
  0xe19c95f27861c30662321ab6c92127a01e9a1ac6c844de8c8bca95f5bb8d7aea33200000 (Nat.shiftLeft
  0xdc33652c7b1f1c4117e4c2029989bfffce21c7c05c9a4b54cfd50a000e9e25a8cf316b5d 288)) (Nat.shiftLeft (
  Nat.add 0x7ebef12864317e6aac54fef31c6a87fe162dda87928163db7eec7703e526edd4b4a6d075 (Nat.shiftLeft
  (Nat.add 0x75f7f6cbd64cdaeeb2f943f5e199f3e59920a796fcd7090f77e8a18744bbe4736f76cf6f (Nat.shiftLeft
  0x5dd4241feaa4e46dfae9d89b4eb2b9c861c 288)) 288)) 576)))), (142, (mkQ false (Nat.add (Nat.add
  0x5940b0750f5aebf0d7fa853eba34c6830f2e619ffbe0296426278eea9c5dd45b856d00d7 (Nat.shiftLeft
  0xcf75c906d6b9fc4e848ac31286afadcc7f3aeabcde5e55c40435267caf597033b32aa17d 288)) (Nat.shiftLeft (
  Nat.add 0xb4b32cfde35df6d6b277d034216e66be1d0a3ff577a2b445c91811f62139f49e1510686 (Nat.shiftLeft (
  Nat.add 0x4c496ccdf9bcca3754c687ccba049b06c9fbbbce1877a218bddf049f748545eb1d53531d (Nat.shiftLeft
  0xa198e8d4449ec6ef1f2ae16a3130cd33ffea796 288)) 288)) 576)) (Nat.add (Nat.add
  0x5a03bb6f167a33c7fabea1647b6971882640a1787a56162faebd3b732a70d9a4bfe80000 (Nat.shiftLeft
  0x53403e7799e6e3515dddf2833fec2fffc1aa39b073c0de2a03ca4c801245af1302fdc635 288)) (Nat.shiftLeft (
  Nat.add 0x5e6ead727d3dde05576a3eafe38529fd9bb951297721bcd25ea794c4de70a949e1d08493 (Nat.shiftLeft
  (Nat.add 0x9375f47ecbe011aa5fb794f35a0070deff68d17cbc0ccb5355e2c9e915eadd904b54834b (Nat.shiftLeft
  0x75492d27e54e1d8979a44ec2225f683a7a3 288)) 288)) 576)))), (180, (mkQ false (Nat.add (Nat.add
  0xe98e737d79a50caa84d7ce60fc7f7138f96a152040bd4383b64d76c53c988fa28170f357 (Nat.shiftLeft
  0x7c05bf7243fe2ea4c84ac58fb4f2aa42a46e76ff5d8b6fc093979230a787bc6b6da58cfb 288)) (Nat.shiftLeft (
  Nat.add 0xdf25f2dfe79a66b13518bdeb5b4ac061a3a4ab70e531abeb4c0a1d2b7e7c79ddf957ecfd (Nat.shiftLeft
  (Nat.add 0xf618a481a248c2cb8f90f19f4be83ae1fc24f23f604b89acc30ca9a9c355ed001e9c2166 (Nat.shiftLeft
  0x1d7ed9608ee130adfe673b819277c0ac42fa44373 288)) 288)) 576)) (Nat.add (Nat.add
  0xca5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda80000 (Nat.shiftLeft
  0x214619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35 288)) (Nat.shiftLeft (
  Nat.add 0x38cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf263 (Nat.shiftLeft
  (Nat.add 0x6684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef9 288)) 288)) 576)))), (218, (mkQ false (Nat.add (Nat.add
  0x5940b0750f5aebf0d7fa853eba34c6830f2e619ffbe0296426278eea9c5dd45b856d00d7 (Nat.shiftLeft
  0xcf75c906d6b9fc4e848ac31286afadcc7f3aeabcde5e55c40435267caf597033b32aa17d 288)) (Nat.shiftLeft (
  Nat.add 0xb4b32cfde35df6d6b277d034216e66be1d0a3ff577a2b445c91811f62139f49e1510686 (Nat.shiftLeft (
  Nat.add 0x4c496ccdf9bcca3754c687ccba049b06c9fbbbce1877a218bddf049f748545eb1d53531d (Nat.shiftLeft
  0xa198e8d4449ec6ef1f2ae16a3130cd33ffea796 288)) 288)) 576)) (Nat.add (Nat.add
  0x5a03bb6f167a33c7fabea1647b6971882640a1787a56162faebd3b732a70d9a4bfe80000 (Nat.shiftLeft
  0x53403e7799e6e3515dddf2833fec2fffc1aa39b073c0de2a03ca4c801245af1302fdc635 288)) (Nat.shiftLeft (
  Nat.add 0x5e6ead727d3dde05576a3eafe38529fd9bb951297721bcd25ea794c4de70a949e1d08493 (Nat.shiftLeft
  (Nat.add 0x9375f47ecbe011aa5fb794f35a0070deff68d17cbc0ccb5355e2c9e915eadd904b54834b (Nat.shiftLeft
  0x75492d27e54e1d8979a44ec2225f683a7a3 288)) 288)) 576)))), (256, (mkQ false (Nat.add (Nat.add
  0xee99d02ad5a1d2979c59064e3b22c7048466556bd08a2607cd8717bf700fdc602a0644d1 (Nat.shiftLeft
  0x26ae5937f9f13eeb2823dad6b83b1b1cd5c489c4553fa5ce8893bc1e32e1ed9d7799a892 288)) (Nat.shiftLeft (
  Nat.add 0xfec1bca96f0acf11a120b0affd9b4d4dcf637404dd846924d41fc23374cb6943e5dd24f6 (Nat.shiftLeft
  (Nat.add 0xf73edeaaa4dc0d930c427fb0a0743b45b035f5be870bf4ab2deee3d77a10ebb13117d8a1 (Nat.shiftLeft
  0x104940562305d587f0099cc0876673e989d7560 288)) 288)) 576)) (Nat.add (Nat.add
  0xe19c95f27861c30662321ab6c92127a01e9a1ac6c844de8c8bca95f5bb8d7aea33200000 (Nat.shiftLeft
  0xdc33652c7b1f1c4117e4c2029989bfffce21c7c05c9a4b54cfd50a000e9e25a8cf316b5d 288)) (Nat.shiftLeft (
  Nat.add 0x7ebef12864317e6aac54fef31c6a87fe162dda87928163db7eec7703e526edd4b4a6d075 (Nat.shiftLeft
  (Nat.add 0x75f7f6cbd64cdaeeb2f943f5e199f3e59920a796fcd7090f77e8a18744bbe4736f76cf6f (Nat.shiftLeft
  0x5dd4241feaa4e46dfae9d89b4eb2b9c861c 288)) 288)) 576))))])]

def sjsuTsp_35 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 10, 6), [(66, (mkQ true (
  Nat.add (Nat.add 0xea32cecb0d7bee8504dc35fa5d1fd58b4ed2e4687d455b1861da261797925f3dcd8b0ba1 (
  Nat.shiftLeft (Nat.add 0x84c1112e2bdcb569245366a16a0b39b7f7a32209545d29bce0f0146a18e03933d5600abc
  (Nat.shiftLeft 0x580b8bb554c928a09a23e85cf3bd82710022573a5f346a0c7158aeb6e15edf166419cd01 288))
  288)) (Nat.shiftLeft (Nat.add
  0x2bb638425d60fe367278e0cfbddc5ad9cbbc70d87061c8f9d94896916c4006b137b4e7b0 (Nat.shiftLeft (Nat.add
  0x547a67de929371f7de9ff54d9ec4ea4498c75588c4f2b0facf251d75b5ab2777576f25e9 (Nat.shiftLeft
  0x3a0757996df2 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (104, (mkQ true (Nat.add (Nat.add
  0x88aa41625c75fffbc540d8a8cb91127b860c7af4acc6e0d0897b3b8f9d914105d687af13 (Nat.shiftLeft (Nat.add
  0xc11c1c030d2ce2537e5a8784e4cf7c812d43ac1854f2ee6e18c7a4ef0438edd184f43453 (Nat.shiftLeft
  0x886aebe6b2945707f2783bd8b42f439a92efabd6ba5f794ffbf201cd49ef9ca3b01a4d73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa371e78f25ba4dc7c014c7d2e06920a5a90fe3a99f790d174bc20a33794e4548e4a1a953
  (Nat.shiftLeft (Nat.add 0x77eb2a9864a23859534eb92f72622b1addd30943de79b190d0b8f2c9f75bd3f09cd66ed1
  (Nat.shiftLeft 0x1bd4924f5e51 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (142, (mkQ true (Nat.add (Nat.add
  0xe6e3eaf32a5a2e65cf3be253e0b917df473e70c46024f9f0ebdd7a0ebd48015d5b3fa54b (Nat.shiftLeft (Nat.add
  0x889d1ab851a67e6e86eb039d7e6969449aae1b71ed579ee2c72ebb735fe266f8df7b5075 (Nat.shiftLeft
  0xc29660a0ca2ec64bf55bc4e8e51828ce41e5b39c76721e7a9da6bd5c3d152fe4d4f234d0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5cbc375dfe5bd79d02ebebc84a0eba6de09c15e785d545d448dc214c8736a18635ca7f2d
  (Nat.shiftLeft (Nat.add 0x43d8d7329a01295aacb29c135328309c50c7f9e955f94295342a98b039f170b55d1efea8
  (Nat.shiftLeft 0x14c629f62a386 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (180, (mkQ true (Nat.add (Nat.add
  0x8cbc6280a6aef0f9ca28953ccdc59b26651b61cafe8d0aa672e736381f2aa5e48ba90e45 (Nat.shiftLeft (Nat.add
  0x58b01568cd7a703351142f26ac3393fad783e170e65b280cc8bd864b4f66d0f65bb3e229 (Nat.shiftLeft
  0x75b64ec58ea92d6af5c2cb732e353713cbb15b0514cbea6fcf661c8156415d0590331ae0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbacfa22f85265c52b49189e3c5468572b12f6b5f3a0bba26010965ed41a415548d3424c0
  (Nat.shiftLeft (Nat.add 0x5ed1ce7788135b909a37c04eb990685ab5597f23e0be0a73d7876c14f4937236a530b401
  (Nat.shiftLeft 0xda6d26ebe5d1 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (218, (mkQ true (Nat.add (Nat.add
  0xe6e3eaf32a5a2e65cf3be253e0b917df473e70c46024f9f0ebdd7a0ebd48015d5b3fa54b (Nat.shiftLeft (Nat.add
  0x889d1ab851a67e6e86eb039d7e6969449aae1b71ed579ee2c72ebb735fe266f8df7b5075 (Nat.shiftLeft
  0xc29660a0ca2ec64bf55bc4e8e51828ce41e5b39c76721e7a9da6bd5c3d152fe4d4f234d0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5cbc375dfe5bd79d02ebebc84a0eba6de09c15e785d545d448dc214c8736a18635ca7f2d
  (Nat.shiftLeft (Nat.add 0x43d8d7329a01295aacb29c135328309c50c7f9e955f94295342a98b039f170b55d1efea8
  (Nat.shiftLeft 0x14c629f62a386 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (256, (mkQ true (Nat.add (Nat.add
  0x88aa41625c75fffbc540d8a8cb91127b860c7af4acc6e0d0897b3b8f9d914105d687af13 (Nat.shiftLeft (Nat.add
  0xc11c1c030d2ce2537e5a8784e4cf7c812d43ac1854f2ee6e18c7a4ef0438edd184f43453 (Nat.shiftLeft
  0x886aebe6b2945707f2783bd8b42f439a92efabd6ba5f794ffbf201cd49ef9ca3b01a4d73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa371e78f25ba4dc7c014c7d2e06920a5a90fe3a99f790d174bc20a33794e4548e4a1a953
  (Nat.shiftLeft (Nat.add 0x77eb2a9864a23859534eb92f72622b1addd30943de79b190d0b8f2c9f75bd3f09cd66ed1
  (Nat.shiftLeft 0x1bd4924f5e51 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (294, (mkQ true (Nat.add (Nat.add
  0xea32cecb0d7bee8504dc35fa5d1fd58b4ed2e4687d455b1861da261797925f3dcd8b0ba1 (Nat.shiftLeft (Nat.add
  0x84c1112e2bdcb569245366a16a0b39b7f7a32209545d29bce0f0146a18e03933d5600abc (Nat.shiftLeft
  0x580b8bb554c928a09a23e85cf3bd82710022573a5f346a0c7158aeb6e15edf166419cd01 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2bb638425d60fe367278e0cfbddc5ad9cbbc70d87061c8f9d94896916c4006b137b4e7b0
  (Nat.shiftLeft (Nat.add 0x547a67de929371f7de9ff54d9ec4ea4498c75588c4f2b0facf251d75b5ab2777576f25e9
  (Nat.shiftLeft 0x3a0757996df2 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864))))])]

def sjsuTsp_36 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 10, 8), [(28, (mkQ true (
  Nat.add (Nat.add 0xb174d2fae0f4575004f40f5a255049b3ec9fc6099dd092cb20f305165183108cecb320b1 (
  Nat.shiftLeft (Nat.add 0xf409cb2001f6de4f1ad5c2bde5c25adb0c4d0573abf756cdb0d4097afa56fa4da57c376 (
  Nat.shiftLeft 0x30936d9f6dba89acabde72fa57319e83fcfdd1ad7c49c8321b5ad14238d1d2c77fbc7a5e 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x35a4a7534162c6bdbab3ef1ccd752e5e6bf5fc09704bed9bde1b36d8d1c711ab434a8938 (Nat.shiftLeft (Nat.add
  0xbded065383acf2d19c1c62d658e8eb8ecb4b6f431f522135fdd0f177ee910fff899a340 (Nat.shiftLeft
  0x1fb33f5f7e251ef8ff3f26343179a20ed3edaa608a8634996494 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (66, (mkQ
  true (Nat.add (Nat.add 0xb19505d3473a354aaa982107ca73f0a3b4ffd473ee485fdec874f16d21e17fe48ccd4c1d
  (Nat.shiftLeft (Nat.add 0x981b497cb746a16da7034191a5c1526d635be9d1656594ff7418c2f3ad0f69be2f6a371b
  (Nat.shiftLeft 0xbb5a7c2f00847eee68bdcaf0f816b3b9a03e42c5275a896bf0f758e47fc61b2afacea8d5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x747a0c2dd7b0731af9d02ea0d2750993b346682fe27efcf2b8f082b166d3c35b62ca635d (Nat.shiftLeft (Nat.add
  0x3121a81f8d3d9279f3bf199911cb4628aee1a3b57b8a6a2f310f6f2ae1d13405476c9c9c (Nat.shiftLeft
  0x1f3640a7b13c3978d30f1670a2e72f25b23df3c47a02168ad0955 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (104, (mkQ
  false (Nat.add (Nat.add 0x95d8d9f54341d0852c67498939473bd1bf0e1f2516f00b800038da0bb89cb5760ae40047
  (Nat.shiftLeft (Nat.add 0x47c2385cfa3adb15e78c561ac9c697474af044edc737deb9e95b43aa0ff610079f80d524
  (Nat.shiftLeft 0x99eea49d7e7030ddc9cd6025405f145e29739282cef8f361706dcb0d50ee90d1cf6fc90b 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdf097982c7b2c7797a218ac7f8e5db7ff3506637d946eba8d7bec5da27debef7fae3493b (Nat.shiftLeft (Nat.add
  0x22887574e42dcb49ef52b36428ddd5ef31d6e129b23649e59af447f3e3efab6230fc2f1c (Nat.shiftLeft
  0x2bb743b4d405fddb9b40ec8b5f170ab543cdbbec389bbb1967a478 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (142, (mkQ
  false (Nat.add (Nat.add 0x190e5ecaa88149a0cb0271e95a952f9822b722eff464a2418a70b82c349fa67212353bc7
  (Nat.shiftLeft (Nat.add 0xe72d50b1d8db4ce9be865b531fece39055a3d23b44bc979713233d00044cd95ee10fa98c
  (Nat.shiftLeft 0x5f854e9c7aa8368119f820527b64fd0dd50ff693edeb1805fe0c88d5c5ca4e2998ebb5e1 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4c80cc3ff112b351ebe4ab80c5386917d121cc80116c9d35daa24c4fd8dbf30ee1eaa40d (Nat.shiftLeft (Nat.add
  0x5905488fb95f928b3f8d1813e5b91ad39a10264215b9b1450e234b57a561c87dca701672 (Nat.shiftLeft
  0x77814533ac87944d11a6b2879c072a6cf9dea01dc3a773ad8ecea4 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (180, (mkQ
  false (Nat.add (Nat.add 0x3015ea30b4e604d3cf086fce74fd6b1ea9763e0673c91b2dd7f1efd67f92b6042b19a381
  (Nat.shiftLeft (Nat.add 0x726a97d242233d0661800b6ff7a701af9252e54f11d2a002940721c5b820caea647d77d1
  (Nat.shiftLeft 0x5cf7fcec30578de0001c17db184aeb60c501fdb68e5e828cc20df75dfb67619eeb3191d2 288))
  288)) (Nat.shiftLeft (Nat.add
  0xf8da71385ca0ff21a32d24741137619cab0f51799629b422a0857e8fe2beab877658395 (Nat.shiftLeft (Nat.add
  0x3170de2164127a882425d2a29644bb8c76e67d2e1f141116e059a3bbfd452cefdeabbd6e (Nat.shiftLeft
  0x1fc1e1f76691fd3269281c86e54a523d227a2fe66414865afdf48 288)) 288)) 864)) (Nat.add (Nat.add
  0x53206ea1f02d36457556c08c9483017cc867e0fd4abd75e18b58fec0124a163ecb5e9000 (Nat.shiftLeft (Nat.add
  0xc3782fd86c5bfeb23e26e50677d9403f14dc8dc2b9a3037e502f0e16b518c27300378675 (Nat.shiftLeft
  0xc5c07729b9e463aba9d91c91262b4eff759225c35a39ae55ca6f06d0e408feaad3ce3626 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbb79a78eb4decae62b8e82ee6da3fcf697ccefdfcab6c6f7829f90f5177da276d353887c
  (Nat.shiftLeft (Nat.add 0x8617245e435822d53ea77dcd9c0fa78e541af33734508ebb76a5e7237d77524ba5ef62ff
  (Nat.shiftLeft 0x359f5bf571984f6106f0e3415daf60bdd433802b57b2a 288)) 288)) 864)))), (218, (mkQ
  false (Nat.add (Nat.add 0x190e5ecaa88149a0cb0271e95a952f9822b722eff464a2418a70b82c349fa67212353bc7
  (Nat.shiftLeft (Nat.add 0xe72d50b1d8db4ce9be865b531fece39055a3d23b44bc979713233d00044cd95ee10fa98c
  (Nat.shiftLeft 0x5f854e9c7aa8368119f820527b64fd0dd50ff693edeb1805fe0c88d5c5ca4e2998ebb5e1 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4c80cc3ff112b351ebe4ab80c5386917d121cc80116c9d35daa24c4fd8dbf30ee1eaa40d (Nat.shiftLeft (Nat.add
  0x5905488fb95f928b3f8d1813e5b91ad39a10264215b9b1450e234b57a561c87dca701672 (Nat.shiftLeft
  0x77814533ac87944d11a6b2879c072a6cf9dea01dc3a773ad8ecea4 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (256, (mkQ
  false (Nat.add (Nat.add 0x95d8d9f54341d0852c67498939473bd1bf0e1f2516f00b800038da0bb89cb5760ae40047
  (Nat.shiftLeft (Nat.add 0x47c2385cfa3adb15e78c561ac9c697474af044edc737deb9e95b43aa0ff610079f80d524
  (Nat.shiftLeft 0x99eea49d7e7030ddc9cd6025405f145e29739282cef8f361706dcb0d50ee90d1cf6fc90b 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdf097982c7b2c7797a218ac7f8e5db7ff3506637d946eba8d7bec5da27debef7fae3493b (Nat.shiftLeft (Nat.add
  0x22887574e42dcb49ef52b36428ddd5ef31d6e129b23649e59af447f3e3efab6230fc2f1c (Nat.shiftLeft
  0x2bb743b4d405fddb9b40ec8b5f170ab543cdbbec389bbb1967a478 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (294, (mkQ
  true (Nat.add (Nat.add 0xb19505d3473a354aaa982107ca73f0a3b4ffd473ee485fdec874f16d21e17fe48ccd4c1d
  (Nat.shiftLeft (Nat.add 0x981b497cb746a16da7034191a5c1526d635be9d1656594ff7418c2f3ad0f69be2f6a371b
  (Nat.shiftLeft 0xbb5a7c2f00847eee68bdcaf0f816b3b9a03e42c5275a896bf0f758e47fc61b2afacea8d5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x747a0c2dd7b0731af9d02ea0d2750993b346682fe27efcf2b8f082b166d3c35b62ca635d (Nat.shiftLeft (Nat.add
  0x3121a81f8d3d9279f3bf199911cb4628aee1a3b57b8a6a2f310f6f2ae1d13405476c9c9c (Nat.shiftLeft
  0x1f3640a7b13c3978d30f1670a2e72f25b23df3c47a02168ad0955 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (332, (mkQ
  true (Nat.add (Nat.add 0xb174d2fae0f4575004f40f5a255049b3ec9fc6099dd092cb20f305165183108cecb320b1
  (Nat.shiftLeft (Nat.add 0xf409cb2001f6de4f1ad5c2bde5c25adb0c4d0573abf756cdb0d4097afa56fa4da57c376
  (Nat.shiftLeft 0x30936d9f6dba89acabde72fa57319e83fcfdd1ad7c49c8321b5ad14238d1d2c77fbc7a5e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x35a4a7534162c6bdbab3ef1ccd752e5e6bf5fc09704bed9bde1b36d8d1c711ab434a8938 (Nat.shiftLeft (Nat.add
  0xbded065383acf2d19c1c62d658e8eb8ecb4b6f431f522135fdd0f177ee910fff899a340 (Nat.shiftLeft
  0x1fb33f5f7e251ef8ff3f26343179a20ed3edaa608a8634996494 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864))))])]

def sjsuTsp_37 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 11, 1), [(161, (mkQ false (
  Nat.add (Nat.add 0xc687b22569eba35130a8255bea59d7c28f7efb2796191dcddee8bdc3e4f9b2a82506d2a3 (
  Nat.shiftLeft 0xf5201fd7370b020845cfbc5b747d61516492086c138a714d36ea08266989e05bb345665a 288)) (
  Nat.shiftLeft (Nat.add 0x9f85dabb34a48b575123edcc4c1cdbc15c565ea9be8e7bdf9e48b973caade8096a0d8c99
  (Nat.shiftLeft 0xc8f5df5ceba383b009eaa8f4c3a4da4cf594e679b63387b718cc43bb74bf3e870f8 288)) 576)) (
  Nat.add (Nat.add 0xe6925aa018b70cde8365844efe45be916c8553da65c148f7f979c5dec11f76302a000000 (
  Nat.shiftLeft 0x87d45c308c20f7bd1806cd1064f2fc10aad0e0d8b6fa401fc911e76afb23bc7b7c506703 288)) (
  Nat.shiftLeft (Nat.add 0x937d7d626f8c676ab37f0065668d38678b87fe105147dde27ce0ebd6c62ad9eae7ce8177
  (Nat.shiftLeft 0x1b6d185950632dcb99434158d8e4ec464243c1a03f1bcbd42eb52c1037497ae85c3 288)) 576))))
  , (199, (mkQ false (Nat.add (Nat.add
  0xc687b22569eba35130a8255bea59d7c28f7efb2796191dcddee8bdc3e4f9b2a82506d2a3 (Nat.shiftLeft
  0xf5201fd7370b020845cfbc5b747d61516492086c138a714d36ea08266989e05bb345665a 288)) (Nat.shiftLeft (
  Nat.add 0x9f85dabb34a48b575123edcc4c1cdbc15c565ea9be8e7bdf9e48b973caade8096a0d8c99 (Nat.shiftLeft
  0xc8f5df5ceba383b009eaa8f4c3a4da4cf594e679b63387b718cc43bb74bf3e870f8 288)) 576)) (Nat.add (
  Nat.add 0xe6925aa018b70cde8365844efe45be916c8553da65c148f7f979c5dec11f76302a000000 (Nat.shiftLeft
  0x87d45c308c20f7bd1806cd1064f2fc10aad0e0d8b6fa401fc911e76afb23bc7b7c506703 288)) (Nat.shiftLeft (
  Nat.add 0x937d7d626f8c676ab37f0065668d38678b87fe105147dde27ce0ebd6c62ad9eae7ce8177 (Nat.shiftLeft
  0x1b6d185950632dcb99434158d8e4ec464243c1a03f1bcbd42eb52c1037497ae85c3 288)) 576))))]), ((0, 11, 3)
  , [(123, (mkQ true (Nat.add (Nat.add
  0xa22c728f6738f9f13a9613b0e9adc954fe8da37d417334cc8bd7d8084ce88160f594f01d (Nat.shiftLeft
  0x323862bb9dcd2464ea7908f2761159be7bf2f1e490dffaddede38560ecadf967cbd3ec5c 288)) (Nat.shiftLeft (
  Nat.add 0xb9fa3ac3a5b5cf9bfcab391027be6fcfe14b869e863e775e0c0d8239a4af17e2a8e2125e (Nat.shiftLeft
  (Nat.add 0x5c5f1d8733e99a01874e338edbe6d9bbb1fd0a5db77726432642a0254daf96d522fd5635 (Nat.shiftLeft
  0x97de7c4aac0f8ce8d7e48a4cc26c678a49cd6ed 288)) 288)) 576)) (Nat.add (Nat.add
  0xca5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda80000 (Nat.shiftLeft
  0x214619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35 288)) (Nat.shiftLeft (
  Nat.add 0x38cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf263 (Nat.shiftLeft
  (Nat.add 0x6684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef9 288)) 288)) 576)))), (161, (mkQ true (Nat.add (Nat.add
  0x10ceb4f968b0882c59d27ff834e91036f7e9a6b1e4d7d865862a5aa01d6701d43698f057 (Nat.shiftLeft
  0x862c8b34e104e7f8b8f74c8317645bd12f070a00544e65db5317978c9716048b48aa7c02 288)) (Nat.shiftLeft (
  Nat.add 0xcc482aa2b056adb241f059e2c93aad9fcf1d1de46fabd39aab575004e733827565ebe1a (Nat.shiftLeft (
  Nat.add 0xff2879ed08d7d1ef48c5644ff0d229436163538b88c3014e947e724ea46b85d2728fd169 (Nat.shiftLeft
  0x54efb840dea8355d1221e82423e7a1d8f4f7cc4d 288)) 288)) 576)) (Nat.add (Nat.add
  0x94ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b500000 (Nat.shiftLeft
  0x428c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b 288)) (Nat.shiftLeft (
  Nat.add 0x719de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c6 (Nat.shiftLeft
  (Nat.add 0xcd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b8 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2 288)) 288)) 576)))), (199, (mkQ true (Nat.add (Nat.add
  0x10ceb4f968b0882c59d27ff834e91036f7e9a6b1e4d7d865862a5aa01d6701d43698f057 (Nat.shiftLeft
  0x862c8b34e104e7f8b8f74c8317645bd12f070a00544e65db5317978c9716048b48aa7c02 288)) (Nat.shiftLeft (
  Nat.add 0xcc482aa2b056adb241f059e2c93aad9fcf1d1de46fabd39aab575004e733827565ebe1a (Nat.shiftLeft (
  Nat.add 0xff2879ed08d7d1ef48c5644ff0d229436163538b88c3014e947e724ea46b85d2728fd169 (Nat.shiftLeft
  0x54efb840dea8355d1221e82423e7a1d8f4f7cc4d 288)) 288)) 576)) (Nat.add (Nat.add
  0x94ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b500000 (Nat.shiftLeft
  0x428c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b 288)) (Nat.shiftLeft (
  Nat.add 0x719de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c6 (Nat.shiftLeft
  (Nat.add 0xcd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b8 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2 288)) 288)) 576)))), (237, (mkQ true (Nat.add (Nat.add
  0xa22c728f6738f9f13a9613b0e9adc954fe8da37d417334cc8bd7d8084ce88160f594f01d (Nat.shiftLeft
  0x323862bb9dcd2464ea7908f2761159be7bf2f1e490dffaddede38560ecadf967cbd3ec5c 288)) (Nat.shiftLeft (
  Nat.add 0xb9fa3ac3a5b5cf9bfcab391027be6fcfe14b869e863e775e0c0d8239a4af17e2a8e2125e (Nat.shiftLeft
  (Nat.add 0x5c5f1d8733e99a01874e338edbe6d9bbb1fd0a5db77726432642a0254daf96d522fd5635 (Nat.shiftLeft
  0x97de7c4aac0f8ce8d7e48a4cc26c678a49cd6ed 288)) 288)) 576)) (Nat.add (Nat.add
  0xca5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda80000 (Nat.shiftLeft
  0x214619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35 288)) (Nat.shiftLeft (
  Nat.add 0x38cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf263 (Nat.shiftLeft
  (Nat.add 0x6684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef9 288)) 288)) 576))))])]

def sjsuTsp_38 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 11, 5), [(85, (mkQ false (
  Nat.add (Nat.add 0x740154703201a4e4e367d8ea6b13bcf36e0ceef41a9e310d4e48f73a22ed7eb609fa062d (
  Nat.shiftLeft (Nat.add 0xbbd0ea0101d2062be5e902e7dd4775c18af59679fbdd3022ccd338baa0976047eb2aacfe
  (Nat.shiftLeft 0xc9efbfbc958fa9952c4377ff36aba90ff8cb9ffd924cec89603b64adb0f4b0e05ae30783 288))
  288)) (Nat.shiftLeft (Nat.add
  0x18b73f8bf05da044fa3cb6bbb7adee73377a8d3a9f5e4b272fcb3e1a76265aef939fbaf8 (Nat.shiftLeft (Nat.add
  0x364a43c221e1253d0ea3ee47efde63779e54f749e8241be31baba2786afd27b99d9d00b (Nat.shiftLeft
  0x9583982d33f 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (123, (mkQ false (Nat.add (Nat.add
  0x6d8079ffc3a231169b21bbfe19ceef2945113509f0fdc33732364e47b57624d3be067c4d (Nat.shiftLeft (Nat.add
  0xaa12923e4c5a72b1db46f2ba3809329a22d2922b5954d91132a2623fbc7e20e21171c283 (Nat.shiftLeft
  0x802ccb7a4f090576c12b956fca9234f024a4c025d9cc17a4502f5f9238b7fea10f24f687 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbf9e1e26e2fc7f8a19eda967a29a201a2e79dd7869387c9517552c52c05a8deb5db9fcd3
  (Nat.shiftLeft (Nat.add 0xf55cf6e8422ed730db4f8e0c9b8f2185b92713ceb47ab7dedf16e0b4feb69cd2a7d74640
  (Nat.shiftLeft 0x292e71a9da14 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (161, (mkQ false (Nat.add (Nat.add
  0x9beebfa2576a7773c567d57e54f862518275e4bbc436180151069bade2a081479e01e421 (Nat.shiftLeft (Nat.add
  0xc2d843463aa9f16de482784b3e31ad93042db615c46ca0eeaa8dfd3f1f3264b7ad03120b (Nat.shiftLeft
  0xe2e5fce03c6b809da2042758a80795cdb8fb4272cfbb2f8f16c59cb726b39b6bb5dc07c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7db4694e3abad7219014bfba05ad38bc9b772053920276ed4b366e288dfcbe4723f4e509
  (Nat.shiftLeft (Nat.add 0x6e6dbccf01b6930146ed473f66d5eae192e2d71b86e3c92010e859d11f02ca82b853ac53
  (Nat.shiftLeft 0x12c9e841d8c05 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (199, (mkQ false (Nat.add (Nat.add
  0x9beebfa2576a7773c567d57e54f862518275e4bbc436180151069bade2a081479e01e421 (Nat.shiftLeft (Nat.add
  0xc2d843463aa9f16de482784b3e31ad93042db615c46ca0eeaa8dfd3f1f3264b7ad03120b (Nat.shiftLeft
  0xe2e5fce03c6b809da2042758a80795cdb8fb4272cfbb2f8f16c59cb726b39b6bb5dc07c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7db4694e3abad7219014bfba05ad38bc9b772053920276ed4b366e288dfcbe4723f4e509
  (Nat.shiftLeft (Nat.add 0x6e6dbccf01b6930146ed473f66d5eae192e2d71b86e3c92010e859d11f02ca82b853ac53
  (Nat.shiftLeft 0x12c9e841d8c05 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (237, (mkQ false (Nat.add (Nat.add
  0x6d8079ffc3a231169b21bbfe19ceef2945113509f0fdc33732364e47b57624d3be067c4d (Nat.shiftLeft (Nat.add
  0xaa12923e4c5a72b1db46f2ba3809329a22d2922b5954d91132a2623fbc7e20e21171c283 (Nat.shiftLeft
  0x802ccb7a4f090576c12b956fca9234f024a4c025d9cc17a4502f5f9238b7fea10f24f687 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbf9e1e26e2fc7f8a19eda967a29a201a2e79dd7869387c9517552c52c05a8deb5db9fcd3
  (Nat.shiftLeft (Nat.add 0xf55cf6e8422ed730db4f8e0c9b8f2185b92713ceb47ab7dedf16e0b4feb69cd2a7d74640
  (Nat.shiftLeft 0x292e71a9da14 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (275, (mkQ false (Nat.add (Nat.add
  0x740154703201a4e4e367d8ea6b13bcf36e0ceef41a9e310d4e48f73a22ed7eb609fa062d (Nat.shiftLeft (Nat.add
  0xbbd0ea0101d2062be5e902e7dd4775c18af59679fbdd3022ccd338baa0976047eb2aacfe (Nat.shiftLeft
  0xc9efbfbc958fa9952c4377ff36aba90ff8cb9ffd924cec89603b64adb0f4b0e05ae30783 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x18b73f8bf05da044fa3cb6bbb7adee73377a8d3a9f5e4b272fcb3e1a76265aef939fbaf8
  (Nat.shiftLeft (Nat.add 0x364a43c221e1253d0ea3ee47efde63779e54f749e8241be31baba2786afd27b99d9d00b
  (Nat.shiftLeft 0x9583982d33f 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864))))])]

def sjsuTsp_39 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 11, 7), [(47, (mkQ false (
  Nat.add (Nat.add 0x1af049015446851dce343968782c68961ff9c3dcbd2caf679bc3401d65dc0428f8a5c879 (
  Nat.shiftLeft (Nat.add 0x60713a81bd87fa567b58094c67101abfa15cfa501e254a96c5a56315af17c575a45918f3
  (Nat.shiftLeft 0xc1bd866bee67afa2e1c5cf5034899ace9e8a51ab33a89dea4ba5e79af20acaa1dafd0b7b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6c85a5bbc094c6672e2bfb623498cf007d2c2f84711fcb3e4cb89a97a761643a07e99786 (Nat.shiftLeft (Nat.add
  0x53c3342deb39e5305ba0fdd83b4ce5ce15d28418b769c7ad08b1d928574eeeafd9dae1c7 (Nat.shiftLeft
  0x28c6332996203fd702b3fcf81a1be0658753f6eb63e92faa5cd 288)) 288)) 864)) (Nat.add (Nat.add
  0x640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd20000 (Nat.shiftLeft (Nat.add
  0x6f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa (Nat.shiftLeft
  0xb80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff7
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550 288)) 288)) 864)))), (85, (mkQ
  true (Nat.add (Nat.add 0xe3f2383e863275fa1f63741fa158e50a910d2703c4fea7e968b1b9c4ebba92495ac839d9
  (Nat.shiftLeft (Nat.add 0x3bd966735c15c6beb7c6970bdeafba9399fe26823adbbe757d8a3b430d949c0acbb868b5
  (Nat.shiftLeft 0x1115990cd50eef367405f4ee66232320054f09003afe0127a21263985e56733e2ade0400 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3c180ce3d70a2220ec8506ca4e06782847d71448a35732f85f4a8d3374a6d41c8f3f79ca (Nat.shiftLeft (Nat.add
  0x3f386d2b933c6812614e4f90d02084646861088b260b64ee931b4017685179da64acd553 (Nat.shiftLeft
  0x3f87e3c76809c5aa09f713f81ce40884ba33814f7c290b0434db4 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (123, (mkQ
  true (Nat.add (Nat.add 0x6660a70321b1977041cc505d8968d85ec0acd24c423c3e861bb72fd16f52b1b5ab09109b
  (Nat.shiftLeft (Nat.add 0x7eb478b5ec0e606f3d2b0d4003add870ce985a6d99c5a586429788b593b83847fc0830ba
  (Nat.shiftLeft 0x5de60452208f1edb9ce3393c829ff509ab9b7283d6d186c2ad1489de3bb54fe7f5cb3421 288))
  288)) (Nat.shiftLeft (Nat.add
  0x5c595fb2d320eff16aeeded7fa9bd20e75694268df0b9713b1ed9169dc6b2370ccd4df28 (Nat.shiftLeft (Nat.add
  0x8162136147af293a824e12c2523ccd6c1dafa2d856c31404cda8e551ea4e05fc814acc6e (Nat.shiftLeft
  0x8f255376c36de5e76b1ea6ffc0fe3260657a4a536e6745c45da01 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (161, (mkQ
  true (Nat.add (Nat.add 0x37b6578d9ff1942240bdee3a34aa9a63e39d155897380679fe3092e172bfa0000a735215
  (Nat.shiftLeft (Nat.add 0xaba1717f03f2c5dedd7e5e7c1eb8f078111ff8835c88b518649e2c4482e2322668d55820
  (Nat.shiftLeft 0x6341d50e2e835111e8f0547e704d98d6f76ef0896f63e63123f1a96f7d45c9a76de823a 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x51eedee095001cfef81a8e9ebad11bc9bed9e6a15e3af55ba9e65d8ab5408f2ddd36d37 (Nat.shiftLeft (Nat.add
  0x7a8d6c08b5f9fa51002ed10acb3419cfb580eebabdd6909f1833e5ade8e4c6fb057d6f2a (Nat.shiftLeft
  0x7c176ad6921f77d149a120fc74c5e9ac24a85b9b2820d3da22878b 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (199, (mkQ
  true (Nat.add (Nat.add 0x37b6578d9ff1942240bdee3a34aa9a63e39d155897380679fe3092e172bfa0000a735215
  (Nat.shiftLeft (Nat.add 0xaba1717f03f2c5dedd7e5e7c1eb8f078111ff8835c88b518649e2c4482e2322668d55820
  (Nat.shiftLeft 0x6341d50e2e835111e8f0547e704d98d6f76ef0896f63e63123f1a96f7d45c9a76de823a 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x51eedee095001cfef81a8e9ebad11bc9bed9e6a15e3af55ba9e65d8ab5408f2ddd36d37 (Nat.shiftLeft (Nat.add
  0x7a8d6c08b5f9fa51002ed10acb3419cfb580eebabdd6909f1833e5ade8e4c6fb057d6f2a (Nat.shiftLeft
  0x7c176ad6921f77d149a120fc74c5e9ac24a85b9b2820d3da22878b 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (237, (mkQ
  true (Nat.add (Nat.add 0x6660a70321b1977041cc505d8968d85ec0acd24c423c3e861bb72fd16f52b1b5ab09109b
  (Nat.shiftLeft (Nat.add 0x7eb478b5ec0e606f3d2b0d4003add870ce985a6d99c5a586429788b593b83847fc0830ba
  (Nat.shiftLeft 0x5de60452208f1edb9ce3393c829ff509ab9b7283d6d186c2ad1489de3bb54fe7f5cb3421 288))
  288)) (Nat.shiftLeft (Nat.add
  0x5c595fb2d320eff16aeeded7fa9bd20e75694268df0b9713b1ed9169dc6b2370ccd4df28 (Nat.shiftLeft (Nat.add
  0x8162136147af293a824e12c2523ccd6c1dafa2d856c31404cda8e551ea4e05fc814acc6e (Nat.shiftLeft
  0x8f255376c36de5e76b1ea6ffc0fe3260657a4a536e6745c45da01 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (275, (mkQ
  true (Nat.add (Nat.add 0xe3f2383e863275fa1f63741fa158e50a910d2703c4fea7e968b1b9c4ebba92495ac839d9
  (Nat.shiftLeft (Nat.add 0x3bd966735c15c6beb7c6970bdeafba9399fe26823adbbe757d8a3b430d949c0acbb868b5
  (Nat.shiftLeft 0x1115990cd50eef367405f4ee66232320054f09003afe0127a21263985e56733e2ade0400 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3c180ce3d70a2220ec8506ca4e06782847d71448a35732f85f4a8d3374a6d41c8f3f79ca (Nat.shiftLeft (Nat.add
  0x3f386d2b933c6812614e4f90d02084646861088b260b64ee931b4017685179da64acd553 (Nat.shiftLeft
  0x3f87e3c76809c5aa09f713f81ce40884ba33814f7c290b0434db4 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (313, (mkQ
  false (Nat.add (Nat.add 0x1af049015446851dce343968782c68961ff9c3dcbd2caf679bc3401d65dc0428f8a5c879
  (Nat.shiftLeft (Nat.add 0x60713a81bd87fa567b58094c67101abfa15cfa501e254a96c5a56315af17c575a45918f3
  (Nat.shiftLeft 0xc1bd866bee67afa2e1c5cf5034899ace9e8a51ab33a89dea4ba5e79af20acaa1dafd0b7b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6c85a5bbc094c6672e2bfb623498cf007d2c2f84711fcb3e4cb89a97a761643a07e99786 (Nat.shiftLeft (Nat.add
  0x53c3342deb39e5305ba0fdd83b4ce5ce15d28418b769c7ad08b1d928574eeeafd9dae1c7 (Nat.shiftLeft
  0x28c6332996203fd702b3fcf81a1be0658753f6eb63e92faa5cd 288)) 288)) 864)) (Nat.add (Nat.add
  0x640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd20000 (Nat.shiftLeft (Nat.add
  0x6f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa (Nat.shiftLeft
  0xb80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff7
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550 288)) 288)) 864))))])]

def sjsuTsp_40 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 12, 0), [(180, (mkQ false (
  Nat.add (Nat.add 0x9bbd687f0e74ac00134210aa9fce27085bd020830d519cf2882b583bf56967a62f3f7347 (
  Nat.shiftLeft 0x5b94220a81e310a36f95c54264fc2d7c4e37e8d89a2b22e4d0c56e0f0228f73946c6f101 288)) (
  Nat.shiftLeft (Nat.add 0x16b9548d7119bfd5b8fe11545c13daeec8ec88fa6c579e9585124860b4be4503a112c752
  (Nat.shiftLeft 0x13e30e9fcd879bf5af592169595c41052117342bdd51e08a647908ffc5088aef459 288)) 576)) (
  Nat.add (Nat.add 0x380dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d200000 (
  Nat.shiftLeft 0x5a725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d92031 288)) (
  Nat.shiftLeft (Nat.add 0x1e17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded641968708875
  (Nat.shiftLeft 0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd 288)) 576))))]
  ), ((0, 12, 2), [(142, (mkQ false (Nat.add (Nat.add
  0x18b04d84778530833c26ad24701dee3017ec0745c1ab0a9c25f9adbf9468e5b647b439 (Nat.shiftLeft
  0x88dd2a21d698b1e1a3a23409c487b2fd78d9d6121b0778afeb7a48178e9f2d9f7839012d 288)) (Nat.shiftLeft (
  Nat.add 0x5c122e326b0ab1892c4981cf165494a534d76db07b5d195439436329f4ebab6bf6f42987 (Nat.shiftLeft
  (Nat.add 0x4d566f9068996db957cddcf84a2cb570bc37896bd13317100015e3b12a7c15ee5f69e593 (Nat.shiftLeft
  0x667dee0dd1f3e5a4293bd76ebc9e263f070d6c3 288)) 288)) 576)) (Nat.add (Nat.add
  0x29753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a00000 (Nat.shiftLeft
  0x851866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd7 288)) (Nat.shiftLeft (
  Nat.add 0xe33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c (Nat.shiftLeft
  (Nat.add 0x9a138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970 (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be5 288)) 288)) 576)))), (180, (mkQ false (Nat.add (Nat.add
  0x53a75523907eb22b832a994af3ee548da44e026596a6560c3583449075e3caa3edeffbdd (Nat.shiftLeft
  0x6b12f64c9f367f375d3884f3bcff4757674cf91e13f8114eb6c0dcecca97cdf719f986e9 288)) (Nat.shiftLeft (
  Nat.add 0x60cab1e52fe88e174ab8c4d4d15bab87cdf0b03b47a340f66cd8ebb20961ccc2f08ba528 (Nat.shiftLeft
  (Nat.add 0xad2ac457184eb8d0dcb4352256115cb60d656bac58704c49d6787f35d7bf2f415b1ff749 (Nat.shiftLeft
  0x1eab83d308bd051e7d5ea0fc9fe25d55d254d36b 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (218, (mkQ false (Nat.add (Nat.add
  0x18b04d84778530833c26ad24701dee3017ec0745c1ab0a9c25f9adbf9468e5b647b439 (Nat.shiftLeft
  0x88dd2a21d698b1e1a3a23409c487b2fd78d9d6121b0778afeb7a48178e9f2d9f7839012d 288)) (Nat.shiftLeft (
  Nat.add 0x5c122e326b0ab1892c4981cf165494a534d76db07b5d195439436329f4ebab6bf6f42987 (Nat.shiftLeft
  (Nat.add 0x4d566f9068996db957cddcf84a2cb570bc37896bd13317100015e3b12a7c15ee5f69e593 (Nat.shiftLeft
  0x667dee0dd1f3e5a4293bd76ebc9e263f070d6c3 288)) 288)) 576)) (Nat.add (Nat.add
  0x29753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a00000 (Nat.shiftLeft
  0x851866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd7 288)) (Nat.shiftLeft (
  Nat.add 0xe33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c (Nat.shiftLeft
  (Nat.add 0x9a138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970 (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be5 288)) 288)) 576))))])]

def sjsuTsp_41 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 12, 4), [(104, (mkQ true (
  Nat.add (Nat.add 0xc40882de57aa1b34efbdd6cd99c1c98a51e3d2d581b494ac0be23dd4230f1153a3ac1849 (
  Nat.shiftLeft (Nat.add 0x4403ced7d91ebed532a552a5a37c91937a06c4f17dbea070ef1615d5bff54aaa41ef26b (
  Nat.shiftLeft 0xb61562ed12ebb6c0b8b9d71b88dd7cc8de693a81303e1d4b95c4e0001152fa38c790e8b 288)) 288)
  ) (Nat.shiftLeft (Nat.add
  0x1093e29ff4e95c7101f0bde646922ad7851868a3320baf54494f72fe7d981923c944c22f (Nat.shiftLeft (Nat.add
  0x4d6c9b1393047e4a64c43e8a1ea10a8dc830757773d7c8fc0fd31ed7784f498246a17245 (Nat.shiftLeft
  0xdefd31dc21 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (142, (mkQ true (Nat.add (Nat.add
  0x690d1b3a41eeffd82b840e885f92f174132fa1856bb2019219c1b8907940a4f948915373 (Nat.shiftLeft (Nat.add
  0x53d7bf3c66b3bdf81454c644db3f1159ae0eb45b1f2ea12288c4200dfbe4f177f430ba40 (Nat.shiftLeft
  0xbe449aee584bc9b2d909f55910f97d8ce56fbc1bfd823d7b2d23a5f8d70857dbc89f2a31 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x46e05716e4a9626280b7cc38da58afeeb40dca84d89cd31a400c9fd12e31c294ed13efb (
  Nat.shiftLeft (Nat.add 0x363f0c9fe76dacf18384f0389426c392ed685eebd816e0ddf0e2d68f499c995cee2c2327
  (Nat.shiftLeft 0x4b1bbd21b7e 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (180, (mkQ true (Nat.add (Nat.add
  0x5864b823a990fce972fbd3d4766ab01ccc4c37728b3deb6ecbbca281275918a2bde6f911 (Nat.shiftLeft (Nat.add
  0xa702da2894b2c6d681272505c43fdc64ba9cff06f1b0b238c42fd8f3bcdce64617e9088e (Nat.shiftLeft
  0x17f796f7835336a811051f93dce79a38ee7679c9d2771fe46a31e4f55fa6ed8f3e045136 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf522f209d01f1a246f371a012155749c29e0db0b81638e4da7ffe15fbb07880cd5094605
  (Nat.shiftLeft (Nat.add 0xea4deac74baf5c2a2d848139271e695f9ca11e3c87fec613282664bb49aace2a75cdaec3
  (Nat.shiftLeft 0x536fedc9fd37 288)) 288)) 864)) (Nat.add (Nat.add
  0xa67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb78880000 (Nat.shiftLeft (Nat.add
  0xec3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9 (Nat.shiftLeft
  0xd91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310
  (Nat.shiftLeft (Nat.add 0x7ee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb
  (Nat.shiftLeft 0x3d39df9 288)) 288)) 864)))), (218, (mkQ true (Nat.add (Nat.add
  0x690d1b3a41eeffd82b840e885f92f174132fa1856bb2019219c1b8907940a4f948915373 (Nat.shiftLeft (Nat.add
  0x53d7bf3c66b3bdf81454c644db3f1159ae0eb45b1f2ea12288c4200dfbe4f177f430ba40 (Nat.shiftLeft
  0xbe449aee584bc9b2d909f55910f97d8ce56fbc1bfd823d7b2d23a5f8d70857dbc89f2a31 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x46e05716e4a9626280b7cc38da58afeeb40dca84d89cd31a400c9fd12e31c294ed13efb (
  Nat.shiftLeft (Nat.add 0x363f0c9fe76dacf18384f0389426c392ed685eebd816e0ddf0e2d68f499c995cee2c2327
  (Nat.shiftLeft 0x4b1bbd21b7e 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (256, (mkQ true (Nat.add (Nat.add
  0xc40882de57aa1b34efbdd6cd99c1c98a51e3d2d581b494ac0be23dd4230f1153a3ac1849 (Nat.shiftLeft (Nat.add
  0x4403ced7d91ebed532a552a5a37c91937a06c4f17dbea070ef1615d5bff54aaa41ef26b (Nat.shiftLeft
  0xb61562ed12ebb6c0b8b9d71b88dd7cc8de693a81303e1d4b95c4e0001152fa38c790e8b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x1093e29ff4e95c7101f0bde646922ad7851868a3320baf54494f72fe7d981923c944c22f
  (Nat.shiftLeft (Nat.add 0x4d6c9b1393047e4a64c43e8a1ea10a8dc830757773d7c8fc0fd31ed7784f498246a17245
  (Nat.shiftLeft 0xdefd31dc21 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864))))])]

def sjsuTsp_42 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 12, 6), [(66, (mkQ false (
  Nat.add (Nat.add 0x6921b5219ef42e0d9a3220fa6a30d2f0702cb722b9f29a0647badafdd06d01146f97faa7 (
  Nat.shiftLeft (Nat.add 0x529bbd7d304329b76e38a578cb9f8d49383b4e3b502d332aa4a89edba1827082e691a392
  (Nat.shiftLeft 0x94c2622df1760e476b9e3a74658b6f08a01518c987196444bb81b3915d4a126d677a7f5 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x2e2702bd68f87fc7b661a141140dd9ce6ad0927f671b34c6f3b0d431d23b3bb8faf83ef9 (Nat.shiftLeft (Nat.add
  0x58ae2f6172a0ca59ab7cc8bd419d5c34e5644489bd0ed55be52f94a7a7c16eb48193f7fe (Nat.shiftLeft
  0x960999d899d5039718a371f5409317033ae65c5836300b96d8d 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (104, (mkQ
  false (Nat.add (Nat.add 0xf30401196b9bdc4e80a15e503e6fa71c63b474297f7f7e351af64ae2660f5b76f8ffdb35
  (Nat.shiftLeft (Nat.add 0x975b6f16ec76431c966e8a31f67a493cd6b67c9305e821d31c2c3499f4a4d156c465ae74
  (Nat.shiftLeft 0x20c2e573aea53fc109308d75e1913f39f36ae556ded7760b93681cb4661288ad7a8e5ee3 288))
  288)) (Nat.shiftLeft (Nat.add
  0xefc3ae194eeb971e0882f43ff7ac67c5c716417d42932305ba8bbedd80ca50080b6f8dfe (Nat.shiftLeft (Nat.add
  0xb26db6427912c4e3bcc5d5fafec6adfd1dff1c66d041eeb525be5f45a1841327ef21fd (Nat.shiftLeft
  0x26cc8cc4439042601168ddfdf9a6391ceaa5cfaf3baced2245259 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (142, (mkQ
  false (Nat.add (Nat.add 0x4f5d8d61a0bf4a87b497681cc0fe51abc3542f5e64238c9070bfe47a8aa659db4949ca59
  (Nat.shiftLeft (Nat.add 0xd37d875e33be5f94d9d398d76f595a33c3eda557f8a503af7c94289d75326124d924e7d1
  (Nat.shiftLeft 0xe1274e8304147bfeeb736165a368e2d56614bd62bce434c20ba80e991c4665f64aa63576 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3124bd0ad7f66eafb2ad7a7edc63db05ad6baf0122390cc5b60d02c6f5bf44499453ec3a (Nat.shiftLeft (Nat.add
  0x3ff9bdb31201ce45ee3a45eb0ab703a3618a5e4074f964d16fc0c7d7804bb0a7366665ce (Nat.shiftLeft
  0x26ca09de0fc8f8ebd233510a424b59bb416e3de83101843442b9 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (180, (mkQ
  false (Nat.add (Nat.add 0x34f003cdc14fcc8bfeac25fcf491bf4096a0ff4d18201c9b1832cd8138c54d3fe5906b59
  (Nat.shiftLeft (Nat.add 0xceef93b913e92eba60d63a8aa7cf9d89b8713f3ea46949f59d11e1669e6935a4d875102f
  (Nat.shiftLeft 0xb3063ae6481013ffbc947268a943c8023b8f1d0473c4c6f4ef080e785117ee85e4e2e568 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4999a59ce14c8a81c1736ae2a9b32cc21f38662f504ab4be073d84f3b70e5bff7b957dc6 (Nat.shiftLeft (Nat.add
  0x8f8623b06c37b932290b0ae2c4d63f089b24dfe0c8465a185d52ca0ad658054f97c290de (Nat.shiftLeft
  0x1fb30d6bacc67db0d0879de4f349f9ffa1e5cb7ade2bdb35327ef 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (218, (mkQ
  false (Nat.add (Nat.add 0x4f5d8d61a0bf4a87b497681cc0fe51abc3542f5e64238c9070bfe47a8aa659db4949ca59
  (Nat.shiftLeft (Nat.add 0xd37d875e33be5f94d9d398d76f595a33c3eda557f8a503af7c94289d75326124d924e7d1
  (Nat.shiftLeft 0xe1274e8304147bfeeb736165a368e2d56614bd62bce434c20ba80e991c4665f64aa63576 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3124bd0ad7f66eafb2ad7a7edc63db05ad6baf0122390cc5b60d02c6f5bf44499453ec3a (Nat.shiftLeft (Nat.add
  0x3ff9bdb31201ce45ee3a45eb0ab703a3618a5e4074f964d16fc0c7d7804bb0a7366665ce (Nat.shiftLeft
  0x26ca09de0fc8f8ebd233510a424b59bb416e3de83101843442b9 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (256, (mkQ
  false (Nat.add (Nat.add 0xf30401196b9bdc4e80a15e503e6fa71c63b474297f7f7e351af64ae2660f5b76f8ffdb35
  (Nat.shiftLeft (Nat.add 0x975b6f16ec76431c966e8a31f67a493cd6b67c9305e821d31c2c3499f4a4d156c465ae74
  (Nat.shiftLeft 0x20c2e573aea53fc109308d75e1913f39f36ae556ded7760b93681cb4661288ad7a8e5ee3 288))
  288)) (Nat.shiftLeft (Nat.add
  0xefc3ae194eeb971e0882f43ff7ac67c5c716417d42932305ba8bbedd80ca50080b6f8dfe (Nat.shiftLeft (Nat.add
  0xb26db6427912c4e3bcc5d5fafec6adfd1dff1c66d041eeb525be5f45a1841327ef21fd (Nat.shiftLeft
  0x26cc8cc4439042601168ddfdf9a6391ceaa5cfaf3baced2245259 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (294, (mkQ
  false (Nat.add (Nat.add 0x6921b5219ef42e0d9a3220fa6a30d2f0702cb722b9f29a0647badafdd06d01146f97faa7
  (Nat.shiftLeft (Nat.add 0x529bbd7d304329b76e38a578cb9f8d49383b4e3b502d332aa4a89edba1827082e691a392
  (Nat.shiftLeft 0x94c2622df1760e476b9e3a74658b6f08a01518c987196444bb81b3915d4a126d677a7f5 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x2e2702bd68f87fc7b661a141140dd9ce6ad0927f671b34c6f3b0d431d23b3bb8faf83ef9 (Nat.shiftLeft (Nat.add
  0x58ae2f6172a0ca59ab7cc8bd419d5c34e5644489bd0ed55be52f94a7a7c16eb48193f7fe (Nat.shiftLeft
  0x960999d899d5039718a371f5409317033ae65c5836300b96d8d 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864))))])]

def sjsuTsp_43 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 13, 1), [(161, (mkQ true (
  Nat.add (Nat.add 0x53f01f4d469a76da5d55fd752b8f44d7f686dabddef2e8d6267b4236b0cf093eec4efa8d (
  Nat.shiftLeft 0x7a1edc4d9c5fa7df58bb2791acbcb3cd1b8a91e5fa224d7929d986aacbbb30174fafe1e8 288)) (
  Nat.shiftLeft (Nat.add 0xfa26b9d81e6b8ea531191abb610614d30ac3aee0a12b0971924c75462d6dc0c532663f69
  (Nat.shiftLeft (Nat.add 0x64001d412b9f3ac385a9318f67bbee58f0da8b0cad7c2ecfbd0c19507353203ba8700f8e
  (Nat.shiftLeft 0x2db12f230a16a2325935febac2869a133429e07 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576)))), (199, (mkQ true (Nat.add (Nat.add
  0x53f01f4d469a76da5d55fd752b8f44d7f686dabddef2e8d6267b4236b0cf093eec4efa8d (Nat.shiftLeft
  0x7a1edc4d9c5fa7df58bb2791acbcb3cd1b8a91e5fa224d7929d986aacbbb30174fafe1e8 288)) (Nat.shiftLeft (
  Nat.add 0xfa26b9d81e6b8ea531191abb610614d30ac3aee0a12b0971924c75462d6dc0c532663f69 (Nat.shiftLeft
  (Nat.add 0x64001d412b9f3ac385a9318f67bbee58f0da8b0cad7c2ecfbd0c19507353203ba8700f8e (Nat.shiftLeft
  0x2db12f230a16a2325935febac2869a133429e07 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576))))]), ((0, 13, 3), [(123, (mkQ false (
  Nat.add (Nat.add 0x1af30c1c033a94a82d669f909fe9dade682d0d7dae94b47da68e05572b45149cf51a2407 (
  Nat.shiftLeft (Nat.add 0xd3935fcc969d1674a025cb4fbf6e4a0fae6ca6e05caeb24bf96077220486b410c7956b88
  (Nat.shiftLeft 0xc3e1a06edb433ad06d500d5bc93b2df60e8bf370330fde180ddfc0a1011de85954134605 288))
  288)) (Nat.shiftLeft (Nat.add
  0xb2da4c1f0cd06e743a1c556a8cbc81f37276b38e54b4a890bc6e276c3e4a2e25ad957b83 (Nat.shiftLeft (Nat.add
  0xf515c106d936be79eeaad1c64bf879d24657d035c6d5ebb36e3081972e9afbaf239098ac (Nat.shiftLeft
  0x66819ce4077 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (161, (mkQ false (Nat.add (Nat.add
  0x86ee820243ebba5d98f00f5e725a1f1b68020cba00c925e2c08f24f1649018b9fcde0ad1 (Nat.shiftLeft (Nat.add
  0xcca4986484753c9cb1c80e39edec6cc1c9258165884419d47135fff20117e5a10d39b70d (Nat.shiftLeft
  0xc8a6740cababb17c7e33e173a99742c5b46ffd5ebdb06537addb7d3b32dbbf2b09da294c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5303e5068ffbea936d50538292826e8159174eda1ea80b320173fb1508ffa124a46a039
  (Nat.shiftLeft (Nat.add 0x2faf834924ff6d4c0e0891ae4b263fe90f868fd65606597464c4b7dc465883a22eb3762a
  (Nat.shiftLeft 0x868194198f 288)) 288)) 864)) (Nat.add (Nat.add
  0x2c09e66c69fd2b8fb3858829289f74d2ab46ea580ba5ccbf54fe9620397bdbbe5b900000 (Nat.shiftLeft (Nat.add
  0x319e5771fc3f99f9521bfe2ae59b31d31c4ccc69291e3293f5207dad87c44f151dda50c7 (Nat.shiftLeft
  0x1b9bdf25282c6527bfc1d64b228c5beaebdc055ba1a0eb698ddf4c7e89bc1e8d8cd358fb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76d36438c446dbabc7e0ec18cb4a4742ce50e6090605ee80b7ea72ecb2461b1116a67ef7
  (Nat.shiftLeft (Nat.add 0xd6f33cb8fecb000c2b743d31b151b03801f1290106aedc6a70414b943eec7ecde3456f83
  (Nat.shiftLeft 0x4e5e8e 288)) 288)) 864)))), (199, (mkQ false (Nat.add (Nat.add
  0x86ee820243ebba5d98f00f5e725a1f1b68020cba00c925e2c08f24f1649018b9fcde0ad1 (Nat.shiftLeft (Nat.add
  0xcca4986484753c9cb1c80e39edec6cc1c9258165884419d47135fff20117e5a10d39b70d (Nat.shiftLeft
  0xc8a6740cababb17c7e33e173a99742c5b46ffd5ebdb06537addb7d3b32dbbf2b09da294c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5303e5068ffbea936d50538292826e8159174eda1ea80b320173fb1508ffa124a46a039
  (Nat.shiftLeft (Nat.add 0x2faf834924ff6d4c0e0891ae4b263fe90f868fd65606597464c4b7dc465883a22eb3762a
  (Nat.shiftLeft 0x868194198f 288)) 288)) 864)) (Nat.add (Nat.add
  0x2c09e66c69fd2b8fb3858829289f74d2ab46ea580ba5ccbf54fe9620397bdbbe5b900000 (Nat.shiftLeft (Nat.add
  0x319e5771fc3f99f9521bfe2ae59b31d31c4ccc69291e3293f5207dad87c44f151dda50c7 (Nat.shiftLeft
  0x1b9bdf25282c6527bfc1d64b228c5beaebdc055ba1a0eb698ddf4c7e89bc1e8d8cd358fb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76d36438c446dbabc7e0ec18cb4a4742ce50e6090605ee80b7ea72ecb2461b1116a67ef7
  (Nat.shiftLeft (Nat.add 0xd6f33cb8fecb000c2b743d31b151b03801f1290106aedc6a70414b943eec7ecde3456f83
  (Nat.shiftLeft 0x4e5e8e 288)) 288)) 864)))), (237, (mkQ false (Nat.add (Nat.add
  0x1af30c1c033a94a82d669f909fe9dade682d0d7dae94b47da68e05572b45149cf51a2407 (Nat.shiftLeft (Nat.add
  0xd3935fcc969d1674a025cb4fbf6e4a0fae6ca6e05caeb24bf96077220486b410c7956b88 (Nat.shiftLeft
  0xc3e1a06edb433ad06d500d5bc93b2df60e8bf370330fde180ddfc0a1011de85954134605 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb2da4c1f0cd06e743a1c556a8cbc81f37276b38e54b4a890bc6e276c3e4a2e25ad957b83
  (Nat.shiftLeft (Nat.add 0xf515c106d936be79eeaad1c64bf879d24657d035c6d5ebb36e3081972e9afbaf239098ac
  (Nat.shiftLeft 0x66819ce4077 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864))))])]

def sjsuTsp_44 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 13, 5), [(85, (mkQ true (
  Nat.add (Nat.add 0x5e20f75c1613b6811cb4516f94f66bf7fcc8bd5ef0fe8a288810c64e16fc2083e29fec87 (
  Nat.shiftLeft (Nat.add 0xa9ecbd485317853cf40e752be4a1375fff6d007610f311426d74e42c301aa5b961969c4c
  (Nat.shiftLeft 0x948ceaae43bc067c3a86504ee8b1106a387f66bfc35e55e9b7089b6e5e7f2ad2fbce0fa2 288))
  288)) (Nat.shiftLeft (Nat.add
  0x89b3a51a01f098fa756606fd7e8866b4f53545f68d3ffed57a05a8bf8e19a454328a146f (Nat.shiftLeft (Nat.add
  0xa9c7d1adeba1a62b49f17c83b3b8cfd8a7eeb2c1d4e2ffc6f1356b9a3f0cdaa26db814e9 (Nat.shiftLeft
  0x27eb0eef2d0a3d4ee6ab4f45a17695480e3adb30096cd8f204d 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864)))), (123, (mkQ
  true (Nat.add (Nat.add 0x86f92b040a43ed8963f6c4d0b64c7e93c5560d350bc6a0c7531638a11c93db34ad5d9d5 (
  Nat.shiftLeft (Nat.add 0x167b1e1bbc6efedafbc9710a8531d254ed9173317ab9361513467923c43fec598502326d
  (Nat.shiftLeft 0x56bad9dbb25e73f27e87b4c790f3bd98eded766f8122b3ebde1a70ae77513c42b310868d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa2e687c487e52f92983774467e6b99d7887189bdd113814c88a566bbc8af9377e6515859 (Nat.shiftLeft (Nat.add
  0xa05432178eee551b7ccbecb45493ec4528817c6253ed276027ec08b2283fa63b12c50431 (Nat.shiftLeft
  0x2cfada7d155694769078ad95c7b68d359993c9fa3ace3f343b219 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (161, (mkQ
  true (Nat.add (Nat.add 0xcd031131224499fa7df4dc34c30224a67a1d91244827c6125cf91c01bd99728fa11b3a6b
  (Nat.shiftLeft (Nat.add 0x57a10ead70653bcd4c33e2ccb6359023f85f95261589510f310529cf46f9bc9d14c3b8e3
  (Nat.shiftLeft 0x518cc72a227a1eec1c2d7b6c7057be4a7e70d6baaf28c7aeb279fd036fa664b026de63bf 288))
  288)) (Nat.shiftLeft (Nat.add
  0x169cae95c2bd909ba25c60f2b87eb944fe7a119683e215293dc31b08bee44970bb4489a7 (Nat.shiftLeft (Nat.add
  0x223566f855398c974acc2e4b44eb9fa0cdebac98432c2fbb925ce6d348fd8ae8b5ee0ee (Nat.shiftLeft
  0x1faeb9ffbe47c41566cf58dd7bfe3df656cb58e28fdea5f831e0a 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (199, (mkQ
  true (Nat.add (Nat.add 0xcd031131224499fa7df4dc34c30224a67a1d91244827c6125cf91c01bd99728fa11b3a6b
  (Nat.shiftLeft (Nat.add 0x57a10ead70653bcd4c33e2ccb6359023f85f95261589510f310529cf46f9bc9d14c3b8e3
  (Nat.shiftLeft 0x518cc72a227a1eec1c2d7b6c7057be4a7e70d6baaf28c7aeb279fd036fa664b026de63bf 288))
  288)) (Nat.shiftLeft (Nat.add
  0x169cae95c2bd909ba25c60f2b87eb944fe7a119683e215293dc31b08bee44970bb4489a7 (Nat.shiftLeft (Nat.add
  0x223566f855398c974acc2e4b44eb9fa0cdebac98432c2fbb925ce6d348fd8ae8b5ee0ee (Nat.shiftLeft
  0x1faeb9ffbe47c41566cf58dd7bfe3df656cb58e28fdea5f831e0a 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (237, (mkQ
  true (Nat.add (Nat.add 0x86f92b040a43ed8963f6c4d0b64c7e93c5560d350bc6a0c7531638a11c93db34ad5d9d5 (
  Nat.shiftLeft (Nat.add 0x167b1e1bbc6efedafbc9710a8531d254ed9173317ab9361513467923c43fec598502326d
  (Nat.shiftLeft 0x56bad9dbb25e73f27e87b4c790f3bd98eded766f8122b3ebde1a70ae77513c42b310868d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa2e687c487e52f92983774467e6b99d7887189bdd113814c88a566bbc8af9377e6515859 (Nat.shiftLeft (Nat.add
  0xa05432178eee551b7ccbecb45493ec4528817c6253ed276027ec08b2283fa63b12c50431 (Nat.shiftLeft
  0x2cfada7d155694769078ad95c7b68d359993c9fa3ace3f343b219 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (275, (mkQ
  true (Nat.add (Nat.add 0x5e20f75c1613b6811cb4516f94f66bf7fcc8bd5ef0fe8a288810c64e16fc2083e29fec87
  (Nat.shiftLeft (Nat.add 0xa9ecbd485317853cf40e752be4a1375fff6d007610f311426d74e42c301aa5b961969c4c
  (Nat.shiftLeft 0x948ceaae43bc067c3a86504ee8b1106a387f66bfc35e55e9b7089b6e5e7f2ad2fbce0fa2 288))
  288)) (Nat.shiftLeft (Nat.add
  0x89b3a51a01f098fa756606fd7e8866b4f53545f68d3ffed57a05a8bf8e19a454328a146f (Nat.shiftLeft (Nat.add
  0xa9c7d1adeba1a62b49f17c83b3b8cfd8a7eeb2c1d4e2ffc6f1356b9a3f0cdaa26db814e9 (Nat.shiftLeft
  0x27eb0eef2d0a3d4ee6ab4f45a17695480e3adb30096cd8f204d 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864))))]), ((0, 14, 0)
  , [(180, (mkQ true (Nat.add (Nat.add
  0x1410e730d8563bc6edb4869ab2f5ba648938934e6d8c1bd93475e318d6e43d962460701b (Nat.shiftLeft
  0xa03f812bd26c4212712e14c7264234209adf9add2c70114771cf36cf22078d815ca795bb 288)) (Nat.shiftLeft (
  Nat.add 0xe623c326acbdbbf4610926b752d5644682638dc013dd498a70cf6b0e4e2b390b784dce8b (Nat.shiftLeft
  (Nat.add 0xda88e0b5f82bac005ae8f437868b2c69829ed8b841bbd1d9764357d39371d8b2723e336e (Nat.shiftLeft
  0x45de9f8d39b92ddf8bad13b4aeafdbce8f23e 288)) 288)) 576)) (Nat.add (Nat.add
  0xca5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda80000 (Nat.shiftLeft
  0x214619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35 288)) (Nat.shiftLeft (
  Nat.add 0x38cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf263 (Nat.shiftLeft
  (Nat.add 0x6684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef9 288)) 288)) 576))))])]

def sjsuTsp_45 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((0, 14, 2), [(142, (mkQ true (
  Nat.add (Nat.add 0xb769c26bb3142dac94a7cd5c8134da797e66f1da12a143143ef4e1fca681cebc631df71d (
  Nat.shiftLeft (Nat.add 0x57443de783b8d9f7c59bf18873d44c27a8396935bdf33b0c2ed0e7e2e22888a3eaee6143
  (Nat.shiftLeft 0x6ecc9891967a51520902443265cd5877ab8c95b5b51aa9b341726783b1fdc3415e454357 288))
  288)) (Nat.shiftLeft (Nat.add
  0x242d5fcffa9797e7c1e98f061444c14a92c0f209c892f5569e448e74ac389d93ed2584a (Nat.shiftLeft (Nat.add
  0xe941728a2b1f55cccd3aecd925677db94b300726bf9285b52161e1944ab2b9117e732349 (Nat.shiftLeft
  0x73134dac47 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (180, (mkQ true (Nat.add (Nat.add
  0x85e006875623d22c49ffff127d3ebcfb65c9d6d03b835b68cdb3b1a53ae8e8a4e7792f2d (Nat.shiftLeft (Nat.add
  0xe080254c55eb7652757cb4a6c908718493d608f526842238a796145ba55a7d24bc8bdc6b (Nat.shiftLeft
  0x1eeb2186d023f994c777e4450791bc2210373ae19ec2803d218a69c050be7518aa1e321b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x937f46aef606b2dbec2bc7b62d359afedd26766400f5365910db8ac41cbfd3f51d20b019
  (Nat.shiftLeft (Nat.add 0xa9887f3c2bc22f015596fb0c01df0328cd138d8ed02d922e6dc04b823a1dc714c69bd6d9
  (Nat.shiftLeft 0x153cebafc4 288)) 288)) 864)) (Nat.add (Nat.add
  0x5813ccd8d3fa571f670b1052513ee9a5568dd4b0174b997ea9fd2c4072f7b77cb7200000 (Nat.shiftLeft (Nat.add
  0x633caee3f87f33f2a437fc55cb3663a6389998d2523c6527ea40fb5b0f889e2a3bb4a18e (Nat.shiftLeft
  0x3737be4a5058ca4f7f83ac964518b7d5d7b80ab74341d6d31bbe98fd13783d1b19a6b1f6 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xeda6c871888db7578fc1d83196948e859ca1cc120c0bdd016fd4e5d9648c36222d4cfdee
  (Nat.shiftLeft (Nat.add 0xade67971fd96001856e87a6362a3607003e252020d5db8d4e08297287dd8fd9bc68adf06
  (Nat.shiftLeft 0x9cbd1d 288)) 288)) 864)))), (218, (mkQ true (Nat.add (Nat.add
  0xb769c26bb3142dac94a7cd5c8134da797e66f1da12a143143ef4e1fca681cebc631df71d (Nat.shiftLeft (Nat.add
  0x57443de783b8d9f7c59bf18873d44c27a8396935bdf33b0c2ed0e7e2e22888a3eaee6143 (Nat.shiftLeft
  0x6ecc9891967a51520902443265cd5877ab8c95b5b51aa9b341726783b1fdc3415e454357 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x242d5fcffa9797e7c1e98f061444c14a92c0f209c892f5569e448e74ac389d93ed2584a (
  Nat.shiftLeft (Nat.add 0xe941728a2b1f55cccd3aecd925677db94b300726bf9285b52161e1944ab2b9117e732349
  (Nat.shiftLeft 0x73134dac47 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864))))])]


end KAM.EffectiveStability.SJSU

end
