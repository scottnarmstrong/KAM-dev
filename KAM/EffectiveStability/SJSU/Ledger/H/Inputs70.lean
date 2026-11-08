/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs69

/-!
# Ledger inputs (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

def sjsuTsp_452 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 3, 1), [(125, (mkQ false (
  Nat.add (Nat.add 0x47abe90cc7f7421b7bf66f64e198ee6ad2664d69a8b0c7064c9101e750064429dc770137 (
  Nat.shiftLeft 0xc8303570f6acea9fe0249482abcfa1bd6d0bc161b5474d9f2bdccdb05a03af49bcd8bebc 288)) (
  Nat.shiftLeft (Nat.add 0xaadd63c77cf52dc12f8e02fe7e66d6b0d4835a03b19bc44698a4ad45ec011aa7b83815b (
  Nat.shiftLeft 0xc16d1de93a845530447e5ff8ff67309836aa4d32bfea30f7f848913f68ab58abc14e21e 288)) 576)
  ) (Nat.add (Nat.add 0x6de2903dc9a02c487dcac57bae5c6b8f4d51a1fe63366befb06eace2cea778690000000 (
  Nat.shiftLeft 0x392e6795e526b58bc1100a8fc5f7629ab0a321dc971a04f76acc28b73d95734b6c90189c 288)) (
  Nat.shiftLeft (Nat.add 0xb9b97616df028ac0bd80fd80610d02dcd3fb28cb33aab638324d98ef6b20cb438443aad (
  Nat.shiftLeft 0x4490bcdf48f7f27cff28235e1e3c4eafa5a964109dc57d9274c4ee288a37b344e68f 288)) 576))))
  , (127, (mkQ true (Nat.add (Nat.add
  0xea85fcff31faf1f4c68bdbca0d5b90192cb8cfb2a47a4c1a1609c54ea637d32b2c1a069 (Nat.shiftLeft
  0xc05e371959a9767d7dcc4be5a96a29fd9e01667fffb4749d26290e87a93d03647e45774a 288)) (Nat.shiftLeft (
  Nat.add 0x8b0a36fcd8b4b3f6df97022e6cf258bed2fe2e03434a172cdca777b4f7dad3ce47ef125 (Nat.shiftLeft
  0x1810a2f4d5f4bab1b7028877bdd83eea942c293289b2755abaaad4e9836ff07b0f34c80 288)) 576)) (Nat.add (
  Nat.add 0x36f1481ee4d016243ee562bdd72e35c7a6a8d0ff319b35f7d83756716753bc348000000 (Nat.shiftLeft
  0x9c9733caf2935ac5e0880547e2fbb14d585190ee4b8d027bb566145b9ecab9a5b6480c4e 288)) (Nat.shiftLeft (
  Nat.add 0x85cdcbb0b6f8145605ec07ec03086816e69fd946599d55b1c1926cc77b59065a1c221d56 (Nat.shiftLeft
  0x22485e6fa47bf93e7f9411af0f1e2757d2d4b2084ee2bec93a627714451bd9a27347 288)) 576)))), (161, (mkQ
  false (Nat.add (Nat.add 0xc937d96b76b182ac3fcaba8ca94e6ae0d5e1cc314dd8a91df04101e3e481d9a85a8f1c33
  (Nat.shiftLeft 0xb562665b0f8da4acb0833163fa17959d8a4911a584bedcd28c1abfe861f07b8ef2630304 288)) (
  Nat.shiftLeft (Nat.add 0xb38a6ae1a8675e1754a7f4cad9f4569ad1deedb1044f70f58a17440a2f9702937cdb005c
  (Nat.shiftLeft 0xedf90fec3d4a5f049dd92798df97fb7e6aa4be71acf8ba07faa6d43b513d88c6f144f16 288)) 576
  )) (Nat.add (Nat.add 0x3492d500c5b866f41b2c2277f22df48b642a9ed32e0a47bfcbce2ef608fbb18150000000 (
  Nat.shiftLeft 0x3ea2e1846107bde8c03668832797e085568706c5b7d200fe488f3b57d91de3dbe283381f 288)) (
  Nat.shiftLeft (Nat.add 0x9bebeb137c633b559bf8032b3469c33c5c3ff0828a3eef13e7075eb63156cf573e740bbc
  (Nat.shiftLeft 0xdb68c2ca83196e5cca1a0ac6c7276232121e0d01f8de5ea175a96081ba4bd742e1c 288)) 576))))
  , (163, (mkQ false (Nat.add (Nat.add
  0x4996008a259d9be9adc57682c7e71f01ad67377c06528058733d153a324d03f4b79c6e55 (Nat.shiftLeft
  0x7ac9c5a5b435db36a480beccf19315078fc12e000cc1083741182ec27b018269ab369b61 288)) (Nat.shiftLeft (
  Nat.add 0xd84e0186d40c443ed76ec6e96357b14519364d445cce10d1294f1b56c6adb9fd4b2891ce (Nat.shiftLeft
  0x31320b1d73c0a15adb33b606ac03ad8655573a823b175c0590bc15dd22ed0323735fa8f1 288)) 576)) (Nat.add (
  Nat.add 0x6de2903dc9a02c487dcac57bae5c6b8f4d51a1fe63366befb06eace2cea778690000000 (Nat.shiftLeft
  0x392e6795e526b58bc1100a8fc5f7629ab0a321dc971a04f76acc28b73d95734b6c90189c 288)) (Nat.shiftLeft (
  Nat.add 0xb9b97616df028ac0bd80fd80610d02dcd3fb28cb33aab638324d98ef6b20cb438443aad (Nat.shiftLeft
  0x4490bcdf48f7f27cff28235e1e3c4eafa5a964109dc57d9274c4ee288a37b344e68f 288)) 576)))), (197, (mkQ
  false (Nat.add (Nat.add 0x4996008a259d9be9adc57682c7e71f01ad67377c06528058733d153a324d03f4b79c6e55
  (Nat.shiftLeft 0x7ac9c5a5b435db36a480beccf19315078fc12e000cc1083741182ec27b018269ab369b61 288)) (
  Nat.shiftLeft (Nat.add 0xd84e0186d40c443ed76ec6e96357b14519364d445cce10d1294f1b56c6adb9fd4b2891ce
  (Nat.shiftLeft 0x31320b1d73c0a15adb33b606ac03ad8655573a823b175c0590bc15dd22ed0323735fa8f1 288))
  576)) (Nat.add (Nat.add 0x6de2903dc9a02c487dcac57bae5c6b8f4d51a1fe63366befb06eace2cea778690000000
  (Nat.shiftLeft 0x392e6795e526b58bc1100a8fc5f7629ab0a321dc971a04f76acc28b73d95734b6c90189c 288)) (
  Nat.shiftLeft (Nat.add 0xb9b97616df028ac0bd80fd80610d02dcd3fb28cb33aab638324d98ef6b20cb438443aad (
  Nat.shiftLeft 0x4490bcdf48f7f27cff28235e1e3c4eafa5a964109dc57d9274c4ee288a37b344e68f 288)) 576))))
  , (199, (mkQ false (Nat.add (Nat.add
  0xc937d96b76b182ac3fcaba8ca94e6ae0d5e1cc314dd8a91df04101e3e481d9a85a8f1c33 (Nat.shiftLeft
  0xb562665b0f8da4acb0833163fa17959d8a4911a584bedcd28c1abfe861f07b8ef2630304 288)) (Nat.shiftLeft (
  Nat.add 0xb38a6ae1a8675e1754a7f4cad9f4569ad1deedb1044f70f58a17440a2f9702937cdb005c (Nat.shiftLeft
  0xedf90fec3d4a5f049dd92798df97fb7e6aa4be71acf8ba07faa6d43b513d88c6f144f16 288)) 576)) (Nat.add (
  Nat.add 0x3492d500c5b866f41b2c2277f22df48b642a9ed32e0a47bfcbce2ef608fbb18150000000 (Nat.shiftLeft
  0x3ea2e1846107bde8c03668832797e085568706c5b7d200fe488f3b57d91de3dbe283381f 288)) (Nat.shiftLeft (
  Nat.add 0x9bebeb137c633b559bf8032b3469c33c5c3ff0828a3eef13e7075eb63156cf573e740bbc (Nat.shiftLeft
  0xdb68c2ca83196e5cca1a0ac6c7276232121e0d01f8de5ea175a96081ba4bd742e1c 288)) 576)))), (233, (mkQ
  true (Nat.add (Nat.add 0xea85fcff31faf1f4c68bdbca0d5b90192cb8cfb2a47a4c1a1609c54ea637d32b2c1a069 (
  Nat.shiftLeft 0xc05e371959a9767d7dcc4be5a96a29fd9e01667fffb4749d26290e87a93d03647e45774a 288)) (
  Nat.shiftLeft (Nat.add 0x8b0a36fcd8b4b3f6df97022e6cf258bed2fe2e03434a172cdca777b4f7dad3ce47ef125 (
  Nat.shiftLeft 0x1810a2f4d5f4bab1b7028877bdd83eea942c293289b2755abaaad4e9836ff07b0f34c80 288)) 576)
  ) (Nat.add (Nat.add 0x36f1481ee4d016243ee562bdd72e35c7a6a8d0ff319b35f7d83756716753bc348000000 (
  Nat.shiftLeft 0x9c9733caf2935ac5e0880547e2fbb14d585190ee4b8d027bb566145b9ecab9a5b6480c4e 288)) (
  Nat.shiftLeft (Nat.add 0x85cdcbb0b6f8145605ec07ec03086816e69fd946599d55b1c1926cc77b59065a1c221d56
  (Nat.shiftLeft 0x22485e6fa47bf93e7f9411af0f1e2757d2d4b2084ee2bec93a627714451bd9a27347 288)) 576)))
  ), (235, (mkQ false (Nat.add (Nat.add
  0x47abe90cc7f7421b7bf66f64e198ee6ad2664d69a8b0c7064c9101e750064429dc770137 (Nat.shiftLeft
  0xc8303570f6acea9fe0249482abcfa1bd6d0bc161b5474d9f2bdccdb05a03af49bcd8bebc 288)) (Nat.shiftLeft (
  Nat.add 0xaadd63c77cf52dc12f8e02fe7e66d6b0d4835a03b19bc44698a4ad45ec011aa7b83815b (Nat.shiftLeft
  0xc16d1de93a845530447e5ff8ff67309836aa4d32bfea30f7f848913f68ab58abc14e21e 288)) 576)) (Nat.add (
  Nat.add 0x6de2903dc9a02c487dcac57bae5c6b8f4d51a1fe63366befb06eace2cea778690000000 (Nat.shiftLeft
  0x392e6795e526b58bc1100a8fc5f7629ab0a321dc971a04f76acc28b73d95734b6c90189c 288)) (Nat.shiftLeft (
  Nat.add 0xb9b97616df028ac0bd80fd80610d02dcd3fb28cb33aab638324d98ef6b20cb438443aad (Nat.shiftLeft
  0x4490bcdf48f7f27cff28235e1e3c4eafa5a964109dc57d9274c4ee288a37b344e68f 288)) 576))))])]

def sjsuTsp_453 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 3, 3), [(123, (mkQ true (
  Nat.add (Nat.add 0x8906dec98d5887552d13980aff5fa95c0c2438b62cfd31d023740fae021ca7fafe1c8439 (
  Nat.shiftLeft 0xcc6f1eef94c99fc0c64c88e80c82b5fea5c51a073fa8a846177ddeab615f636e6a5e5b16 288)) (
  Nat.shiftLeft (Nat.add 0xd47ddb664a0a6690c70c074e80ca6c50d98b823ba3d3be61425fc676a529fc700177dc18
  (Nat.shiftLeft (Nat.add 0xe66920e29a6c66b4c3f8c9ffbc9fa717b6781b5098d8b5ef4c7df0e420da88bcc0d7ad32
  (Nat.shiftLeft 0x290e55edad0d428c9c0e8b75ae2038b8bcfeeb55 288)) 288)) 576)) (Nat.add (Nat.add
  0x3392be4f0c3860cc464356d92424f403d34358d9089bd1917952beb771af5d4664000000 (Nat.shiftLeft
  0x866ca58f63e38822fc9840533137fff9c438f80b93496a99faa14001d3c4b519e62d6bbc 288)) (Nat.shiftLeft (
  Nat.add 0xd7de250c862fcd558a9fde638d50ffc2c5bb50f2502c7b6fdd8ee07ca4ddba9694da0ebb (Nat.shiftLeft
  (Nat.add 0xbefed97ac99b5dd65f287ebc333e7cb32414f2df9ae121eefd1430e8977c8e6deed9edef (Nat.shiftLeft
  0xbba8483fd549c8dbf5d3b1369d657390c38e 288)) 288)) 576)))), (125, (mkQ true (Nat.add (Nat.add
  0x67031cc4d66c1e5aa3810888d259d21a58458d6f12a559133b203c85d6aff00381e846b (Nat.shiftLeft
  0xccb38ca15ae5a46b4ae9fbd4fcd3672c8d299100235660e4ca7265c35aea0826622564e6 288)) (Nat.shiftLeft (
  Nat.add 0x54eae791279654c9a72acd295f97f266da696270719d6aa7eb25f58e51c3b4b115d26aa0 (Nat.shiftLeft
  (Nat.add 0x21c5a68890d5063bbbf62a6117c77e4db1496c3534ef01f6df82f0512aab69b5948be809 (Nat.shiftLeft
  0x2c713dbbe2687cda4b66babb092da491a637c424da 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (127, (mkQ true (Nat.add (Nat.add
  0x32a6cd43cae7daff7673ddc87a1fa753e831c903ae2e4ba87280936adad50dc71eff3465 (Nat.shiftLeft
  0xe1143f14cec15b2ca72f5e8c1d8de30321b413925f08f9e8981adddf4ca1589500112b8a 288)) (Nat.shiftLeft (
  Nat.add 0xe8143300a2229e4ce340e8b4ef4c5de0387eb63a49f072ed20f617c14ff7c877a3fbb748 (Nat.shiftLeft
  (Nat.add 0x22fcb688407511e2a60f9897d20b6045686c09a611e26825ff2899c5318b4be0359522c1 (Nat.shiftLeft
  0xd63474ed0244dce2904aba30cd54845f358ad734f 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (129, (mkQ false (Nat.add (Nat.add
  0x7b7c1e9747b99d613b72b75d2dfc1a52e139405b4a4629dd600da7e60b71061e3bba733 (Nat.shiftLeft
  0x12120122b7c3e0dafd5468d1d63b7c6cbbd562e35762778d933e02ede9341905611d92 288)) (Nat.shiftLeft (
  Nat.add 0xa3525f0ea16541bcc9306ecb0abcd44d59c32c748c5768f3d722af82d4bb530d26da56be (Nat.shiftLeft
  (Nat.add 0xba539c47e340c2985f5d03f1434df22e9ae91ca5204d2fcb73ae9dbe6d2b9ba2498d9a25 (Nat.shiftLeft
  0x51affdfc4f12f741b5d1a837cff75cc42fd2b155 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (159, (mkQ true (Nat.add (Nat.add
  0x6c896251256f002fc60c32823b37f9e551a5fe2c3863393f5ccbb1984c6e1b8b3340a637 (Nat.shiftLeft
  0x2c6fb4d0087a679bece460c78c9e7a3af392d600af9cfa5d1f69768fac8d97bdbf51f140 288)) (Nat.shiftLeft (
  Nat.add 0xbc7a7294771cc6aca418cc4266cc32c9a6f0e678b90dae6fad71b91b3cf50cf2139307da (Nat.shiftLeft
  (Nat.add 0x851c013fdfc60befd4c49fe478fd20a502fa45bc451748a6bab495296594666668133302 (Nat.shiftLeft
  0x5a9fb33b6197fdef98d91fd071c2baf6c290395553 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (161, (mkQ true (Nat.add (Nat.add
  0xdfbf2d1e33168f56bbed11575e22f69c5b4f46c4a0d42202bfd71629fbb628f56f2e8a81 (Nat.shiftLeft
  0x55049cc0b973deb0050c8e58d57f9a2dbb7c4aec67aa440a46417d67a9c2f3331e2f828d 288)) (Nat.shiftLeft (
  Nat.add 0xac97ad49650cc7981bb2c52b873c0733060fe616bca01456cffee71cf136db46e1b33e33 (Nat.shiftLeft
  (Nat.add 0x4dc311644b118fdf0927eb6da78ffc95a83b2fb9c7d22eaccc1a0c80fc711c8147fd590c (Nat.shiftLeft
  0x3bd4f020ab2949742a47bd3003bf271f900cc3b9a 288)) 288)) 576)) (Nat.add (Nat.add
  0x80eedbc59e8cf1feafa8591eda5c620990285e1e95858bebaf4edcca9c36692ffa000000 (Nat.shiftLeft
  0xd00f9de679b8d457777ca0cffb0bfff06a8e6c1cf0378a80f2932004916bc4c0bf718d56 288)) (Nat.shiftLeft (
  Nat.add 0x9bab5c9f4f778155da8fabf8e14a7f66ee544a5dc86f3497a9e531379c2a5278742124d4 (Nat.shiftLeft
  (Nat.add 0xdd7d1fb2f8046a97ede53cd6801c37bfda345f2f0332d4d578b27a457ab76412d520d2d7 (Nat.shiftLeft
  0x1d524b49f95387625e6913b08897da0e9e8e4 288)) 288)) 576)))), (163, (mkQ true (Nat.add (Nat.add
  0xb21dae64aeb91761917e5a65047603b3888d9251bab0fa47ba13446d9bbc01e984e1065d (Nat.shiftLeft
  0x35a346d38ff1a459f7b105bd6ec6f41181afb231f00f3b955f3e4381f38877b10f47a7ed 288)) (Nat.shiftLeft (
  Nat.add 0x6d9ef448819f0f232533d386d317d91783c7ab29a4981f18f7d1d4779e06ac9043593244 (Nat.shiftLeft
  (Nat.add 0x4120c1e5d936799798df67c90fa58e77c133e2afc2cd2aa40adabfba09a3fc6a5ecd08ac (Nat.shiftLeft
  0xdce4e041a629efd742dcaf75f9eea4f30804b06f0 288)) 288)) 576)) (Nat.add (Nat.add
  0x84aa4adc18c0b9f96e49bd9a43cdea2fd0c9d698eb9bbb9a6c8a4ff50d100defe2000000 (Nat.shiftLeft
  0x104e1580609c25b5556f240fe73bffb214c81c90b115b484bcdfa016d71ad7c3bd37c2b0 288)) (Nat.shiftLeft (
  Nat.add 0xa58cf1c8d5586ad44ce5bdc66747d02a7a573d4ea2c06f65179f6160cd39c5a44a5b828 (Nat.shiftLeft (
  Nat.add 0x53719e7ed81614f7a57a3030808d16bf4305dbeb0ffe282b5b7c635b6594f45e29a41e36 (Nat.shiftLeft
  0x929b7871dea1a4ebd80d6272aaf7424918c78 288)) 288)) 576)))), (165, (mkQ true (Nat.add (Nat.add
  0x7fbd93e2df41d3f6af6d0cfb81c7deba4543d946a5645114eb5fb4f47b3d218691eaeb3d (Nat.shiftLeft
  0x7e18c7a98b411fd55d5fddad8384707a059e03b269180ed3101dc2e03a1b3337c949dc7 288)) (Nat.shiftLeft (
  Nat.add 0x3d79264b4c9538c9b288ce25ef5263c2958efec01a39e5913f1460b905440f23caae87d3 (Nat.shiftLeft
  (Nat.add 0xfc95975626bcd425d287250bb807161a9db3cd17f27237f3c66cf6486915ea48b4aacbd (Nat.shiftLeft
  0x266e1ab9227641ca181a3b1f9c0754533ead54f20 288)) 288)) 576)) (Nat.add (Nat.add
  0x776de2cf4678ff57d42c8f6d2e3104c8142f0f4ac2c5f5d7a76e654e1b3497fd0000000 (Nat.shiftLeft
  0x807cef33cdc6a2bbbbe5067fd85fff83547360e781bc5407949900248b5e2605fb8c6ab4 288)) (Nat.shiftLeft (
  Nat.add 0xdd5ae4fa7bbc0aaed47d5fc70a53fb3772a252ee4379a4bd4f2989bce15293c3a10926a6 (Nat.shiftLeft
  (Nat.add 0xebe8fd97c02354bf6f29e6b400e1bdfed1a2f9781996a6abc593d22bd5bb2096a90696bc (Nat.shiftLeft
  0xea925a4fca9c3b12f3489d8444bed074f4726 288)) 288)) 576)))), (195, (mkQ true (Nat.add (Nat.add
  0x7fbd93e2df41d3f6af6d0cfb81c7deba4543d946a5645114eb5fb4f47b3d218691eaeb3d (Nat.shiftLeft
  0x7e18c7a98b411fd55d5fddad8384707a059e03b269180ed3101dc2e03a1b3337c949dc7 288)) (Nat.shiftLeft (
  Nat.add 0x3d79264b4c9538c9b288ce25ef5263c2958efec01a39e5913f1460b905440f23caae87d3 (Nat.shiftLeft
  (Nat.add 0xfc95975626bcd425d287250bb807161a9db3cd17f27237f3c66cf6486915ea48b4aacbd (Nat.shiftLeft
  0x266e1ab9227641ca181a3b1f9c0754533ead54f20 288)) 288)) 576)) (Nat.add (Nat.add
  0x776de2cf4678ff57d42c8f6d2e3104c8142f0f4ac2c5f5d7a76e654e1b3497fd0000000 (Nat.shiftLeft
  0x807cef33cdc6a2bbbbe5067fd85fff83547360e781bc5407949900248b5e2605fb8c6ab4 288)) (Nat.shiftLeft (
  Nat.add 0xdd5ae4fa7bbc0aaed47d5fc70a53fb3772a252ee4379a4bd4f2989bce15293c3a10926a6 (Nat.shiftLeft
  (Nat.add 0xebe8fd97c02354bf6f29e6b400e1bdfed1a2f9781996a6abc593d22bd5bb2096a90696bc (Nat.shiftLeft
  0xea925a4fca9c3b12f3489d8444bed074f4726 288)) 288)) 576)))), (197, (mkQ true (Nat.add (Nat.add
  0xb21dae64aeb91761917e5a65047603b3888d9251bab0fa47ba13446d9bbc01e984e1065d (Nat.shiftLeft
  0x35a346d38ff1a459f7b105bd6ec6f41181afb231f00f3b955f3e4381f38877b10f47a7ed 288)) (Nat.shiftLeft (
  Nat.add 0x6d9ef448819f0f232533d386d317d91783c7ab29a4981f18f7d1d4779e06ac9043593244 (Nat.shiftLeft
  (Nat.add 0x4120c1e5d936799798df67c90fa58e77c133e2afc2cd2aa40adabfba09a3fc6a5ecd08ac (Nat.shiftLeft
  0xdce4e041a629efd742dcaf75f9eea4f30804b06f0 288)) 288)) 576)) (Nat.add (Nat.add
  0x84aa4adc18c0b9f96e49bd9a43cdea2fd0c9d698eb9bbb9a6c8a4ff50d100defe2000000 (Nat.shiftLeft
  0x104e1580609c25b5556f240fe73bffb214c81c90b115b484bcdfa016d71ad7c3bd37c2b0 288)) (Nat.shiftLeft (
  Nat.add 0xa58cf1c8d5586ad44ce5bdc66747d02a7a573d4ea2c06f65179f6160cd39c5a44a5b828 (Nat.shiftLeft (
  Nat.add 0x53719e7ed81614f7a57a3030808d16bf4305dbeb0ffe282b5b7c635b6594f45e29a41e36 (Nat.shiftLeft
  0x929b7871dea1a4ebd80d6272aaf7424918c78 288)) 288)) 576)))), (199, (mkQ true (Nat.add (Nat.add
  0xdfbf2d1e33168f56bbed11575e22f69c5b4f46c4a0d42202bfd71629fbb628f56f2e8a81 (Nat.shiftLeft
  0x55049cc0b973deb0050c8e58d57f9a2dbb7c4aec67aa440a46417d67a9c2f3331e2f828d 288)) (Nat.shiftLeft (
  Nat.add 0xac97ad49650cc7981bb2c52b873c0733060fe616bca01456cffee71cf136db46e1b33e33 (Nat.shiftLeft
  (Nat.add 0x4dc311644b118fdf0927eb6da78ffc95a83b2fb9c7d22eaccc1a0c80fc711c8147fd590c (Nat.shiftLeft
  0x3bd4f020ab2949742a47bd3003bf271f900cc3b9a 288)) 288)) 576)) (Nat.add (Nat.add
  0x80eedbc59e8cf1feafa8591eda5c620990285e1e95858bebaf4edcca9c36692ffa000000 (Nat.shiftLeft
  0xd00f9de679b8d457777ca0cffb0bfff06a8e6c1cf0378a80f2932004916bc4c0bf718d56 288)) (Nat.shiftLeft (
  Nat.add 0x9bab5c9f4f778155da8fabf8e14a7f66ee544a5dc86f3497a9e531379c2a5278742124d4 (Nat.shiftLeft
  (Nat.add 0xdd7d1fb2f8046a97ede53cd6801c37bfda345f2f0332d4d578b27a457ab76412d520d2d7 (Nat.shiftLeft
  0x1d524b49f95387625e6913b08897da0e9e8e4 288)) 288)) 576)))), (201, (mkQ true (Nat.add (Nat.add
  0x6c896251256f002fc60c32823b37f9e551a5fe2c3863393f5ccbb1984c6e1b8b3340a637 (Nat.shiftLeft
  0x2c6fb4d0087a679bece460c78c9e7a3af392d600af9cfa5d1f69768fac8d97bdbf51f140 288)) (Nat.shiftLeft (
  Nat.add 0xbc7a7294771cc6aca418cc4266cc32c9a6f0e678b90dae6fad71b91b3cf50cf2139307da (Nat.shiftLeft
  (Nat.add 0x851c013fdfc60befd4c49fe478fd20a502fa45bc451748a6bab495296594666668133302 (Nat.shiftLeft
  0x5a9fb33b6197fdef98d91fd071c2baf6c290395553 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (231, (mkQ false (Nat.add (Nat.add
  0x7b7c1e9747b99d613b72b75d2dfc1a52e139405b4a4629dd600da7e60b71061e3bba733 (Nat.shiftLeft
  0x12120122b7c3e0dafd5468d1d63b7c6cbbd562e35762778d933e02ede9341905611d92 288)) (Nat.shiftLeft (
  Nat.add 0xa3525f0ea16541bcc9306ecb0abcd44d59c32c748c5768f3d722af82d4bb530d26da56be (Nat.shiftLeft
  (Nat.add 0xba539c47e340c2985f5d03f1434df22e9ae91ca5204d2fcb73ae9dbe6d2b9ba2498d9a25 (Nat.shiftLeft
  0x51affdfc4f12f741b5d1a837cff75cc42fd2b155 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (233, (mkQ true (Nat.add (Nat.add
  0x32a6cd43cae7daff7673ddc87a1fa753e831c903ae2e4ba87280936adad50dc71eff3465 (Nat.shiftLeft
  0xe1143f14cec15b2ca72f5e8c1d8de30321b413925f08f9e8981adddf4ca1589500112b8a 288)) (Nat.shiftLeft (
  Nat.add 0xe8143300a2229e4ce340e8b4ef4c5de0387eb63a49f072ed20f617c14ff7c877a3fbb748 (Nat.shiftLeft
  (Nat.add 0x22fcb688407511e2a60f9897d20b6045686c09a611e26825ff2899c5318b4be0359522c1 (Nat.shiftLeft
  0xd63474ed0244dce2904aba30cd54845f358ad734f 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (235, (mkQ true (Nat.add (Nat.add
  0x67031cc4d66c1e5aa3810888d259d21a58458d6f12a559133b203c85d6aff00381e846b (Nat.shiftLeft
  0xccb38ca15ae5a46b4ae9fbd4fcd3672c8d299100235660e4ca7265c35aea0826622564e6 288)) (Nat.shiftLeft (
  Nat.add 0x54eae791279654c9a72acd295f97f266da696270719d6aa7eb25f58e51c3b4b115d26aa0 (Nat.shiftLeft
  (Nat.add 0x21c5a68890d5063bbbf62a6117c77e4db1496c3534ef01f6df82f0512aab69b5948be809 (Nat.shiftLeft
  0x2c713dbbe2687cda4b66babb092da491a637c424da 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (237, (mkQ true (Nat.add (Nat.add
  0x8906dec98d5887552d13980aff5fa95c0c2438b62cfd31d023740fae021ca7fafe1c8439 (Nat.shiftLeft
  0xcc6f1eef94c99fc0c64c88e80c82b5fea5c51a073fa8a846177ddeab615f636e6a5e5b16 288)) (Nat.shiftLeft (
  Nat.add 0xd47ddb664a0a6690c70c074e80ca6c50d98b823ba3d3be61425fc676a529fc700177dc18 (Nat.shiftLeft
  (Nat.add 0xe66920e29a6c66b4c3f8c9ffbc9fa717b6781b5098d8b5ef4c7df0e420da88bcc0d7ad32 (Nat.shiftLeft
  0x290e55edad0d428c9c0e8b75ae2038b8bcfeeb55 288)) 288)) 576)) (Nat.add (Nat.add
  0x3392be4f0c3860cc464356d92424f403d34358d9089bd1917952beb771af5d4664000000 (Nat.shiftLeft
  0x866ca58f63e38822fc9840533137fff9c438f80b93496a99faa14001d3c4b519e62d6bbc 288)) (Nat.shiftLeft (
  Nat.add 0xd7de250c862fcd558a9fde638d50ffc2c5bb50f2502c7b6fdd8ee07ca4ddba9694da0ebb (Nat.shiftLeft
  (Nat.add 0xbefed97ac99b5dd65f287ebc333e7cb32414f2df9ae121eefd1430e8977c8e6deed9edef (Nat.shiftLeft
  0xbba8483fd549c8dbf5d3b1369d657390c38e 288)) 288)) 576))))])]

def sjsuTsp_454 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 3, 5), [(121, (mkQ false (
  Nat.add (Nat.add 0xdcdfbb5f8e545ede2d774ff62e012c9df9fd355308513c78351488aa6003e304991f1cb (
  Nat.shiftLeft (Nat.add 0x7e4aa8b94a8e8645d3c3b3084e7a7d6c34b014a4a7f49bf86c04e84ec9bf08ba5f77f4e5
  (Nat.shiftLeft 0x36d01a6dd453eaeff66bd94cb47a6f9b7254aba48daaaeae2e59393aeff82801119ffb8 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xf2f1aca5fed45fd518435906cecce41fef6afa0ee2797f099415093a4799cd42ae10144e (Nat.shiftLeft (Nat.add
  0x7b4f199b7baf33e80145a8f4b93f1803f3bcb4b4deff159ba5b432a2a0157c4e5e0eeab7 (Nat.shiftLeft
  0x1f23750c8e 288)) 288)) 864)) (Nat.add (Nat.add
  0x2c0ab9f6e3d650c8a0a54193c0abe4900b1433cccfc82408055fe4e56ef8cbb5da00000 (Nat.shiftLeft (Nat.add
  0xc14e4f391ea8f420a93fef9630bacd98e1bb98c64a62c983642d936b3977e07f50598251 (Nat.shiftLeft
  0x8fcd3ef65ac138ea1ba4e4b56d18c614248ab036b6cf5fed35784f0c43bd60beae490378 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9b804f6d73c7ca2bb55fc23dd6325727fb1beb1ac4b451a3d9fb8f269a67858d95ddccc8
  (Nat.shiftLeft (Nat.add 0x3cc87ff2936fcac0b4eb54f275866d50c4a39a418d6b3eeb2ccdd83fcfdad2ecc425f997
  (Nat.shiftLeft 0x14100 288)) 288)) 864)))), (123, (mkQ false (Nat.add (Nat.add
  0xe52bfee757bffe64888017e913d6eaefe108d8a519a224f701b14c6faeef60c7bc210d23 (Nat.shiftLeft (Nat.add
  0xe2f773fa7761e44134df22e984a0033f159aaeafe699d392c12d78253d69a6083d0ca508 (Nat.shiftLeft
  0xcd7d1670cd3de5cac83160892898dba843869cdadbd945a5448de1aae1c2d7dc12ebc63a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe6393839e6fa21c5346de6c579c785ad0b653ad0aac92a636f5bfee0aa8702f7f1bbbaad
  (Nat.shiftLeft (Nat.add 0x799eac2ebf10c13593e69342ecbb8f9d8a85c619d67f2c565dfbc26f935f8ba1cb7712ea
  (Nat.shiftLeft 0x1c2a6865bd66f 288)) 288)) 864)) (Nat.add (Nat.add
  0xdc31801e11f1d9ce819ba8cdcb1d481d586293b83a3cffbca8f8eea11f6b4ab7c9d00000 (Nat.shiftLeft (Nat.add
  0xf817b539ed3e01de9a8bf6d67c07f91f8d7ffe0dcd96fce3c9a27463a6d58b69954393e3 (Nat.shiftLeft
  0x8a0b5bb9c8ddf9c6bec92f77acbdcb969b4c1aca2824990fc55c7e78b0ac98c3c020bce7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5220f51bd5624a5ae7649c7bf873644e07947e2d1e1da88397943e9f7b5e875571407ad3
  (Nat.shiftLeft (Nat.add 0x32c02f9cf9f7003cd94531f87698711809b5cd05216a4e14314679e53a9e7a05705b2d91
  (Nat.shiftLeft 0x187d8ca 288)) 288)) 864)))), (125, (mkQ false (Nat.add (Nat.add
  0xf8409a876401353612ff66dbc7b22a7da65ef52f40f780255eed23ba6034a05e8c385e37 (Nat.shiftLeft (Nat.add
  0xf7319b4ff4193b97dae5b59e0990abf991c974ce77614263784a996a6faabe5329e7b85a (Nat.shiftLeft
  0x852d307f868072e06385a84dbd4af930b0f96eab58f18b4f6cbe232d630bcb7ec79cda5a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x97fefa94cdbb9d229e9baeddff7e5898f10aa64214cd1f0b3677c1990ccce36cf26306d6
  (Nat.shiftLeft (Nat.add 0xa8a0ab573004cd12d9d3390667cdebcdd18b0cad18c1c30df273a9175a93299f72048a3a
  (Nat.shiftLeft 0x48233a23e886c 288)) 288)) 864)) (Nat.add (Nat.add
  0xa67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb78880000 (Nat.shiftLeft (Nat.add
  0xec3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9 (Nat.shiftLeft
  0xd91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310
  (Nat.shiftLeft (Nat.add 0x7ee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb
  (Nat.shiftLeft 0x3d39df9 288)) 288)) 864)))), (127, (mkQ false (Nat.add (Nat.add
  0x3f470ef71a7f0b0fbefb3b625858b0013c2cc68d6194fb40cd6f7fd7737f695961848dab (Nat.shiftLeft (Nat.add
  0xb581e824d9f8102d7feadddbd3a6271c115c3bc944be0efc38f60b9c4de6ddb4fb23839d (Nat.shiftLeft
  0x64e32a2c257c6e36f4ae4bf02db74ff5ea7be899c85ec3ff3fbd90331fb6663db5d14aed 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe8cfb48edb4aabdc8badea9d9a36f2f9c3df02a595125b7e623d8f66f534ecb4fd418c61
  (Nat.shiftLeft (Nat.add 0x6cd5d186bcb2ca20e6e49536ed76b458111030774aa9bbea57f9ebbc81c374d7d2ab2e44
  (Nat.shiftLeft 0x7971d776a52e 288)) 288)) 864)) (Nat.add (Nat.add
  0x699ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de220000 (Nat.shiftLeft (Nat.add
  0xfb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e (Nat.shiftLeft
  0x364719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc4
  (Nat.shiftLeft (Nat.add 0x5fb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7a
  (Nat.shiftLeft 0xf4e77e 288)) 288)) 864)))), (129, (mkQ false (Nat.add (Nat.add
  0xa438c26d145752f3cae23f55eadb0aa2e303440e0af054bc051ebd8c8bc131f1ebe35eab (Nat.shiftLeft (Nat.add
  0xd119d1f365a55dce1b846d375293365f2084a8c305666f8570f0b832e69fe42855b4696a (Nat.shiftLeft
  0x45647571e34a38f300f9b76d53101a60710ff29a7bbfc56ab16b4b9bec0e2eb8613283e0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xfae0cd216b6c54e1f6156fa4ae6859e8eeced5ff1e44447b09d70bc0f8d4873dd57646c3
  (Nat.shiftLeft (Nat.add 0x715d31302e8d2837e53d03c10ed3f37482198fa4da3c78c2cdbf670d36c355455e8ff531
  (Nat.shiftLeft 0x826ece66c7da 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (131, (mkQ false (Nat.add (Nat.add
  0x73c701163118a8ba88eb061c4f0e6fe05bce1571dc33be754ec28d2fd0fc37f6d85809c7 (Nat.shiftLeft (Nat.add
  0x6cac40ca77c9b6c937cb8733cf7e45e85da00f7fbcf9fe12144def1d118bd9664d3a4e10 (Nat.shiftLeft
  0x257962cc69bd2348a6c30024fb992b2de338ba00e43260148bd5901cfcde8af9b4534567 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x427233ce1c330ff11c264c44669c870f4ca825e92d0d52d245b8ff6e9ebc51a2bbf710cb
  (Nat.shiftLeft (Nat.add 0x9b232e30a66b3edd6b826a1bf44eaa5443107265d4abd219eee9f15e84c277af012a3b3
  (Nat.shiftLeft 0x5ac338ff9d2 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (157, (mkQ false (Nat.add (Nat.add
  0x54f1178b1fba1ecdbfa61c3b4b7751c198c112686e034f1446e68f96e982313e76ff955 (Nat.shiftLeft (Nat.add
  0xbbc40f3d077fd06f7137a98b409bf58e7257190fa706b9e67c1e11c9406598105c93c0aa (Nat.shiftLeft
  0x99c84c9f94314f9c9d700188ee07e50c3bd5bac7c510d842cf0ab576201e3eb025f74ca1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdbdda6fa7a20b752d1e4307ae15dd6f52542e1e38d894a791f4321fbef5f3fc462343ec9
  (Nat.shiftLeft (Nat.add 0xad454f9222138800ccfc25b6955ac470d532f53a3b1c07437d753dbeaeb973cbb760206b
  (Nat.shiftLeft 0x227defcd62bde 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (159, (mkQ false (Nat.add (Nat.add
  0x2265be83e242e553d8cbd22afe85d09df733984b2cfa36a6eced2a29323e42711d1d9dfb (Nat.shiftLeft (Nat.add
  0xe06165d48ba458ad81aa508e6456bd4a234aa29654305bd56bc02acaa0758de686756eaf (Nat.shiftLeft
  0x61e1ee05410be7679d53f096416eb0ee4ee9ef967d9ca7c1a3e1ed30daf0831b13e9afb1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x1cc73409244bfd10a9a1f22a98a2aa264df8c3f2163b23f926b755fda7cc2a804cb70065
  (Nat.shiftLeft (Nat.add 0x269b82c41a1c8241a3a2bf56553e494f67ff536156e6a37ea60da2cf9f095adc0e1fbfe6
  (Nat.shiftLeft 0xa26976478b45 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (161, (mkQ false (Nat.add (Nat.add
  0xf81611fc80e3e0a7eff6c594fcd23260f2c745bea1dc369fd371f6ca120a41513abc51a7 (Nat.shiftLeft (Nat.add
  0x5f8dd5b8b614fb59f3b2ce08336136f4f849082b4d5a44120666427a6504a5a6355805ed (Nat.shiftLeft
  0x1d1a934dc91da05af053da4568c810ed60c6a4062216daaea24370596344ebfc27ff1fbc 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc593b988b59ac230b755c19837ca44ad10517a8ad33db0a699f6e2dced388aa0a01abd01
  (Nat.shiftLeft (Nat.add 0xb0b7b94879c65aad93558d23b689fdc67d8e659122d967c49047d95da65e7619be19f2d9
  (Nat.shiftLeft 0x8586be1c1c90 288)) 288)) 864)) (Nat.add (Nat.add
  0xcb02799b1a7f4ae3ece1620a4a27dd34aad1ba9602e9732fd53fa5880e5ef6ef96e40000 (Nat.shiftLeft (Nat.add
  0xcc6795dc7f0fe67e5486ff8ab966cc74c713331a4a478ca4fd481f6b61f113c547769431 (Nat.shiftLeft
  0xc6e6f7c94a0b1949eff07592c8a316fabaf70156e8683ada6377d31fa26f07a36334d63e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xddb4d90e3111b6eaf1f83b0632d291d0b394398241817ba02dfa9cbb2c9186c445a99fbd
  (Nat.shiftLeft (Nat.add 0xb5bccf2e3fb2c0030add0f4c6c546c0e007c4a4041abb71a9c1052e50fbb1fb378d15be0
  (Nat.shiftLeft 0x1397a3 288)) 288)) 864)))), (163, (mkQ false (Nat.add (Nat.add
  0x4d51f0394305c623c1c78157ebbd58350e77df1ce37fab486a67eea5b90e03d9cbaf07e7 (Nat.shiftLeft (Nat.add
  0x6aeb4deec0894a3f3bf0723ea0fa52b5c7cac74705ad4c8ef7c04ea36dea1380ef725306 (Nat.shiftLeft
  0x4f1365fb0872f10ef8780dd05c209691f465f76dfb36e9e4cfdedffebdabbfe57f774a52 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf842926e9dfe0210e9a74a81de70549858f9c6246eb8fb501adc9944bef6b705f420c337
  (Nat.shiftLeft (Nat.add 0xb44ed8dfed6dd86e28e14785a3d6ea9c858b44bf96684fe7cc8f3e775979fab846683e83
  (Nat.shiftLeft 0x6ad6f851e83bf 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (165, (mkQ false (Nat.add (Nat.add
  0xd9bb2258f0027de288b6246c47eef1abfb07160ad0f87e3c059b21617f4f5f7afa355edb (Nat.shiftLeft (Nat.add
  0x3db653802d298ea3a60d262b2173df92e1241c9cc71ae7dbed9fea38f1d1c39e1f38803e (Nat.shiftLeft
  0x7b9edf927b56d38fe31bd73429fc2f1d8cc0f93d77a1a9c70987bc97c05be672ef5ad980 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x47f5762ba18ec4ebed5e6dbc4cff82c7fa38e5473a34ef735d805bc3d3e1a703968fcada
  (Nat.shiftLeft (Nat.add 0x5184ecf165393ecc1f37ffa36eb1bef6ee954a14922b4be94fac993c13c52fd82ff407d
  (Nat.shiftLeft 0x2ce22fa95f73b 288)) 288)) 864)) (Nat.add (Nat.add
  0xa67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb78880000 (Nat.shiftLeft (Nat.add
  0xec3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9 (Nat.shiftLeft
  0xd91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310
  (Nat.shiftLeft (Nat.add 0x7ee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb
  (Nat.shiftLeft 0x3d39df9 288)) 288)) 864)))), (167, (mkQ false (Nat.add (Nat.add
  0x148be643284886e0d934ade8b4628b8cc89b5567919752f76628a57f22872ac6659ea7fd (Nat.shiftLeft (Nat.add
  0x63a8319842edb9722f90763b933ac86da475ef12f362dbe0cb6f97824026dedd23412026 (Nat.shiftLeft
  0x6074c28dab072c9ff1851344d76347d84d045d65b43cb3a63df0d64566288658a5c76833 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd2db095bcecc2b688b4bc525cc75bec271e4682b465526a5e20cdb9887e31f93216d75e9
  (Nat.shiftLeft (Nat.add 0x8f39a10ee5d41573d898815a59750bccc4d9ae01a32adbfc6771a0af860fcfd80b5a7b16
  (Nat.shiftLeft 0x945a36f4d006 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (193, (mkQ false (Nat.add (Nat.add
  0x148be643284886e0d934ade8b4628b8cc89b5567919752f76628a57f22872ac6659ea7fd (Nat.shiftLeft (Nat.add
  0x63a8319842edb9722f90763b933ac86da475ef12f362dbe0cb6f97824026dedd23412026 (Nat.shiftLeft
  0x6074c28dab072c9ff1851344d76347d84d045d65b43cb3a63df0d64566288658a5c76833 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd2db095bcecc2b688b4bc525cc75bec271e4682b465526a5e20cdb9887e31f93216d75e9
  (Nat.shiftLeft (Nat.add 0x8f39a10ee5d41573d898815a59750bccc4d9ae01a32adbfc6771a0af860fcfd80b5a7b16
  (Nat.shiftLeft 0x945a36f4d006 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (195, (mkQ false (Nat.add (Nat.add
  0xd9bb2258f0027de288b6246c47eef1abfb07160ad0f87e3c059b21617f4f5f7afa355edb (Nat.shiftLeft (Nat.add
  0x3db653802d298ea3a60d262b2173df92e1241c9cc71ae7dbed9fea38f1d1c39e1f38803e (Nat.shiftLeft
  0x7b9edf927b56d38fe31bd73429fc2f1d8cc0f93d77a1a9c70987bc97c05be672ef5ad980 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x47f5762ba18ec4ebed5e6dbc4cff82c7fa38e5473a34ef735d805bc3d3e1a703968fcada
  (Nat.shiftLeft (Nat.add 0x5184ecf165393ecc1f37ffa36eb1bef6ee954a14922b4be94fac993c13c52fd82ff407d
  (Nat.shiftLeft 0x2ce22fa95f73b 288)) 288)) 864)) (Nat.add (Nat.add
  0xa67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb78880000 (Nat.shiftLeft (Nat.add
  0xec3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9 (Nat.shiftLeft
  0xd91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310
  (Nat.shiftLeft (Nat.add 0x7ee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb
  (Nat.shiftLeft 0x3d39df9 288)) 288)) 864)))), (197, (mkQ false (Nat.add (Nat.add
  0x4d51f0394305c623c1c78157ebbd58350e77df1ce37fab486a67eea5b90e03d9cbaf07e7 (Nat.shiftLeft (Nat.add
  0x6aeb4deec0894a3f3bf0723ea0fa52b5c7cac74705ad4c8ef7c04ea36dea1380ef725306 (Nat.shiftLeft
  0x4f1365fb0872f10ef8780dd05c209691f465f76dfb36e9e4cfdedffebdabbfe57f774a52 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf842926e9dfe0210e9a74a81de70549858f9c6246eb8fb501adc9944bef6b705f420c337
  (Nat.shiftLeft (Nat.add 0xb44ed8dfed6dd86e28e14785a3d6ea9c858b44bf96684fe7cc8f3e775979fab846683e83
  (Nat.shiftLeft 0x6ad6f851e83bf 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (199, (mkQ false (Nat.add (Nat.add
  0xf81611fc80e3e0a7eff6c594fcd23260f2c745bea1dc369fd371f6ca120a41513abc51a7 (Nat.shiftLeft (Nat.add
  0x5f8dd5b8b614fb59f3b2ce08336136f4f849082b4d5a44120666427a6504a5a6355805ed (Nat.shiftLeft
  0x1d1a934dc91da05af053da4568c810ed60c6a4062216daaea24370596344ebfc27ff1fbc 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc593b988b59ac230b755c19837ca44ad10517a8ad33db0a699f6e2dced388aa0a01abd01
  (Nat.shiftLeft (Nat.add 0xb0b7b94879c65aad93558d23b689fdc67d8e659122d967c49047d95da65e7619be19f2d9
  (Nat.shiftLeft 0x8586be1c1c90 288)) 288)) 864)) (Nat.add (Nat.add
  0xcb02799b1a7f4ae3ece1620a4a27dd34aad1ba9602e9732fd53fa5880e5ef6ef96e40000 (Nat.shiftLeft (Nat.add
  0xcc6795dc7f0fe67e5486ff8ab966cc74c713331a4a478ca4fd481f6b61f113c547769431 (Nat.shiftLeft
  0xc6e6f7c94a0b1949eff07592c8a316fabaf70156e8683ada6377d31fa26f07a36334d63e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xddb4d90e3111b6eaf1f83b0632d291d0b394398241817ba02dfa9cbb2c9186c445a99fbd
  (Nat.shiftLeft (Nat.add 0xb5bccf2e3fb2c0030add0f4c6c546c0e007c4a4041abb71a9c1052e50fbb1fb378d15be0
  (Nat.shiftLeft 0x1397a3 288)) 288)) 864)))), (201, (mkQ false (Nat.add (Nat.add
  0x2265be83e242e553d8cbd22afe85d09df733984b2cfa36a6eced2a29323e42711d1d9dfb (Nat.shiftLeft (Nat.add
  0xe06165d48ba458ad81aa508e6456bd4a234aa29654305bd56bc02acaa0758de686756eaf (Nat.shiftLeft
  0x61e1ee05410be7679d53f096416eb0ee4ee9ef967d9ca7c1a3e1ed30daf0831b13e9afb1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x1cc73409244bfd10a9a1f22a98a2aa264df8c3f2163b23f926b755fda7cc2a804cb70065
  (Nat.shiftLeft (Nat.add 0x269b82c41a1c8241a3a2bf56553e494f67ff536156e6a37ea60da2cf9f095adc0e1fbfe6
  (Nat.shiftLeft 0xa26976478b45 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (203, (mkQ false (Nat.add (Nat.add
  0x54f1178b1fba1ecdbfa61c3b4b7751c198c112686e034f1446e68f96e982313e76ff955 (Nat.shiftLeft (Nat.add
  0xbbc40f3d077fd06f7137a98b409bf58e7257190fa706b9e67c1e11c9406598105c93c0aa (Nat.shiftLeft
  0x99c84c9f94314f9c9d700188ee07e50c3bd5bac7c510d842cf0ab576201e3eb025f74ca1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdbdda6fa7a20b752d1e4307ae15dd6f52542e1e38d894a791f4321fbef5f3fc462343ec9
  (Nat.shiftLeft (Nat.add 0xad454f9222138800ccfc25b6955ac470d532f53a3b1c07437d753dbeaeb973cbb760206b
  (Nat.shiftLeft 0x227defcd62bde 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (229, (mkQ false (Nat.add (Nat.add
  0x73c701163118a8ba88eb061c4f0e6fe05bce1571dc33be754ec28d2fd0fc37f6d85809c7 (Nat.shiftLeft (Nat.add
  0x6cac40ca77c9b6c937cb8733cf7e45e85da00f7fbcf9fe12144def1d118bd9664d3a4e10 (Nat.shiftLeft
  0x257962cc69bd2348a6c30024fb992b2de338ba00e43260148bd5901cfcde8af9b4534567 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x427233ce1c330ff11c264c44669c870f4ca825e92d0d52d245b8ff6e9ebc51a2bbf710cb
  (Nat.shiftLeft (Nat.add 0x9b232e30a66b3edd6b826a1bf44eaa5443107265d4abd219eee9f15e84c277af012a3b3
  (Nat.shiftLeft 0x5ac338ff9d2 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (231, (mkQ false (Nat.add (Nat.add
  0xa438c26d145752f3cae23f55eadb0aa2e303440e0af054bc051ebd8c8bc131f1ebe35eab (Nat.shiftLeft (Nat.add
  0xd119d1f365a55dce1b846d375293365f2084a8c305666f8570f0b832e69fe42855b4696a (Nat.shiftLeft
  0x45647571e34a38f300f9b76d53101a60710ff29a7bbfc56ab16b4b9bec0e2eb8613283e0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xfae0cd216b6c54e1f6156fa4ae6859e8eeced5ff1e44447b09d70bc0f8d4873dd57646c3
  (Nat.shiftLeft (Nat.add 0x715d31302e8d2837e53d03c10ed3f37482198fa4da3c78c2cdbf670d36c355455e8ff531
  (Nat.shiftLeft 0x826ece66c7da 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (233, (mkQ false (Nat.add (Nat.add
  0x3f470ef71a7f0b0fbefb3b625858b0013c2cc68d6194fb40cd6f7fd7737f695961848dab (Nat.shiftLeft (Nat.add
  0xb581e824d9f8102d7feadddbd3a6271c115c3bc944be0efc38f60b9c4de6ddb4fb23839d (Nat.shiftLeft
  0x64e32a2c257c6e36f4ae4bf02db74ff5ea7be899c85ec3ff3fbd90331fb6663db5d14aed 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe8cfb48edb4aabdc8badea9d9a36f2f9c3df02a595125b7e623d8f66f534ecb4fd418c61
  (Nat.shiftLeft (Nat.add 0x6cd5d186bcb2ca20e6e49536ed76b458111030774aa9bbea57f9ebbc81c374d7d2ab2e44
  (Nat.shiftLeft 0x7971d776a52e 288)) 288)) 864)) (Nat.add (Nat.add
  0x699ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de220000 (Nat.shiftLeft (Nat.add
  0xfb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e (Nat.shiftLeft
  0x364719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc4
  (Nat.shiftLeft (Nat.add 0x5fb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7a
  (Nat.shiftLeft 0xf4e77e 288)) 288)) 864)))), (235, (mkQ false (Nat.add (Nat.add
  0xf8409a876401353612ff66dbc7b22a7da65ef52f40f780255eed23ba6034a05e8c385e37 (Nat.shiftLeft (Nat.add
  0xf7319b4ff4193b97dae5b59e0990abf991c974ce77614263784a996a6faabe5329e7b85a (Nat.shiftLeft
  0x852d307f868072e06385a84dbd4af930b0f96eab58f18b4f6cbe232d630bcb7ec79cda5a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x97fefa94cdbb9d229e9baeddff7e5898f10aa64214cd1f0b3677c1990ccce36cf26306d6
  (Nat.shiftLeft (Nat.add 0xa8a0ab573004cd12d9d3390667cdebcdd18b0cad18c1c30df273a9175a93299f72048a3a
  (Nat.shiftLeft 0x48233a23e886c 288)) 288)) 864)) (Nat.add (Nat.add
  0xa67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb78880000 (Nat.shiftLeft (Nat.add
  0xec3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9 (Nat.shiftLeft
  0xd91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310
  (Nat.shiftLeft (Nat.add 0x7ee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb
  (Nat.shiftLeft 0x3d39df9 288)) 288)) 864)))), (237, (mkQ false (Nat.add (Nat.add
  0xe52bfee757bffe64888017e913d6eaefe108d8a519a224f701b14c6faeef60c7bc210d23 (Nat.shiftLeft (Nat.add
  0xe2f773fa7761e44134df22e984a0033f159aaeafe699d392c12d78253d69a6083d0ca508 (Nat.shiftLeft
  0xcd7d1670cd3de5cac83160892898dba843869cdadbd945a5448de1aae1c2d7dc12ebc63a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe6393839e6fa21c5346de6c579c785ad0b653ad0aac92a636f5bfee0aa8702f7f1bbbaad
  (Nat.shiftLeft (Nat.add 0x799eac2ebf10c13593e69342ecbb8f9d8a85c619d67f2c565dfbc26f935f8ba1cb7712ea
  (Nat.shiftLeft 0x1c2a6865bd66f 288)) 288)) 864)) (Nat.add (Nat.add
  0xdc31801e11f1d9ce819ba8cdcb1d481d586293b83a3cffbca8f8eea11f6b4ab7c9d00000 (Nat.shiftLeft (Nat.add
  0xf817b539ed3e01de9a8bf6d67c07f91f8d7ffe0dcd96fce3c9a27463a6d58b69954393e3 (Nat.shiftLeft
  0x8a0b5bb9c8ddf9c6bec92f77acbdcb969b4c1aca2824990fc55c7e78b0ac98c3c020bce7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5220f51bd5624a5ae7649c7bf873644e07947e2d1e1da88397943e9f7b5e875571407ad3
  (Nat.shiftLeft (Nat.add 0x32c02f9cf9f7003cd94531f87698711809b5cd05216a4e14314679e53a9e7a05705b2d91
  (Nat.shiftLeft 0x187d8ca 288)) 288)) 864)))), (239, (mkQ false (Nat.add (Nat.add
  0xdcdfbb5f8e545ede2d774ff62e012c9df9fd355308513c78351488aa6003e304991f1cb (Nat.shiftLeft (Nat.add
  0x7e4aa8b94a8e8645d3c3b3084e7a7d6c34b014a4a7f49bf86c04e84ec9bf08ba5f77f4e5 (Nat.shiftLeft
  0x36d01a6dd453eaeff66bd94cb47a6f9b7254aba48daaaeae2e59393aeff82801119ffb8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf2f1aca5fed45fd518435906cecce41fef6afa0ee2797f099415093a4799cd42ae10144e
  (Nat.shiftLeft (Nat.add 0x7b4f199b7baf33e80145a8f4b93f1803f3bcb4b4deff159ba5b432a2a0157c4e5e0eeab7
  (Nat.shiftLeft 0x1f23750c8e 288)) 288)) 864)) (Nat.add (Nat.add
  0x2c0ab9f6e3d650c8a0a54193c0abe4900b1433cccfc82408055fe4e56ef8cbb5da00000 (Nat.shiftLeft (Nat.add
  0xc14e4f391ea8f420a93fef9630bacd98e1bb98c64a62c983642d936b3977e07f50598251 (Nat.shiftLeft
  0x8fcd3ef65ac138ea1ba4e4b56d18c614248ab036b6cf5fed35784f0c43bd60beae490378 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9b804f6d73c7ca2bb55fc23dd6325727fb1beb1ac4b451a3d9fb8f269a67858d95ddccc8
  (Nat.shiftLeft (Nat.add 0x3cc87ff2936fcac0b4eb54f275866d50c4a39a418d6b3eeb2ccdd83fcfdad2ecc425f997
  (Nat.shiftLeft 0x14100 288)) 288)) 864))))])]

def sjsuTsp_455 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 3, 7), [(119, (mkQ false (
  Nat.add (Nat.add 0x8c001f3a63754ac01512c81bd808ae144eb463f601a1e0cda49f13a4959b6732f3c3e099 (
  Nat.shiftLeft (Nat.add 0xdc6eeb5f3d4e15e07e5b2f1370232e06a45afa1980de4f4c39f595ade56c75f0b91833c6
  (Nat.shiftLeft 0x24a95f2bb546e1a9c676322ab55fb3cf19ffb831eae69ec27712d278d8e19bf118f0bcc8 288))
  288)) (Nat.shiftLeft (Nat.add
  0xeb048ad45895396a1cc8708625b65aad6bd65adf60e1c0f554b771a5736ca0766ab720c6 (Nat.shiftLeft (Nat.add
  0x2b2bc7b25f07597d5c10e940855dd3142b82fe733991b5e9b9ffd498b4c1579833c644ca (Nat.shiftLeft
  0x1a2159e74d2f776c18dc23313140923f8aa8c7464b2f0d7604f42b 288)) 288)) 864)) (Nat.add (Nat.add
  0x40dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd200000 (Nat.shiftLeft (Nat.add
  0xf05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa6 (Nat.shiftLeft
  0x80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d86 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98b
  (Nat.shiftLeft (Nat.add 0x2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff76
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550c 288)) 288)) 864)))), (121, (mkQ
  false (Nat.add (Nat.add 0xeebcd177fdd40164fcac16ca0e221664b002c24bc242917d83cd61a4c91450b2ceff29e9
  (Nat.shiftLeft (Nat.add 0x2f50982bf2c81aced1b2d383fd70952a5bdfb34b0264e21f2406f57f26eecdf86f16edba
  (Nat.shiftLeft 0x3261d9a6ae78f7787eba5c3c8474da17a3ffb428013be14f598983ae69c5a0b2ee5a66ff 288))
  288)) (Nat.shiftLeft (Nat.add
  0x67c5b8ab756e2e0f7240740e232f3c543ed8522a170f75ee3cd32e34202a336be909c117 (Nat.shiftLeft (Nat.add
  0xc5633298b6d43c330f07e589f9f3e516ad9f6fca8596dfccd2f1583ce904452bc5d911b0 (Nat.shiftLeft
  0x911e3f7f40b6846e5ba9f03b298a02fbf3441bc4e0f37cd6fe1a7fb 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (123, (mkQ
  false (Nat.add (Nat.add 0x5ae0137ae16df188defa1b2b08a571b72a723917c875902851724c717184e277c90b910d
  (Nat.shiftLeft (Nat.add 0x79f39805a7575f04a5bd65c72efd99b91a9e1c5017400063cb45b9dbfb0358f7cecac255
  (Nat.shiftLeft 0xcb34d3e328d98b6e4f61634e8d49520d61c750fe6837623672e0baca481e491e022ae1fd 288))
  288)) (Nat.shiftLeft (Nat.add
  0x9ef152f0f1c96d0916249b2f13bc3015a9eaaecf64c9fec6064e2f91776c5d2195b910d1 (Nat.shiftLeft (Nat.add
  0x7c64eb055df80729bfd48f5db8bed0d3b38202fb4f22dbe99ab77513ff00c05225eefe70 (Nat.shiftLeft
  0x23c2e41e4574be2e05d812f22eab3734ab73657ba2772f442c44bee6 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (125, (mkQ
  false (Nat.add (Nat.add 0x5d937f76bcf30b36403d2508ba8fcbf3c9cc7544d1198a7d43c5081465d780880f044611
  (Nat.shiftLeft (Nat.add 0xd7855b04e02c9538b6c10918a0ec719391310395e3ccbf0f802f1b5b2a1f4f727ae80d74
  (Nat.shiftLeft 0x8ace0b82dd4e68cc9f5ee306d397a4bb01168184724620f9b5bf701638c3bd5a22e6d9b4 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa41b7540380590ce7f4b070143946d37f301dcbb54064acc7715b47a91df5a036578c767 (Nat.shiftLeft (Nat.add
  0x918cb0d3b0eb8ea0a177e737ce79a551d71937432aa74c3318c523f01ac4d68117011939 (Nat.shiftLeft
  0x302d474b3092ef45cc250cefcefb72c931d07ee7df1e72819d3380b 288)) 288)) 864)) (Nat.add (Nat.add
  0x3f44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a000 (Nat.shiftLeft (Nat.add
  0xa2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b4095 (Nat.shiftLeft
  0xb984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x52c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354df
  (Nat.shiftLeft (Nat.add 0x3ce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa9 288)) 288)) 864)))), (127, (mkQ
  false (Nat.add (Nat.add 0x3e3e8fb6eca15c703e9f40fc7e1a66be1f4ce6096348d6f432940c0a887cdfd8a6adedb9
  (Nat.shiftLeft (Nat.add 0x6f7ba25370a9b6526a748263ed958ee26e4372275833c868b63ff078cec42e088d087da
  (Nat.shiftLeft 0x5b6d7bfcfb49c5551697d5a38a43864e8c4f789ab93c4e3e904002a8f9b38606c6946778 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdd95ab6a911ab0d7720b0c2832f9888ddcfa0c9c41d25edf8978a0fe8ea020b0d5d19eda (Nat.shiftLeft (Nat.add
  0xb8c33fcd1fde9ae7e9e9c9cfba80d9626a185411b6a722a8cb9887c694586ec79a31cad3 (Nat.shiftLeft
  0x561af1265cc582bff27bb95f7ad58f7f0156562939f3151b94f711 288)) 288)) 864)) (Nat.add (Nat.add
  0x7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e3634000 (Nat.shiftLeft (Nat.add
  0x4563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a (Nat.shiftLeft
  0x73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b07 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf
  (Nat.shiftLeft (Nat.add 0x79ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfa
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f52 288)) 288)) 864)))), (129, (mkQ
  false (Nat.add (Nat.add 0x7533b9503a29e60b7e5b161a63ca089c835b3088af31cd49be78ca761128e4ae00afd75
  (Nat.shiftLeft (Nat.add 0xd1bfbfe40383b3748840a2c764d76cc9f5833233a2d2164b1eb0672d9e603d3358966b71
  (Nat.shiftLeft 0x3e0f8f6e9554b5a59470ccd9cb6ab8d60e3d9957538324b3d0e3112368b829d4031774bd 288))
  288)) (Nat.shiftLeft (Nat.add
  0x41b676823e311627c26514863902b8efdc8860386c07b4d6d4deb652dfb92d8daa14df94 (Nat.shiftLeft (Nat.add
  0x5bc8797ead61ce7c6302582a2b7182e763d6338e981289710247d0467b406b7f3b0af5a9 (Nat.shiftLeft
  0x11f682929c555a240d202bd87cf4ee6d3c86eee389768bb72a5ab5 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (131, (mkQ
  false (Nat.add (Nat.add 0x3655206a7c957a48e215f7df38b50be0b3768324aac1486d6c46815c12a3cb4467aff67f
  (Nat.shiftLeft (Nat.add 0xfd29e0bc096cb156e8dcaaf8fa517094a68cd935af8dec496c2b7a089ea860c47caf70e4
  (Nat.shiftLeft 0x8baa27f0f2cf22700210a228aaec7f0ef9029b9bd24b627b04020cd7f01455e69a2229a 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x3c3d35be2a240e858d955883edd7329f0bf9b108e53309b000eed021e72bb1bfa679f09b (Nat.shiftLeft (Nat.add
  0xb0bf46c0e98d8ab2be3564b73ffad553249c94378bf5ae2a71a8ad00c64acc55ccdb7f56 (Nat.shiftLeft
  0x155df6c52549d231eeabc77ef109eaff72db9b8e902784eac38e2f 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (155, (mkQ
  false (Nat.add (Nat.add 0x5a5e3ef611ae056bef789070485a1ae3033f1b9b4d84669c1360f49ef90edbe13d4da453
  (Nat.shiftLeft (Nat.add 0x301c34c20de70711c754cb93fd6bcd72e442dfaddd4d24a9d48185355220e3464e2d2a4e
  (Nat.shiftLeft 0x741a4b790218b9a76487f6e8440efe1611b63bd6dac225f768b5644296c7833aca85976 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xfe878c418d16cbc917af9398d591e3b09672b53cfac430f5565ee59746ffa4c5398b2a71 (Nat.shiftLeft (Nat.add
  0x209e0f0839520b0810b48e906ba66f3221b3dbcdb39db47ffc86aec4ce9782ffc6d37dbc (Nat.shiftLeft
  0x9daae521fe756fe81a03a5b0c45341b9e0c27710a93fc4026e5c40 288)) 288)) 864)) (Nat.add (Nat.add
  0x1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e080000 (Nat.shiftLeft (Nat.add
  0x5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8f (Nat.shiftLeft
  0xe5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x70ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a7
  (Nat.shiftLeft (Nat.add 0x21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca7
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938c 288)) 288)) 864)))), (157, (mkQ
  false (Nat.add (Nat.add 0x10fcb3379d15cbd16353cd1f7d31eb9f4c0215c3d9366d746e352461132ff9095e5e11d9
  (Nat.shiftLeft (Nat.add 0x52c8f48c9f27de2bfd6502125c26b19296e9b2d5471441b50883c17c73b8aaf67c94505a
  (Nat.shiftLeft 0xc304e4fd2574d62c5891bc22084754772afa11e57543b3b42dfef11ba394957917aabcb7 288))
  288)) (Nat.shiftLeft (Nat.add
  0x80991ec29aa5610ea075cf48c9a577f96cd0bd22bb05eea06e09e22d751079210e399cf4 (Nat.shiftLeft (Nat.add
  0x554d159fb52627792e0751f858d34c93ca526aa4e2f509c6d5a63a8e536b6c23f997ba67 (Nat.shiftLeft
  0x25741244f6996b0d0db5e6e292e5ff0ad7c2d02494fcb3923752a31 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (159, (mkQ
  false (Nat.add (Nat.add 0x274f5bf434eb3944a25dec8db052ef97a464f7ed64faa3ed2176597d30db38f56cc5bc8f
  (Nat.shiftLeft (Nat.add 0x33e117074a99773c484cc35cdd72cea399cb2b8a1829bc7a6f5b200ec135a18bc0b6c4e4
  (Nat.shiftLeft 0x9545be201fc71d85416b17da36c44a54430f860ebd73a93cd5409aeb9b491c4cc4bcab4b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x75b5c39916a52e2f89f82763196be3e19eaef75a02590fdb7837dc33c4de46e3055e6011 (Nat.shiftLeft (Nat.add
  0x29a30bb0dc67a6b1925efc306e996e5b353f88ad88adc8b6a9ebd12e382220dd7c9f83a9 (Nat.shiftLeft
  0x26cb3b162779054219064824def7a779b19e6aa5931605534506aa7e 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (161, (mkQ
  false (Nat.add (Nat.add 0xd5f0a6bb995a50b1c16cd25655bb2c90de1ad6ecfc1de944f359b9af0f549aedd9583389
  (Nat.shiftLeft (Nat.add 0x811e813e292fbafd9266427e229fe3155102b07bd47c50105cddfa719a3e1ada8d2f15bd
  (Nat.shiftLeft 0x8689a38b4d9acfd2791281fdece1a1f48a71928b1ee949977e9415b6cd256e902ad1f855 288))
  288)) (Nat.shiftLeft (Nat.add
  0xae794b4620707de78f399ac3aa4971cefdb406cc303e947d86aec6ab3d392a8fac7cabb6 (Nat.shiftLeft (Nat.add
  0xb5640d360167c574de845282968931f3c3473075eb991ff29b4a48f722e4c66d89c8fb05 (Nat.shiftLeft
  0x8a08ea0657d8ae9e1f5f0316186b7a11afca0379061dea935ed9567 288)) 288)) 864)) (Nat.add (Nat.add
  0xa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd2000 (Nat.shiftLeft (Nat.add
  0x86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0cea (Nat.shiftLeft
  0x8b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f9
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af655 288)) 288)) 864)))), (163, (mkQ
  false (Nat.add (Nat.add 0x6a0fcc136960071d0234f374f2a235eb3e8e07e86f8221a60edcd60b811ecf84635b37a3
  (Nat.shiftLeft (Nat.add 0x79e69a8d49162bc544e830b132f4d76ae3b02778348a628844162fd3d09cda2f1c49e8bb
  (Nat.shiftLeft 0x239f85821b5547e41325bff68ca7be532ffd50205925f8d58001ea9b5ed96be9fe6b16e5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x685cd5548689bd8f0ed6afdf62738e05377a230f53cda29325b555a8bbf61182cca4b1e7 (Nat.shiftLeft (Nat.add
  0xcccbebd424b02a6c08bd06f8865a71e65be1a4bad2851a3fdbf3ceb247c9acbd34cf9007 (Nat.shiftLeft
  0x10f74b727d088382f5aabe922b6e47c1021d108232be04fe5441d59e 288)) 288)) 864)) (Nat.add (Nat.add
  0x7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e3634000 (Nat.shiftLeft (Nat.add
  0x4563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a (Nat.shiftLeft
  0x73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b07 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf
  (Nat.shiftLeft (Nat.add 0x79ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfa
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f52 288)) 288)) 864)))), (165, (mkQ
  false (Nat.add (Nat.add 0x82136d84293f3284d7a70eaae50ad254f56170382f061077e6c5e3abd2b8ec13b3d8e8f
  (Nat.shiftLeft (Nat.add 0x954f3e277e7037be829fb8a52d03e64e89c6c70e1bba6a7e30a4d671287c322ade703f2c
  (Nat.shiftLeft 0xcb5b6a3ac157a609c7f1d2c8d684fb3a419897b0eeefbbe8c60cf3d7942b8673338a5a6e 288))
  288)) (Nat.shiftLeft (Nat.add
  0xb6b68855e97be187e9d48532bf5117ecfa391d70205ed694d5b1d39e56be5c68c63e6972 (Nat.shiftLeft (Nat.add
  0x33c0f5dd4fbfd9926f727100c96ebbf7e68ed68433c7c681804a2d397fa23b81f74022e5 (Nat.shiftLeft
  0x2ae180588d1372f6d469ddb59601be21ffa82211eb316d21051cf5a 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (167, (mkQ
  false (Nat.add (Nat.add 0x12b5555137ea33eeb1a51f10ef8c1118cefe2916a2cec12352db11d9cc934ad1179c01f3
  (Nat.shiftLeft (Nat.add 0x344ebf15968c79d9810e018cba632da81c1323956f6e1b0ce87161c37a22737b2257293d
  (Nat.shiftLeft 0xfa377f04307416068ab9e4e33723bf305a3d2f089c60cf9f53bd44fa9dd42f1105a21526 288))
  288)) (Nat.shiftLeft (Nat.add
  0xed43a66f0b5b4bd298fc6b330bd1490a1bc5421723b55c8111d9d3c1089592fe5bbe9009 (Nat.shiftLeft (Nat.add
  0xbfbffe67952fd8c5625b8eb964ce7efefc6d36db3c279519735a64a1f92adb0de4bd9366 (Nat.shiftLeft
  0xcd0b6ac4f0a1f7cb3aa46c29cf4cfa1b1a13580892feba31e3fb75 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (169, (mkQ
  false (Nat.add (Nat.add 0xf29828939d460f3df7417322014f6f72306002802574f0ccf5b4a1be15ece2405937b2a1
  (Nat.shiftLeft (Nat.add 0xf1e927bedebce5e17d6ec0b8bce588eb1fe422532c03a278d7394c1cf65e4843eab53cc0
  (Nat.shiftLeft 0x6e90d01b293b9a879357c10d5142ee9753822c9ff5066ed5f165dd3e73cb0e27d6c153eb 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa2c163e87be9898b0586a241ca23a291f030aed9dc5385e36949d1cb46b711db9765201a (Nat.shiftLeft (Nat.add
  0x89956a7e8125e80edac5ea1942959a6f77c84f5ff3e731e3882560a4c6eb61ce8d2e68a7 (Nat.shiftLeft
  0xa1e6850b99ca0369423bd0e0db3087b5dc1b7909835eba615ce1d 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (191, (mkQ
  false (Nat.add (Nat.add 0xf29828939d460f3df7417322014f6f72306002802574f0ccf5b4a1be15ece2405937b2a1
  (Nat.shiftLeft (Nat.add 0xf1e927bedebce5e17d6ec0b8bce588eb1fe422532c03a278d7394c1cf65e4843eab53cc0
  (Nat.shiftLeft 0x6e90d01b293b9a879357c10d5142ee9753822c9ff5066ed5f165dd3e73cb0e27d6c153eb 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa2c163e87be9898b0586a241ca23a291f030aed9dc5385e36949d1cb46b711db9765201a (Nat.shiftLeft (Nat.add
  0x89956a7e8125e80edac5ea1942959a6f77c84f5ff3e731e3882560a4c6eb61ce8d2e68a7 (Nat.shiftLeft
  0xa1e6850b99ca0369423bd0e0db3087b5dc1b7909835eba615ce1d 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (193, (mkQ
  false (Nat.add (Nat.add 0x12b5555137ea33eeb1a51f10ef8c1118cefe2916a2cec12352db11d9cc934ad1179c01f3
  (Nat.shiftLeft (Nat.add 0x344ebf15968c79d9810e018cba632da81c1323956f6e1b0ce87161c37a22737b2257293d
  (Nat.shiftLeft 0xfa377f04307416068ab9e4e33723bf305a3d2f089c60cf9f53bd44fa9dd42f1105a21526 288))
  288)) (Nat.shiftLeft (Nat.add
  0xed43a66f0b5b4bd298fc6b330bd1490a1bc5421723b55c8111d9d3c1089592fe5bbe9009 (Nat.shiftLeft (Nat.add
  0xbfbffe67952fd8c5625b8eb964ce7efefc6d36db3c279519735a64a1f92adb0de4bd9366 (Nat.shiftLeft
  0xcd0b6ac4f0a1f7cb3aa46c29cf4cfa1b1a13580892feba31e3fb75 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (195, (mkQ
  false (Nat.add (Nat.add 0x82136d84293f3284d7a70eaae50ad254f56170382f061077e6c5e3abd2b8ec13b3d8e8f
  (Nat.shiftLeft (Nat.add 0x954f3e277e7037be829fb8a52d03e64e89c6c70e1bba6a7e30a4d671287c322ade703f2c
  (Nat.shiftLeft 0xcb5b6a3ac157a609c7f1d2c8d684fb3a419897b0eeefbbe8c60cf3d7942b8673338a5a6e 288))
  288)) (Nat.shiftLeft (Nat.add
  0xb6b68855e97be187e9d48532bf5117ecfa391d70205ed694d5b1d39e56be5c68c63e6972 (Nat.shiftLeft (Nat.add
  0x33c0f5dd4fbfd9926f727100c96ebbf7e68ed68433c7c681804a2d397fa23b81f74022e5 (Nat.shiftLeft
  0x2ae180588d1372f6d469ddb59601be21ffa82211eb316d21051cf5a 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (197, (mkQ
  false (Nat.add (Nat.add 0x6a0fcc136960071d0234f374f2a235eb3e8e07e86f8221a60edcd60b811ecf84635b37a3
  (Nat.shiftLeft (Nat.add 0x79e69a8d49162bc544e830b132f4d76ae3b02778348a628844162fd3d09cda2f1c49e8bb
  (Nat.shiftLeft 0x239f85821b5547e41325bff68ca7be532ffd50205925f8d58001ea9b5ed96be9fe6b16e5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x685cd5548689bd8f0ed6afdf62738e05377a230f53cda29325b555a8bbf61182cca4b1e7 (Nat.shiftLeft (Nat.add
  0xcccbebd424b02a6c08bd06f8865a71e65be1a4bad2851a3fdbf3ceb247c9acbd34cf9007 (Nat.shiftLeft
  0x10f74b727d088382f5aabe922b6e47c1021d108232be04fe5441d59e 288)) 288)) 864)) (Nat.add (Nat.add
  0x7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e3634000 (Nat.shiftLeft (Nat.add
  0x4563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a (Nat.shiftLeft
  0x73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b07 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf
  (Nat.shiftLeft (Nat.add 0x79ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfa
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f52 288)) 288)) 864)))), (199, (mkQ
  false (Nat.add (Nat.add 0xd5f0a6bb995a50b1c16cd25655bb2c90de1ad6ecfc1de944f359b9af0f549aedd9583389
  (Nat.shiftLeft (Nat.add 0x811e813e292fbafd9266427e229fe3155102b07bd47c50105cddfa719a3e1ada8d2f15bd
  (Nat.shiftLeft 0x8689a38b4d9acfd2791281fdece1a1f48a71928b1ee949977e9415b6cd256e902ad1f855 288))
  288)) (Nat.shiftLeft (Nat.add
  0xae794b4620707de78f399ac3aa4971cefdb406cc303e947d86aec6ab3d392a8fac7cabb6 (Nat.shiftLeft (Nat.add
  0xb5640d360167c574de845282968931f3c3473075eb991ff29b4a48f722e4c66d89c8fb05 (Nat.shiftLeft
  0x8a08ea0657d8ae9e1f5f0316186b7a11afca0379061dea935ed9567 288)) 288)) 864)) (Nat.add (Nat.add
  0xa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd2000 (Nat.shiftLeft (Nat.add
  0x86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0cea (Nat.shiftLeft
  0x8b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f9
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af655 288)) 288)) 864)))), (201, (mkQ
  false (Nat.add (Nat.add 0x274f5bf434eb3944a25dec8db052ef97a464f7ed64faa3ed2176597d30db38f56cc5bc8f
  (Nat.shiftLeft (Nat.add 0x33e117074a99773c484cc35cdd72cea399cb2b8a1829bc7a6f5b200ec135a18bc0b6c4e4
  (Nat.shiftLeft 0x9545be201fc71d85416b17da36c44a54430f860ebd73a93cd5409aeb9b491c4cc4bcab4b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x75b5c39916a52e2f89f82763196be3e19eaef75a02590fdb7837dc33c4de46e3055e6011 (Nat.shiftLeft (Nat.add
  0x29a30bb0dc67a6b1925efc306e996e5b353f88ad88adc8b6a9ebd12e382220dd7c9f83a9 (Nat.shiftLeft
  0x26cb3b162779054219064824def7a779b19e6aa5931605534506aa7e 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (203, (mkQ
  false (Nat.add (Nat.add 0x10fcb3379d15cbd16353cd1f7d31eb9f4c0215c3d9366d746e352461132ff9095e5e11d9
  (Nat.shiftLeft (Nat.add 0x52c8f48c9f27de2bfd6502125c26b19296e9b2d5471441b50883c17c73b8aaf67c94505a
  (Nat.shiftLeft 0xc304e4fd2574d62c5891bc22084754772afa11e57543b3b42dfef11ba394957917aabcb7 288))
  288)) (Nat.shiftLeft (Nat.add
  0x80991ec29aa5610ea075cf48c9a577f96cd0bd22bb05eea06e09e22d751079210e399cf4 (Nat.shiftLeft (Nat.add
  0x554d159fb52627792e0751f858d34c93ca526aa4e2f509c6d5a63a8e536b6c23f997ba67 (Nat.shiftLeft
  0x25741244f6996b0d0db5e6e292e5ff0ad7c2d02494fcb3923752a31 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (205, (mkQ
  false (Nat.add (Nat.add 0x5a5e3ef611ae056bef789070485a1ae3033f1b9b4d84669c1360f49ef90edbe13d4da453
  (Nat.shiftLeft (Nat.add 0x301c34c20de70711c754cb93fd6bcd72e442dfaddd4d24a9d48185355220e3464e2d2a4e
  (Nat.shiftLeft 0x741a4b790218b9a76487f6e8440efe1611b63bd6dac225f768b5644296c7833aca85976 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xfe878c418d16cbc917af9398d591e3b09672b53cfac430f5565ee59746ffa4c5398b2a71 (Nat.shiftLeft (Nat.add
  0x209e0f0839520b0810b48e906ba66f3221b3dbcdb39db47ffc86aec4ce9782ffc6d37dbc (Nat.shiftLeft
  0x9daae521fe756fe81a03a5b0c45341b9e0c27710a93fc4026e5c40 288)) 288)) 864)) (Nat.add (Nat.add
  0x1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e080000 (Nat.shiftLeft (Nat.add
  0x5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8f (Nat.shiftLeft
  0xe5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x70ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a7
  (Nat.shiftLeft (Nat.add 0x21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca7
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938c 288)) 288)) 864)))), (229, (mkQ
  false (Nat.add (Nat.add 0x3655206a7c957a48e215f7df38b50be0b3768324aac1486d6c46815c12a3cb4467aff67f
  (Nat.shiftLeft (Nat.add 0xfd29e0bc096cb156e8dcaaf8fa517094a68cd935af8dec496c2b7a089ea860c47caf70e4
  (Nat.shiftLeft 0x8baa27f0f2cf22700210a228aaec7f0ef9029b9bd24b627b04020cd7f01455e69a2229a 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x3c3d35be2a240e858d955883edd7329f0bf9b108e53309b000eed021e72bb1bfa679f09b (Nat.shiftLeft (Nat.add
  0xb0bf46c0e98d8ab2be3564b73ffad553249c94378bf5ae2a71a8ad00c64acc55ccdb7f56 (Nat.shiftLeft
  0x155df6c52549d231eeabc77ef109eaff72db9b8e902784eac38e2f 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (231, (mkQ
  false (Nat.add (Nat.add 0x7533b9503a29e60b7e5b161a63ca089c835b3088af31cd49be78ca761128e4ae00afd75
  (Nat.shiftLeft (Nat.add 0xd1bfbfe40383b3748840a2c764d76cc9f5833233a2d2164b1eb0672d9e603d3358966b71
  (Nat.shiftLeft 0x3e0f8f6e9554b5a59470ccd9cb6ab8d60e3d9957538324b3d0e3112368b829d4031774bd 288))
  288)) (Nat.shiftLeft (Nat.add
  0x41b676823e311627c26514863902b8efdc8860386c07b4d6d4deb652dfb92d8daa14df94 (Nat.shiftLeft (Nat.add
  0x5bc8797ead61ce7c6302582a2b7182e763d6338e981289710247d0467b406b7f3b0af5a9 (Nat.shiftLeft
  0x11f682929c555a240d202bd87cf4ee6d3c86eee389768bb72a5ab5 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (233, (mkQ
  false (Nat.add (Nat.add 0x3e3e8fb6eca15c703e9f40fc7e1a66be1f4ce6096348d6f432940c0a887cdfd8a6adedb9
  (Nat.shiftLeft (Nat.add 0x6f7ba25370a9b6526a748263ed958ee26e4372275833c868b63ff078cec42e088d087da
  (Nat.shiftLeft 0x5b6d7bfcfb49c5551697d5a38a43864e8c4f789ab93c4e3e904002a8f9b38606c6946778 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdd95ab6a911ab0d7720b0c2832f9888ddcfa0c9c41d25edf8978a0fe8ea020b0d5d19eda (Nat.shiftLeft (Nat.add
  0xb8c33fcd1fde9ae7e9e9c9cfba80d9626a185411b6a722a8cb9887c694586ec79a31cad3 (Nat.shiftLeft
  0x561af1265cc582bff27bb95f7ad58f7f0156562939f3151b94f711 288)) 288)) 864)) (Nat.add (Nat.add
  0x7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e3634000 (Nat.shiftLeft (Nat.add
  0x4563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a (Nat.shiftLeft
  0x73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b07 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf
  (Nat.shiftLeft (Nat.add 0x79ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfa
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f52 288)) 288)) 864)))), (235, (mkQ
  false (Nat.add (Nat.add 0x5d937f76bcf30b36403d2508ba8fcbf3c9cc7544d1198a7d43c5081465d780880f044611
  (Nat.shiftLeft (Nat.add 0xd7855b04e02c9538b6c10918a0ec719391310395e3ccbf0f802f1b5b2a1f4f727ae80d74
  (Nat.shiftLeft 0x8ace0b82dd4e68cc9f5ee306d397a4bb01168184724620f9b5bf701638c3bd5a22e6d9b4 288))
  288)) (Nat.shiftLeft (Nat.add
  0xa41b7540380590ce7f4b070143946d37f301dcbb54064acc7715b47a91df5a036578c767 (Nat.shiftLeft (Nat.add
  0x918cb0d3b0eb8ea0a177e737ce79a551d71937432aa74c3318c523f01ac4d68117011939 (Nat.shiftLeft
  0x302d474b3092ef45cc250cefcefb72c931d07ee7df1e72819d3380b 288)) 288)) 864)) (Nat.add (Nat.add
  0x3f44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a000 (Nat.shiftLeft (Nat.add
  0xa2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b4095 (Nat.shiftLeft
  0xb984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x52c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354df
  (Nat.shiftLeft (Nat.add 0x3ce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa9 288)) 288)) 864)))), (237, (mkQ
  false (Nat.add (Nat.add 0x5ae0137ae16df188defa1b2b08a571b72a723917c875902851724c717184e277c90b910d
  (Nat.shiftLeft (Nat.add 0x79f39805a7575f04a5bd65c72efd99b91a9e1c5017400063cb45b9dbfb0358f7cecac255
  (Nat.shiftLeft 0xcb34d3e328d98b6e4f61634e8d49520d61c750fe6837623672e0baca481e491e022ae1fd 288))
  288)) (Nat.shiftLeft (Nat.add
  0x9ef152f0f1c96d0916249b2f13bc3015a9eaaecf64c9fec6064e2f91776c5d2195b910d1 (Nat.shiftLeft (Nat.add
  0x7c64eb055df80729bfd48f5db8bed0d3b38202fb4f22dbe99ab77513ff00c05225eefe70 (Nat.shiftLeft
  0x23c2e41e4574be2e05d812f22eab3734ab73657ba2772f442c44bee6 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (239, (mkQ
  false (Nat.add (Nat.add 0xeebcd177fdd40164fcac16ca0e221664b002c24bc242917d83cd61a4c91450b2ceff29e9
  (Nat.shiftLeft (Nat.add 0x2f50982bf2c81aced1b2d383fd70952a5bdfb34b0264e21f2406f57f26eecdf86f16edba
  (Nat.shiftLeft 0x3261d9a6ae78f7787eba5c3c8474da17a3ffb428013be14f598983ae69c5a0b2ee5a66ff 288))
  288)) (Nat.shiftLeft (Nat.add
  0x67c5b8ab756e2e0f7240740e232f3c543ed8522a170f75ee3cd32e34202a336be909c117 (Nat.shiftLeft (Nat.add
  0xc5633298b6d43c330f07e589f9f3e516ad9f6fca8596dfccd2f1583ce904452bc5d911b0 (Nat.shiftLeft
  0x911e3f7f40b6846e5ba9f03b298a02fbf3441bc4e0f37cd6fe1a7fb 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (241, (mkQ
  false (Nat.add (Nat.add 0x8c001f3a63754ac01512c81bd808ae144eb463f601a1e0cda49f13a4959b6732f3c3e099
  (Nat.shiftLeft (Nat.add 0xdc6eeb5f3d4e15e07e5b2f1370232e06a45afa1980de4f4c39f595ade56c75f0b91833c6
  (Nat.shiftLeft 0x24a95f2bb546e1a9c676322ab55fb3cf19ffb831eae69ec27712d278d8e19bf118f0bcc8 288))
  288)) (Nat.shiftLeft (Nat.add
  0xeb048ad45895396a1cc8708625b65aad6bd65adf60e1c0f554b771a5736ca0766ab720c6 (Nat.shiftLeft (Nat.add
  0x2b2bc7b25f07597d5c10e940855dd3142b82fe733991b5e9b9ffd498b4c1579833c644ca (Nat.shiftLeft
  0x1a2159e74d2f776c18dc23313140923f8aa8c7464b2f0d7604f42b 288)) 288)) 864)) (Nat.add (Nat.add
  0x40dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd200000 (Nat.shiftLeft (Nat.add
  0xf05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa6 (Nat.shiftLeft
  0x80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d86 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98b
  (Nat.shiftLeft (Nat.add 0x2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff76
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550c 288)) 288)) 864))))])]


end KAM.EffectiveStability.SJSU

end
