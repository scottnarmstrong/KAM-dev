/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs71

/-!
# Ledger inputs (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

def sjsuTsp_460 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 5, 1), [(89, (mkQ false (
  Nat.add (Nat.add 0x5eb40f7f3b2799177a0fe901bc9d5e35dc4b1ac1f1b9913ac6b9bafe4c4137129b32cd7f (
  Nat.shiftLeft 0xe79c1cd19acdfdc6f56a3fb834f5b0f3c9d5de88678e489e4653eed511e554a3585ddf8 288)) (
  Nat.shiftLeft (Nat.add 0xa5492dc73da3ff4276f251cbc5a1b26a53c728059e9d7c69819e721cd922344ccf02a807
  (Nat.shiftLeft (Nat.add 0xa362886766821761175681856498cc33e3fca1f723ba2bfdbbe9f61a25f8e9d56f2bcb64
  (Nat.shiftLeft 0x94c51d37f8ccf2bff939fe446210676a74f59b56 288)) 288)) 576)) (Nat.add (Nat.add
  0x95495b8318173f2dc937b34879bd45fa193ad31d7377734d9149fea1a201bdfc4000000 (Nat.shiftLeft
  0x209c2b00c1384b6aaade481fce77ff6429903921622b690979bf402dae35af877a6f8561 288)) (Nat.shiftLeft (
  Nat.add 0x14b19e391aab0d5a899cb7b8cce8fa054f4ae7a9d4580deca2f3ec2c19a738b4894b7050 (Nat.shiftLeft
  (Nat.add 0xa6e33cfdb02c29ef4af46061011a2d7e860bb7d61ffc5056b6f8c6b6cb29e8bc53483c6c (Nat.shiftLeft
  0x12536f0e3bd4349d7b01ac4e555ee8492318f0 288)) 288)) 576)))), (91, (mkQ false (Nat.add (Nat.add
  0x74b5f6cdaa9a149d447a94724baace23e6e7618aa2d8359e9753bcdc8a891db9d3a611ef (Nat.shiftLeft
  0xde9f4d29451f339b7d758db38e909888b516d093c3366372c7927d56ef08046e8dc2bea2 288)) (Nat.shiftLeft (
  Nat.add 0x4b3e08d1ad172800adcd716097dd37b9981c3fb9ee6ed6cecc01442e651758ec6c954cd3 (Nat.shiftLeft
  (Nat.add 0x9aee98f65dc4535786b9623a10d8da5f493f0b0c0621dff98f1668cb996fe9210dfe23ac (Nat.shiftLeft
  0x12b8bf8d6b0667fe919b458fc87d8468fc01eaf47e 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (125, (mkQ true (Nat.add (Nat.add
  0xb90f66ee1d55c1559807dedcc7ed991f1a0dd048dd39194155f69dffb56bb3e58c6394f1 (Nat.shiftLeft
  0x48f93378783485ce6525bd9a7346d8662bdf53f01bd52a43bebbaef0480d33f21432c5af 288)) (Nat.shiftLeft (
  Nat.add 0xd54eec4892c7a3e18e0bc7dcdee7f9cf564b4a474f66a1fa5b76627f02113a8be19978d7 (Nat.shiftLeft
  (Nat.add 0xb196098a53f7096e7d80abf9f136868b7ad142ab874c6521b2b86806031424153c44bbb4 (Nat.shiftLeft
  0x34bfcaa31ef806355249b7e591bd45a861fa460aa0 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (127, (mkQ true (Nat.add (Nat.add
  0x129a641d38b8d735e4e59f0b4efff62d8278d04b4c654c60343bb8d6deea74721cee0171 (Nat.shiftLeft
  0x8fb59a927bd4f6f3a7beecd95fb1e50f034e908f6b094abcf9a22d6e703e0c8d3631740f 288)) (Nat.shiftLeft (
  Nat.add 0x73e40c291c7ac8d5c4d07d0771aae22a061493af4e46a224992940890684cfad45692029 (Nat.shiftLeft
  (Nat.add 0xc19a27b2960dd45db0a845355f49308fd8236ea8a310d003496e5555d3f1837cff371f3d (Nat.shiftLeft
  0x17c990271679536f94fb8e65e8e960656f1003ed09 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (161, (mkQ true (Nat.add (Nat.add
  0x2297f953efd88c238ffa5be1f78ce4a62f31aad12ca2e9c126f5f01487f6ad61166ee83f (Nat.shiftLeft
  0x2144fbed37266a7f158dfc55a93c43049cf71cf210e08460b2182b968c77dfa2804c5240 288)) (Nat.shiftLeft (
  Nat.add 0x6adf9f1be0aa9e01c08df8f9ef7b903d49aaff38eaaf23f1f708c2c13d41f0f2bb45201e (Nat.shiftLeft
  (Nat.add 0x27cc05a560b37306dc98cb25e0c9e6ce724f6824431c30e1528b27e7a9283d7126c7c633 (Nat.shiftLeft
  0x1a61192189c75e8656f3313db63aec81940a7e25de 288)) 288)) 576)) (Nat.add (Nat.add
  0x1ddb78b3d19e3fd5f50b23db4b8c4132050bc3d2b0b17d75e9db995386cd25ff4000000 (Nat.shiftLeft
  0xa01f3bccf371a8aeeef9419ff617ffe0d51cd839e06f1501e526400922d789817ee31aad 288)) (Nat.shiftLeft (
  Nat.add 0x3756b93e9eef02abb51f57f1c294fecddca894bb90de692f53ca626f3854a4f0e84249a9 (Nat.shiftLeft
  (Nat.add 0xbafa3f65f008d52fdbca79ad00386f7fb468be5e0665a9aaf164f48af56ec825aa41a5af (Nat.shiftLeft
  0x3aa49693f2a70ec4bcd22761112fb41d3d1c9 288)) 288)) 576)))), (163, (mkQ true (Nat.add (Nat.add
  0xb33155256056c1583878e8140a795c0d0e48cc041ac4a69d15d1716f0c196cae83ba2c39 (Nat.shiftLeft
  0xd0552ad39bfa87109594804cd09f0f76536ab54da562bdf638de6c14bc1bfa7091db607 288)) (Nat.shiftLeft (
  Nat.add 0x40db4b07b316f08cb356f82bf3842bff4824d8ea98bc6306b27f9d9780be38eabdfc2e70 (Nat.shiftLeft
  (Nat.add 0x4799735ed658514bbba79d651f1e54dfbaab4631c536ef4e5b53764e37001b7d3902a449 (Nat.shiftLeft
  0x76a4ef692fe4aeeb6cf2a4c3541810c0f5fdd0bc6f 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (197, (mkQ true (Nat.add (Nat.add
  0xb33155256056c1583878e8140a795c0d0e48cc041ac4a69d15d1716f0c196cae83ba2c39 (Nat.shiftLeft
  0xd0552ad39bfa87109594804cd09f0f76536ab54da562bdf638de6c14bc1bfa7091db607 288)) (Nat.shiftLeft (
  Nat.add 0x40db4b07b316f08cb356f82bf3842bff4824d8ea98bc6306b27f9d9780be38eabdfc2e70 (Nat.shiftLeft
  (Nat.add 0x4799735ed658514bbba79d651f1e54dfbaab4631c536ef4e5b53764e37001b7d3902a449 (Nat.shiftLeft
  0x76a4ef692fe4aeeb6cf2a4c3541810c0f5fdd0bc6f 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (199, (mkQ true (Nat.add (Nat.add
  0x2297f953efd88c238ffa5be1f78ce4a62f31aad12ca2e9c126f5f01487f6ad61166ee83f (Nat.shiftLeft
  0x2144fbed37266a7f158dfc55a93c43049cf71cf210e08460b2182b968c77dfa2804c5240 288)) (Nat.shiftLeft (
  Nat.add 0x6adf9f1be0aa9e01c08df8f9ef7b903d49aaff38eaaf23f1f708c2c13d41f0f2bb45201e (Nat.shiftLeft
  (Nat.add 0x27cc05a560b37306dc98cb25e0c9e6ce724f6824431c30e1528b27e7a9283d7126c7c633 (Nat.shiftLeft
  0x1a61192189c75e8656f3313db63aec81940a7e25de 288)) 288)) 576)) (Nat.add (Nat.add
  0x1ddb78b3d19e3fd5f50b23db4b8c4132050bc3d2b0b17d75e9db995386cd25ff4000000 (Nat.shiftLeft
  0xa01f3bccf371a8aeeef9419ff617ffe0d51cd839e06f1501e526400922d789817ee31aad 288)) (Nat.shiftLeft (
  Nat.add 0x3756b93e9eef02abb51f57f1c294fecddca894bb90de692f53ca626f3854a4f0e84249a9 (Nat.shiftLeft
  (Nat.add 0xbafa3f65f008d52fdbca79ad00386f7fb468be5e0665a9aaf164f48af56ec825aa41a5af (Nat.shiftLeft
  0x3aa49693f2a70ec4bcd22761112fb41d3d1c9 288)) 288)) 576)))), (233, (mkQ true (Nat.add (Nat.add
  0x129a641d38b8d735e4e59f0b4efff62d8278d04b4c654c60343bb8d6deea74721cee0171 (Nat.shiftLeft
  0x8fb59a927bd4f6f3a7beecd95fb1e50f034e908f6b094abcf9a22d6e703e0c8d3631740f 288)) (Nat.shiftLeft (
  Nat.add 0x73e40c291c7ac8d5c4d07d0771aae22a061493af4e46a224992940890684cfad45692029 (Nat.shiftLeft
  (Nat.add 0xc19a27b2960dd45db0a845355f49308fd8236ea8a310d003496e5555d3f1837cff371f3d (Nat.shiftLeft
  0x17c990271679536f94fb8e65e8e960656f1003ed09 288)) 288)) 576)) (Nat.add (Nat.add
  0x2ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed4000000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae5 288)) (Nat.shiftLeft (
  Nat.add 0x6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae793190 (Nat.shiftLeft
  (Nat.add 0x427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1c (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb3 288)) 288)) 576)))), (235, (mkQ true (Nat.add (Nat.add
  0xb90f66ee1d55c1559807dedcc7ed991f1a0dd048dd39194155f69dffb56bb3e58c6394f1 (Nat.shiftLeft
  0x48f93378783485ce6525bd9a7346d8662bdf53f01bd52a43bebbaef0480d33f21432c5af 288)) (Nat.shiftLeft (
  Nat.add 0xd54eec4892c7a3e18e0bc7dcdee7f9cf564b4a474f66a1fa5b76627f02113a8be19978d7 (Nat.shiftLeft
  (Nat.add 0xb196098a53f7096e7d80abf9f136868b7ad142ab874c6521b2b86806031424153c44bbb4 (Nat.shiftLeft
  0x34bfcaa31ef806355249b7e591bd45a861fa460aa0 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (269, (mkQ false (Nat.add (Nat.add
  0x74b5f6cdaa9a149d447a94724baace23e6e7618aa2d8359e9753bcdc8a891db9d3a611ef (Nat.shiftLeft
  0xde9f4d29451f339b7d758db38e909888b516d093c3366372c7927d56ef08046e8dc2bea2 288)) (Nat.shiftLeft (
  Nat.add 0x4b3e08d1ad172800adcd716097dd37b9981c3fb9ee6ed6cecc01442e651758ec6c954cd3 (Nat.shiftLeft
  (Nat.add 0x9aee98f65dc4535786b9623a10d8da5f493f0b0c0621dff98f1668cb996fe9210dfe23ac (Nat.shiftLeft
  0x12b8bf8d6b0667fe919b458fc87d8468fc01eaf47e 288)) 288)) 576)) (Nat.add (Nat.add
  0x5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda8000000 (Nat.shiftLeft
  0x4619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35ca 288)) (Nat.shiftLeft (
  Nat.add 0xcef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf26321 (Nat.shiftLeft
  (Nat.add 0x84e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c38 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef966 288)) 288)) 576)))), (271, (mkQ false (Nat.add (Nat.add
  0x5eb40f7f3b2799177a0fe901bc9d5e35dc4b1ac1f1b9913ac6b9bafe4c4137129b32cd7f (Nat.shiftLeft
  0xe79c1cd19acdfdc6f56a3fb834f5b0f3c9d5de88678e489e4653eed511e554a3585ddf8 288)) (Nat.shiftLeft (
  Nat.add 0xa5492dc73da3ff4276f251cbc5a1b26a53c728059e9d7c69819e721cd922344ccf02a807 (Nat.shiftLeft
  (Nat.add 0xa362886766821761175681856498cc33e3fca1f723ba2bfdbbe9f61a25f8e9d56f2bcb64 (Nat.shiftLeft
  0x94c51d37f8ccf2bff939fe446210676a74f59b56 288)) 288)) 576)) (Nat.add (Nat.add
  0x95495b8318173f2dc937b34879bd45fa193ad31d7377734d9149fea1a201bdfc4000000 (Nat.shiftLeft
  0x209c2b00c1384b6aaade481fce77ff6429903921622b690979bf402dae35af877a6f8561 288)) (Nat.shiftLeft (
  Nat.add 0x14b19e391aab0d5a899cb7b8cce8fa054f4ae7a9d4580deca2f3ec2c19a738b4894b7050 (Nat.shiftLeft
  (Nat.add 0xa6e33cfdb02c29ef4af46061011a2d7e860bb7d61ffc5056b6f8c6b6cb29e8bc53483c6c (Nat.shiftLeft
  0x12536f0e3bd4349d7b01ac4e555ee8492318f0 288)) 288)) 576))))])]

def sjsuTsp_461 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 5, 3), [(87, (mkQ false (
  Nat.add (Nat.add 0x18a109513030dcb95b4a05d2e3a6dfdf2226112fd73c4de40f38626f246a46cf42069be9 (
  Nat.shiftLeft (Nat.add 0xe231b71ce56479431a328124995ed06c4e0a97a99f60755475d93367a4b28a7590db033b
  (Nat.shiftLeft 0xe0a9dbe9c3dc39e4d82315cfcf96d03b26827139e882e5a105d7b2881d5cdc94c4806cbb 288))
  288)) (Nat.shiftLeft (Nat.add
  0x29a007733ad77d006f5480c84f7f39cfe694be3a101a3fb8ce78df96ae724a144cdf59b4 (Nat.shiftLeft (Nat.add
  0x92abb9472f684d602bd31bc84eecc753b75ec779fd02d9a58467fe4105b4412213dd18e5 (Nat.shiftLeft
  0x224bf5670e4 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (89, (mkQ false (Nat.add (Nat.add
  0x88b7dd4abcf5846fb017a2ab42f6919cb34ea42159df6bfbbd09f8eb82310124e78a5ea3 (Nat.shiftLeft (Nat.add
  0x494e80104127c6a1ed4e4a9c82a8c78faf5ee3b7ed49bf18cc1e36e0c8f17a7cb3724582 (Nat.shiftLeft
  0x1691e8e589bea7e74e7deb27c9e230ccf29dd514ad16cd585f58dbf5fd46ddc504a66e6f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x20a8838755e478c317bd7a50cdc6afc0b44295562749c7f7e6ca70cccc441a30f019405b
  (Nat.shiftLeft (Nat.add 0x1a937b65c1296f06b8089dd9a822dc53fc74e77d84ea75e8a877cb227aef44f2279e07e
  (Nat.shiftLeft 0x6e749aafb336 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (91, (mkQ false (Nat.add (Nat.add
  0x9c37dd0a8bd6143865c1fa1183c359464b8647e782a4e1a717b0d00ecccb0016b57af229 (Nat.shiftLeft (Nat.add
  0x67a1ec139d2790da70e99b9bb0363059b35b0f03226334eeee9e7e169fb46bb1a91b7c6 (Nat.shiftLeft
  0x2cf730d42a46c096133cba7113fad9b1d63022cf072dc6b475f7fa0da9a55648c06c2f3d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd87bb6ecb7cc0919499a73cfca80d73f1918bd064a5568176ac4c62ec1cd4074d3488266
  (Nat.shiftLeft (Nat.add 0xd0b049a541686961f8e62c00e60a9ca57d15cef54e51ff9b4037b54b92be94e617e2f4fe
  (Nat.shiftLeft 0x39b08c319826 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864)))), (93, (mkQ false (Nat.add (Nat.add
  0x10c83ded74eaa42ead5b2124d9d3cb62d3c68622408632f07e76c87785ee82a7787c1f8f (Nat.shiftLeft (Nat.add
  0xca5ea766481d1d78b1ea09a9f73d872e4890f9c9e3aa7224ee71902b94cde96ca7bf6343 (Nat.shiftLeft
  0x5483d55f3fc3891b4f9ee62eb6905a22c226a00d5615338c0d1f4193babf857235db80c5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xede09739d8c4cc963bf6bf939084d380fb6e16a2c15a681358b93c53fe248d789b1dfe5c
  (Nat.shiftLeft (Nat.add 0x96a212e139f503d099ac173bfa14311c98acd15350f601743deeca1fd265ff3b537f8d39
  (Nat.shiftLeft 0x1f156632088 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864)))), (123, (mkQ false (Nat.add (Nat.add
  0xf18da606114b98d7040b01ba3a4e739b309cc07b60489b9c2de329acedf9df677f354b01 (Nat.shiftLeft (Nat.add
  0x84c084b7dbed666b35050426f98dda0aea448727c720af499bfd906052e15477a35027b6 (Nat.shiftLeft
  0xc95910269f2baebd6e6813f499e319c13936414c52eccc49c3ad20e8b0ab6639d04d9ebb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5beba408f6624e9386df4633e51b75a222d3309b27e9597f86190f9aeceb85abdefb8bf8
  (Nat.shiftLeft (Nat.add 0x4a9225313da520f5a158600da0aa234d214c7da3d35923a36d73a0a643e0b3cb29c107ca
  (Nat.shiftLeft 0x1117381210954 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (125, (mkQ false (Nat.add (Nat.add
  0xae83109d5c8d733c42be465ba786cd7a4019f54fbcab87b084784e1b4ae428891bb84a9 (Nat.shiftLeft (Nat.add
  0xe42291d4aded38c7233350c64816e983b7a3d1935225ff5fb0a702df0bd14981ca289f2b (Nat.shiftLeft
  0x18551d7f6fb5e7c6fdaac927faa61f242a0119f695ab7f0beacab51d7c0bd872faca5648 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb2da18f2703439703f5c3d6727bbcb68400051080ead004b7e7c687f770e509c8976d312
  (Nat.shiftLeft (Nat.add 0x1282135d78f98b7aca458f365fdbd5f827f8de6ad30d8711f09d13220696c43661d92fcf
  (Nat.shiftLeft 0x51ea7b77b791a 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (127, (mkQ false (Nat.add (Nat.add
  0x882671dcdc283dc8c5bf5266974c1a2fb29e5950d839a4631da6b1de7f97f9bfb5187131 (Nat.shiftLeft (Nat.add
  0x2d1dc8bf830cf256f4cca6d77932d1ba6f00e217f568918d2c9350af43f071fc12347020 (Nat.shiftLeft
  0xf7346eef509293faf0dff37fd330682496e86e7fe340c8994ea7fc0bdc6d17a5695ae234 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc61e8f1e74d86dc6125c9894103cda82d14ddab24d9a9f30e72ccc8022ba1d72f754eb44
  (Nat.shiftLeft (Nat.add 0x77beea6ce2d5a26a5c353dc6ce9092ee0b95d44956a7bb4cecb9ff8e815c8aa021e325e9
  (Nat.shiftLeft 0x236449c98c1b9 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (129, (mkQ false (Nat.add (Nat.add
  0x9bb114ed3de8ddc75f2b0b94a29e5284d58606429ae6d52c438a53e2c98c918b583117db (Nat.shiftLeft (Nat.add
  0x5e020f735ccc92e126f6921143d9dc14c4427f596c2cf0cc36da555ece25886695531b9b (Nat.shiftLeft
  0x8f93f02f676c76a5a35bf3bd06698da955d80f772144ea488cc566b338226f29f1c26ac5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x38b78dca2c5e3c9a6f4111aeb5c56c7b57d716288dbff13a0070f6b9993179c3e7bfa593
  (Nat.shiftLeft (Nat.add 0xb8d844a58d3e1d46e0a94b398931e1d5f8cf69fa4a6631f22e04b20a112192e68ffcfd38
  (Nat.shiftLeft 0x12e0afff778a 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (159, (mkQ false (Nat.add (Nat.add
  0xcca01d1b347827253dbe92f425a71d6a167e6f40602bd0912cc3bf3e5050fd652ee8cb39 (Nat.shiftLeft (Nat.add
  0xc4123b571bea49cf727a3c2935292c86e761d8e635accf2c7dcb45f479db39571a9fa647 (Nat.shiftLeft
  0xb2f7128fe661a77cd9d3e45a3c9b7a2934f172fe83724ed6359d5126257957c9dbe1aeb3 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdfede5ddff5e90150432e8b714080617f75bc17e93b26c25d995fa65b33f90e23a481d74
  (Nat.shiftLeft (Nat.add 0xa6e8380997e7fa3807165318a3a203b4a5f12de9f6726ddcdf9f58a1c7b0c8118b1d9e82
  (Nat.shiftLeft 0x1b41268f7e3bb 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (161, (mkQ false (Nat.add (Nat.add
  0x61b90511c19c65b2b989dd2a7161b1a20f0f0cf6790a009ad22b28ee55c4d86fd5b43f0f (Nat.shiftLeft (Nat.add
  0x79f4a32efd46827c99c070ee6c8d0b13b23b601588ecb39448b46035d8cc8e300cfcbd3a (Nat.shiftLeft
  0x87e0d8f841bd7a8692ab814fcb679ee4e948aee6e949621c32ad34e67250e41ef5d8a8c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d99e5188160fd8dc75531ff5093bb1dd253c5556668e135ec9f9e5788ab79bc84efa39 (
  Nat.shiftLeft (Nat.add 0xa6b4ca673dc41031855e5dcf8f352725bf3150df8fa96e00480733bd68045bdd6047444a
  (Nat.shiftLeft 0x3342d743922c 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (163, (mkQ false (Nat.add (Nat.add
  0xaf013e59711216e4ccac96ee83b0579290b4ca59b84bf54e8847ef55e7f835e6763feb81 (Nat.shiftLeft (Nat.add
  0x55c4dc5821cd6302624973d06695a8803dc3eff1c192ff90d386544febeace18a7e4ce9f (Nat.shiftLeft
  0xfe5acbcf4c3334ba93c3290b54c0b71cd16dc8a61c799e662b240fd1b4f417a29fa2145a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x1e046ba352567fa4257183cc9e117943b27bc562b13f290915e5dc22a438f91c395e41ea
  (Nat.shiftLeft (Nat.add 0x4cbf315003bc62eb64c3a199e48320dea124cdf256bcbca54a34dc3587cb4305a764dd7f
  (Nat.shiftLeft 0x4206d3eda079 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (165, (mkQ false (Nat.add (Nat.add
  0x824b6807e17474a7f4365b06a0c412f03aed6e77dfab1270e10676fb71d24b4574332a69 (Nat.shiftLeft (Nat.add
  0x7a7c7987b703d6c1948ddd9ea784a48f49e724766fcfb9e6bcb18ff88ae39dfdac3daee5 (Nat.shiftLeft
  0xc6476f71a5230a1a1c5d6dce0f9977d9f03d915041a01a81cf539a9f7e6fbb9c39fb3a79 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc3a1635e13d5ada41a3dfab58a2dbf30e4649d70e6148a2e784a7c75524b004f66913fa
  (Nat.shiftLeft (Nat.add 0x9cdd3deb39312a744f47bafc6a7bddd050c865022b3a9b5275ad80d27a0f436eb11b970
  (Nat.shiftLeft 0xbe0462648d55 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (195, (mkQ false (Nat.add (Nat.add
  0x824b6807e17474a7f4365b06a0c412f03aed6e77dfab1270e10676fb71d24b4574332a69 (Nat.shiftLeft (Nat.add
  0x7a7c7987b703d6c1948ddd9ea784a48f49e724766fcfb9e6bcb18ff88ae39dfdac3daee5 (Nat.shiftLeft
  0xc6476f71a5230a1a1c5d6dce0f9977d9f03d915041a01a81cf539a9f7e6fbb9c39fb3a79 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc3a1635e13d5ada41a3dfab58a2dbf30e4649d70e6148a2e784a7c75524b004f66913fa
  (Nat.shiftLeft (Nat.add 0x9cdd3deb39312a744f47bafc6a7bddd050c865022b3a9b5275ad80d27a0f436eb11b970
  (Nat.shiftLeft 0xbe0462648d55 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (197, (mkQ false (Nat.add (Nat.add
  0xaf013e59711216e4ccac96ee83b0579290b4ca59b84bf54e8847ef55e7f835e6763feb81 (Nat.shiftLeft (Nat.add
  0x55c4dc5821cd6302624973d06695a8803dc3eff1c192ff90d386544febeace18a7e4ce9f (Nat.shiftLeft
  0xfe5acbcf4c3334ba93c3290b54c0b71cd16dc8a61c799e662b240fd1b4f417a29fa2145a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x1e046ba352567fa4257183cc9e117943b27bc562b13f290915e5dc22a438f91c395e41ea
  (Nat.shiftLeft (Nat.add 0x4cbf315003bc62eb64c3a199e48320dea124cdf256bcbca54a34dc3587cb4305a764dd7f
  (Nat.shiftLeft 0x4206d3eda079 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (199, (mkQ false (Nat.add (Nat.add
  0x61b90511c19c65b2b989dd2a7161b1a20f0f0cf6790a009ad22b28ee55c4d86fd5b43f0f (Nat.shiftLeft (Nat.add
  0x79f4a32efd46827c99c070ee6c8d0b13b23b601588ecb39448b46035d8cc8e300cfcbd3a (Nat.shiftLeft
  0x87e0d8f841bd7a8692ab814fcb679ee4e948aee6e949621c32ad34e67250e41ef5d8a8c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4d99e5188160fd8dc75531ff5093bb1dd253c5556668e135ec9f9e5788ab79bc84efa39 (
  Nat.shiftLeft (Nat.add 0xa6b4ca673dc41031855e5dcf8f352725bf3150df8fa96e00480733bd68045bdd6047444a
  (Nat.shiftLeft 0x3342d743922c 288)) 288)) 864)) (Nat.add (Nat.add
  0xf70c6007847c7673a066ea3372c752075618a4ee0e8f3fef2a3e3ba847dad2adf2740000 (Nat.shiftLeft (Nat.add
  0xfe05ed4e7b4f8077a6a2fdb59f01fe47e35fff837365bf38f2689d18e9b562da6550e4f8 (Nat.shiftLeft
  0xe282d6ee72377e71afb24bddeb2f72e5a6d306b28a092643f1571f9e2c2b2630f0082f39 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x54883d46f5589296b9d9271efe1cd91381e51f8b47876a20e5e50fa7ded7a1d55c501eb4
  (Nat.shiftLeft (Nat.add 0x8cb00be73e7dc00f36514c7e1da61c46026d7341485a93850c519e794ea79e815c16cb64
  (Nat.shiftLeft 0x61f632 288)) 288)) 864)))), (201, (mkQ false (Nat.add (Nat.add
  0xcca01d1b347827253dbe92f425a71d6a167e6f40602bd0912cc3bf3e5050fd652ee8cb39 (Nat.shiftLeft (Nat.add
  0xc4123b571bea49cf727a3c2935292c86e761d8e635accf2c7dcb45f479db39571a9fa647 (Nat.shiftLeft
  0xb2f7128fe661a77cd9d3e45a3c9b7a2934f172fe83724ed6359d5126257957c9dbe1aeb3 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdfede5ddff5e90150432e8b714080617f75bc17e93b26c25d995fa65b33f90e23a481d74
  (Nat.shiftLeft (Nat.add 0xa6e8380997e7fa3807165318a3a203b4a5f12de9f6726ddcdf9f58a1c7b0c8118b1d9e82
  (Nat.shiftLeft 0x1b41268f7e3bb 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (231, (mkQ false (Nat.add (Nat.add
  0x9bb114ed3de8ddc75f2b0b94a29e5284d58606429ae6d52c438a53e2c98c918b583117db (Nat.shiftLeft (Nat.add
  0x5e020f735ccc92e126f6921143d9dc14c4427f596c2cf0cc36da555ece25886695531b9b (Nat.shiftLeft
  0x8f93f02f676c76a5a35bf3bd06698da955d80f772144ea488cc566b338226f29f1c26ac5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x38b78dca2c5e3c9a6f4111aeb5c56c7b57d716288dbff13a0070f6b9993179c3e7bfa593
  (Nat.shiftLeft (Nat.add 0xb8d844a58d3e1d46e0a94b398931e1d5f8cf69fa4a6631f22e04b20a112192e68ffcfd38
  (Nat.shiftLeft 0x12e0afff778a 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (233, (mkQ false (Nat.add (Nat.add
  0x882671dcdc283dc8c5bf5266974c1a2fb29e5950d839a4631da6b1de7f97f9bfb5187131 (Nat.shiftLeft (Nat.add
  0x2d1dc8bf830cf256f4cca6d77932d1ba6f00e217f568918d2c9350af43f071fc12347020 (Nat.shiftLeft
  0xf7346eef509293faf0dff37fd330682496e86e7fe340c8994ea7fc0bdc6d17a5695ae234 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc61e8f1e74d86dc6125c9894103cda82d14ddab24d9a9f30e72ccc8022ba1d72f754eb44
  (Nat.shiftLeft (Nat.add 0x77beea6ce2d5a26a5c353dc6ce9092ee0b95d44956a7bb4cecb9ff8e815c8aa021e325e9
  (Nat.shiftLeft 0x236449c98c1b9 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (235, (mkQ false (Nat.add (Nat.add
  0xae83109d5c8d733c42be465ba786cd7a4019f54fbcab87b084784e1b4ae428891bb84a9 (Nat.shiftLeft (Nat.add
  0xe42291d4aded38c7233350c64816e983b7a3d1935225ff5fb0a702df0bd14981ca289f2b (Nat.shiftLeft
  0x18551d7f6fb5e7c6fdaac927faa61f242a0119f695ab7f0beacab51d7c0bd872faca5648 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb2da18f2703439703f5c3d6727bbcb68400051080ead004b7e7c687f770e509c8976d312
  (Nat.shiftLeft (Nat.add 0x1282135d78f98b7aca458f365fdbd5f827f8de6ad30d8711f09d13220696c43661d92fcf
  (Nat.shiftLeft 0x51ea7b77b791a 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (237, (mkQ false (Nat.add (Nat.add
  0xf18da606114b98d7040b01ba3a4e739b309cc07b60489b9c2de329acedf9df677f354b01 (Nat.shiftLeft (Nat.add
  0x84c084b7dbed666b35050426f98dda0aea448727c720af499bfd906052e15477a35027b6 (Nat.shiftLeft
  0xc95910269f2baebd6e6813f499e319c13936414c52eccc49c3ad20e8b0ab6639d04d9ebb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5beba408f6624e9386df4633e51b75a222d3309b27e9597f86190f9aeceb85abdefb8bf8
  (Nat.shiftLeft (Nat.add 0x4a9225313da520f5a158600da0aa234d214c7da3d35923a36d73a0a643e0b3cb29c107ca
  (Nat.shiftLeft 0x1117381210954 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (267, (mkQ false (Nat.add (Nat.add
  0x10c83ded74eaa42ead5b2124d9d3cb62d3c68622408632f07e76c87785ee82a7787c1f8f (Nat.shiftLeft (Nat.add
  0xca5ea766481d1d78b1ea09a9f73d872e4890f9c9e3aa7224ee71902b94cde96ca7bf6343 (Nat.shiftLeft
  0x5483d55f3fc3891b4f9ee62eb6905a22c226a00d5615338c0d1f4193babf857235db80c5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xede09739d8c4cc963bf6bf939084d380fb6e16a2c15a681358b93c53fe248d789b1dfe5c
  (Nat.shiftLeft (Nat.add 0x96a212e139f503d099ac173bfa14311c98acd15350f601743deeca1fd265ff3b537f8d39
  (Nat.shiftLeft 0x1f156632088 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864)))), (269, (mkQ false (Nat.add (Nat.add
  0x9c37dd0a8bd6143865c1fa1183c359464b8647e782a4e1a717b0d00ecccb0016b57af229 (Nat.shiftLeft (Nat.add
  0x67a1ec139d2790da70e99b9bb0363059b35b0f03226334eeee9e7e169fb46bb1a91b7c6 (Nat.shiftLeft
  0x2cf730d42a46c096133cba7113fad9b1d63022cf072dc6b475f7fa0da9a55648c06c2f3d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd87bb6ecb7cc0919499a73cfca80d73f1918bd064a5568176ac4c62ec1cd4074d3488266
  (Nat.shiftLeft (Nat.add 0xd0b049a541686961f8e62c00e60a9ca57d15cef54e51ff9b4037b54b92be94e617e2f4fe
  (Nat.shiftLeft 0x39b08c319826 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864)))), (271, (mkQ false (Nat.add (Nat.add
  0x88b7dd4abcf5846fb017a2ab42f6919cb34ea42159df6bfbbd09f8eb82310124e78a5ea3 (Nat.shiftLeft (Nat.add
  0x494e80104127c6a1ed4e4a9c82a8c78faf5ee3b7ed49bf18cc1e36e0c8f17a7cb3724582 (Nat.shiftLeft
  0x1691e8e589bea7e74e7deb27c9e230ccf29dd514ad16cd585f58dbf5fd46ddc504a66e6f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x20a8838755e478c317bd7a50cdc6afc0b44295562749c7f7e6ca70cccc441a30f019405b
  (Nat.shiftLeft (Nat.add 0x1a937b65c1296f06b8089dd9a822dc53fc74e77d84ea75e8a877cb227aef44f2279e07e
  (Nat.shiftLeft 0x6e749aafb336 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (273, (mkQ false (Nat.add (Nat.add
  0x18a109513030dcb95b4a05d2e3a6dfdf2226112fd73c4de40f38626f246a46cf42069be9 (Nat.shiftLeft (Nat.add
  0xe231b71ce56479431a328124995ed06c4e0a97a99f60755475d93367a4b28a7590db033b (Nat.shiftLeft
  0xe0a9dbe9c3dc39e4d82315cfcf96d03b26827139e882e5a105d7b2881d5cdc94c4806cbb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x29a007733ad77d006f5480c84f7f39cfe694be3a101a3fb8ce78df96ae724a144cdf59b4
  (Nat.shiftLeft (Nat.add 0x92abb9472f684d602bd31bc84eecc753b75ec779fd02d9a58467fe4105b4412213dd18e5
  (Nat.shiftLeft 0x224bf5670e4 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864))))])]

def sjsuTsp_462 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 5, 5), [(85, (mkQ false (
  Nat.add (Nat.add 0x173d8eef1e5d7c0e3a7d98554f856ff75ee5b89e04aa196f91f4cd0cf88cd94d531e09b3 (
  Nat.shiftLeft (Nat.add 0xab81d18cd6a3e73d0a30d82ab4feca0b046f7d54f0b60b026420eb4364b02906380f52f8
  (Nat.shiftLeft 0x85c917eca972e2151c4a94e68547283e25d0d76410dc6356c03d3a29f62970faf298247b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x71485521a5f1de577a18d9b7b1e096b3dddf538fa7d9bc293cf4f36136aa2548cec5006b (Nat.shiftLeft (Nat.add
  0x32f172aa59b6453f62c4e95ea10440c65b4dee77e89f6b184b7c7076f47f7cc211454598 (Nat.shiftLeft
  0x5a7ee4de6571f6eac6f1652afd3ea1c7b606a498f2f1f82ee4ec38a 288)) 288)) 864)) (Nat.add (Nat.add
  0xa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d00000 (Nat.shiftLeft (Nat.add
  0x58ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9f (Nat.shiftLeft
  0xc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fdc
  (Nat.shiftLeft (Nat.add 0x73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea9
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49e 288)) 288)) 864)))), (87, (mkQ
  false (Nat.add (Nat.add 0xbc209f22a3f7ed3ac3d79057d5d879aa7fec7d5366710841edc7a0111d18c49e89cbc581
  (Nat.shiftLeft (Nat.add 0xe88ab8546326b9fd3f2f07e9e82dc5239ea31fd9300227e78b7c8e2902f01e93edfd986e
  (Nat.shiftLeft 0x1c1b395b24f329bca99db121d6642c1649d2aaa599b3e49bd492802d37c6f5b163cd57e9 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd4b2aaf7ba182bc484a38b6fad457b98a6f5a60499b416dea6f4d95fca5c0b87ef0d3f91 (Nat.shiftLeft (Nat.add
  0xc04959333358a2855ef553fa06924336d4b9d7056400aefd70ae532f16a91f9d98479f19 (Nat.shiftLeft
  0xa3a555bcc2db7378b19845f93586268a458bb94d8705e76a1b49272 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (89, (mkQ
  false (Nat.add (Nat.add 0x19898bafebed21056a96102b40fe31fa5f745f8f094b67b348e1e066c0282c8a12928275
  (Nat.shiftLeft (Nat.add 0xd5362350ea4e4504e2ef594a3ead420fe34331c1f59f7a4c8052777ef405ef488e8d891a
  (Nat.shiftLeft 0x6525e0d7dbaf116a4ddfb3dec35801419ec4b1b1b5de823743a9a6b842bd8e5a84a74a63 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd73796dcca370713ffaaeb8cf52449468380c1ef72418715560d1bfddaad723dde31ec62 (Nat.shiftLeft (Nat.add
  0xf14ed1ab3227842af208da7e30a1fc13e5755778ecffa9d824c65d66f36067fb5dbe097a (Nat.shiftLeft
  0x71c42e10e9ceefb096aa30c266f28683f599b1d78e21f2ef4cd2d 288)) 288)) 864)) (Nat.add (Nat.add
  0x1e2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c1000 (Nat.shiftLeft (Nat.add
  0x16bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c2175 (Nat.shiftLeft
  0x4fcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c9 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4ee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f
  (Nat.shiftLeft (Nat.add 0x18428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf9
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b90727 288)) 288)) 864)))), (91, (mkQ
  false (Nat.add (Nat.add 0xd1d141ab71e1cf43e76fbd1ea45b4f6e91aa838e1394e9fe43e6646a918bdf7b21e42279
  (Nat.shiftLeft (Nat.add 0xd6566f204c80757c94ccf9e16fb2225f1ac084684eae6da47effd5dcdf7dca12a00412b3
  (Nat.shiftLeft 0x29e117e772c422ae958dea62b973ba6d2bfa46c88bad650d40aad104daf7ccf441bf9e63 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd3d022ed555553217434d508c27431be5edaca9ed6c2695589d4f2ad260db1d1c51a012d (Nat.shiftLeft (Nat.add
  0xc163c7466fbd859b9a855e3cf585d4dc244267544136457c3f90f6bb2974dda7d11151b5 (Nat.shiftLeft
  0x2b8d50f45354ef78a95f7085faa0baa8201fbe801eb0c9e271545c 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (93, (mkQ
  false (Nat.add (Nat.add 0x4807dbf3ac9b2852c2932d2cd95acdcb3eb72efa1597aa295ca68c818689fc5c56871ab7
  (Nat.shiftLeft (Nat.add 0xf0c35e1da92e5171d6fb54c7424baa5ab0751f5f9a9588f6e5178ebe00f227736acf30fc
  (Nat.shiftLeft 0x61798f032864c664e73f154ff6b2ded1106eff2c6c5be5929c5672266d2108475896f725 288))
  288)) (Nat.shiftLeft (Nat.add
  0xb1207d634afc5094a04e103f1a5c93707ec84d8d5fd861e638070bfe615091ff82eae84 (Nat.shiftLeft (Nat.add
  0x3d7e4cd23f53e02213c816b3b8d98952aabf750f010dedd6c58f2812a57610692a39f25c (Nat.shiftLeft
  0x30693ff4f0193eb3b062ebd3dc6589ab30024635c7d01fd87d0d3 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (121, (mkQ
  false (Nat.add (Nat.add 0x6ed91baa34697ec0131f926916779f16dae36af20771b5b49becc8b4beefb121adee1aef
  (Nat.shiftLeft (Nat.add 0x1f31cfce33f65f20229552b575265c2e0df4b82ad43210368dd3a7ce4027c070a7f374aa
  (Nat.shiftLeft 0x8dafeba2d98a31001414f14c664f27ee0c6b9d2cd599691b4fcc53726d6a6b14e956a20f 288))
  288)) (Nat.shiftLeft (Nat.add
  0x886819cf66f096ca03562fce9427a844d3e40fd60aa4521a6745ddadcd8502d66bd4e117 (Nat.shiftLeft (Nat.add
  0x8e0511b69ce5135f6605f956f73bebbd90f002f2951202f3d3c8a58405590ca67843926f (Nat.shiftLeft
  0x21f0b32e7d08f43368584d4291cefbef177b2b98b2382ab40a8b91c 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (123, (mkQ
  false (Nat.add (Nat.add 0x744d53d4364bf874407a0b606e5026e7ed17188246ad2ecc61c5486194d3cbac9596ebfd
  (Nat.shiftLeft (Nat.add 0x9c2aa3459338bdbbf7305a9d5ecb1eb009f752c4c3df1b8b09f6551a3572a40285465f36
  (Nat.shiftLeft 0xc6f71af18b8cb261d03907606d526d132093f73f0c0e025545bf0851adeff70073902d8 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xa256bfe5f9e5b6abf77620e8e418fd78cc66d080f6167173a967ffc90025c6643ade8b13 (Nat.shiftLeft (Nat.add
  0x22d8c7b35a3d430c148f9dcc8edbf9a51f87baac10c56009109dfe51badf3324e4f2c138 (Nat.shiftLeft
  0x6e48a65245d3336a8b7dad717cbd301a373052c37a043e98c7347ea 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864)))), (125, (mkQ
  false (Nat.add (Nat.add 0x5f94d80d836e91ef3fb1208eed092d24d814ad50a50d7f27c5acac2163f82dcdcd99ffb3
  (Nat.shiftLeft (Nat.add 0x37c5de318bb3c941adf650ef8ecf0fb05ef4073701dad3b63c66dbfc3f707247565ba3b6
  (Nat.shiftLeft 0xda522154b4f143d6dcd9e928466585c10285d272d06df7caf3b659aada84aab9488d0323 288))
  288)) (Nat.shiftLeft (Nat.add
  0xc67d4a06628ed52e768ea801447630d36ba0680bb665607ff2b5bb32e96773280fd1114e (Nat.shiftLeft (Nat.add
  0x950da92529fa20b0f7756279216fda3c8814ddaef86c98f9faba36445decb1ff708aedd8 (Nat.shiftLeft
  0x2bb4d68079ffbb667e460c22d66ed9612118048e75c06b187e367fb 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (127, (mkQ
  false (Nat.add (Nat.add 0x729ab2b821cb9c8faebe5e29451a8a1429976ab1b67cc4a8f374416a92ce7ebcaeb027a7
  (Nat.shiftLeft (Nat.add 0xddd63081a3e674dec68ba488c8c2ea60071b31a4a6f8e83c5d61773d22deee5f2afaa3e8
  (Nat.shiftLeft 0x47f529438a59d07261e5ec191f6a9341e24ef6bc0d4e787f42966db50aab6f4ca5a733b 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xe388c2d69235d3c2e65b19f65990b1f047992c24b7b1b00bfcc15cafa4aafd5a35549bd5 (Nat.shiftLeft (Nat.add
  0x12752af8fe316cbeef05cae3db03bdcb8bd0864bf349d93b88bd427f4e6b4529c0ed761a (Nat.shiftLeft
  0x148ed76288963f5b668e45aafea0361d497395a8fa4b108b9440d6b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (129, (mkQ
  false (Nat.add (Nat.add 0x4e5aec9fafa16903170fea73b91f013805e7d3cbef2b4b7ff1a049e96cac27b65a165f85
  (Nat.shiftLeft (Nat.add 0x5fac570b53a713c0b2b74ea94906b15b4972350a1d5be71720467766a151b545d1853648
  (Nat.shiftLeft 0xcefd8ef40e1b8bcc2e6841fc3bb1958d6485e49d926d870958adf20b9bfcdf95ba564243 288))
  288)) (Nat.shiftLeft (Nat.add
  0x8c4d7b94c63fba93d5910d687cf15fe82c7cdb0f9bb119b24c0553d81024d69070dab3f1 (Nat.shiftLeft (Nat.add
  0x393ba964c9bc64daee4afe2ba65e3d401def5f62aac5079a0d9af94bc52b47cae162f690 (Nat.shiftLeft
  0x16f02418fd77cc9b8479ab945a98f6e4757f3aac309cf920f2a8ce 288)) 288)) 864)) (Nat.add (Nat.add
  0x903750f8169b22baab60464a4180be6433f07ea55ebaf0c5ac7f6009250b1f65af480000 (Nat.shiftLeft (Nat.add
  0xbc17ec362dff591f1372833beca01f8a6e46e15cd181bf2817870b5a8c6139801bc33aa9 (Nat.shiftLeft
  0xe03b94dcf231d5d4ec8e489315a77fbac912e1ad1cd72ae537836872047f5569e71b1361 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbcd3c75a6f657315c7417736d1fe7b4be677efe55b637bc14fc87a8bbed13b69a9c43e62
  (Nat.shiftLeft (Nat.add 0xb922f21ac116a9f53bee6ce07d3c72a0d799b9a28475dbb52f391bebba925d2f7b17fdd
  (Nat.shiftLeft 0x1acfadfab8cc27b0837871a0aed7b05eea19c015abd9543 288)) 288)) 864)))), (131, (mkQ
  false (Nat.add (Nat.add 0xfc2fc1cd8a02b3c5b1709975b24ebb85d2e809cb67bb61fb64053129df1bc8dab1fdeb1d
  (Nat.shiftLeft (Nat.add 0xa015685230afa2908e133e443d1d3186acce5b96303cad5315e2ddbbd6be56f53ed34e65
  (Nat.shiftLeft 0xaa5baa3f676fa43ce00ff6abb2bb722804e7eb619167270fcfd06b7f15d12a9ba8ca409b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x43f99948d8ff80f4488d1d3ac5dce09d00c7b93242fff104f02f1235e762f13ad2e0b19c (Nat.shiftLeft (Nat.add
  0x4f50f5dd8891859033911f7a31a9ffa246793da3a875bb62b26cb30b81e5be1245bdd04b (Nat.shiftLeft
  0x11047f66178bc6b1f2c938e68418aec0b2b97736e5337a0570f3ca 288)) 288)) 864)) (Nat.add (Nat.add
  0x559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b878200000 (Nat.shiftLeft (Nat.add
  0x79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3c (Nat.shiftLeft
  0x9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9f
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29d
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e30 288)) 288)) 864)))), (157, (mkQ
  false (Nat.add (Nat.add 0xdbc9a85440fc123f7d33bf979e7003b68cbc7392add8b2d0809ce70d3ed21427270c9301
  (Nat.shiftLeft (Nat.add 0x77a71a34f6c5acd6614b114572ec23a498f7b8f94605fc6fa0a311e53bbd225a8f95382a
  (Nat.shiftLeft 0x4e647957b5c3686ff0fdf81ff9fbc71480eb1b1e0695cc3eb4b360ff5fbe0831690ed84 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xbe1ff5f727c28ac172d306e9f72179a51cdfd553519736eb9b9be2bae36530be7a5e7d18 (Nat.shiftLeft (Nat.add
  0x71d7dadae4867f5bfbb65b9940658b3c80b30f3399322fcb1483a0fae29e48256c6ed52a (Nat.shiftLeft
  0x3459fb8b5635bae18e16e50a77feec484822fa2515bfaef221fe7b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (159, (mkQ
  false (Nat.add (Nat.add 0x44ce7cebe8c26fab8d340ef4b07f03e982a22b82686782145250b9e2652f46a4461767e3
  (Nat.shiftLeft (Nat.add 0x7cba629c293ece15becd81031a15490c943a2a182648e3140ab0e1bd8d401c2c0d0c771e
  (Nat.shiftLeft 0x4bbfecd929766f75b63c1cbf780767da775edfbd3b25a1e22ed3072e8b1b4cf0a88b319d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xf5a3f731474abe43f68ba2572764b3fcfb946dad336c2b55dbe5283f95bd32c3c035374d (Nat.shiftLeft (Nat.add
  0x6544ac05d86cef926c20b90661271ca2900100ec29760d5bd71bf5a2f59a2216b0b8e725 (Nat.shiftLeft
  0x55fc04e7beb3bb1c95dde965508126d044731acff1598e434c14231 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (161, (mkQ
  false (Nat.add (Nat.add 0xe40db77a3c524532fe22d5ec2be80dfab4a62e75364cda3797f8eca581c460d93a82f56d
  (Nat.shiftLeft (Nat.add 0xc08f470f71d57e06278f6b4760298030df8c33b38f502070568930cabbd21d5f943345af
  (Nat.shiftLeft 0x7105fcffeb36e927de3aabc37f2915e660813290abfe51144a2e2dcfeae61707ca8c1e7b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x967f0c5952c5c4e648276491d8bad1045682ad9e6ba30a1442a403be358450a2661c2cc6 (Nat.shiftLeft (Nat.add
  0xa20279678dc323e4349ca10c63755b2a96aee18ff6895561ad627346ad67e9e5b43cc46e (Nat.shiftLeft
  0x36599d1c43ce559f850a54e16e07fd4e4be7e9b438e5a0afecd3997 288)) 288)) 864)) (Nat.add (Nat.add
  0x9903750f8169b22baab60464a4180be6433f07ea55ebaf0c5ac7f6009250b1f65af48000 (Nat.shiftLeft (Nat.add
  0x1bc17ec362dff591f1372833beca01f8a6e46e15cd181bf2817870b5a8c6139801bc33aa (Nat.shiftLeft
  0x2e03b94dcf231d5d4ec8e489315a77fbac912e1ad1cd72ae537836872047f5569e71b136 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdbcd3c75a6f657315c7417736d1fe7b4be677efe55b637bc14fc87a8bbed13b69a9c43e6
  (Nat.shiftLeft (Nat.add 0x30b922f21ac116a9f53bee6ce07d3c72a0d799b9a28475dbb52f391bebba925d2f7b17fd
  (Nat.shiftLeft 0x1acfadfab8cc27b0837871a0aed7b05eea19c015abd954 288)) 288)) 864)))), (163, (mkQ
  false (Nat.add (Nat.add 0x3980c20ede6faedddf10af872a1c55f17317af12a98f1acc2a5f01e9e2be568060c3e133
  (Nat.shiftLeft (Nat.add 0x88e404dc19cbf248aa7d2212cd69e1edebe813e75a747f4750954648b883a332aa61f915
  (Nat.shiftLeft 0xc2198abfd5a63f836dd1d169c7af528c53441cd7885582a09fb6a337225fac5c7bc8c02f 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdd95ad94798ba7239a8a1101d4ff877de32b163a59f051b964479d3f79cd5e8348888be0 (Nat.shiftLeft (Nat.add
  0x67a7ab7091c01fcf2bfbda6789205ab5c6c9866fa032d24da2720f15e5a2ca77fc7a37d0 (Nat.shiftLeft
  0xb3b3772cc5242ce260de9de73f299a651a8241c692e7db40256e269 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (165, (mkQ
  false (Nat.add (Nat.add 0x71b402a9effd83cbe9ca9e47d8c8492d81ce50808dd3ee07d40b86af5130e32982ce39e7
  (Nat.shiftLeft (Nat.add 0x5f18462852dd3f826382b27f1368d905f063e2c9b48b7a7d49eede2449d9ec41526362c8
  (Nat.shiftLeft 0x4813b19cf0baef943ac9d43998a478aa38a91620187b65abd87b9360b0e7c5895c22fc6e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x7c7f85f1be98985e30f7157ff4a78732b58b3b07d99a921b313a2f1975d75d7691225de7 (Nat.shiftLeft (Nat.add
  0xd37717bb8a6e60858d47efd6a6a65ae2d9b8a17b078706ac62c702a086de2c5c1af01791 (Nat.shiftLeft
  0xa642a133335547545a6c7bbea0eb1bd7cab9d12bb7ff4e7282bc8b 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (167, (mkQ
  false (Nat.add (Nat.add 0xe0163dd9006754ecf75d16aa85e5865859fc8824ce4fe6ccc02a1cc817654775ba3929db
  (Nat.shiftLeft (Nat.add 0x95b237a35b0d6940a05e501cd97bd021745b7e955a815cb3b333cc72c79d01e0cbd5eb2e
  (Nat.shiftLeft 0xee517c6b38ea8440333cc13d55128f43ba11eb31126753b8fa8998dc5fc09e9516894b4c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4b9d226cc33035779d2b975ba44fa98241569878518a7135b1cf2cc40e16013f10e7d996 (Nat.shiftLeft (Nat.add
  0x3f4a7e1c4b71385065291c25e47f7b79c9a699fc7b7aa5f1f93400d5d1d69e02e58ce55d (Nat.shiftLeft
  0xd52cc79fa830855718ea56414c19baf41303602253d810a92da8f 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (193, (mkQ
  false (Nat.add (Nat.add 0xe0163dd9006754ecf75d16aa85e5865859fc8824ce4fe6ccc02a1cc817654775ba3929db
  (Nat.shiftLeft (Nat.add 0x95b237a35b0d6940a05e501cd97bd021745b7e955a815cb3b333cc72c79d01e0cbd5eb2e
  (Nat.shiftLeft 0xee517c6b38ea8440333cc13d55128f43ba11eb31126753b8fa8998dc5fc09e9516894b4c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4b9d226cc33035779d2b975ba44fa98241569878518a7135b1cf2cc40e16013f10e7d996 (Nat.shiftLeft (Nat.add
  0x3f4a7e1c4b71385065291c25e47f7b79c9a699fc7b7aa5f1f93400d5d1d69e02e58ce55d (Nat.shiftLeft
  0xd52cc79fa830855718ea56414c19baf41303602253d810a92da8f 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (195, (mkQ
  false (Nat.add (Nat.add 0x71b402a9effd83cbe9ca9e47d8c8492d81ce50808dd3ee07d40b86af5130e32982ce39e7
  (Nat.shiftLeft (Nat.add 0x5f18462852dd3f826382b27f1368d905f063e2c9b48b7a7d49eede2449d9ec41526362c8
  (Nat.shiftLeft 0x4813b19cf0baef943ac9d43998a478aa38a91620187b65abd87b9360b0e7c5895c22fc6e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x7c7f85f1be98985e30f7157ff4a78732b58b3b07d99a921b313a2f1975d75d7691225de7 (Nat.shiftLeft (Nat.add
  0xd37717bb8a6e60858d47efd6a6a65ae2d9b8a17b078706ac62c702a086de2c5c1af01791 (Nat.shiftLeft
  0xa642a133335547545a6c7bbea0eb1bd7cab9d12bb7ff4e7282bc8b 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (197, (mkQ
  false (Nat.add (Nat.add 0x3980c20ede6faedddf10af872a1c55f17317af12a98f1acc2a5f01e9e2be568060c3e133
  (Nat.shiftLeft (Nat.add 0x88e404dc19cbf248aa7d2212cd69e1edebe813e75a747f4750954648b883a332aa61f915
  (Nat.shiftLeft 0xc2198abfd5a63f836dd1d169c7af528c53441cd7885582a09fb6a337225fac5c7bc8c02f 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdd95ad94798ba7239a8a1101d4ff877de32b163a59f051b964479d3f79cd5e8348888be0 (Nat.shiftLeft (Nat.add
  0x67a7ab7091c01fcf2bfbda6789205ab5c6c9866fa032d24da2720f15e5a2ca77fc7a37d0 (Nat.shiftLeft
  0xb3b3772cc5242ce260de9de73f299a651a8241c692e7db40256e269 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (199, (mkQ
  false (Nat.add (Nat.add 0xe40db77a3c524532fe22d5ec2be80dfab4a62e75364cda3797f8eca581c460d93a82f56d
  (Nat.shiftLeft (Nat.add 0xc08f470f71d57e06278f6b4760298030df8c33b38f502070568930cabbd21d5f943345af
  (Nat.shiftLeft 0x7105fcffeb36e927de3aabc37f2915e660813290abfe51144a2e2dcfeae61707ca8c1e7b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x967f0c5952c5c4e648276491d8bad1045682ad9e6ba30a1442a403be358450a2661c2cc6 (Nat.shiftLeft (Nat.add
  0xa20279678dc323e4349ca10c63755b2a96aee18ff6895561ad627346ad67e9e5b43cc46e (Nat.shiftLeft
  0x36599d1c43ce559f850a54e16e07fd4e4be7e9b438e5a0afecd3997 288)) 288)) 864)) (Nat.add (Nat.add
  0x9903750f8169b22baab60464a4180be6433f07ea55ebaf0c5ac7f6009250b1f65af48000 (Nat.shiftLeft (Nat.add
  0x1bc17ec362dff591f1372833beca01f8a6e46e15cd181bf2817870b5a8c6139801bc33aa (Nat.shiftLeft
  0x2e03b94dcf231d5d4ec8e489315a77fbac912e1ad1cd72ae537836872047f5569e71b136 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdbcd3c75a6f657315c7417736d1fe7b4be677efe55b637bc14fc87a8bbed13b69a9c43e6
  (Nat.shiftLeft (Nat.add 0x30b922f21ac116a9f53bee6ce07d3c72a0d799b9a28475dbb52f391bebba925d2f7b17fd
  (Nat.shiftLeft 0x1acfadfab8cc27b0837871a0aed7b05eea19c015abd954 288)) 288)) 864)))), (201, (mkQ
  false (Nat.add (Nat.add 0x44ce7cebe8c26fab8d340ef4b07f03e982a22b82686782145250b9e2652f46a4461767e3
  (Nat.shiftLeft (Nat.add 0x7cba629c293ece15becd81031a15490c943a2a182648e3140ab0e1bd8d401c2c0d0c771e
  (Nat.shiftLeft 0x4bbfecd929766f75b63c1cbf780767da775edfbd3b25a1e22ed3072e8b1b4cf0a88b319d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xf5a3f731474abe43f68ba2572764b3fcfb946dad336c2b55dbe5283f95bd32c3c035374d (Nat.shiftLeft (Nat.add
  0x6544ac05d86cef926c20b90661271ca2900100ec29760d5bd71bf5a2f59a2216b0b8e725 (Nat.shiftLeft
  0x55fc04e7beb3bb1c95dde965508126d044731acff1598e434c14231 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (203, (mkQ
  false (Nat.add (Nat.add 0xdbc9a85440fc123f7d33bf979e7003b68cbc7392add8b2d0809ce70d3ed21427270c9301
  (Nat.shiftLeft (Nat.add 0x77a71a34f6c5acd6614b114572ec23a498f7b8f94605fc6fa0a311e53bbd225a8f95382a
  (Nat.shiftLeft 0x4e647957b5c3686ff0fdf81ff9fbc71480eb1b1e0695cc3eb4b360ff5fbe0831690ed84 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xbe1ff5f727c28ac172d306e9f72179a51cdfd553519736eb9b9be2bae36530be7a5e7d18 (Nat.shiftLeft (Nat.add
  0x71d7dadae4867f5bfbb65b9940658b3c80b30f3399322fcb1483a0fae29e48256c6ed52a (Nat.shiftLeft
  0x3459fb8b5635bae18e16e50a77feec484822fa2515bfaef221fe7b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (229, (mkQ
  false (Nat.add (Nat.add 0xfc2fc1cd8a02b3c5b1709975b24ebb85d2e809cb67bb61fb64053129df1bc8dab1fdeb1d
  (Nat.shiftLeft (Nat.add 0xa015685230afa2908e133e443d1d3186acce5b96303cad5315e2ddbbd6be56f53ed34e65
  (Nat.shiftLeft 0xaa5baa3f676fa43ce00ff6abb2bb722804e7eb619167270fcfd06b7f15d12a9ba8ca409b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x43f99948d8ff80f4488d1d3ac5dce09d00c7b93242fff104f02f1235e762f13ad2e0b19c (Nat.shiftLeft (Nat.add
  0x4f50f5dd8891859033911f7a31a9ffa246793da3a875bb62b26cb30b81e5be1245bdd04b (Nat.shiftLeft
  0x11047f66178bc6b1f2c938e68418aec0b2b97736e5337a0570f3ca 288)) 288)) 864)) (Nat.add (Nat.add
  0x559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b878200000 (Nat.shiftLeft (Nat.add
  0x79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3c (Nat.shiftLeft
  0x9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9f
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29d
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e30 288)) 288)) 864)))), (231, (mkQ
  false (Nat.add (Nat.add 0x4e5aec9fafa16903170fea73b91f013805e7d3cbef2b4b7ff1a049e96cac27b65a165f85
  (Nat.shiftLeft (Nat.add 0x5fac570b53a713c0b2b74ea94906b15b4972350a1d5be71720467766a151b545d1853648
  (Nat.shiftLeft 0xcefd8ef40e1b8bcc2e6841fc3bb1958d6485e49d926d870958adf20b9bfcdf95ba564243 288))
  288)) (Nat.shiftLeft (Nat.add
  0x8c4d7b94c63fba93d5910d687cf15fe82c7cdb0f9bb119b24c0553d81024d69070dab3f1 (Nat.shiftLeft (Nat.add
  0x393ba964c9bc64daee4afe2ba65e3d401def5f62aac5079a0d9af94bc52b47cae162f690 (Nat.shiftLeft
  0x16f02418fd77cc9b8479ab945a98f6e4757f3aac309cf920f2a8ce 288)) 288)) 864)) (Nat.add (Nat.add
  0x903750f8169b22baab60464a4180be6433f07ea55ebaf0c5ac7f6009250b1f65af480000 (Nat.shiftLeft (Nat.add
  0xbc17ec362dff591f1372833beca01f8a6e46e15cd181bf2817870b5a8c6139801bc33aa9 (Nat.shiftLeft
  0xe03b94dcf231d5d4ec8e489315a77fbac912e1ad1cd72ae537836872047f5569e71b1361 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbcd3c75a6f657315c7417736d1fe7b4be677efe55b637bc14fc87a8bbed13b69a9c43e62
  (Nat.shiftLeft (Nat.add 0xb922f21ac116a9f53bee6ce07d3c72a0d799b9a28475dbb52f391bebba925d2f7b17fdd
  (Nat.shiftLeft 0x1acfadfab8cc27b0837871a0aed7b05eea19c015abd9543 288)) 288)) 864)))), (233, (mkQ
  false (Nat.add (Nat.add 0x729ab2b821cb9c8faebe5e29451a8a1429976ab1b67cc4a8f374416a92ce7ebcaeb027a7
  (Nat.shiftLeft (Nat.add 0xddd63081a3e674dec68ba488c8c2ea60071b31a4a6f8e83c5d61773d22deee5f2afaa3e8
  (Nat.shiftLeft 0x47f529438a59d07261e5ec191f6a9341e24ef6bc0d4e787f42966db50aab6f4ca5a733b 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xe388c2d69235d3c2e65b19f65990b1f047992c24b7b1b00bfcc15cafa4aafd5a35549bd5 (Nat.shiftLeft (Nat.add
  0x12752af8fe316cbeef05cae3db03bdcb8bd0864bf349d93b88bd427f4e6b4529c0ed761a (Nat.shiftLeft
  0x148ed76288963f5b668e45aafea0361d497395a8fa4b108b9440d6b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (235, (mkQ
  false (Nat.add (Nat.add 0x5f94d80d836e91ef3fb1208eed092d24d814ad50a50d7f27c5acac2163f82dcdcd99ffb3
  (Nat.shiftLeft (Nat.add 0x37c5de318bb3c941adf650ef8ecf0fb05ef4073701dad3b63c66dbfc3f707247565ba3b6
  (Nat.shiftLeft 0xda522154b4f143d6dcd9e928466585c10285d272d06df7caf3b659aada84aab9488d0323 288))
  288)) (Nat.shiftLeft (Nat.add
  0xc67d4a06628ed52e768ea801447630d36ba0680bb665607ff2b5bb32e96773280fd1114e (Nat.shiftLeft (Nat.add
  0x950da92529fa20b0f7756279216fda3c8814ddaef86c98f9faba36445decb1ff708aedd8 (Nat.shiftLeft
  0x2bb4d68079ffbb667e460c22d66ed9612118048e75c06b187e367fb 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (237, (mkQ
  false (Nat.add (Nat.add 0x744d53d4364bf874407a0b606e5026e7ed17188246ad2ecc61c5486194d3cbac9596ebfd
  (Nat.shiftLeft (Nat.add 0x9c2aa3459338bdbbf7305a9d5ecb1eb009f752c4c3df1b8b09f6551a3572a40285465f36
  (Nat.shiftLeft 0xc6f71af18b8cb261d03907606d526d132093f73f0c0e025545bf0851adeff70073902d8 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0xa256bfe5f9e5b6abf77620e8e418fd78cc66d080f6167173a967ffc90025c6643ade8b13 (Nat.shiftLeft (Nat.add
  0x22d8c7b35a3d430c148f9dcc8edbf9a51f87baac10c56009109dfe51badf3324e4f2c138 (Nat.shiftLeft
  0x6e48a65245d3336a8b7dad717cbd301a373052c37a043e98c7347ea 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864)))), (239, (mkQ
  false (Nat.add (Nat.add 0x6ed91baa34697ec0131f926916779f16dae36af20771b5b49becc8b4beefb121adee1aef
  (Nat.shiftLeft (Nat.add 0x1f31cfce33f65f20229552b575265c2e0df4b82ad43210368dd3a7ce4027c070a7f374aa
  (Nat.shiftLeft 0x8dafeba2d98a31001414f14c664f27ee0c6b9d2cd599691b4fcc53726d6a6b14e956a20f 288))
  288)) (Nat.shiftLeft (Nat.add
  0x886819cf66f096ca03562fce9427a844d3e40fd60aa4521a6745ddadcd8502d66bd4e117 (Nat.shiftLeft (Nat.add
  0x8e0511b69ce5135f6605f956f73bebbd90f002f2951202f3d3c8a58405590ca67843926f (Nat.shiftLeft
  0x21f0b32e7d08f43368584d4291cefbef177b2b98b2382ab40a8b91c 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (267, (mkQ
  false (Nat.add (Nat.add 0x4807dbf3ac9b2852c2932d2cd95acdcb3eb72efa1597aa295ca68c818689fc5c56871ab7
  (Nat.shiftLeft (Nat.add 0xf0c35e1da92e5171d6fb54c7424baa5ab0751f5f9a9588f6e5178ebe00f227736acf30fc
  (Nat.shiftLeft 0x61798f032864c664e73f154ff6b2ded1106eff2c6c5be5929c5672266d2108475896f725 288))
  288)) (Nat.shiftLeft (Nat.add
  0xb1207d634afc5094a04e103f1a5c93707ec84d8d5fd861e638070bfe615091ff82eae84 (Nat.shiftLeft (Nat.add
  0x3d7e4cd23f53e02213c816b3b8d98952aabf750f010dedd6c58f2812a57610692a39f25c (Nat.shiftLeft
  0x30693ff4f0193eb3b062ebd3dc6589ab30024635c7d01fd87d0d3 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (269, (mkQ
  false (Nat.add (Nat.add 0xd1d141ab71e1cf43e76fbd1ea45b4f6e91aa838e1394e9fe43e6646a918bdf7b21e42279
  (Nat.shiftLeft (Nat.add 0xd6566f204c80757c94ccf9e16fb2225f1ac084684eae6da47effd5dcdf7dca12a00412b3
  (Nat.shiftLeft 0x29e117e772c422ae958dea62b973ba6d2bfa46c88bad650d40aad104daf7ccf441bf9e63 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd3d022ed555553217434d508c27431be5edaca9ed6c2695589d4f2ad260db1d1c51a012d (Nat.shiftLeft (Nat.add
  0xc163c7466fbd859b9a855e3cf585d4dc244267544136457c3f90f6bb2974dda7d11151b5 (Nat.shiftLeft
  0x2b8d50f45354ef78a95f7085faa0baa8201fbe801eb0c9e271545c 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (271, (mkQ
  false (Nat.add (Nat.add 0x19898bafebed21056a96102b40fe31fa5f745f8f094b67b348e1e066c0282c8a12928275
  (Nat.shiftLeft (Nat.add 0xd5362350ea4e4504e2ef594a3ead420fe34331c1f59f7a4c8052777ef405ef488e8d891a
  (Nat.shiftLeft 0x6525e0d7dbaf116a4ddfb3dec35801419ec4b1b1b5de823743a9a6b842bd8e5a84a74a63 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd73796dcca370713ffaaeb8cf52449468380c1ef72418715560d1bfddaad723dde31ec62 (Nat.shiftLeft (Nat.add
  0xf14ed1ab3227842af208da7e30a1fc13e5755778ecffa9d824c65d66f36067fb5dbe097a (Nat.shiftLeft
  0x71c42e10e9ceefb096aa30c266f28683f599b1d78e21f2ef4cd2d 288)) 288)) 864)) (Nat.add (Nat.add
  0x1e2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c1000 (Nat.shiftLeft (Nat.add
  0x16bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c2175 (Nat.shiftLeft
  0x4fcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c9 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4ee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f
  (Nat.shiftLeft (Nat.add 0x18428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf9
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b90727 288)) 288)) 864)))), (273, (mkQ
  false (Nat.add (Nat.add 0xbc209f22a3f7ed3ac3d79057d5d879aa7fec7d5366710841edc7a0111d18c49e89cbc581
  (Nat.shiftLeft (Nat.add 0xe88ab8546326b9fd3f2f07e9e82dc5239ea31fd9300227e78b7c8e2902f01e93edfd986e
  (Nat.shiftLeft 0x1c1b395b24f329bca99db121d6642c1649d2aaa599b3e49bd492802d37c6f5b163cd57e9 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd4b2aaf7ba182bc484a38b6fad457b98a6f5a60499b416dea6f4d95fca5c0b87ef0d3f91 (Nat.shiftLeft (Nat.add
  0xc04959333358a2855ef553fa06924336d4b9d7056400aefd70ae532f16a91f9d98479f19 (Nat.shiftLeft
  0xa3a555bcc2db7378b19845f93586268a458bb94d8705e76a1b49272 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (275, (mkQ
  false (Nat.add (Nat.add 0x173d8eef1e5d7c0e3a7d98554f856ff75ee5b89e04aa196f91f4cd0cf88cd94d531e09b3
  (Nat.shiftLeft (Nat.add 0xab81d18cd6a3e73d0a30d82ab4feca0b046f7d54f0b60b026420eb4364b02906380f52f8
  (Nat.shiftLeft 0x85c917eca972e2151c4a94e68547283e25d0d76410dc6356c03d3a29f62970faf298247b 288))
  288)) (Nat.shiftLeft (Nat.add
  0x71485521a5f1de577a18d9b7b1e096b3dddf538fa7d9bc293cf4f36136aa2548cec5006b (Nat.shiftLeft (Nat.add
  0x32f172aa59b6453f62c4e95ea10440c65b4dee77e89f6b184b7c7076f47f7cc211454598 (Nat.shiftLeft
  0x5a7ee4de6571f6eac6f1652afd3ea1c7b606a498f2f1f82ee4ec38a 288)) 288)) 864)) (Nat.add (Nat.add
  0xa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d00000 (Nat.shiftLeft (Nat.add
  0x58ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9f (Nat.shiftLeft
  0xc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fdc
  (Nat.shiftLeft (Nat.add 0x73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea9
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49e 288)) 288)) 864))))])]

def sjsuTsp_463 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((8, 6, 0), [(72, (mkQ false (
  Nat.add (Nat.add 0x15cb035a96ad9fc4ddfb5507a9c53d09cd2001f0563317b5dc204888bb0d0e51ed358b1 (
  Nat.shiftLeft 0xf0a5c8afe4bee06be4dd3a4fe607d450784179e9da7e48c8979d87841d2585a9dce316c5 288)) (
  Nat.shiftLeft (Nat.add 0x24127bd670eff91287ef1f68b8eafe7df62f9e99265d8d2babc74c26881d1658be80fbcd
  (Nat.shiftLeft (Nat.add 0x1ea40be19210df1c432d641403b1fe95778aa41884f15b136e7018125d6eb97b0be13612
  (Nat.shiftLeft 0x20a10fe2dc615c6c224a2974add14ecfde2201226 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (108, (mkQ true (Nat.add (Nat.add
  0x4d5d9b7ed8a7b42e4a4a44d57d34f198b71333189713021739a2a26f8e23b83047850d2d (Nat.shiftLeft
  0xa37a9d27184a7fe3e5613a1ff4ffecb4097101e82d02b44b98c1703685ba6106bbc7b466 288)) (Nat.shiftLeft (
  Nat.add 0x5eb3e2d0a261fac04151455c51c39c9de7ac30e53722bfb0fd68a4345ebcc6ae307cce2d (Nat.shiftLeft
  (Nat.add 0xcb012fa9d4136c2a25506c9caab1308ac4922aced82bb620dd10fb97cde9523a94032760 (Nat.shiftLeft
  0xf7dc143fd6819beebc5440e9e331d74e813fc20c 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (144, (mkQ true (Nat.add (Nat.add
  0x144b2126a8854f90fcae8f2cfd768e33e9a73398fa5409866e859530437744f74a2e8cd5 (Nat.shiftLeft
  0x5c61a505f183c5ec47c85a9da2e854df381c68e4390f4afa8e6cd5bbb078dd28f9e7333a 288)) (Nat.shiftLeft (
  Nat.add 0xb8a6ed35b8cc22a235fc51e8ee765a0eecc09b7d63d2b159dfa9b1cd37b25526c8ae3d9a (Nat.shiftLeft
  (Nat.add 0x1c8a6a293e4d7bafe11558a9a74645d8d3296e19e1923e760b38366ca8e4dff1dbf8abe5 (Nat.shiftLeft
  0x4992964a71f9e35d5521e33476c614b43efcc48646 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576)))), (180, (mkQ true (Nat.add (Nat.add
  0xfedb27f3f28f6be9d745a2b03cdfcd3cd9acad00e14b9049d285d7340ef49f71108528e7 (Nat.shiftLeft
  0x588da1e78b8736e2a9cd57137c1b8536663441634c8bff50627fb782ce22afd3b77d8f92 288)) (Nat.shiftLeft (
  Nat.add 0x5eb8ed5ff9f77a7a367ed6b444881e4a32437e2c8357f74e70732d85fdb646dd4b5d48fd (Nat.shiftLeft
  (Nat.add 0x254a44ae40b68a9cea731ea5d74aa55901489eb390e1bcdba8956da4487240aaa822e063 (Nat.shiftLeft
  0xdfcb5c11ad4555d973554a6085c19070415e050e1 288)) 288)) 576)) (Nat.add (Nat.add
  0x1095495b8318173f2dc937b34879bd45fa193ad31d7377734d9149fea1a201bdfc400000 (Nat.shiftLeft
  0x209c2b00c1384b6aaade481fce77ff6429903921622b690979bf402dae35af877a6f856 288)) (Nat.shiftLeft (
  Nat.add 0xc14b19e391aab0d5a899cb7b8cce8fa054f4ae7a9d4580deca2f3ec2c19a738b4894b705 (Nat.shiftLeft
  (Nat.add 0xa6e33cfdb02c29ef4af46061011a2d7e860bb7d61ffc5056b6f8c6b6cb29e8bc53483c6 (Nat.shiftLeft
  0x12536f0e3bd4349d7b01ac4e555ee8492318f 288)) 288)) 576)))), (216, (mkQ true (Nat.add (Nat.add
  0x144b2126a8854f90fcae8f2cfd768e33e9a73398fa5409866e859530437744f74a2e8cd5 (Nat.shiftLeft
  0x5c61a505f183c5ec47c85a9da2e854df381c68e4390f4afa8e6cd5bbb078dd28f9e7333a 288)) (Nat.shiftLeft (
  Nat.add 0xb8a6ed35b8cc22a235fc51e8ee765a0eecc09b7d63d2b159dfa9b1cd37b25526c8ae3d9a (Nat.shiftLeft
  (Nat.add 0x1c8a6a293e4d7bafe11558a9a74645d8d3296e19e1923e760b38366ca8e4dff1dbf8abe5 (Nat.shiftLeft
  0x4992964a71f9e35d5521e33476c614b43efcc48646 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576)))), (252, (mkQ true (Nat.add (Nat.add
  0x4d5d9b7ed8a7b42e4a4a44d57d34f198b71333189713021739a2a26f8e23b83047850d2d (Nat.shiftLeft
  0xa37a9d27184a7fe3e5613a1ff4ffecb4097101e82d02b44b98c1703685ba6106bbc7b466 288)) (Nat.shiftLeft (
  Nat.add 0x5eb3e2d0a261fac04151455c51c39c9de7ac30e53722bfb0fd68a4345ebcc6ae307cce2d (Nat.shiftLeft
  (Nat.add 0xcb012fa9d4136c2a25506c9caab1308ac4922aced82bb620dd10fb97cde9523a94032760 (Nat.shiftLeft
  0xf7dc143fd6819beebc5440e9e331d74e813fc20c 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (288, (mkQ false (Nat.add (Nat.add
  0x15cb035a96ad9fc4ddfb5507a9c53d09cd2001f0563317b5dc204888bb0d0e51ed358b1 (Nat.shiftLeft
  0xf0a5c8afe4bee06be4dd3a4fe607d450784179e9da7e48c8979d87841d2585a9dce316c5 288)) (Nat.shiftLeft (
  Nat.add 0x24127bd670eff91287ef1f68b8eafe7df62f9e99265d8d2babc74c26881d1658be80fbcd (Nat.shiftLeft
  (Nat.add 0x1ea40be19210df1c432d641403b1fe95778aa41884f15b136e7018125d6eb97b0be13612 (Nat.shiftLeft
  0x20a10fe2dc615c6c224a2974add14ecfde2201226 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576))))])]


end KAM.EffectiveStability.SJSU

end
