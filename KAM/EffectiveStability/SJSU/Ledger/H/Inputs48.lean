/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs47

/-!
# Ledger inputs (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

def sjsuTsp_342 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 8, 1), [(71, (mkQ true (
  Nat.add (Nat.add 0xcaca2a330666355f6127ecfaf97f67a4869080266748f981006ad8d1a47410b0a8e0caaf (
  Nat.shiftLeft 0x3721fb1f5ce5565d41937c92cac7e0921e2f446c9c745aeed1f10fde302615b86933365b 288)) (
  Nat.shiftLeft (Nat.add 0x313e05de914e9b78b3e29fab51944ba81f0cf3e44dd0fb18fd78f7706fe0818efb1fd01a
  (Nat.shiftLeft (Nat.add 0x61b6bafe4389ca80612782a98309b0b13b2e995d4b80dad2a1b19375f26b5bf74cc4fb61
  (Nat.shiftLeft 0x1d1cbe090e5112b8bfbac75b58fec6da2b126cf2 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576)))), (107, (mkQ true (Nat.add (Nat.add
  0x6e0a49b3517917648d5fbec82f0efc28ad57882b67c072fb15a0db99eeb71a3c54567243 (Nat.shiftLeft
  0x603b9c2917654c6725613cfd9aae9b8cec585285a26632fc5587d1c4d87d43c6fb26011b 288)) (Nat.shiftLeft (
  Nat.add 0xca656380a92f464a5f6c43a93a1e2f6df797273116eb1802030cd5720300208f9608c8cc (Nat.shiftLeft
  (Nat.add 0x4867f9960b4f676602b6b8fff7ab200fee2e5a4030950f96e26c07a4bcf67d40f59f100e (Nat.shiftLeft
  0x7b0212c8942901f842c99a91654b022d11362fb0a 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (109, (mkQ true (Nat.add (Nat.add
  0x68673c9a16d9ee888182aac6bf8e00685aa8c111f0194ba135886c5e615fd0a54c5d869d (Nat.shiftLeft
  0xa565294a01ac575ce8eb9625bccbdb3224a3d59ac678f92b4911e51143b5953b4e0008a0 288)) (Nat.shiftLeft (
  Nat.add 0xbd27738efd24085adf603c53fd758a68c78ea818c8cdfa0e3999d7e31988be71204a0183 (Nat.shiftLeft
  (Nat.add 0xfc98f21ea55266376bd9995b2ca5f4300a1311ecc02348c90e52d3ab80e1550e8ef10a32 (Nat.shiftLeft
  0x105092ce202e984fa5d3cfcabc167a03872fd8787 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (143, (mkQ true (Nat.add (Nat.add
  0xea9ad5bcac1d0bddff1715c7a40752cab26963152bfece2e7d8b784a456806ee7cd12923 (Nat.shiftLeft
  0xb4d570db5287b68d61d845d3d2d43a4a5210dc7c651afea671100cd660963a8c3fd8935f 288)) (Nat.shiftLeft (
  Nat.add 0xee5c8b0082f2c6b9a8822854788110e0f7fe79478435ffd24d7b775b5ccfb0d6dd63d337 (Nat.shiftLeft
  (Nat.add 0x9f1ec7647be90dccca2cc953e7f0c35cf229f8ad9fe51e571443d67c3f088f2f3d3daba (Nat.shiftLeft
  0x1e1e47e5c26c460406046f6f68bc58de19b563dc49 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (145, (mkQ true (Nat.add (Nat.add
  0x6331739d24d1a5227eb15dff579f68a7d5b60d69f2e40f28a25673ea351713e023052e61 (Nat.shiftLeft
  0xdfd81242cf3496ac87f1d1ef59ee3ec06b83890b77236de0b363bf2eb692ed010d2f36d7 288)) (Nat.shiftLeft (
  Nat.add 0xa268367eba0b809ee94968f2df4faaa7eacc9952af24f994162a569e570f66edde1d51c1 (Nat.shiftLeft
  (Nat.add 0xd2324c67ccea72081eeb5c17e8bc95ece126d34360706c2c6484f57dd12ec51054a29866 (Nat.shiftLeft
  0x3fb54d62cbbf469dffdff660c4596eab04c77c72b 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576)))), (179, (mkQ true (Nat.add (Nat.add
  0x4b84d21c6405e26d60265bd3cd3829ab5e33321d6c555a82ad7739687753109424394b71 (Nat.shiftLeft
  0xeb75664ebe9020411848e7599a7d4a2383cabf5182995f2d1e993a6494a17f1a7e92d99f 288)) (Nat.shiftLeft (
  Nat.add 0x3489873af8674b719404f7451a353860f2a0345deb714b25b64b453ad52aebfe4f1bf009 (Nat.shiftLeft
  (Nat.add 0x8adfaa4e16370f10f11927fca0e8ceb622c3797342905201daf8847f25a1f13a78de03a8 (Nat.shiftLeft
  0xbf54aef4d2f32b33b93ba586e62bfc06d3b66586 288)) 288)) 576)) (Nat.add (Nat.add
  0x40776de2cf4678ff57d42c8f6d2e3104c8142f0f4ac2c5f5d7a76e654e1b3497fd000000 (Nat.shiftLeft
  0x6807cef33cdc6a2bbbbe5067fd85fff83547360e781bc5407949900248b5e2605fb8c6ab 288)) (Nat.shiftLeft (
  Nat.add 0xcdd5ae4fa7bbc0aaed47d5fc70a53fb3772a252ee4379a4bd4f2989bce15293c3a10926a (Nat.shiftLeft
  (Nat.add 0x6ebe8fd97c02354bf6f29e6b400e1bdfed1a2f9781996a6abc593d22bd5bb2096a90696b (Nat.shiftLeft
  0xea925a4fca9c3b12f3489d8444bed074f472 288)) 288)) 576)))), (181, (mkQ true (Nat.add (Nat.add
  0x4b84d21c6405e26d60265bd3cd3829ab5e33321d6c555a82ad7739687753109424394b71 (Nat.shiftLeft
  0xeb75664ebe9020411848e7599a7d4a2383cabf5182995f2d1e993a6494a17f1a7e92d99f 288)) (Nat.shiftLeft (
  Nat.add 0x3489873af8674b719404f7451a353860f2a0345deb714b25b64b453ad52aebfe4f1bf009 (Nat.shiftLeft
  (Nat.add 0x8adfaa4e16370f10f11927fca0e8ceb622c3797342905201daf8847f25a1f13a78de03a8 (Nat.shiftLeft
  0xbf54aef4d2f32b33b93ba586e62bfc06d3b66586 288)) 288)) 576)) (Nat.add (Nat.add
  0x40776de2cf4678ff57d42c8f6d2e3104c8142f0f4ac2c5f5d7a76e654e1b3497fd000000 (Nat.shiftLeft
  0x6807cef33cdc6a2bbbbe5067fd85fff83547360e781bc5407949900248b5e2605fb8c6ab 288)) (Nat.shiftLeft (
  Nat.add 0xcdd5ae4fa7bbc0aaed47d5fc70a53fb3772a252ee4379a4bd4f2989bce15293c3a10926a (Nat.shiftLeft
  (Nat.add 0x6ebe8fd97c02354bf6f29e6b400e1bdfed1a2f9781996a6abc593d22bd5bb2096a90696b (Nat.shiftLeft
  0xea925a4fca9c3b12f3489d8444bed074f472 288)) 288)) 576)))), (215, (mkQ true (Nat.add (Nat.add
  0x6331739d24d1a5227eb15dff579f68a7d5b60d69f2e40f28a25673ea351713e023052e61 (Nat.shiftLeft
  0xdfd81242cf3496ac87f1d1ef59ee3ec06b83890b77236de0b363bf2eb692ed010d2f36d7 288)) (Nat.shiftLeft (
  Nat.add 0xa268367eba0b809ee94968f2df4faaa7eacc9952af24f994162a569e570f66edde1d51c1 (Nat.shiftLeft
  (Nat.add 0xd2324c67ccea72081eeb5c17e8bc95ece126d34360706c2c6484f57dd12ec51054a29866 (Nat.shiftLeft
  0x3fb54d62cbbf469dffdff660c4596eab04c77c72b 288)) 288)) 576)) (Nat.add (Nat.add
  0xa5d4dd931ef0e877c9dc2d00d4c164bbc4fc4c3f2682aa8107ace3f25054116bda800000 (Nat.shiftLeft
  0x14619ae078c32f22aacaed13e10aff9e99fa23b4dd5b21a5ec17881c8ce18db4ac85b35c 288)) (Nat.shiftLeft (
  Nat.add 0x8cef02e3b0aae8589601f2d380119c43518ed0ca24b708b3e5d8739b90088370d5cf2632 (Nat.shiftLeft
  (Nat.add 0x684e061e8e1b9a358ed8bc3ca0b05c6f13c752e5d3fdb236325b7c323efa3175b40d25c3 (Nat.shiftLeft
  0xb742568e564a0e26ce10bb0f55b512db5ef96 288)) 288)) 576)))), (217, (mkQ true (Nat.add (Nat.add
  0xea9ad5bcac1d0bddff1715c7a40752cab26963152bfece2e7d8b784a456806ee7cd12923 (Nat.shiftLeft
  0xb4d570db5287b68d61d845d3d2d43a4a5210dc7c651afea671100cd660963a8c3fd8935f 288)) (Nat.shiftLeft (
  Nat.add 0xee5c8b0082f2c6b9a8822854788110e0f7fe79478435ffd24d7b775b5ccfb0d6dd63d337 (Nat.shiftLeft
  (Nat.add 0x9f1ec7647be90dccca2cc953e7f0c35cf229f8ad9fe51e571443d67c3f088f2f3d3daba (Nat.shiftLeft
  0x1e1e47e5c26c460406046f6f68bc58de19b563dc49 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (251, (mkQ true (Nat.add (Nat.add
  0x68673c9a16d9ee888182aac6bf8e00685aa8c111f0194ba135886c5e615fd0a54c5d869d (Nat.shiftLeft
  0xa565294a01ac575ce8eb9625bccbdb3224a3d59ac678f92b4911e51143b5953b4e0008a0 288)) (Nat.shiftLeft (
  Nat.add 0xbd27738efd24085adf603c53fd758a68c78ea818c8cdfa0e3999d7e31988be71204a0183 (Nat.shiftLeft
  (Nat.add 0xfc98f21ea55266376bd9995b2ca5f4300a1311ecc02348c90e52d3ab80e1550e8ef10a32 (Nat.shiftLeft
  0x105092ce202e984fa5d3cfcabc167a03872fd8787 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (253, (mkQ true (Nat.add (Nat.add
  0x6e0a49b3517917648d5fbec82f0efc28ad57882b67c072fb15a0db99eeb71a3c54567243 (Nat.shiftLeft
  0x603b9c2917654c6725613cfd9aae9b8cec585285a26632fc5587d1c4d87d43c6fb26011b 288)) (Nat.shiftLeft (
  Nat.add 0xca656380a92f464a5f6c43a93a1e2f6df797273116eb1802030cd5720300208f9608c8cc (Nat.shiftLeft
  (Nat.add 0x4867f9960b4f676602b6b8fff7ab200fee2e5a4030950f96e26c07a4bcf67d40f59f100e (Nat.shiftLeft
  0x7b0212c8942901f842c99a91654b022d11362fb0a 288)) 288)) 576)) (Nat.add (Nat.add
  0x9753764c7bc3a1df2770b403530592ef13f130fc9a0aaa041eb38fc9415045af6a000000 (Nat.shiftLeft
  0x51866b81e30cbc8aab2bb44f842bfe7a67e88ed3756c8697b05e2072338636d2b216cd72 288)) (Nat.shiftLeft (
  Nat.add 0x33bc0b8ec2aba1625807cb4e0046710d463b432892dc22cf9761ce6e40220dc3573c98c8 (Nat.shiftLeft
  (Nat.add 0xa138187a386e68d63b62f0f282c171bc4f1d4b974ff6c8d8c96df0c8fbe8c5d6d034970e (Nat.shiftLeft
  0x2dd095a395928389b3842ec3d56d44b6d7be59 288)) 288)) 576)))), (289, (mkQ true (Nat.add (Nat.add
  0xcaca2a330666355f6127ecfaf97f67a4869080266748f981006ad8d1a47410b0a8e0caaf (Nat.shiftLeft
  0x3721fb1f5ce5565d41937c92cac7e0921e2f446c9c745aeed1f10fde302615b86933365b 288)) (Nat.shiftLeft (
  Nat.add 0x313e05de914e9b78b3e29fab51944ba81f0cf3e44dd0fb18fd78f7706fe0818efb1fd01a (Nat.shiftLeft
  (Nat.add 0x61b6bafe4389ca80612782a98309b0b13b2e995d4b80dad2a1b19375f26b5bf74cc4fb61 (Nat.shiftLeft
  0x1d1cbe090e5112b8bfbac75b58fec6da2b126cf2 288)) 288)) 576)) (Nat.add (Nat.add
  0x4ba9bb263de1d0ef93b85a01a982c97789f8987e4d0555020f59c7e4a0a822d7b5000000 (Nat.shiftLeft
  0x28c335c0f1865e455595da27c215ff3d33f44769bab6434bd82f103919c31b69590b66b9 288)) (Nat.shiftLeft (
  Nat.add 0x19de05c76155d0b12c03e5a700233886a31da194496e1167cbb0e737201106e1ab9e4c64 (Nat.shiftLeft
  (Nat.add 0xd09c0c3d1c37346b1db178794160b8de278ea5cba7fb646c64b6f8647df462eb681a4b87 (Nat.shiftLeft
  0x16e84ad1cac941c4d9c21761eab6a25b6bdf2c 288)) 288)) 576))))])]

def sjsuTsp_343 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 8, 3), [(33, (mkQ false (
  Nat.add (Nat.add 0x104eec60c7a36076bef5435f3c9b52083fcc898b528f3c932b65d02bbc2a022c099d051f (
  Nat.shiftLeft (Nat.add 0x7b3715a8ed948905f238ba5f277dd42825645254b4dbbc9ff08ddedeabca6478823fb322
  (Nat.shiftLeft 0xca3eb646c171acf3324e17d92b302bbebd2b46d8f1f2e88437bf3728819574676e18245c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x199e9cfad1d00209820928e571c55a78d6b7b8468a99a15f93a54a58b7d5c5701190ea82 (Nat.shiftLeft (Nat.add
  0x274fecd74be0742b1a2ba9ed15be29b45636a9e898ddda46b7472de92751bc79fd238ae3 (Nat.shiftLeft
  0x1caa7391920 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (69, (mkQ false (Nat.add (Nat.add
  0x6f1fdf27f9dd00b79ea674d70191ca9a0b566e22aa029b8b48c24576f4ea7fdc6d326de7 (Nat.shiftLeft (Nat.add
  0x5ef430651f707f2a09dd7bc2293eefad227eb4b6002b985fcb86d5d094fb3653f05ccfaf (Nat.shiftLeft
  0x2a61a171bf96f9de58408c1aa9133763721bcc79f2e14f58235ca36858cd03dba53b1d82 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7865aaa71438dd9129dff7fd4da681d89ea7573ab82b6f02e1d35298aef11ba0496bfb5d
  (Nat.shiftLeft (Nat.add 0x1a3fe6f266a41827de128c9963a5bad4c9cf08a72db10cfd3b6c1df9129d06fb17f9d53c
  (Nat.shiftLeft 0xea9e3d672e8 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (71, (mkQ false (Nat.add (Nat.add
  0xcf4ebdba9cf015e6d8bdc408d1883e9c647042c9c0fffb754a1ac09553fc19d85ce54beb (Nat.shiftLeft (Nat.add
  0x3b514ed089e99f381808d5c535b6b9c7c2f8f379e7de2da5cbf5e225d3c04dfa97b132cb (Nat.shiftLeft
  0x34c632cc148d0f19402121adcad07177bd4b824055fe28ae1fa0434ef7893745c93f601 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb27966a03e3d6ba8c9625fb0d80182bfb8d327578d87fe16c84ed9a6331605dc4553c598
  (Nat.shiftLeft (Nat.add 0x404afc7a65e220021f446d91ba61359dbe0d5fdd52526ffcab830210bfba6aaec0bdb39a
  (Nat.shiftLeft 0x43eef086863 288)) 288)) 864)) (Nat.add (Nat.add
  0xb863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a00000 (Nat.shiftLeft (Nat.add
  0xf02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c7 (Nat.shiftLeft
  0x1416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179cf 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a7
  (Nat.shiftLeft (Nat.add 0x65805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b22
  (Nat.shiftLeft 0x30fb194 288)) 288)) 864)))), (105, (mkQ false (Nat.add (Nat.add
  0x9c171fb1201f585390d9c1bcb8053359582e374fb616c5aa4b3783fd55d28562ffd2cce3 (Nat.shiftLeft (Nat.add
  0x571d1a5f8cd70bfc50453d34019ff686bbd36449cff7ca290c308a140f7141ea858d5f5c (Nat.shiftLeft
  0x441b16984e4032376c4748574468dbd2dcb9d9d67881959d36d6ff09547ff6feccef2c45 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5cbf33348b749cf8cbda7168d4a91b67c0e84433bee76fbd9ff096db36ff3949931d2e29
  (Nat.shiftLeft (Nat.add 0x5bbe29d54b403350704a427690ea4723aa98bb373cd946643415913b67b0fd5bb2c80915
  (Nat.shiftLeft 0x40a56fc0589b 288)) 288)) 864)) (Nat.add (Nat.add
  0xb863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a00000 (Nat.shiftLeft (Nat.add
  0xf02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c7 (Nat.shiftLeft
  0x1416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179cf 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a7
  (Nat.shiftLeft (Nat.add 0x65805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b22
  (Nat.shiftLeft 0x30fb194 288)) 288)) 864)))), (107, (mkQ false (Nat.add (Nat.add
  0xb1a92609dab9c663d311b735205453cd886db312e1f61106be88bf6fc21d03c8be3b8af3 (Nat.shiftLeft (Nat.add
  0x72391eb5780c01fa8c93b39569cce4b707b1c2a68e5493222d242666b15c50bb3ab0fa9 (Nat.shiftLeft
  0xdc58653e43cc844d14edb385be309e0d9f55da7dfca3ea381ea5299510c673bea159e9f7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7f35793120295fddf1faf1af6cdabfe76697b87fad4e20bf9270c5d9816a0b3042805397
  (Nat.shiftLeft (Nat.add 0xe6aa765fed2c4b102a786addb963aebc21a126d181c977f498f86cf49aa7bab9a5173ed5
  (Nat.shiftLeft 0x15023e207ca7f 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (109, (mkQ false (Nat.add (Nat.add
  0xbef389d45234d16e3df8333d90cf3caa7e05ef42dd8201bc40f2d19dbf99b19cbcc0bab3 (Nat.shiftLeft (Nat.add
  0xa8eb50ad0926793db86c1030035c66c0b43822d43b98e534f79c748568d46f328c1df20f (Nat.shiftLeft
  0x51d04b29bd3ea18b6949a19c02fb9ab892fa235f375ec1b65b0d6a915a08919a0d83f066 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x21a444605488e0d1642b41822f1ef7b78823411e781aa9723bae83d494472f03b552f504
  (Nat.shiftLeft (Nat.add 0x720967c6918ecebbfeada0b5e5be7135f4a0b19197e86503916c77487ba41688dfae28c
  (Nat.shiftLeft 0x48e202a6bfc0 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (141, (mkQ false (Nat.add (Nat.add
  0xba24f39922081f3dd4c36439ad8829c5975e4452e5358bcc3cb5de0741922fc7f67d1c91 (Nat.shiftLeft (Nat.add
  0x7f9c94dcfd1395317a04a5e3f3b921427df1ba84e3302b153c11efabb826148ffd2bd4f7 (Nat.shiftLeft
  0xe287785346ca583aa501ef42c0644b417e6b1ef7e37e4fe5b5347bea2af9de1429d73cd0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe66e2b233fe12ccca3a46f20c7f4622ba7be3f242e53a08c7ff9017b1cfa8c58b294559b
  (Nat.shiftLeft (Nat.add 0x7185366013fcb2e77024f1847254f74dc39acc90e5c750dd6e80c9ecfa6e54b09a7ed37a
  (Nat.shiftLeft 0x22b40070ddfc9 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (143, (mkQ false (Nat.add (Nat.add
  0xb62e355c48d139c98525f26e989818bc9165fb470e72f351b7f4f6bf5c8dd79fd1e53f59 (Nat.shiftLeft (Nat.add
  0x354a43ce827dc628020a94bcb343b9f19f60acde876cb756c348d162eb5feb8c22d2444a (Nat.shiftLeft
  0x2e22127d01dfb703090be02bb59778e3e6a693639038bf0b52ac0e52ba285e2bf2534cb8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x50c0a7015f95ed3ed93744a8c5cbba9707cbd2cd9309ef31f33e7d203d9db27aa12bb2bf
  (Nat.shiftLeft (Nat.add 0x1280d92c3457257def8d678514372bec0283e81f9043417baf7bd8ae75195f6e239846a6
  (Nat.shiftLeft 0x7723179a2e27b 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (145, (mkQ false (Nat.add (Nat.add
  0xae14e10b9910de234b1e2ce470c4357a02ac20d0670cdde94a0a7e5998013a9aed506235 (Nat.shiftLeft (Nat.add
  0xea7a2f915091e138be414b21aca7b31c8068faccdbfc796b8f70bb781395b80a0aa6393b (Nat.shiftLeft
  0xbe252f2dc4d732acb373df5feb9943b074d54bb292c5b97d3bf870eb9e7a7483a19875f5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x46f4a8256fc9076028ff9f85ffbf53af7dbc1c799ba368036acf0be330b4d306c61ba67c
  (Nat.shiftLeft (Nat.add 0xbc2d7790ae99f3d99ae2a1074cbd28ffc83f5ade576ea4c35461e57fc1e8865a72511a57
  (Nat.shiftLeft 0x2c1ae22581dd8 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (147, (mkQ false (Nat.add (Nat.add
  0x59fbdc4021702d7de8030349c098946ac7ef0dfb6b6b04e9e09206aa1ad8a9bce860a9ed (Nat.shiftLeft (Nat.add
  0x7182c665234b1e15b340abd059e44fa1093aaf46ef16d4112e1c78978c3663195b916aa0 (Nat.shiftLeft
  0x24602bba2951086f3f738738997bcf281de0e84dff0cb01524375b929a1b1fcffda536bd 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x55e2b8135b350a1c00b11a31c92bee94f7a5680425eb2d9f59988fe4deb223aede670f67
  (Nat.shiftLeft (Nat.add 0x48da9564c149de149dae93b667f45b6e34dc0ebb1bd21777b8112726c8b0f36ccaf77fed
  (Nat.shiftLeft 0x25cc3b16473f 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (177, (mkQ false (Nat.add (Nat.add
  0x74b724263072d1df6489700507e7aaee24e2ac22033e016928dd57457e64889e32178cfd (Nat.shiftLeft (Nat.add
  0xa7dfad15d3bb13d67c9aa47345c940f12914017da6f80516279318f6cabeba694f7f00c (Nat.shiftLeft
  0x2aecccae2bc0ba243bddc9eb72cf92e60c1b33e92f155e01df1db5c5711c0d355964511c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9f9b56563d2c0c564c94ebd963ac48c422944fd8ee99b1c5dbb1a5d12413f425d883051e
  (Nat.shiftLeft (Nat.add 0x18e9250ef64cbedbae506e9b4e7e2da80816defb4f210bcd8d2b000516de7ba69e636673
  (Nat.shiftLeft 0xefd7f08ef114 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (179, (mkQ false (Nat.add (Nat.add
  0xba85651481a97c39137ddb63fab182ce8ed31b2486a87658581ad887f848f86bab47ab1d (Nat.shiftLeft (Nat.add
  0xf964c630fa75f1094bb68b2a4fc8b30d3e9916d964c229109af94945697ce5e48b5a03f3 (Nat.shiftLeft
  0xb7ec4720a1aa416ed8d54f787b9d83d2085fc0011d22a693127190e4528daf06c29a00c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5244b1dc84e74f27c6ddff36d03c0a342dfa32943200c1d611c98249e5e28a705c870b82
  (Nat.shiftLeft (Nat.add 0xdc647a4604176332299c7af0f465185bd4c8588902eee6468c3b59acf6fd7e78351d8c33
  (Nat.shiftLeft 0x709e45fb4149 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (181, (mkQ false (Nat.add (Nat.add
  0xba85651481a97c39137ddb63fab182ce8ed31b2486a87658581ad887f848f86bab47ab1d (Nat.shiftLeft (Nat.add
  0xf964c630fa75f1094bb68b2a4fc8b30d3e9916d964c229109af94945697ce5e48b5a03f3 (Nat.shiftLeft
  0xb7ec4720a1aa416ed8d54f787b9d83d2085fc0011d22a693127190e4528daf06c29a00c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5244b1dc84e74f27c6ddff36d03c0a342dfa32943200c1d611c98249e5e28a705c870b82
  (Nat.shiftLeft (Nat.add 0xdc647a4604176332299c7af0f465185bd4c8588902eee6468c3b59acf6fd7e78351d8c33
  (Nat.shiftLeft 0x709e45fb4149 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (183, (mkQ false (Nat.add (Nat.add
  0x74b724263072d1df6489700507e7aaee24e2ac22033e016928dd57457e64889e32178cfd (Nat.shiftLeft (Nat.add
  0xa7dfad15d3bb13d67c9aa47345c940f12914017da6f80516279318f6cabeba694f7f00c (Nat.shiftLeft
  0x2aecccae2bc0ba243bddc9eb72cf92e60c1b33e92f155e01df1db5c5711c0d355964511c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9f9b56563d2c0c564c94ebd963ac48c422944fd8ee99b1c5dbb1a5d12413f425d883051e
  (Nat.shiftLeft (Nat.add 0x18e9250ef64cbedbae506e9b4e7e2da80816defb4f210bcd8d2b000516de7ba69e636673
  (Nat.shiftLeft 0xefd7f08ef114 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (213, (mkQ false (Nat.add (Nat.add
  0x59fbdc4021702d7de8030349c098946ac7ef0dfb6b6b04e9e09206aa1ad8a9bce860a9ed (Nat.shiftLeft (Nat.add
  0x7182c665234b1e15b340abd059e44fa1093aaf46ef16d4112e1c78978c3663195b916aa0 (Nat.shiftLeft
  0x24602bba2951086f3f738738997bcf281de0e84dff0cb01524375b929a1b1fcffda536bd 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x55e2b8135b350a1c00b11a31c92bee94f7a5680425eb2d9f59988fe4deb223aede670f67
  (Nat.shiftLeft (Nat.add 0x48da9564c149de149dae93b667f45b6e34dc0ebb1bd21777b8112726c8b0f36ccaf77fed
  (Nat.shiftLeft 0x25cc3b16473f 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (215, (mkQ false (Nat.add (Nat.add
  0xae14e10b9910de234b1e2ce470c4357a02ac20d0670cdde94a0a7e5998013a9aed506235 (Nat.shiftLeft (Nat.add
  0xea7a2f915091e138be414b21aca7b31c8068faccdbfc796b8f70bb781395b80a0aa6393b (Nat.shiftLeft
  0xbe252f2dc4d732acb373df5feb9943b074d54bb292c5b97d3bf870eb9e7a7483a19875f5 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x46f4a8256fc9076028ff9f85ffbf53af7dbc1c799ba368036acf0be330b4d306c61ba67c
  (Nat.shiftLeft (Nat.add 0xbc2d7790ae99f3d99ae2a1074cbd28ffc83f5ade576ea4c35461e57fc1e8865a72511a57
  (Nat.shiftLeft 0x2c1ae22581dd8 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (217, (mkQ false (Nat.add (Nat.add
  0xb62e355c48d139c98525f26e989818bc9165fb470e72f351b7f4f6bf5c8dd79fd1e53f59 (Nat.shiftLeft (Nat.add
  0x354a43ce827dc628020a94bcb343b9f19f60acde876cb756c348d162eb5feb8c22d2444a (Nat.shiftLeft
  0x2e22127d01dfb703090be02bb59778e3e6a693639038bf0b52ac0e52ba285e2bf2534cb8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x50c0a7015f95ed3ed93744a8c5cbba9707cbd2cd9309ef31f33e7d203d9db27aa12bb2bf
  (Nat.shiftLeft (Nat.add 0x1280d92c3457257def8d678514372bec0283e81f9043417baf7bd8ae75195f6e239846a6
  (Nat.shiftLeft 0x7723179a2e27b 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (219, (mkQ false (Nat.add (Nat.add
  0xba24f39922081f3dd4c36439ad8829c5975e4452e5358bcc3cb5de0741922fc7f67d1c91 (Nat.shiftLeft (Nat.add
  0x7f9c94dcfd1395317a04a5e3f3b921427df1ba84e3302b153c11efabb826148ffd2bd4f7 (Nat.shiftLeft
  0xe287785346ca583aa501ef42c0644b417e6b1ef7e37e4fe5b5347bea2af9de1429d73cd0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xe66e2b233fe12ccca3a46f20c7f4622ba7be3f242e53a08c7ff9017b1cfa8c58b294559b
  (Nat.shiftLeft (Nat.add 0x7185366013fcb2e77024f1847254f74dc39acc90e5c750dd6e80c9ecfa6e54b09a7ed37a
  (Nat.shiftLeft 0x22b40070ddfc9 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (251, (mkQ false (Nat.add (Nat.add
  0xbef389d45234d16e3df8333d90cf3caa7e05ef42dd8201bc40f2d19dbf99b19cbcc0bab3 (Nat.shiftLeft (Nat.add
  0xa8eb50ad0926793db86c1030035c66c0b43822d43b98e534f79c748568d46f328c1df20f (Nat.shiftLeft
  0x51d04b29bd3ea18b6949a19c02fb9ab892fa235f375ec1b65b0d6a915a08919a0d83f066 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x21a444605488e0d1642b41822f1ef7b78823411e781aa9723bae83d494472f03b552f504
  (Nat.shiftLeft (Nat.add 0x720967c6918ecebbfeada0b5e5be7135f4a0b19197e86503916c77487ba41688dfae28c
  (Nat.shiftLeft 0x48e202a6bfc0 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (253, (mkQ false (Nat.add (Nat.add
  0xb1a92609dab9c663d311b735205453cd886db312e1f61106be88bf6fc21d03c8be3b8af3 (Nat.shiftLeft (Nat.add
  0x72391eb5780c01fa8c93b39569cce4b707b1c2a68e5493222d242666b15c50bb3ab0fa9 (Nat.shiftLeft
  0xdc58653e43cc844d14edb385be309e0d9f55da7dfca3ea381ea5299510c673bea159e9f7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7f35793120295fddf1faf1af6cdabfe76697b87fad4e20bf9270c5d9816a0b3042805397
  (Nat.shiftLeft (Nat.add 0xe6aa765fed2c4b102a786addb963aebc21a126d181c977f498f86cf49aa7bab9a5173ed5
  (Nat.shiftLeft 0x15023e207ca7f 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (255, (mkQ false (Nat.add (Nat.add
  0x9c171fb1201f585390d9c1bcb8053359582e374fb616c5aa4b3783fd55d28562ffd2cce3 (Nat.shiftLeft (Nat.add
  0x571d1a5f8cd70bfc50453d34019ff686bbd36449cff7ca290c308a140f7141ea858d5f5c (Nat.shiftLeft
  0x441b16984e4032376c4748574468dbd2dcb9d9d67881959d36d6ff09547ff6feccef2c45 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x5cbf33348b749cf8cbda7168d4a91b67c0e84433bee76fbd9ff096db36ff3949931d2e29
  (Nat.shiftLeft (Nat.add 0x5bbe29d54b403350704a427690ea4723aa98bb373cd946643415913b67b0fd5bb2c80915
  (Nat.shiftLeft 0x40a56fc0589b 288)) 288)) 864)) (Nat.add (Nat.add
  0xb863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a00000 (Nat.shiftLeft (Nat.add
  0xf02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c7 (Nat.shiftLeft
  0x1416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179cf 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a7
  (Nat.shiftLeft (Nat.add 0x65805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b22
  (Nat.shiftLeft 0x30fb194 288)) 288)) 864)))), (289, (mkQ false (Nat.add (Nat.add
  0xcf4ebdba9cf015e6d8bdc408d1883e9c647042c9c0fffb754a1ac09553fc19d85ce54beb (Nat.shiftLeft (Nat.add
  0x3b514ed089e99f381808d5c535b6b9c7c2f8f379e7de2da5cbf5e225d3c04dfa97b132cb (Nat.shiftLeft
  0x34c632cc148d0f19402121adcad07177bd4b824055fe28ae1fa0434ef7893745c93f601 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb27966a03e3d6ba8c9625fb0d80182bfb8d327578d87fe16c84ed9a6331605dc4553c598
  (Nat.shiftLeft (Nat.add 0x404afc7a65e220021f446d91ba61359dbe0d5fdd52526ffcab830210bfba6aaec0bdb39a
  (Nat.shiftLeft 0x43eef086863 288)) 288)) 864)) (Nat.add (Nat.add
  0xb863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a00000 (Nat.shiftLeft (Nat.add
  0xf02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c7 (Nat.shiftLeft
  0x1416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179cf 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a7
  (Nat.shiftLeft (Nat.add 0x65805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b22
  (Nat.shiftLeft 0x30fb194 288)) 288)) 864)))), (291, (mkQ false (Nat.add (Nat.add
  0x6f1fdf27f9dd00b79ea674d70191ca9a0b566e22aa029b8b48c24576f4ea7fdc6d326de7 (Nat.shiftLeft (Nat.add
  0x5ef430651f707f2a09dd7bc2293eefad227eb4b6002b985fcb86d5d094fb3653f05ccfaf (Nat.shiftLeft
  0x2a61a171bf96f9de58408c1aa9133763721bcc79f2e14f58235ca36858cd03dba53b1d82 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x7865aaa71438dd9129dff7fd4da681d89ea7573ab82b6f02e1d35298aef11ba0496bfb5d
  (Nat.shiftLeft (Nat.add 0x1a3fe6f266a41827de128c9963a5bad4c9cf08a72db10cfd3b6c1df9129d06fb17f9d53c
  (Nat.shiftLeft 0xea9e3d672e8 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (327, (mkQ false (Nat.add (Nat.add
  0x104eec60c7a36076bef5435f3c9b52083fcc898b528f3c932b65d02bbc2a022c099d051f (Nat.shiftLeft (Nat.add
  0x7b3715a8ed948905f238ba5f277dd42825645254b4dbbc9ff08ddedeabca6478823fb322 (Nat.shiftLeft
  0xca3eb646c171acf3324e17d92b302bbebd2b46d8f1f2e88437bf3728819574676e18245c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x199e9cfad1d00209820928e571c55a78d6b7b8468a99a15f93a54a58b7d5c5701190ea82
  (Nat.shiftLeft (Nat.add 0x274fecd74be0742b1a2ba9ed15be29b45636a9e898ddda46b7472de92751bc79fd238ae3
  (Nat.shiftLeft 0x1caa7391920 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864))))])]

def sjsuTsp_344 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 8, 5), [(31, (mkQ true (
  Nat.add (Nat.add 0x2d97cb948aaeb0dd9936efcac1cce28316689ab3214a183aa8fe0b238b2fbef0ff006e6b (
  Nat.shiftLeft (Nat.add 0x914739b6b82887fa7ad37e8e45f9957633b34abec30f4a214191ba0a8bd5fcb030988113
  (Nat.shiftLeft 0x5a2d7be0e7d68b86834eb028db0fb0c11ec5ad6718adf89fc041e91065a30bf5ecb3344c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x85fd2b7943f5c116d4a1afee5eeb24c62117c12cb99c8cc56f0edde251e64394233a8c6f (Nat.shiftLeft (Nat.add
  0x3ceca07c36455f633677e8b8b4586f42c14936da9abe7c7ab078150646c195da5c920286 (Nat.shiftLeft
  0x6c8ed03eb96536b55e4c7401aa843fa95bd50d7324b2af412258c5 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (33, (mkQ
  false (Nat.add (Nat.add 0xecf4c90de9d03f5c35bb58bc4e09c988a3fb6fc36a76bf9d10352ca78160bd03a70c0ff1
  (Nat.shiftLeft (Nat.add 0xe1c68a151c358047a48085d6d65995e3d969567e5572cd12b0ae4ec408b575d05b96524f
  (Nat.shiftLeft 0x23946f55b386b8b4ef80977dbadd2a0c4ca7788e5254c14a29abae68aabb6488354aa074 288))
  288)) (Nat.shiftLeft (Nat.add
  0x8dc8b8a8bad6bece2f7d7dd5148a9049c0cf76f72026be6e68c5d6d976c0e72fbd7c359c (Nat.shiftLeft (Nat.add
  0x11f5de84b95229a1380181c8e77d366bfb4b5ae57661786afa3ea74f38704f5d5a4d7a0d (Nat.shiftLeft
  0x23c0189187d873f980e7e6f5cc504bef02de30a3194018db5eb05 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (67, (mkQ
  false (Nat.add (Nat.add 0xe07106b66a7e2683cb40081ead2a66268d597bada4dace3181ad1e1060c3237214bd87b7
  (Nat.shiftLeft (Nat.add 0xc091eaaa88edbd801d7f6a4fad52b1e87a2034a35d8fd45952b191acb27b53c198746b7c
  (Nat.shiftLeft 0x1c45d62645c32e7038bf5439a2a008bffa944ff1d16405c8d5aac2d27bc88f9a7de0f6a2 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdf812195694a986a6798c3df10c11696252ff2add6ca566bbc2bfaf7ac99ad0ee7374673 (Nat.shiftLeft (Nat.add
  0x125a59cfb49133e44a568bf2a54602c32bc81cd1abfe98fc9ceb2505d98c545116fee08a (Nat.shiftLeft
  0x31ab4215488448461556b9ba1e227a9e11d376ae14a8703f0a52560 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (69, (mkQ
  true (Nat.add (Nat.add 0xe6d8d8fda0fd2cfbb2a93e68c31d382a6dd2ad16143a907aa3a6d74708949e3f951724c1
  (Nat.shiftLeft (Nat.add 0xd55929d1328964cf639410ea0f4b368052634801879690e0c6c0ad85710a115078eb370a
  (Nat.shiftLeft 0xf6f5b3fd48544c91a524cac5bbfec055f3a89c87755efd82307d06c1a7ed13cb767e435e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x64c21fbe8c2b26cda905ee8d0feb7f337065ce452604bcb4b2baed91615957f811d8cef4 (Nat.shiftLeft (Nat.add
  0xef5bf3aec4470678d45c2cfc0b8c0ae9557aaeaded52c2d55c54aa125920ff7ab4b52ccf (Nat.shiftLeft
  0x81ab79205772ac1c82435ce9dde1583d891c003b6dbc52f8cba1cd 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (71, (mkQ
  false (Nat.add (Nat.add 0xaa5ba60ea9622f6caa3f29727cdf408f07507b2cbbf65ea9ca81e8cd18a84a4211670875
  (Nat.shiftLeft (Nat.add 0xa37fcff87dd5cd22e8199a90056bd79dcff37f14f582524793a532159af491ec1dea4e6f
  (Nat.shiftLeft 0x92e5ae28c7fd83aa27283f277f59e4542f0f1ce66f0e16dc607b2991862f982f81ed50f9 288))
  288)) (Nat.shiftLeft (Nat.add
  0x487c2ce653acbaa20e2d1db671e3ca24b37d57583c19183efc8335c78bb0c5111b60186d (Nat.shiftLeft (Nat.add
  0x9443b38ad9b7e210beddf349df433a5b3461c0d58a2b45e30bf6b108701d003c024acc27 (Nat.shiftLeft
  0xf107c288c790a3cd8657101f03c8165ee3425df372b75a52ebfdc 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (103, (mkQ
  false (Nat.add (Nat.add 0x88e4cc6d7eb278f1f552d495279a52e38a282a856a13462e508dd2ce3989783cff10d35b
  (Nat.shiftLeft (Nat.add 0x9b6552b17bf80dc340d59ebd1dd28097df148a1643b83a4a989b21950dd69c7ca76f909d
  (Nat.shiftLeft 0xc2535184985603f90eb2351ce39c2669742209b898bf5dbd881a0f6eb90ef5a2f5202425 288))
  288)) (Nat.shiftLeft (Nat.add
  0xbb0430bb1f04c9f83e2c5785526f769c946b92d81a2b584c8f1e4dedc7f79da56bc658c2 (Nat.shiftLeft (Nat.add
  0x6fc7e26992a65fdff6924b0eb3ff39d0bc0889cf3615153f1afb7ba67e5fcdb3cad451f7 (Nat.shiftLeft
  0x268f33259dc1d23a9bf6037e66b47d78bc76d27c0eb3349f7f545cb 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (105, (mkQ
  false (Nat.add (Nat.add 0xfe3372d7436c36c20952708615fd135ed5758d68e9893bea2f5eaecdc292f44d37b86913
  (Nat.shiftLeft (Nat.add 0x26cf4bcf4d0b5af8c016be6e7c5e951597697ce188ea234ec816ea88a8959eb1617eb2de
  (Nat.shiftLeft 0x8d70cc27801ec5b5a4d3025239be2fdea196fec27c91f3e00515ca4122a201dd39142bbc 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6e86ac4603304767bad27ee44188dcb90ac9df67af75eeb9b82cf51e877e54e3d075a82e (Nat.shiftLeft (Nat.add
  0x76ff09b72fa5547e00629ae6534fc36cdb1e9a4e1cd0238d6b5943cca8c0d3de08a205a4 (Nat.shiftLeft
  0x34db6dc418c071c17d7fc9bdda477dc7fbaff651d6cabed31638f4e 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (107, (mkQ
  true (Nat.add (Nat.add 0x27fce8ef9bf5255b1d082c91d288baf967f9f8be39daeef42ec87e2e9e629de9111a73a7
  (Nat.shiftLeft (Nat.add 0xf80af59b735e609af19b7fae042b7984dded94109625e291f91ccc367ad5a76956eaf7dc
  (Nat.shiftLeft 0xd4501218db668ac8b7db935611dbac4b6e5df65751cf9a077c5fe31bc9f96b299ac267d6 288))
  288)) (Nat.shiftLeft (Nat.add
  0xe9cb917520221129315b38495fa7f252e6cb0850f66a4fc0ca8c6134d51a1e991df4a534 (Nat.shiftLeft (Nat.add
  0x855d2de795c82f25f76631393959610a2643104142f665a400dfa1d1daf5314e1731b80d (Nat.shiftLeft
  0xf686f370d1ba1c7bf8ff5e9958d217cd3004a0ea648720577038d8 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (109, (mkQ
  false (Nat.add (Nat.add 0x744d938aec81d13a1543601a3df1c623572d3236409f55b898feb5323057147c7654c66b
  (Nat.shiftLeft (Nat.add 0x686ef4653af7461c8eb2d28c48d68846ef677e59d6875951e4926db8cfc1cbee74c0a157
  (Nat.shiftLeft 0xb87d107f6798af64538010417f5daf545be13986c24c98f53686ada0525c075a6758a838 288))
  288)) (Nat.shiftLeft (Nat.add
  0x64c57f444124c1fc678ee79785ae2c275da281a0a86abcf10ed54147c1062ac43e42d7c9 (Nat.shiftLeft (Nat.add
  0x6cc291f1b4372b526da0017d6c872d50aa3a31a383b219a7b09204b7ca365a3ae8bb1894 (Nat.shiftLeft
  0x2c000330d33b530a8c1466a4e9ad319d68afffae86d1fdb5fcd289 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (139, (mkQ
  false (Nat.add (Nat.add 0x2f47a4dbd2d5d891b9a5518c7b9debc06ee1b43bc20dc2e9a33b3bfcd96cee659cfddb6b
  (Nat.shiftLeft (Nat.add 0x54bbea4402f7056636de29bc3386fe54c176644d578106f4278f4d8b7bd43f8e5186ad45
  (Nat.shiftLeft 0xae46e0733ac7272a63a1cbe866815de14786603a8d2550e8c84e8f9b54623f995873264e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x1730fa2faeb02a50bc1f615f5a48643b4c19878932191b8756e5223c1442ccc74ea867c5 (Nat.shiftLeft (Nat.add
  0x6aaa893d3bc1ecaafcb20eca6fda217febc77b6725fc0d2a0cf6214313a163228c099854 (Nat.shiftLeft
  0x5f6f79014fadf8f82df8c8619f602b724fb777ee92930f2d31a986 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (141, (mkQ
  false (Nat.add (Nat.add 0x97ad6685349e4f5221d828b8df7db318fa01661f06ef152028cf4bd477a22b6e786c1469
  (Nat.shiftLeft (Nat.add 0x3a317c75e17d270c4b5565c304f2850acca246bf31b87b73adc5bcfbc9b4e608bb86a825
  (Nat.shiftLeft 0x8c78694aa1b932d48aa2ebf0211b9144160182b1bfb5fcac5db9111265ea05b8a4772af1 288))
  288)) (Nat.shiftLeft (Nat.add
  0x2e6516e3bfca35642ae138e85c49f17da703fb95b01def32a0bf9402997a09da7050bfdc (Nat.shiftLeft (Nat.add
  0xac902fac0883ccff2c91d483489ab85670251032bf308d103692639e866190eb54e5ee3f (Nat.shiftLeft
  0xb96d88982379ff94761d4c38ac358882b60ce90038871013e3ae73b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (143, (mkQ
  false (Nat.add (Nat.add 0x88f56cecaef3a7bbb116e97dcdfa7d541bd815d441e432b4b91a41741ae36ad648886415
  (Nat.shiftLeft (Nat.add 0xe468575d767d5dba75e8cd27871148d2c05ab14d20f9debc037d98c9f20468d5d35d7599
  (Nat.shiftLeft 0xcb75f1a27ef061e8e0bf552d9db420812f9bc426ea16beb519a5825e6a17ad0771384867 288))
  288)) (Nat.shiftLeft (Nat.add
  0xcfd7a5ac9cf73a0f25cac5267b1511b46a118b976a122184c706085f2adbdc5bdca9b62d (Nat.shiftLeft (Nat.add
  0x690e33f7e66b2e766e13e5d0291218523b250a0ea385937e7a546b84a29443701908b471 (Nat.shiftLeft
  0x4e059515b7419fa0ab1c7d1c8e6484094b0089616d03ad2fd70818d 288)) 288)) 864)) (Nat.add (Nat.add
  0x3206ea1f02d36457556c08c9483017cc867e0fd4abd75e18b58fec0124a163ecb5e90000 (Nat.shiftLeft (Nat.add
  0x3782fd86c5bfeb23e26e50677d9403f14dc8dc2b9a3037e502f0e16b518c273003786755 (Nat.shiftLeft
  0x5c07729b9e463aba9d91c91262b4eff759225c35a39ae55ca6f06d0e408feaad3ce3626c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb79a78eb4decae62b8e82ee6da3fcf697ccefdfcab6c6f7829f90f5177da276d353887cc
  (Nat.shiftLeft (Nat.add 0x617245e435822d53ea77dcd9c0fa78e541af33734508ebb76a5e7237d77524ba5ef62ffb
  (Nat.shiftLeft 0x359f5bf571984f6106f0e3415daf60bdd433802b57b2a8 288)) 288)) 864)))), (145, (mkQ
  true (Nat.add (Nat.add 0x70a4037db6fffcba90e42d08d995340b32adbf8f6d2d0de4c428933f5f2ccf31440347cf
  (Nat.shiftLeft (Nat.add 0x5b3fc29990202a4678c3e203fd08d2f0e3f1f084164989af12016b0f05c5e1c89d3ec4eb
  (Nat.shiftLeft 0x6d0955ed32fd0589b152203859d5e46e4c4006023d07c2f3b58c194c4beef03107d34c6 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x1d3dbe99a03d57d68efdd5c1db59f463fecd1c4edb24ebd827e52877ebd2bff3715b7cc3 (Nat.shiftLeft (Nat.add
  0x5ce2b812ae72e8278b81c8e982428c9ba6dd6912dec76037336a8294cdcf7cf5ce1f95c8 (Nat.shiftLeft
  0x35da30470428d1104c67c43702b777fa6341d390ae822e7d6e225a8 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (147, (mkQ
  false (Nat.add (Nat.add 0x6b557e0179edbf9a6a5c6a2968376f38bed7633afe519cd65af47f548e95bb69b7740877
  (Nat.shiftLeft (Nat.add 0x41ba45ce08083dda0e4fe77714bfe2710046d1e276ede835a59f75e7770a83bd1f3ac4c1
  (Nat.shiftLeft 0x2d58a32673bc6740e5673f787a16058a2c26dab64960a2194bf4c4c31eb6bff3ffe10c77 288))
  288)) (Nat.shiftLeft (Nat.add
  0xf5e416e02ec94c1f759dc97134ee48b4e906f20ef0475d873686eeacbb7013032d9dfbda (Nat.shiftLeft (Nat.add
  0xcdd817aee4471c0dfa6c1586d5cbbdf83ad39fdbd4d068e90893399c39cf20001571683a (Nat.shiftLeft
  0x12cc479f3d3c56c55fc436fff47e8ee211e83f26cbaf300cd6fca0b 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (175, (mkQ
  false (Nat.add (Nat.add 0xc43aa748226e2f9737d2e0f5241718fcf4f3265f3bd430a3a220269b571acf34861ad9b5
  (Nat.shiftLeft (Nat.add 0x5e7d6681df69be25262e42c497d4f4786777417fa4274a08fbaca870e7736833217ecffe
  (Nat.shiftLeft 0xba1f5f6dcc78963c7b9672f783490cd76e8b5eac084d36e01ef6eeb73f9a176782fac83e 288))
  288)) (Nat.shiftLeft (Nat.add
  0xe0957c063397c4dc00280ca72cac2126e34d220c473e63dd637aa00d22ea5f0c4b989e5a (Nat.shiftLeft (Nat.add
  0x207ea4311aea1efb52842cd958d8181648091ebca810660b5d4133f259f70cd17ed87622 (Nat.shiftLeft
  0x3688863fb83d9ffa8aaf0bfa359937ec2264c3f50060cd01230c03 288)) 288)) 864)) (Nat.add (Nat.add
  0xa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d00000 (Nat.shiftLeft (Nat.add
  0x58ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9f (Nat.shiftLeft
  0xc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fdc
  (Nat.shiftLeft (Nat.add 0x73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea9
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49e 288)) 288)) 864)))), (177, (mkQ
  true (Nat.add (Nat.add 0xeaad080b23a2814404d75b07be1e3b4325dda73e3e711d3973f6f04f940e8d9768f21909
  (Nat.shiftLeft (Nat.add 0xd7057ff07ee9e160ef136f1172842c7ebce656c28263af4d10123337f9988cd6cdad86f6
  (Nat.shiftLeft 0x7137e0f3f71e32e75c591b91a1979640d2610815e966592018dc8c5ddcc11cff5824d062 288))
  288)) (Nat.shiftLeft (Nat.add
  0x2771553528d1153061a2be62b9d61ee475c9cf08023feeb46e9268dcfafd75e04dcc8c93 (Nat.shiftLeft (Nat.add
  0x2c6449b9f28cf69acb722a0c422f62c1f69488c15a8fb2d6de584b11d38ca0d55cf75e31 (Nat.shiftLeft
  0x10c983fbfce0983df9ee13e7cfcc428b7e093273f679cc0ea4001 288)) 288)) 864)) (Nat.add (Nat.add
  0xb833e4364d1523a255579a7a8738026140a634c877958968def4caccea102397abca8000 (Nat.shiftLeft (Nat.add
  0x38c04c8d7a2ccab6c9d7d4d7262866cb549416045c380596e6b1b02454f46a5199f270bb (Nat.shiftLeft
  0x933f1dc5ca09f790fc1c74ea3787e6588e9d6055d2916efaa4b3e1b0674caaaec7d2371 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf8c2a5b1216477d6ac1737e3e29ffb242614b2ffaabe0b259dcc1b21bf2f6a57b885a72e
  (Nat.shiftLeft (Nat.add 0x3cf1d3ca0559d155310bfc7c2ce5d8e3b9c4b85853b41792576fd838c8beea12a3189e65
  (Nat.shiftLeft 0x55cbc655828d4bce71816b9bc9189ac9538599def2b77 288)) 288)) 864)))), (179, (mkQ
  false (Nat.add (Nat.add 0x6a8642fe87e9e03c6188bbaed1058ea013c3d19a6652fcbf6b7703537fcb6fd5f573bcc9
  (Nat.shiftLeft (Nat.add 0x248806365057205f549e3306c77214f1f81be56505af30c36a089352afccc355532095d7
  (Nat.shiftLeft 0x7f2d1fc9ad56ab4520a15f4eb4fb8593e75ec1b0e735fe465246a9bb12018b64e26d03ad 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6d7a709dcbf58116747a7cbb6f42d733ac674d91fb9cb9b8c4ebfcb72ff4f9270b74098 (Nat.shiftLeft (Nat.add
  0xf84ec28e7eb807b0414d843e42ab179e538bd60040766a6d67cd8fe77a37920fc742a417 (Nat.shiftLeft
  0xef79ad78a329b8072a3c4952c22132bac9463391e767dc072732df 288)) 288)) 864)) (Nat.add (Nat.add
  0x7067c86c9a2a4744aaaf34f50e7004c2814c6990ef2b12d1bde99599d420472f57950000 (Nat.shiftLeft (Nat.add
  0x7180991af459956d93afa9ae4c50cd96a9282c08b8700b2dcd636048a9e8d4a333e4e177 (Nat.shiftLeft
  0x1267e3b8b9413ef21f838e9d46f0fccb11d3ac0aba522ddf54967c360ce99555d8fa46e2 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf1854b6242c8efad582e6fc7c53ff6484c2965ff557c164b3b9836437e5ed4af710b4e5c
  (Nat.shiftLeft (Nat.add 0x79e3a7940ab3a2aa6217f8f859cbb1c7738970b0a7682f24aedfb071917dd42546313ccb
  (Nat.shiftLeft 0xab978cab051a979ce302d73792313592a70b33bde56ee 288)) 288)) 864)))), (181, (mkQ
  false (Nat.add (Nat.add 0x6a8642fe87e9e03c6188bbaed1058ea013c3d19a6652fcbf6b7703537fcb6fd5f573bcc9
  (Nat.shiftLeft (Nat.add 0x248806365057205f549e3306c77214f1f81be56505af30c36a089352afccc355532095d7
  (Nat.shiftLeft 0x7f2d1fc9ad56ab4520a15f4eb4fb8593e75ec1b0e735fe465246a9bb12018b64e26d03ad 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6d7a709dcbf58116747a7cbb6f42d733ac674d91fb9cb9b8c4ebfcb72ff4f9270b74098 (Nat.shiftLeft (Nat.add
  0xf84ec28e7eb807b0414d843e42ab179e538bd60040766a6d67cd8fe77a37920fc742a417 (Nat.shiftLeft
  0xef79ad78a329b8072a3c4952c22132bac9463391e767dc072732df 288)) 288)) 864)) (Nat.add (Nat.add
  0x7067c86c9a2a4744aaaf34f50e7004c2814c6990ef2b12d1bde99599d420472f57950000 (Nat.shiftLeft (Nat.add
  0x7180991af459956d93afa9ae4c50cd96a9282c08b8700b2dcd636048a9e8d4a333e4e177 (Nat.shiftLeft
  0x1267e3b8b9413ef21f838e9d46f0fccb11d3ac0aba522ddf54967c360ce99555d8fa46e2 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf1854b6242c8efad582e6fc7c53ff6484c2965ff557c164b3b9836437e5ed4af710b4e5c
  (Nat.shiftLeft (Nat.add 0x79e3a7940ab3a2aa6217f8f859cbb1c7738970b0a7682f24aedfb071917dd42546313ccb
  (Nat.shiftLeft 0xab978cab051a979ce302d73792313592a70b33bde56ee 288)) 288)) 864)))), (183, (mkQ
  true (Nat.add (Nat.add 0xeaad080b23a2814404d75b07be1e3b4325dda73e3e711d3973f6f04f940e8d9768f21909
  (Nat.shiftLeft (Nat.add 0xd7057ff07ee9e160ef136f1172842c7ebce656c28263af4d10123337f9988cd6cdad86f6
  (Nat.shiftLeft 0x7137e0f3f71e32e75c591b91a1979640d2610815e966592018dc8c5ddcc11cff5824d062 288))
  288)) (Nat.shiftLeft (Nat.add
  0x2771553528d1153061a2be62b9d61ee475c9cf08023feeb46e9268dcfafd75e04dcc8c93 (Nat.shiftLeft (Nat.add
  0x2c6449b9f28cf69acb722a0c422f62c1f69488c15a8fb2d6de584b11d38ca0d55cf75e31 (Nat.shiftLeft
  0x10c983fbfce0983df9ee13e7cfcc428b7e093273f679cc0ea4001 288)) 288)) 864)) (Nat.add (Nat.add
  0xb833e4364d1523a255579a7a8738026140a634c877958968def4caccea102397abca8000 (Nat.shiftLeft (Nat.add
  0x38c04c8d7a2ccab6c9d7d4d7262866cb549416045c380596e6b1b02454f46a5199f270bb (Nat.shiftLeft
  0x933f1dc5ca09f790fc1c74ea3787e6588e9d6055d2916efaa4b3e1b0674caaaec7d2371 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf8c2a5b1216477d6ac1737e3e29ffb242614b2ffaabe0b259dcc1b21bf2f6a57b885a72e
  (Nat.shiftLeft (Nat.add 0x3cf1d3ca0559d155310bfc7c2ce5d8e3b9c4b85853b41792576fd838c8beea12a3189e65
  (Nat.shiftLeft 0x55cbc655828d4bce71816b9bc9189ac9538599def2b77 288)) 288)) 864)))), (185, (mkQ
  false (Nat.add (Nat.add 0xc43aa748226e2f9737d2e0f5241718fcf4f3265f3bd430a3a220269b571acf34861ad9b5
  (Nat.shiftLeft (Nat.add 0x5e7d6681df69be25262e42c497d4f4786777417fa4274a08fbaca870e7736833217ecffe
  (Nat.shiftLeft 0xba1f5f6dcc78963c7b9672f783490cd76e8b5eac084d36e01ef6eeb73f9a176782fac83e 288))
  288)) (Nat.shiftLeft (Nat.add
  0xe0957c063397c4dc00280ca72cac2126e34d220c473e63dd637aa00d22ea5f0c4b989e5a (Nat.shiftLeft (Nat.add
  0x207ea4311aea1efb52842cd958d8181648091ebca810660b5d4133f259f70cd17ed87622 (Nat.shiftLeft
  0x3688863fb83d9ffa8aaf0bfa359937ec2264c3f50060cd01230c03 288)) 288)) 864)) (Nat.add (Nat.add
  0xa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d00000 (Nat.shiftLeft (Nat.add
  0x58ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9f (Nat.shiftLeft
  0xc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fdc
  (Nat.shiftLeft (Nat.add 0x73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea9
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49e 288)) 288)) 864)))), (213, (mkQ
  false (Nat.add (Nat.add 0x6b557e0179edbf9a6a5c6a2968376f38bed7633afe519cd65af47f548e95bb69b7740877
  (Nat.shiftLeft (Nat.add 0x41ba45ce08083dda0e4fe77714bfe2710046d1e276ede835a59f75e7770a83bd1f3ac4c1
  (Nat.shiftLeft 0x2d58a32673bc6740e5673f787a16058a2c26dab64960a2194bf4c4c31eb6bff3ffe10c77 288))
  288)) (Nat.shiftLeft (Nat.add
  0xf5e416e02ec94c1f759dc97134ee48b4e906f20ef0475d873686eeacbb7013032d9dfbda (Nat.shiftLeft (Nat.add
  0xcdd817aee4471c0dfa6c1586d5cbbdf83ad39fdbd4d068e90893399c39cf20001571683a (Nat.shiftLeft
  0x12cc479f3d3c56c55fc436fff47e8ee211e83f26cbaf300cd6fca0b 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864)))), (215, (mkQ
  true (Nat.add (Nat.add 0x70a4037db6fffcba90e42d08d995340b32adbf8f6d2d0de4c428933f5f2ccf31440347cf
  (Nat.shiftLeft (Nat.add 0x5b3fc29990202a4678c3e203fd08d2f0e3f1f084164989af12016b0f05c5e1c89d3ec4eb
  (Nat.shiftLeft 0x6d0955ed32fd0589b152203859d5e46e4c4006023d07c2f3b58c194c4beef03107d34c6 288)) 288
  )) (Nat.shiftLeft (Nat.add
  0x1d3dbe99a03d57d68efdd5c1db59f463fecd1c4edb24ebd827e52877ebd2bff3715b7cc3 (Nat.shiftLeft (Nat.add
  0x5ce2b812ae72e8278b81c8e982428c9ba6dd6912dec76037336a8294cdcf7cf5ce1f95c8 (Nat.shiftLeft
  0x35da30470428d1104c67c43702b777fa6341d390ae822e7d6e225a8 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (217, (mkQ
  false (Nat.add (Nat.add 0x88f56cecaef3a7bbb116e97dcdfa7d541bd815d441e432b4b91a41741ae36ad648886415
  (Nat.shiftLeft (Nat.add 0xe468575d767d5dba75e8cd27871148d2c05ab14d20f9debc037d98c9f20468d5d35d7599
  (Nat.shiftLeft 0xcb75f1a27ef061e8e0bf552d9db420812f9bc426ea16beb519a5825e6a17ad0771384867 288))
  288)) (Nat.shiftLeft (Nat.add
  0xcfd7a5ac9cf73a0f25cac5267b1511b46a118b976a122184c706085f2adbdc5bdca9b62d (Nat.shiftLeft (Nat.add
  0x690e33f7e66b2e766e13e5d0291218523b250a0ea385937e7a546b84a29443701908b471 (Nat.shiftLeft
  0x4e059515b7419fa0ab1c7d1c8e6484094b0089616d03ad2fd70818d 288)) 288)) 864)) (Nat.add (Nat.add
  0x3206ea1f02d36457556c08c9483017cc867e0fd4abd75e18b58fec0124a163ecb5e90000 (Nat.shiftLeft (Nat.add
  0x3782fd86c5bfeb23e26e50677d9403f14dc8dc2b9a3037e502f0e16b518c273003786755 (Nat.shiftLeft
  0x5c07729b9e463aba9d91c91262b4eff759225c35a39ae55ca6f06d0e408feaad3ce3626c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb79a78eb4decae62b8e82ee6da3fcf697ccefdfcab6c6f7829f90f5177da276d353887cc
  (Nat.shiftLeft (Nat.add 0x617245e435822d53ea77dcd9c0fa78e541af33734508ebb76a5e7237d77524ba5ef62ffb
  (Nat.shiftLeft 0x359f5bf571984f6106f0e3415daf60bdd433802b57b2a8 288)) 288)) 864)))), (219, (mkQ
  false (Nat.add (Nat.add 0x97ad6685349e4f5221d828b8df7db318fa01661f06ef152028cf4bd477a22b6e786c1469
  (Nat.shiftLeft (Nat.add 0x3a317c75e17d270c4b5565c304f2850acca246bf31b87b73adc5bcfbc9b4e608bb86a825
  (Nat.shiftLeft 0x8c78694aa1b932d48aa2ebf0211b9144160182b1bfb5fcac5db9111265ea05b8a4772af1 288))
  288)) (Nat.shiftLeft (Nat.add
  0x2e6516e3bfca35642ae138e85c49f17da703fb95b01def32a0bf9402997a09da7050bfdc (Nat.shiftLeft (Nat.add
  0xac902fac0883ccff2c91d483489ab85670251032bf308d103692639e866190eb54e5ee3f (Nat.shiftLeft
  0xb96d88982379ff94761d4c38ac358882b60ce90038871013e3ae73b 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (221, (mkQ
  false (Nat.add (Nat.add 0x2f47a4dbd2d5d891b9a5518c7b9debc06ee1b43bc20dc2e9a33b3bfcd96cee659cfddb6b
  (Nat.shiftLeft (Nat.add 0x54bbea4402f7056636de29bc3386fe54c176644d578106f4278f4d8b7bd43f8e5186ad45
  (Nat.shiftLeft 0xae46e0733ac7272a63a1cbe866815de14786603a8d2550e8c84e8f9b54623f995873264e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x1730fa2faeb02a50bc1f615f5a48643b4c19878932191b8756e5223c1442ccc74ea867c5 (Nat.shiftLeft (Nat.add
  0x6aaa893d3bc1ecaafcb20eca6fda217febc77b6725fc0d2a0cf6214313a163228c099854 (Nat.shiftLeft
  0x5f6f79014fadf8f82df8c8619f602b724fb777ee92930f2d31a986 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (251, (mkQ
  false (Nat.add (Nat.add 0x744d938aec81d13a1543601a3df1c623572d3236409f55b898feb5323057147c7654c66b
  (Nat.shiftLeft (Nat.add 0x686ef4653af7461c8eb2d28c48d68846ef677e59d6875951e4926db8cfc1cbee74c0a157
  (Nat.shiftLeft 0xb87d107f6798af64538010417f5daf545be13986c24c98f53686ada0525c075a6758a838 288))
  288)) (Nat.shiftLeft (Nat.add
  0x64c57f444124c1fc678ee79785ae2c275da281a0a86abcf10ed54147c1062ac43e42d7c9 (Nat.shiftLeft (Nat.add
  0x6cc291f1b4372b526da0017d6c872d50aa3a31a383b219a7b09204b7ca365a3ae8bb1894 (Nat.shiftLeft
  0x2c000330d33b530a8c1466a4e9ad319d68afffae86d1fdb5fcd289 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (253, (mkQ
  true (Nat.add (Nat.add 0x27fce8ef9bf5255b1d082c91d288baf967f9f8be39daeef42ec87e2e9e629de9111a73a7
  (Nat.shiftLeft (Nat.add 0xf80af59b735e609af19b7fae042b7984dded94109625e291f91ccc367ad5a76956eaf7dc
  (Nat.shiftLeft 0xd4501218db668ac8b7db935611dbac4b6e5df65751cf9a077c5fe31bc9f96b299ac267d6 288))
  288)) (Nat.shiftLeft (Nat.add
  0xe9cb917520221129315b38495fa7f252e6cb0850f66a4fc0ca8c6134d51a1e991df4a534 (Nat.shiftLeft (Nat.add
  0x855d2de795c82f25f76631393959610a2643104142f665a400dfa1d1daf5314e1731b80d (Nat.shiftLeft
  0xf686f370d1ba1c7bf8ff5e9958d217cd3004a0ea648720577038d8 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (255, (mkQ
  false (Nat.add (Nat.add 0xfe3372d7436c36c20952708615fd135ed5758d68e9893bea2f5eaecdc292f44d37b86913
  (Nat.shiftLeft (Nat.add 0x26cf4bcf4d0b5af8c016be6e7c5e951597697ce188ea234ec816ea88a8959eb1617eb2de
  (Nat.shiftLeft 0x8d70cc27801ec5b5a4d3025239be2fdea196fec27c91f3e00515ca4122a201dd39142bbc 288))
  288)) (Nat.shiftLeft (Nat.add
  0x6e86ac4603304767bad27ee44188dcb90ac9df67af75eeb9b82cf51e877e54e3d075a82e (Nat.shiftLeft (Nat.add
  0x76ff09b72fa5547e00629ae6534fc36cdb1e9a4e1cd0238d6b5943cca8c0d3de08a205a4 (Nat.shiftLeft
  0x34db6dc418c071c17d7fc9bdda477dc7fbaff651d6cabed31638f4e 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (257, (mkQ
  false (Nat.add (Nat.add 0x88e4cc6d7eb278f1f552d495279a52e38a282a856a13462e508dd2ce3989783cff10d35b
  (Nat.shiftLeft (Nat.add 0x9b6552b17bf80dc340d59ebd1dd28097df148a1643b83a4a989b21950dd69c7ca76f909d
  (Nat.shiftLeft 0xc2535184985603f90eb2351ce39c2669742209b898bf5dbd881a0f6eb90ef5a2f5202425 288))
  288)) (Nat.shiftLeft (Nat.add
  0xbb0430bb1f04c9f83e2c5785526f769c946b92d81a2b584c8f1e4dedc7f79da56bc658c2 (Nat.shiftLeft (Nat.add
  0x6fc7e26992a65fdff6924b0eb3ff39d0bc0889cf3615153f1afb7ba67e5fcdb3cad451f7 (Nat.shiftLeft
  0x268f33259dc1d23a9bf6037e66b47d78bc76d27c0eb3349f7f545cb 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (289, (mkQ
  false (Nat.add (Nat.add 0xaa5ba60ea9622f6caa3f29727cdf408f07507b2cbbf65ea9ca81e8cd18a84a4211670875
  (Nat.shiftLeft (Nat.add 0xa37fcff87dd5cd22e8199a90056bd79dcff37f14f582524793a532159af491ec1dea4e6f
  (Nat.shiftLeft 0x92e5ae28c7fd83aa27283f277f59e4542f0f1ce66f0e16dc607b2991862f982f81ed50f9 288))
  288)) (Nat.shiftLeft (Nat.add
  0x487c2ce653acbaa20e2d1db671e3ca24b37d57583c19183efc8335c78bb0c5111b60186d (Nat.shiftLeft (Nat.add
  0x9443b38ad9b7e210beddf349df433a5b3461c0d58a2b45e30bf6b108701d003c024acc27 (Nat.shiftLeft
  0xf107c288c790a3cd8657101f03c8165ee3425df372b75a52ebfdc 288)) 288)) 864)) (Nat.add (Nat.add
  0xf1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e08000 (Nat.shiftLeft (Nat.add
  0xb5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8 (Nat.shiftLeft
  0x7e5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x770ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a
  (Nat.shiftLeft (Nat.add 0xc21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938 288)) 288)) 864)))), (291, (mkQ
  true (Nat.add (Nat.add 0xe6d8d8fda0fd2cfbb2a93e68c31d382a6dd2ad16143a907aa3a6d74708949e3f951724c1
  (Nat.shiftLeft (Nat.add 0xd55929d1328964cf639410ea0f4b368052634801879690e0c6c0ad85710a115078eb370a
  (Nat.shiftLeft 0xf6f5b3fd48544c91a524cac5bbfec055f3a89c87755efd82307d06c1a7ed13cb767e435e 288))
  288)) (Nat.shiftLeft (Nat.add
  0x64c21fbe8c2b26cda905ee8d0feb7f337065ce452604bcb4b2baed91615957f811d8cef4 (Nat.shiftLeft (Nat.add
  0xef5bf3aec4470678d45c2cfc0b8c0ae9557aaeaded52c2d55c54aa125920ff7ab4b52ccf (Nat.shiftLeft
  0x81ab79205772ac1c82435ce9dde1583d891c003b6dbc52f8cba1cd 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (293, (mkQ
  false (Nat.add (Nat.add 0xe07106b66a7e2683cb40081ead2a66268d597bada4dace3181ad1e1060c3237214bd87b7
  (Nat.shiftLeft (Nat.add 0xc091eaaa88edbd801d7f6a4fad52b1e87a2034a35d8fd45952b191acb27b53c198746b7c
  (Nat.shiftLeft 0x1c45d62645c32e7038bf5439a2a008bffa944ff1d16405c8d5aac2d27bc88f9a7de0f6a2 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdf812195694a986a6798c3df10c11696252ff2add6ca566bbc2bfaf7ac99ad0ee7374673 (Nat.shiftLeft (Nat.add
  0x125a59cfb49133e44a568bf2a54602c32bc81cd1abfe98fc9ceb2505d98c545116fee08a (Nat.shiftLeft
  0x31ab4215488448461556b9ba1e227a9e11d376ae14a8703f0a52560 288)) 288)) 864)) (Nat.add (Nat.add
  0xc559ba0e8d49990eaf19b7501964a5f2449f1789901060d3761c18392785843b87820000 (Nat.shiftLeft (Nat.add
  0xd79584529f7bed02398bb43686e8c521313b00841d6aeaba930c06f5ed5fa760ad842ea3 (Nat.shiftLeft
  0xf9746264e9b77872c67945974756de4f68b60279f440cc189af54cc89c1bd5d5e4693922 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xdc2b9df5383a0f481d592916a076829a606d9b597b2dc57832a4fde9689bb354650a85e9
  (Nat.shiftLeft (Nat.add 0x851a692736cda63cb692287b0eb9cc6d4380c837bbe09d2c6724ee814e12c668c155f29
  (Nat.shiftLeft 0xa791ff5f02fbf80f35b0c62c44c40e513720f087720e4e3 288)) 288)) 864)))), (327, (mkQ
  false (Nat.add (Nat.add 0xecf4c90de9d03f5c35bb58bc4e09c988a3fb6fc36a76bf9d10352ca78160bd03a70c0ff1
  (Nat.shiftLeft (Nat.add 0xe1c68a151c358047a48085d6d65995e3d969567e5572cd12b0ae4ec408b575d05b96524f
  (Nat.shiftLeft 0x23946f55b386b8b4ef80977dbadd2a0c4ca7788e5254c14a29abae68aabb6488354aa074 288))
  288)) (Nat.shiftLeft (Nat.add
  0x8dc8b8a8bad6bece2f7d7dd5148a9049c0cf76f72026be6e68c5d6d976c0e72fbd7c359c (Nat.shiftLeft (Nat.add
  0x11f5de84b95229a1380181c8e77d366bfb4b5ae57661786afa3ea74f38704f5d5a4d7a0d (Nat.shiftLeft
  0x23c0189187d873f980e7e6f5cc504bef02de30a3194018db5eb05 288)) 288)) 864)) (Nat.add (Nat.add
  0xe2acdd0746a4cc87578cdba80cb252f9224f8bc4c8083069bb0e0c1c93c2c21dc3c10000 (Nat.shiftLeft (Nat.add
  0x6bcac2294fbdf6811cc5da1b43746290989d80420eb5755d4986037af6afd3b056c21751 (Nat.shiftLeft
  0xfcba313274dbbc39633ca2cba3ab6f27b45b013cfa20660c4d7aa6644e0deaeaf2349c91 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xee15cefa9c1d07a40eac948b503b414d3036cdacbd96e2bc19527ef4b44dd9aa328542f4
  (Nat.shiftLeft (Nat.add 0x8428d34939b66d31e5b49143d875ce636a1c0641bddf04e9633927740a709633460aaf94
  (Nat.shiftLeft 0x53c8ffaf817dfc079ad86316226207289b907843b907271 288)) 288)) 864)))), (329, (mkQ
  true (Nat.add (Nat.add 0x2d97cb948aaeb0dd9936efcac1cce28316689ab3214a183aa8fe0b238b2fbef0ff006e6b
  (Nat.shiftLeft (Nat.add 0x914739b6b82887fa7ad37e8e45f9957633b34abec30f4a214191ba0a8bd5fcb030988113
  (Nat.shiftLeft 0x5a2d7be0e7d68b86834eb028db0fb0c11ec5ad6718adf89fc041e91065a30bf5ecb3344c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x85fd2b7943f5c116d4a1afee5eeb24c62117c12cb99c8cc56f0edde251e64394233a8c6f (Nat.shiftLeft (Nat.add
  0x3ceca07c36455f633677e8b8b4586f42c14936da9abe7c7ab078150646c195da5c920286 (Nat.shiftLeft
  0x6c8ed03eb96536b55e4c7401aa843fa95bd50d7324b2af412258c5 288)) 288)) 864)) (Nat.add (Nat.add
  0x8ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f040000 (Nat.shiftLeft (Nat.add
  0xaf2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d47 (Nat.shiftLeft
  0xf2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d27245 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd3
  (Nat.shiftLeft (Nat.add 0x10a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe53
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c6 288)) 288)) 864))))])]

def sjsuTsp_345 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 9, 0), [(90, (mkQ true (
  Nat.add (Nat.add 0xb26d438a92ffcd0b06d5ed7c7ed0f717390e400a2ad55dd727cf8385b21de2cc63b4e043 (
  Nat.shiftLeft 0x3e6fa38a0b046f0b4105f97396cdaf8f452c7fe8e2fca543ee3a51039df3ccdf3292584 288)) (
  Nat.shiftLeft (Nat.add 0x7349a7f766a9785e63236b0c1c0fab86a6b824d5f17bc33bff77ba45f464c23b31831de7
  (Nat.shiftLeft (Nat.add 0xa448d23b1ba9a4c330705fe9e5cf2841b30951ccb8aa564398df784b9b60f7b8f61d3cc
  (Nat.shiftLeft 0x167ae8e4c5659b01690a3918b856751ec4774d8f 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (126, (mkQ true (Nat.add (Nat.add
  0x1394f910534bfc4bed8779dca1321a66dddf74e48e6c5c41b744b40ca62000a6b5bdbd13 (Nat.shiftLeft
  0x13dcb82145c85adce3ffe4b4c4d88137fd0a3fd7fc35f32f39f2e195bc25c8cb05f81531 288)) (Nat.shiftLeft (
  Nat.add 0x37ea1188c308a37e4ef1840682a66ed648e1eab2deaa18be8beabe0debd53f6aeca129f4 (Nat.shiftLeft
  (Nat.add 0xc09ecbf38b9ed4f8092040f884913b6bc3458f4678de7a4da1a37b176512835f57634a82 (Nat.shiftLeft
  0x1af5505751f8a22908e97e755d066fb863082d7ac 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (162, (mkQ true (Nat.add (Nat.add
  0xa4418796a61c24f76d874b463970c6a09451c503cd5eeaa5851a61d2b12837487ee05f8f (Nat.shiftLeft
  0x68868d0f860361ba74ec076ad381d7f0fa94edec5b7e258384cec88fdfc798626f39f2ad 288)) (Nat.shiftLeft (
  Nat.add 0x5efaa08514a047fb2a94f3fa14eaa3f4ac3ca56b0718b61f42f4302d181568cda734c4f1 (Nat.shiftLeft
  (Nat.add 0x95ad7b99aa4e39596b9823ea609c1806c8a44b561a2f1790ad09c917ed2653fcd2c333ee (Nat.shiftLeft
  0xf0382ed3794d82415d5696e63841a91ae6b4a3be 288)) 288)) 576)) (Nat.add (Nat.add
  0x1095495b8318173f2dc937b34879bd45fa193ad31d7377734d9149fea1a201bdfc400000 (Nat.shiftLeft
  0x209c2b00c1384b6aaade481fce77ff6429903921622b690979bf402dae35af877a6f856 288)) (Nat.shiftLeft (
  Nat.add 0xc14b19e391aab0d5a899cb7b8cce8fa054f4ae7a9d4580deca2f3ec2c19a738b4894b705 (Nat.shiftLeft
  (Nat.add 0xa6e33cfdb02c29ef4af46061011a2d7e860bb7d61ffc5056b6f8c6b6cb29e8bc53483c6 (Nat.shiftLeft
  0x12536f0e3bd4349d7b01ac4e555ee8492318f 288)) 288)) 576)))), (198, (mkQ true (Nat.add (Nat.add
  0xa4418796a61c24f76d874b463970c6a09451c503cd5eeaa5851a61d2b12837487ee05f8f (Nat.shiftLeft
  0x68868d0f860361ba74ec076ad381d7f0fa94edec5b7e258384cec88fdfc798626f39f2ad 288)) (Nat.shiftLeft (
  Nat.add 0x5efaa08514a047fb2a94f3fa14eaa3f4ac3ca56b0718b61f42f4302d181568cda734c4f1 (Nat.shiftLeft
  (Nat.add 0x95ad7b99aa4e39596b9823ea609c1806c8a44b561a2f1790ad09c917ed2653fcd2c333ee (Nat.shiftLeft
  0xf0382ed3794d82415d5696e63841a91ae6b4a3be 288)) 288)) 576)) (Nat.add (Nat.add
  0x1095495b8318173f2dc937b34879bd45fa193ad31d7377734d9149fea1a201bdfc400000 (Nat.shiftLeft
  0x209c2b00c1384b6aaade481fce77ff6429903921622b690979bf402dae35af877a6f856 288)) (Nat.shiftLeft (
  Nat.add 0xc14b19e391aab0d5a899cb7b8cce8fa054f4ae7a9d4580deca2f3ec2c19a738b4894b705 (Nat.shiftLeft
  (Nat.add 0xa6e33cfdb02c29ef4af46061011a2d7e860bb7d61ffc5056b6f8c6b6cb29e8bc53483c6 (Nat.shiftLeft
  0x12536f0e3bd4349d7b01ac4e555ee8492318f 288)) 288)) 576)))), (234, (mkQ true (Nat.add (Nat.add
  0x1394f910534bfc4bed8779dca1321a66dddf74e48e6c5c41b744b40ca62000a6b5bdbd13 (Nat.shiftLeft
  0x13dcb82145c85adce3ffe4b4c4d88137fd0a3fd7fc35f32f39f2e195bc25c8cb05f81531 288)) (Nat.shiftLeft (
  Nat.add 0x37ea1188c308a37e4ef1840682a66ed648e1eab2deaa18be8beabe0debd53f6aeca129f4 (Nat.shiftLeft
  (Nat.add 0xc09ecbf38b9ed4f8092040f884913b6bc3458f4678de7a4da1a37b176512835f57634a82 (Nat.shiftLeft
  0x1af5505751f8a22908e97e755d066fb863082d7ac 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576)))), (270, (mkQ true (Nat.add (Nat.add
  0xb26d438a92ffcd0b06d5ed7c7ed0f717390e400a2ad55dd727cf8385b21de2cc63b4e043 (Nat.shiftLeft
  0x3e6fa38a0b046f0b4105f97396cdaf8f452c7fe8e2fca543ee3a51039df3ccdf3292584 288)) (Nat.shiftLeft (
  Nat.add 0x7349a7f766a9785e63236b0c1c0fab86a6b824d5f17bc33bff77ba45f464c23b31831de7 (Nat.shiftLeft
  (Nat.add 0xa448d23b1ba9a4c330705fe9e5cf2841b30951ccb8aa564398df784b9b60f7b8f61d3cc (Nat.shiftLeft
  0x167ae8e4c5659b01690a3918b856751ec4774d8f 288)) 288)) 576)) (Nat.add (Nat.add
  0x52ea6ec98f78743be4ee16806a60b25de27e261f9341554083d671f9282a08b5ed400000 (Nat.shiftLeft
  0xa30cd703c61979155657689f0857fcf4cfd11da6ead90d2f60bc40e4670c6da5642d9ae 288)) (Nat.shiftLeft (
  Nat.add 0xc6778171d855742c4b00f969c008ce21a8c76865125b8459f2ec39cdc80441b86ae79319 (Nat.shiftLeft
  (Nat.add 0x3427030f470dcd1ac76c5e1e50582e3789e3a972e9fed91b192dbe191f7d18bada0692e1 (Nat.shiftLeft
  0x5ba12b472b25071367085d87aada896daf7cb 288)) 288)) 576))))])]


end KAM.EffectiveStability.SJSU

end
