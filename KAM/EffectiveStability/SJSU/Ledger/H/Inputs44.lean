/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs43

/-!
# Ledger inputs (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

def sjsuTsp_327 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 4, 7), [(101, (mkQ false (
  Nat.add (Nat.add 0x5ebd9d700a9d0d99c6cb8c4f88e25a77c7a8ad8a833a2f3a0599e5f289da19c10951c29d (
  Nat.shiftLeft (Nat.add 0xe92612f0504cf74d23aab446ceab36aa58e986afaca9047988ca0a240e727b273ec5f4de
  (Nat.shiftLeft 0x17969a2e7604fc1faea18e8195510164567e8dd5d9b443f095d20094619bd6243a3a1562 288))
  288)) (Nat.shiftLeft (Nat.add
  0x919aab28cc14b7be836e237c188a839192ee692b158a93cc81ee4f33861f755221de14c (Nat.shiftLeft (Nat.add
  0x6b242c9b5c7fa929370274f2576e900936ab24080deed8e7ca7c30e99a0fe10777512768 (Nat.shiftLeft
  0x10bbdc36bbec4f 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864)))), (103, (mkQ false (Nat.add (Nat.add
  0x661d4d5ccc0890b791d8747353d29cf509d6163dbe3fb561ee3d0ee6a2a7f947256612d (Nat.shiftLeft (Nat.add
  0x7ecabd4d9bac02cb5e9645cbbd7fa03a96dd4880f2f1dff5a548ba91a652aa9ffd7c04e9 (Nat.shiftLeft
  0x2417cb37eaf2101f366729e3da9f284df0ae30e5660e16ec624b17c5cb59443b0f483673 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96f96d5741118b8dc8cbe8c1b288629f9bc198a48939aa7001bf3a51b36e7cba956d92d7
  (Nat.shiftLeft (Nat.add 0x5f7dc1af7542d31bee95013122427ddc324273b85864f5a937e9bb94e43cab4e38022b8b
  (Nat.shiftLeft 0x3fa80c81d096d9 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (105, (mkQ false (Nat.add (Nat.add
  0x7db1fb45ee37dda1c417622b0f1c6b6aa44f30644d0e28c443a395082b24bcdec1d50987 (Nat.shiftLeft (Nat.add
  0x5ac26e46b09201eec67dc0d2d009e17b875f2eab84d53ce3e6bee724a8c8d781fb972aa7 (Nat.shiftLeft
  0x55a3612e09751788fecc62840a4d185279554bcd5cd80600201c3ab2877e249cd7e32d1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9228ecdd50960085e27f3ac955fb89fc895539cc75856c83bdc1e5d94e551bbb5c231b0c
  (Nat.shiftLeft (Nat.add 0x3201e8b174d22ab293d5b91b7edcea55379b282e5ef83df1f19824b7c937739ca3935785
  (Nat.shiftLeft 0x18ad908d1baa47 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (107, (mkQ false (Nat.add (Nat.add
  0x9cd76c87a2eb3c32f971da26bf95fbd4d1ebe3be26f256da385b5ff0887de5fe3fbdc90f (Nat.shiftLeft (Nat.add
  0xf24590dcc4ddff5d6437b8e23fbd13d849fd62df3842c2ab4288eedbf9fd5e683fc49157 (Nat.shiftLeft
  0xef26d4ce59fa3bb21c762387afec89a2a37f7065d48f76ea64cbdb788ba0537c48dc857c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x90e5a15384b1f1b55167897cc108f13a78c644cf876573bb4cfe10006b01ccb27fff10cc
  (Nat.shiftLeft (Nat.add 0x7fc405454d9fd178c4e4c8ca4cc5bc77c3798aa3aaab8d29988d1a3bd9baefcf7888c699
  (Nat.shiftLeft 0x189eab45e5772 288)) 288)) 864)) (Nat.add (Nat.add
  0x9604f33634fe95c7d9c2c414944fba6955a3752c05d2e65faa7f4b101cbdeddf2dc80000 (Nat.shiftLeft (Nat.add
  0x98cf2bb8fe1fccfca90dff1572cd98e98e266634948f1949fa903ed6c3e2278a8eed2863 (Nat.shiftLeft
  0x8dcdef9294163293dfe0eb2591462df575ee02add0d075b4c6efa63f44de0f46c669ac7d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbb69b21c62236dd5e3f0760c65a523a1672873048302f7405bf5397659230d888b533f7b
  (Nat.shiftLeft (Nat.add 0x6b799e5c7f65800615ba1e98d8a8d81c00f8948083576e353820a5ca1f763f66f1a2b7c1
  (Nat.shiftLeft 0x272f47 288)) 288)) 864)))), (109, (mkQ false (Nat.add (Nat.add
  0xcd86dec37c3516b649044d2f6a3cf269eed909d8341ed5f2792e15e6446e19cf8dd570d3 (Nat.shiftLeft (Nat.add
  0x97e330bc94ed9b5565f016a4cdb46f2ded6ed77d2c66457e6f51eeaefd65282cd59a905f (Nat.shiftLeft
  0x8a4684090c685e226e24b7baa5b3e915106e71a2219ceaef949fbd83026cafaedd8ecde7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb34673d536f41d5f88a5fb33daaf439ae9c760c70dfc55941c7b26a70f0892cbcf38a542
  (Nat.shiftLeft (Nat.add 0x7edc5f81ad23cd4a154010bb682007bb13a85ff4e29dd81ea45b53d8ccb9d0e95248d7a3
  (Nat.shiftLeft 0xfc337ce602486 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (137, (mkQ false (Nat.add (Nat.add
  0xc9a664fc11ecc1eb505323ce229b15a5fbed4eba968b1d3206a63c202984bb9eb01c738b (Nat.shiftLeft (Nat.add
  0x9b8249aadde782c509955cc30fda70be04fc6d88bd407dc6b1912fea8bb9549a02ccfc8 (Nat.shiftLeft
  0x25ebd3f84ee5fca1a5381f2a95423e61a86a5e313d01616148ab101a6ba839bb2c55e877 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa1d6d0abeb32cb3c153225ebaae7e9d1c4403c5f1cc79d00e16e3c0c92c3b610a1a33740
  (Nat.shiftLeft (Nat.add 0x9429196bb5a43db26f6babc3369086d0dfce7ef337bbb1d37c1b96bf202785dbe4aa9eda
  (Nat.shiftLeft 0x26f3ede7b7e58 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (139, (mkQ false (Nat.add (Nat.add
  0x799df9843ca956db791e8796e11391dbd4acd6ad5ca01c92105f44084017dea175fba73f (Nat.shiftLeft (Nat.add
  0x7bda9fa1f7437ae17fcffa40c77c6960dab6a5aa752b84a2766a092c85c9bdf470e92293 (Nat.shiftLeft
  0xc4ccf4240962a48985fe5eb492036a43d1a674a06724262826af41e458ea6b5c146f0fa 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8244ee83fc528ead4915c0d0208174d5c5ad481811c98e39ffa151e86441a69bd9ad2d0c
  (Nat.shiftLeft (Nat.add 0x11876eae787361d9ccf7a66392ffc5b933a6fae6931262333c5eb3ce683adcd7646f62f7
  (Nat.shiftLeft 0xf6094b623d6abb 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (141, (mkQ false (Nat.add (Nat.add
  0x876f8ab95b380b9b294dc2c913a0963623676e062b5d39f2de47d40cc4dea0fa2c32507d (Nat.shiftLeft (Nat.add
  0xb2157a003f4855cb90c2a85ad8d57cc3070831c24b6ccd50e24d854acdbb2a7f2fa4f7e4 (Nat.shiftLeft
  0xd324a9346cca2062cfc540363e5968ca8039beaeb3b537f3c4958c91a89e3579519df927 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc9102c55acab319aa627c9c901827d2250b07fe1fec233e46a77d76404856cdeceaef399
  (Nat.shiftLeft (Nat.add 0xbcd90f364d84a990222ef127a047a9d34dc5bf9397908219b854c431b3d89192ff333e65
  (Nat.shiftLeft 0x3caddb1938f1d 288)) 288)) 864)) (Nat.add (Nat.add
  0xcb02799b1a7f4ae3ece1620a4a27dd34aad1ba9602e9732fd53fa5880e5ef6ef96e40000 (Nat.shiftLeft (Nat.add
  0xcc6795dc7f0fe67e5486ff8ab966cc74c713331a4a478ca4fd481f6b61f113c547769431 (Nat.shiftLeft
  0xc6e6f7c94a0b1949eff07592c8a316fabaf70156e8683ada6377d31fa26f07a36334d63e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xddb4d90e3111b6eaf1f83b0632d291d0b394398241817ba02dfa9cbb2c9186c445a99fbd
  (Nat.shiftLeft (Nat.add 0xb5bccf2e3fb2c0030add0f4c6c546c0e007c4a4041abb71a9c1052e50fbb1fb378d15be0
  (Nat.shiftLeft 0x1397a3 288)) 288)) 864)))), (143, (mkQ false (Nat.add (Nat.add
  0x9f53ba5e8c5c31b6a557bcfb79b6806d3492cd118ad922676df7b6c7cca352941cdbf40d (Nat.shiftLeft (Nat.add
  0x3de5f7cea543fdc4e7ecca600c56f190038f4ae02aa22600d8047bccb70c4ef52f39f25 (Nat.shiftLeft
  0x63976facdec0ece56a54f642dcbc393aabd4b545b2826991db353e765d703158f87b09fe 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x86228bb463b395f8a53ca3c8653eb71d0f22655908cf24c92f6262d83369519446492dcf
  (Nat.shiftLeft (Nat.add 0xdcefd155b52864b907410b09213183df008d1e416b1f3d68a7ed39ade1027b0230dfbe54
  (Nat.shiftLeft 0x11fed7ffcf6673 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (145, (mkQ false (Nat.add (Nat.add
  0xadb8a0f1d0d983fdf94b58388e219af5f12320f15103933826eaaf80bc7fa2b3d45756d (Nat.shiftLeft (Nat.add
  0x7039a88a0c38d10c3ed781fa0fc6e4042d8008aa51926c76fb3f85cd6f017894c3d86d25 (Nat.shiftLeft
  0xf0a7695df49f585f035baea92e4aed9c8c3df90aa32aa468ab53368a3900015532de1174 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8379b3de853ef347761808636866c33e742905d533be9132614ea7594f196ad89385a459
  (Nat.shiftLeft (Nat.add 0xc0f51dd50a83b577ad7993eb5141a12aead3fade8de918df275e40370aeddb904a32d8f0
  (Nat.shiftLeft 0x808441f355d9e 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (147, (mkQ false (Nat.add (Nat.add
  0xb9ba0d579014df59c106cd6744b39759ad08cf0357ef93abd7f385e2dd28b7af7b5c6585 (Nat.shiftLeft (Nat.add
  0xb802157ba7c9e5880f4126b349e63678575f35ee335c0bc94476c08882e763f30ed6102c (Nat.shiftLeft
  0xe6da0e3e77bf06de868f21df743b0b069f595b3d976b81ad0e91eb0cd7fe32414122790 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x627833326bda61a151b69a7527770f3dfd7129017f24698546cb9adf60a03757eab93325
  (Nat.shiftLeft (Nat.add 0x5a65e0b6c41b264ba635902a40aa89bf62e5da888deeadd2c012a316decafc7ad5620f6f
  (Nat.shiftLeft 0x2479b07d1bf49 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (175, (mkQ false (Nat.add (Nat.add
  0xfdecdac31f0f9e4ac86409c1abe7acf5dce3f4a667ac425f6a3284a78b118dd9dd74ea5 (Nat.shiftLeft (Nat.add
  0x28a0edf887395957f6aa9ef4bb333ebe58b295c697fa6c0a177a63a5f12a52d63df93007 (Nat.shiftLeft
  0x13a32aeae375283f750a2cef5813bfdfe1b436c11825840741a7b10749fe3efef3f722eb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x55c766f972c7d89e32ba9aef3775502d28d77c2ffc1b0337eb16da493fc78e84693ec1db
  (Nat.shiftLeft (Nat.add 0x287a0ca120b59650f9a6961f3aceeedbbe37f3c624cfdf26060b3e40b8528e4d31ac3f33
  (Nat.shiftLeft 0x1ba842a728375 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (177, (mkQ false (Nat.add (Nat.add
  0x5907134ef8d4589a563d8b0285dd054a846abd270a1c368572b84eb82396a5b2345a92ed (Nat.shiftLeft (Nat.add
  0x4a538f36547f2d1f095d3f3261bd2d08891c139d36c1dff61bceb7e1bc5e06019acc172f (Nat.shiftLeft
  0x3e05d5d5b52296c3b9285bc3fee9874cb2792bd668159512ffc344e46ccda0b62306ecab 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2fa41e893c8162f55a0047b852e114e35d39421ae861193cccc6892bb6bf88bad8cfede8
  (Nat.shiftLeft (Nat.add 0xb3cac8d49027df7950c49b13ad64fb69e6bad2adbd7089f726706ec144b6ff30b24770a8
  (Nat.shiftLeft 0x11f8fcfc140ec6 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (179, (mkQ false (Nat.add (Nat.add
  0xfef36bee075af97813c9118ea2cefe6fe00ab699fce7eb52bb94900983ae12d63e1f2971 (Nat.shiftLeft (Nat.add
  0x77268f99c41cce44973454acacf9550562e58228383aaa03e41ef4a0b497552e67e130c7 (Nat.shiftLeft
  0x5a2561bf802faf1cb95930e635a465317c4c50ad2d648d62d493d0cd14946f2da1ae0aa9 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x22bf02d7e931b8dbdd9ff1e716bc53015f8506bbee47807c03a553adae32dd3f39e0fa5c
  (Nat.shiftLeft (Nat.add 0x59aacb7eb54e1edb13ddefb2c4d36d59e1fe353f4d817a0a9208985f191a23dd0be8db5a
  (Nat.shiftLeft 0xcd7109db264fd 288)) 288)) 864)) (Nat.add (Nat.add
  0x3dc31801e11f1d9ce819ba8cdcb1d481d586293b83a3cffbca8f8eea11f6b4ab7c9d0000 (Nat.shiftLeft (Nat.add
  0x7f817b539ed3e01de9a8bf6d67c07f91f8d7ffe0dcd96fce3c9a27463a6d58b69954393e (Nat.shiftLeft
  0x38a0b5bb9c8ddf9c6bec92f77acbdcb969b4c1aca2824990fc55c7e78b0ac98c3c020bce 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x15220f51bd5624a5ae7649c7bf873644e07947e2d1e1da88397943e9f7b5e875571407ad
  (Nat.shiftLeft (Nat.add 0xa32c02f9cf9f7003cd94531f87698711809b5cd05216a4e14314679e53a9e7a05705b2d9
  (Nat.shiftLeft 0x187d8c 288)) 288)) 864)))), (181, (mkQ false (Nat.add (Nat.add
  0xfef36bee075af97813c9118ea2cefe6fe00ab699fce7eb52bb94900983ae12d63e1f2971 (Nat.shiftLeft (Nat.add
  0x77268f99c41cce44973454acacf9550562e58228383aaa03e41ef4a0b497552e67e130c7 (Nat.shiftLeft
  0x5a2561bf802faf1cb95930e635a465317c4c50ad2d648d62d493d0cd14946f2da1ae0aa9 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x22bf02d7e931b8dbdd9ff1e716bc53015f8506bbee47807c03a553adae32dd3f39e0fa5c
  (Nat.shiftLeft (Nat.add 0x59aacb7eb54e1edb13ddefb2c4d36d59e1fe353f4d817a0a9208985f191a23dd0be8db5a
  (Nat.shiftLeft 0xcd7109db264fd 288)) 288)) 864)) (Nat.add (Nat.add
  0x3dc31801e11f1d9ce819ba8cdcb1d481d586293b83a3cffbca8f8eea11f6b4ab7c9d0000 (Nat.shiftLeft (Nat.add
  0x7f817b539ed3e01de9a8bf6d67c07f91f8d7ffe0dcd96fce3c9a27463a6d58b69954393e (Nat.shiftLeft
  0x38a0b5bb9c8ddf9c6bec92f77acbdcb969b4c1aca2824990fc55c7e78b0ac98c3c020bce 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x15220f51bd5624a5ae7649c7bf873644e07947e2d1e1da88397943e9f7b5e875571407ad
  (Nat.shiftLeft (Nat.add 0xa32c02f9cf9f7003cd94531f87698711809b5cd05216a4e14314679e53a9e7a05705b2d9
  (Nat.shiftLeft 0x187d8c 288)) 288)) 864)))), (183, (mkQ false (Nat.add (Nat.add
  0x5907134ef8d4589a563d8b0285dd054a846abd270a1c368572b84eb82396a5b2345a92ed (Nat.shiftLeft (Nat.add
  0x4a538f36547f2d1f095d3f3261bd2d08891c139d36c1dff61bceb7e1bc5e06019acc172f (Nat.shiftLeft
  0x3e05d5d5b52296c3b9285bc3fee9874cb2792bd668159512ffc344e46ccda0b62306ecab 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2fa41e893c8162f55a0047b852e114e35d39421ae861193cccc6892bb6bf88bad8cfede8
  (Nat.shiftLeft (Nat.add 0xb3cac8d49027df7950c49b13ad64fb69e6bad2adbd7089f726706ec144b6ff30b24770a8
  (Nat.shiftLeft 0x11f8fcfc140ec6 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (185, (mkQ false (Nat.add (Nat.add
  0xfdecdac31f0f9e4ac86409c1abe7acf5dce3f4a667ac425f6a3284a78b118dd9dd74ea5 (Nat.shiftLeft (Nat.add
  0x28a0edf887395957f6aa9ef4bb333ebe58b295c697fa6c0a177a63a5f12a52d63df93007 (Nat.shiftLeft
  0x13a32aeae375283f750a2cef5813bfdfe1b436c11825840741a7b10749fe3efef3f722eb 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x55c766f972c7d89e32ba9aef3775502d28d77c2ffc1b0337eb16da493fc78e84693ec1db
  (Nat.shiftLeft (Nat.add 0x287a0ca120b59650f9a6961f3aceeedbbe37f3c624cfdf26060b3e40b8528e4d31ac3f33
  (Nat.shiftLeft 0x1ba842a728375 288)) 288)) 864)) (Nat.add (Nat.add
  0xee18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e80000 (Nat.shiftLeft (Nat.add
  0xfc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1 (Nat.shiftLeft
  0xc505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69
  (Nat.shiftLeft (Nat.add 0x196017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8
  (Nat.shiftLeft 0xc3ec65 288)) 288)) 864)))), (213, (mkQ false (Nat.add (Nat.add
  0xb9ba0d579014df59c106cd6744b39759ad08cf0357ef93abd7f385e2dd28b7af7b5c6585 (Nat.shiftLeft (Nat.add
  0xb802157ba7c9e5880f4126b349e63678575f35ee335c0bc94476c08882e763f30ed6102c (Nat.shiftLeft
  0xe6da0e3e77bf06de868f21df743b0b069f595b3d976b81ad0e91eb0cd7fe32414122790 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x627833326bda61a151b69a7527770f3dfd7129017f24698546cb9adf60a03757eab93325
  (Nat.shiftLeft (Nat.add 0x5a65e0b6c41b264ba635902a40aa89bf62e5da888deeadd2c012a316decafc7ad5620f6f
  (Nat.shiftLeft 0x2479b07d1bf49 288)) 288)) 864)) (Nat.add (Nat.add
  0x34cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f110000 (Nat.shiftLeft (Nat.add
  0x7d8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e37 (Nat.shiftLeft
  0x1b238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b08 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x69aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab3642662
  (Nat.shiftLeft (Nat.add 0x2fdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d
  (Nat.shiftLeft 0x7a73bf 288)) 288)) 864)))), (215, (mkQ false (Nat.add (Nat.add
  0xadb8a0f1d0d983fdf94b58388e219af5f12320f15103933826eaaf80bc7fa2b3d45756d (Nat.shiftLeft (Nat.add
  0x7039a88a0c38d10c3ed781fa0fc6e4042d8008aa51926c76fb3f85cd6f017894c3d86d25 (Nat.shiftLeft
  0xf0a7695df49f585f035baea92e4aed9c8c3df90aa32aa468ab53368a3900015532de1174 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8379b3de853ef347761808636866c33e742905d533be9132614ea7594f196ad89385a459
  (Nat.shiftLeft (Nat.add 0xc0f51dd50a83b577ad7993eb5141a12aead3fade8de918df275e40370aeddb904a32d8f0
  (Nat.shiftLeft 0x808441f355d9e 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (217, (mkQ false (Nat.add (Nat.add
  0x9f53ba5e8c5c31b6a557bcfb79b6806d3492cd118ad922676df7b6c7cca352941cdbf40d (Nat.shiftLeft (Nat.add
  0x3de5f7cea543fdc4e7ecca600c56f190038f4ae02aa22600d8047bccb70c4ef52f39f25 (Nat.shiftLeft
  0x63976facdec0ece56a54f642dcbc393aabd4b545b2826991db353e765d703158f87b09fe 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x86228bb463b395f8a53ca3c8653eb71d0f22655908cf24c92f6262d83369519446492dcf
  (Nat.shiftLeft (Nat.add 0xdcefd155b52864b907410b09213183df008d1e416b1f3d68a7ed39ade1027b0230dfbe54
  (Nat.shiftLeft 0x11fed7ffcf6673 288)) 288)) 864)) (Nat.add (Nat.add
  0x7b863003c23e3b39d0337519b963a903ab0c527707479ff7951f1dd423ed6956f93a0000 (Nat.shiftLeft (Nat.add
  0xff02f6a73da7c03bd3517edacf80ff23f1afffc1b9b2df9c79344e8c74dab16d32a8727c (Nat.shiftLeft
  0x71416b77391bbf38d7d925eef597b972d369835945049321f8ab8fcf161593187804179c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2a441ea37aac494b5cec938f7f0e6c89c0f28fc5a3c3b51072f287d3ef6bd0eaae280f5a
  (Nat.shiftLeft (Nat.add 0x465805f39f3ee0079b28a63f0ed30e230136b9a0a42d49c28628cf3ca753cf40ae0b65b2
  (Nat.shiftLeft 0x30fb19 288)) 288)) 864)))), (219, (mkQ false (Nat.add (Nat.add
  0x876f8ab95b380b9b294dc2c913a0963623676e062b5d39f2de47d40cc4dea0fa2c32507d (Nat.shiftLeft (Nat.add
  0xb2157a003f4855cb90c2a85ad8d57cc3070831c24b6ccd50e24d854acdbb2a7f2fa4f7e4 (Nat.shiftLeft
  0xd324a9346cca2062cfc540363e5968ca8039beaeb3b537f3c4958c91a89e3579519df927 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xc9102c55acab319aa627c9c901827d2250b07fe1fec233e46a77d76404856cdeceaef399
  (Nat.shiftLeft (Nat.add 0xbcd90f364d84a990222ef127a047a9d34dc5bf9397908219b854c431b3d89192ff333e65
  (Nat.shiftLeft 0x3caddb1938f1d 288)) 288)) 864)) (Nat.add (Nat.add
  0xcb02799b1a7f4ae3ece1620a4a27dd34aad1ba9602e9732fd53fa5880e5ef6ef96e40000 (Nat.shiftLeft (Nat.add
  0xcc6795dc7f0fe67e5486ff8ab966cc74c713331a4a478ca4fd481f6b61f113c547769431 (Nat.shiftLeft
  0xc6e6f7c94a0b1949eff07592c8a316fabaf70156e8683ada6377d31fa26f07a36334d63e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xddb4d90e3111b6eaf1f83b0632d291d0b394398241817ba02dfa9cbb2c9186c445a99fbd
  (Nat.shiftLeft (Nat.add 0xb5bccf2e3fb2c0030add0f4c6c546c0e007c4a4041abb71a9c1052e50fbb1fb378d15be0
  (Nat.shiftLeft 0x1397a3 288)) 288)) 864)))), (221, (mkQ false (Nat.add (Nat.add
  0x799df9843ca956db791e8796e11391dbd4acd6ad5ca01c92105f44084017dea175fba73f (Nat.shiftLeft (Nat.add
  0x7bda9fa1f7437ae17fcffa40c77c6960dab6a5aa752b84a2766a092c85c9bdf470e92293 (Nat.shiftLeft
  0xc4ccf4240962a48985fe5eb492036a43d1a674a06724262826af41e458ea6b5c146f0fa 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8244ee83fc528ead4915c0d0208174d5c5ad481811c98e39ffa151e86441a69bd9ad2d0c
  (Nat.shiftLeft (Nat.add 0x11876eae787361d9ccf7a66392ffc5b933a6fae6931262333c5eb3ce683adcd7646f62f7
  (Nat.shiftLeft 0xf6094b623d6abb 288)) 288)) 864)) (Nat.add (Nat.add
  0x33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc4400000 (Nat.shiftLeft (Nat.add
  0x61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dcd (Nat.shiftLeft
  0xc8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd9099886
  (Nat.shiftLeft (Nat.add 0xf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5a
  (Nat.shiftLeft 0x1e9cefcb 288)) 288)) 864)))), (223, (mkQ false (Nat.add (Nat.add
  0xc9a664fc11ecc1eb505323ce229b15a5fbed4eba968b1d3206a63c202984bb9eb01c738b (Nat.shiftLeft (Nat.add
  0x9b8249aadde782c509955cc30fda70be04fc6d88bd407dc6b1912fea8bb9549a02ccfc8 (Nat.shiftLeft
  0x25ebd3f84ee5fca1a5381f2a95423e61a86a5e313d01616148ab101a6ba839bb2c55e877 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa1d6d0abeb32cb3c153225ebaae7e9d1c4403c5f1cc79d00e16e3c0c92c3b610a1a33740
  (Nat.shiftLeft (Nat.add 0x9429196bb5a43db26f6babc3369086d0dfce7ef337bbb1d37c1b96bf202785dbe4aa9eda
  (Nat.shiftLeft 0x26f3ede7b7e58 288)) 288)) 864)) (Nat.add (Nat.add
  0xe18c00f08f8ece740cdd466e58ea40eac3149dc1d1e7fde547c77508fb5a55be4e800000 (Nat.shiftLeft (Nat.add
  0xc0bda9cf69f00ef4d45fb6b3e03fc8fc6bfff06e6cb7e71e4d13a31d36ac5b4caa1c9f1e (Nat.shiftLeft
  0x505addce46efce35f6497bbd65ee5cb4da60d6514124c87e2ae3f3c58564c61e0105e73f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9107a8deab1252d73b24e3dfc39b22703ca3f168f0ed441cbca1f4fbdaf43aab8a03d69c
  (Nat.shiftLeft (Nat.add 0x96017ce7cfb801e6ca298fc3b4c388c04dae68290b5270a18a33cf29d4f3d02b82d96c8a
  (Nat.shiftLeft 0xc3ec651 288)) 288)) 864)))), (251, (mkQ false (Nat.add (Nat.add
  0xcd86dec37c3516b649044d2f6a3cf269eed909d8341ed5f2792e15e6446e19cf8dd570d3 (Nat.shiftLeft (Nat.add
  0x97e330bc94ed9b5565f016a4cdb46f2ded6ed77d2c66457e6f51eeaefd65282cd59a905f (Nat.shiftLeft
  0x8a4684090c685e226e24b7baa5b3e915106e71a2219ceaef949fbd83026cafaedd8ecde7 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb34673d536f41d5f88a5fb33daaf439ae9c760c70dfc55941c7b26a70f0892cbcf38a542
  (Nat.shiftLeft (Nat.add 0x7edc5f81ad23cd4a154010bb682007bb13a85ff4e29dd81ea45b53d8ccb9d0e95248d7a3
  (Nat.shiftLeft 0xfc337ce602486 288)) 288)) 864)) (Nat.add (Nat.add
  0x4cf7809659b94108880a4c04f7926892b9ece2992330feaf4cdca9259d187596f1100000 (Nat.shiftLeft (Nat.add
  0xd8768a21a236095904bbd2306c27dd9dc37ff64503f2f072f02c45f2422bb90fea51e373 (Nat.shiftLeft
  0xb238caa0ec55e0e1b9eded565fb4f9f1087c85f2c8b6fd4edace785b735efbd2c0a3b087 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9aa4c98b2aeb73c684f70e6bda40f58625e676e196944a91f5e5391d68d8a4ab36426621
  (Nat.shiftLeft (Nat.add 0xfdc0ee10e1d301303e59f9da50fa3578308d0119a7138664f660617a2518621b31c7e3d6
  (Nat.shiftLeft 0x7a73bf2 288)) 288)) 864)))), (253, (mkQ false (Nat.add (Nat.add
  0x9cd76c87a2eb3c32f971da26bf95fbd4d1ebe3be26f256da385b5ff0887de5fe3fbdc90f (Nat.shiftLeft (Nat.add
  0xf24590dcc4ddff5d6437b8e23fbd13d849fd62df3842c2ab4288eedbf9fd5e683fc49157 (Nat.shiftLeft
  0xef26d4ce59fa3bb21c762387afec89a2a37f7065d48f76ea64cbdb788ba0537c48dc857c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x90e5a15384b1f1b55167897cc108f13a78c644cf876573bb4cfe10006b01ccb27fff10cc
  (Nat.shiftLeft (Nat.add 0x7fc405454d9fd178c4e4c8ca4cc5bc77c3798aa3aaab8d29988d1a3bd9baefcf7888c699
  (Nat.shiftLeft 0x189eab45e5772 288)) 288)) 864)) (Nat.add (Nat.add
  0x9604f33634fe95c7d9c2c414944fba6955a3752c05d2e65faa7f4b101cbdeddf2dc80000 (Nat.shiftLeft (Nat.add
  0x98cf2bb8fe1fccfca90dff1572cd98e98e266634948f1949fa903ed6c3e2278a8eed2863 (Nat.shiftLeft
  0x8dcdef9294163293dfe0eb2591462df575ee02add0d075b4c6efa63f44de0f46c669ac7d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xbb69b21c62236dd5e3f0760c65a523a1672873048302f7405bf5397659230d888b533f7b
  (Nat.shiftLeft (Nat.add 0x6b799e5c7f65800615ba1e98d8a8d81c00f8948083576e353820a5ca1f763f66f1a2b7c1
  (Nat.shiftLeft 0x272f47 288)) 288)) 864)))), (255, (mkQ false (Nat.add (Nat.add
  0x7db1fb45ee37dda1c417622b0f1c6b6aa44f30644d0e28c443a395082b24bcdec1d50987 (Nat.shiftLeft (Nat.add
  0x5ac26e46b09201eec67dc0d2d009e17b875f2eab84d53ce3e6bee724a8c8d781fb972aa7 (Nat.shiftLeft
  0x55a3612e09751788fecc62840a4d185279554bcd5cd80600201c3ab2877e249cd7e32d1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x9228ecdd50960085e27f3ac955fb89fc895539cc75856c83bdc1e5d94e551bbb5c231b0c
  (Nat.shiftLeft (Nat.add 0x3201e8b174d22ab293d5b91b7edcea55379b282e5ef83df1f19824b7c937739ca3935785
  (Nat.shiftLeft 0x18ad908d1baa47 288)) 288)) 864)) (Nat.add (Nat.add
  0xd33de025966e5042220293013de49a24ae7b38a648cc3fabd3372a4967461d65bc440000 (Nat.shiftLeft (Nat.add
  0xf61da288688d8256412ef48c1b09f76770dffd9140fcbc1cbc0b117c908aee43fa9478dc (Nat.shiftLeft
  0x6c8e32a83b1578386e7b7b5597ed3e7c421f217cb22dbf53b6b39e16dcd7bef4b028ec21 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa6a93262cabadcf1a13dc39af6903d6189799db865a512a47d794e475a36292acd909988
  (Nat.shiftLeft (Nat.add 0xbf703b843874c04c0f967e76943e8d5e0c23404669c4e1993d98185e89461886cc71f8f5
  (Nat.shiftLeft 0x1e9cefc 288)) 288)) 864)))), (257, (mkQ false (Nat.add (Nat.add
  0x661d4d5ccc0890b791d8747353d29cf509d6163dbe3fb561ee3d0ee6a2a7f947256612d (Nat.shiftLeft (Nat.add
  0x7ecabd4d9bac02cb5e9645cbbd7fa03a96dd4880f2f1dff5a548ba91a652aa9ffd7c04e9 (Nat.shiftLeft
  0x2417cb37eaf2101f366729e3da9f284df0ae30e5660e16ec624b17c5cb59443b0f483673 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96f96d5741118b8dc8cbe8c1b288629f9bc198a48939aa7001bf3a51b36e7cba956d92d7
  (Nat.shiftLeft (Nat.add 0x5f7dc1af7542d31bee95013122427ddc324273b85864f5a937e9bb94e43cab4e38022b8b
  (Nat.shiftLeft 0x3fa80c81d096d9 288)) 288)) 864)) (Nat.add (Nat.add
  0x99ef012cb372821110149809ef24d12573d9c5324661fd5e99b9524b3a30eb2de2200000 (Nat.shiftLeft (Nat.add
  0xb0ed1443446c12b20977a460d84fbb3b86ffec8a07e5e0e5e0588be48457721fd4a3c6e6 (Nat.shiftLeft
  0x64719541d8abc1c373dbdaacbf69f3e210f90be5916dfa9db59cf0b6e6bdf7a58147610f 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3549931655d6e78d09ee1cd7b481eb0c4bccedc32d289523ebca723ad1b149566c84cc43
  (Nat.shiftLeft (Nat.add 0xfb81dc21c3a602607cb3f3b4a1f46af0611a02334e270cc9ecc0c2f44a30c436638fc7ad
  (Nat.shiftLeft 0xf4e77e5 288)) 288)) 864)))), (259, (mkQ false (Nat.add (Nat.add
  0x5ebd9d700a9d0d99c6cb8c4f88e25a77c7a8ad8a833a2f3a0599e5f289da19c10951c29d (Nat.shiftLeft (Nat.add
  0xe92612f0504cf74d23aab446ceab36aa58e986afaca9047988ca0a240e727b273ec5f4de (Nat.shiftLeft
  0x17969a2e7604fc1faea18e8195510164567e8dd5d9b443f095d20094619bd6243a3a1562 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x919aab28cc14b7be836e237c188a839192ee692b158a93cc81ee4f33861f755221de14c (
  Nat.shiftLeft (Nat.add 0x6b242c9b5c7fa929370274f2576e900936ab24080deed8e7ca7c30e99a0fe10777512768
  (Nat.shiftLeft 0x10bbdc36bbec4f 288)) 288)) 864)) (Nat.add (Nat.add
  0x67bc04b2cdca084440526027bc934495cf6714c91987f57a66e5492ce8c3acb788800000 (Nat.shiftLeft (Nat.add
  0xc3b4510d11b04ac825de9183613eecee1bffb2281f97839781622f92115dc87f528f1b9a (Nat.shiftLeft
  0x91c6550762af070dcf6f6ab2fda7cf8843e42f9645b7ea76d673c2db9af7de96051d843e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xd5264c59575b9e3427b8735ed207ac312f33b70cb4a2548faf29c8eb46c52559b213310d
  (Nat.shiftLeft (Nat.add 0xee0770870e980981f2cfced287d1abc1846808cd389c3327b3030bd128c310d98e3f1eb4
  (Nat.shiftLeft 0x3d39df97 288)) 288)) 864))))])]

def sjsuTsp_328 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 4, 9), [(99, (mkQ false (
  Nat.add (Nat.add 0xf0789e24301d8d5d7bab114a71eb4dc9cb1acd571fdcc1817710d629fafefa210a38cb89 (
  Nat.shiftLeft (Nat.add 0xcc6f965ece38c720e496517e9d963a4c5e94ed453eebbb6c85f0d42e05ee33a60aac0715
  (Nat.shiftLeft 0xb79c76ce958083270233316e60df81df51aa2056cc74d25d5c298dba30bd4c0bd24334d5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3fab787e2bc696d5d01420db225c939cac33b23ef290fcbb8f8712faf53546a39ebe6f40 (Nat.shiftLeft (Nat.add
  0x4d10dee972e5c956c2aff470a178573954fb81e646d3941a4a65357673e0d059ac813cde (Nat.shiftLeft
  0x281fa8e82cfaa44c812570a7e462ae531e82f83c21a451c63fdb080 288)) 288)) 864)) (Nat.add (Nat.add
  0x11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c6800000 (Nat.shiftLeft (Nat.add
  0xc779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254fd (Nat.shiftLeft
  0x129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e8a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x22e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537ee6 (
  Nat.shiftLeft (Nat.add 0x9daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f54b
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4f3 288)) 288)) 864)))), (101, (mkQ
  false (Nat.add (Nat.add 0xcddba7a5f11358077556fe3c2f6f35ac78bb6c9d42b2049b70487f72782118d6e9f0d797
  (Nat.shiftLeft (Nat.add 0x78a80123fee920f89ec0ed88cbf43f2885c68c11fc36fc41957f6cd1621f5a84e9c98b9
  (Nat.shiftLeft 0x360374fe933e9b4826148a2e6667fafb454b30f31727a08d19ce1dc856061c222843c8d1 288))
  288)) (Nat.shiftLeft (Nat.add
  0xfa73b42111faa9545b59a04cb8f363938f7931961674c93ba58bbdf6dd76163371bf0587 (Nat.shiftLeft (Nat.add
  0x2d819ec6fbc7325679d4e2be4f34df7927562bf5a126075879921977f5c774de6430471 (Nat.shiftLeft
  0x38333c7af7404832677afac3babeda42c0011317d3aac150b6b2fa5b 288)) 288)) 864)) (Nat.add (Nat.add
  0x88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e363400000 (Nat.shiftLeft (Nat.add
  0x63bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a7e (Nat.shiftLeft
  0x94f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b0745 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf73
  (Nat.shiftLeft (Nat.add 0xced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfaa5
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f5279 288)) 288)) 864)))), (103, (mkQ
  false (Nat.add (Nat.add 0xbd573e69a975f80d8e161327cae6530879eb79e43f505d24afd913886b0d5353128f2083
  (Nat.shiftLeft (Nat.add 0xd10bb9ef53847ea7c60d798813b7a62518496ac1a3863ba1fe12fbf3aa095e664a9ee262
  (Nat.shiftLeft 0x64d74b66cbf748c3cd5110568f57382ff7fddb872615da44fc2a2edb5dc31d1c8ab126ae 288))
  288)) (Nat.shiftLeft (Nat.add
  0xc1ab177b10c443452e6939a99ee14e33f7bb60310e1c291597aa9e9bf7f36b7bedffef87 (Nat.shiftLeft (Nat.add
  0x18af06a3ff7c5ab9991b455bf372e7af27fab073693570d584d008d604401569bf77a6d2 (Nat.shiftLeft
  0x526cacb79efb84a7e669e88afabc8d5f1e3e964ef615c60250c75fc 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864)))), (105, (mkQ
  false (Nat.add (Nat.add 0xa17eb4fcdc8e5f1956fa66161a5cd904a2526d158825773e84ea8a236c1e64ff807f40d1
  (Nat.shiftLeft (Nat.add 0x8df9c564ecda1b65620c03f0b03ed7e8f3335558021763bcc1baddb72ab30266b535c3d1
  (Nat.shiftLeft 0xdad89879cd40b9648459a18dabfb93055090d46bcf4f163a3021ad53881700aebc6318ec 288))
  288)) (Nat.shiftLeft (Nat.add
  0x65807a0facfba0e88a8ddcc78c869064d76cb86df85fd0ac4a425246b677b1af9004e1bd (Nat.shiftLeft (Nat.add
  0x347d4bdc2c95d3b0ccdae717860d64bb20d49c8d3f567b69b8dd73a8ba923b29399fad15 (Nat.shiftLeft
  0x358eee76846d5de902439a5f3e59857cb5e1ad56f1f9fcaf0670fb64 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (107, (mkQ
  true (Nat.add (Nat.add 0xcdbdca67677cf3a1eaf1edead1baa82d1e59b3c39b79286dab408eb7c39cd688dee866fb
  (Nat.shiftLeft (Nat.add 0x57381372817b8b9fdb1a829f1fabe64c8653f7f08b8d719e2c1fe30222ae302ffa41ba99
  (Nat.shiftLeft 0xe6c426c4988092a954c06349d9ec44ec0344a1fd88137efddbb50672288174195b76d9 288)) 288)
  ) (Nat.shiftLeft (Nat.add
  0xf4b2406b607b2d3f9de1b394b163ed72568587f4afb2844418f4f485138b6f5a11b374a3 (Nat.shiftLeft (Nat.add
  0x3f7d72724fa02307e321a8784c9361deca294a586fc2a8b518f9bc111dfd6df6e9fd64e8 (Nat.shiftLeft
  0x100bedae604c481b669451b2ea367158561ae9c0101f164fd996a8c6 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (109, (mkQ
  false (Nat.add (Nat.add 0xf3ec4e6586daf3e682beb81e83af0a2c4a06d9d0805a5e8bcfc3be347b736187b2902693
  (Nat.shiftLeft (Nat.add 0x51cb0b171b173f5d74ee2f9443515206cd7915e910debeef8e2dcd131238dc752def6b6a
  (Nat.shiftLeft 0xa4f6c1f70a7891ab84320e4b263eb8829262877773146ef5018201cbf8563542fc51b840 288))
  288)) (Nat.shiftLeft (Nat.add
  0x166fe0d5983dcd1953a2acf865bd1202ce6c84d859d3cbbffc6b7547f1e7fe8050ba3978 (Nat.shiftLeft (Nat.add
  0x30a12c74cad1b3a891490af3b668906422928f6e987ba5c31ec1441787b5df6df3ff6fa3 (Nat.shiftLeft
  0x816cd4a1b3c922f293b074b509d4ac4b2288097407b53a809dc0d3 288)) 288)) 864)) (Nat.add (Nat.add
  0x3206ea1f02d36457556c08c9483017cc867e0fd4abd75e18b58fec0124a163ecb5e90000 (Nat.shiftLeft (Nat.add
  0x3782fd86c5bfeb23e26e50677d9403f14dc8dc2b9a3037e502f0e16b518c273003786755 (Nat.shiftLeft
  0x5c07729b9e463aba9d91c91262b4eff759225c35a39ae55ca6f06d0e408feaad3ce3626c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb79a78eb4decae62b8e82ee6da3fcf697ccefdfcab6c6f7829f90f5177da276d353887cc
  (Nat.shiftLeft (Nat.add 0x617245e435822d53ea77dcd9c0fa78e541af33734508ebb76a5e7237d77524ba5ef62ffb
  (Nat.shiftLeft 0x359f5bf571984f6106f0e3415daf60bdd433802b57b2a8 288)) 288)) 864)))), (137, (mkQ
  false (Nat.add (Nat.add 0xd2d2396342fdf165256c0c82caec8adebe8c11b90b54ccc40cbef6b8023de5d0bca22c2b
  (Nat.shiftLeft (Nat.add 0xedf50ac703360f7321f559d9331264bcbc467e9c0c1d81c8173f412a907517d30f96823b
  (Nat.shiftLeft 0x6b739db04a55cf7e291e86f058992ac5c5d815ac7d461b54cc11b2776b9b1f4b445706eb 288))
  288)) (Nat.shiftLeft (Nat.add
  0x184a4640902db87e54eb6fc38cf30e5b7f0be45c5d75921700b5af0c7c347e592a5b5e6a (Nat.shiftLeft (Nat.add
  0xe7e9aae20cf848f69c9c5b8070ccc3c47bab559dc6f4d36ad7b3817910e3df54f2a8c892 (Nat.shiftLeft
  0x1c074964ccf75e2255bcf9bceb571bb30595ad6589c40d101526dd40 288)) 288)) 864)) (Nat.add (Nat.add
  0x1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e080000 (Nat.shiftLeft (Nat.add
  0x5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8f (Nat.shiftLeft
  0xe5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x70ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a7
  (Nat.shiftLeft (Nat.add 0x21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca7
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938c 288)) 288)) 864)))), (139, (mkQ
  false (Nat.add (Nat.add 0xb7a5357b358e6ab5bc54d8b1657d292f618250bfdb14d5530b15a8a3e3a77138a10b7975
  (Nat.shiftLeft (Nat.add 0xf9ce91e6c1feaf66a6004a70d7e98d0bea72c779bb69799bb76e155bea8ecb1237808afa
  (Nat.shiftLeft 0xf889f9d4328013d99bc59207c9c8d8189857b61d6c3d47370663ee92f55b93135f84f565 288))
  288)) (Nat.shiftLeft (Nat.add
  0xce2a0fd65c5baf48139655a31ee2e946a5f0f8166356e15bf2d062a621f78ff0c400705b (Nat.shiftLeft (Nat.add
  0xf53beb74c8ec6ffd8dccd0fb82d4cc870de79e055aad5e946b10c571161ebf3e78f91a93 (Nat.shiftLeft
  0x1b92924e20d8ea965739b1405e62c9a18cdaeee2a2b53860d539d14a 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (141, (mkQ
  false (Nat.add (Nat.add 0x8341b09942ea19eace9f9f886e3ca32d72d851fa76d637d4eba561561ee73662ef6e3859
  (Nat.shiftLeft (Nat.add 0x22126a217ca27260fa920ba0decd348240864b1214f24c5f79821eb754cb485f5e1d16bc
  (Nat.shiftLeft 0xed6648d210e30820a62956d263cc6618e72ff2c052ef5db73611f478b93fc850a9b01f52 288))
  288)) (Nat.shiftLeft (Nat.add
  0x58bdf06b15ee4195871b59198f95500b2d515f886f770d4c6ec214a96dc402d1f624aaf (Nat.shiftLeft (Nat.add
  0x201a18a9c58cc38c6df7aca545d54c2266e3070ea5325650a0faa43be80564450a478977 (Nat.shiftLeft
  0x4dd11b999983dd5536009fbe700066351c5d7050e7b0ba65ff19cc 288)) 288)) 864)) (Nat.add (Nat.add
  0xa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd2000 (Nat.shiftLeft (Nat.add
  0x86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0cea (Nat.shiftLeft
  0x8b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f9
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af655 288)) 288)) 864)))), (143, (mkQ
  false (Nat.add (Nat.add 0xef8126f28be8222f18e51ec2b686df46fa056b03b9af8989c2cf9e81b393dda6f0b3e12d
  (Nat.shiftLeft (Nat.add 0x5e5cbe862f523d074e39870eae1adaa67323acb215b0abc42d7c832df15866137cc69dc8
  (Nat.shiftLeft 0xd9a700dc54680cf3a8f3939696e7a279a97ec980aeef68ed5d73c30c21a1ebdb7f447955 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4227c0fe2ab0d43c0813aae01c3a9bcd37f407740819c84441dce71b58e71a428f56f207 (Nat.shiftLeft (Nat.add
  0x829f016a8dc69bd0acd3cb8a0eb5c7b14d33757fe14ea0e435d26bce8e2a560e08c4f997 (Nat.shiftLeft
  0x13e9b778bdcb1713a1810474b3f8812825a1e6850952cfd009362f3 288)) 288)) 864)) (Nat.add (Nat.add
  0xaa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd200 (Nat.shiftLeft (Nat.add
  0xd86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ce (Nat.shiftLeft
  0x98b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f
  (Nat.shiftLeft (Nat.add 0x50c2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5f
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af65 288)) 288)) 864)))), (145, (mkQ
  false (Nat.add (Nat.add 0x9e3f8ddaba81dd612908970e5d59abecaf71e766a34ddefd01acfec1611226425ef420cf
  (Nat.shiftLeft (Nat.add 0x4c10b78c27195aa95de766bef717036e164e7e3e3c6a0dcf99b92687096d847a331e5174
  (Nat.shiftLeft 0x44712649c03eaaf0e435777ca529e0799f85c820ff80720764cc3fccd85163d00ab542e4 288))
  288)) (Nat.shiftLeft (Nat.add
  0x7f0773e2f2a296d9983fe932399d3263403ed810a9bc70841d5343e8e4c62deb59f1a574 (Nat.shiftLeft (Nat.add
  0x6563c4cf955c560e571b0d2ee857e008b31a145840918f80f55dd0b8aa62b5e1fb7c3606 (Nat.shiftLeft
  0x133ddb3d63989ad32511337a0c23d50e2fcbbe0a18e87f72f4d2d41 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (147, (mkQ
  false (Nat.add (Nat.add 0xd5079e538d0923ff6fd2de51208a5bddb719c9c2f3edebd5af72711ead4ca5ab3394561b
  (Nat.shiftLeft (Nat.add 0x752dff6317bbdda9ce61fcbc1508efc226693f9d4f28dff77cc1d39b61e180f29b31cfdb
  (Nat.shiftLeft 0xfba75fa377d9968b91791a1d93a111c4b1f0fe982162082f36ff90aa0af2d6479461660d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdfd21e1df9e12076880b33f76f5d650339459881ea5381978b03a25e699195ed6939ae47 (Nat.shiftLeft (Nat.add
  0xf73dd986005349bbd2bb259108b13c20cffa25d6642d897466a182ac77ce462680afa3e9 (Nat.shiftLeft
  0x82c42968a494cc56398d8722580656248c23452a5fd1407148cf01e 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (175, (mkQ
  false (Nat.add (Nat.add 0xf2377270a13cbd1b9b78cadb757d05bfa5cb2cb8afbc806f5d6f2a47d81c61ac8c11d063
  (Nat.shiftLeft (Nat.add 0xbf9824d52efd11d10469aa8ab531280b652f594750d2eac9c673799c8181d14d9efd3237
  (Nat.shiftLeft 0x5db129d12c9204edc1cc1cee3f0952cffa3155e1f5288776b2a35a1941b18c0b77336161 288))
  288)) (Nat.shiftLeft (Nat.add
  0x1791a0ad37151f7a53efbe8afa7ed83292e7bddb55389d2aca863601f41ca19d1aca52fb (Nat.shiftLeft (Nat.add
  0x7f653dd06e109678d08552cf5877914712978da46a631ab767e88105e722cc83314a0105 (Nat.shiftLeft
  0x1b07732f9ed29fbaa8875d7c7437805068d69cd733da0b6bab8545f 288)) 288)) 864)) (Nat.add (Nat.add
  0x640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd20000 (Nat.shiftLeft (Nat.add
  0x6f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa (Nat.shiftLeft
  0xb80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff7
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550 288)) 288)) 864)))), (177, (mkQ
  false (Nat.add (Nat.add 0xd6ac500046b590c48aba185b101cb231479a4d0974c87b80d4aaa91884eba2e7b7169f0f
  (Nat.shiftLeft (Nat.add 0xc4ca3cb84288e982f5109cc01d2fc90f053c27a87cb8a10d08b7c64aaef38d6422f72059
  (Nat.shiftLeft 0x96e27e1a004dea2acfe3cfa91e5be2d5c16b15a6731794e05efa8d314daf383c9d622e6c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x5bf7b9338df582934f5d6c0f5868b61ff7a427eba8fcb6b793ff1c5f8c196f1cc9f14c98 (Nat.shiftLeft (Nat.add
  0xe4e7d32ff6426417a59edbd88be28a7b02fc244617e282a894ab950f0628e91aac45e9bb (Nat.shiftLeft
  0x3d4917c59b2f237d80ef54cf4a59c0df663beabf19089e79077ee38 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (179, (mkQ
  false (Nat.add (Nat.add 0xc686f8321f493a52bd3199c6a230b2169fcb6b2ec136265ab8918b5e343efd97c54d34bf
  (Nat.shiftLeft (Nat.add 0xafbbd9c8faa1e9e9d71f8fcb8b527b0321d11aea9c8c632b06218de96deb178e4ae16833
  (Nat.shiftLeft 0x925f0608878a6cdd3b6599bdcdd8f6da8612421eae924294bca3da370e124e262457736f 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd2d0744c1b4a005ff31ad4d4c5afec4dff9efea76af17ad2069999fbb8709b64ea422835 (Nat.shiftLeft (Nat.add
  0xe893b8c264b47448f8de387b34feb478ce928ded361de0993ecde6cb5ad99e60ad933f5 (Nat.shiftLeft
  0xb05fbb0f065287161eefacdefd6ad66e09822e1bef1aa111fdce2e1 288)) 288)) 864)) (Nat.add (Nat.add
  0xa7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e363400 (Nat.shiftLeft (Nat.add
  0x74563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812 (Nat.shiftLeft
  0xf73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xaa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9b
  (Nat.shiftLeft (Nat.add 0x279ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbf
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f5 288)) 288)) 864)))), (181, (mkQ
  false (Nat.add (Nat.add 0xc686f8321f493a52bd3199c6a230b2169fcb6b2ec136265ab8918b5e343efd97c54d34bf
  (Nat.shiftLeft (Nat.add 0xafbbd9c8faa1e9e9d71f8fcb8b527b0321d11aea9c8c632b06218de96deb178e4ae16833
  (Nat.shiftLeft 0x925f0608878a6cdd3b6599bdcdd8f6da8612421eae924294bca3da370e124e262457736f 288))
  288)) (Nat.shiftLeft (Nat.add
  0xd2d0744c1b4a005ff31ad4d4c5afec4dff9efea76af17ad2069999fbb8709b64ea422835 (Nat.shiftLeft (Nat.add
  0xe893b8c264b47448f8de387b34feb478ce928ded361de0993ecde6cb5ad99e60ad933f5 (Nat.shiftLeft
  0xb05fbb0f065287161eefacdefd6ad66e09822e1bef1aa111fdce2e1 288)) 288)) 864)) (Nat.add (Nat.add
  0xa7e88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e363400 (Nat.shiftLeft (Nat.add
  0x74563bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812 (Nat.shiftLeft
  0xf73094f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xaa58117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9b
  (Nat.shiftLeft (Nat.add 0x279ced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbf
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f5 288)) 288)) 864)))), (183, (mkQ
  false (Nat.add (Nat.add 0xd6ac500046b590c48aba185b101cb231479a4d0974c87b80d4aaa91884eba2e7b7169f0f
  (Nat.shiftLeft (Nat.add 0xc4ca3cb84288e982f5109cc01d2fc90f053c27a87cb8a10d08b7c64aaef38d6422f72059
  (Nat.shiftLeft 0x96e27e1a004dea2acfe3cfa91e5be2d5c16b15a6731794e05efa8d314daf383c9d622e6c 288))
  288)) (Nat.shiftLeft (Nat.add
  0x5bf7b9338df582934f5d6c0f5868b61ff7a427eba8fcb6b793ff1c5f8c196f1cc9f14c98 (Nat.shiftLeft (Nat.add
  0xe4e7d32ff6426417a59edbd88be28a7b02fc244617e282a894ab950f0628e91aac45e9bb (Nat.shiftLeft
  0x3d4917c59b2f237d80ef54cf4a59c0df663beabf19089e79077ee38 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (185, (mkQ
  false (Nat.add (Nat.add 0xf2377270a13cbd1b9b78cadb757d05bfa5cb2cb8afbc806f5d6f2a47d81c61ac8c11d063
  (Nat.shiftLeft (Nat.add 0xbf9824d52efd11d10469aa8ab531280b652f594750d2eac9c673799c8181d14d9efd3237
  (Nat.shiftLeft 0x5db129d12c9204edc1cc1cee3f0952cffa3155e1f5288776b2a35a1941b18c0b77336161 288))
  288)) (Nat.shiftLeft (Nat.add
  0x1791a0ad37151f7a53efbe8afa7ed83292e7bddb55389d2aca863601f41ca19d1aca52fb (Nat.shiftLeft (Nat.add
  0x7f653dd06e109678d08552cf5877914712978da46a631ab767e88105e722cc83314a0105 (Nat.shiftLeft
  0x1b07732f9ed29fbaa8875d7c7437805068d69cd733da0b6bab8545f 288)) 288)) 864)) (Nat.add (Nat.add
  0x640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd20000 (Nat.shiftLeft (Nat.add
  0x6f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ceaa (Nat.shiftLeft
  0xb80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d8 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x6f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f98
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff7
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af6550 288)) 288)) 864)))), (213, (mkQ
  false (Nat.add (Nat.add 0xd5079e538d0923ff6fd2de51208a5bddb719c9c2f3edebd5af72711ead4ca5ab3394561b
  (Nat.shiftLeft (Nat.add 0x752dff6317bbdda9ce61fcbc1508efc226693f9d4f28dff77cc1d39b61e180f29b31cfdb
  (Nat.shiftLeft 0xfba75fa377d9968b91791a1d93a111c4b1f0fe982162082f36ff90aa0af2d6479461660d 288))
  288)) (Nat.shiftLeft (Nat.add
  0xdfd21e1df9e12076880b33f76f5d650339459881ea5381978b03a25e699195ed6939ae47 (Nat.shiftLeft (Nat.add
  0xf73dd986005349bbd2bb259108b13c20cffa25d6642d897466a182ac77ce462680afa3e9 (Nat.shiftLeft
  0x82c42968a494cc56398d8722580656248c23452a5fd1407148cf01e 288)) 288)) 864)) (Nat.add (Nat.add
  0x78ab3741d1a93321d5e336ea032c94be4893e2f132020c1a6ec3830724f0b08770f04000 (Nat.shiftLeft (Nat.add
  0x5af2b08a53ef7da047317686d0dd18a42627601083ad5d57526180debdabf4ec15b085d4 (Nat.shiftLeft
  0x3f2e8c4c9d36ef0e58cf28b2e8eadbc9ed16c04f3e881983135ea99913837ababc8d2724 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x3b8573bea70741e903ab2522d40ed0534c0db36b2f65b8af06549fbd2d13766a8ca150bd
  (Nat.shiftLeft (Nat.add 0x610a34d24e6d9b4c796d2450f61d7398da8701906f77c13a58ce49dd029c258cd182abe5
  (Nat.shiftLeft 0x14f23febe05f7f01e6b618c5889881ca26e41e10ee41c9c 288)) 288)) 864)))), (215, (mkQ
  false (Nat.add (Nat.add 0x9e3f8ddaba81dd612908970e5d59abecaf71e766a34ddefd01acfec1611226425ef420cf
  (Nat.shiftLeft (Nat.add 0x4c10b78c27195aa95de766bef717036e164e7e3e3c6a0dcf99b92687096d847a331e5174
  (Nat.shiftLeft 0x44712649c03eaaf0e435777ca529e0799f85c820ff80720764cc3fccd85163d00ab542e4 288))
  288)) (Nat.shiftLeft (Nat.add
  0x7f0773e2f2a296d9983fe932399d3263403ed810a9bc70841d5343e8e4c62deb59f1a574 (Nat.shiftLeft (Nat.add
  0x6563c4cf955c560e571b0d2ee857e008b31a145840918f80f55dd0b8aa62b5e1fb7c3606 (Nat.shiftLeft
  0x133ddb3d63989ad32511337a0c23d50e2fcbbe0a18e87f72f4d2d41 288)) 288)) 864)) (Nat.add (Nat.add
  0x9fa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d000 (Nat.shiftLeft (Nat.add
  0xd158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a (Nat.shiftLeft
  0xdcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xa96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6f
  (Nat.shiftLeft (Nat.add 0x9e73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefe
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d4 288)) 288)) 864)))), (217, (mkQ
  false (Nat.add (Nat.add 0xef8126f28be8222f18e51ec2b686df46fa056b03b9af8989c2cf9e81b393dda6f0b3e12d
  (Nat.shiftLeft (Nat.add 0x5e5cbe862f523d074e39870eae1adaa67323acb215b0abc42d7c832df15866137cc69dc8
  (Nat.shiftLeft 0xd9a700dc54680cf3a8f3939696e7a279a97ec980aeef68ed5d73c30c21a1ebdb7f447955 288))
  288)) (Nat.shiftLeft (Nat.add
  0x4227c0fe2ab0d43c0813aae01c3a9bcd37f407740819c84441dce71b58e71a428f56f207 (Nat.shiftLeft (Nat.add
  0x829f016a8dc69bd0acd3cb8a0eb5c7b14d33757fe14ea0e435d26bce8e2a560e08c4f997 (Nat.shiftLeft
  0x13e9b778bdcb1713a1810474b3f8812825a1e6850952cfd009362f3 288)) 288)) 864)) (Nat.add (Nat.add
  0xaa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd200 (Nat.shiftLeft (Nat.add
  0xd86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0ce (Nat.shiftLeft
  0x98b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xf76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f
  (Nat.shiftLeft (Nat.add 0x50c2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5f
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af65 288)) 288)) 864)))), (219, (mkQ
  false (Nat.add (Nat.add 0x8341b09942ea19eace9f9f886e3ca32d72d851fa76d637d4eba561561ee73662ef6e3859
  (Nat.shiftLeft (Nat.add 0x22126a217ca27260fa920ba0decd348240864b1214f24c5f79821eb754cb485f5e1d16bc
  (Nat.shiftLeft 0xed6648d210e30820a62956d263cc6618e72ff2c052ef5db73611f478b93fc850a9b01f52 288))
  288)) (Nat.shiftLeft (Nat.add
  0x58bdf06b15ee4195871b59198f95500b2d515f886f770d4c6ec214a96dc402d1f624aaf (Nat.shiftLeft (Nat.add
  0x201a18a9c58cc38c6df7aca545d54c2266e3070ea5325650a0faa43be80564450a478977 (Nat.shiftLeft
  0x4dd11b999983dd5536009fbe700066351c5d7050e7b0ba65ff19cc 288)) 288)) 864)) (Nat.add (Nat.add
  0xa640dd43e05a6c8aeaad8119290602f990cfc1fa957aebc316b1fd8024942c7d96bd2000 (Nat.shiftLeft (Nat.add
  0x86f05fb0d8b7fd647c4dca0cefb2807e29b91b85734606fca05e1c2d6a3184e6006f0cea (Nat.shiftLeft
  0x8b80ee5373c8c75753b239224c569dfeeb244b86b4735cab94de0da1c811fd55a79c6c4d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x76f34f1d69bd95cc571d05dcdb47f9ed2f99dfbf956d8def053f21ea2efb44eda6a710f9
  (Nat.shiftLeft (Nat.add 0xc2e48bc86b045aa7d4efb9b381f4f1ca835e66e68a11d76ed4bce46faeea4974bdec5ff
  (Nat.shiftLeft 0x6b3eb7eae3309ec20de1c682bb5ec17ba8670056af655 288)) 288)) 864)))), (221, (mkQ
  false (Nat.add (Nat.add 0xb7a5357b358e6ab5bc54d8b1657d292f618250bfdb14d5530b15a8a3e3a77138a10b7975
  (Nat.shiftLeft (Nat.add 0xf9ce91e6c1feaf66a6004a70d7e98d0bea72c779bb69799bb76e155bea8ecb1237808afa
  (Nat.shiftLeft 0xf889f9d4328013d99bc59207c9c8d8189857b61d6c3d47370663ee92f55b93135f84f565 288))
  288)) (Nat.shiftLeft (Nat.add
  0xce2a0fd65c5baf48139655a31ee2e946a5f0f8166356e15bf2d062a621f78ff0c400705b (Nat.shiftLeft (Nat.add
  0xf53beb74c8ec6ffd8dccd0fb82d4cc870de79e055aad5e946b10c571161ebf3e78f91a93 (Nat.shiftLeft
  0x1b92924e20d8ea965739b1405e62c9a18cdaeee2a2b53860d539d14a 288)) 288)) 864)) (Nat.add (Nat.add
  0xf44525361c41eb69563857dcd1e0edfd40ec9e4eb669acf7179f380b6e4de73f1b1a0000 (Nat.shiftLeft (Nat.add
  0x2b1de743b97f2f66d84f240ae7c8276d09d899b405e22ef21d68ce312f7987e022b40953 (Nat.shiftLeft
  0x984a7a142ebe4b4a27b1dab7db115fa97b579a18640cf59e8564428e859f2ac460e1d83a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x2c08b9310b3ecfdb3911d504867e1a1ee015ebdeb23c5ab1a3ba992eae858a4414354dfb
  (Nat.shiftLeft (Nat.add 0xce76baea1715c54728aea08189c8b8f490d80280b259352a27b0762e6a936f47b59ddfd5
  (Nat.shiftLeft 0x2183997966ff319ca4568e08da8d9c76a4a0301b16cfa93 288)) 288)) 864)))), (223, (mkQ
  false (Nat.add (Nat.add 0xd2d2396342fdf165256c0c82caec8adebe8c11b90b54ccc40cbef6b8023de5d0bca22c2b
  (Nat.shiftLeft (Nat.add 0xedf50ac703360f7321f559d9331264bcbc467e9c0c1d81c8173f412a907517d30f96823b
  (Nat.shiftLeft 0x6b739db04a55cf7e291e86f058992ac5c5d815ac7d461b54cc11b2776b9b1f4b445706eb 288))
  288)) (Nat.shiftLeft (Nat.add
  0x184a4640902db87e54eb6fc38cf30e5b7f0be45c5d75921700b5af0c7c347e592a5b5e6a (Nat.shiftLeft (Nat.add
  0xe7e9aae20cf848f69c9c5b8070ccc3c47bab559dc6f4d36ad7b3817910e3df54f2a8c892 (Nat.shiftLeft
  0x1c074964ccf75e2255bcf9bceb571bb30595ad6589c40d101526dd40 288)) 288)) 864)) (Nat.add (Nat.add
  0x1566e83a3526643abc66dd40659297c9127c5e264041834dd87060e49e1610ee1e080000 (Nat.shiftLeft (Nat.add
  0x5e56114a7defb408e62ed0da1ba31484c4ec021075abaaea4c301bd7b57e9d82b610ba8f (Nat.shiftLeft
  0xe5d18993a6dde1cb19e5165d1d5b793da2d809e7d10330626bd53322706f575791a4e48b 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x70ae77d4e0e83d207564a45a81da0a6981b66d65ecb715e0ca93f7a5a26ecd51942a17a7
  (Nat.shiftLeft (Nat.add 0x21469a49cdb3698f2da48a1ec3ae731b50e0320deef8274b19c93ba05384b19a30557ca7
  (Nat.shiftLeft 0x29e47fd7c0befe03cd6c318b113103944dc83c21dc83938c 288)) 288)) 864)))), (251, (mkQ
  false (Nat.add (Nat.add 0xf3ec4e6586daf3e682beb81e83af0a2c4a06d9d0805a5e8bcfc3be347b736187b2902693
  (Nat.shiftLeft (Nat.add 0x51cb0b171b173f5d74ee2f9443515206cd7915e910debeef8e2dcd131238dc752def6b6a
  (Nat.shiftLeft 0xa4f6c1f70a7891ab84320e4b263eb8829262877773146ef5018201cbf8563542fc51b840 288))
  288)) (Nat.shiftLeft (Nat.add
  0x166fe0d5983dcd1953a2acf865bd1202ce6c84d859d3cbbffc6b7547f1e7fe8050ba3978 (Nat.shiftLeft (Nat.add
  0x30a12c74cad1b3a891490af3b668906422928f6e987ba5c31ec1441787b5df6df3ff6fa3 (Nat.shiftLeft
  0x816cd4a1b3c922f293b074b509d4ac4b2288097407b53a809dc0d3 288)) 288)) 864)) (Nat.add (Nat.add
  0x3206ea1f02d36457556c08c9483017cc867e0fd4abd75e18b58fec0124a163ecb5e90000 (Nat.shiftLeft (Nat.add
  0x3782fd86c5bfeb23e26e50677d9403f14dc8dc2b9a3037e502f0e16b518c273003786755 (Nat.shiftLeft
  0x5c07729b9e463aba9d91c91262b4eff759225c35a39ae55ca6f06d0e408feaad3ce3626c 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xb79a78eb4decae62b8e82ee6da3fcf697ccefdfcab6c6f7829f90f5177da276d353887cc
  (Nat.shiftLeft (Nat.add 0x617245e435822d53ea77dcd9c0fa78e541af33734508ebb76a5e7237d77524ba5ef62ffb
  (Nat.shiftLeft 0x359f5bf571984f6106f0e3415daf60bdd433802b57b2a8 288)) 288)) 864)))), (253, (mkQ
  true (Nat.add (Nat.add 0xcdbdca67677cf3a1eaf1edead1baa82d1e59b3c39b79286dab408eb7c39cd688dee866fb
  (Nat.shiftLeft (Nat.add 0x57381372817b8b9fdb1a829f1fabe64c8653f7f08b8d719e2c1fe30222ae302ffa41ba99
  (Nat.shiftLeft 0xe6c426c4988092a954c06349d9ec44ec0344a1fd88137efddbb50672288174195b76d9 288)) 288)
  ) (Nat.shiftLeft (Nat.add
  0xf4b2406b607b2d3f9de1b394b163ed72568587f4afb2844418f4f485138b6f5a11b374a3 (Nat.shiftLeft (Nat.add
  0x3f7d72724fa02307e321a8784c9361deca294a586fc2a8b518f9bc111dfd6df6e9fd64e8 (Nat.shiftLeft
  0x100bedae604c481b669451b2ea367158561ae9c0101f164fd996a8c6 288)) 288)) 864)) (Nat.add (Nat.add
  0xfd11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c68000 (Nat.shiftLeft (Nat.add
  0x8ac779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254 (Nat.shiftLeft
  0xe6129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x4b022e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537e
  (Nat.shiftLeft (Nat.add 0xf39daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f5
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4 288)) 288)) 864)))), (255, (mkQ
  false (Nat.add (Nat.add 0xa17eb4fcdc8e5f1956fa66161a5cd904a2526d158825773e84ea8a236c1e64ff807f40d1
  (Nat.shiftLeft (Nat.add 0x8df9c564ecda1b65620c03f0b03ed7e8f3335558021763bcc1baddb72ab30266b535c3d1
  (Nat.shiftLeft 0xdad89879cd40b9648459a18dabfb93055090d46bcf4f163a3021ad53881700aebc6318ec 288))
  288)) (Nat.shiftLeft (Nat.add
  0x65807a0facfba0e88a8ddcc78c869064d76cb86df85fd0ac4a425246b677b1af9004e1bd (Nat.shiftLeft (Nat.add
  0x347d4bdc2c95d3b0ccdae717860d64bb20d49c8d3f567b69b8dd73a8ba923b29399fad15 (Nat.shiftLeft
  0x358eee76846d5de902439a5f3e59857cb5e1ad56f1f9fcaf0670fb64 288)) 288)) 864)) (Nat.add (Nat.add
  0xfa22929b0e20f5b4ab1c2bee68f076fea0764f275b34d67b8bcf9c05b726f39f8d8d0000 (Nat.shiftLeft (Nat.add
  0x158ef3a1dcbf97b36c27920573e413b684ec4cda02f117790eb4671897bcc3f0115a04a9 (Nat.shiftLeft
  0xcc253d0a175f25a513d8ed5bed88afd4bdabcd0c32067acf42b2214742cf95623070ec1d 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x96045c98859f67ed9c88ea82433f0d0f700af5ef591e2d58d1dd4c975742c5220a1aa6fd
  (Nat.shiftLeft (Nat.add 0xe73b5d750b8ae2a394575040c4e45c7a486c0140592c9a9513d83b173549b7a3daceefea
  (Nat.shiftLeft 0x10c1ccbcb37f98ce522b47046d46ce3b5250180d8b67d49 288)) 288)) 864)))), (257, (mkQ
  false (Nat.add (Nat.add 0xbd573e69a975f80d8e161327cae6530879eb79e43f505d24afd913886b0d5353128f2083
  (Nat.shiftLeft (Nat.add 0xd10bb9ef53847ea7c60d798813b7a62518496ac1a3863ba1fe12fbf3aa095e664a9ee262
  (Nat.shiftLeft 0x64d74b66cbf748c3cd5110568f57382ff7fddb872615da44fc2a2edb5dc31d1c8ab126ae 288))
  288)) (Nat.shiftLeft (Nat.add
  0xc1ab177b10c443452e6939a99ee14e33f7bb60310e1c291597aa9e9bf7f36b7bedffef87 (Nat.shiftLeft (Nat.add
  0x18af06a3ff7c5ab9991b455bf372e7af27fab073693570d584d008d604401569bf77a6d2 (Nat.shiftLeft
  0x526cacb79efb84a7e669e88afabc8d5f1e3e964ef615c60250c75fc 288)) 288)) 864)) (Nat.add (Nat.add
  0xc81ba87c0b4d915d55b0232520c05f3219f83f52af5d7862d63fb00492858fb2d7a40000 (Nat.shiftLeft (Nat.add
  0xde0bf61b16ffac8f89b9419df6500fc5372370ae68c0df940bc385ad46309cc00de19d54 (Nat.shiftLeft
  0x701dca6e7918eaea764724498ad3bfdd648970d68e6b95729bc1b439023faab4f38d89b0 288)) 288)) (
  Nat.shiftLeft (Nat.add 0xde69e3ad37b2b98ae3a0bb9b68ff3da5f33bf7f2adb1bde0a7e43d45df689db4d4e21f31
  (Nat.shiftLeft (Nat.add 0x85c91790d608b54fa9df736703e9e39506bccdcd1423aedda979c8df5dd492e97bd8bfee
  (Nat.shiftLeft 0xd67d6fd5c6613d841bc38d0576bd82f750ce00ad5ecaa1 288)) 288)) 864)))), (259, (mkQ
  false (Nat.add (Nat.add 0xcddba7a5f11358077556fe3c2f6f35ac78bb6c9d42b2049b70487f72782118d6e9f0d797
  (Nat.shiftLeft (Nat.add 0x78a80123fee920f89ec0ed88cbf43f2885c68c11fc36fc41957f6cd1621f5a84e9c98b9
  (Nat.shiftLeft 0x360374fe933e9b4826148a2e6667fafb454b30f31727a08d19ce1dc856061c222843c8d1 288))
  288)) (Nat.shiftLeft (Nat.add
  0xfa73b42111faa9545b59a04cb8f363938f7931961674c93ba58bbdf6dd76163371bf0587 (Nat.shiftLeft (Nat.add
  0x2d819ec6fbc7325679d4e2be4f34df7927562bf5a126075879921977f5c774de6430471 (Nat.shiftLeft
  0x38333c7af7404832677afac3babeda42c0011317d3aac150b6b2fa5b 288)) 288)) 864)) (Nat.add (Nat.add
  0x88a4a6c3883d6d2ac70afb9a3c1dbfa81d93c9d6cd359ee2f3e7016dc9bce7e363400000 (Nat.shiftLeft (Nat.add
  0x63bce8772fe5ecdb09e4815cf904eda13b133680bc45de43ad19c625ef30fc0456812a7e (Nat.shiftLeft
  0x94f4285d7c96944f63b56fb622bf52f6af3430c819eb3d0ac8851d0b3e5588c1c3b0745 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x8117262167d9fb67223aa090cfc343dc02bd7bd6478b5634775325d5d0b1488286a9bf73
  (Nat.shiftLeft (Nat.add 0xced75d42e2b8a8e515d4103139171e921b0050164b26a544f60ec5cd526de8f6b3bbfaa5
  (Nat.shiftLeft 0x430732f2cdfe633948ad1c11b51b38ed494060362d9f5279 288)) 288)) 864)))), (261, (mkQ
  false (Nat.add (Nat.add 0xf0789e24301d8d5d7bab114a71eb4dc9cb1acd571fdcc1817710d629fafefa210a38cb89
  (Nat.shiftLeft (Nat.add 0xcc6f965ece38c720e496517e9d963a4c5e94ed453eebbb6c85f0d42e05ee33a60aac0715
  (Nat.shiftLeft 0xb79c76ce958083270233316e60df81df51aa2056cc74d25d5c298dba30bd4c0bd24334d5 288))
  288)) (Nat.shiftLeft (Nat.add
  0x3fab787e2bc696d5d01420db225c939cac33b23ef290fcbb8f8712faf53546a39ebe6f40 (Nat.shiftLeft (Nat.add
  0x4d10dee972e5c956c2aff470a178573954fb81e646d3941a4a65357673e0d059ac813cde (Nat.shiftLeft
  0x281fa8e82cfaa44c812570a7e462ae531e82f83c21a451c63fdb080 288)) 288)) 864)) (Nat.add (Nat.add
  0x11494d87107ada558e15f734783b7f503b2793ad9a6b3dc5e7ce02db9379cfc6c6800000 (Nat.shiftLeft (Nat.add
  0xc779d0ee5fcbd9b613c902b9f209db4276266d01788bbc875a338c4bde61f808ad0254fd (Nat.shiftLeft
  0x129e850baf92d289ec76adf6c457ea5ed5e68619033d67a15910a3a167cab11838760e8a 288)) 288)) (
  Nat.shiftLeft (Nat.add 0x22e4c42cfb3f6ce447541219f8687b8057af7ac8f16ac68eea64baba16291050d537ee6 (
  Nat.shiftLeft (Nat.add 0x9daeba85c57151ca2ba82062722e3d243600a02c964d4a89ec1d8b9aa4dbd1ed6777f54b
  (Nat.shiftLeft 0x860e65e59bfcc672915a38236a3671da9280c06c5b3ea4f3 288)) 288)) 864))))])]

def sjsuTsp_329 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 5, 0), [(90, (mkQ false (
  Nat.add (Nat.add 0x315fae57816f48dac18fbd07f2bc46ab795c46874a2f26fd217b96f06416686d2df9c857 (
  Nat.shiftLeft 0x5326c8114630e5d38a64ce7f0250b39b6a721b00559705154675b128bbfb2c4e32b5f49d 288)) (
  Nat.shiftLeft (Nat.add 0xc1c09bf82fd87b0f7ffa1b9d14cd57bce06b958a3ec29832ad9d62dd5525f54cd15e3a40
  (Nat.shiftLeft 0x10bdb7de89b36fd5113da76e9e5 288)) 576)) (Nat.add (Nat.add
  0x43359c7f893910db5ee567fcf4f3f74768b668ce86ca1643499ea92756e607d484000000 (Nat.shiftLeft
  0xc68a702fe84112cd7ef6b425277c766b36f02ef4aba4c5885b306f66bc760de434c80753 288)) (Nat.shiftLeft (
  Nat.add 0x5e033901ecefeb76d872cff619ad549f20c407c1d33344a681240d7394df744d1a69e0bb (Nat.shiftLeft
  0x1008896bcf57ac08839547edd0 288)) 576)))), (126, (mkQ true (Nat.add (Nat.add
  0x2dd2fcbaad994c0bf65a83b6b1a496d97cf4482abdcc0cf806ff160b212acdcde0317a29 (Nat.shiftLeft
  0xffa19af5b3836b1394bb53009b3377044d7b2e4488216ab7d950ce0268a3e3caf4b84f1 288)) (Nat.shiftLeft (
  Nat.add 0x2bd1d52175366225ffa1746654c3dbb365ec76f7fd9b3ada2a2d936cbb6955f301e59ae0 (Nat.shiftLeft
  0x8db11f740f5516282a7c4edbfb3 288)) 576)) (Nat.add (Nat.add
  0xa19ace3fc49c886daf72b3fe7a79fba3b45b346743650b21a4cf5493ab7303ea42000000 (Nat.shiftLeft
  0xe3453817f4208966bf7b5a1293be3b359b78177a55d262c42d9837b35e3b06f21a6403a9 288)) (Nat.shiftLeft (
  Nat.add 0x2f019c80f677f5bb6c3967fb0cd6aa4f906203e0e999a253409206b9ca6fba268d34f05d (Nat.shiftLeft
  0x80444b5e7abd60441caa3f6e8 288)) 576)))), (162, (mkQ true (Nat.add (Nat.add
  0x2479bf36baf7c9227e10897220907d774802a6a0fc78c6e7219124ec7347e64a0f86a8cf (Nat.shiftLeft
  0xf045e2bbe150dbe68de110ad2b0a10ddf19314da845c4bc09ade72d8a644fbe71daf33b4 288)) (Nat.shiftLeft (
  Nat.add 0x9d13f2ac55176382ec89830a1d78839bb25237e3c08c09524b1927b8ad737b40bbe1d362 (Nat.shiftLeft
  0x2d26e2762aef58b8406f0d72bf88 288)) 576)) (Nat.add (Nat.add
  0xa19ace3fc49c886daf72b3fe7a79fba3b45b346743650b21a4cf5493ab7303ea42000000 (Nat.shiftLeft
  0xe3453817f4208966bf7b5a1293be3b359b78177a55d262c42d9837b35e3b06f21a6403a9 288)) (Nat.shiftLeft (
  Nat.add 0x2f019c80f677f5bb6c3967fb0cd6aa4f906203e0e999a253409206b9ca6fba268d34f05d (Nat.shiftLeft
  0x80444b5e7abd60441caa3f6e8 288)) 576)))), (198, (mkQ true (Nat.add (Nat.add
  0x2479bf36baf7c9227e10897220907d774802a6a0fc78c6e7219124ec7347e64a0f86a8cf (Nat.shiftLeft
  0xf045e2bbe150dbe68de110ad2b0a10ddf19314da845c4bc09ade72d8a644fbe71daf33b4 288)) (Nat.shiftLeft (
  Nat.add 0x9d13f2ac55176382ec89830a1d78839bb25237e3c08c09524b1927b8ad737b40bbe1d362 (Nat.shiftLeft
  0x2d26e2762aef58b8406f0d72bf88 288)) 576)) (Nat.add (Nat.add
  0xa19ace3fc49c886daf72b3fe7a79fba3b45b346743650b21a4cf5493ab7303ea42000000 (Nat.shiftLeft
  0xe3453817f4208966bf7b5a1293be3b359b78177a55d262c42d9837b35e3b06f21a6403a9 288)) (Nat.shiftLeft (
  Nat.add 0x2f019c80f677f5bb6c3967fb0cd6aa4f906203e0e999a253409206b9ca6fba268d34f05d (Nat.shiftLeft
  0x80444b5e7abd60441caa3f6e8 288)) 576)))), (234, (mkQ true (Nat.add (Nat.add
  0x2dd2fcbaad994c0bf65a83b6b1a496d97cf4482abdcc0cf806ff160b212acdcde0317a29 (Nat.shiftLeft
  0xffa19af5b3836b1394bb53009b3377044d7b2e4488216ab7d950ce0268a3e3caf4b84f1 288)) (Nat.shiftLeft (
  Nat.add 0x2bd1d52175366225ffa1746654c3dbb365ec76f7fd9b3ada2a2d936cbb6955f301e59ae0 (Nat.shiftLeft
  0x8db11f740f5516282a7c4edbfb3 288)) 576)) (Nat.add (Nat.add
  0xa19ace3fc49c886daf72b3fe7a79fba3b45b346743650b21a4cf5493ab7303ea42000000 (Nat.shiftLeft
  0xe3453817f4208966bf7b5a1293be3b359b78177a55d262c42d9837b35e3b06f21a6403a9 288)) (Nat.shiftLeft (
  Nat.add 0x2f019c80f677f5bb6c3967fb0cd6aa4f906203e0e999a253409206b9ca6fba268d34f05d (Nat.shiftLeft
  0x80444b5e7abd60441caa3f6e8 288)) 576)))), (270, (mkQ false (Nat.add (Nat.add
  0x315fae57816f48dac18fbd07f2bc46ab795c46874a2f26fd217b96f06416686d2df9c857 (Nat.shiftLeft
  0x5326c8114630e5d38a64ce7f0250b39b6a721b00559705154675b128bbfb2c4e32b5f49d 288)) (Nat.shiftLeft (
  Nat.add 0xc1c09bf82fd87b0f7ffa1b9d14cd57bce06b958a3ec29832ad9d62dd5525f54cd15e3a40 (Nat.shiftLeft
  0x10bdb7de89b36fd5113da76e9e5 288)) 576)) (Nat.add (Nat.add
  0x43359c7f893910db5ee567fcf4f3f74768b668ce86ca1643499ea92756e607d484000000 (Nat.shiftLeft
  0xc68a702fe84112cd7ef6b425277c766b36f02ef4aba4c5885b306f66bc760de434c80753 288)) (Nat.shiftLeft (
  Nat.add 0x5e033901ecefeb76d872cff619ad549f20c407c1d33344a681240d7394df744d1a69e0bb (Nat.shiftLeft
  0x1008896bcf57ac08839547edd0 288)) 576))))])]

def sjsuTsp_330 : List ((Nat × Nat × Nat) × List (Nat × Rat)) := [((5, 5, 2), [(88, (mkQ false (
  Nat.add (Nat.add 0xfec16112fe9db5c270d58ea5e4ecd6dc6b143c9ba5d59f569239d9fc96cfe13059b7e9df (
  Nat.shiftLeft 0xc022c48d57043be79b5d153fff766d606ce95f593e826b106ac81832248812767890136d 288)) (
  Nat.shiftLeft (Nat.add 0x1b71923175ceaf03ec4e773bc455815a5ca009c98e515669b4b37bad81a16d899f796f85
  (Nat.shiftLeft 0xa3562e41e938ec0e35c1aa96437fec464f3d1d25514d2322d1c8d0d11b8cb2b64c470 288)) 576))
  (Nat.add (Nat.add 0x36f1481ee4d016243ee562bdd72e35c7a6a8d0ff319b35f7d83756716753bc348000000 (
  Nat.shiftLeft 0x9c9733caf2935ac5e0880547e2fbb14d585190ee4b8d027bb566145b9ecab9a5b6480c4e 288)) (
  Nat.shiftLeft (Nat.add 0x85cdcbb0b6f8145605ec07ec03086816e69fd946599d55b1c1926cc77b59065a1c221d56
  (Nat.shiftLeft 0x22485e6fa47bf93e7f9411af0f1e2757d2d4b2084ee2bec93a627714451bd9a27347 288)) 576)))
  ), (90, (mkQ true (Nat.add (Nat.add
  0x64f5494994df93f57469a1197dd3efc4d12c66e560fb47bfff160ebf3aac1b58c775922b (Nat.shiftLeft
  0x52665265c050b1e99c1f218296b05e83cb903ea1f9f4406cb5532a5259b11e958cbbbf5c 288)) (Nat.shiftLeft (
  Nat.add 0x977aaab3e82a7acfcfb4991d4db9ae3f5367a3f305fa95c24bf7400162d32b19bd5d21d8 (Nat.shiftLeft
  0xad22e1b2d309ba7eac6a8d6779aee8edfe22a150f4df457af612294cd9c6bf701a29 288)) 576)) (Nat.add (
  Nat.add 0x80dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d2000000 (Nat.shiftLeft
  0xa725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d920313 288)) (Nat.shiftLeft (
  Nat.add 0xe17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded6419687088755 (Nat.shiftLeft
  0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd1 288)) 576)))), (124, (mkQ
  false (Nat.add (Nat.add 0xbb76de119ffb294250998c7d7a5f458af1fdd692a13b4307aacadab02906f6936e521297
  (Nat.shiftLeft 0xce13dc954cc5f7f78ac549a23d019d0df19bc0223e2707aa42541fdf4436dbc4da3977ff 288)) (
  Nat.shiftLeft (Nat.add 0x17a1254148652935b85f57b1a36d38faa352b178d244b6be961235cab4da678a38de93b7
  (Nat.shiftLeft 0x1b0f85ac6aa76599b6e8c02a1d6b6307cb2c39ba05f4bb9b5bcfb8e361eb655f910b2 288)) 576))
  (Nat.add (Nat.add 0xf9a496a8062dc337a0d96113bf916fa45b2154f69970523dfe5e7177b047dd8c0a800000 (
  Nat.shiftLeft 0xe1f5170c23083def4601b344193cbf042ab438362dbe9007f24479dabec8ef1edf1419c0 288)) (
  Nat.shiftLeft (Nat.add 0xe4df5f589be319daacdfc01959a34e19e2e1ff841451f7789f383af5b18ab67ab9f3a05d
  (Nat.shiftLeft 0x6db46165418cb72e650d05636393b119090f0680fc6f2f50bad4b040dd25eba170 288)) 576)))),
  (126, (mkQ false (Nat.add (Nat.add
  0xeb0ee7bbb54f6bb37d6a05806f07ccad14b17a45d58ea3627fc175369493ae1d69dcaf47 (Nat.shiftLeft
  0xf2bb46821cd7c72809cb665bc23018f0290c66c70255cd01f15aee8512a75dd27789e53e 288)) (Nat.shiftLeft (
  Nat.add 0x9ac81dcfacfec20d706bb7dd4f1186a3fabcd51b8f37018b64ce23abafb1bffc2b6584ac (Nat.shiftLeft
  0xd044361fcaa56b9acb21affd3af91025bd402ce89e616187b03e736a7358c49da53a4 288)) 576)) (Nat.add (
  Nat.add 0xcd24b540316e19bd06cb089dfc8b7d22d90aa7b4cb8291eff2f38bbd823eec6054000000 (Nat.shiftLeft
  0xfa8b8611841ef7a300d9a20c9e5f82155a1c1b16df4803f9223ced5f64778f6f8a0ce07 288)) (Nat.shiftLeft (
  Nat.add 0x26fafac4df18ced566fe00cacd1a70cf170ffc20a28fbbc4f9c1d7ad8c55b3d5cf9d02ef (Nat.shiftLeft
  0x36da30b2a0c65b97328682b1b1c9d88c848783407e3797a85d6a58206e92f5d0b87 288)) 576)))), (128, (mkQ
  true (Nat.add (Nat.add 0x137bfeeb2636374ab7824235cb68216e8cc957fe011ef1adae141da403d772befb66ccf3
  (Nat.shiftLeft 0x272469d06e71ba6d9b8cbc927cd8ddfc6f4500d7406d2a943df303805997ec67f6850b89 288)) (
  Nat.shiftLeft (Nat.add 0x197dc477423a043629f89b5fab6745c0b42715141e4746443c61394a97711061f57b92a5
  (Nat.shiftLeft 0x2801d637170caa00d79c49cfcf1b4dcf4bc63ddff649b43886e440b930f51949804b 288)) 576))
  (Nat.add (Nat.add 0x80dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d2000000 (
  Nat.shiftLeft 0xa725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d920313 288)) (
  Nat.shiftLeft (Nat.add 0xe17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded6419687088755
  (Nat.shiftLeft 0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd1 288)) 576))))
  , (160, (mkQ false (Nat.add (Nat.add
  0x2ea810704c5a5e4788ba99f635939ed54c86967c5f41b6eec437be15b73023a91f701b17 (Nat.shiftLeft
  0x591ee5e91025f97e647d58bf28b0850c1de3e61b1ef1be0488dc5ffb22fafb4e36212cb2 288)) (Nat.shiftLeft (
  Nat.add 0xdc990bb3a26e903f2f9f46bac26ba7df4b426e8ef09e33bbddf0be6277040c1932b3732f (Nat.shiftLeft
  0xd8dc7ecd6998707abf1f2831f7df8607b4f96f93dcabe5d0eee150901a5377e3cfded 288)) 576)) (Nat.add (
  Nat.add 0xe6925aa018b70cde8365844efe45be916c8553da65c148f7f979c5dec11f76302a000000 (Nat.shiftLeft
  0x87d45c308c20f7bd1806cd1064f2fc10aad0e0d8b6fa401fc911e76afb23bc7b7c506703 288)) (Nat.shiftLeft (
  Nat.add 0x937d7d626f8c676ab37f0065668d38678b87fe105147dde27ce0ebd6c62ad9eae7ce8177 (Nat.shiftLeft
  0x1b6d185950632dcb99434158d8e4ec464243c1a03f1bcbd42eb52c1037497ae85c3 288)) 576)))), (162, (mkQ
  false (Nat.add (Nat.add 0x3660fa611c8338dd34755a14bd33606d1a9c083c60303b41c2df42b13f21a6da191de697
  (Nat.shiftLeft 0x63dbeea0efb128274a0dec02adbc248747de4e69fcea456405b8dc603f935a7f567076e6 288)) (
  Nat.shiftLeft (Nat.add 0xd78a6b4b816caa6eefe684d9018a4dccabf97bae1c67aae89bb39a726f034f7b791f8b37
  (Nat.shiftLeft 0x2bb88eab04fe7dc1a5cc0e640892b2b3878acfe2cb09832403ebb656434260b2ef989 288)) 576))
  (Nat.add (Nat.add 0xca41d5dccf458149738a26d4b306f974f1408862a3c6874bff58fa2fe01cbf04d1000000 (
  Nat.shiftLeft 0xf3fba2d1a79ce592e8cd7ae80a184c681114e348df190669941b63f1191d2c72bfa1a3e6 288)) (
  Nat.shiftLeft (Nat.add 0xf5262623718e0a577859800a23daec0a5ac0cc9b3b53fc96a6167dfbe09de2977d94a68b
  (Nat.shiftLeft 0x2be1c08ee70516128ed20227c16e46d6d06c690064f946204abb79b38ba8c4a6f9 288)) 576)))),
  (164, (mkQ false (Nat.add (Nat.add
  0xf003d3d62ad67fb655f25bb9388df9c1ef89046fcf6a0e55f944046d2af6ce704c8dc705 (Nat.shiftLeft
  0x83605da4a6f1cff8d9ba4021986e05d2b9c9b9a15e05b5295c5f7e8f4a66a25534b0f5c2 288)) (Nat.shiftLeft (
  Nat.add 0xde78b7e361fa08f5f071cd6710e3b679fb081b4b78c8f54cc48fe5a181bbebdf51558a9f (Nat.shiftLeft
  0xf0c72a9062a447ad81acb44cfdccafc7dc8d8270c1790ba7769c827b7b2feb822a6f9 288)) 576)) (Nat.add (
  Nat.add 0xcd24b540316e19bd06cb089dfc8b7d22d90aa7b4cb8291eff2f38bbd823eec6054000000 (Nat.shiftLeft
  0xfa8b8611841ef7a300d9a20c9e5f82155a1c1b16df4803f9223ced5f64778f6f8a0ce07 288)) (Nat.shiftLeft (
  Nat.add 0x26fafac4df18ced566fe00cacd1a70cf170ffc20a28fbbc4f9c1d7ad8c55b3d5cf9d02ef (Nat.shiftLeft
  0x36da30b2a0c65b97328682b1b1c9d88c848783407e3797a85d6a58206e92f5d0b87 288)) 576)))), (196, (mkQ
  false (Nat.add (Nat.add 0xf003d3d62ad67fb655f25bb9388df9c1ef89046fcf6a0e55f944046d2af6ce704c8dc705
  (Nat.shiftLeft 0x83605da4a6f1cff8d9ba4021986e05d2b9c9b9a15e05b5295c5f7e8f4a66a25534b0f5c2 288)) (
  Nat.shiftLeft (Nat.add 0xde78b7e361fa08f5f071cd6710e3b679fb081b4b78c8f54cc48fe5a181bbebdf51558a9f
  (Nat.shiftLeft 0xf0c72a9062a447ad81acb44cfdccafc7dc8d8270c1790ba7769c827b7b2feb822a6f9 288)) 576))
  (Nat.add (Nat.add 0xcd24b540316e19bd06cb089dfc8b7d22d90aa7b4cb8291eff2f38bbd823eec6054000000 (
  Nat.shiftLeft 0xfa8b8611841ef7a300d9a20c9e5f82155a1c1b16df4803f9223ced5f64778f6f8a0ce07 288)) (
  Nat.shiftLeft (Nat.add 0x26fafac4df18ced566fe00cacd1a70cf170ffc20a28fbbc4f9c1d7ad8c55b3d5cf9d02ef
  (Nat.shiftLeft 0x36da30b2a0c65b97328682b1b1c9d88c848783407e3797a85d6a58206e92f5d0b87 288)) 576))))
  , (198, (mkQ false (Nat.add (Nat.add
  0x3660fa611c8338dd34755a14bd33606d1a9c083c60303b41c2df42b13f21a6da191de697 (Nat.shiftLeft
  0x63dbeea0efb128274a0dec02adbc248747de4e69fcea456405b8dc603f935a7f567076e6 288)) (Nat.shiftLeft (
  Nat.add 0xd78a6b4b816caa6eefe684d9018a4dccabf97bae1c67aae89bb39a726f034f7b791f8b37 (Nat.shiftLeft
  0x2bb88eab04fe7dc1a5cc0e640892b2b3878acfe2cb09832403ebb656434260b2ef989 288)) 576)) (Nat.add (
  Nat.add 0xca41d5dccf458149738a26d4b306f974f1408862a3c6874bff58fa2fe01cbf04d1000000 (Nat.shiftLeft
  0xf3fba2d1a79ce592e8cd7ae80a184c681114e348df190669941b63f1191d2c72bfa1a3e6 288)) (Nat.shiftLeft (
  Nat.add 0xf5262623718e0a577859800a23daec0a5ac0cc9b3b53fc96a6167dfbe09de2977d94a68b (Nat.shiftLeft
  0x2be1c08ee70516128ed20227c16e46d6d06c690064f946204abb79b38ba8c4a6f9 288)) 576)))), (200, (mkQ
  false (Nat.add (Nat.add 0x2ea810704c5a5e4788ba99f635939ed54c86967c5f41b6eec437be15b73023a91f701b17
  (Nat.shiftLeft 0x591ee5e91025f97e647d58bf28b0850c1de3e61b1ef1be0488dc5ffb22fafb4e36212cb2 288)) (
  Nat.shiftLeft (Nat.add 0xdc990bb3a26e903f2f9f46bac26ba7df4b426e8ef09e33bbddf0be6277040c1932b3732f
  (Nat.shiftLeft 0xd8dc7ecd6998707abf1f2831f7df8607b4f96f93dcabe5d0eee150901a5377e3cfded 288)) 576))
  (Nat.add (Nat.add 0xe6925aa018b70cde8365844efe45be916c8553da65c148f7f979c5dec11f76302a000000 (
  Nat.shiftLeft 0x87d45c308c20f7bd1806cd1064f2fc10aad0e0d8b6fa401fc911e76afb23bc7b7c506703 288)) (
  Nat.shiftLeft (Nat.add 0x937d7d626f8c676ab37f0065668d38678b87fe105147dde27ce0ebd6c62ad9eae7ce8177
  (Nat.shiftLeft 0x1b6d185950632dcb99434158d8e4ec464243c1a03f1bcbd42eb52c1037497ae85c3 288)) 576))))
  , (232, (mkQ true (Nat.add (Nat.add
  0x137bfeeb2636374ab7824235cb68216e8cc957fe011ef1adae141da403d772befb66ccf3 (Nat.shiftLeft
  0x272469d06e71ba6d9b8cbc927cd8ddfc6f4500d7406d2a943df303805997ec67f6850b89 288)) (Nat.shiftLeft (
  Nat.add 0x197dc477423a043629f89b5fab6745c0b42715141e4746443c61394a97711061f57b92a5 (Nat.shiftLeft
  0x2801d637170caa00d79c49cfcf1b4dcf4bc63ddff649b43886e440b930f51949804b 288)) 576)) (Nat.add (
  Nat.add 0x80dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d2000000 (Nat.shiftLeft
  0xa725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d920313 288)) (Nat.shiftLeft (
  Nat.add 0xe17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded6419687088755 (Nat.shiftLeft
  0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd1 288)) 576)))), (234, (mkQ
  false (Nat.add (Nat.add 0xeb0ee7bbb54f6bb37d6a05806f07ccad14b17a45d58ea3627fc175369493ae1d69dcaf47
  (Nat.shiftLeft 0xf2bb46821cd7c72809cb665bc23018f0290c66c70255cd01f15aee8512a75dd27789e53e 288)) (
  Nat.shiftLeft (Nat.add 0x9ac81dcfacfec20d706bb7dd4f1186a3fabcd51b8f37018b64ce23abafb1bffc2b6584ac
  (Nat.shiftLeft 0xd044361fcaa56b9acb21affd3af91025bd402ce89e616187b03e736a7358c49da53a4 288)) 576))
  (Nat.add (Nat.add 0xcd24b540316e19bd06cb089dfc8b7d22d90aa7b4cb8291eff2f38bbd823eec6054000000 (
  Nat.shiftLeft 0xfa8b8611841ef7a300d9a20c9e5f82155a1c1b16df4803f9223ced5f64778f6f8a0ce07 288)) (
  Nat.shiftLeft (Nat.add 0x26fafac4df18ced566fe00cacd1a70cf170ffc20a28fbbc4f9c1d7ad8c55b3d5cf9d02ef
  (Nat.shiftLeft 0x36da30b2a0c65b97328682b1b1c9d88c848783407e3797a85d6a58206e92f5d0b87 288)) 576))))
  , (236, (mkQ false (Nat.add (Nat.add
  0xbb76de119ffb294250998c7d7a5f458af1fdd692a13b4307aacadab02906f6936e521297 (Nat.shiftLeft
  0xce13dc954cc5f7f78ac549a23d019d0df19bc0223e2707aa42541fdf4436dbc4da3977ff 288)) (Nat.shiftLeft (
  Nat.add 0x17a1254148652935b85f57b1a36d38faa352b178d244b6be961235cab4da678a38de93b7 (Nat.shiftLeft
  0x1b0f85ac6aa76599b6e8c02a1d6b6307cb2c39ba05f4bb9b5bcfb8e361eb655f910b2 288)) 576)) (Nat.add (
  Nat.add 0xf9a496a8062dc337a0d96113bf916fa45b2154f69970523dfe5e7177b047dd8c0a800000 (Nat.shiftLeft
  0xe1f5170c23083def4601b344193cbf042ab438362dbe9007f24479dabec8ef1edf1419c0 288)) (Nat.shiftLeft (
  Nat.add 0xe4df5f589be319daacdfc01959a34e19e2e1ff841451f7789f383af5b18ab67ab9f3a05d (Nat.shiftLeft
  0x6db46165418cb72e650d05636393b119090f0680fc6f2f50bad4b040dd25eba170 288)) 576)))), (270, (mkQ
  true (Nat.add (Nat.add 0x64f5494994df93f57469a1197dd3efc4d12c66e560fb47bfff160ebf3aac1b58c775922b
  (Nat.shiftLeft 0x52665265c050b1e99c1f218296b05e83cb903ea1f9f4406cb5532a5259b11e958cbbbf5c 288)) (
  Nat.shiftLeft (Nat.add 0x977aaab3e82a7acfcfb4991d4db9ae3f5367a3f305fa95c24bf7400162d32b19bd5d21d8
  (Nat.shiftLeft 0xad22e1b2d309ba7eac6a8d6779aee8edfe22a150f4df457af612294cd9c6bf701a29 288)) 576))
  (Nat.add (Nat.add 0x80dbc5207b93405890fb958af75cb8d71e9aa343fcc66cd7df60dd59c59d4ef0d2000000 (
  Nat.shiftLeft 0xa725ccf2bca4d6b178220151f8beec535614643b92e3409eed598516e7b2ae696d920313 288)) (
  Nat.shiftLeft (Nat.add 0xe17372ec2dbe0515817b01fb00c21a05b9a7f6519667556c70649b31ded6419687088755
  (Nat.shiftLeft 0x892179be91efe4f9fe5046bc3c789d5f4b52c8213b8afb24e989dc51146f6689cd1 288)) 576))))
  , (272, (mkQ false (Nat.add (Nat.add
  0xfec16112fe9db5c270d58ea5e4ecd6dc6b143c9ba5d59f569239d9fc96cfe13059b7e9df (Nat.shiftLeft
  0xc022c48d57043be79b5d153fff766d606ce95f593e826b106ac81832248812767890136d 288)) (Nat.shiftLeft (
  Nat.add 0x1b71923175ceaf03ec4e773bc455815a5ca009c98e515669b4b37bad81a16d899f796f85 (Nat.shiftLeft
  0xa3562e41e938ec0e35c1aa96437fec464f3d1d25514d2322d1c8d0d11b8cb2b64c470 288)) 576)) (Nat.add (
  Nat.add 0x36f1481ee4d016243ee562bdd72e35c7a6a8d0ff319b35f7d83756716753bc348000000 (Nat.shiftLeft
  0x9c9733caf2935ac5e0880547e2fbb14d585190ee4b8d027bb566145b9ecab9a5b6480c4e 288)) (Nat.shiftLeft (
  Nat.add 0x85cdcbb0b6f8145605ec07ec03086816e69fd946599d55b1c1926cc77b59065a1c221d56 (Nat.shiftLeft
  0x22485e6fa47bf93e7f9411af0f1e2757d2d4b2084ee2bec93a627714451bd9a27347 288)) 576))))])]


end KAM.EffectiveStability.SJSU

end
