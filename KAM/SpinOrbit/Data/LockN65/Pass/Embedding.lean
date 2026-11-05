/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.Data.LockN65.EmbBridge
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingA0
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingA1
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingB0
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingB1
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingR0
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingR1
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingR2
public import KAM.SpinOrbit.Data.LockN65.Pass.EmbeddingR3

/-!
# The N = 65 lock: embedding check

`checkEmbedding` from its eight pieces (`Pass/EmbeddingA0`–`A1` angle rows, `B0`–`B1` action rows,
`R0`–`R3` `DK` row sums; one kernel run each) through `checkEmbedding_of_parts`.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_embedding :
    checkEmbedding base = true := by
  refine checkEmbedding_of_parts base ?_ ?_ ?_
  · intro i hi
    interval_cases i
    · exact lock_embeddingA0
    · exact lock_embeddingA1
  · intro i hi
    interval_cases i
    · exact lock_embeddingB0
    · exact lock_embeddingB1
  · intro r hr
    interval_cases r
    · exact lock_embeddingR0
    · exact lock_embeddingR1
    · exact lock_embeddingR2
    · exact lock_embeddingR3

end KAM.SpinOrbit.Data.LockN65
