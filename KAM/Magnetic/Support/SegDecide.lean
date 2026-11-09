/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Slp

/-!
# Decidable equality of straight-line operations (MAG-SEAL; copy of the lock's `SegDecide`)

The generated segment proofs check `s.ops ops = [op]` by kernel evaluation (`decide`), instead of
an elaborator `rfl` whose list unfolding recurses once per cell (it exceeds the default recursion
depth for segments past index ~80 of the chunked plan lists). This needs `DecidableEq SlpOp`.
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM.Certificate

deriving instance DecidableEq for SlpOp

example : ([SlpOp.exp 870] : List SlpOp) = [SlpOp.exp 870] := by decide +kernel

end KAM.Magnetic.Data
