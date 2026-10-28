/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Canonical.Flow

/-!
# The extended flow `extFlow` (Part 11)

The signed definition `KAM.Nekhoroshev.extFlow`: the generic Part 5 canonical flow of the weighted
field `wfield b.c φ` on the domain `𝒟_{R-ρ,s-σ}`. It is shared by packages N11-F1 (composition,
transform) and N11-F2 (canonical map); it lives in its own small module so both import one copy.
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

def extFlow (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ) (t : ℝ) : EC n k → EC n k :=
  KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R-ρ) (s-σ)) t

end KAM.Nekhoroshev

end
