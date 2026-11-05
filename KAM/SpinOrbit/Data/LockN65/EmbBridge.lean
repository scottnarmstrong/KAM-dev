/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# The embedding check from its pieces

`checkEmbedding` from its three families of conditions (the angle rows, the action rows, the `DK`
row sums), each given index by index. Stated over an abstract certificate, so instantiating it
evaluates nothing.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `checkEmbedding` from its conditions, index by index. -/
theorem checkEmbedding_of_parts (c : TorusCertificate n α)
    (ha : ∀ i, i < n →
      angleImOk n c.emb c.weight c.piEnc c.params.rho
        (c.weightH.rho - c.params.rho - c.params.μ) i = true)
    (hb : ∀ i, i < n →
      ble ((actionShiftModel n c.emb c.weight c.piEnc (c.centre.getD i 0) i).supBound c.weight)
        (ofRatDown (c.radius.getD i 0 - c.params.μ)) = true)
    (hc : ∀ r, r < n + n →
      ble (dkRowUp n c.emb c.weight c.piEnc r) (ofRatDown (c.params.σK - c.params.μ)) = true) :
    checkEmbedding c = true := by
  unfold checkEmbedding
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨⟨ha, hb⟩, hc⟩

end KAM.SpinOrbit.Data.LockN65
