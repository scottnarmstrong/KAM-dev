/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# Landed checks from their conjuncts

`checkEmbedding_of`: the landed embedding check from its conjuncts (the angle's imaginary parts, the
action shifts, the rows of `DK`), each of which can be established in its own declaration. A
certificate with a large embedding (MAG: 2,407 keys) does not decide the whole check in one kernel
process under 4 GB.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- **The embedding check from its conjuncts.** -/
theorem checkEmbedding_of {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    (hA : ∀ i < n, angleImOk n c.emb c.weight c.piEnc c.params.rho
      (c.weightH.rho - c.params.rho - c.params.μ) i = true)
    (hS : ∀ i < n, ble ((actionShiftModel n c.emb c.weight c.piEnc (c.centre.getD i 0) i).supBound
      c.weight) (ofRatDown (c.radius.getD i 0 - c.params.μ)) = true)
    (hD : ∀ r < n + n,
      ble (dkRowUp n c.emb c.weight c.piEnc r) (ofRatDown (c.params.σK - c.params.μ)) = true) :
    checkEmbedding c = true := by
  simp only [checkEmbedding, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨⟨hA, hS⟩, hD⟩

end KAM.Certificate
