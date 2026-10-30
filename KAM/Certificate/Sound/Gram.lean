/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Static

/-!
# Soundness of the Gram sub-check

`checkGram_sound`: `gramCheck_sound` at the certificate's data, with `1 ≤ n` from
`StaticFacts.hn` and the strip width `weight.rho = rho` from `StaticFacts.hrho`.
-/

public section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

theorem checkGram_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkGram c = true) : ∀ θ ∈ complexStrip n c.params.rho,
      IsUnit (gramMatrix c.K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ := by
  have hS := checkStatic_sound hs
  intro θ hθ
  unfold checkGram at h
  obtain ⟨δβ, hδβ⟩ := Option.isSome_iff_exists.mp h
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [hS.hrho]; exact hθ
  obtain ⟨hu, hb, -⟩ :=
    (gramCheck_sound (by have := hS.hn; omega) c.emb c.gramInv hS.hW c.cfgLow hS.hpe _ hδβ).2
      θ hθ'
  exact ⟨hu, fun i => by have := hb i; push_cast at this; exact this⟩

end KAM.Certificate
