/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainGammaSympl

/-!
# Invariant tori are transported (blueprint-W `bpW:w3:transport-tori`)

Package W3-MAIN, blueprint label `bpW:w3:transport-tori`.

`birk_transport_tori`: let `Ψ` take values in `B_{ρ₁} ∩ 𝔚⁺` (`Ψ θ` read at weight `p+1`) with
`∂_t ι Ψ(θ + tν)|_{t=0} = X_Λ(Ψθ) + X_Ḡ + X_{G^{nor}} + X_K` (all in `𝔚`). Then `Γ(ι Ψ θ) = ι z`
with `z ∈ 𝔚⁺` and `∂_t Γ(ι Ψ(θ + tν))|_{t=0} = X_Λ(z) + X_G(Γ(ι Ψ θ)) = X_H(Γ ∘ Ψ(θ))`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem birk_transport_tori (ν : Fin 2 → ℝ) (Ψ : (Fin 2 → ℝ) → BirkSpace)
    (hΨ : ∀ θ, 160 * birkCF m p * ‖birkEmbed a (p + 1) p (by linarith) (Ψ θ)‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamBarX m hm ha hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamNorX m hm ha hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkXK m hm ha hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ)))) 0)
    (θ : Fin 2 → ℝ) :
    ∃ z : BirkSpace, birkEmbed a (p + 1) p (by linarith) z =
        birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)) ∧
      HasDerivAt (fun t : ℝ => birkGamma m hm ha hp 1
          (birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν))))
        (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp
            (birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ))))) 0 := by
  obtain ⟨z, hz, hconj⟩ := birk_conjugacy (ha := ha) (hm := hm) (hp := hp) (Ψ θ) (hΨ θ)
  refine ⟨z, hz, ?_⟩
  set w := birkEmbed a (p + 1) p (by linarith) (Ψ θ) with hw
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    have := hΨ θ
    nlinarith
  have hΓ := birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num) hw40
  have hΓ' : HasFDerivAt (fun w' => birkGamma m hm ha hp 1 w')
      ((birkGammaD m hm ha hp 1 w).restrictScalars ℝ)
      (birkEmbed a (p + 1) p (by linarith) (Ψ (θ + (0 : ℝ) • ν))) := by
    simpa only [zero_smul, add_zero] using hΓ
  have hc := hΓ'.comp_hasDerivAt (0 : ℝ) (hder θ)
  refine hc.congr_deriv ?_
  exact hconj

end KAM.Wave

end
