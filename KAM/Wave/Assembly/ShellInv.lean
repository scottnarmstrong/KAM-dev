/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.PatchInst

/-!
# W8: invariance and continuity of a shell torus, W8-side reduction
(blueprint `bpW:w8:shell-inv`)

Blueprint label `bpW:w8:shell-inv` (milestone W8).

Lemma `bpW:w8:shell-inv` is about `K^{(n)}_ξ = w8KOfBirk m hm Ψ̃^{(n)}_ξ` with
`Ψ̃^{(n)}_ξ = 𝒜_ξ ∘ Φ^{(n)}_P ∘ Φ^{(n)}_*`, i.e. it needs W5's `bpW:w5:action-angle` (not in this
base). This module reduces it to properties of an arbitrary torus `Ψ` in Birkhoff coordinates:
* `w8KOfBirk_eq_gamma`: at real points with `𝒵⁻¹Ψ(θ) ∈ B^E_{r₁}`,
  `K(θ) = Γ^ℝ(𝒵⁻¹Ψ(θ)) = Π Γ(Ψ(θ))` (the second expression of Definition `bpW:w8:Kshell`);
* `w8_shellInv_of_birk` (`bpW:w8:shell-inv` (i), Steps `stepW:w8:si-tr`, `stepW:w8:si-frozen`;
  hypothesis-taking variant): if `Ψ` is real, maps into `B_{ρ₁}` with `𝒵⁻¹Ψ ∈ B^E_{r₁}`, is
  differentiable along `ν` with derivative `D`, and `D = X_{H'}(Ψ)` in `𝔚_{a,p-1}` (Theorem
  `bpW:w6:tori` (i), (iii) and Lemma `bpW:w8:torus-shape` (v)),
  then `K = w8KOfBirk m hm Ψ` satisfies
  the two `HasDerivAt` statements of clause (4) of `nlw2` (W3 Corollary
  `bpW:w3:transport-tori-weak`, frozen form);
* `w8_shellInvCont_of_birk` (`bpW:w8:shell-inv` (ii), Step `stepW:w8:si-cont`; hypothesis-taking
  variant): joint continuity of `(ξ, θ) ↦ K_ξ(θ)` from that of `(ξ, θ) ↦ Ψ_ξ(θ)`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

/-- `Γ = Γ_1` of W3 at `a = p = 1`. -/
abbrev w8Gam1 (m : ℝ) (hm : 0 < m) : BirkSpace → BirkSpace :=
  birkGamma m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) 1

variable {m : ℝ} {hm : 0 < m}

/-- At a real point `Ψ(θ)` with `𝒵⁻¹Ψ(θ) ∈ B^E_{r₁}`: `w8KOfBirk m hm Ψ θ = Π Γ(Ψ(θ))`
(Definition `bpW:w8:Kshell`, second expression `τ_E 𝒵⁻¹ Γ(Ψ̃(θ))`). -/
theorem w8KOfBirk_eq_gamma {Ψ : (Fin 2 → ℝ) → BirkSpace} {θ : Fin 2 → ℝ}
    (hρ : birkRho (Ψ θ) = Ψ θ) (hb : birkPi (Ψ θ) ∈ birkRealBall1 m 1) :
    w8KOfBirk m hm Ψ θ = birkPi (w8Gam1 m hm (Ψ θ)) := by
  rw [w8KOfBirk_of_mem hb]
  show birkPi (birkGamma m hm zero_le_one _ 1 (birkZR (birkPi (Ψ θ)))) = _
  rw [birkZR_birkPi _ hρ]

/-- **Invariance of a shell torus, W8-side reduction** (blueprint `bpW:w8:shell-inv` (i);
hypothesis-taking variant): for a real torus `Ψ` in `B_{ρ₁}` with `𝒵⁻¹Ψ ∈ B^E_{r₁}`, derivative `D`
along `ν`, and the weak invariance `D = X_Λ(Ψ) + X_Ḡ(Ψ) + X_{G^{nor}}(Ψ) + X_K(Ψ)` in `𝔚_{a,p-1}`,
`K = w8KOfBirk m hm Ψ` satisfies clause (4) of `nlw2` with frequency `ν`. -/
theorem w8_shellInv_of_birk (ν : Fin 2 → ℝ) (Ψ D : (Fin 2 → ℝ) → BirkSpace)
    (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ) (hΨ : ∀ θ, Ψ θ ∈ birkBall1 m 1)
    (hb : ∀ θ, birkPi (Ψ θ) ∈ birkRealBall1 m 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed 1 1 (1 - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestField m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) ⟨Ψ θ, hΨ θ⟩))
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff (w8KOfBirk m hm Ψ (θ + t • ν)).1 j)
        (lam m hm j * coeff (w8KOfBirk m hm Ψ θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (w8KOfBirk m hm Ψ (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (w8KOfBirk m hm Ψ θ).1 j) -
          cubicGrad m hm (w8KOfBirk m hm Ψ θ).1 j) 0 := by
  have hK : w8KOfBirk m hm Ψ = fun θ => birkPi (w8Gam1 m hm (Ψ θ)) :=
    funext fun θ => w8KOfBirk_eq_gamma (hρ θ) (hb θ)
  rw [hK]
  exact birk_transport_tori_weak_frozen_coord (by norm_num) ν Ψ D hρ hΨ hder heq θ j

/-- **Continuity of a shell torus in `(ξ, θ)`, W8-side reduction** (blueprint `bpW:w8:shell-inv`
(ii); hypothesis-taking variant): if `(ξ, θ) ↦ Ψ_ξ(θ)` is continuous on `S × ℝ²` with real values in
`B_{ρ₁}` and `𝒵⁻¹Ψ_ξ(θ) ∈ B^E_{r₁}`, then `(ξ, θ) ↦ K_ξ(θ) = w8KOfBirk m hm Ψ_ξ θ` is continuous on
`S × ℝ²`. -/
theorem w8_shellInvCont_of_birk {S : Set (Fin 2 → ℝ)}
    {Ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → BirkSpace}
    (hc : ContinuousOn (Function.uncurry Ψ) (S ×ˢ univ))
    (hρ : ∀ ξ ∈ S, ∀ θ, birkRho (Ψ ξ θ) = Ψ ξ θ) (hΨ : ∀ ξ ∈ S, ∀ θ, Ψ ξ θ ∈ birkBall1 m 1)
    (hb : ∀ ξ ∈ S, ∀ θ, birkPi (Ψ ξ θ) ∈ birkRealBall1 m 1) :
    ContinuousOn (Function.uncurry fun ξ => w8KOfBirk m hm (Ψ ξ)) (S ×ˢ univ) := by
  have hg : ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      birkPi (w8Gam1 m hm (Function.uncurry Ψ q))) (S ×ˢ univ) := by
    intro q hq
    have hG : ContinuousAt (fun w => birkGamma m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1)
        1 w) (Function.uncurry Ψ q) :=
      (birkGamma_differentiableAt_one (hm := hm) _ (hΨ q.1 hq.1 q.2)).continuousAt
    exact (birkPi.continuous.continuousAt.comp hG).comp_continuousWithinAt (hc q hq)
  refine hg.congr fun q hq => ?_
  exact w8KOfBirk_eq_gamma (hρ q.1 hq.1 q.2) (hb q.1 hq.1 q.2)

end KAM.Wave

end
