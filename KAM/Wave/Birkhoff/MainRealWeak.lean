/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainRealTori

/-!
# Weak invariance, real form (blueprint-W `bpW:w3:transport-tori-weak`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-MAIN, blueprint label `bpW:w3:transport-tori-weak`.

`birk_transport_tori_weak_real`: for real `Ψ` (`ϱ Ψ = Ψ`) satisfying the weak equation in
`𝔚_{a,p-1}`, `Ψ(θ) ∈ 𝔚⁺` (with the bound), and `(Q,P) = Π Γ Ψ` satisfies the coefficient
system `D_ν Q_j = λ_j P_j`, `D_ν P_j = -λ_j Q_j - 𝒢(Q)_j` (for `a > 0`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {hp : 1 / 2 ≤ p}

include hm hp in
/-- (`bpW:w3:transport-tori-weak`, real form). -/
theorem birk_transport_tori_weak_real (hapos : 0 < a) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace)
    (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m p * ‖Ψ θ‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed a p (p - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed a p (p - 1) (by linarith)
        (birkRestField m hm hapos.le hp (Ψ θ)))
    (θ : Fin 2 → ℝ) :
    (∃ y : BirkSpace, birkEmbed a (p + 1) p (by linarith) y = Ψ θ ∧
      ‖y‖ ≤ ‖D θ‖ + waveCubicConst p * ‖Ψ θ‖ ^ 3 +
        66 * waveCubicConst p * birkCF m p * ‖Ψ θ‖ ^ 5) ∧
    birkZR (birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ))) =
        birkGamma m hm hapos.le hp 1 (Ψ θ) ∧
      ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkPi (birkGamma m hm hapos.le hp 1 (Ψ (θ + t • ν)))).1 j)
          (lam m hm j * coeffW (K := ℝ) a p
            (birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ))).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkPi (birkGamma m hm hapos.le hp 1 (Ψ (θ + t • ν)))).2 j)
          (-(lam m hm j * coeffW (K := ℝ) a p
              (birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ))).1 j) -
            waveCubic m hm (coeffW (K := ℝ) a p
              (birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ))).1) j) 0 := by
  have hreg : ∀ θ', ∃ y : BirkSpace, birkEmbed a (p + 1) p (by linarith) y = Ψ θ' ∧
      birkXLam m hm y = D θ' - birkRestField m hm hapos.le hp (Ψ θ') := fun θ' => by
    set R := D θ' - birkRestField m hm hapos.le hp (Ψ θ') with hR
    have h0 : birkEmbed a p (p - 1) (by linarith) R = birkXLam m hm (Ψ θ') := by
      rw [hR, map_sub, heq θ']; abel
    exact ⟨birkXLamInv m hm R, birkEmbed_birkXLamInv R (Ψ θ') h0,
      birkXLam_birkXLamInv m hm R⟩
  choose Y hY1 hY2 using hreg
  have hYρ : ∀ θ', birkRho (Y θ') = Y θ' := fun θ' => by
    refine birkEmbed_injective a (p + 1) p (by linarith) ?_
    rw [← birkRho_birkEmbed, hY1, hρ]
  have hweak := birk_transport_tori_weak (ha := hapos.le) (hm := hm) (hp := hp) ν Ψ D hΨ hder
    heq θ
  have hΨ' : ∀ θ', 160 * birkCF m p * ‖birkEmbed a (p + 1) p (by linarith) (Y θ')‖ ^ 2 < 1 :=
    fun θ' => by rw [hY1 θ']; exact hΨ θ'
  have hder' : ∀ θ' : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Y (θ' + t • ν)))
      (birkXLam m hm (Y θ') +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamBarX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Y θ'))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamNorX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Y θ'))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkXK m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Y θ')))) 0 := fun θ' => by
    have h1 : (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Y (θ' + t • ν))) =
        fun t : ℝ => Ψ (θ' + t • ν) := funext fun t => hY1 _
    rw [h1]
    refine (hder θ').congr_deriv ?_
    rw [hY2 θ', hY1 θ']; unfold birkRestField; abel
  have hmain := birk_transport_tori_real (a := a) (p := p) (hm := hm) (hp := hp) hapos ν Y hYρ
    hΨ' hder' θ
  have hT : ∀ θ', birkTransportQP m hm hapos.le hp Y θ' =
      birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ')) := fun θ' => by
    simp only [birkTransportQP, hY1]
  obtain ⟨y, z, hy1, hybd, -, -⟩ := hweak
  refine ⟨⟨y, hy1, hybd⟩, ?_⟩
  have e : ∀ θ', birkTransportQP m hm hapos.le hp Y θ' =
      birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ')) := hT
  simp only [e] at hmain
  refine ⟨?_, hmain.2⟩
  have := hmain.1
  rwa [hY1 θ] at this

end KAM.Wave

end
