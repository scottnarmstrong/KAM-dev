/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainRealWeak
public import KAM.Wave.Cubic.FrozenForm

/-!
# Transported tori in the frozen form (blueprint-W `bpW:w3:transport-tori`, `bpW:w1:coordinatewise`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-MAIN, blueprint labels `bpW:w3:transport-tori`,
`bpW:w3:transport-tori-weak`.

At `(a,p) = (1,1)` the real transport (`birk_transport_tori_real_aux`) says that the frozen
coordinatewise system of clause (4) holds along `ν` for `Kmap θ = (Q,P) = Π Γ ι Ψ θ ∈ E_{1,1}`
(`birk_transport_tori_frozen_coord_aux`), and, when `ι Ψ` is differentiable at `θ`, that
`ι̂ (DKmap(θ) ν) = X^w(Kmap θ)` (`birk_transport_tori_frozen_aux`, via
`frozen_invariance_iff_waveXw`); the weak version is `birk_transport_tori_weak_frozen_aux`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m}

/-- The frozen coordinatewise form of the system at `(a,p) = (1,1)`. -/
theorem birk_transport_tori_frozen_coord_aux (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m 1 * ‖birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ)‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamBarX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamNorX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkXKExt m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ)))) 0)
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff (birkTransportQPExt m hm zero_le_one hp Ψ (θ + t • ν)).1 j)
        (lam m hm j * coeff (birkTransportQPExt m hm zero_le_one hp Ψ θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (birkTransportQPExt m hm zero_le_one hp Ψ (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (birkTransportQPExt m hm zero_le_one hp Ψ θ).1 j) -
          cubicGrad m hm (birkTransportQPExt m hm zero_le_one hp Ψ θ).1 j) 0 := by
  have h := (birk_transport_tori_real_aux (a := 1) (p := 1) (hm := hm) (hp := hp) one_pos ν Ψ hρ hΨ
    hder θ).2 j
  simp only [coeffW_one_one] at h
  rw [cubicGrad_eq_waveCubic]
  exact h

/-- `‖w‖` small enough for `Γ` to be differentiable (`40 C_F ‖w‖² < 1`). -/
theorem birk_lt_forty_of_lt_160 {c r : ℝ} (hc : 0 ≤ c) (h : 160 * c * r ^ 2 < 1) :
    40 * c * r ^ 2 < 1 := by
  have : 0 ≤ c * r ^ 2 := mul_nonneg hc (sq_nonneg _)
  nlinarith

include hm in
/-- `Γ` is real differentiable at points of the ball `{160 C_F ‖w‖² < 1}`. -/
theorem birkGamma_differentiableAt_one {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p} (w : BirkSpace)
    (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    DifferentiableAt ℝ (fun w' => birkGamma m hm ha hp 1 w') w :=
  (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num)
    (birk_lt_forty_of_lt_160 (birkCF_pos m hm hp).le hw)).differentiableAt

include hm in
/-- (`bpW:w3:transport-tori`, frozen form) If moreover `ι Ψ` is differentiable at `θ`, then
`ι̂ (DKmap(θ) ν) = X^w(Kmap θ)` for `Kmap θ = (Q,P) = Π Γ ι Ψ θ`. -/
theorem birk_transport_tori_frozen_aux (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m 1 * ‖birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ)‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamBarX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamNorX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkXKExt m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ)))) 0)
    (θ : Fin 2 → ℝ)
    (hdiff : DifferentiableAt ℝ (fun θ' => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ')) θ) :
    (embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (birkTransportQPExt m hm zero_le_one hp Ψ) θ ν).1,
      embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (birkTransportQPExt m hm zero_le_one hp Ψ) θ ν).2) =
      waveXw m hm (birkTransportQPExt m hm zero_le_one hp Ψ θ) := by
  have hK : DifferentiableAt ℝ (birkTransportQPExt m hm zero_le_one hp Ψ) θ :=
    (birkPi.differentiableAt).comp θ
      ((birkGamma_differentiableAt_one (hm := hm) (ha := zero_le_one) (hp := hp) _ (hΨ θ)).comp
        θ hdiff)
  exact (frozen_invariance_iff_waveXw (m := m) hm hK).1
    (fun j => birk_transport_tori_frozen_coord_aux hp ν Ψ hρ hΨ hder θ j)

include hm in
/-- (`bpW:w3:transport-tori-weak`, frozen form, coordinatewise) -/
theorem birk_transport_tori_weak_frozen_coord_aux (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m 1 * ‖Ψ θ‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed 1 1 (1 - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestFieldExt m hm zero_le_one hp (Ψ θ)))
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff
        (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ (θ + t • ν)))).1 j)
        (lam m hm j * coeff (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff
        (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ (θ + t • ν)))).2 j)
        (-(lam m hm j * coeff (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).1 j) -
          cubicGrad m hm (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).1 j) 0 := by
  have h := (birk_transport_tori_weak_real_aux (a := 1) (p := 1) (hm := hm) (hp := hp) one_pos ν Ψ D
    hρ hΨ hder heq θ).2.2 j
  simp only [coeffW_one_one] at h
  rw [cubicGrad_eq_waveCubic]
  exact h

include hm in
/-- (`bpW:w3:transport-tori-weak`, frozen form) If `Ψ` is differentiable at `θ`:
`ι̂ (DKmap(θ) ν) = X^w(Kmap θ)` for `Kmap θ = Π Γ Ψ θ`. -/
theorem birk_transport_tori_weak_frozen_aux (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m 1 * ‖Ψ θ‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed 1 1 (1 - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestFieldExt m hm zero_le_one hp (Ψ θ)))
    (θ : Fin 2 → ℝ) (hdiff : DifferentiableAt ℝ Ψ θ) :
    (embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (fun θ' => birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ'))) θ ν).1,
      embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (fun θ' => birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ'))) θ ν).2) =
      waveXw m hm (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))) := by
  have hK : DifferentiableAt ℝ (fun θ' => birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ'))) θ :=
    (birkPi.differentiableAt).comp θ
      ((birkGamma_differentiableAt_one (hm := hm) (ha := zero_le_one) (hp := hp) _ (hΨ θ)).comp
        θ hdiff)
  exact (frozen_invariance_iff_waveXw (m := m) hm hK).1
    (fun j => birk_transport_tori_weak_frozen_coord_aux hp ν Ψ D hρ hΨ hder heq θ j)

end KAM.Wave

end
