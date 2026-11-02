/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainBall
public import KAM.Wave.Birkhoff.MainFrozenForm
public import KAM.Wave.Birkhoff.MainRealId

/-!
# Domain-restricted real objects and transport of tori (blueprint-W `bpW:w3:main`,
`bpW:w3:gamma-real`, `bpW:w3:transport-tori`, `bpW:w3:transport-tori-weak`)

Package W3-MAIN, blueprint labels `bpW:w3:main` (ii) real part, (iv),
`bpW:w3:gamma-real`, `bpW:w3:transport-tori`, `bpW:w3:transport-tori-weak`.

Restricted objects (internal totalized helpers `…Ext`):
* `birkRealBall1 m p = B^E_{r₁} = {x ∈ E | 320 C_F ‖x‖² < 1}` (`r₁ = ρ₁/√2`) and
  `birkGammaR : B^E_{r₁} → E`, `Γ^ℝ = 𝒵⁻¹ ∘ Γ ∘ 𝒵`;
* `birkRestField : B_{ρ₁} → 𝔚`, `X_Ḡ + X_{G^{nor}} + X_K`;
* `birkTransportQP Ψ hΨ`, `(Q,P) = 𝒵⁻¹ Γ ∘ ι Ψ`, for `Ψ` with `ι Ψ(θ) ∈ B_{ρ₁}` for all `θ`.
The main results of these nodes are restated for the restricted objects.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The real ball `B^E_{r₁} = {x ∈ E | 320 C_F ‖x‖² < 1}`, `r₁ = ρ₁/√2`. -/
def birkRealBall1 (m p : ℝ) : Set BirkReal := {x | 320 * birkCF m p * ‖x‖ ^ 2 < 1}

theorem isOpen_birkRealBall1 (m p : ℝ) : IsOpen (birkRealBall1 m p) :=
  isOpen_lt (by fun_prop) continuous_const

theorem birkZR_mem_birkBall1 (m : ℝ) (hm : 0 < m) {p : ℝ} (hp : 1 / 2 ≤ p) {x : BirkReal}
    (hx : x ∈ birkRealBall1 m p) :
    birkZR x ∈ birkBall1 m p :=
  birkZR_dom (hm := hm) (hp := hp) x hx

/-- (`bpW:w3:gamma-real`) `Γ^ℝ = 𝒵⁻¹ ∘ Γ ∘ 𝒵 : B^E_{r₁} → E`. -/
def birkGammaR : birkRealBall1 m p → BirkReal :=
  (birkRealBall1 m p).domRestrict (birkGammaRExt m hm ha hp)

/-- (`bpW:w3:transport-tori-weak`) `X_Ḡ + X_{G^{nor}} + X_K` on `B_{ρ₁}` (embedded in `𝔚`). -/
def birkRestField : birkBall1 m p → BirkSpace :=
  (birkBall1 m p).domRestrict (birkRestFieldExt m hm ha hp)

/-- (`bpW:w3:transport-tori`) `(Q,P) = 𝒵⁻¹ Γ ∘ ι Ψ`, for `Ψ : ℝ² → 𝔚⁺` with `ι Ψ` taking values
in `B_{ρ₁}`. -/
def birkTransportQP (Ψ : (Fin 2 → ℝ) → BirkSpace)
    (_hΨ : ∀ θ, birkEmbed a (p + 1) p (by linarith) (Ψ θ) ∈ birkBall1 m p) (θ : Fin 2 → ℝ) :
    BirkReal :=
  birkTransportQPExt m hm ha hp Ψ θ

variable {m hm ha hp}

/-! ### `Γ^ℝ` (`bpW:w3:gamma-real`) -/

section GammaR

/-- (`bpW:w3:gamma-real` (i)) `Γ^ℝ` is real analytic on `B^E_{r₁}`. -/
theorem birkGammaR_analyticOnNhd (g : BirkReal → BirkReal)
    (hg : IsBirkExtension (birkGammaR m hm ha hp) g) : AnalyticOnNhd ℝ g (birkRealBall1 m p) :=
  (birkGammaRExt_analyticOnNhd (hm := hm) (hp := hp) (ha := ha)).congr
    (isOpen_birkRealBall1 m p) hg.eqOn_restrict

variable (x : birkRealBall1 m p)

/-- (`bpW:w3:gamma-real` (ii)) `𝒵Γ^ℝx = 𝒵x + ι𝒵ψ` with `‖ψ‖_{E_{a,p+1}} ≤ 6√2 C_F ‖x‖³`, and
`‖Γ^ℝ x‖ ≤ (10/9)√2 ‖x‖ < 2 r₁`. -/
theorem birkGammaR_sub :
    ∃ ψR : BirkReal, birkZR (birkGammaR m hm ha hp x) =
        birkZR x + birkEmbed a (p + 1) p (by linarith) (birkZR ψR) ∧
      ‖ψR‖ ≤ 6 * Real.sqrt 2 * birkCF m p * ‖(x : BirkReal)‖ ^ 3 ∧
      ‖birkGammaR m hm ha hp x‖ ≤ 10 / 9 * Real.sqrt 2 * ‖(x : BirkReal)‖ :=
  birkGammaRExt_sub (hm := hm) (hp := hp) (ha := ha) x x.2

/-- (`bpW:w3:gamma-real` (iii)) The inverse on the image: `𝒵⁻¹ Γ_{-1} 𝒵 Γ^ℝ = id`. -/
theorem birkGammaR_inv :
    birkPi (birkGamma m hm ha hp (-1) (birkZR (birkGammaR m hm ha hp x))) = x :=
  birkGammaRExt_inv (hm := hm) (hp := hp) (ha := ha) x x.2

/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ` is injective. -/
theorem birkGammaR_injective : Function.Injective (birkGammaR m hm ha hp) := fun x x' h =>
  Subtype.ext (birkGammaRExt_injOn (hm := hm) (hp := hp) (ha := ha) x.2 x'.2 h)

/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ(B^E_{r₁}) ⊃ B^E_{r₁/2}`. -/
theorem birkGammaR_surj (y : BirkReal) (hy : 1280 * birkCF m p * ‖y‖ ^ 2 < 1) :
    ∃ x : birkRealBall1 m p, birkGammaR m hm ha hp x = y := by
  obtain ⟨x, hx, h⟩ := birkGammaRExt_surj (hm := hm) (hp := hp) (ha := ha) y hy
  exact ⟨⟨x, hx⟩, h⟩

/-- (`bpW:w3:gamma-real` (iii)) `DΓ^ℝ(x) = 𝒵⁻¹ DΓ(𝒵x) 𝒵`. -/
theorem birkGammaR_hasFDerivAt (g : BirkReal → BirkReal)
    (hg : IsBirkExtension (birkGammaR m hm ha hp) g) :
    HasFDerivAt g
      ((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) x :=
  (birkGammaRExt_hasFDerivAt (hm := hm) (hp := hp) (ha := ha) x x.2).congr_of_eventuallyEq
    (hg.eventuallyEq_restrict (isOpen_birkRealBall1 m p) x.2).symm

/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ` is symplectic for `Σ dq_j ∧ dp_j`. -/
theorem birkGammaR_symplectic (ξ η : BirkReal) :
    birkOmegaR a p
        (((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) ξ)
        (((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) η)
      = birkOmegaR a p ξ η :=
  birkGammaRExt_symplectic (hm := hm) (hp := hp) (ha := ha) x x.2 ξ η

/-- (`bpW:w3:gamma-real` (iv)) `H(Γ^ℝ x) = Λ(x) + Ḡ(x) + G^{nor}(x) + K(𝒵x)` with
`Ḡ = ½⟨AI,I⟩ + ⟨BI,Z⟩`, `I_j = (q_j² + p_j²)/2`. -/
theorem birkH_gammaR :
    birkLambda m hm ha hp (birkZR (birkGammaR m hm ha hp x)) +
        birkHamG m hm ha hp (birkZR (birkGammaR m hm ha hp x)) =
      ((∑' j : ℕ+, lam m hm j * birkActionR a p x j : ℝ) : ℂ) +
        ((birkGbarR m hm a p x : ℝ) : ℂ) + birkHamNor m hm ha hp (birkZR x) +
        birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩ :=
  birkH_gammaR_aux (hm := hm) (hp := hp) (ha := ha) x x.2

end GammaR

/-! ### Real restrictions of `K` and `X_K` (`bpW:w3:main` (ii)) -/

section RealK

/-- (`bpW:w3:main` (ii)) `K^ℝ = K ∘ 𝒵` is real valued and real analytic on `B^E_{r₁}`. -/
theorem birkK_real :
    (∀ g : BirkReal → ℝ,
        (∀ x : birkRealBall1 m p,
          g x = (birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩).re) →
        AnalyticOnNhd ℝ g (birkRealBall1 m p)) ∧
      ∀ x : birkRealBall1 m p,
        (((birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩).re : ℝ) : ℂ) =
          birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩ := by
  obtain ⟨h1, h2⟩ := birkKExt_real (hm := hm) (hp := hp) (ha := ha)
  exact ⟨fun g hg => h1.congr (isOpen_birkRealBall1 m p) fun x hx => (hg ⟨x, hx⟩).symm,
    fun x => h2 x x.2⟩

/-- (`bpW:w3:main` (ii)) `X_K^ℝ = 𝒵⁻¹ X_K ∘ 𝒵 : B^E_{r₁} → E_{a,p+1}` is real analytic and
`𝒵 X_K^ℝ = X_K ∘ 𝒵`. -/
theorem birkXK_real :
    (∀ g : BirkReal → BirkReal,
        (∀ x : birkRealBall1 m p,
          g x = birkPi (birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩)) →
        AnalyticOnNhd ℝ g (birkRealBall1 m p)) ∧
      ∀ x : birkRealBall1 m p,
        birkZR (birkPi (birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩)) =
          birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩ := by
  obtain ⟨h1, h2⟩ := birkXKExt_real (hm := hm) (hp := hp) (ha := ha)
  exact ⟨fun g hg => h1.congr (isOpen_birkRealBall1 m p) fun x hx => (hg ⟨x, hx⟩).symm,
    fun x => h2 x x.2⟩

/-- (`bpW:w3:main` (ii)) `DK^ℝ(x) h = ω_ℝ(X_K^ℝ(x), h)`. -/
theorem birkK_real_fderiv (g : BirkReal → ℝ)
    (hg : ∀ x : birkRealBall1 m p,
      g x = (birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩).re)
    (x : birkRealBall1 m p) (h : BirkReal) :
    fderiv ℝ g x h =
      birkOmegaR a p (birkPi (birkEmbed a (p + 1) p (by linarith)
        (birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩))) h := by
  have e : (fun y : BirkReal => (birkKExt m hm ha hp (birkZR y)).re) =ᶠ[nhds (x : BirkReal)] g :=
    Filter.eventuallyEq_of_mem ((isOpen_birkRealBall1 m p).mem_nhds x.2) fun y hy =>
      (hg ⟨y, hy⟩).symm
  rw [← e.fderiv_eq]
  exact birkKExt_real_fderiv (hm := hm) (hp := hp) (ha := ha) x x.2 h

/-- (`bpW:w3:main` (ii)) `X_K^ℝ = (∂_p K^ℝ, -∂_q K^ℝ)` in coordinates. -/
theorem birkK_real_gradient (g : BirkReal → ℝ)
    (hg : ∀ x : birkRealBall1 m p,
      g x = (birkK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩).re)
    (x : birkRealBall1 m p) (h : BirkReal) :
    fderiv ℝ g x h =
      ∑' j : ℕ+, (coeffW (K := ℝ) a (p + 1)
            (birkPi (birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩)).1 j *
          coeffW (K := ℝ) a p h.2 j -
        coeffW (K := ℝ) a (p + 1)
            (birkPi (birkXK m hm ha hp ⟨birkZR x, birkZR_mem_birkBall1 m hm hp x.2⟩)).2 j *
          coeffW (K := ℝ) a p h.1 j) := by
  have e : (fun y : BirkReal => (birkKExt m hm ha hp (birkZR y)).re) =ᶠ[nhds (x : BirkReal)] g :=
    Filter.eventuallyEq_of_mem ((isOpen_birkRealBall1 m p).mem_nhds x.2) fun y hy =>
      (hg ⟨y, hy⟩).symm
  rw [← e.fderiv_eq]
  exact birkKExt_real_gradient (hm := hm) (hp := hp) (ha := ha) x x.2 h

end RealK

/-! ### Conjugacy and transport (`bpW:w3:main` (iv), `bpW:w3:transport-tori`) -/

section Transport

/-- (`bpW:w3:main` (iv)) For `y ∈ 𝔚⁺` with `ι y ∈ B_{ρ₁}`: `Γ(ιy) = ιz` with `z ∈ 𝔚⁺` and
`DΓ(ιy)[X_Λ(y) + X_Ḡ + X_{G^{nor}} + X_K] = X_Λ(z) + X_G(Γ(ιy))`. -/
theorem birk_conjugacy (y : BirkSpace)
    (hy : birkEmbed a (p + 1) p (by linarith) y ∈ birkBall1 m p) :
    ∃ z : BirkSpace, birkEmbed a (p + 1) p (by linarith) z =
        birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y) ∧
      birkGammaD m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y)
        (birkXLam m hm y + birkEmbed a (p + 1) p (by linarith)
            (birkHamBarX m hm ha hp (birkEmbed a (p + 1) p (by linarith) y)) +
          birkEmbed a (p + 1) p (by linarith)
            (birkHamNorX m hm ha hp (birkEmbed a (p + 1) p (by linarith) y)) +
          birkEmbed a (p + 1) p (by linarith) (birkXK m hm ha hp ⟨_, hy⟩)) =
        birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp
            (birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y))) :=
  birk_conjugacy_aux (hm := hm) (hp := hp) (ha := ha) y hy

/-- (`bpW:w3:transport-tori`) If `D(ιΨ)(θ)ν = X_{H'}(ιΨ(θ))` (`X_{H'} = X_Λ + X_Ḡ + X_{G^{nor}} +
X_K`) then `Γ∘ιΨ` takes values in `𝔚⁺` and `D(Γ∘ιΨ)(θ)ν = X_H(Γ∘ιΨ(θ))`. -/
theorem birk_transport_tori (ν : Fin 2 → ℝ) (Ψ : (Fin 2 → ℝ) → BirkSpace)
    (hΨ : ∀ θ, birkEmbed a (p + 1) p (by linarith) (Ψ θ) ∈ birkBall1 m p)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamBarX m hm ha hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamNorX m hm ha hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith) (birkXK m hm ha hp ⟨_, hΨ θ⟩)) 0)
    (θ : Fin 2 → ℝ) :
    ∃ z : BirkSpace, birkEmbed a (p + 1) p (by linarith) z =
        birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)) ∧
      HasDerivAt (fun t : ℝ => birkGamma m hm ha hp 1
          (birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν))))
        (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp
            (birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ))))) 0 :=
  birk_transport_tori_aux (hm := hm) (hp := hp) (ha := ha) ν Ψ hΨ hder θ

/-- (`bpW:w3:transport-tori`) Real tori: `(Q,P) = 𝒵⁻¹ Γ∘ιΨ` satisfies `D_ν Q_j = λ_j P_j`,
`D_ν P_j = -λ_j Q_j - 𝒢(Q)_j` (`a > 0`). -/
theorem birk_transport_tori_real (hapos : 0 < a) (ν : Fin 2 → ℝ) (Ψ : (Fin 2 → ℝ) → BirkSpace)
    (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, birkEmbed a (p + 1) p (by linarith) (Ψ θ) ∈ birkBall1 m p)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamBarX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamNorX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith) (birkXK m hm hapos.le hp ⟨_, hΨ θ⟩)) 0)
    (θ : Fin 2 → ℝ) :
    birkZR (birkTransportQP m hm hapos.le hp Ψ hΨ θ) =
        birkGamma m hm hapos.le hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)) ∧
      ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkTransportQP m hm hapos.le hp Ψ hΨ (θ + t • ν)).1 j)
          (lam m hm j * coeffW (K := ℝ) a p (birkTransportQP m hm hapos.le hp Ψ hΨ θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkTransportQP m hm hapos.le hp Ψ hΨ (θ + t • ν)).2 j)
          (-(lam m hm j * coeffW (K := ℝ) a p (birkTransportQP m hm hapos.le hp Ψ hΨ θ).1 j) -
            waveCubic m hm (coeffW (K := ℝ) a p
              (birkTransportQP m hm hapos.le hp Ψ hΨ θ).1) j) 0 :=
  birk_transport_tori_real_aux (hm := hm) (hp := hp) hapos ν Ψ hρ hΨ hder θ

/-- (`bpW:w3:transport-tori`, frozen clause (4), coordinates) At `(a,p) = (1,1)`. -/
theorem birk_transport_tori_frozen_coord (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ) ∈ birkBall1 m 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamBarX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamNorX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith) (birkXK m hm zero_le_one hp ⟨_, hΨ θ⟩)) 0)
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff (birkTransportQP m hm zero_le_one hp Ψ hΨ (θ + t • ν)).1 j)
        (lam m hm j * coeff (birkTransportQP m hm zero_le_one hp Ψ hΨ θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (birkTransportQP m hm zero_le_one hp Ψ hΨ (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (birkTransportQP m hm zero_le_one hp Ψ hΨ θ).1 j) -
          cubicGrad m hm (birkTransportQP m hm zero_le_one hp Ψ hΨ θ).1 j) 0 :=
  birk_transport_tori_frozen_coord_aux (hm := hm) hp ν Ψ hρ hΨ hder θ j

/-- (`bpW:w3:transport-tori`, frozen clause (4)) At `(a,p) = (1,1)`, `Kmap = (Q,P)` satisfies
the frozen invariance equation `D Kmap(θ) ν = X_w(Kmap θ)`. -/
theorem birk_transport_tori_frozen (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ) ∈ birkBall1 m 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamBarX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith)
          (birkHamNorX m hm zero_le_one hp (birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ))) +
        birkEmbed 1 (1 + 1) 1 (by linarith) (birkXK m hm zero_le_one hp ⟨_, hΨ θ⟩)) 0)
    (θ : Fin 2 → ℝ)
    (hdiff : DifferentiableAt ℝ (fun θ' => birkEmbed 1 (1 + 1) 1 (by linarith) (Ψ θ')) θ) :
    (embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (birkTransportQP m hm zero_le_one hp Ψ hΨ) θ ν).1,
      embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (birkTransportQP m hm zero_le_one hp Ψ hΨ) θ ν).2) =
      waveXw m hm (birkTransportQP m hm zero_le_one hp Ψ hΨ θ) :=
  birk_transport_tori_frozen_aux (hm := hm) hp ν Ψ hρ hΨ hder θ hdiff

end Transport

/-! ### Weak invariance (`bpW:w3:transport-tori-weak`) -/

section Weak

/-- (`bpW:w3:transport-tori-weak`, Step `stepW:w3:wk-reg`)
`‖X_Ḡ(w) + X_{G^{nor}}(w) + X_K(w)‖ ≤ C_* ‖w‖³ + C'_K ‖w‖⁵`. -/
theorem norm_birkRestField_le (w : birkBall1 m p) :
    ‖birkRestField m hm ha hp w‖ ≤
      waveCubicConst p * ‖(w : BirkSpace)‖ ^ 3 +
        66 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 5 :=
  norm_birkRestFieldExt_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:transport-tori-weak`) The weak equation in `𝔚_{a,p-1}` forces `Ψ(θ) ∈ 𝔚⁺` with
`‖Ψ(θ)‖₊ ≤ ‖DΨ(θ)ν‖ + C_*‖Ψ(θ)‖³ + C'_K‖Ψ(θ)‖⁵`, and then `D(Γ∘Ψ)(θ)ν = X_H(Γ∘Ψ(θ))`. -/
theorem birk_transport_tori_weak (ν : Fin 2 → ℝ) (Ψ D : (Fin 2 → ℝ) → BirkSpace)
    (hΨ : ∀ θ, Ψ θ ∈ birkBall1 m p)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed a p (p - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed a p (p - 1) (by linarith)
        (birkRestField m hm ha hp ⟨Ψ θ, hΨ θ⟩))
    (θ : Fin 2 → ℝ) :
    ∃ y z : BirkSpace, birkEmbed a (p + 1) p (by linarith) y = Ψ θ ∧
      ‖y‖ ≤ ‖D θ‖ + waveCubicConst p * ‖Ψ θ‖ ^ 3 +
        66 * waveCubicConst p * birkCF m p * ‖Ψ θ‖ ^ 5 ∧
      birkEmbed a (p + 1) p (by linarith) z = birkGamma m hm ha hp 1 (Ψ θ) ∧
      HasDerivAt (fun t : ℝ => birkGamma m hm ha hp 1 (Ψ (θ + t • ν)))
        (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp (birkGamma m hm ha hp 1 (Ψ θ)))) 0 :=
  birk_transport_tori_weak_aux (hm := hm) (hp := hp) (ha := ha) ν Ψ D hΨ hder heq θ

/-- (`bpW:w3:transport-tori-weak`) Real form of the weak transport (`a > 0`). -/
theorem birk_transport_tori_weak_real (hapos : 0 < a) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace)
    (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, Ψ θ ∈ birkBall1 m p)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed a p (p - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed a p (p - 1) (by linarith)
        (birkRestField m hm hapos.le hp ⟨Ψ θ, hΨ θ⟩))
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
              (birkPi (birkGamma m hm hapos.le hp 1 (Ψ θ))).1) j) 0 :=
  birk_transport_tori_weak_real_aux (hm := hm) (hp := hp) hapos ν Ψ D hρ hΨ hder heq θ

/-- (`bpW:w3:transport-tori-weak`, frozen clause (4), coordinates) At `(a,p) = (1,1)`. -/
theorem birk_transport_tori_weak_frozen_coord (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, Ψ θ ∈ birkBall1 m 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed 1 1 (1 - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestField m hm zero_le_one hp ⟨Ψ θ, hΨ θ⟩))
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff
        (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ (θ + t • ν)))).1 j)
        (lam m hm j * coeff (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff
        (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ (θ + t • ν)))).2 j)
        (-(lam m hm j * coeff (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).1 j) -
          cubicGrad m hm (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))).1 j) 0 :=
  birk_transport_tori_weak_frozen_coord_aux (hm := hm) hp ν Ψ D hρ hΨ hder heq θ j

/-- (`bpW:w3:transport-tori-weak`, frozen clause (4)) At `(a,p) = (1,1)`. -/
theorem birk_transport_tori_weak_frozen (hp : (1 / 2 : ℝ) ≤ 1) (ν : Fin 2 → ℝ)
    (Ψ D : (Fin 2 → ℝ) → BirkSpace) (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, Ψ θ ∈ birkBall1 m 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed 1 1 (1 - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestField m hm zero_le_one hp ⟨Ψ θ, hΨ θ⟩))
    (θ : Fin 2 → ℝ) (hdiff : DifferentiableAt ℝ Ψ θ) :
    (embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (fun θ' => birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ'))) θ ν).1,
      embedCLM 1 1 1 0 le_rfl zero_le_one
        (fderiv ℝ (fun θ' => birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ'))) θ ν).2) =
      waveXw m hm (birkPi (birkGamma m hm zero_le_one hp 1 (Ψ θ))) :=
  birk_transport_tori_weak_frozen_aux (hm := hm) hp ν Ψ D hρ hΨ hder heq θ hdiff

end Weak

end KAM.Wave

end
