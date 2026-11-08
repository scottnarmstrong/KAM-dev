/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainYSeries

/-!
# Domain-restricted objects of the normal form (blueprint-W `bpW:w3:main` (i)–(ii))

Package W3-MAIN, blueprint labels `bpW:w3:main`, `bpW:w3:Yseries`.

The source objects of `bpW:w3:main` live on balls; here they are defined only there (as
`Set.domRestrict` of the internal totalized helpers `…Ext`, which are meaningful only on the ball):
* on `B_{ρ₀} = birkBall0 m p`: `birkPsi` (`ψ = Γ - id`, `𝔚⁺`-valued), `birkXi = Dψ`,
  `birkAF = DΓ` on `𝔚⁺`, `birkBF = DΓ⁻¹` on `𝔚⁺` (`birkInvData`);
* on `B_{ρ₁} = birkBall1 m p`: `birkK1 = G∘Γ - G`, `birkK2 = Λ∘Γ - Λ - Z'`,
  `birkK = H∘Γ - Λ - Ḡ - G^{nor}`, and the fields `birkXK1`, `birkXK2`, `birkXK`.

Statements about analyticity and Fréchet derivatives of a map `f : U → β` defined on an open set
`U` are stated for every extension `g` of `f` (`IsBirkExtension f g`); they only depend on `f`.
`IsBirkClassAOn U P X`: every extension of `(P, X)` is in the class `𝒜(U)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-! ### Maps defined on a subset -/

/-- `g : E → β` extends the map `f : U → β` defined on `U ⊂ E`. -/
def IsBirkExtension {E β : Type*} {U : Set E} (f : U → β) (g : E → β) : Prop :=
  ∀ x : U, g x = f x

section Extension

variable {E β : Type*} {U : Set E}

theorem IsBirkExtension.eqOn_restrict {f g : E → β} (hg : IsBirkExtension (U.domRestrict f) g) :
    Set.EqOn f g U := fun x hx => (hg ⟨x, hx⟩).symm

theorem IsBirkExtension.eventuallyEq_restrict [TopologicalSpace E] {f g : E → β}
    (hU : IsOpen U) (hg : IsBirkExtension (U.domRestrict f) g) {x : E} (hx : x ∈ U) :
    f =ᶠ[nhds x] g :=
  Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun _ hy => hg.eqOn_restrict hy

end Extension

/-- `𝒜(U)` for maps `P : U → ℂ`, `X : U → 𝔚⁺` defined on `U`: every extension of `(P, X)`
belongs to `𝒜(U)` (`IsBirkClassA` depends only on the values on the open set `U`). -/
def IsBirkClassAOn (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (U : Set BirkSpace) (P : U → ℂ)
    (X : U → BirkSpace) : Prop :=
  ∀ P' X', IsBirkExtension P P' → IsBirkExtension X X' → IsBirkClassA a p ha hp U P' X'

section ClassA

variable {a p : ℝ} {ha : 0 ≤ a} {hp : 0 ≤ p} {U : Set BirkSpace}

/-- `IsBirkClassA` only depends on the values on `U`. -/
theorem IsBirkClassA.of_eqOn {P P' : BirkSpace → ℂ} {X X' : BirkSpace → BirkSpace}
    (h : IsBirkClassA a p ha hp U P X) (hP : Set.EqOn P P' U) (hX : Set.EqOn X X' U) :
    IsBirkClassA a p ha hp U P' X' where
  isOpen := h.isOpen
  rho_mem := h.rho_mem
  real w hw := by rw [← hP (h.rho_mem w hw), ← hP hw]; exact h.real w hw
  analytic := h.analytic.congr h.isOpen hP
  field w hw v := by
    have e : P' =ᶠ[nhds w] P :=
      Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds hw) fun y hy => (hP hy).symm
    rw [e.fderiv_eq, ← hX hw]; exact h.field w hw v
  analytic_field := h.analytic_field.congr h.isOpen hX

theorem IsBirkClassA.isBirkClassAOn {P : BirkSpace → ℂ} {X : BirkSpace → BirkSpace}
    (h : IsBirkClassA a p ha hp U P X) :
    IsBirkClassAOn a p ha hp U (U.domRestrict P) (U.domRestrict X) :=
  fun _ _ hP hX => h.of_eqOn hP.eqOn_restrict hX.eqOn_restrict

end ClassA

/-! ### The restricted objects -/

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- (`bpW:w3:main`, Step XK1) `ψ = Γ - id` on `B_{ρ₀}`, as a `𝔚⁺`-valued map. -/
def birkPsi : birkBall0 m p → BirkSpace := (birkBall0 m p).domRestrict (birkPsiExt m hm ha hp)

/-- (`bpW:w3:main`, Step XK1) `Ξ(w) = Dψ(w) : 𝔚 → 𝔚⁺` on `B_{ρ₀}`. -/
def birkXi : birkBall0 m p → BirkSpace →L[ℂ] BirkSpace :=
  (birkBall0 m p).domRestrict (birkXiExt m hm ha hp)

/-- (`bpW:w3:flow` (iii)) `DΓ(w) = I + Ξ(w) ι` on `𝔚⁺`, `w ∈ B_{ρ₀}`. -/
def birkAF : birkBall0 m p → BirkSpace →L[ℂ] BirkSpace :=
  (birkBall0 m p).domRestrict (birkAFExt m hm ha hp)

/-- (`bpW:w3:flow` (iii)) `DΓ(w)⁻¹` on `𝔚⁺`, `w ∈ B_{ρ₀}` (a two-sided inverse: `birkInvData`). -/
def birkBF : birkBall0 m p → BirkSpace →L[ℂ] BirkSpace :=
  (birkBall0 m p).domRestrict (birkBFExt m hm ha hp)

/-- (`bpW:w3:main`) `K₁ = G ∘ Γ - G` on `B_{ρ₁}`. -/
def birkK1 : birkBall1 m p → ℂ := (birkBall1 m p).domRestrict (birkK1Ext m hm ha hp)

/-- (`bpW:w3:main`) `K₂ = Λ ∘ Γ - Λ - Z'` on `B_{ρ₁}`. -/
def birkK2 : birkBall1 m p → ℂ := (birkBall1 m p).domRestrict (birkK2Ext m hm ha hp)

/-- (`bpW:w3:main`) `K = H ∘ Γ - Λ - Ḡ - G^{nor}` on `B_{ρ₁}`, `H = Λ + G`. -/
def birkK : birkBall1 m p → ℂ := (birkBall1 m p).domRestrict (birkKExt m hm ha hp)

/-- (`bpW:w3:main`, Step XK1) `X_{K₁}(w) = DΓ(w)⁻¹ X_G(Γ w) - X_G(w) ∈ 𝔚⁺` on `B_{ρ₁}`. -/
def birkXK1 : birkBall1 m p → BirkSpace := (birkBall1 m p).domRestrict (birkXK1Ext m hm ha hp)

/-- (`bpW:w3:main`, Step XK2) `X_{K₂}(w) = Σ_{n ≥ 1} V_n(w,…,w)/(n+1) = ∫₀¹ Y(t,w) dt`
(`birkYInt_eq_birkXK2`) on `B_{ρ₁}`. -/
def birkXK2 : birkBall1 m p → BirkSpace := (birkBall1 m p).domRestrict (birkXK2Ext m hm ha hp)

/-- (`bpW:w3:main` (ii)) `X_K = X_{K₁} + X_{K₂}` on `B_{ρ₁}`. -/
def birkXK : birkBall1 m p → BirkSpace := (birkBall1 m p).domRestrict (birkXKExt m hm ha hp)

variable {m hm ha hp}

/-! ### Characterizations on `B_{ρ₀}` -/

section Ball0

variable (w : birkBall0 m p)

/-- (`bpW:w3:flow` (iii)) The inverse data of `DΓ(w)` on `𝔚` and on `𝔚⁺`: `birkBF w` is the
two-sided inverse of `birkAF w`, compatible with the inverse `B` on `𝔚`, of norm `≤ 2`, with
`‖(birkBF w - 1) f‖₊ ≤ 20 C_F ‖w‖² ‖f‖₊`. -/
theorem birkInvData :
    ∃ B : BirkSpace →L[ℂ] BirkSpace, birkGammaD m hm ha hp 1 w * B = 1 ∧
      B * birkGammaD m hm ha hp 1 w = 1 ∧
      (birkEmbed a (p + 1) p (by linarith)).comp (birkBF m hm ha hp w) =
        B.comp (birkEmbed a (p + 1) p (by linarith)) ∧
      ‖birkBF m hm ha hp w‖ ≤ 2 ∧ birkAF m hm ha hp w * birkBF m hm ha hp w = 1 ∧
      birkBF m hm ha hp w * birkAF m hm ha hp w = 1 ∧
      ∀ f, ‖birkBF m hm ha hp w f - f‖ ≤ 20 * birkCF m p * ‖(w : BirkSpace)‖ ^ 2 * ‖f‖ :=
  birkInvDataExt (hm := hm) (hp := hp) (ha := ha) w w.2

end Ball0

/-! ### The remainder `K` on `B_{ρ₁}` -/

section Ball1

variable (w : birkBall1 m p)

/-- (`bpW:w3:main` (i)) `K = K₁ + K₂`. -/
theorem birkK_eq : birkK m hm ha hp w = birkK1 m hm ha hp w + birkK2 m hm ha hp w :=
  birkKExt_eq m hm ha hp w

/-- (`bpW:w3:main` (i)) `|K₁(w)| ≤ 5 C_* C_F ‖w‖⁶`. -/
theorem norm_birkK1_le :
    ‖birkK1 m hm ha hp w‖ ≤ 5 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 6 :=
  norm_birkK1Ext_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (i)) `|K₂(w)| ≤ 5 C_* C_F ‖w‖⁶`. -/
theorem norm_birkK2_le :
    ‖birkK2 m hm ha hp w‖ ≤ 5 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 6 :=
  norm_birkK2Ext_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (i)) `|K(w)| ≤ C_K ‖w‖⁶`, `C_K = 10 C_* C_F`. -/
theorem norm_birkK_le :
    ‖birkK m hm ha hp w‖ ≤ 10 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 6 :=
  norm_birkKExt_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (i)) `K` is real: `K(ϱw) = conj K(w)`. -/
theorem birkK_rho :
    birkK m hm ha hp ⟨birkRho w, birkRho_mem_birkBall1 m w.2⟩ =
      starRingEnd ℂ (birkK m hm ha hp w) :=
  birkKExt_rho (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (ii)) `‖X_{K₁}(w)‖₊ ≤ 44 C_* C_F ‖w‖⁵`. -/
theorem norm_birkXK1_le :
    ‖birkXK1 m hm ha hp w‖ ≤ 44 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 5 :=
  norm_birkXK1Ext_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (ii)) `‖X_{K₂}(w)‖₊ ≤ 22 C_* C_F ‖w‖⁵`. -/
theorem norm_birkXK2_le :
    ‖birkXK2 m hm ha hp w‖ ≤ 22 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 5 :=
  norm_birkXK2Ext_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (ii)) `‖X_K(w)‖₊ ≤ C'_K ‖w‖⁵`, `C'_K = 66 C_* C_F`. -/
theorem norm_birkXK_le :
    ‖birkXK m hm ha hp w‖ ≤ 66 * waveCubicConst p * birkCF m p * ‖(w : BirkSpace)‖ ^ 5 :=
  norm_birkXKExt_le (hm := hm) (hp := hp) (ha := ha) w w.2

/-- (`bpW:w3:main` (ii)) `X_K = X_{K₁} + X_{K₂}`. -/
theorem birkXK_eq : birkXK m hm ha hp w = birkXK1 m hm ha hp w + birkXK2 m hm ha hp w := rfl

/-- (`bpW:w3:Yseries`, `bpW:w3:main` Step XK2) `∫₀¹ Y(t,w) dt = X_{K₂}(w)`. -/
theorem birkYInt_eq_birkXK2 : birkYInt m hm ha hp w = birkXK2 m hm ha hp w :=
  birkYInt_eq_birkXK2Ext w

end Ball1

section Calculus

/-- (`bpW:w3:main` (i)) `K` is analytic on `B_{ρ₁}`. -/
theorem birkK_analyticOnNhd (g : BirkSpace → ℂ) (hg : IsBirkExtension (birkK m hm ha hp) g) :
    AnalyticOnNhd ℂ g (birkBall1 m p) :=
  ((birkKExt_analyticOnNhd (hm := hm) (hp := hp) (ha := ha)).mono
    (birkBall1_subset_birkBall0 m hm hp)).congr (isOpen_birkBall1 m p) hg.eqOn_restrict

/-- (`bpW:w3:main`, Step XK1) `DK₁(w) v = Ω(X_{K₁}(w), v)`. -/
theorem birkK1_field (g : BirkSpace → ℂ) (hg : IsBirkExtension (birkK1 m hm ha hp) g)
    (w : birkBall1 m p) (v : BirkSpace) :
    fderiv ℂ g w v = birkOmegaPlus a p ha (by linarith) (birkXK1 m hm ha hp w) v := by
  rw [← (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) w.2).fderiv_eq]
  exact birkK1Ext_field (hm := hm) (hp := hp) (ha := ha) w w.2 v

/-- (`bpW:w3:main`, Step XK2) `DK₂(w) v = Ω(X_{K₂}(w), v)`. -/
theorem birkK2_field (g : BirkSpace → ℂ) (hg : IsBirkExtension (birkK2 m hm ha hp) g)
    (w : birkBall1 m p) (v : BirkSpace) :
    fderiv ℂ g w v = birkOmegaPlus a p ha (by linarith) (birkXK2 m hm ha hp w) v := by
  rw [← (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) w.2).fderiv_eq]
  exact birkK2Ext_field (hm := hm) (hp := hp) (ha := ha) w w.2 v

/-- (`bpW:w3:main` (ii)) `DK(w) v = Ω(X_K(w), v)`. -/
theorem birkK_field (g : BirkSpace → ℂ) (hg : IsBirkExtension (birkK m hm ha hp) g)
    (w : birkBall1 m p) (v : BirkSpace) :
    fderiv ℂ g w v = birkOmegaPlus a p ha (by linarith) (birkXK m hm ha hp w) v := by
  rw [← (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) w.2).fderiv_eq]
  exact birkKExt_field (hm := hm) (hp := hp) (ha := ha) w w.2 v

/-- (`bpW:w3:main` (ii)) `X_{K₁}` is analytic `B_{ρ₁} → 𝔚⁺`. -/
theorem birkXK1_analyticOnNhd (g : BirkSpace → BirkSpace)
    (hg : IsBirkExtension (birkXK1 m hm ha hp) g) : AnalyticOnNhd ℂ g (birkBall1 m p) :=
  fun w hw => (birkXK1Ext_analyticAt (hm := hm) (hp := hp) (ha := ha) w hw).congr
    (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) hw)

/-- (`bpW:w3:main` (ii)) `X_{K₂}` is analytic `B_{ρ₁} → 𝔚⁺`. -/
theorem birkXK2_analyticOnNhd (g : BirkSpace → BirkSpace)
    (hg : IsBirkExtension (birkXK2 m hm ha hp) g) : AnalyticOnNhd ℂ g (birkBall1 m p) :=
  fun w hw => (birkXK2Ext_analyticAt (hm := hm) (hp := hp) (ha := ha) w hw).congr
    (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) hw)

/-- (`bpW:w3:main` (ii)) `X_K` is analytic `B_{ρ₁} → 𝔚⁺`. -/
theorem birkXK_analyticOnNhd (g : BirkSpace → BirkSpace)
    (hg : IsBirkExtension (birkXK m hm ha hp) g) : AnalyticOnNhd ℂ g (birkBall1 m p) :=
  fun w hw => (birkXKExt_analyticAt (hm := hm) (hp := hp) (ha := ha) w hw).congr
    (hg.eventuallyEq_restrict (isOpen_birkBall1 m p) hw)

/-- (`bpW:w3:main` (i), (ii)) `K ∈ 𝒜(B_{ρ₁})` with Hamiltonian field `X_K`. -/
theorem birkK_isClassA :
    IsBirkClassAOn a p ha (by linarith) (birkBall1 m p) (birkK m hm ha hp) (birkXK m hm ha hp) :=
  (birkKExt_isClassA (hm := hm) (hp := hp) (ha := ha)).isBirkClassAOn

/-- `K₂ ∈ 𝒜(B_{ρ₁})` with Hamiltonian field `X_{K₂}`. -/
theorem birkK2_isClassA :
    IsBirkClassAOn a p ha (by linarith) (birkBall1 m p) (birkK2 m hm ha hp)
      (birkXK2 m hm ha hp) :=
  (birkK2Ext_isClassA (hm := hm) (hp := hp) (ha := ha)).isBirkClassAOn

/-- (`bpW:w3:main` (ii)) Reality of the field: `X_K(ϱw) = ϱ X_K(w)`. -/
theorem birkXK_rho (w : birkBall1 m p) :
    birkXK m hm ha hp ⟨birkRho w, birkRho_mem_birkBall1 m w.2⟩ =
      birkRho (birkXK m hm ha hp w) :=
  (birkKExt_isClassA (hm := hm) (hp := hp) (ha := ha)).field_rho w.2

end Calculus

end KAM.Wave

end
