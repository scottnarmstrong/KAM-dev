/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Equation
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Planetary.Poincare.Chart
public import KAM.Planetary.Poincare.D25
public import KAM.Planetary.Poincare.Lattice
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Planetary.SecularForm.ProductInterface

/-!
# Poincaré product chart, D25 and the circular endpoint: literal exports of the graph nodes

Graph-gap package GAP-P7 (append-only).  Each theorem states the literal conclusion of one node of
the dependency graph, built from the landed declarations of `SecularForm.ProductInterface`,
`Poincare.Product`, `Poincare.Lattice`, `Poincare.D25`, `Poincare.Chart`, `Poincare.Symplectic`
and `Hamiltonian.Chart`:

* `pc_eq` (`stepP:p7:pc-eq`): the Hamilton equations in the chart, moving and fixed models;
* `product_chart_full` (`bpP:p7:product-chart`): parts (a)–(d), including the quotient bijection;
* `la_ham` (`stepP:p7:la-ham`): `H ∘ Ψ ∘ Θ_n = h(I) + μ f̂ ∘ Θ_n`;
* `d25_e` (`stepP:p7:d25-e`) and `d25` (`bpP:p7:d25`): the D25 dictionary;
* `po_el_circular` (`stepP:p7:po-el#circular`): the scalar circular endpoint identities.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Function
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

/-! ### The lattice quotient -/

section Quotient

variable {n : ℕ}

private theorem fastShift_zero : (fastShift (a := n) (b := n) (0 : Fin n → ℤ)) = 0 := by
  refine Prod.ext (funext fun j => ?_) rfl
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift]

private theorem fastShift_add (k k' : Fin n → ℤ) :
    fastShift (a := n) (b := n) (k + k') =
      fastShift (a := n) (b := n) k + fastShift (a := n) (b := n) k' := by
  refine Prod.ext (funext fun j => ?_) (by simp [fastShift])
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift, mul_add]

private theorem fastShift_neg (k : Fin n → ℤ) :
    fastShift (a := n) (b := n) (-k) = -fastShift (a := n) (b := n) k := by
  refine Prod.ext (funext fun j => ?_) (by simp [fastShift])
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift]

/-- The orbit relation of the fast lattice `{((2π k, 0), 0)}` on `O_n`. -/
def fastLatticeSetoid (n : ℕ) : Setoid (poincareProdDom n) where
  r w w' := ∃ k : Fin n → ℤ, (w' : Phase (n + n)) = w + fastShift (a := n) (b := n) k
  iseqv :=
    ⟨fun w => ⟨0, by rw [fastShift_zero, add_zero]⟩,
     fun {w w'} ⟨k, hk⟩ => ⟨-k, by rw [fastShift_neg, hk]; abel⟩,
     fun {w w' w''} ⟨k, hk⟩ ⟨k', hk'⟩ => ⟨k + k', by rw [fastShift_add, hk', hk]; abel⟩⟩

/-- `bpP:p7:product-chart` (a): `Ψ` induces a bijection `O_n / lattice → 𝒦⁽ⁿ⁾`. -/
theorem exists_quotient_bijection (D : SecularForm.Data n) :
    ∃ f : Quotient (fastLatticeSetoid n) → regionProd D.m (D.G * D.m0),
      Function.Bijective f ∧
        ∀ w : poincareProdDom n, (f (Quotient.mk _ w) : Phase (n * 2)) =
          poincareProd D.m (D.G * D.m0) w := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hmem : ∀ w : poincareProdDom n, poincareProd D.m (D.G * D.m0) w ∈
      regionProd D.m (D.G * D.m0) := fun w => poincareProd_mem_regionProd D.hm hκ w.2
  refine ⟨Quotient.lift (fun w => ⟨poincareProd D.m (D.G * D.m0) w, hmem w⟩) ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro w w' ⟨k, hk⟩
    refine Subtype.ext ?_
    show poincareProd D.m (D.G * D.m0) w = poincareProd D.m (D.G * D.m0) w'
    rw [hk]
    exact (poincareProd_lattice D.hm hκ w.2 k).2.symm
  · intro a b
    induction a using Quotient.inductionOn with | _ w => ?_
    induction b using Quotient.inductionOn with | _ w' => ?_
    intro h
    have h' : poincareProd D.m (D.G * D.m0) w = poincareProd D.m (D.G * D.m0) w' :=
      congrArg Subtype.val h
    exact Quotient.sound ((poincareProd_eq_iff D.hm hκ w.2 w'.2).1 h')
  · rintro ⟨z, hz⟩
    have hz' : z ∈ poincareProd D.m (D.G * D.m0) '' poincareProdDom n := by
      rw [poincareProd_image D.hm hκ]; exact hz
    obtain ⟨w, hw, rfl⟩ := hz'
    exact ⟨Quotient.mk _ ⟨w, hw⟩, rfl⟩
  · intro w; rfl

end Quotient

namespace SecularForm

variable {n : ℕ}

/-! ### `stepP:p7:pc-eq` -/

/-- The Hamilton equations of `G ∘ Ψ` at `w` in the chart coordinates `z₁ = (λ, ξ)`,
`z₂ = (Λ, η)` for `G = h + μ f̂`, with `f̂ = f`: `λ̇ᵢ = νᵢ + μ ∂_{Λᵢ} f̂`, `Λ̇ᵢ = -μ ∂_{λᵢ} f̂`,
`ξ̇ᵢ = μ ∂_{ηᵢ} f̂`, `η̇ᵢ = -μ ∂_{ξᵢ} f̂`. -/
def ChartHamiltonEq (D : Data n) (H : Phase (n * 2) → ℝ) (f : Phase (n + n) → ℝ) (μ : ℝ)
    (w : Phase (n + n)) : Prop :=
  ∀ i : Fin n,
    fast (hamiltonianVectorField (H ∘ poincareProd D.m (D.G * D.m0)) w).1 i =
      nu D (fast w.2) i +
        μ * fderiv ℝ f w ((0 : Fin (n + n) → ℝ), Pi.single (Fin.castAdd n i) 1) ∧
    slow (hamiltonianVectorField (H ∘ poincareProd D.m (D.G * D.m0)) w).1 i =
      μ * fderiv ℝ f w ((0 : Fin (n + n) → ℝ), Pi.single (Fin.natAdd n i) 1) ∧
    fast (hamiltonianVectorField (H ∘ poincareProd D.m (D.G * D.m0)) w).2 i =
      -(μ * fderiv ℝ f w (Pi.single (Fin.castAdd n i) 1, (0 : Fin (n + n) → ℝ))) ∧
    slow (hamiltonianVectorField (H ∘ poincareProd D.m (D.G * D.m0)) w).2 i =
      -(μ * fderiv ℝ f w (Pi.single (Fin.natAdd n i) 1, (0 : Fin (n + n) → ℝ)))

private theorem chartHamiltonEq_core (D : Data n) (μ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (H : Phase (n * 2) → ℝ) (f : Phase (n + n) → ℝ)
    (hf : DifferentiableAt ℝ f w) (hH : DifferentiableAt ℝ H (poincareProd D.m (D.G * D.m0) w))
    (hev : ∀ v ∈ poincareProdDom n,
      H (poincareProd D.m (D.G * D.m0) v) = hProd (D.G * D.m0) D.m v + μ * f v) :
    ChartHamiltonEq D H f μ w := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hΨ : DifferentiableAt ℝ (poincareProd D.m (D.G * D.m0)) w :=
    (analyticOnNhd_poincareProd D.hm hκ w hw).differentiableAt
  have hHΨ : DifferentiableAt ℝ (H ∘ poincareProd D.m (D.G * D.m0)) w := hH.comp w hΨ
  have e : (H ∘ poincareProd D.m (D.G * D.m0)) =ᶠ[𝓝 w]
      fun v => hProd (D.G * D.m0) D.m v + μ * f v := by
    filter_upwards [(isOpen_poincareProdDom n).mem_nhds hw] with v hv
    exact hev v hv
  have hK : DifferentiableAt ℝ (hProd (D.G * D.m0) D.m) w := by
    have e2 : (fun v => (H ∘ poincareProd D.m (D.G * D.m0)) v - μ * f v) =ᶠ[𝓝 w]
        hProd (D.G * D.m0) D.m := by
      filter_upwards [(isOpen_poincareProdDom n).mem_nhds hw] with v hv
      simp only [Function.comp_apply, hev v hv]
      ring
    exact (hHΨ.sub (hf.const_mul μ)).congr_of_eventuallyEq e2.symm
  have hd : fderiv ℝ (H ∘ poincareProd D.m (D.G * D.m0)) w =
      fderiv ℝ (hProd (D.G * D.m0) D.m) w + μ • fderiv ℝ f w := by
    rw [e.fderiv_eq, fderiv_fun_add hK (hf.const_mul μ), fderiv_const_mul hf]
  have hXh := (product_chart D).2.2 w hw
  have h1 : ∀ j, fderiv ℝ (hProd (D.G * D.m0) D.m) w ((0 : Fin (n + n) → ℝ), Pi.single j 1) =
      Fin.append (nu D (fast w.2)) (0 : Fin n → ℝ) j := fun j =>
    congrFun (congrArg Prod.fst hXh) j
  have h2 : ∀ j, -fderiv ℝ (hProd (D.G * D.m0) D.m) w (Pi.single j 1, (0 : Fin (n + n) → ℝ)) =
      (0 : Fin (n + n) → ℝ) j := fun j => congrFun (congrArg Prod.snd hXh) j
  intro i
  have a1 := h1 (Fin.castAdd n i)
  have a2 := h1 (Fin.natAdd n i)
  have b1 := h2 (Fin.castAdd n i)
  have b2 := h2 (Fin.natAdd n i)
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply] at a1 a2 b1 b2
  have b1' : fderiv ℝ (hProd (D.G * D.m0) D.m) w (Pi.single (Fin.castAdd n i) 1,
      (0 : Fin (n + n) → ℝ)) = 0 := by linarith
  have b2' : fderiv ℝ (hProd (D.G * D.m0) D.m) w (Pi.single (Fin.natAdd n i) 1,
      (0 : Fin (n + n) → ℝ)) = 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fast, slow, hamiltonianVectorField, hd, add_apply,
      smul_apply, smul_eq_mul]
  · rw [a1]
  · rw [a2]; ring
  · rw [b1']; ring
  · rw [b2']; ring

/-- `stepP:p7:pc-eq`: on `Ψ⁻¹(W)` (`hW`), the components of `X_{H ∘ Ψ}` for the moving
(`b = true`, `G = h + μ f̂_mov`) or fixed (`b = false`, `G = h + ε f̂_fix`, with `μ = ε`) model are
`λ̇ = ν + μ ∂_Λ f̂`, `Λ̇ = -μ ∂_λ f̂`, `ξ̇ = μ ∂_η f̂`, `η̇ = -μ ∂_ξ f̂`. -/
theorem pc_eq (D : Data n) (b : Bool) (μ : ℝ) {w : Phase (n + n)} (hw : w ∈ poincareProdDom n)
    (hW : NoCollision (poincareProd D.m (D.G * D.m0) w).1) :
    ChartHamiltonEq D
      (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
      (perturbation D b) μ w := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  cases b
  · exact chartHamiltonEq_core D μ hw _ _
      (analyticOnNhd_fFix_poincareProd D.hm hκ w ⟨hw, hW⟩).differentiableAt
      (differentiableAt_fixedHamiltonian D.G D.m0 D.m μ hW)
      (fun v hv => fixedHamiltonian_poincareProd D.hm hκ hv)
  · exact chartHamiltonEq_core D μ hw _ _
      (analyticOnNhd_fMov_poincareProd D.hm hκ w ⟨hw, hW⟩).differentiableAt
      (differentiableAt_movingHamiltonian D.G D.m0 D.m μ hW)
      (fun v hv => movingHamiltonian_poincareProd D.hm hκ hv)

/-! ### `stepP:p7:la-ham` and `bpP:p7:product-chart` -/

private theorem fast_assemble_snd (I phi p q : Vec n) :
    fast (assemble I phi p q : Phase (n + n)).2 = I := by
  funext i
  simp [fast, assemble]

private theorem hProd_eq_keplerActionHam (D : Data n) (w : Phase (n + n)) :
    hProd (D.G * D.m0) D.m w = keplerActionHam D (fast w.2) := by
  unfold keplerActionHam hProd
  rw [fast_assemble_snd]

/-- `stepP:p7:la-ham`: on `O₀ = polarDom n`, `H ∘ Ψ ∘ Θ_n = h(I) + μ f̂ ∘ Θ_n` with `I = Λ`
(`fast z.2`) for the moving (`b = true`) and the fixed (`b = false`) model, and the unperturbed
part `h ∘ Θ_n` is independent of `(ψ, R)`. -/
theorem la_ham (D : Data n) (b : Bool) (μ : ℝ) :
    (∀ z ∈ polarDom n,
      (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
          (poincareProd D.m (D.G * D.m0) (polarMap z)) =
        keplerActionHam D (fast z.2) + μ * perturbation D b (polarMap z)) ∧
    (∀ z z' : Phase (n + n), fast z.2 = fast z'.2 →
      hProd (D.G * D.m0) D.m (polarMap z) = hProd (D.G * D.m0) D.m (polarMap z')) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hfast : ∀ z : Phase (n + n), fast (polarMap z).2 = fast z.2 := fun z =>
    fast_assemble_snd _ _ _ _
  refine ⟨fun z hz => ?_, fun z z' h => ?_⟩
  · have hmem := polarMap_mapsTo n hz
    have hh : hProd (D.G * D.m0) D.m (polarMap z) = keplerActionHam D (fast z.2) := by
      rw [hProd_eq_keplerActionHam, hfast]
    rw [← hh]
    cases b
    · exact fixedHamiltonian_poincareProd D.hm hκ hmem
    · exact movingHamiltonian_poincareProd D.hm hκ hmem
  · rw [hProd_eq_keplerActionHam, hProd_eq_keplerActionHam, hfast, hfast, h]

/-- `bpP:p7:product-chart`, parts (a)–(d).  (a) `Ψ` is a real-analytic `1`-chart on `O_n`
(also as the equal-dimension chart `poincareProdCast`), `O_n` and `Ψ` are invariant under the fast
lattice, `Ψ w' = Ψ w` iff `w' = w + ((2π k, 0), 0)`, `Ψ` maps onto `𝒦⁽ⁿ⁾`, is a local analytic
diffeomorphism and induces a bijection `O_n / lattice → 𝒦⁽ⁿ⁾`.  (b) `H_Kep ∘ Ψ = h(Λ)`, `h`
independent of `λ, ξ, η`, `∂h/∂Λᵢ = νᵢ`, `∂²h/∂Λᵢ² = -3κ²mᵢ³/Λᵢ⁴ ≠ 0`, `h` analytic on
`{Λᵢ > 0}`.  (c) `H^Ψ = h + μ f̂` for both models with `f̂` independent of `μ, ε`, analytic on
`Ψ⁻¹(W)`, the field identity `DΨ X_{H^Ψ} = X_H ∘ Ψ` and the transfer of orbits.  (d) the Hamilton
equations (`pc_eq`). -/
theorem product_chart_full (D : Data n) :
    (IsChart 1 (poincareProdCast D.m (D.G * D.m0)) (poincareProdCastDom n) ∧
      AnalyticOnNhd ℝ (poincareProd D.m (D.G * D.m0)) (poincareProdDom n) ∧
      IsSymplecticOn 1 (poincareProd D.m (D.G * D.m0)) (poincareProdDom n) ∧
      (∀ w ∈ poincareProdDom n, ∀ k : Fin n → ℤ,
        w + fastShift (a := n) (b := n) k ∈ poincareProdDom n ∧
          poincareProd D.m (D.G * D.m0) (w + fastShift (a := n) (b := n) k) =
            poincareProd D.m (D.G * D.m0) w) ∧
      (∀ w ∈ poincareProdDom n, ∀ w' ∈ poincareProdDom n,
        poincareProd D.m (D.G * D.m0) w = poincareProd D.m (D.G * D.m0) w' ↔
          ∃ k : Fin n → ℤ, w' = w + fastShift (a := n) (b := n) k) ∧
      poincareProd D.m (D.G * D.m0) '' poincareProdDom n = regionProd D.m (D.G * D.m0) ∧
      (∀ w ∈ poincareProdDom n,
        ∃ φ : OpenPartialHomeomorph (Phase (n + n)) (Phase (n * 2)), w ∈ φ.source ∧
          (φ : Phase (n + n) → Phase (n * 2)) = poincareProd D.m (D.G * D.m0) ∧
          AnalyticOnNhd ℝ φ.symm φ.target) ∧
      ∃ f : Quotient (fastLatticeSetoid n) → regionProd D.m (D.G * D.m0),
        Function.Bijective f ∧
          ∀ w : poincareProdDom n, (f (Quotient.mk _ w) : Phase (n * 2)) =
            poincareProd D.m (D.G * D.m0) w) ∧
    ((∀ w ∈ poincareProdDom n,
        keplerPart (D.G * D.m0) D.m (poincareProd D.m (D.G * D.m0) w) =
          hProd (D.G * D.m0) D.m w) ∧
      (∀ w : Phase (n + n), hProd (D.G * D.m0) D.m w = keplerActionHam D (fast w.2)) ∧
      AnalyticOnNhd ℝ (keplerActionHam D) {I | ∀ i, 0 < I i} ∧
      (∀ I : Vec n, (∀ i, 0 < I i) → ∀ i,
        fderiv ℝ (keplerActionHam D) I (Pi.single i 1) = nu D I i ∧
        nu D I i = (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 3 ∧
        fderiv ℝ (fun J => nu D J i) I (Pi.single i 1) =
          -3 * (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 4 ∧
        -3 * (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 4 ≠ 0) ∧
      ∀ w ∈ poincareProdDom n,
        hamiltonianVectorField (hProd (D.G * D.m0) D.m) w = (Fin.append (nu D (fast w.2)) 0, 0)) ∧
    (∀ b : Bool,
      (∀ μ : ℝ, ∀ w ∈ poincareProdDom n,
        (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
            (poincareProd D.m (D.G * D.m0) w) =
          hProd (D.G * D.m0) D.m w + μ * perturbation D b w) ∧
      AnalyticOnNhd ℝ (perturbation D b)
        (poincareProdDom n ∩ poincareProd D.m (D.G * D.m0) ⁻¹' collisionFreeDomain n) ∧
      (∀ μ : ℝ, ∀ w ∈ poincareProdDom n, NoCollision (poincareProd D.m (D.G * D.m0) w).1 →
        fderiv ℝ (poincareProd D.m (D.G * D.m0)) w
            (hamiltonianVectorField
              ((if b then movingHamiltonian D.G D.m0 D.m μ
                else fixedHamiltonian D.G D.m0 D.m μ) ∘ poincareProd D.m (D.G * D.m0)) w) =
          hamiltonianVectorField
            (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
            (poincareProd D.m (D.G * D.m0) w)) ∧
      (∀ (μ : ℝ) (J : Set ℝ) (y : ℝ → Phase (n + n)),
        (∀ t ∈ J, y t ∈ poincareProdDom n ∧ NoCollision (poincareProd D.m (D.G * D.m0) (y t)).1) →
        (∀ t ∈ J, HasDerivAt y (hamiltonianVectorField
          ((if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ) ∘
            poincareProd D.m (D.G * D.m0)) (y t)) t) →
        ∀ t ∈ J, HasDerivAt (poincareProd D.m (D.G * D.m0) ∘ y)
          (hamiltonianVectorField
            (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
            (poincareProd D.m (D.G * D.m0) (y t))) t)) ∧
    (∀ (b : Bool) (μ : ℝ) {w : Phase (n + n)}, w ∈ poincareProdDom n →
      NoCollision (poincareProd D.m (D.G * D.m0) w).1 →
      ChartHamiltonEq D
        (if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ)
        (perturbation D b) μ w) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hpc := pc_prod D
  have hpcf := product_chart D
  refine ⟨⟨⟨analyticOnNhd_poincareProdCast D.hm hκ, poincareProdCast_symplectic D.hm hκ⟩,
    hpc.1, hpc.2.1, fun w hw k => poincareProd_lattice D.hm hκ hw k, hpc.2.2.2.1, hpc.2.2.1,
    hpc.2.2.2.2, exists_quotient_bijection D⟩,
    ⟨fun w hw => keplerPart_poincareProd D.hm hκ hw, hProd_eq_keplerActionHam D, hpcf.1,
      fun I hI i => ⟨(hpcf.2.1 I hI i).1, rfl, (hpcf.2.1 I hI i).2⟩, hpcf.2.2⟩, ?_, ?_⟩
  · intro b
    refine ⟨fun μ w hw => ?_, ?_, fun μ w hw hW => (pc_share D b μ hw hW).2, ?_⟩
    · cases b
      · exact fixedHamiltonian_poincareProd D.hm hκ hw
      · exact movingHamiltonian_poincareProd D.hm hκ hw
    · cases b
      · exact analyticOnNhd_fFix_poincareProd D.hm hκ
      · exact analyticOnNhd_fMov_poincareProd D.hm hκ
    · intro μ J y hyd hy t ht
      have hΨ : DifferentiableAt ℝ (poincareProd D.m (D.G * D.m0)) (y t) :=
        (analyticOnNhd_poincareProd D.hm hκ _ (hyd t ht).1).differentiableAt
      have h := hΨ.hasFDerivAt.comp_hasDerivAt t (hy t ht)
      rw [(pc_share D b μ (hyd t ht).1 (hyd t ht).2).2] at h
      exact h
  · intro b μ w hw hW
    exact pc_eq D b μ hw hW

end SecularForm

end KAM.Planetary

end
