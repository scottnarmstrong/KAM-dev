/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Periodicity
public import KAM.Apost.Tools
public import KAM.Apost.Frame
public import KAM.Apost.Identities

/-!
# Exactness: two vanishing averages

Blueprint Part 2, Lemma `bp:p2:exactness` (`KAM.Apost.exactness`). Let `K` be holomorphic and
primary on `T_r` with `K(T_r) ⊆ 𝔅`. Then `⟨Ω_K⟩ = 0` and `⟨Lᵀ Ω₀ E⟩ = ⟨η^ᴺ⟩ = 0`. The second
average needs no inverse of the Gram matrix: `ηᴺ := Lᵀ Ω₀ E` is defined without one.

The proof follows the blueprint (steps `step:p2:ex-curl`, `step:p2:ex-avg-omega`,
`step:p2:ex-gradient`, `step:p2:ex-avg-eta`); all helper lemmas live in the namespace
`KAM.Apost.Exactness`.

* `step:p2:ex-curl`: with the action forms `f_j = (K^I)ᵀ ∂_{θ_j} K^θ` (`actionForm`), the entries of
  `Ω_K` are `∂_{θ_i} f_j - ∂_{θ_j} f_i` (`curl_actionForm`). This uses the symmetry of the mixed
  second derivatives of the holomorphic `K` (`fderiv_tangentMat_symm`).
* `step:p2:ex-avg-omega`: the `f_j` are holomorphic and periodic on `T_r`
  (`differentiableOn_actionForm`, `periodic_actionForm`), so every `∂_{θ_i} f_j` has zero average
  (`KAM.Apost.Tools.torusAverage_fderiv_apply_eq_zero`); hence `avg_lagrangeMat`.
* `step:p2:ex-gradient`: `etaN_apply` is `Lᵀ Ω₀ E = (D(h ∘ K))ᵀ - Ω_K ω`, from `Ω₀ X_h = (Dh)ᵀ`
  (`KAM.Apost.sumVec_omegaZero_ham`).
* `step:p2:ex-avg-eta`: `h ∘ K` is holomorphic and periodic (`periodic_h_comp_K`), and
  `⟨Ω_K ω⟩ = ⟨Ω_K⟩ ω = 0`; hence `avg_etaN`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Apost

open KAM.Torus

namespace Exactness

/-! ### Step `step:p2:ex-curl`: `Ω_K` is a curl -/

section Curl

variable {n : ℕ} {r : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- The action form `f_j = (K^I)ᵀ ∂_{θ_j} K^θ`, written with the entries of `L = DK`. -/
def actionForm (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (j : Fin n) (θ : Fin n → ℂ) : ℂ :=
  ∑ l, sumVec n (K θ) (Sum.inr l) * tangentMat K θ (Sum.inl l) j

/-- The entries of `Ω_K = Lᵀ Ω₀ L`:
`(Ω_K)_{ij} = ∂_{θ_i} K^I · ∂_{θ_j} K^θ - ∂_{θ_i} K^θ · ∂_{θ_j} K^I`. -/
theorem lagrangeMat_apply (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (i j : Fin n) :
    lagrangeMat K θ i j = ∑ l, (tangentMat K θ (Sum.inr l) i * tangentMat K θ (Sum.inl l) j -
      tangentMat K θ (Sum.inl l) i * tangentMat K θ (Sum.inr l) j) := by
  rw [lagrangeMat, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.transpose_apply, omegaZeroMatrix_mul_apply_inl, omegaZeroMatrix_mul_apply_inr,
    Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  ring

/-- `K^I` and the entries of `L` are holomorphic on `T_r`; hence so is the action form. -/
theorem differentiableOn_actionForm (hK : DifferentiableOn ℂ K (complexStrip n r)) (j : Fin n) :
    DifferentiableOn ℂ (actionForm K j) (complexStrip n r) := by
  have hL := (differentiableOn_matrix_iff_entries.1 (differentiableOn_tangentMat hK))
  have hs : ∀ s, DifferentiableOn ℂ (fun θ => sumVec n (K θ) s) (complexStrip n r) := fun s =>
    differentiableOn_pi.1 ((sumVecIso n).differentiable.comp_differentiableOn hK) s
  show DifferentiableOn ℂ (fun θ => ∑ l, sumVec n (K θ) (Sum.inr l) *
    tangentMat K θ (Sum.inl l) j) _
  exact DifferentiableOn.fun_sum fun l _ => (hs _).mul (hL _ _)

/-- The action form is `1`-periodic when `K` is primary. -/
theorem periodic_actionForm (hKp : IsPrimaryOnStrip K r) (j : Fin n) :
    IsPeriodicOn (actionForm K j) r := fun i z hz => by
  have hK2 : ∀ l, sumVec n (K (z + Pi.single i 1)) (Sum.inr l) = sumVec n (K z) (Sum.inr l) :=
    fun l => by
      rw [primary_coordinatewise hKp i hz]
      simp [sumVec_apply]
  simp only [actionForm, hK2, periodic_tangentMat hKp i z hz]

/-- The mixed second derivatives of a holomorphic `K` commute:
`∂_i L_{sj} = ∂_j L_{si}`. -/
theorem fderiv_tangentMat_symm (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (i j : Fin n) (s : Fin n ⊕ Fin n) :
    fderiv ℂ (tangentMat K) θ (Pi.single i 1) s j =
      fderiv ℂ (tangentMat K) θ (Pi.single j 1) s i := by
  rw [Identities.fderiv_tangentMat_apply hK hθ, Identities.fderiv_tangentMat_apply hK hθ,
    fderiv_apply_comm_of_differentiableOn (isOpen_complexStrip n r) hK hθ (Pi.single i 1)
      (Pi.single j 1)]

/-- Product rule for the action form: `D f_j · v = ∑_l (D K^I_l v) L_{lj} + K^I_l (D L_{lj} v)`. -/
theorem fderiv_actionForm (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (j : Fin n) (v : Fin n → ℂ) :
    fderiv ℂ (actionForm K j) θ v = ∑ l, (sumVec n (fderiv ℂ K θ v) (Sum.inr l) *
      tangentMat K θ (Sum.inl l) j + sumVec n (K θ) (Sum.inr l) *
        fderiv ℂ (tangentMat K) θ v (Sum.inl l) j) := by
  have hKd : DifferentiableAt ℂ K θ := hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hLd : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hs : ∀ s, DifferentiableAt ℂ (fun y => sumVec n (K y) s) θ := fun s =>
    differentiableAt_pi.1 ((sumVecIso n).differentiable.differentiableAt.comp θ hKd) s
  have hterm : ∀ l ∈ Finset.univ, DifferentiableAt ℂ
      (fun y => sumVec n (K y) (Sum.inr l) * tangentMat K y (Sum.inl l) j) θ :=
    fun l _ => (hs _).mul (hLd.matrix_apply _ _)
  have hfun : actionForm K j =
      fun y => ∑ l, sumVec n (K y) (Sum.inr l) * tangentMat K y (Sum.inl l) j := rfl
  rw [hfun, fderiv_fun_sum hterm]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_fun_mul (hs _) (hLd.matrix_apply _ _)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_sumVec_coord hKd, fderiv_matrix_apply hLd]
  ring

/-- Step `step:p2:ex-curl`: `(Ω_K)_{ij} = ∂_{θ_i} f_j - ∂_{θ_j} f_i`. -/
theorem curl_actionForm (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (i j : Fin n) :
    fderiv ℂ (actionForm K j) θ (Pi.single i 1) - fderiv ℂ (actionForm K i) θ (Pi.single j 1) =
      lagrangeMat K θ i j := by
  rw [fderiv_actionForm hK hθ, fderiv_actionForm hK hθ, lagrangeMat_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : sumVec n (fderiv ℂ K θ (Pi.single i 1)) (Sum.inr l) = tangentMat K θ (Sum.inr l) i :=
    (tangentMat_apply K θ _ i).symm
  have h2 : sumVec n (fderiv ℂ K θ (Pi.single j 1)) (Sum.inr l) = tangentMat K θ (Sum.inr l) j :=
    (tangentMat_apply K θ _ j).symm
  rw [h1, h2, fderiv_tangentMat_symm hK hθ i j (Sum.inl l)]
  ring

end Curl

/-! ### Step `step:p2:ex-avg-omega`: `⟨Ω_K⟩ = 0` -/

section AvgOmega

variable {n : ℕ} {r : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- The real embedding `ℝⁿ → ℂⁿ` is continuous. -/
theorem continuous_ofReal_vec : Continuous (fun x : Fin n → ℝ => fun i => (x i : ℂ)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

/-- A function holomorphic on `T_r` is continuous at the real points. -/
theorem continuous_real_of_differentiableOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : (Fin n → ℂ) → F} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (complexStrip n r)) :
    Continuous (fun x : Fin n → ℝ => f (fun i => (x i : ℂ))) :=
  hf.continuousOn.comp_continuous continuous_ofReal_vec fun x => ofReal_mem_complexStrip hr x

/-- The integral of a directional derivative of a holomorphic periodic function over the cube
vanishes (`bp:p2:averages` (b), unfolded). -/
theorem integral_fderiv_apply_eq_zero (hr : 0 < r) {v : (Fin n → ℂ) → ℂ}
    (hv : DifferentiableOn ℂ v (complexStrip n r)) (hp : IsPeriodicOn v r) (w : Fin n → ℂ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      fderiv ℂ v (fun i => (x i : ℂ)) w = 0 :=
  Tools.torusAverage_fderiv_apply_eq_zero hr hv hp w

/-- The integrand `x ↦ fderiv v x w` of a holomorphic function is continuous on `ℝⁿ`. -/
theorem continuous_fderiv_apply_real (hr : 0 < r) {v : (Fin n → ℂ) → ℂ}
    (hv : DifferentiableOn ℂ v (complexStrip n r)) (w : Fin n → ℂ) :
    Continuous (fun x : Fin n → ℝ => fderiv ℂ v (fun i => (x i : ℂ)) w) :=
  (continuous_fderiv_real_of_holomorphic hr hv).clm_apply continuous_const

/-- `Ω_K` is holomorphic on `T_r` when `K` is. -/
theorem differentiableOn_lagrangeMat (hK : DifferentiableOn ℂ K (complexStrip n r)) :
    DifferentiableOn ℂ (lagrangeMat K) (complexStrip n r) := by
  have hL := differentiableOn_tangentMat hK
  exact (hL.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hL

/-- Step `step:p2:ex-avg-omega`: the average of `Ω_K` vanishes, since every entry is a
difference of derivatives of periodic holomorphic functions. -/
theorem avg_lagrangeMat (hr : 0 < r) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) : avg (lagrangeMat K) = 0 := by
  ext i j
  refine (torusAverage_matrix_apply (continuous_real_of_differentiableOn hr
    (differentiableOn_lagrangeMat hK)) i j).trans ?_
  have hint : (fun x : Fin n → ℝ => lagrangeMat K (fun l => (x l : ℂ)) i j) = fun x =>
      fderiv ℂ (actionForm K j) (fun l => (x l : ℂ)) (Pi.single i 1) -
        fderiv ℂ (actionForm K i) (fun l => (x l : ℂ)) (Pi.single j 1) :=
    funext fun x => (curl_actionForm hK (ofReal_mem_complexStrip hr x) i j).symm
  simp only [Matrix.zero_apply]
  rw [hint, integral_sub
    (integrableOn_unitCube_of_continuous (continuous_fderiv_apply_real hr
      (differentiableOn_actionForm hK j) _))
    (integrableOn_unitCube_of_continuous (continuous_fderiv_apply_real hr
      (differentiableOn_actionForm hK i) _)),
    integral_fderiv_apply_eq_zero hr (differentiableOn_actionForm hK j)
      (periodic_actionForm hKp j),
    integral_fderiv_apply_eq_zero hr (differentiableOn_actionForm hK i)
      (periodic_actionForm hKp i), sub_zero]

end AvgOmega

/-! ### Steps `step:p2:ex-gradient`, `step:p2:ex-avg-eta`: `⟨ηᴺ⟩ = 0` -/

section AvgEta

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ} {r : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `Lᵀ Ω₀ X_h(K) = (D(h ∘ K))ᵀ`: the entry `j` of `Lᵀ Ω₀ sumVec (X_h(Kθ))` is `∂_{θ_j}(h ∘ K)`.
This is `Ω₀ X_h = (Dh)ᵀ` (`KAM.Apost.hamiltonian`(d)) together with the chain rule. -/
theorem transpose_mul_omegaZero_ham (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hθ : θ ∈ complexStrip n r) (j : Fin n) :
    (((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (hamiltonianVectorFieldℂ h (K θ))) j =
      fderiv ℂ (fun y => h (K y)) θ (Pi.single j 1) := by
  have hKd : DifferentiableAt ℂ K θ := hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hhd : DifferentiableAt ℂ h (K θ) := hS.holo.differentiableAt (hS.isOpen.mem_nhds (hK𝔅 θ hθ))
  have hchain : fderiv ℂ (fun y => h (K y)) θ = (fderiv ℂ h (K θ)).comp (fderiv ℂ K θ) :=
    (hhd.hasFDerivAt.comp θ hKd.hasFDerivAt).fderiv
  have hcol : (sumVec n).symm (fun s => tangentMat K θ s j) = fderiv ℂ K θ (Pi.single j 1) := by
    have : (fun s => tangentMat K θ s j) = sumVec n (fderiv ℂ K θ (Pi.single j 1)) :=
      funext fun s => tangentMat_apply K θ s j
    rw [this, sumVec_symm_apply_sumVec]
  rw [hchain, ContinuousLinearMap.comp_apply, ← hcol, ← Matrix.mulVec_mulVec]
  rw [← sumVec_omegaZero, sumVec_omegaZero_ham]
  conv_rhs => rw [pi_eq_sum_univ' (fun s => tangentMat K θ s j)]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, map_sum, map_smul, smul_eq_mul]

/-- Step `step:p2:ex-gradient`: `Lᵀ Ω₀ E = (D(h ∘ K))ᵀ - Ω_K ω`. -/
theorem etaN_apply (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hθ : θ ∈ complexStrip n r) (j : Fin n) :
    etaN h K ω θ j = fderiv ℂ (fun y => h (K y)) θ (Pi.single j 1) -
      ∑ l, lagrangeMat K θ j l * (ω l : ℂ) := by
  have hlag : ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (tangentMat K θ *ᵥ fun l => (ω l : ℂ)) =
      lagrangeMat K θ *ᵥ fun l => (ω l : ℂ) := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [etaN, sumVec_invarianceError, Matrix.mulVec_sub, hlag, Pi.sub_apply,
    transpose_mul_omegaZero_ham hS hK hK𝔅 hθ j]
  rfl

/-- The function `θ ↦ Lᵀ Ω₀ E` is holomorphic on `T_r`. -/
theorem differentiableOn_etaN (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) :
    DifferentiableOn ℂ (etaN h K ω) (complexStrip n r) := by
  have hE := FrameAux.differentiableOn_invarianceError hS hK hK𝔅
  have hL := differentiableOn_tangentMat hK
  exact (hL.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mulVec
    ((sumVecIso n).differentiable.comp_differentiableOn hE)

/-- Step `step:p2:ex-avg-eta`: the average of `ηᴺ = Lᵀ Ω₀ E` vanishes. -/
theorem avg_etaN (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) : avg (etaN h K ω) = 0 := by
  ext j
  have hcont : Continuous (fun x : Fin n → ℝ => etaN h K ω (fun i => (x i : ℂ))) :=
    continuous_real_of_differentiableOn hr (differentiableOn_etaN hS hK hK𝔅)
  have hhK : DifferentiableOn ℂ (fun y => h (K y)) (complexStrip n r) :=
    hS.holo.comp hK hK𝔅
  have hΩ : Continuous (fun x : Fin n → ℝ => lagrangeMat K (fun i => (x i : ℂ))) :=
    continuous_real_of_differentiableOn hr (differentiableOn_lagrangeMat hK)
  have hΩent : ∀ l, Continuous (fun x : Fin n → ℝ =>
      lagrangeMat K (fun i => (x i : ℂ)) j l * (ω l : ℂ)) := fun l =>
    ((continuous_apply l).comp ((continuous_apply j).comp hΩ)).mul continuous_const
  refine (Tools.torusAverage_vector_apply hcont j).trans ?_
  have hint : (fun x : Fin n → ℝ => etaN h K ω (fun i => (x i : ℂ)) j) = fun x =>
      fderiv ℂ (fun y => h (K y)) (fun i => (x i : ℂ)) (Pi.single j 1) -
        ∑ l, lagrangeMat K (fun i => (x i : ℂ)) j l * (ω l : ℂ) :=
    funext fun x => etaN_apply hS hK hK𝔅 (ofReal_mem_complexStrip hr x) j
  have hsum : ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      ∑ l, lagrangeMat K (fun i => (x i : ℂ)) j l * (ω l : ℂ) = 0 := by
    rw [integral_finsetSum _ fun l _ => integrableOn_unitCube_of_continuous (hΩent l)]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_mul_const]
    have hl := congrFun (congrFun (avg_lagrangeMat hr hK hKp) j) l
    have hl' := (torusAverage_matrix_apply hΩ j l).symm.trans hl
    rw [show (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      lagrangeMat K (fun i => (x i : ℂ)) j l) = 0 from hl', zero_mul]
  simp only [Pi.zero_apply]
  rw [hint, integral_sub
    (integrableOn_unitCube_of_continuous (continuous_fderiv_apply_real hr hhK _))
    (integrable_finsetSum _ fun l _ => integrableOn_unitCube_of_continuous (hΩent l)),
    integral_fderiv_apply_eq_zero hr hhK (periodic_h_comp_K hS hK𝔅 hKp) _, hsum, sub_zero]

end AvgEta

end Exactness

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2:exactness`: `⟨Ω_K⟩ = 0` and `⟨Lᵀ Ω₀ E⟩ = ⟨ηᴺ⟩ = 0`. -/
theorem exactness (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) :
    avg (lagrangeMat K) = 0 ∧ avg (etaN h K ω) = 0 :=
  ⟨Exactness.avg_lagrangeMat hr hK hKp, Exactness.avg_etaN hS hr hK hKp hK𝔅⟩

end KAM.Apost

end
