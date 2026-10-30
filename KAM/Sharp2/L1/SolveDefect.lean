/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Solve
public import KAM.Sharp2.L1.NormsCauchy
public import KAM.Sharp2.Geometry
public import KAM.Apost.Exactness
public import KAM.Apost.Periodicity
public import KAM.Apost.Correction
public import KAM.Strip.Periodic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Lagrangian defect from `u = 𝓡ηᴺ` (package B10b)

Blueprint `bp:p2s2l1:defect` of `blueprint/parts/p2s2-l1hybrid.tex`.

* `lagrangeMat_eq_neg_antisymm`: `Ω_K = -(Du - (Du)ᵀ)` on `T_{r-δ}` with `u = 𝓡ηᴺ`. Both sides are
    holomorphic,
  periodic and of zero average (exactness, `KAM.Apost.exactness`; derivatives of periodic maps), and
  `∂_ω Ω_K = -(Dηᴺ - (Dηᴺ)ᵀ)` (the sign of `KAM.Sharp2.fderiv_lagrangeMat_eq_etaN`) while
  `∂_ω Du = D ∂_ω u = Dηᴺ` (symmetry of the second derivative,
      `KAM.fderiv_apply_comm_of_differentiableOn`).
  The difference is killed by the a-priori clause of `KAM.Apost.cohomological` with `H = 0`. The
      data `ηᴺ` is
  bounded on every narrower strip (`KAM.periodic_bounded`), so the sup solve applies on `T_{r-δ/4}`.
* `norm_lagrangeMat_le_l1`: `|Ω_K| ≤ n Γ_∞(ω, δ) ε¹_N/(e δ')` on `T_{r-δ-δ'}`, from the identity,
    the ℓ¹ solve
  (`l1_cohR`) and the antisymmetric row-sum Cauchy estimate (`L1Vec.norm_jac_antisymm_le`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-! ### The Jacobian as a linear image of the derivative -/

/-- `L ↦ (L e_j)_i`. -/
def jacCLM {ι : Type*} [Fintype ι] : ((Fin n → ℂ) →L[ℂ] (ι → ℂ)) →L[ℂ] Matrix ι (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => Matrix.of fun i j => L (Pi.single j 1) i
      map_add' := fun L L' => by ext i j; simp
      map_smul' := fun c L => by ext i j; simp }

theorem jacCLM_apply {ι : Type*} [Fintype ι] (L : (Fin n → ℂ) →L[ℂ] (ι → ℂ)) :
    jacCLM L = Matrix.of fun i j => L (Pi.single j 1) i := rfl

theorem jac_eq_jacCLM {ι : Type*} [Fintype ι] (f : (Fin n → ℂ) → ι → ℂ) (θ : Fin n → ℂ) :
    jac f θ = jacCLM (fderiv ℂ f θ) := rfl

/-- The Jacobian of a holomorphic map on an open set is holomorphic. -/
theorem differentiableOn_jac {ι : Type*} [Fintype ι] {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ι → ℂ} (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (jac f) U := by
  have h := jacCLM.differentiable.comp_differentiableOn (differentiableOn_fderiv_of_isOpen hU hf)
  exact h.congr fun θ _ => jac_eq_jacCLM f θ

/-- A component of the derivative is the derivative of the component. -/
theorem fderiv_component {ι : Type*} [Fintype ι] {g : (Fin n → ℂ) → ι → ℂ} {θ : Fin n → ℂ}
    (hg : DifferentiableAt ℂ g θ) (i : ι) (w : Fin n → ℂ) :
    fderiv ℂ (fun z => g z i) θ w = fderiv ℂ g θ w i := by
  have h1 : fderiv ℂ (fun z => g z i) θ =
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp (fderiv ℂ g θ) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp θ
      hg.hasFDerivAt).fderiv
  rw [h1]
  rfl

/-- `∂_v (Df) = D(∂_v f)` (symmetry of the second derivative of a holomorphic map). -/
theorem fderiv_jac_apply {ι : Type*} [Fintype ι] {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ι → ℂ} (hf : DifferentiableOn ℂ f U) {θ : Fin n → ℂ} (hθ : θ ∈ U)
    (v : Fin n → ℂ) :
    fderiv ℂ (jac f) θ v = Matrix.of fun i j => fderiv ℂ (fun x => fderiv ℂ f x v) θ (Pi.single j
        1) i := by
  have hg : DifferentiableAt ℂ (fderiv ℂ f) θ :=
    (differentiableOn_fderiv_of_isOpen hU hf).differentiableAt (hU.mem_nhds hθ)
  have h1 : fderiv ℂ (jac f) θ = jacCLM.comp (fderiv ℂ (fderiv ℂ f) θ) := by
    have hj : jac f = fun x => jacCLM (fderiv ℂ f x) := funext (jac_eq_jacCLM f)
    rw [hj]
    exact (jacCLM.hasFDerivAt.comp θ hg.hasFDerivAt).fderiv
  have h2 : ∀ j, fderiv ℂ (fderiv ℂ f) θ v (Pi.single j 1) =
      fderiv ℂ (fun x => fderiv ℂ f x (Pi.single j 1)) θ v := fun j => by
    rw [fderiv_clm_apply hg (differentiableAt_const _)]
    simp
  rw [h1, ContinuousLinearMap.comp_apply, jacCLM_apply]
  ext i j
  simp only [Matrix.of_apply]
  rw [h2 j, fderiv_apply_comm_of_differentiableOn hU hf hθ v (Pi.single j 1)]

/-! ### The identity (`bp:p2s2l1:defect`) -/

/-- Blueprint `bp:p2s2l1:defect`, identity: `Ω_K = -(Du - (Du)ᵀ)` with `u = 𝓡ηᴺ` (sign of
`KAM.Sharp2.fderiv_lagrangeMat_eq_etaN`). -/
theorem lagrangeMat_eq_neg_antisymm {τ M σK σB σT γ r δ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n →
        ℂ)}
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hδ : 0 < δ) (hδr : δ < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (_hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    ∀ θ ∈ complexStrip n (r - δ), lagrangeMat K θ =
      -(jac (cohR ω (etaN h K ω)) θ - (jac (cohR ω (etaN h K ω)) θ)ᵀ) := by
  have hr : 0 < r := hδ.trans hδr
  have hr₁ : 0 < r - δ / 4 := by linarith
  have hr₂ : 0 < r - δ / 2 := by linarith
  have hsub₁ : complexStrip n (r - δ / 4) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hsub₂ : complexStrip n (r - δ / 2) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  -- the data `ηᴺ`
  have hη : DifferentiableOn ℂ (etaN h K ω) (complexStrip n r) :=
    KAM.Apost.Exactness.differentiableOn_etaN hS hK hK𝔅
  have hηp : IsPeriodicOn (etaN h K ω) r :=
    KAM.Apost.Correction.periodic_etaN (KAM.Apost.periodic_eta hS hK𝔅 hKp)
  have hη0 : avg (etaN h K ω) = 0 := (KAM.Apost.exactness hS hr hK hKp hK𝔅).2
  obtain ⟨H, hH⟩ := KAM.periodic_bounded hη hηp (show r - δ / 4 < r by linarith)
  -- the sup solve on `T_{r-δ/4}` with loss `δ/4`
  obtain ⟨hvec, -⟩ := KAM.Apost.cohomological hS hr₁ (by positivity : (0 : ℝ) < δ / 4)
    (by linarith : δ / 4 < r - δ / 4)
  obtain ⟨hu, hup, -, hueq, -, -, -⟩ := hvec (etaN h K ω) H (hη.mono hsub₁)
    (fun i z hz => hηp i z (hsub₁ hz)) hH hη0
  have e₁ : r - δ / 4 - δ / 4 = r - δ / 2 := by ring
  rw [e₁] at hu hup hueq
  set u := cohR ω (etaN h K ω) with hudef
  -- the difference `D = Ω_K + (Du - (Du)ᵀ)`
  have hΩ : DifferentiableOn ℂ (lagrangeMat K) (complexStrip n r) :=
    KAM.Apost.Exactness.differentiableOn_lagrangeMat hK
  have hJ : DifferentiableOn ℂ (jac u) (complexStrip n (r - δ / 2)) :=
    differentiableOn_jac (isOpen_complexStrip n _) hu
  set D : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ := fun θ => lagrangeMat K θ + (jac u θ - (jac u
      θ)ᵀ) with hD
  have hDd : DifferentiableOn ℂ D (complexStrip n (r - δ / 2)) :=
    (hΩ.mono hsub₂).add (hJ.sub hJ.matrix_transpose)
  -- periodicity
  have hJp : IsPeriodicOn (jac u) (r - δ / 2) := fun i z hz => by
    rw [jac_eq_jacCLM, jac_eq_jacCLM, KAM.Apost.isPeriodicOn_fderiv_of_shift (fun _ => 0)
      (fun i z hz => by rw [hup i z hz, add_zero]) i z hz]
  have hDp : IsPeriodicOn D (r - δ / 2) := fun i z hz => by
    simp only [hD, KAM.Apost.periodic_lagrangeMat hKp i z (hsub₂ hz), hJp i z hz]
  -- zero average
  have hui : ∀ l, DifferentiableOn ℂ (fun z => u z l) (complexStrip n (r - δ / 2)) := fun l =>
    differentiableOn_pi.mp hu l
  have huip : ∀ l, IsPeriodicOn (fun z => u z l) (r - δ / 2) := fun l k z hz =>
    congrFun (hup k z hz) l
  have hjac : ∀ a b (x : Fin n → ℝ), jac u (fun l => (x l : ℂ)) a b =
      fderiv ℂ (fun z => u z a) (fun l => (x l : ℂ)) (Pi.single b 1) := fun a b x =>
    (fderiv_component (hu.differentiableAt ((isOpen_complexStrip n _).mem_nhds
      (ofReal_mem_complexStrip hr₂ x))) a _).symm
  have hcJ : ∀ a b, Continuous (fun x : Fin n → ℝ => jac u (fun l => (x l : ℂ)) a b) := fun a b =>
      by
    simp only [hjac]
    exact KAM.Apost.Exactness.continuous_fderiv_apply_real hr₂ (hui a) _
  have hintJ : ∀ a b, ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      jac u (fun l => (x l : ℂ)) a b = 0 := fun a b => by
    simp only [hjac]
    exact KAM.Apost.Exactness.integral_fderiv_apply_eq_zero hr₂ (hui a) (huip a) _
  have hcΩ : Continuous (fun x : Fin n → ℝ => lagrangeMat K (fun l => (x l : ℂ))) :=
    KAM.Apost.Exactness.continuous_real_of_differentiableOn hr hΩ
  have hD0 : avg D = 0 := by
    ext i j
    have hcD : Continuous (fun x : Fin n → ℝ => D fun l => (x l : ℂ)) :=
      KAM.Apost.Exactness.continuous_real_of_differentiableOn hr₂ hDd
    have hΩij : ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        lagrangeMat K (fun l => (x l : ℂ)) i j = 0 := by
      have h0 := torusAverage_matrix_apply hcΩ i j
      rw [show torusAverage (fun x : Fin n → ℝ => lagrangeMat K (fun l => (x l : ℂ))) = 0 from
        KAM.Apost.Exactness.avg_lagrangeMat hr hK hKp] at h0
      simpa using h0.symm
    have hcΩe : Continuous (fun x : Fin n → ℝ => lagrangeMat K (fun l => (x l : ℂ)) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hcΩ)
    refine (torusAverage_matrix_apply hcD i j).trans ?_
    simp only [hD, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.zero_apply]
    have hsplit : ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        (lagrangeMat K (fun l => (x l : ℂ)) i j +
          (jac u (fun l => (x l : ℂ)) i j - jac u (fun l => (x l : ℂ)) j i)) =
        (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), lagrangeMat K (fun l => (x l
            : ℂ)) i j) +
          ((∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), jac u (fun l => (x l : ℂ))
              i j) -
            ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), jac u (fun l => (x l : ℂ))
                j i) := by
      rw [← MeasureTheory.integral_sub (integrableOn_unitCube_of_continuous (hcJ i j))
          (integrableOn_unitCube_of_continuous (hcJ j i))]
      exact MeasureTheory.integral_add (integrableOn_unitCube_of_continuous hcΩe)
        (integrableOn_unitCube_of_continuous ((hcJ i j).sub (hcJ j i)))
    rw [hsplit, hΩij, hintJ, hintJ]
    simp
  -- `∂_ω D = 0`
  have hDω : ∀ θ ∈ complexStrip n (r - δ / 2), fderiv ℂ D θ (fun l => (ω l : ℂ)) = 0 := by
    intro θ hθ
    have hθr : θ ∈ complexStrip n r := hsub₂ hθ
    have hΩθ : DifferentiableAt ℂ (lagrangeMat K) θ :=
      hΩ.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
    have hJθ : DifferentiableAt ℂ (jac u) θ :=
      hJ.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ)
    have hJω : fderiv ℂ (jac u) θ (fun l => (ω l : ℂ)) = etaNDeriv h K ω θ := by
      rw [fderiv_jac_apply (isOpen_complexStrip n _) hu hθ]
      have heq : fderiv ℂ (fun x => fderiv ℂ u x (fun l => (ω l : ℂ))) θ = fderiv ℂ (etaN h K ω) θ
          := by
        refine Filter.EventuallyEq.fderiv_eq ?_
        filter_upwards [(isOpen_complexStrip n _).mem_nhds hθ] with z hz
        exact hueq z hz
      rw [heq]
      rfl
    have hfd : HasFDerivAt D (fderiv ℂ (lagrangeMat K) θ + (fderiv ℂ (jac u) θ -
        (matTransposeCLM (l := Fin n) (m := Fin n)).comp (fderiv ℂ (jac u) θ))) θ :=
      hΩθ.hasFDerivAt.add (hJθ.hasFDerivAt.sub hJθ.hasFDerivAt.matrix_transpose)
    rw [hfd.fderiv]
    simp only [_root_.add_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply,
        matTransposeCLM_apply]
    rw [fderiv_lagrangeMat_eq_etaN hS hK hK𝔅 hθr, hJω]
    abel
  -- the a-priori clause with `H = 0` on `T_{r-δ/2}`, loss `δ/2`
  obtain ⟨-, hmat⟩ := KAM.Apost.cohomological hS hr₂ (by positivity : (0 : ℝ) < δ / 2)
    (by linarith : δ / 2 < r - δ / 2)
  have hb := hmat D 0 hDd hDp hD0 (fun θ hθ => by rw [hDω θ hθ, norm_zero])
  intro θ hθ
  have e₂ : r - δ / 2 - δ / 2 = r - δ := by ring
  have hθ' : θ ∈ complexStrip n (r - δ / 2 - δ / 2) := by rw [e₂]; exact hθ
  have h0 : D θ = 0 := norm_le_zero_iff.mp (by simpa using hb θ hθ')
  simp only [hD] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- Blueprint `bp:p2s2l1:defect`, bound: `|Ω_K| ≤ n Γ_∞(ω, δ) ε¹_N/(e δ')` on `T_{r-δ-δ'}`. -/
theorem norm_lagrangeMat_le_l1 {τ M σK σB σT γ r δ δ' εN : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n →
        ℂ)}
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hδ : 0 < δ) (hδ' : 0 < δ') (hδr : δ + δ' < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K
        θ).det)
    (hηN : L1Vec r (etaN h K ω) εN) :
    ∀ θ ∈ complexStrip n (r - δ - δ'), ‖lagrangeMat K θ‖ ≤ n / (Real.exp 1 * δ') * smallDivisorSup
        ω δ * εN := by
  intro θ hθ
  have hr : 0 < r := by linarith
  have hδr' : δ < r := by linarith
  have hθ1 : θ ∈ complexStrip n (r - δ) := Triangular.strip_mono (by linarith) hθ
  rw [lagrangeMat_eq_neg_antisymm hS hδ hδr' hK hKp hK𝔅 hG θ hθ1, norm_neg]
  have hη : DifferentiableOn ℂ (etaN h K ω) (complexStrip n r) :=
    KAM.Apost.Exactness.differentiableOn_etaN hS hK hK𝔅
  have hηp : IsPeriodicOn (etaN h K ω) r :=
    KAM.Apost.Correction.periodic_etaN (KAM.Apost.periodic_eta hS hK𝔅 hKp)
  have hη0 : avg (etaN h K ω) = 0 := (KAM.Apost.exactness hS hr hK hKp hK𝔅).2
  have hτ := KAM.Apost.cohomological_tau_nonneg hS
  obtain ⟨hu1, -⟩ := l1_cohR hS.dio hS.gamma_pos hτ hδ hδr' hη hηp hη0 hηN
  have hu := differentiableOn_cohR_l1 hS.dio hS.gamma_pos hτ hδ hδr' hηN
  have hb := L1Vec.norm_jac_antisymm_le hδ' (by linarith : δ' < r - δ) hu
    (isPeriodicOn_cohR ω (etaN h K ω) (r - δ)) hu1 θ hθ
  calc ‖jac (cohR ω (etaN h K ω)) θ - (jac (cohR ω (etaN h K ω)) θ)ᵀ‖
      ≤ n * (smallDivisorSup ω δ * εN) / (Real.exp 1 * δ') := hb
    _ = n / (Real.exp 1 * δ') * smallDivisorSup ω δ * εN := by ring

end KAM.Sharp2.L1

end
