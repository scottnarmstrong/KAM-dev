/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Standing
public import KAM.Torus.FrozenAgreement
import KAM.Strip.RealRestriction
import KAM.Strip.Limits
import KAM.Strip.Taylor
public import KAM.Head.TorsionRegularGeneral

/-!
# The Hamiltonian vector field

Blueprint Part 2, Lemma `bp:p2:hamiltonian` (`KAM.Apost.hamiltonian`). Under the standing
assumption `KAM.Apost.Standing`, with `X_h = KAM.hamiltonianVectorFieldℂ h`:

* (a) `X_h` and `DX_h` are holomorphic on `𝔅`, and `‖D (DX_h)‖ = ‖D²X_h‖ ≤ M`;
* (b) `X_h` and `DX_h` are invariant under `z ↦ z + (k, 0)`, `k ∈ ℤⁿ`;
* (c) `X_h(z)` and `DX_h(z)` are real at the real points of `𝔅` (`DX_h` as the real entries of
  `KAM.Torus.sqMat`);
* (d) `Ω₀ X_h = (Dh)ᵀ`, `Ω₀ DX_h` is symmetric, and `DX_hᵀ Ω₀ + Ω₀ DX_h = 0`;
* (e) `‖DX_h(z + w) - DX_h(z)‖ ≤ M ‖w‖` and `‖X_h(z + w) - X_h(z) - DX_h(z) w‖ ≤ M ‖w‖²` whenever
  `B_β(z) ⊆ 𝔅` and `‖w‖ < β`.

Each item is a separate lemma, assembled in `KAM.Apost.hamiltonian`. The generic lemmas
`KAM.Apost.fderiv_add_right_eq_of_eventually` (translation invariance up to a constant passes to
the derivative) and `KAM.Apost.im_fderiv_eq_zero_of_real_line` (the derivative of a function real
along a real line is real) are reused by `KAM/Apost/Periodicity.lean`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Apost

open KAM.Torus

/-! ### Generic lemmas -/

/-- If `f (y + a) = f y + c` near `z`, then `Df (z + a) = Df z`. -/
theorem fderiv_add_right_eq_of_eventually {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {a : E} {c : F}
    {z : E} (hf : ∀ᶠ y in 𝓝 z, f (y + a) = f y + c) : fderiv ℂ f (z + a) = fderiv ℂ f z := by
  have h1 : fderiv ℂ (fun y => f (y + a)) z = fderiv ℂ f (z + a) := fderiv_comp_add_right a
  have h2 : fderiv ℂ (fun y => f y + c) z = fderiv ℂ f z := fderiv_add_const c
  rw [← h1, ← h2]
  exact Filter.EventuallyEq.fderiv_eq hf

/-- A complex derivative is real along a real line: if `f` is differentiable at `x` and
`f (x + t v)` is real for all small real `t`, then `Df x v` is real (a limit of real difference
quotients). -/
theorem im_fderiv_eq_zero_of_real_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x)
    (hreal : ∀ᶠ t : ℝ in 𝓝 0, (f (x + (t : ℂ) • v)).im = 0) : (fderiv ℂ f x v).im = 0 := by
  have hpath : HasDerivAt (fun t : ℝ => x + (t : ℂ) • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.smul_const v).const_add x
  have hf' : HasFDerivAt (𝕜 := ℝ) f ((fderiv ℂ f x).restrictScalars ℝ)
      (x + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have h2 := hf'.comp_hasDerivAt (0 : ℝ) hpath
  have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : HasDerivAt (fun t : ℝ => (f (x + (t : ℂ) • v)).im) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (hreal.mono fun t ht => ht)
  exact h3.unique h4

/-- Realness of `Df` in real directions at real points of an open set of `ℂⁿ × ℂⁿ`: if `f` is
holomorphic on `V` and real at the real points of `V`, then `Df z u` is real for every real point
`z ∈ V` and every real direction `u`. -/
theorem im_fderiv_real_direction {n : ℕ} {V : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hV : IsOpen V)
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f V)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ V →
      (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    {θ I : Fin n → ℝ} (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ V)
    {u : (Fin n → ℂ) × (Fin n → ℂ)} (hu1 : ∀ i, (u.1 i).im = 0) (hu2 : ∀ i, (u.2 i).im = 0) :
    (fderiv ℂ f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) u).im = 0 := by
  set a : Fin n → ℝ := fun i => (u.1 i).re with ha
  set b : Fin n → ℝ := fun i => (u.2 i).re with hb
  have hu : u = ((fun i => (a i : ℂ)), (fun i => (b i : ℂ))) :=
    Prod.ext (funext fun i => Complex.ext (by simp [ha]) (by simp [hu1 i]))
      (funext fun i => Complex.ext (by simp [hb]) (by simp [hu2 i]))
  rw [hu]
  refine im_fderiv_eq_zero_of_real_line (hf.differentiableAt (hV.mem_nhds hz)) ?_
  have hcont : Continuous fun t : ℝ => ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) +
      (t : ℂ) • ((fun i => (a i : ℂ)), (fun i => (b i : ℂ))) :=
    continuous_const.add (Continuous.smul Complex.continuous_ofReal continuous_const)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) +
      (t : ℂ) • ((fun i => (a i : ℂ)), (fun i => (b i : ℂ))) ∈ V := by
    refine hcont.continuousAt.eventually_mem ?_
    simpa using hV.mem_nhds hz
  filter_upwards [hmem] with t ht
  have heq : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) +
      (t : ℂ) • ((fun i => (a i : ℂ)), (fun i => (b i : ℂ))) =
      ((fun i => ((θ i + t * a i : ℝ) : ℂ)), (fun i => ((I i + t * b i : ℝ) : ℂ))) := by
    ext i <;> simp
  rw [heq] at ht ⊢
  exact hreal _ _ ht

section Basis

variable {n : ℕ}

theorem sumVec_symm_apply (v : Fin n ⊕ Fin n → ℂ) :
    (sumVec n).symm v = (fun i => v (Sum.inl i), fun i => v (Sum.inr i)) := rfl

/-- The basis vector `e_s` of `ℂ^{n ⊕ n}` pulled back to `ℂⁿ × ℂⁿ` has real entries. -/
theorem sumVec_symm_single_im (s : Fin n ⊕ Fin n) :
    (∀ i, (((sumVec n).symm (Pi.single s 1)).1 i).im = 0) ∧
      ∀ i, (((sumVec n).symm (Pi.single s 1)).2 i).im = 0 := by
  rw [sumVec_symm_apply]
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> simp [Pi.single_apply] <;> split_ifs <;> simp

theorem sumVec_symm_single_inl (i : Fin n) :
    (sumVec n).symm (Pi.single (Sum.inl i) 1) = (Pi.single i 1, 0) := by
  rw [sumVec_symm_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    simp [Pi.single_apply]

theorem sumVec_symm_single_inr (i : Fin n) :
    (sumVec n).symm (Pi.single (Sum.inr i) 1) = (0, Pi.single i 1) := by
  rw [sumVec_symm_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    simp [Pi.single_apply]

end Basis

/-! ### Items (a)-(e) of `bp:p2:hamiltonian` -/

section Items

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- `Dh` is holomorphic on `𝔅` (`bp:p1:holomorphic-regularity`). -/
theorem differentiableOn_fderiv_h (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    DifferentiableOn ℂ (fderiv ℂ h) 𝔅 :=
  (holomorphic_regularity_of_finiteDimensional hS.isOpen hS.holo).1

/-- Step `step:p2:ham-regular`: `X_h` is holomorphic on `𝔅`. -/
theorem differentiableOn_ham (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅 := by
  have hD := differentiableOn_fderiv_h hS
  unfold hamiltonianVectorFieldℂ
  exact DifferentiableOn.prodMk
    (differentiableOn_pi.2 fun i => hD.clm_apply (differentiableOn_const _))
    (differentiableOn_pi.2 fun i => (hD.clm_apply (differentiableOn_const _)).neg)

/-- Step `step:p2:ham-regular`: `DX_h` is holomorphic on `𝔅`. -/
theorem differentiableOn_fderiv_ham (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅 :=
  (holomorphic_regularity_of_finiteDimensional hS.isOpen (differentiableOn_ham hS)).1

/-- Step `step:p2:ham-regular`: `‖D (DX_h)‖ = ‖D²X_h‖`, with no hypothesis. -/
theorem norm_fderiv_fderiv_eq (f : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖fderiv ℂ (fderiv ℂ f) z‖ = ‖iteratedFDeriv ℂ 2 f z‖ := by
  rw [← norm_iteratedFDeriv_one (𝕜 := ℂ), norm_iteratedFDeriv_fderiv]

/-- Item (a) of `bp:p2:hamiltonian`. -/
theorem ham_regularity (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅 ∧
      DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅 ∧
      ∀ z ∈ 𝔅, ‖fderiv ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) z‖ =
          ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ∧
        ‖fderiv ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) z‖ ≤ M :=
  ⟨differentiableOn_ham hS, differentiableOn_fderiv_ham hS, fun z hz =>
    ⟨norm_fderiv_fderiv_eq _ z, (norm_fderiv_fderiv_eq _ z).trans_le (hS.bounds z hz).2.2⟩⟩

theorem add_angle_eq (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) :
    z + (a, 0) = (z.1 + a, z.2) := Prod.ext rfl (add_zero _)

/-- `Dh` is invariant under integer translations in the angle, at points of `𝔅`. -/
theorem fderiv_h_translate (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ 𝔅) (k : Fin n → ℤ) :
    fderiv ℂ h (z + (fun i => (k i : ℂ), 0)) = fderiv ℂ h z := by
  refine fderiv_add_right_eq_of_eventually (c := 0) ?_
  filter_upwards [hS.isOpen.mem_nhds hz] with y hy
  rw [add_zero, add_angle_eq]
  exact hS.periodic y hy k

/-- `X_h` is invariant under integer translations in the angle, at points of `𝔅`. -/
theorem ham_translate (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ 𝔅) (k : Fin n → ℤ) :
    hamiltonianVectorFieldℂ h (z + (fun i => (k i : ℂ), 0)) = hamiltonianVectorFieldℂ h z := by
  simp only [hamiltonianVectorFieldℂ, fderiv_h_translate hS hz k]

/-- `DX_h` is invariant under integer translations in the angle, at points of `𝔅`. -/
theorem fderiv_ham_translate (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ 𝔅) (k : Fin n → ℤ) :
    fderiv ℂ (hamiltonianVectorFieldℂ h) (z + (fun i => (k i : ℂ), 0)) =
      fderiv ℂ (hamiltonianVectorFieldℂ h) z := by
  refine fderiv_add_right_eq_of_eventually (c := 0) ?_
  filter_upwards [hS.isOpen.mem_nhds hz] with y hy
  rw [add_zero]
  exact ham_translate hS hy k

/-- Item (b) of `bp:p2:hamiltonian`. -/
theorem ham_periodic (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ,
      hamiltonianVectorFieldℂ h (z.1 + (fun i => (k i : ℂ)), z.2) = hamiltonianVectorFieldℂ h z ∧
      fderiv ℂ (hamiltonianVectorFieldℂ h) (z.1 + (fun i => (k i : ℂ)), z.2) =
        fderiv ℂ (hamiltonianVectorFieldℂ h) z := fun z hz k => by
  rw [← add_angle_eq]
  exact ⟨ham_translate hS hz k, fderiv_ham_translate hS hz k⟩

/-- Item (c), first half: `X_h` is real at the real points of `𝔅`. -/
theorem im_ham_eq_zero (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {θ I : Fin n → ℝ}
    (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅) (s : Fin n ⊕ Fin n) :
    (sumVec n (hamiltonianVectorFieldℂ h ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s).im = 0 := by
  have key : ∀ u : (Fin n → ℂ) × (Fin n → ℂ), (∀ i, (u.1 i).im = 0) → (∀ i, (u.2 i).im = 0) →
      (fderiv ℂ h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) u).im = 0 := fun u hu1 hu2 =>
    im_fderiv_real_direction hS.isOpen hS.holo hS.real hz hu1 hu2
  rcases s with i | i
  · refine key _ (fun j => by simp) (fun j => by simp [Pi.single_apply]; split_ifs <;> simp)
  · simp only [sumVec_apply, hamiltonianVectorFieldℂ, Sum.elim_inr, Complex.neg_im]
    rw [key _ (fun j => by simp [Pi.single_apply]; split_ifs <;> simp) (fun j => by simp)]
    simp

/-- The `s`-th coordinate of `sumVec ∘ f` differentiates to the `s`-th coordinate of
`sumVec (Df)`. -/
theorem fderiv_sumVec_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Fin n → ℂ) × (Fin n → ℂ)} {x : E} (hf : DifferentiableAt ℂ f x)
    (s : Fin n ⊕ Fin n) (u : E) :
    fderiv ℂ (fun y => sumVec n (f y) s) x u = sumVec n (fderiv ℂ f x u) s := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin n => ℂ) s).hasFDerivAt.comp
    x (differentiableAt_sumVec_iff.2 hf).hasFDerivAt
  have h2 : fderiv ℂ (fun y => sumVec n (f y) s) x = _ := h.fderiv
  rw [h2]
  simp [fderiv_sumVec_apply]

/-- Item (c), second half: `DX_h` is real at the real points of `𝔅`. -/
theorem im_sqMat_ham (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {θ I : Fin n → ℝ}
    (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅) (s t : Fin n ⊕ Fin n) :
    (sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h)
      ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s t).im = 0 := by
  have hX : DifferentiableAt ℂ (hamiltonianVectorFieldℂ h) _ :=
    (differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds hz)
  rw [KAM.Head.sqMat_apply_entry, ← fderiv_sumVec_coord hX]
  refine im_fderiv_real_direction hS.isOpen (f := fun w => sumVec n (hamiltonianVectorFieldℂ h w) s)
    ?_ (fun θ' I' hz' => im_ham_eq_zero hS hz' s) hz (sumVec_symm_single_im t).1
    (sumVec_symm_single_im t).2
  exact (differentiableOn_pi.1 ((sumVecIso n).differentiable.comp_differentiableOn
    (differentiableOn_ham hS))) s

/-- Item (c) of `bp:p2:hamiltonian`. -/
theorem ham_real (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (∀ s, (sumVec n (hamiltonianVectorFieldℂ h ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s).im
        = 0) ∧
      ∀ s t, (sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h)
        ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s t).im = 0 := fun _ _ hz =>
  ⟨im_ham_eq_zero hS hz, im_sqMat_ham hS hz⟩

/-! ### Item (d) -/

/-- `Ω₀ X_h = (Dh)ᵀ` (`bp:p1:hamiltonian-real`), in the coordinates of `ℂ^{n ⊕ n}`. -/
theorem sumVec_omegaZero_ham (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    sumVec n (omegaZero (hamiltonianVectorFieldℂ h z)) =
      fun s => fderiv ℂ h z ((sumVec n).symm (Pi.single s 1)) := by
  rw [KAM.omegaZero_hamiltonianVectorFieldℂ]
  funext s
  rcases s with i | i
  · simp [sumVec_apply, gradientColumn, sumVec_symm_single_inl]
  · simp [sumVec_apply, gradientColumn, sumVec_symm_single_inr]

/-- The second derivative of a holomorphic function is symmetric. -/
theorem fderiv_fderiv_comm (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ 𝔅) (v w : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ (fderiv ℂ h) z v w = fderiv ℂ (fderiv ℂ h) z w v := by
  have hD : DifferentiableAt ℂ (fderiv ℂ h) z :=
    (differentiableOn_fderiv_h hS).differentiableAt (hS.isOpen.mem_nhds hz)
  have happly : ∀ u t : (Fin n → ℂ) × (Fin n → ℂ),
      fderiv ℂ (fun x => fderiv ℂ h x u) z t = fderiv ℂ (fderiv ℂ h) z t u := by
    intro u t
    rw [fderiv_clm_apply hD (differentiableAt_const u)]
    simp
  have h1 := fderiv_apply_comm_of_differentiableOn hS.isOpen hS.holo hz v w
  rw [happly w v, happly v w] at h1
  exact h1

/-- `Ω₀ DX_h` is the Hessian `D²h` (in the basis `b_s`). -/
theorem omegaZeroMatrix_mul_sqMat_apply (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ 𝔅) (s t : Fin n ⊕ Fin n) :
    (omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z)) s t =
      fderiv ℂ (fderiv ℂ h) z ((sumVec n).symm (Pi.single t 1))
        ((sumVec n).symm (Pi.single s 1)) := by
  have hX : DifferentiableAt ℂ (hamiltonianVectorFieldℂ h) z :=
    (differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds hz)
  have hD : DifferentiableAt ℂ (fderiv ℂ h) z :=
    (differentiableOn_fderiv_h hS).differentiableAt (hS.isOpen.mem_nhds hz)
  set ℓ : (Fin n ⊕ Fin n → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.proj s) ∘ₗ (Matrix.mulVecLin (omegaZeroMatrix n))) with hℓ
  have hℓapply : ∀ v, ℓ v = (omegaZeroMatrix n *ᵥ v) s := fun v => rfl
  have hfun : (fun w => ℓ (sumVec n (hamiltonianVectorFieldℂ h w))) =
      fun w => fderiv ℂ h w ((sumVec n).symm (Pi.single s 1)) := by
    funext w
    rw [hℓapply, ← sumVec_omegaZero, sumVec_omegaZero_ham]
  have hL : fderiv ℂ (fun w => ℓ (sumVec n (hamiltonianVectorFieldℂ h w))) z
      ((sumVec n).symm (Pi.single t 1)) =
      ℓ (sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) z ((sumVec n).symm (Pi.single t 1)))) := by
    have hY : DifferentiableAt ℂ (fun w => sumVec n (hamiltonianVectorFieldℂ h w)) z :=
      differentiableAt_sumVec_iff.2 hX
    have h2 : fderiv ℂ (fun w => ℓ (sumVec n (hamiltonianVectorFieldℂ h w))) z = _ :=
      (ℓ.hasFDerivAt.comp z hY.hasFDerivAt).fderiv
    rw [h2]
    simp [fderiv_sumVec_apply]
  have hR : fderiv ℂ (fun w => fderiv ℂ h w ((sumVec n).symm (Pi.single s 1))) z
      ((sumVec n).symm (Pi.single t 1)) =
      fderiv ℂ (fderiv ℂ h) z ((sumVec n).symm (Pi.single t 1))
        ((sumVec n).symm (Pi.single s 1)) := by
    rw [fderiv_clm_apply hD (differentiableAt_const _)]
    simp
  rw [← hR, ← hfun, hL, hℓapply, ← sqMat_mulVec, Matrix.mulVec_mulVec]
  simp

/-- Item (d) of `bp:p2:hamiltonian`. -/
theorem ham_symplectic (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    ∀ z ∈ 𝔅, sumVec n (omegaZero (hamiltonianVectorFieldℂ h z)) =
        (fun s => fderiv ℂ h z ((sumVec n).symm (Pi.single s 1))) ∧
      (omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z))ᵀ =
        omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) ∧
      (sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z))ᵀ * omegaZeroMatrix n +
        omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) = 0 := by
  intro z hz
  have hsym : (omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z))ᵀ =
      omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) := by
    ext s t
    rw [Matrix.transpose_apply, omegaZeroMatrix_mul_sqMat_apply hS hz,
      omegaZeroMatrix_mul_sqMat_apply hS hz]
    exact fderiv_fderiv_comm hS hz _ _
  refine ⟨sumVec_omegaZero_ham z, hsym, ?_⟩
  rw [Matrix.transpose_mul, omegaZeroMatrix_transpose] at hsym
  rw [← hsym]
  simp

/-! ### Item (e) -/

/-- Item (e) of `bp:p2:hamiltonian`: the mean value estimates. -/
theorem ham_mvt (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    ∀ (z w : (Fin n → ℂ) × (Fin n → ℂ)) (β : ℝ), Metric.ball z β ⊆ 𝔅 → ‖w‖ < β →
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) (z + w) - fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤
        M * ‖w‖ ∧
      ‖hamiltonianVectorFieldℂ h (z + w) - hamiltonianVectorFieldℂ h z -
        fderiv ℂ (hamiltonianVectorFieldℂ h) z w‖ ≤ M * ‖w‖ ^ 2 := by
  intro z w β hball hw
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg w) hw
  have hzw : z + w ∈ Metric.ball z β := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg_ball : segment ℝ z (z + w) ⊆ Metric.ball z β :=
    (convex_ball z β).segment_subset (Metric.mem_ball_self hβ) hzw
  have hseg : segment ℝ z (z + w) ⊆ 𝔅 := hseg_ball.trans hball
  have hM : 0 ≤ M := hS.M_pos.le
  refine ⟨?_, ?_⟩
  · have h1 := increments_open (Metric.isOpen_ball (x := z) (ε := β))
      ((differentiableOn_fderiv_ham hS).mono hball) (A := M)
      (fun x hx => (ham_regularity hS).2.2 x (hball hx) |>.2) hseg_ball
    exact h1
  · have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := M)
      (fun x hx => (hS.bounds x hx).2.2) hseg
    calc _ ≤ M / 2 * ‖w‖ ^ 2 := h1
      _ ≤ M * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]

/-! ### The lemma -/

/-- Blueprint `bp:p2:hamiltonian`, items (a)–(e). -/
theorem hamiltonian (hS : Standing n τ M σK σB σT 𝔅 h ω γ) :
    (DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅 ∧
      DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅 ∧
      ∀ z ∈ 𝔅, ‖fderiv ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) z‖ =
          ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ∧
        ‖fderiv ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) z‖ ≤ M) ∧
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ,
      hamiltonianVectorFieldℂ h (z.1 + (fun i => (k i : ℂ)), z.2) = hamiltonianVectorFieldℂ h z ∧
      fderiv ℂ (hamiltonianVectorFieldℂ h) (z.1 + (fun i => (k i : ℂ)), z.2) =
        fderiv ℂ (hamiltonianVectorFieldℂ h) z) ∧
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (∀ s, (sumVec n (hamiltonianVectorFieldℂ h ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s).im
        = 0) ∧
      ∀ s t, (sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h)
        ((fun i => (θ i : ℂ)), fun i => (I i : ℂ))) s t).im = 0) ∧
    (∀ z ∈ 𝔅, sumVec n (omegaZero (hamiltonianVectorFieldℂ h z)) =
        (fun s => fderiv ℂ h z ((sumVec n).symm (Pi.single s 1))) ∧
      (omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z))ᵀ =
        omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) ∧
      (sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z))ᵀ * omegaZeroMatrix n +
        omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) = 0) ∧
    (∀ (z w : (Fin n → ℂ) × (Fin n → ℂ)) (β : ℝ), Metric.ball z β ⊆ 𝔅 → ‖w‖ < β →
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) (z + w) - fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤
        M * ‖w‖ ∧
      ‖hamiltonianVectorFieldℂ h (z + w) - hamiltonianVectorFieldℂ h z -
        fderiv ℂ (hamiltonianVectorFieldℂ h) z w‖ ≤ M * ‖w‖ ^ 2) :=
  ⟨ham_regularity hS, ham_periodic hS, ham_real hS, ham_symplectic hS, ham_mvt hS⟩

end Items

end KAM.Apost

end
