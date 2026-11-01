/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.PPlusOne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The Lie-coefficient rule for a general `F` (`bpW:w4:lie` (iii))

Off-frontier, source-faithful infrastructure (W4-COMPLETE); the dependency graph is still
being built. Blueprint label: `bpW:w4:lie` (iii), step `stepW:w4:liecoef`.

For a general Taylor Hamiltonian `F ∈ 𝒯_{s'}` (not only the solution of the homological
equation) and finitely supported `z, \bar z`:

* `homLieComp w λ g θ = (2π)⁻¹ ⟨ω, ∂_θ g(θ)⟩ - iλ g(θ)` is the operator acting on one scalar
  component `g` (a coefficient function of the polynomial `bpW:w4:R`);
* `homCoeff_homLieComp`: its `k`-th Fourier coefficient is `i(⟨k,ω⟩ - λ) ĝ_k`, i.e. the
  coefficient of `e^{2πi⟨k,θ⟩}` is replaced by `iδ` times it with `δ = ⟨k,ω⟩ - λ`;
* `homRval_fin_true_gen`: the value of `F` is the finite expression `bpW:w4:R` in the true
  coordinates `z_j = ẑ_j/ω_{a,p}(j+2)` (`homTrueCoord`), with the true matrix entries
  `homNormalEntry_gen`;
* `homLieN_fin_expansion_gen`: `L_N F` is the same finite expression with every component `g`
  replaced by `homLieComp w λ g`, where `λ = 0` for `a_F, b_F`, `λ = Ω_j` for `c^+_{F,j}`,
  `λ = -Ω_j` for `c^-_{F,j}`, `λ = Ω_i + Ω_j` for `P_{F,ij}`, `λ = Ω_j - Ω_i` for `Q_{F,ij}`,
  `λ = -(Ω_i + Ω_j)` for `P'_{F,ij}`;
* `homLemma_lie_iii_gen`: the coefficient rule of `bpW:w4:lie` (iii): the expansion together
  with the coefficient identities `(component of L_N F)^_k = iδ (component of F)^_k` for the
  divisors `δ = ⟨k,ω⟩` (`homDelta0`), `δ^+_{k,j}`, `δ^-_{k,j}`, `δ^P_{k,ij}`, `δ^Q_{k,ij}`
  (so `δ^Q_{0,jj} = 0`), `δ^{P'}_{k,ij}`; `homLemma_lie_iii` is the original `p_+ = p + 1`
  version, with the carrier of `L_N` supplied by the frequency hypotheses.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The true coordinate `x_j = x̂_j / ω_{a,q}(j+2)` of a vector of `ℓ^N_{a,q}` given by its
representative `x̂ ∈ ℓ²`. -/
def homTrueCoord (a q : ℝ) (x : HomL2) (j : ℕ+) : ℂ := x j / (homWt a q j : ℂ)

/-- The true coordinate as a continuous linear functional on the representatives. -/
def homTrueCoordCLM (a q : ℝ) (j : ℕ+) : HomL2 →L[ℂ] ℂ :=
  ((homWt a q j : ℂ))⁻¹ • lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j

theorem homTrueCoordCLM_apply (a q : ℝ) (j : ℕ+) (x : HomL2) :
    homTrueCoordCLM a q j x = homTrueCoord a q x j := by
  simp [homTrueCoordCLM, homTrueCoord, lp.evalCLM, div_eq_inv_mul]

/-- **The component operator** `g ↦ (2π)⁻¹ ⟨ω, ∂_θ g⟩ - iλ g` (`bpW:w4:lie` (iii)). -/
def homLieComp (w : Fin 2 → ℝ) (lam : ℝ) (g : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homPartial l g θ) - Complex.I * lam * g θ

/-- **Coefficients of the component operator** (`bpW:w4:lie` (iii), via `bpW:w4:fourier-ops`):
`(homLieComp w λ g)^_k = i(⟨k,ω⟩ - λ) ĝ_k`. -/
theorem homCoeff_homLieComp {s : ℝ} (hs : 0 < s) (w : Fin 2 → ℝ) (lam : ℝ)
    {g : (Fin 2 → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → g (z + Pi.single i 1) = g z)
    (k : Fin 2 → ℤ) :
    homCoeff (homLieComp w lam g) k = Complex.I * ((homPairZ k w : ℂ) - lam) * homCoeff g k := by
  have hD : ∀ i : Fin 2, DifferentiableOn ℂ (homPartial i g) (complexStrip 2 s) :=
    fun i => homPartial_differentiableOn i hg
  have hDc : ∀ i : Fin 2, homCoeff (homPartial i g) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * homCoeff g k := fun i => by
    simpa using homCoeff_partial hs hg hp i k
  have hS2 : (fun z => ∑ i : Fin 2, (w i : ℂ) * homPartial i g z) =
      fun z => (w 0 : ℂ) * homPartial 0 g z + (w 1 : ℂ) * homPartial 1 g z := by
    funext z; simp [Fin.sum_univ_two]
  have hSd : DifferentiableOn ℂ (fun z => ∑ i : Fin 2, (w i : ℂ) * homPartial i g z)
      (complexStrip 2 s) := by
    rw [hS2]
    exact ((differentiableOn_const _).mul (hD 0)).add ((differentiableOn_const _).mul (hD 1))
  have hAd : DifferentiableOn ℂ (fun z => (2 * Real.pi : ℂ)⁻¹ *
      (∑ i : Fin 2, (w i : ℂ) * homPartial i g z)) (complexStrip 2 s) :=
    (differentiableOn_const _).mul hSd
  have hBd : DifferentiableOn ℂ (fun z => Complex.I * lam * g z) (complexStrip 2 s) :=
    (differentiableOn_const _).mul hg
  have e2 := homCoeff_sub hs hAd hBd k
  have e3 := homCoeff_smul hs hSd (2 * Real.pi : ℂ)⁻¹ k
  have e4 := homCoeff_add hs (u := fun z => (w 0 : ℂ) * homPartial 0 g z)
    (v := fun z => (w 1 : ℂ) * homPartial 1 g z)
    ((differentiableOn_const _).mul (hD 0)) ((differentiableOn_const _).mul (hD 1)) k
  have e5 := homCoeff_smul hs (hD 0) (w 0 : ℂ) k
  have e6 := homCoeff_smul hs (hD 1) (w 1 : ℂ) k
  have e7 := homCoeff_smul hs hg (Complex.I * lam) k
  have hL : homLieComp w lam g = fun z => (2 * Real.pi : ℂ)⁻¹ *
      (∑ i : Fin 2, (w i : ℂ) * homPartial i g z) - Complex.I * lam * g z := rfl
  rw [hL, e2, e3, e7, hS2, e4, e5, e6, hDc 0, hDc 1]
  have hz : (homPairZ k w : ℂ) = (k 0 : ℂ) * (w 0 : ℂ) + (k 1 : ℂ) * (w 1 : ℂ) := by
    simp [homPairZ, Fin.sum_univ_two]
  rw [hz]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp

/-- The coefficient rule for a component read through a continuous linear functional `Λ`:
`(homLieComp w λ (Λ ∘ f))^_k = iδ Λ(f̂_k)` whenever `δ = ⟨k,ω⟩ - λ`. -/
theorem homCoeff_homLieComp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {s : ℝ} (hs : 0 < s) {f : (Fin 2 → ℂ) → E} (hf : IsHomComp s f)
    (Λ : E →L[ℂ] ℂ) (w : Fin 2 → ℝ) (lam δ : ℝ) (k : Fin 2 → ℤ)
    (hδ : δ = homPairZ k w - lam) :
    homCoeff (homLieComp w lam fun θ => Λ (f θ)) k = Complex.I * δ * Λ (homCoeff f k) := by
  have hΛf : DifferentiableOn ℂ (fun θ => Λ (f θ)) (complexStrip 2 s) :=
    Λ.differentiable.comp_differentiableOn hf.1
  have hΛp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ (f (z + Pi.single i 1)) = Λ (f z) :=
    fun i z hz => by rw [hf.2.1 i z hz]
  rw [homCoeff_homLieComp hs w lam hΛf hΛp k, homCoeff_clm hs hf.1 Λ k, hδ]
  push_cast
  rfl

section rule

variable {a p pb s : ℝ}

/-- Matrix entries of the components as continuous linear functionals. -/
theorem homNormalEntry_fun_eq (a p pb : ℝ) (f : (Fin 2 → ℂ) → HomOp) (i j : ℕ+) :
    (fun θ => homNormalEntry_gen a p pb (f θ) i j) =
      fun θ => homNormEntryCLM_gen a p pb i j (f θ) := rfl

theorem homTrueCoord_fun_eq (a q : ℝ) (f : (Fin 2 → ℂ) → HomL2) (j : ℕ+) :
    (fun θ => homTrueCoord a q (f θ) j) = fun θ => homTrueCoordCLM a q j (f θ) :=
  funext fun θ => (homTrueCoordCLM_apply a q j (f θ)).symm

/-- **Lie-coefficient rule, `a_F`** (`bpW:w4:lie` (iii)): `δ = ⟨k,ω⟩`. -/
theorem homLieComp_coeff_a (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (k : Fin 2 → ℤ) :
    homCoeff (homLieComp w 0 F.a0) k = Complex.I * (homDelta0 w k : ℂ) * homCoeff F.a0 k := by
  have := homCoeff_homLieComp_clm hs F.comp_a0 (ContinuousLinearMap.id ℂ ℂ) w 0
    (homDelta0 w k) k (by simp [homDelta0])
  simpa using this

/-- **Lie-coefficient rule, `b_F`** (`bpW:w4:lie` (iii)): `δ = ⟨k,ω⟩`. -/
theorem homLieComp_coeff_b (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (k : Fin 2 → ℤ) (m : Fin 2) :
    homCoeff (homLieComp w 0 fun θ => F.b θ m) k =
      Complex.I * (homDelta0 w k : ℂ) * homCoeff F.b k m := by
  have := homCoeff_homLieComp_clm hs F.comp_b (ContinuousLinearMap.proj m) w 0
    (homDelta0 w k) k (by simp [homDelta0])
  simpa using this

/-- **Lie-coefficient rule, `c^+_F`** (`bpW:w4:lie` (iii)): `δ = δ^+_{k,j} = ⟨k,ω⟩ - Ω_j`. -/
theorem homLieComp_coeff_cp (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) :
    homCoeff (homLieComp w (W j) fun θ => homTrueCoord a pb (F.cp θ) j) k =
      Complex.I * (homDeltaPlus w W k j : ℂ) * homTrueCoord a pb (homCoeff F.cp k) j := by
  rw [homTrueCoord_fun_eq, homCoeff_homLieComp_clm hs F.comp_cp _ w (W j) _ k rfl,
    homTrueCoordCLM_apply]
  rfl

/-- **Lie-coefficient rule, `c^-_F`** (`bpW:w4:lie` (iii)): `δ = δ^-_{k,j} = ⟨k,ω⟩ + Ω_j`. -/
theorem homLieComp_coeff_cm (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) :
    homCoeff (homLieComp w (-W j) fun θ => homTrueCoord a pb (F.cm θ) j) k =
      Complex.I * (homDeltaMinus w W k j : ℂ) * homTrueCoord a pb (homCoeff F.cm k) j := by
  rw [homTrueCoord_fun_eq, homCoeff_homLieComp_clm hs F.comp_cm _ w (-W j) (homDeltaMinus w W k j)
    k (by simp [homDeltaMinus]), homTrueCoordCLM_apply]

/-- **Lie-coefficient rule, `P_F`** (`bpW:w4:lie` (iii)): `δ = δ^P_{k,ij} = ⟨k,ω⟩ - Ω_i - Ω_j`. -/
theorem homLieComp_coeff_P (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    homCoeff (homLieComp w (W i + W j) fun θ => homNormalEntry_gen a p pb (F.P θ) i j) k =
      Complex.I * (homDeltaP w W k i j : ℂ) * homNormalEntry_gen a p pb (homCoeff F.P k) i j := by
  rw [homNormalEntry_fun_eq, homCoeff_homLieComp_clm hs F.comp_P _ w (W i + W j)
    (homDeltaP w W k i j) k (by simp only [homDeltaP]; ring)]
  rfl

/-- **Lie-coefficient rule, `Q_F`** (`bpW:w4:lie` (iii)): `δ = δ^Q_{k,ij} = ⟨k,ω⟩ + Ω_i - Ω_j`
(so `δ^Q_{0,jj} = 0`). -/
theorem homLieComp_coeff_Q (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    homCoeff (homLieComp w (W j - W i) fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) k =
      Complex.I * (homDeltaQ w W k i j : ℂ) * homNormalEntry_gen a p pb (homCoeff F.Q k) i j := by
  rw [homNormalEntry_fun_eq, homCoeff_homLieComp_clm hs F.comp_Q _ w (W j - W i)
    (homDeltaQ w W k i j) k (by simp only [homDeltaQ]; ring)]
  rfl

/-- **Lie-coefficient rule, `P'_F`** (`bpW:w4:lie` (iii)):
`δ = δ^{P'}_{k,ij} = ⟨k,ω⟩ + Ω_i + Ω_j`. -/
theorem homLieComp_coeff_P' (hs : 0 < s) (F : HomTaylor_gen a p pb s) (w : Fin 2 → ℝ)
    (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    homCoeff (homLieComp w (-(W i + W j)) fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) k =
      Complex.I * (homDeltaP' w W k i j : ℂ) *
        homNormalEntry_gen a p pb (homCoeff F.P' k) i j := by
  rw [homNormalEntry_fun_eq, homCoeff_homLieComp_clm hs F.comp_P' _ w (-(W i + W j))
    (homDeltaP' w W k i j) k (by simp only [homDeltaP']; ring)]
  rfl

end rule

end KAM.Wave
