/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealCalc
public import KAM.Wave.KamStep.TaylorSmoothing
public import KAM.Wave.Birkhoff.Coords
public import KAM.Wave.Normal.ActionCoeff
public import KAM.Frozen.Wave.Defs.LinearTorus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The action–angle substitution: definition and part (i) (blueprint-W `bpW:w5:action-angle`)

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (i).

For `ξ ∈ ℂ²` and `w = (θ, y, u, v) ∈ 𝒫` (`KamPhase`, normal components in `p`-representatives with
the Dirichlet labels `j + 2`) with `Re(ξ_i + y_i) > 0`, `𝒜_ξ(w) ∈ 𝔚 = 𝔚_{a,p}` (`BirkSpace`,
weighted
coordinates at `(a,p)`) is
`𝒜_ξ(w)_{±i} = √(ξ_i + y_i) e^{∓2πiθ_i}` (`i = 1, 2`), `𝒜_ξ(w)_{±J} = (u_{J-2} ± i v_{J-2})/√2`
(`J ≥ 3`), `√` the principal branch (`aaSqrt`, external fact `bpW:w5:ext-sqrt`).

* `aaSqrt`, `aaShift` (the index shift `j ↦ j + 2` on `ℓ²(ℕ+)`), `aaNormal` (the normal part, a
  continuous linear map `𝒫 → 𝔚`), `aaTanCoord` (the actual tangential coordinates), `aaMap a p ξ w`
  (`𝒜_ξ(w)` in weighted coordinates at `(a,p)`), `aaDomJ` (the open domain);
* coordinates: `birkCoord_aaMap_tan`, `aaMap_nor_true`, `aaMap_nor_false`;
* (i): `aaMap_differentiableOn` (holomorphic in `(ξ, w)` on its open domain `aaDomJ`,
  `isOpen_aaDomJ`), `aaMap_add_tau` (`1`-periodic in each `θ_i`), `aaMap_real` (real data are mapped
  into `{ϱ w = w}`), `aaMap_linearTorus` (`𝒵⁻¹ 𝒜_ξ(θ,0,0,0) = K⁰_ξ(θ)` at `a = p = 1`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-! ### The principal square root -/

/-- The principal square root `√ζ = ζ^{1/2}` (`bpW:w5:ext-sqrt`). -/
def aaSqrt (ζ : ℂ) : ℂ := ζ ^ (2⁻¹ : ℂ)

theorem aaSqrt_sq (ζ : ℂ) : aaSqrt ζ ^ 2 = ζ := Complex.cpow_ofNat_inv_pow ζ 2

theorem aaSqrt_mul_self (ζ : ℂ) : aaSqrt ζ * aaSqrt ζ = ζ := by rw [← sq, aaSqrt_sq]

theorem aaSqrt_ne_zero {ζ : ℂ} (h : ζ ≠ 0) : aaSqrt ζ ≠ 0 := fun h0 =>
  h (by rw [← aaSqrt_sq ζ, h0]; ring)

theorem aa_ne_zero_of_re_pos {ζ : ℂ} (h : 0 < ζ.re) : ζ ≠ 0 := fun h0 => by simp [h0] at h

theorem aa_mem_slitPlane_of_re_pos {ζ : ℂ} (h : 0 < ζ.re) : ζ ∈ slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl h)

/-- `√x` of a real `x ≥ 0` is the real square root. -/
theorem aaSqrt_ofReal {x : ℝ} (hx : 0 ≤ x) : aaSqrt (x : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
  unfold aaSqrt
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  norm_num

theorem differentiableAt_aaSqrt_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {x : E} (hg : DifferentiableAt ℂ g x) (h : 0 < (g x).re) :
    DifferentiableAt ℂ (fun x => aaSqrt (g x)) x :=
  hg.cpow_const (aa_mem_slitPlane_of_re_pos h)

/-! ### The index shift `j ↦ j + 2` -/

theorem aaIdx_injective : Function.Injective (fun j : ℕ+ => j + 2) := fun _ _ h => by
  simpa using h

/-- The sequence `J ↦ x_{J-2}` (`J ≥ 3`), `0` for `J ≤ 2`. -/
def aaShiftFun (x : HomL2) (J : ℕ+) : ℂ :=
  if h : 3 ≤ (J : ℕ) then x ⟨(J : ℕ) - 2, by omega⟩ else 0

theorem pnat_sub_two_add_two (J : ℕ+) (h : 3 ≤ (J : ℕ)) :
    Nat.toPNat ((J : ℕ) - 2) (by omega) + 2 = J := by
  apply PNat.eq
  rw [PNat.add_coe]
  show (J : ℕ) - 2 + 2 = J
  omega

theorem aaShiftFun_add_two (x : HomL2) (j : ℕ+) : aaShiftFun x (j + 2) = x j := by
  have h : 3 ≤ ((j + 2 : ℕ+) : ℕ) := by simp; have := j.pos; omega
  simp only [aaShiftFun, h, dite_true]
  congr 1

theorem aaShiftFun_le_two (x : HomL2) {J : ℕ+} (hJ : (J : ℕ) ≤ 2) : aaShiftFun x J = 0 := by
  simp only [aaShiftFun]
  exact dite_eq_right_iff.2 fun h => absurd h (by omega)

theorem aaShiftFun_notMem_range (x : HomL2) (J : ℕ+) (hJ : J ∉ Set.range (fun j : ℕ+ => j + 2)) :
    aaShiftFun x J = 0 := by
  by_cases h : 3 ≤ (J : ℕ)
  · exfalso
    exact hJ ⟨⟨(J : ℕ) - 2, by omega⟩, pnat_sub_two_add_two J h⟩
  · exact aaShiftFun_le_two x (by omega)

theorem aaShift_hasSum_sq (x : HomL2) :
    HasSum (fun J => ‖aaShiftFun x J‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp_two_hasSum_sq x
  have hs : (fun j : ℕ+ => ‖aaShiftFun x (j + 2)‖ ^ 2) = fun j => ‖x j‖ ^ 2 := funext fun j => by
    rw [aaShiftFun_add_two]
  rw [← hs] at h
  exact (Function.Injective.hasSum_iff aaIdx_injective (f := fun J => ‖aaShiftFun x J‖ ^ 2)
    (fun J hJ => by simp [aaShiftFun_notMem_range x J hJ])).1 h

theorem memℓp_aaShiftFun (x : HomL2) : Memℓp (aaShiftFun x) 2 :=
  memℓp_gen (by simpa using (aaShift_hasSum_sq x).summable)

/-- The isometric shift `ℓ²(ℕ+) → ℓ²(ℕ+)`, `(Sx)_J = x_{J-2}` (`J ≥ 3`), `0` otherwise. -/
def aaShift : HomL2 →L[ℂ] HomL2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨aaShiftFun x, memℓp_aaShiftFun x⟩
      map_add' := fun x y => by
        ext J
        show aaShiftFun (x + y) J = aaShiftFun x J + aaShiftFun y J
        unfold aaShiftFun; split_ifs <;> first | rfl | simp
      map_smul' := fun c x => by
        ext J
        show aaShiftFun (c • x) J = c * aaShiftFun x J
        unfold aaShiftFun; split_ifs <;> first | rfl | simp }
    1 (fun x => by
      have h1 := lp_two_hasSum_sq (⟨aaShiftFun x, memℓp_aaShiftFun x⟩ : HomL2)
      have h2 := aaShift_hasSum_sq x
      have : ‖(⟨aaShiftFun x, memℓp_aaShiftFun x⟩ : HomL2)‖ ^ 2 = ‖x‖ ^ 2 := h1.unique h2
      rw [one_mul]
      exact le_of_eq ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this))

@[simp] theorem aaShift_apply (x : HomL2) (J : ℕ+) : aaShift x J = aaShiftFun x J := rfl

theorem norm_aaShift (x : HomL2) : ‖aaShift x‖ = ‖x‖ := by
  have h1 := lp_two_hasSum_sq (aaShift x)
  have h2 := aaShift_hasSum_sq x
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.unique h2)

/-! ### The map `𝒜_ξ` -/

/-- The normal part `(u, v) ↦ ŵ`, `ŵ_{±J} = (u_{J-2} ± i v_{J-2})/√2`, in weighted coordinates (the
same formula at every weight, as the normal weights of `𝒫` and `𝔚` agree at the Dirichlet label). -/
def aaNormal : KamPhase →L[ℂ] BirkSpace :=
  birkZ.comp ((aaShift.comp ((ContinuousLinearMap.fst ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))))).prod
    (aaShift.comp ((ContinuousLinearMap.snd ℂ HomL2 HomL2).comp
      ((ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))))))

theorem aaNormal_apply (w : KamPhase) (l : BirkIdx) :
    aaNormal w l = (aaShiftFun w.2.2.1 l.2 + birkSgn l * I * aaShiftFun w.2.2.2 l.2) / birkSqrt2 :=
  rfl

/-- The actual tangential coordinate `𝒜_ξ(w)_{±i} = √(ξ_i + y_i) e^{∓2πiθ_i}`
(`b = true` is `+i`). -/
def aaTanCoord (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) : ℂ :=
  aaSqrt (ξ i + w.2.1 i) * cexp (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i))

/-- The tangential part of `𝒜_ξ(w)` in weighted coordinates at `(a,p)`. -/
def aaTan (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) : BirkSpace :=
  ∑ i : Fin 2, ∑ b : Bool,
    lp.single 2 (b, modeIdx i) ((ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i)

/-- **The action–angle substitution** `𝒜_ξ(w) ∈ 𝔚_{a,p}` (blueprint `bpW:w5:action-angle`), in
weighted coordinates at `(a,p)`; it is the stated map on the domain `Re(ξ_i + y_i) > 0` (`aaDomJ`),
and is extended by the same formula (principal `cpow`) elsewhere. -/
def aaMap (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) : BirkSpace := aaTan a p ξ w + aaNormal w

/-- The open domain `{(ξ, w) : Re(ξ_i + y_i) > 0, i = 1, 2}` of `(ξ, w) ↦ 𝒜_ξ(w)`. -/
def aaDomJ : Set ((Fin 2 → ℂ) × KamPhase) := {x | ∀ i, 0 < (x.1 i + x.2.2.1 i).re}

theorem isOpen_aaDomJ : IsOpen aaDomJ := by
  have : aaDomJ = ⋂ i : Fin 2, {x : (Fin 2 → ℂ) × KamPhase | 0 < (x.1 i + x.2.2.1 i).re} := by
    ext x; simp [aaDomJ]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  fun_prop

/-! ### Coordinates -/

theorem modeIdx_cases (J : ℕ+) : (∃ i : Fin 2, J = modeIdx i) ∨ ∃ j : ℕ+, J = j + 2 := by
  by_cases h : (J : ℕ) ≤ 2
  · left
    refine ⟨⟨(J : ℕ) - 1, by have := J.pos; omega⟩, PNat.eq ?_⟩
    simp [modeIdx]; have := J.pos; omega
  · right
    exact ⟨⟨(J : ℕ) - 2, by omega⟩, (pnat_sub_two_add_two J (by omega)).symm⟩

theorem modeIdx_ne_add_two (i : Fin 2) (j : ℕ+) : modeIdx i ≠ j + 2 := fun h => by
  have h' : ((modeIdx i : ℕ+) : ℕ) = ((j + 2 : ℕ+) : ℕ) := congrArg _ h
  rw [PNat.add_coe] at h'
  simp only [modeIdx, PNat.mk_coe] at h'
  have := i.is_lt
  have := j.pos
  simp at h'
  omega

theorem aaTan_apply (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (l : BirkIdx) :
    aaTan a p ξ w l = ∑ i : Fin 2, ∑ b : Bool,
      if l = (b, modeIdx i) then (ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i else 0 := by
  simp only [aaTan, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]

theorem aaTan_tan (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) :
    aaTan a p ξ w (b, modeIdx i) = (ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i := by
  rw [aaTan_apply]
  have hinj := modeIdx_injective (N := 2)
  fin_cases i <;> cases b <;> simp [Prod.ext_iff, hinj.eq_iff]

theorem aaTan_nor (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (j : ℕ+) :
    aaTan a p ξ w (b, j + 2) = 0 := by
  rw [aaTan_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b' _ => ?_
  exact ite_eq_right_iff.2 fun h => absurd (congrArg Prod.snd h).symm (modeIdx_ne_add_two i j)

theorem aaNormal_tan (w : KamPhase) (b : Bool) (i : Fin 2) : aaNormal w (b, modeIdx i) = 0 := by
  have h : ((modeIdx i : ℕ+) : ℕ) ≤ 2 := by simp [modeIdx]; have := i.is_lt; omega
  rw [aaNormal_apply]
  simp [aaShiftFun_le_two _ h]

theorem aaMap_tan (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) :
    aaMap a p ξ w (b, modeIdx i) = (ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i := by
  simp only [aaMap, lp.coeFn_add, Pi.add_apply, aaTan_tan, aaNormal_tan, add_zero]

/-- (`bpW:w5:action-angle`) The actual tangential coordinates `√(ξ_i+y_i) e^{∓2πiθ_i}`. -/
theorem birkCoord_aaMap_tan (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) :
    birkCoord a p (aaMap a p ξ w) (b, modeIdx i) = aaTanCoord ξ w b i := by
  rw [birkCoord, aaMap_tan]
  exact mul_div_cancel_left₀ _ (ellWeight_cast_ne_zero (K := ℂ) a p (modeIdx i))

/-- (`bpW:w5:action-angle`) `𝒜_ξ(w)_{J} = z_{J-2} = (u + i v)/√2` (`J = j + 2`, representatives). -/
theorem aaMap_nor_true (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (j : ℕ+) :
    aaMap a p ξ w (true, j + 2) = (w.2.2.1 j + I * w.2.2.2 j) / birkSqrt2 := by
  simp only [aaMap, lp.coeFn_add, Pi.add_apply, aaTan_nor, zero_add, aaNormal_apply,
    aaShiftFun_add_two, birkSgn, ite_true, one_mul]

/-- (`bpW:w5:action-angle`) `𝒜_ξ(w)_{-J} = \bar z_{J-2} = (u - i v)/√2`. -/
theorem aaMap_nor_false (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (j : ℕ+) :
    aaMap a p ξ w (false, j + 2) = (w.2.2.1 j - I * w.2.2.2 j) / birkSqrt2 := by
  simp only [aaMap, lp.coeFn_add, Pi.add_apply, aaTan_nor, zero_add, aaNormal_apply,
    aaShiftFun_add_two, birkSgn, Bool.false_eq_true, ite_false]
  ring

/-! ### Part (i) -/

theorem lp_single_eq_smul (l : BirkIdx) (c : ℂ) :
    (lp.single 2 l c : BirkSpace) = c • lp.single 2 l (1 : ℂ) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem differentiableAt_aaTanCoord {x : (Fin 2 → ℂ) × KamPhase} (hx : x ∈ aaDomJ) (b : Bool)
    (i : Fin 2) :
    DifferentiableAt ℂ (fun x : (Fin 2 → ℂ) × KamPhase => aaTanCoord x.1 x.2 b i) x := by
  unfold aaTanCoord
  refine DifferentiableAt.mul ?_ ?_
  · exact differentiableAt_aaSqrt_comp (g := fun x : (Fin 2 → ℂ) × KamPhase => x.1 i + x.2.2.1 i)
      (by fun_prop) (hx i)
  · fun_prop

/-- (`bpW:w5:action-angle` (i)) `(ξ, w) ↦ 𝒜_ξ(w)` is holomorphic on its open domain. -/
theorem aaMap_differentiableOn (a p : ℝ) :
    DifferentiableOn ℂ (fun x : (Fin 2 → ℂ) × KamPhase => aaMap a p x.1 x.2) aaDomJ := by
  intro x hx
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold aaMap aaTan
  refine DifferentiableAt.add ?_ (aaNormal.differentiableAt.comp x differentiableAt_snd)
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun b _ => ?_
  have e : (fun x : (Fin 2 → ℂ) × KamPhase => (lp.single 2 (b, modeIdx i)
      ((ellWeight a p (modeIdx i) : ℂ) * aaTanCoord x.1 x.2 b i) : BirkSpace)) =
      fun x => ((ellWeight a p (modeIdx i) : ℂ) * aaTanCoord x.1 x.2 b i) •
        (lp.single 2 (b, modeIdx i) (1 : ℂ) : BirkSpace) :=
    funext fun x => lp_single_eq_smul _ _
  rw [e]
  exact ((differentiableAt_const _).mul (differentiableAt_aaTanCoord hx b i)).smul_const _

theorem aaTanCoord_add_tau (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i k : Fin 2) :
    aaTanCoord ξ (w + stepTau k) b i = aaTanCoord ξ w b i := by
  unfold aaTanCoord stepTau
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero]
  congr 1
  by_cases hk : i = k
  · subst hk
    rw [Pi.single_eq_same, mul_add, mul_add, Complex.exp_add]
    have h1 : cexp (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * ((1 : ℝ) : ℂ))) = 1 := by
      cases b
      · simp only [birkSgn, Bool.false_eq_true, ite_false, neg_neg, one_mul, Complex.ofReal_one,
          mul_one]
        exact Complex.exp_two_pi_mul_I
      · simp only [birkSgn, ite_true, Complex.ofReal_one, mul_one, neg_mul, one_mul,
          Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    simpa using congrArg (fun z => cexp (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i)) * z)
      h1
  · rw [Pi.single_eq_of_ne hk, add_zero]

/-- (`bpW:w5:action-angle` (i)) `𝒜_ξ` is `1`-periodic in each `θ_i`. -/
theorem aaMap_add_tau (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (k : Fin 2) :
    aaMap a p ξ (w + stepTau k) = aaMap a p ξ w := by
  have hN : aaNormal (w + stepTau k) = aaNormal w := by
    rw [map_add]
    have h0 : ∀ J, aaShiftFun (0 : HomL2) J = 0 := fun J => by
      unfold aaShiftFun; split_ifs <;> rfl
    have : aaNormal (stepTau k) = 0 := by
      ext l; rw [aaNormal_apply]; simp only [stepTau, h0]; simp
    rw [this, add_zero]
  unfold aaMap aaTan
  simp_rw [aaTanCoord_add_tau, hN]

/-- `√(x) e^{∓2πiθ}` with `x > 0`, `θ` real: the conjugate is the other sign. -/
theorem aaTanCoord_conj (ξ : Fin 2 → ℝ) (w : KamPhase) (hw : StepReal w)
    (hpos : ∀ i, 0 < ξ i + (w.2.1 i).re) (b : Bool) (i : Fin 2) :
    starRingEnd ℂ (aaTanCoord (fun i => (ξ i : ℂ)) w (!b) i) =
      aaTanCoord (fun i => (ξ i : ℂ)) w b i := by
  have hy : w.2.1 i = ((w.2.1 i).re : ℂ) := (Complex.ext rfl (by simp [hw.2.1 i]))
  have hθ : w.1 i = ((w.1 i).re : ℂ) := (Complex.ext rfl (by simp [hw.1 i]))
  have hx : (ξ i : ℂ) + w.2.1 i = ((ξ i + (w.2.1 i).re : ℝ) : ℂ) := by
    rw [hy]; push_cast; simp
  unfold aaTanCoord
  rw [hx, aaSqrt_ofReal (hpos i).le, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hθ]
  congr 2
  cases b <;> simp [birkSgn, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]

/-- (`bpW:w5:action-angle` (i)) Real points with real `ξ` are mapped into `𝔚_ℝ = {ϱ w = w}`. -/
theorem aaMap_real (a p : ℝ) (ξ : Fin 2 → ℝ) (w : KamPhase) (hw : StepReal w)
    (hpos : ∀ i, 0 < ξ i + (w.2.1 i).re) :
    birkRho (aaMap a p (fun i => (ξ i : ℂ)) w) = aaMap a p (fun i => (ξ i : ℂ)) w := by
  ext ⟨b, J⟩
  rw [birkRho_apply]
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp only [birkNeg, aaMap_tan, map_mul, Complex.conj_ofReal]
    rw [aaTanCoord_conj ξ w hw hpos]
  · have hu : starRingEnd ℂ (w.2.2.1 j) = w.2.2.1 j := Complex.conj_eq_iff_im.2 (hw.2.2.1 j)
    have hv : starRingEnd ℂ (w.2.2.2 j) = w.2.2.2 j := Complex.conj_eq_iff_im.2 (hw.2.2.2 j)
    cases b
    · simp only [birkNeg, Bool.not_false, aaMap_nor_true, aaMap_nor_false, map_div₀, map_add,
        map_mul, hu, hv, Complex.conj_I, conj_birkSqrt2]
      ring
    · simp only [birkNeg, Bool.not_true, aaMap_nor_true, aaMap_nor_false, map_div₀, map_sub,
        map_mul, hu, hv, Complex.conj_I, conj_birkSqrt2]
      ring

theorem birkSgn_true (j : ℕ+) : birkSgn (true, j) = 1 := rfl

theorem birkSgn_false (j : ℕ+) : birkSgn (false, j) = -1 := rfl

/-- The tangential coordinate at real data in trigonometric form. -/
theorem aaTanCoord_eq_trig (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) {x φ : ℝ}
    (hx : 0 ≤ x) (hxi : ξ i + w.2.1 i = x) (hφ : w.1 i = φ) :
    aaTanCoord ξ w b i = ((Real.sqrt x : ℝ) : ℂ) *
      ((Real.cos (2 * Real.pi * φ) : ℂ) - birkSgn (b, modeIdx i) * I * Real.sin (2 * Real.pi * φ))
    := by
  unfold aaTanCoord
  rw [hxi, hφ, aaSqrt_ofReal hx]
  congr 1
  have e : -(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * (φ : ℂ)) =
      ((-(birkSgn (b, modeIdx i)) * (2 * Real.pi * φ) : ℂ)) * I := by ring
  rw [e, Complex.exp_mul_I]
  cases b
  · simp only [birkSgn, Bool.false_eq_true, ite_false, neg_neg, one_mul]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  · simp only [birkSgn, ite_true, neg_mul, one_mul]
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

/-- (`bpW:w5:action-angle` (i)) At `y = 0`, `u = v = 0`, real `θ` and `ξ ∈ (0,∞)²`, `𝒜_ξ` is the
linear torus: `𝒵⁻¹ 𝒜_ξ(θ, 0, 0, 0) = K⁰_ξ(θ)` (`bpW:w0:periodone`, `bpW:w3:coords`), at
`a = p = 1`. -/
theorem aaMap_linearTorus (ξ : Fin 2 → ℝ) (hξ : ∀ i, 0 < ξ i) (θ : Fin 2 → ℝ) :
    birkZinv (aaMap 1 1 (fun i => (ξ i : ℂ)) (fun i => (θ i : ℂ), 0, 0, 0)) =
      birkReal (linearTorus ξ hξ θ) := by
  have h2 := birkSqrt2_ne
  have h2sq := birkSqrt2_sq
  have hsucc : ∀ i : Fin 2, (i : ℕ).succPNat = modeIdx i := fun i => rfl
  have htrig : ∀ (b : Bool) (i : Fin 2), aaTanCoord (fun i => (ξ i : ℂ))
      ((fun i => (θ i : ℂ), 0, 0, 0) : KamPhase) b i = ((Real.sqrt (ξ i) : ℝ) : ℂ) *
      ((Real.cos (2 * Real.pi * θ i) : ℂ) - birkSgn (b, modeIdx i) * I *
        Real.sin (2 * Real.pi * θ i)) := fun b i =>
    aaTanCoord_eq_trig _ _ b i (hξ i).le (by simp) rfl
  have hsq : ∀ i : Fin 2, ((Real.sqrt (2 * ξ i) : ℝ) : ℂ) = birkSqrt2 * Real.sqrt (ξ i) :=
      fun i => by
    rw [Real.sqrt_mul (by norm_num), birkSqrt2]; push_cast; ring
  refine Prod.ext (lp.ext (funext fun J => ?_)) (lp.ext (funext fun J => ?_))
  · rw [birkZinv_fst_apply, birkReal_apply, complexifyLp_apply]
    rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [aaMap_tan, aaMap_tan, htrig, htrig]
      simp only [linearTorus, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
        hsucc, Pi.single_apply, (modeIdx_injective (N := 2)).eq_iff, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      rw [div_eq_iff h2]
      push_cast
      rw [hsq, birkSgn_true, birkSgn_false]
      linear_combination (-((ellWeight 1 1 (modeIdx i) : ℂ) * (Real.sqrt (ξ i) : ℂ) *
        Complex.cos (2 * (Real.pi : ℂ) * (θ i : ℂ)))) * h2sq
    · rw [aaMap_nor_true, aaMap_nor_false]
      simp only [linearTorus, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, hsucc,
        Pi.single_apply]
      rw [Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun h =>
        absurd h.symm (modeIdx_ne_add_two i j)]
      simp
  · rw [birkZinv_snd_apply, birkReal_apply, complexifyLp_apply]
    rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [aaMap_tan, aaMap_tan, htrig, htrig]
      simp only [linearTorus, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
        hsucc, Pi.single_apply, (modeIdx_injective (N := 2)).eq_iff, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero h2)]
      push_cast
      rw [hsq, birkSgn_true, birkSgn_false]
      linear_combination ((ellWeight 1 1 (modeIdx i) : ℂ) * (Real.sqrt (ξ i) : ℂ) *
        Complex.sin (2 * (Real.pi : ℂ) * (θ i : ℂ)) * I) * h2sq
    · rw [aaMap_nor_true, aaMap_nor_false]
      simp only [linearTorus, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, hsucc,
        Pi.single_apply]
      rw [Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun h =>
        absurd h.symm (modeIdx_ne_add_two i j)]
      simp

end KAM.Wave

end
