/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.CubicMap
public import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Higher derivatives of the cubic map (blueprint `bpW:w1:cubic-analytic` (ii))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

`D²𝒩(y)(h,k) = 6 𝒯(y,h,k)` (`waveCubicNL_hasFDerivAt_fderiv`, `waveCubicNL_second_apply`), with
`‖D²𝒩(y)(h,k)‖ ≤ 6 C_* ‖y‖‖h‖‖k‖` (`waveCubicNL_second_norm_le`), and `D³𝒩(y) = 6 𝒯`
(`waveCubicNL_third_apply`), where `𝒯` is invariant under all permutations of its arguments
(`waveTriML_perm`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

lemma waveTriML_swap_vec (x y : Fin 3) (hxy : x ≠ y) (v : Fin 3 → lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp (fun i => v (Equiv.swap x y i)) =
      waveTriML (K := K) m hm ha hp v := by
  have hv : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
  have s01 := waveTriML_swap_left_mid (K := K) m hm ha hp (v 0) (v 1) (v 2)
  have s12 := waveTriML_swap_mid_right (K := K) m hm ha hp (v 0) (v 1) (v 2)
  have s02 := waveTriML_swap_left_right (K := K) m hm ha hp (v 0) (v 1) (v 2)
  have e : ∀ w : Fin 3 → lp (fun _ : ℕ+ => K) 2, waveTriML (K := K) m hm ha hp w =
      waveTriML (K := K) m hm ha hp ![w 0, w 1, w 2] := fun w => by
    congr 1; ext i; fin_cases i <;> rfl
  rw [e (fun i => v (Equiv.swap x y i)), e v]
  fin_cases x <;> fin_cases y <;> simp [Equiv.swap_apply_def] at hxy ⊢ <;> first
    | exact s01.symm | exact s12.symm | exact s02.symm

/-- `𝒯` is symmetric under every permutation of its three arguments. -/
theorem waveTriML_perm (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp (fun i => v (σ i)) = waveTriML (K := K) m hm ha hp v := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => rfl
  | swap_mul f x y hxy ih =>
    have := ih (fun k => v (Equiv.swap x y k))
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [this, waveTriML_swap_vec m hm ha hp x y hxy]

/-- `bpW:w1:cubic-analytic` (ii): `D³𝒩(y) = 6 𝒯`. -/
theorem waveCubicNL_third_apply (y : lp (fun _ : ℕ+ => K) 2) (v : Fin 3 → lp (fun _ : ℕ+ => K) 2) :
    iteratedFDeriv K 3 (waveCubicNL (K := K) m hm ha hp) y v =
      (6 : K) • waveTriML (K := K) m hm ha hp v := by
  have h := (waveTriML (K := K) m hm ha hp).iteratedFDeriv_comp_diagonal y v
  have e : (waveCubicNL (K := K) m hm ha hp) =
      fun x => waveTriML (K := K) m hm ha hp (fun _ => x) :=
    rfl
  rw [e, h]
  simp only [waveTriML_perm m hm ha hp _ v, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K]
  norm_num

/-- The bilinear map `(u, v) ↦ 𝒯(u, v, h)` with `h` frozen. -/
def waveTriBil (h : lp (fun _ : ℕ+ => K) 2) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ K (fun u v => waveTriAux m hm ha hp u v h)
      (fun u u' v => waveTriAux_add_left m hm ha hp u u' v h)
      (fun c u v => waveTriAux_smul_left m hm ha hp c u v h)
      (fun u v v' => waveTriAux_add_mid m hm ha hp u v v' h)
      (fun c u v => waveTriAux_smul_mid m hm ha hp c u v h))
    (waveCubicConst p * ‖h‖) (fun u v => by
      have := waveTriAux_norm_le m hm ha hp u v h
      simp only [LinearMap.mk₂_apply]
      calc _ ≤ waveCubicConst p * (‖u‖ * ‖v‖ * ‖h‖) := this
        _ = _ := by ring)

lemma waveTriBil_apply (h u v : lp (fun _ : ℕ+ => K) 2) :
    waveTriBil m hm ha hp h u v = waveTriML (K := K) m hm ha hp ![u, v, h] := rfl

/-- `bpW:w1:cubic-analytic` (ii): `D²𝒩(y)(h, k) = 6 𝒯(y, h, k)`, in the form
`D(y ↦ D𝒩(y) h)(y) k = 6 𝒯(y, k, h)`. -/
theorem waveCubicNL_second_apply (y h k : lp (fun _ : ℕ+ => K) 2) :
    fderiv K (fun y' => fderiv K (waveCubicNL (K := K) m hm ha hp) y' h) y k =
      (6 : K) • waveTriML (K := K) m hm ha hp ![y, k, h] := by
  have hid := (ContinuousLinearMap.id K (lp (fun _ : ℕ+ => K) 2)).hasFDerivAt (x := y)
  have hB := (waveTriBil m hm ha hp h).hasFDerivAt_of_bilinear hid hid
  have hfun : (fun y' => fderiv K (waveCubicNL (K := K) m hm ha hp) y' h) =
      fun y' => (3 : K) • waveTriBil m hm ha hp h y' y' := by
    funext y'
    rw [waveCubicNL_fderiv, waveTriBil_apply]
  have hB' : HasFDerivAt (fun y' => (3 : K) • waveTriBil m hm ha hp h y' y')
      ((3 : K) • ((ContinuousLinearMap.precompR (lp (fun _ : ℕ+ => K) 2)
          (waveTriBil m hm ha hp h)) y
          (ContinuousLinearMap.id K (lp (fun _ : ℕ+ => K) 2)) +
        (ContinuousLinearMap.precompL (lp (fun _ : ℕ+ => K) 2) (waveTriBil m hm ha hp h))
          (ContinuousLinearMap.id K (lp (fun _ : ℕ+ => K) 2)) y)) y := hB.const_smul (3 : K)
  rw [hfun, hB'.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, waveTriBil_apply]
  have e := waveTriML_swap_left_mid (K := K) m hm ha hp k y h
  rw [← e]
  module

/-- `bpW:w1:cubic-analytic` (ii): `‖D²𝒩(y)(h,k)‖ ≤ 6 C_* ‖y‖ ‖h‖ ‖k‖`. -/
theorem waveCubicNL_second_norm_le (y h k : lp (fun _ : ℕ+ => K) 2) :
    ‖fderiv K (fun y' => fderiv K (waveCubicNL (K := K) m hm ha hp) y' h) y k‖ ≤
      6 * waveCubicConst p * ‖y‖ * ‖h‖ * ‖k‖ := by
  rw [waveCubicNL_second_apply, norm_smul]
  have h6 : ‖(6 : K)‖ = 6 := by simp
  rw [h6]
  have := waveTriAux_norm_le m hm ha hp y k h
  have e : waveTriML (K := K) m hm ha hp ![y, k, h] = waveTriAux m hm ha hp y k h := rfl
  rw [e]
  calc 6 * ‖waveTriAux m hm ha hp y k h‖ ≤ 6 * (waveCubicConst p * (‖y‖ * ‖k‖ * ‖h‖)) := by
        gcongr
    _ = _ := by ring

end KAM.Wave

end
