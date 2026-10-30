/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Coords.Maps

/-!
# SO-LOCK coordinates: the real conjugacy

`lock_conjugacy`: for `Ω > 0`, a `C³` centre `c` and `I > 0`, the physical projection
`Φ = lockToPhysicalR Ω c` maps the Hamiltonian vector field of `K = lockHamiltonianR Ω c`
(frozen convention `X_K = (∂_I K, −∂_θ K)`) to `soField`.

Proof: both differentials are computed along lines (`soHasDerivAt_line`). With
`X_α Y_I − X_I Y_α = 1` (`lockX_lockY_bracket`), `q̇ = Y(X_α Y_I − X_I Y_α) + φ̇(1 + c′) = p` and
`ṗ = c″ − (c″ + V_q)(X_α Y_I − X_I Y_α) = −V_q`.
-/

public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

variable {Ω : ℝ} {c : ℝ → ℝ}

/-- The two coordinates along a line. -/
private theorem hasDerivAt_line_coord (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (j : Fin 2) :
    HasDerivAt (fun t : ℝ => (z + t • v).1 j) (v.1 j) 0 ∧
      HasDerivAt (fun t : ℝ => (z + t • v).2 j) (v.2 j) 0 :=
  ⟨by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 j)).const_add (z.1 j),
   by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 j)).const_add (z.2 j)⟩

/-- `∂_α X` at `z`. -/
def lockXα (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 / (π * Ω)) * (Real.cos (2 * π * z.1 0) * (2 * π))

/-- `∂_I X` at `z` (for `I > 0`). -/
def lockXI (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  1 / (π * Ω) / (2 * Real.sqrt (z.2 0 / (π * Ω))) * Real.sin (2 * π * z.1 0)

/-- `∂_α Y` at `z`. -/
def lockYα (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 * Ω / π) * (-Real.sin (2 * π * z.1 0) * (2 * π))

/-- `∂_I Y` at `z` (for `I > 0`). -/
def lockYI (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Ω / π / (2 * Real.sqrt (z.2 0 * Ω / π)) * Real.cos (2 * π * z.1 0)

theorem hasDerivAt_lockX_line (hΩ : 0 < Ω) (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    HasDerivAt (fun t : ℝ => lockX Ω (z + t • v)) (lockXα Ω z * v.1 0 + lockXI Ω z * v.2 0) 0 := by
  have hπ := Real.pi_pos
  have ha := ((hasDerivAt_line_coord z v 0).1.const_mul (2 * π)).sin
  have hI' := ((hasDerivAt_line_coord z v 0).2.div_const (π * Ω)).sqrt
    (by simpa using (div_pos hI (mul_pos hπ hΩ)).ne')
  refine (hI'.mul ha).congr_deriv ?_
  simp [lockXα, lockXI]
  ring

theorem hasDerivAt_lockY_line (hΩ : 0 < Ω) (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    HasDerivAt (fun t : ℝ => lockY Ω (z + t • v)) (lockYα Ω z * v.1 0 + lockYI Ω z * v.2 0) 0 := by
  have hπ := Real.pi_pos
  have ha := ((hasDerivAt_line_coord z v 0).1.const_mul (2 * π)).cos
  have hI' := (((hasDerivAt_line_coord z v 0).2.mul_const Ω).div_const π).sqrt
    (by simpa using (div_pos (mul_pos hI hΩ) hπ).ne')
  refine (hI'.mul ha).congr_deriv ?_
  simp [lockYα, lockYI]
  ring

/-- The canonical bracket `X_α Y_I − X_I Y_α = 1` (`dY ∧ dX = dI ∧ dα`). -/
theorem lockX_lockY_bracket (hΩ : 0 < Ω) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    lockXα Ω z * lockYI Ω z - lockXI Ω z * lockYα Ω z = 1 := by
  have hπ := Real.pi_pos
  have hA : 0 < Real.sqrt (z.2 0 / (π * Ω)) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (z.2 0 * Ω / π) := Real.sqrt_pos.2 (by positivity)
  have hA2 : Real.sqrt (z.2 0 / (π * Ω)) ^ 2 = z.2 0 / (π * Ω) := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (z.2 0 * Ω / π) ^ 2 = z.2 0 * Ω / π := Real.sq_sqrt (by positivity)
  have hsc := Real.sin_sq_add_cos_sq (2 * π * z.1 0)
  simp only [lockXα, lockXI, lockYα, lockYI]
  generalize Real.sin (2 * π * z.1 0) = s at hsc ⊢
  generalize Real.cos (2 * π * z.1 0) = co at hsc ⊢
  generalize Real.sqrt (z.2 0 / (π * Ω)) = A at hA hA2 ⊢
  generalize Real.sqrt (z.2 0 * Ω / π) = B at hB hB2 ⊢
  have hBA : B = Ω * A := by
    refine (pow_left_inj₀ hB.le (by positivity) two_ne_zero).1 ?_
    rw [hB2, mul_pow, hA2]
    field_simp
  subst hBA
  field_simp
  linear_combination hsc

/-- The differential of `K` along a line (for `I > 0`, `c` with differentiable `c′`, `c″`). -/
theorem hasDerivAt_lockHamiltonianR_line (hΩ : 0 < Ω) (hd0 : Differentiable ℝ c)
    (hd1 : Differentiable ℝ (deriv c)) (hd2 : Differentiable ℝ (deriv (deriv c)))
    (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    HasDerivAt (fun t : ℝ => lockHamiltonianR Ω c (z + t • v))
      (v.2 1 + lockY Ω z * (lockYα Ω z * v.1 0 + lockYI Ω z * v.2 0) -
        deriv c (z.1 1) * deriv (deriv c) (z.1 1) * v.1 1 +
        ((lockXα Ω z * v.1 0 + lockXI Ω z * v.2 0) * deriv (deriv c) (z.1 1) +
          lockX Ω z * (deriv (deriv (deriv c)) (z.1 1) * v.1 1)) +
        (soVq (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1) *
            (v.1 1 + deriv c (z.1 1) * v.1 1 + (lockXα Ω z * v.1 0 + lockXI Ω z * v.2 0)) +
          soVφ (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1) * v.1 1)) 0 := by
  have hφ := (hasDerivAt_line_coord z v 1).1
  have hJ := (hasDerivAt_line_coord z v 1).2
  have hX := hasDerivAt_lockX_line hΩ z v hI
  have hY := hasDerivAt_lockY_line hΩ z v hI
  have h0 : (z + (0 : ℝ) • v) = z := by simp
  have hc0 := (hd0 ((z + (0 : ℝ) • v).1 1)).hasDerivAt.comp (0 : ℝ) hφ
  have hc1 := (hd1 ((z + (0 : ℝ) • v).1 1)).hasDerivAt.comp (0 : ℝ) hφ
  have hc2 := (hd2 ((z + (0 : ℝ) • v).1 1)).hasDerivAt.comp (0 : ℝ) hφ
  have hV := hasDerivAt_soV_comp ((hφ.add hc0).add hX) hφ
  have := ((((hJ.add ((hY.pow 2).div_const 2)).sub ((hc1.pow 2).div_const 2)).add
    (hX.mul hc2)).add hV).sub_const (1 / 2)
  simp only [lockHamiltonianR]
  refine this.congr_deriv ?_
  simp only [h0, Function.comp_apply, Pi.add_apply]
  push_cast
  ring

/-- The differential of `Φ = lockToPhysicalR` along a line (for `I > 0`). -/
theorem hasDerivAt_lockToPhysicalR_line (hΩ : 0 < Ω) (hd0 : Differentiable ℝ c)
    (hd1 : Differentiable ℝ (deriv c)) (z v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    HasDerivAt (fun t : ℝ => lockToPhysicalR Ω c (z + t • v))
      (v.1 1 + deriv c (z.1 1) * v.1 1 + (lockXα Ω z * v.1 0 + lockXI Ω z * v.2 0),
        deriv (deriv c) (z.1 1) * v.1 1 + (lockYα Ω z * v.1 0 + lockYI Ω z * v.2 0), v.1 1) 0 := by
  have hφ := (hasDerivAt_line_coord z v 1).1
  have hX := hasDerivAt_lockX_line hΩ z v hI
  have hY := hasDerivAt_lockY_line hΩ z v hI
  have hc0 := (hd0 ((z + (0 : ℝ) • v).1 1)).hasDerivAt.comp (0 : ℝ) hφ
  have hc1 := (hd1 ((z + (0 : ℝ) • v).1 1)).hasDerivAt.comp (0 : ℝ) hφ
  have := ((hφ.add hc0).add hX).prodMk
    ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hc1).add hY).prodMk hφ)
  simp only [lockToPhysicalR]
  refine this.congr_deriv ?_
  simp

theorem differentiableAt_lockHamiltonianR (hΩ : 0 < Ω) (hd0 : Differentiable ℝ c)
    (hd1 : Differentiable ℝ (deriv c)) (hd2 : Differentiable ℝ (deriv (deriv c)))
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    DifferentiableAt ℝ (lockHamiltonianR Ω c) z := by
  have hπ := Real.pi_pos
  have h1 : z.2 0 / (π * Ω) ≠ 0 := (div_pos hI (mul_pos hπ hΩ)).ne'
  have h2 : z.2 0 * Ω / π ≠ 0 := (div_pos (mul_pos hI hΩ) hπ).ne'
  unfold lockHamiltonianR lockX lockY soV
  fun_prop (disch := assumption)

theorem differentiableAt_lockToPhysicalR (hΩ : 0 < Ω) (hd0 : Differentiable ℝ c)
    (hd1 : Differentiable ℝ (deriv c)) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    DifferentiableAt ℝ (lockToPhysicalR Ω c) z := by
  have hπ := Real.pi_pos
  have h1 : z.2 0 / (π * Ω) ≠ 0 := (div_pos hI (mul_pos hπ hΩ)).ne'
  have h2 : z.2 0 * Ω / π ≠ 0 := (div_pos (mul_pos hI hΩ) hπ).ne'
  unfold lockToPhysicalR lockX lockY
  fun_prop (disch := assumption)

/-- **Conjugacy** (real points, `I > 0`): `lockToPhysicalR` maps `X_K` to `soField`. -/
theorem lock_conjugacy {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (hc : ContDiff ℝ 3 c)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    fderiv ℝ (lockToPhysicalR Ω c) z (KAM.hamiltonianVectorField (lockHamiltonianR Ω c) z) =
      soField (lockToPhysicalR Ω c z) := by
  obtain ⟨hd0, -, hc2⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) c from hc)
  obtain ⟨hd1, -, hc1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) (deriv c) from hc2)
  have hd2 : Differentiable ℝ (deriv (deriv c)) := hc1.differentiable (by norm_num)
  have hK : ∀ v, fderiv ℝ (lockHamiltonianR Ω c) z v = _ := fun v =>
    (soHasDerivAt_line (differentiableAt_lockHamiltonianR hΩ hd0 hd1 hd2 z hI) v).unique
      (hasDerivAt_lockHamiltonianR_line hΩ hd0 hd1 hd2 z v hI)
  have hΦ : ∀ v, fderiv ℝ (lockToPhysicalR Ω c) z v = _ := fun v =>
    (soHasDerivAt_line (differentiableAt_lockToPhysicalR hΩ hd0 hd1 z hI) v).unique
      (hasDerivAt_lockToPhysicalR_line hΩ hd0 hd1 z v hI)
  have hb := lockX_lockY_bracket hΩ z hI
  rw [hΦ, soField_eq]
  simp only [KAM.hamiltonianVectorField, hK]
  simp only [lockToPhysicalR]
  simp
  refine ⟨?_, ?_⟩
  · linear_combination lockY Ω z * hb
  · linear_combination (-(deriv (deriv c) (z.1 1)) -
      soVq (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1)) * hb

end KAM.SpinOrbit.Lock

end
