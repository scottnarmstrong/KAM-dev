/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The exact lunar spin-orbit model (track SO, package SO-MODEL)

Proposal `docs/explorations/lunar-spin-orbit-certificate-proposal.md` §2.3. Unfrozen helper code.

* `soEccQ`, `soEpsQ` (rational) and `soEcc = 549/10000`, `soEps = 69/200000` (real): the exact
  constants of owner decision D30.
* `soCoeffPoly e m`: the polynomial `A_m(e)` of the proposal table (`A_m = 0` outside `1 ≤ m ≤ 7`),
  over any field; `soA m = A_m(soEcc)`; `soAQ m` is the exact rational value
  (`soA_eq_ratCast`).
* `soV q φ = -ε Σ_{m=1}^7 A_m cos (2π (2q - mφ))` and its entire complex extension `soVC`
  (`soVC_differentiable`, `soVC_differentiable_pi`, `soVC_analyticOnNhd_q`); `soVC_ofReal`
  (real on reals), 1-periodicity in `q` and in `φ` (`soV_periodic_q`, `soV_periodic_φ`, integer shifts `soVC_add_int`).
* the explicit partial derivatives `soVq = ∂_q V = 4π ε Σ A_m sin(·)`,
  `soVφ = ∂_φ V = -2π ε Σ m A_m sin(·)` with `HasDerivAt` statements (real and complex, also in
  composed form `hasDerivAt_soVC_comp`);
* the physical vector field `soField (q, p, φ) = (p, -∂_q V, 1)` (the derivative is `deriv`, the
  explicit form is `soField_eq`) and the notion of solution `IsSoSolution`.

The complexification of every real-analytic statement uses the same coefficients; `soVC` is not
an independent model.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-! ### Constants and coefficients -/

/-- The eccentricity `e_* = 549/10000` (rational). -/
def soEccQ : ℚ := 549 / 10000

/-- The asphericity parameter `ε_* = 69/200000` (rational). -/
def soEpsQ : ℚ := 69 / 200000

/-- The eccentricity `e_* = 549/10000`. -/
def soEcc : ℝ := 549 / 10000

/-- The asphericity parameter `ε_* = 69/200000`. -/
def soEps : ℝ := 69 / 200000

theorem soEcc_eq_ratCast : soEcc = (soEccQ : ℝ) := by
  unfold soEcc soEccQ; push_cast; norm_num

theorem soEps_eq_ratCast : soEps = (soEpsQ : ℝ) := by
  unfold soEps soEpsQ; push_cast; norm_num

theorem soEps_pos : 0 < soEps := by unfold soEps; norm_num

/-- The coefficient polynomials `A_m(e)` of proposal §2.3 (zero outside `1 ≤ m ≤ 7`). -/
def soCoeffPoly {R : Type*} [Field R] (e : R) : ℕ → R
  | 1 => -e / 4 + e ^ 3 / 32
  | 2 => 1 / 2 - 5 * e ^ 2 / 4 + 13 * e ^ 4 / 32
  | 3 => 7 * e / 4 - 123 * e ^ 3 / 32
  | 4 => 17 * e ^ 2 / 4 - 115 * e ^ 4 / 12
  | 5 => 845 * e ^ 3 / 96 - 32525 * e ^ 5 / 1536
  | 6 => 533 * e ^ 4 / 32
  | 7 => 228347 * e ^ 5 / 7680
  | _ => 0

/-- `A_m(e_*)` as a real number. -/
def soA (m : ℕ) : ℝ := soCoeffPoly soEcc m

/-- `A_m(e_*)` as an exact rational number. -/
def soAQ (m : ℕ) : ℚ := soCoeffPoly soEccQ m

theorem soA_eq_ratCast (m : ℕ) : soA m = (soAQ m : ℝ) := by
  unfold soA soAQ
  rw [soEcc_eq_ratCast]
  match m with
  | 0 => simp [soCoeffPoly]
  | 1 => simp [soCoeffPoly]
  | 2 => simp [soCoeffPoly]
  | 3 => simp [soCoeffPoly]
  | 4 => simp [soCoeffPoly]
  | 5 => simp [soCoeffPoly]
  | 6 => simp [soCoeffPoly]
  | 7 => simp [soCoeffPoly]
  | k + 8 => simp [soCoeffPoly]

/-- The index set of the seven modes. -/
def soModes : Finset ℕ := Finset.Icc 1 7

/-! ### The potential -/

/-- The period-one potential `V(q, φ) = -ε Σ_{m=1}^7 A_m(e) cos (2π (2q - mφ))`. -/
def soV (q φ : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * π * (2 * q - m * φ))

/-- The entire complex extension of `soV` (same coefficients). -/
def soVC (q φ : ℂ) : ℂ :=
  -(soEps : ℂ) * ∑ m ∈ soModes, (soA m : ℂ) * Complex.cos (2 * π * (2 * q - m * φ))

/-- `∂_q V = 4π ε Σ_{m} A_m sin (2π (2q - mφ))`. -/
def soVq (q φ : ℝ) : ℝ :=
  4 * π * soEps * ∑ m ∈ soModes, soA m * Real.sin (2 * π * (2 * q - m * φ))

/-- `∂_φ V = -2π ε Σ_{m} m A_m sin (2π (2q - mφ))`. -/
def soVφ (q φ : ℝ) : ℝ :=
  -(2 * π * soEps) * ∑ m ∈ soModes, (m : ℝ) * soA m * Real.sin (2 * π * (2 * q - m * φ))

/-- Complex extension of `soVq`. -/
def soVqC (q φ : ℂ) : ℂ :=
  4 * π * (soEps : ℂ) * ∑ m ∈ soModes, (soA m : ℂ) * Complex.sin (2 * π * (2 * q - m * φ))

/-- Complex extension of `soVφ`. -/
def soVφC (q φ : ℂ) : ℂ :=
  -(2 * π * (soEps : ℂ)) *
    ∑ m ∈ soModes, (m : ℂ) * (soA m : ℂ) * Complex.sin (2 * π * (2 * q - m * φ))

/-! ### Real on reals, periodicity, entireness -/

theorem soVC_ofReal (q φ : ℝ) : soVC q φ = (soV q φ : ℝ) := by
  simp [soVC, soV, Complex.ofReal_cos]

theorem soVqC_ofReal (q φ : ℝ) : soVqC q φ = (soVq q φ : ℝ) := by
  simp [soVqC, soVq, Complex.ofReal_sin]

theorem soVφC_ofReal (q φ : ℝ) : soVφC q φ = (soVφ q φ : ℝ) := by
  simp [soVφC, soVφ, Complex.ofReal_sin]

/-- Shifting `q` and `φ` by integers does not change the phase modulo `2π`. -/
theorem soVC_add_int (q φ : ℂ) (k l : ℤ) : soVC (q + k) (φ + l) = soVC q φ := by
  unfold soVC
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have : 2 * (π : ℂ) * (2 * (q + k) - m * (φ + l)) =
      2 * π * (2 * q - m * φ) + ((2 * k - m * l : ℤ) : ℂ) * (2 * π) := by
    push_cast; ring
  rw [this, Complex.cos_add_int_mul_two_pi]

theorem soV_add_int (q φ : ℝ) (k l : ℤ) : soV (q + k) (φ + l) = soV q φ := by
  have h := soVC_add_int q φ k l
  rw [← Complex.ofReal_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_add,
    ← Complex.ofReal_add, soVC_ofReal, soVC_ofReal] at h
  exact_mod_cast h

theorem soV_periodic_q (q φ : ℝ) : soV (q + 1) φ = soV q φ := by
  simpa using soV_add_int q φ 1 0

theorem soV_periodic_φ (q φ : ℝ) : soV q (φ + 1) = soV q φ := by
  simpa using soV_add_int q φ 0 1

theorem soVC_periodic_q (q φ : ℂ) : soVC (q + 1) φ = soVC q φ := by
  simpa using soVC_add_int q φ 1 0

theorem soVC_periodic_φ (q φ : ℂ) : soVC q (φ + 1) = soVC q φ := by
  simpa using soVC_add_int q φ 0 1

theorem soVC_differentiable : Differentiable ℂ fun z : ℂ × ℂ => soVC z.1 z.2 := by
  unfold soVC
  fun_prop

theorem soVC_differentiable_pi : Differentiable ℂ fun θ : Fin 2 → ℂ => soVC (θ 0) (θ 1) := by
  unfold soVC
  fun_prop

theorem soVC_analyticOnNhd_q (φ : ℂ) :
    AnalyticOnNhd ℂ (fun x : ℂ => soVC x φ) Set.univ :=
  fun x _ => Differentiable.analyticAt (by unfold soVC; fun_prop) x

theorem soV_differentiable : Differentiable ℝ fun z : ℝ × ℝ => soV z.1 z.2 := by
  unfold soV
  fun_prop

/-! ### Derivatives -/

/-- The derivative of the sum of cosines along a curve, shared by the real and complex cases is
proved separately below because `Real.cos` and `Complex.cos` are different functions. -/
theorem hasDerivAt_soV_comp {a b : ℝ → ℝ} {a' b' t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => soV (a s) (b s)) (soVq (a t) (b t) * a' + soVφ (a t) (b t) * b') t := by
  unfold soV soVq soVφ
  have hterm : ∀ m ∈ soModes, HasDerivAt
      (fun s => soA m * Real.cos (2 * π * (2 * a s - m * b s)))
      (soA m * (-Real.sin (2 * π * (2 * a t - m * b t)) *
        (2 * π * (2 * a' - m * b')))) t := by
    intro m _
    have hin : HasDerivAt (fun s => 2 * π * (2 * a s - m * b s)) (2 * π * (2 * a' - m * b')) t :=
      (((ha.const_mul 2).sub (hb.const_mul (m : ℝ))).const_mul (2 * π))
    exact (hin.cos).const_mul (soA m)
  have hsum := (HasDerivAt.fun_sum hterm).const_mul (-soEps)
  refine hsum.congr_deriv ?_
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem hasDerivAt_soVC_comp {a b : ℂ → ℂ} {a' b' t : ℂ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => soVC (a s) (b s))
      (soVqC (a t) (b t) * a' + soVφC (a t) (b t) * b') t := by
  unfold soVC soVqC soVφC
  have hterm : ∀ m ∈ soModes, HasDerivAt
      (fun s => (soA m : ℂ) * Complex.cos (2 * π * (2 * a s - m * b s)))
      ((soA m : ℂ) * (-Complex.sin (2 * π * (2 * a t - m * b t)) *
        (2 * π * (2 * a' - m * b')))) t := by
    intro m _
    have hin : HasDerivAt (fun s => 2 * (π : ℂ) * (2 * a s - m * b s))
        (2 * π * (2 * a' - m * b')) t :=
      (((ha.const_mul 2).sub (hb.const_mul (m : ℂ))).const_mul (2 * (π : ℂ)))
    exact (hin.ccos).const_mul (soA m : ℂ)
  have hsum := (HasDerivAt.fun_sum hterm).const_mul (-(soEps : ℂ))
  refine hsum.congr_deriv ?_
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem hasDerivAt_soV_q (q φ : ℝ) : HasDerivAt (fun x => soV x φ) (soVq q φ) q := by
  simpa using hasDerivAt_soV_comp (hasDerivAt_id q) (hasDerivAt_const q φ)

theorem hasDerivAt_soV_φ (q φ : ℝ) : HasDerivAt (fun y => soV q y) (soVφ q φ) φ := by
  simpa using hasDerivAt_soV_comp (hasDerivAt_const φ q) (hasDerivAt_id φ)

theorem hasDerivAt_soVC_q (q φ : ℂ) : HasDerivAt (fun x => soVC x φ) (soVqC q φ) q := by
  simpa using hasDerivAt_soVC_comp (hasDerivAt_id q) (hasDerivAt_const q φ)

theorem hasDerivAt_soVC_φ (q φ : ℂ) : HasDerivAt (fun y => soVC q y) (soVφC q φ) φ := by
  simpa using hasDerivAt_soVC_comp (hasDerivAt_const φ q) (hasDerivAt_id φ)

theorem deriv_soV_q (q φ : ℝ) : deriv (fun x => soV x φ) q = soVq q φ :=
  (hasDerivAt_soV_q q φ).deriv

theorem deriv_soV_φ (q φ : ℝ) : deriv (fun y => soV q y) φ = soVφ q φ :=
  (hasDerivAt_soV_φ q φ).deriv

/-! ### The physical vector field -/

/-- The physical vector field on `(q, p, φ)`: `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1`
(proposal §2.3, period-one units). -/
def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)

/-- The explicit form: `ṗ = -4π ε Σ A_m sin (2π (2q - mφ))`. -/
theorem soField_eq (x : ℝ × ℝ × ℝ) :
    soField x = (x.2.1, -soVq x.1 x.2.2, 1) := by
  simp [soField, deriv_soV_q]

theorem soVq_explicit (q φ : ℝ) :
    -soVq q φ = -4 * π * soEps * ∑ m ∈ soModes, soA m * Real.sin (2 * π * (2 * q - m * φ)) := by
  unfold soVq; ring

/-- `(q, p, φ)` is a solution of the physical spin-orbit system on all of `ℝ`
(period-one units, time `t` in orbital periods). -/
def IsSoSolution (q p φ : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt q (soField (q t, p t, φ t)).1 t ∧
    HasDerivAt p (soField (q t, p t, φ t)).2.1 t ∧ HasDerivAt φ (soField (q t, p t, φ t)).2.2 t

theorem isSoSolution_iff (q p φ : ℝ → ℝ) :
    IsSoSolution q p φ ↔ ∀ t, HasDerivAt q (p t) t ∧
      HasDerivAt p (-soVq (q t) (φ t)) t ∧ HasDerivAt φ 1 t := by
  unfold IsSoSolution
  simp only [soField_eq]

end KAM.SpinOrbit

end
