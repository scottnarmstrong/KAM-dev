/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Coords.Maps
public import KAM.Certificate.Expr.Sqrt

/-!
# SO-LOCK coordinates: the complexified map

Design SO-LOCK §3 (complex side). The rational sine centre and its first two derivatives are
written as explicit sine/cosine sums (`lockCentreC`, `lockCentreDC`, `lockCentreDDC`), not via
`deriv`; the polar pieces use the total square root `sqrtE`.

* `lockToRotC`: the complexified map to the rotated frame;
* `hasDerivAt_lockCentre_lockCentreD`, `deriv_lockCentre`, `deriv_deriv_lockCentre`: the real
  centre's derivatives are the real sums `lockCentreD`, `lockCentreDD`;
* `lockToRotC_ofReal`: at real points (`0 < Ω`, `0 < I`) it is `lockToRotR (lockCentre cs)`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

open KAM.Certificate

/-- The complexified centre `c(φ) = Σ_k cs_k sin 2π(k+1)φ`. -/
def lockCentreC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℂ) * Complex.sin (2 * π * (k + 1) * φ)).sum

/-- The complexified `c′(φ) = Σ_k cs_k 2π(k+1) cos 2π(k+1)φ`. -/
def lockCentreDC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℂ) * (2 * π * (k + 1)) * Complex.cos (2 * π * (k + 1) * φ)).sum

/-- The complexified `c″(φ) = −Σ_k cs_k (2π(k+1))² sin 2π(k+1)φ`. -/
def lockCentreDDC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    -((cs.getD k 0 : ℚ) : ℂ) * (2 * π * (k + 1)) ^ 2 * Complex.sin (2 * π * (k + 1) * φ)).sum

/-- Complexified map to the rotated frame (uses `sqrtE`; equals `lockToRotR` at real points with
`I > 0`). -/
def lockToRotC (Ω : ℚ) (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  let X := sqrtE (z.2 0 / (π * (Ω : ℂ))) * Complex.sin (2 * π * z.1 0)
  let Y := sqrtE (z.2 0 * (Ω : ℂ) / π) * Complex.cos (2 * π * z.1 0)
  (![lockCentreC cs (z.1 1) + X, z.1 1],
   ![1 + lockCentreDC cs (z.1 1) + Y,
     z.2 1 - lockCentreDC cs (z.1 1) * (lockCentreDC cs (z.1 1) + Y) +
       X * lockCentreDDC cs (z.1 1)])

/-! ### Real derivatives of the centre -/

/-- The real `c′`. -/
def lockCentreD (cs : List ℚ) (φ : ℝ) : ℝ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℝ) * (2 * π * (k + 1)) * Real.cos (2 * π * (k + 1) * φ)).sum

/-- The real `c″`. -/
def lockCentreDD (cs : List ℚ) (φ : ℝ) : ℝ :=
  ((List.range cs.length).map fun k =>
    -((cs.getD k 0 : ℚ) : ℝ) * (2 * π * (k + 1)) ^ 2 * Real.sin (2 * π * (k + 1) * φ)).sum

theorem hasDerivAt_lockSum {f f' : ℕ → ℝ → ℝ} (hf : ∀ k φ, HasDerivAt (f k) (f' k φ) φ)
    (l : List ℕ) (φ : ℝ) :
    HasDerivAt (fun x => (l.map fun k => f k x).sum) ((l.map fun k => f' k φ).sum) φ := by
  induction l with
  | nil => simpa using hasDerivAt_const φ (0 : ℝ)
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf k φ).add ih

theorem hasDerivAt_lockCentre_lockCentreD (cs : List ℚ) (φ : ℝ) :
    HasDerivAt (lockCentre cs) (lockCentreD cs φ) φ := by
  unfold lockCentre lockCentreD
  refine hasDerivAt_lockSum
    (f := fun k x => ((cs.getD k 0 : ℚ) : ℝ) * Real.sin (2 * π * (k + 1) * x))
    (f' := fun k x => ((cs.getD k 0 : ℚ) : ℝ) * (2 * π * (k + 1)) * Real.cos (2 * π * (k + 1) * x))
    (fun k φ => ?_) _ φ
  have h := ((hasDerivAt_id' φ).const_mul (2 * π * (k + 1))).sin.const_mul
    ((cs.getD k 0 : ℚ) : ℝ)
  convert h using 1
  ring

theorem hasDerivAt_lockCentreD (cs : List ℚ) (φ : ℝ) :
    HasDerivAt (lockCentreD cs) (lockCentreDD cs φ) φ := by
  unfold lockCentreD lockCentreDD
  refine hasDerivAt_lockSum
    (f := fun k x => ((cs.getD k 0 : ℚ) : ℝ) * (2 * π * (k + 1)) * Real.cos (2 * π * (k + 1) * x))
    (f' := fun k x =>
      -((cs.getD k 0 : ℚ) : ℝ) * (2 * π * (k + 1)) ^ 2 * Real.sin (2 * π * (k + 1) * x))
    (fun k φ => ?_) _ φ
  have h := ((hasDerivAt_id' φ).const_mul (2 * π * (k + 1))).cos.const_mul
    ((cs.getD k 0 : ℚ) * (2 * π * (k + 1)))
  convert h using 1
  ring

theorem deriv_lockCentre (cs : List ℚ) : deriv (lockCentre cs) = lockCentreD cs :=
  funext fun φ => (hasDerivAt_lockCentre_lockCentreD cs φ).deriv

theorem deriv_lockCentreD (cs : List ℚ) : deriv (lockCentreD cs) = lockCentreDD cs :=
  funext fun φ => (hasDerivAt_lockCentreD cs φ).deriv

theorem deriv_deriv_lockCentre (cs : List ℚ) :
    deriv (deriv (lockCentre cs)) = lockCentreDD cs := by
  rw [deriv_lockCentre, deriv_lockCentreD]

/-! ### Agreement at real points -/

theorem ofReal_list_sum_map (f : ℕ → ℝ) (l : List ℕ) :
    (((l.map f).sum : ℝ) : ℂ) = (l.map fun k => (f k : ℂ)).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simp [ih]

/-- `sqrtE` of a real number is the cast of its real square root (both vanish for `x ≤ 0`). -/
theorem sqrtE_ofReal_eq (x : ℝ) : sqrtE (x : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
  by_cases hx : x ≤ 0
  · simp [sqrtE, hx, Real.sqrt_eq_zero'.2 hx]
  · push Not at hx
    have hc : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by simp [hx.not_ge]
    simp only [sqrtE, hc, ↓reduceIte]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    norm_num

theorem lockCentreC_ofReal (cs : List ℚ) (φ : ℝ) :
    lockCentreC cs (φ : ℂ) = ((lockCentre cs φ : ℝ) : ℂ) := by
  rw [lockCentreC, lockCentre, ofReal_list_sum_map]
  refine congrArg List.sum <| List.map_congr_left fun k _ => ?_
  push_cast
  rfl

theorem lockCentreDC_ofReal (cs : List ℚ) (φ : ℝ) :
    lockCentreDC cs (φ : ℂ) = ((lockCentreD cs φ : ℝ) : ℂ) := by
  rw [lockCentreDC, lockCentreD, ofReal_list_sum_map]
  refine congrArg List.sum <| List.map_congr_left fun k _ => ?_
  push_cast
  rfl

theorem lockCentreDDC_ofReal (cs : List ℚ) (φ : ℝ) :
    lockCentreDDC cs (φ : ℂ) = ((lockCentreDD cs φ : ℝ) : ℂ) := by
  rw [lockCentreDDC, lockCentreDD, ofReal_list_sum_map]
  refine congrArg List.sum <| List.map_congr_left fun k _ => ?_
  push_cast
  rfl

theorem lockToRotC_ofReal {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hI : 0 < z.2 0) :
    lockToRotC Ω cs ((fun i => (z.1 i : ℂ)), (fun i => (z.2 i : ℂ))) =
      ((fun i => ((lockToRotR Ω (lockCentre cs) z).1 i : ℂ)),
        (fun i => ((lockToRotR Ω (lockCentre cs) z).2 i : ℂ))) := by
  have _ := hΩ
  have _ := hI
  have hX : sqrtE ((z.2 0 : ℂ) / (π * ((Ω : ℚ) : ℂ))) * Complex.sin (2 * π * (z.1 0 : ℂ)) =
      ((lockX Ω z : ℝ) : ℂ) := by
    rw [lockX, show ((z.2 0 : ℂ) / (π * ((Ω : ℚ) : ℂ))) = ((z.2 0 / (π * (Ω : ℝ)) : ℝ) : ℂ) by
      push_cast; rfl, sqrtE_ofReal_eq]
    push_cast
    rfl
  have hY : sqrtE ((z.2 0 : ℂ) * ((Ω : ℚ) : ℂ) / π) * Complex.cos (2 * π * (z.1 0 : ℂ)) =
      ((lockY Ω z : ℝ) : ℂ) := by
    rw [lockY, show ((z.2 0 : ℂ) * ((Ω : ℚ) : ℂ) / π) = ((z.2 0 * (Ω : ℝ) / π : ℝ) : ℂ) by
      push_cast; rfl, sqrtE_ofReal_eq]
    push_cast
    rfl
  simp only [lockToRotC, hX, hY, lockToRotR, deriv_lockCentre, deriv_lockCentreD,
    lockCentreC_ofReal, lockCentreDC_ofReal, lockCentreDDC_ofReal]
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp

end KAM.SpinOrbit.Lock

end
