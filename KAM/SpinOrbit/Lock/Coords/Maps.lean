/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Rotated
public import KAM.SpinOrbit.Hamiltonian

/-!
# SO-LOCK coordinates: the real maps

Design SO-LOCK §3 (corrected after audit F3). On `z = ((α, φ), (I, J̃))`, with a centre curve `c`
and `Ω > 0`:

* `libAction Ω ψ (q, p, φ) = π(Ω X² + Y²/Ω)`, `X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`;
* `lockX`, `lockY`: the polar pieces `X = √(I/(πΩ)) sin 2πα`, `Y = √(IΩ/π) cos 2πα`
  (`dY ∧ dX = dI ∧ dα`);
* `lockToRotR`: the map to the landed rotated frame (`soRotMap` then maps to physical);
* `lockToPhysicalR`: the physical projection `(φ + c + X, 1 + c′ + Y, φ)`, `lockToPhysicalR_eq`;
* `lockHamiltonianR`: `K = H′ ∘ lockToRotR`;
* `lockCentre`: the rational sine centre, `lockCentre_contDiff`; `lunarLockCentre`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

/-- The elliptic libration action around a curve `ψ`: `π(Ω X² + Y²/Ω)` with
`X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

/-- Real polar pieces: `X = √(I/(πΩ)) sin 2πα`, `Y = √(IΩ/π) cos 2πα` on `z = ((α, φ), (I, J̃))`.
Two-form: `dY ∧ dX = dI ∧ dα` (frozen convention `Σ dIᵢ ∧ dθᵢ`). -/
def lockX (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0)

/-- The momentum polar piece `Y = √(IΩ/π) cos 2πα`. -/
def lockY (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0)

/-- To the landed rotated frame `((Q₀, Q₁), (P₀, P₁))` (`soRotMap` then goes to physical):
`Q₀ = c + X`, `Q₁ = φ`, `P₀ = 1 + c′ + Y`, `P₁ = J̃ − c′(c′ + Y) + X c″`. -/
def lockToRotR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (![c (z.1 1) + lockX Ω z, z.1 1],
   ![1 + deriv c (z.1 1) + lockY Ω z,
     z.2 1 - deriv c (z.1 1) * (deriv c (z.1 1) + lockY Ω z) +
       lockX Ω z * deriv (deriv c) (z.1 1)])

/-- Physical projection `(q, p, φ)` (= `soRotMap ∘ lockToRotR` without the clock action). -/
def lockToPhysicalR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  (z.1 1 + c (z.1 1) + lockX Ω z, 1 + deriv c (z.1 1) + lockY Ω z, z.1 1)

/-- `K = H′ ∘ lockToRotR`. -/
def lockHamiltonianR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  z.2 1 + (lockY Ω z) ^ 2 / 2 - (deriv c (z.1 1)) ^ 2 / 2 +
    lockX Ω z * deriv (deriv c) (z.1 1) + soV (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1) - 1 / 2

theorem lockToPhysicalR_eq (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    lockToPhysicalR Ω c z =
      ((lockToRotR Ω c z).1 0 + (lockToRotR Ω c z).1 1, (lockToRotR Ω c z).2 0,
        (lockToRotR Ω c z).1 1) := by
  simp only [lockToPhysicalR, lockToRotR, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ring

/-- `K` is the real rotated Hamiltonian `soHR ∘ soRotMap` (real form of `soRotHC`) composed with
`lockToRotR`: `P₀²/2 − P₀ + P₁ + V(Q₀ + Q₁, Q₁)`. -/
theorem lockHamiltonianR_eq (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    lockHamiltonianR Ω c z =
      (lockToRotR Ω c z).2 0 ^ 2 / 2 - (lockToRotR Ω c z).2 0 + (lockToRotR Ω c z).2 1 +
        soV ((lockToRotR Ω c z).1 0 + (lockToRotR Ω c z).1 1) ((lockToRotR Ω c z).1 1) := by
  simp only [lockHamiltonianR, lockToRotR, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show c (z.1 1) + lockX Ω z + z.1 1 = z.1 1 + c (z.1 1) + lockX Ω z by ring]
  ring

/-! ### The rational sine centre -/

/-- The rational sine centre `c(φ) = Σ_k cs_k sin 2π(k+1)φ`. -/
def lockCentre (cs : List ℚ) (φ : ℝ) : ℝ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℝ) * Real.sin (2 * π * (k + 1) * φ)).sum

/-- LOCK-GEN-1 centre: `−3/250000 sin 2πφ − 699/2000000000 sin 4πφ − 883/50000000000 sin 6πφ`. -/
def lunarLockCentre : List ℚ := [-3 / 250000, -699 / 2000000000, -883 / 50000000000]

theorem contDiff_list_sum_map {g : ℕ → ℝ → ℝ} (hg : ∀ k, ContDiff ℝ ⊤ (g k)) (l : List ℕ) :
    ContDiff ℝ ⊤ fun φ => (l.map fun k => g k φ).sum := by
  induction l with
  | nil => simpa using contDiff_const
  | cons k l ih => simpa using (hg k).add ih

theorem lockCentre_contDiff (cs : List ℚ) : ContDiff ℝ ⊤ (lockCentre cs) :=
  contDiff_list_sum_map (fun _ => contDiff_const.mul
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))) _

end KAM.SpinOrbit.Lock

end
