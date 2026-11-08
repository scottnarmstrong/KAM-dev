/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieMulti

/-!
# Multilinear reality of the Lie coefficients (blueprint-W `bpW:w3:leibniz` (iii))

Package W3-FLOW, blueprint label `bpW:w3:leibniz` (audit finding F2).

If `ρ` is a conjugate-linear isometry commuting with `T`, then on **all** ordered inputs
`Φ_k(ρ w¹, …, ρ w^{2k+1}) = ρ Φ_k(w¹, …, w^{2k+1})` (`lieMulti_rho`).
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) (ρ : E →ₛₗᵢ[starRingEnd ℂ] E)

/-- (`bpW:w3:leibniz` (iii)) Reality of the multilinear Lie coefficients on all inputs. -/
theorem lieMulti_rho (hT : ∀ v : Fin 3 → E, T (fun i => ρ (v i)) = ρ (T v)) (k : ℕ)
    (w : Fin (2 * k + 1) → E) :
    lieMulti T k (fun i => ρ (w i)) = ρ (lieMulti T k w) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp [lieMulti]
    | succ k =>
      rw [lieMulti_succ]
      simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply]
      rw [map_smulₛₗ, map_sum]
      have hc : conj ((1 : ℂ) / ((k : ℂ) + 1)) = (1 : ℂ) / ((k : ℂ) + 1) := by
        rw [map_div₀, map_one, map_add, map_natCast, map_one]
      rw [hc]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      rw [lieBlockT, dif_pos (sum_blocks hx), lieBlock_apply, lieBlock_apply]
      have e : (fun j : Fin 3 => lieMulti T (x j)
          (fun b => ρ (w (lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩)))) =
          fun j => ρ (lieMulti T (x j)
            (fun b => w (lieBlockEquiv x (2 * (k + 1) + 1) (sum_blocks hx) ⟨j, b⟩))) := by
        funext j
        exact ih (x j) (by fin_cases j <;> simp <;> omega) _
      rw [e, hT]

end KAM.Wave

end
