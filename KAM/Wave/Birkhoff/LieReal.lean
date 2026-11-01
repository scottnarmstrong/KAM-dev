/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieFlow3

/-!
# Reality of the flow (blueprint-W `bpW:w3:flow` (iv), `bpW:w3:leibniz` (iii))

Package W3-FLOW, blueprint labels `bpW:w3:flow`, `bpW:w3:leibniz`.

If `ρ` is a conjugate-linear continuous involution-like map commuting with `T`
(`T(ρ v) = ρ T(v)`), then `φ_k(ρ w) = ρ φ_k(w)` (`lieSeq_rho`) and, for real `t`,
`Γ_t(ρ w) = ρ Γ_t(w)` (`lieGamma_rho`).
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) (ρ : E →ₛₗᵢ[starRingEnd ℂ] E)

theorem lieSeq_rho (hT : ∀ v : Fin 3 → E, T (fun i => ρ (v i)) = ρ (T v)) (w : E) (k : ℕ) :
    lieSeq T (ρ w) k = ρ (lieSeq T w k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [lieSeq_succ, lieSeq_succ, map_smulₛₗ, map_sum]
      have hc : conj ((1 : ℂ) / ((k : ℂ) + 1)) = (1 : ℂ) / ((k : ℂ) + 1) := by
        rw [map_div₀, map_one, map_add, map_natCast, map_one]
      rw [hc]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
      simp only [Fin.sum_univ_three] at hx'
      have h0 : x 0 < k + 1 := by omega
      have h1 : x 1 < k + 1 := by omega
      have h2 : x 2 < k + 1 := by omega
      have e : (![lieSeq T (ρ w) (x 0), lieSeq T (ρ w) (x 1), lieSeq T (ρ w) (x 2)] : Fin 3 → E) =
          fun i => ρ (![lieSeq T w (x 0), lieSeq T w (x 1), lieSeq T w (x 2)] i) := by
        funext i
        fin_cases i
        · exact ih _ h0
        · exact ih _ h1
        · exact ih _ h2
      rw [e, hT]

variable [CompleteSpace E] {C : ℝ} (hC : 0 ≤ C) (hT' : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT' in
theorem lieGamma_rho (hT : ∀ v : Fin 3 → E, T (fun i => ρ (v i)) = ρ (T v)) (t : ℝ) (w : E)
    (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    lieGamma T t (ρ w) = ρ (lieGamma T t w) := by
  have hr : ∀ (r : ℝ) (x : E), ρ (r • x) = r • ρ x := fun r x => by
    rw [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
  let ρR : E →L[ℝ] E :=
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := hr
      cont := ρ.continuous }
  have hs := summable_lieTerm T hC hT' t w hq
  unfold lieGamma
  have := ρR.map_tsum hs
  simp only [ρR, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] at this
  refine Eq.trans (tsum_congr fun k => ?_) this.symm
  rw [lieSeq_rho T ρ hT, hr]

end KAM.Wave

end
