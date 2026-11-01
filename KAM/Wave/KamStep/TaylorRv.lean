/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorCommute
public import KAM.Wave.KamStep.TaylorEst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor polynomial of a Hamiltonian and its derivative (blueprint-W `bpW:w5:taylor`, step
`t-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`taylorRv P w = ∑_{k ≤ 2} (k!)⁻¹ ∂_t^k P(S_t w)|_{t=0}` is the value of the Taylor polynomial `R`
(`bpW:w5:taylor`). `hasDerivAt_taylorRv`: its derivative in a direction `W'` is the sum of the
Taylor
coefficients of `t ↦ DP(S_t w)(S_t W')`, by `hasDerivAt_taylorSum_param`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

/-- The value `R(w) = ∑_{k ≤ 2} (k!)⁻¹ ∂_t^k P(S_t w)|_{t=0}` of the Taylor polynomial. -/
def taylorRv (P : KamPhase → ℂ) (w : KamPhase) : ℂ :=
  ∑ k ∈ Finset.range 3, taylorCoeff (fun t : ℂ => P (scaleS t w)) k

theorem scaleS_add_smul (t ε : ℂ) (w W : KamPhase) :
    scaleS t (w + ε • W) = scaleS t w + ε • scaleS t W := by
  simp only [scaleS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.mk_add_mk,
    Prod.smul_mk, smul_add, smul_comm ε]

theorem taylorCoeff_congr_eventually {g h : ℂ → ℂ} (hgh : g =ᶠ[𝓝 0] h) (k : ℕ) :
    taylorCoeff g k = taylorCoeff h k := by
  simp [taylorCoeff, hgh.iteratedDeriv_eq]

/-- **Derivative of `R`** in a direction (`bpW:w5:taylor` step `t-field`): the sum of the Taylor
coefficients of `t ↦ DP(S_t w)(S_t W')`. -/
theorem hasDerivAt_taylorRv {P : KamPhase → ℂ} {V : Set KamPhase} (hV : IsOpen V)
    (hP : DifferentiableOn ℂ P V) {w W' : KamPhase} (hw0 : scaleS 0 w ∈ V) :
    HasDerivAt (fun ε : ℂ => taylorRv P (w + ε • W'))
      (∑ k ∈ Finset.range 3, taylorCoeff (fun t : ℂ => fderiv ℂ P (scaleS t w) (scaleS t W')) k)
      0 := by
  set Φ : (Fin 2 → ℂ) → ℂ := fun q => P (scaleS (q 0) w + q 1 • scaleS (q 0) W') with hΦ
  set S : Set (Fin 2 → ℂ) := {q | scaleS (q 0) w + q 1 • scaleS (q 0) W' ∈ V} with hS
  have hcont : Continuous fun q : Fin 2 → ℂ => scaleS (q 0) w + q 1 • scaleS (q 0) W' := by
    unfold scaleS; fun_prop
  have hSo : IsOpen S := hV.preimage hcont
  have h0 : (0 : Fin 2 → ℂ) ∈ S := by simpa [hS] using hw0
  have hdiff : DifferentiableOn ℂ Φ S := fun q hq => by
    have h1 : DifferentiableAt ℂ P (scaleS (q 0) w + q 1 • scaleS (q 0) W') :=
      hP.differentiableAt (hV.mem_nhds hq)
    have h2 : DifferentiableAt ℂ (fun q : Fin 2 → ℂ => scaleS (q 0) w + q 1 • scaleS (q 0) W') q :=
        by
      unfold scaleS; fun_prop
    exact (h1.comp q h2).differentiableWithinAt
  have han := analyticOnNhd_of_differentiableOn_banach hSo hdiff
  have key := hasDerivAt_taylorSum_param hSo han h0
  have eRv : (fun ε : ℂ => taylorRv P (w + ε • W')) = fun ε : ℂ => ∑ k ∈ Finset.range 3,
      taylorCoeff (fun t : ℂ => Φ (t • e0 + ε • e1)) k := by
    funext ε
    unfold taylorRv
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext t
    simp [hΦ, scaleS_add_smul, e0, e1, Pi.single_apply]
  rw [eRv]
  refine key.congr_deriv (Finset.sum_congr rfl fun k _ => ?_)
  refine taylorCoeff_congr_eventually ?_ k
  have hin : ∀ᶠ t in 𝓝 (0 : ℂ), t • e0 ∈ S := line0_eventually_mem hSo h0
  filter_upwards [hin] with t ht
  have hz : scaleS t w ∈ V := by simpa [hS, e0, Pi.single_apply] using ht
  have h1 := hasDerivAt_line (G := Φ) (q := t • e0) (v := e1) (t := 0)
    (by simpa using (han _ ht).differentiableAt)
  have h2 : HasDerivAt (fun ε : ℂ => P (scaleS t w + ε • scaleS t W'))
      (fderiv ℂ P (scaleS t w) (scaleS t W')) 0 := by
    have hl : HasDerivAt (fun ε : ℂ => scaleS t w + ε • scaleS t W') (scaleS t W') 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (scaleS t W')).const_add (scaleS t w)
    have hP' : HasFDerivAt P (fderiv ℂ P (scaleS t w)) (scaleS t w + (0 : ℂ) • scaleS t W') := by
      simpa using (hP.differentiableAt (hV.mem_nhds hz)).hasFDerivAt
    exact hP'.comp_hasDerivAt 0 hl
  have eΦ : (fun ε : ℂ => Φ (t • e0 + ε • e1)) =
      fun ε : ℂ => P (scaleS t w + ε • scaleS t W') := by
    funext ε; simp [hΦ, e0, e1, Pi.single_apply]
  rw [eΦ] at h1
  simpa using h1.unique h2

end KAM.Wave
