/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep.Remainder
public import KAM.EffectiveStability.OscillatorStep.Drift
public import KAM.EffectiveStability.Cauchy
public import KAM.EffectiveStability.Domains

/-!
# Torus one-step normalization: the angle-derivative bound (track B, B4-TSTEP)

* `ftActOnly`: Boolean check that every monomial has `k = 0`, `e = 0`, `s = 0` (a polynomial in
  the actions only); `ftEvalR_actOnly` says its value does not depend on the angles.
* `torusRemainder_eq`: the chart remainder `R = H ∘ Ψ - N` is `P + Re Rem ∘ ι` on the real half
  interior (exact Lie-sum identity).
* `torusDrift_le`: `|∂_{φ_j} R (x)| ≤ η j` on the closed cylinder, from the angle-drift majorant
  of `P` and the Cauchy estimate for `Rem`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical Filter
open scoped Topology

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- Boolean check: every monomial has `k = 0`, `e = 0`, `s = 0`. -/
def ftActOnly (P : FTPoly) : Bool :=
  P.all fun m => m.k.all (fun a => decide (a = 0)) && decide (m.e = 0) && decide (m.s = 0)

private theorem getD_zero_of_all {k : List ℤ} (h : k.all (fun a => decide (a = 0)) = true)
    (i : ℕ) : k.getD i 0 = 0 := by
  by_cases hi : i < k.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    have := List.all_eq_true.1 h _ (List.getElem_mem hi)
    simpa using this
  · exact ftGetD_zero_of_length_le k i (not_lt.1 hi)

/-- An actions-only polynomial does not depend on the angles. -/
theorem ftEvalR_actOnly {P : FTPoly} (h : ftActOnly P = true) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR P x = ftEvalR P ((0 : Fin n → ℝ), x.2) := by
  induction P with
  | nil => simp [ftEvalR]
  | cons m P ih =>
    have h' := List.all_eq_true.1 h
    have hm := h' m (List.mem_cons_self)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨⟨hk, he⟩, hs⟩ := hm
    have hP : ftActOnly P = true :=
      List.all_eq_true.2 fun m' hm' => h' m' (List.mem_cons_of_mem _ hm')
    have ph : ftPhase m.k x.1 = 0 := by
      simp only [ftPhase, getD_zero_of_all hk, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    have ph0 : ftPhase m.k (0 : Fin n → ℝ) = 0 := by
      simp [ftPhase]
    simp only [ftEvalR, ftEvalG_cons] at ih ⊢
    rw [ih hP]
    simp [ftMonoEvalG, ph, ph0, he, hs]

/-- The chart remainder `R = H ∘ Ψ - N` is `P + Re Rem ∘ ι` on the real half interior. -/
theorem torusRemainder_eq {χ H Nact P : FTPoly} (hA : ftActOnly Nact = true) {L : ℕ}
    {σ ρ σ' ρ' ε : ℝ} {hσ' : 0 < σ'} {hρ' : 0 < ρ'}
    (hid : ftEqCheck (ftLieSum χ H L) (ftAdd Nact P) = true)
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {y : (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : y ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    ftEvalR H (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) 1 y) -
        ftEvalR Nact ((0 : Fin n → ℝ), y.2) =
      ftEvalR P y + (torusRem χ H σ ρ L (KAM.realInclusion₂ n y)).re := by
  rw [torusRem_realInclusion₂ hS L hy, Complex.ofReal_re]
  have h := ftEvalR_eq_of_eqCheck hid y
  rw [ftEvalR_add, ftEvalR_actOnly hA y] at h
  rw [h]
  ring

/-- **Angle-derivative bound** for the chart remainder at a real point of the closed cylinder. -/
theorem torusDrift_le {χ H Nact P : FTPoly} (hχ : FTFits n χ) (hH : FTFits n H)
    (hP : FTFits n P) (hA : ftActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    {σ ρ σ' ρ' δc ε : ℝ} {hσ' : 0 < σ'} {hρ' : 0 < ρ'} (hδc : 0 < δc)
    (hid : ftEqCheck (ftLieSum χ H L) (ftAdd Nact P) = true)
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {πub lam : ℚ} (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hlam : 0 < lam)
    (hσ : σ ≤ Real.log lam / (2 * Real.pi))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (bl : List ℚ) (b r η : Fin n → ℝ) (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i)
    (hbr : ∀ i, b i ≤ r i) (hσc : δc + σ' / 2 < σ) (hr3 : ∀ i, r i + δc + ρ' / 2 < ρ)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j πub bl : ℚ) : ℝ) +
      ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) / ((L.factorial : ℝ) * δc) ≤ η j)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ j, |x.2 j| ≤ b j)
    (hxI : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) (j : Fin n) :
    |fderiv ℝ (fun w => ftEvalR H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) 1 w) -
        ftEvalR Nact ((0 : Fin n → ℝ), w.2)) x (Pi.single j 1, 0)| ≤ η j := by
  set B : ℝ := ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) with hB
  set U := gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) with hU
  have hUo : IsOpen U := isOpen_gaugeInterior hS.isOpen _ _
  have hdiffR := differentiableOn_torusRem (χ := χ) (H := H) hS L
  have hxU : KAM.realInclusion₂ n x ∈ U := hxI
  have hev : (fun w => ftEvalR H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) 1 w) -
        ftEvalR Nact ((0 : Fin n → ℝ), w.2)) =ᶠ[𝓝 x]
      fun y => ftEvalR P y + (torusRem χ H σ ρ L (KAM.realInclusion₂ n y)).re := by
    filter_upwards [(isOpen_realInterior hS.isOpen (1 / 2)).mem_nhds hxI] with y hy
    exact torusRemainder_eq hA hid hS hy
  have hdP : DifferentiableAt ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P y) x :=
    ((ftEvalR_contDiff P 1).differentiable one_ne_zero).differentiableAt
  have hdRe := differentiableAt_realPart hUo hdiffR hxU
  rw [hev.fderiv_eq, fderiv_fun_add hdP hdRe]
  simp only [add_apply]
  have hpoly := abs_fderiv_ftEvalR_le P hP bl hπ x (fun i => by rw [hbl]; exact hx i) j
  have hxr : ∀ i, |x.2 i| ≤ r i := fun i => (hx i).trans (hbr i)
  have hsub : cpolydisc (KAM.realInclusion₂ n x) δc ⊆ U :=
    cauchyDisc_subset_gaugeInterior_strip hρ' hσ' hσc hr3 hxr
  have hM : ∀ w ∈ cpolydisc (KAM.realInclusion₂ n x) δc,
      ‖torusRem χ H σ ρ L w‖ ≤ B / (L.factorial : ℝ) := fun w hw =>
    norm_torusRem_le hχ hH hS hπ hlam hσ ρl hρl hL (hsub hw)
  have hcau := abs_fderiv_realPart_fst_le hUo hdiffR hxU hδc hsub hM j
  have e : B / (L.factorial : ℝ) / δc = B / ((L.factorial : ℝ) * δc) := by rw [div_div]
  rw [e] at hcau
  have := hdrift j
  exact (abs_add_le _ _).trans (by linarith)

end KAM.EffectiveStability
