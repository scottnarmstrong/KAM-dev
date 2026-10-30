/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.MirrorQRef
public import KAM.Sharp2.Examples.PlasmaLean
public import KAM.Sharp2.RouteA.Ref.G1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The certified threshold at PlasmaLean's data with lever L8′

The same hypotheses `CALike` and the same certificates as `plasmaLean_torus`, with the torsion
against the initial torus (`KAM.Sharp2.RouteA.Ref`): `plasmaLean_torus'` raises the certified
threshold from `1.93·10⁻¹⁷` to `3.72·10⁻¹⁷ = 10^{-16.43}`, which is 65 times PlasmaLean's tolerance
`5.7·10⁻¹⁹`.

`L8.cALike_coreR` is `KAM.Sharp2.RouteA.Ref.g1_branch_R` at the cA-like data, with the rational test
`okR` and the budgets `Ref.Budget`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.Examples

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

namespace L8

/-- The rational caps, with the budget `bT` of `𝒯_ab`. -/
def capQ (V : CAVar) (bT : ℚ) : Fin 7 → ℚ :=
  ![1 / 320, 993 / 320, V.sB, bT, V.sLt, V.sN, V.sNt]

/-- The rational initial cap values. -/
def m0Q : Fin 7 → ℚ := ![0, 31 / 10, 2, 0, 62 / 5, 31 / 5, 124 / 5]

theorem capR_eq (V : CAVar) (bT : ℚ) :
    V.numA.capR ((1 / 160) / 2) bT = fun i => (capQ V bT i : ℝ) := by
  funext i
  fin_cases i <;> norm_num [NumA.capR, CAVar.numA, capQ]

theorem initR_eq :
    initR caInit (31 / 10 + 1 / 160) (2 + 1 / 160) (1 / 160) = fun i => (m0Q i : ℝ) := by
  funext i
  fin_cases i <;> norm_num [initR, caInit, m0Q]

open CAVar in
/-- The core theorem at the cA-like data, with the torsion against the initial torus. -/
theorem cALike_coreR (V : CAVar) (hV : V.numA.Wf) {Xs bF bT : ℚ} (hXs : 0 < Xs)
    (hok : V.numQ.okR bF (capQ V bT) m0Q Xs = true)
    (hB : Ref.Budget V.numA (50 / 11) (496 / 25) (bF : ℝ) (bT : ℝ))
    {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))} {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ}
    {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {ω : Fin 2 → ℝ} {Ω : Set (Fin 2 → ℝ)} {γ e : ℝ}
    (hO : CALike 𝔅 h K ω) (hω : ω ∈ Ω) (hCt : V.numA.Cert γ Ω) (hγ : 0 < γ)
    (hγb : γ ≤ 687 / 5000) (hdio : IsDiophantine γ 1 ω)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * (333 / 100000) ^ 4) < Xs) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤
        (V.numQ.sumD Xs : ℝ) / ((Xs : ℝ) * (333 / 100000) ^ 4 * γ ^ 2) * e := by
  have hρ0 : (0 : ℝ) < 1 / 50 := by norm_num
  have hXpos : (0 : ℝ) < Xs := by exact_mod_cast hXs
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hOk := NumQ.okR_sound hok
  rw [V.numQ_toA, show (fun i => (m0Q i : ℝ)) = _ from initR_eq.symm,
    show (fun i => (capQ V bT i : ℝ)) = _ from (capR_eq V bT).symm] at hOk
  have hSv : Standing 2 1 3 (31 / 10 + 1 / 160) (2 + 1 / 160) (50 / 11 + 1 / 160) 𝔅 h ω γ :=
    { toParams := ⟨le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      isOpen := hO.isOpen
      transl_mem := hO.transl
      holo := hO.holo
      periodic := hO.periodic
      real := hO.real
      bounds := fun z hz => (hO.bounds z hz).2
      gamma_pos := hγ
      dio := hdio }
  have hK𝔅 : ∀ θ ∈ complexStrip 2 (1 / 50), K θ ∈ 𝔅 := fun θ hθ =>
    hO.ball θ hθ (Metric.mem_ball_self (by norm_num))
  have hGn : ∀ θ ∈ complexStrip 2 (1 / 50), ‖(gramMatrix K θ)⁻¹‖ ≤ 2 := fun θ hθ =>
    norm_le_of_rowSum_le le_rfl (hO.gram θ hθ).2
  have hfb : ∀ θ ∈ complexStrip 2 (1 / 50), _ := fun θ hθ =>
    frame_bounds hSv (hK𝔅 θ hθ) (hO.deriv_le θ hθ) (hO.gram θ hθ).1 (hGn θ hθ) ω
  have hδ0 : V.numA.δ 0 = 333 / 100000 := by
    rw [V.numA_δ]
    norm_num
  have hRef : RefHypA V.numA caInit 𝔅 h K ω :=
    { dX := fun z hz => (hO.bounds z hz).2.2.1
      d2X := fun z hz => (hO.bounds z hz).2.2.2
      tangentT := fun θ hθ => (hfb θ hθ).2.1.trans_eq (by norm_num [caInit])
      normal := fun θ hθ => (hfb θ hθ).2.2.1.trans_eq (by norm_num [caInit])
      normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1.trans_eq (by norm_num [caInit])
      tors := fun θ hθ => hO.torsion_le θ (by
        have e1 : V.numA.ρ - V.numA.δ 0 = 1 / 50 - 333 / 100000 := by rw [hδ0]; rfl
        rw [← e1]
        exact hθ) }
  have hsm' : e / (γ ^ 4 * Engine.delta0 3 V.numA.ρ V.numA.ρinf ^ (2 * (2 * V.numA.τ))) < Xs := by
    rw [V.delta0_eq, show 2 * (2 * V.numA.τ) = ((4 : ℕ) : ℝ) by
      show 2 * (2 * (1 : ℝ)) = _
      norm_num, Real.rpow_natCast]
    exact hsm
  have hB' : Ref.Budget V.numA ((50 / 11 + 1 / 160) - 1 / 160) caInit.iH (bF : ℝ) (bT : ℝ) := by
    rw [show ((50 / 11 + 1 / 160) - 1 / 160 : ℝ) = 50 / 11 by norm_num]
    exact hB
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := Ref.g1_branch_R (N := V.numA) (M := 3)
    (σK := 31 / 10 + 1 / 160) (σB := 2 + 1 / 160) (σT := 50 / 11 + 1 / 160) (μ := 1 / 160)
    (γbar := 687 / 5000) (Xs := Xs) (I := caInit) hV rfl rfl (by norm_num [numA]) (by norm_num)
    (by norm_num) rfl (by norm_num [numA]) hOk hB' hXpos hO.isOpen hO.transl hO.holo hO.periodic
    hO.real hO.bounds hO.torus_holo hO.primary hO.torus_real
    hO.ball (fun θ hθ => (hO.deriv_le θ hθ).trans_eq (by norm_num))
    (fun θ hθ => ⟨(hO.gram θ hθ).1, fun i => ((hO.gram θ hθ).2 i).trans_eq (by norm_num)⟩)
    hO.twist_unit (fun i => (hO.twist_le i).trans_eq (by norm_num)) hRef hω hCt hγ hγb hdio he0 hE
    hsm'
  refine ⟨Kinf, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · intro θ hθ
    have := h5 θ hθ
    rwa [show (1 / 160 / 2 : ℝ) = 1 / 320 by norm_num] at this
  · intro θ hθ
    exact (h6 θ hθ).trans_eq (by norm_num)
  · intro θ hθ
    refine (h7 θ hθ).trans_eq ?_
    rw [V.rho_pow, V.c2A_eq]
    field_simp

/-- The run: the certified constants of `freqVar`, the caps of L8′. -/
def var : CAVar where
  sB := 20002 / 10000
  sT := 54 / 10
  sLt := 124002 / 10000
  sN := 62004 / 10000
  sNt := 248010 / 10000
  t := 19875 / 1000
  th := 1 / 100
  c := freqC
  cbar := freqCbar
  ctail := 8144 / 100000
  kp := 3

/-- The threshold of the normalised error. -/
def Xs : ℚ := 85 / 100000

/-- The bound of the local part of the torsion. -/
def bF : ℚ := 1 / 10 ^ 6

/-- The budget of `𝒯_ab`. -/
def bT : ℚ := 348 / 10000

theorem var_ok : var.numQ.okR bF (capQ var bT) m0Q Xs = true := by decide +kernel

theorem var_close :
    var.numQ.sumD Xs / (Xs * (333 / 100000) ^ 4 * gammaStar ^ 2) ≤ 20269337 := by
  decide +kernel

theorem var_wf : var.numA.Wf := by
  refine CAVar.wf _ (by norm_num [var]) (by norm_num [var]) (by norm_num [var])
    (by norm_num [var]) (by norm_num [var]) (by norm_num [var]) (by norm_num [var])
    (by norm_num [var]) (fun s => ?_) (fun s => ?_) (by norm_num [var])
  · rcases s with _ | _ | s <;> norm_num [var, freqC]
  · rcases s with _ | _ | s <;> norm_num [var, freqCbar]

theorem var_budget : Ref.Budget var.numA (50 / 11) (496 / 25) (bF : ℝ) (bT : ℝ) where
  mT_pos := by norm_num
  mT_lt := by norm_num [var, CAVar.numA]
  beta := by norm_num [var, CAVar.numA, bF, bT]
  sup := by norm_num [var, CAVar.numA, bF, bT]

/-- The certificates of `freqVar`: they depend on the schedule and the constants alone. -/
theorem var_cert : var.numA.Cert (gammaStar : ℝ) ({omegaStar} : Set (Fin 2 → ℝ)) :=
  ⟨freqVar_cert.stage, freqVar_cert.bar, freqVar_cert.tail⟩

end L8

/-- **PlasmaLean's frequency and strip, certified, with lever L8′.** The statement of
`plasmaLean_torus`, at `e ≤ 3.72·10⁻¹⁷`. -/
theorem plasmaLean_torus' {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {e : ℝ}
    (hO : CALike 𝔅 h K omegaStar)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K omegaStar θ‖ ≤ e)
    (he : e ≤ 372 / 10 ^ 19) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤ 20269337 * e := by
  have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have hXs : (0 : ℚ) < L8.Xs := by norm_num [L8.Xs]
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hsm : e / ((gammaStar : ℝ) ^ 4 * (333 / 100000) ^ 4) < (L8.Xs : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    refine he.trans_lt ?_
    norm_num [gammaStar, L8.Xs]
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := L8.cALike_coreR L8.var L8.var_wf hXs L8.var_ok
    L8.var_budget hO (Set.mem_singleton _) L8.var_cert hγ (by norm_num [gammaStar])
    isDiophantine_omegaStar hE hsm
  refine ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ he0
  have : ((L8.var.numQ.sumD L8.Xs / (L8.Xs * (333 / 100000) ^ 4 * gammaStar ^ 2) : ℚ) : ℝ) ≤
      ((20269337 : ℚ) : ℝ) := Rat.cast_le.mpr L8.var_close
  push_cast at this
  exact this

end KAM.Sharp2.Examples

end
