/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean
public import KAM.Sharp2.Examples.PlasmaLean.GammaInf
public import KAM.Sharp2.Examples.MirrorL1
public import KAM.Sharp2.L1.G1A
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# PlasmaLean's frequency and strip with the ℓ¹ entry (package B10c)

`plasmaLean_torus_l1`: the closed theorem `KAM.Sharp2.Examples.plasmaLean_torus` with the ℓ¹ entry
step of route A (`KAM.Sharp2.L1.g1_branch_AL1`). Every canonical analytic flow and approximate torus
with the bounds `CALike`, the ℓ¹ data `CAL1Like` and invariance error `‖E‖ ≤ e ≤ 9.4·10⁻¹⁶` has a
true invariant torus nearby. This is `10^{-15.03}`, against `10^{-16.71}` of the sup run.

`CAL1Like h K e` is a structure of explicit ℓ¹ bounds of the torus, nothing else; its numbers are
the design's reading (a) of PlasmaLean's declared bounds as ℓ¹ bounds:
`‖ηᴺ‖_{1,ρ} ≤ 12.4 e`, `‖ηᴸ‖_{1,ρ} ≤ 24.8 e` (the caps of `Lᵀ`, `Nᵀ` times `e`),
`‖T‖_{1,ρ-δ₀} ≤ 19.84`, `|T| ≤ 19.84` on `ℝⁿ`, `‖L‖_{1,ρ} ≤ 3.1`, `‖N‖_{1,ρ} ≤ 6.2`. These are
assumed data: nothing here establishes them for PlasmaLean's torus, whose field is not canonical
(AUDIT-B10D-1, F7). The small-divisor constants `Γ_∞(ω*, δ₀) ≤ 5.51`, `Γ_∞(ω*, ρ) ≤ 1.54` are
certified (`gammaInf_d0`, `gammaInf_rho`); the sup constants are those of `Bites`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.Examples

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA KAM.Sharp2.L1

/-- The ℓ¹ data of the torus at `ω*`, relative to the invariance bound `e` (assumed data). -/
structure CAL1Like (h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (e : ℝ) : Prop where
  l1EtaN : L1Vec (1 / 50) (etaN h K omegaStar) (62 / 5 * e)
  l1EtaL : L1Vec (1 / 50) (etaL h K omegaStar) (124 / 5 * e)
  l1Torsion : L1Mat (1 / 50 - 333 / 100000) (torsion h K omegaStar) (496 / 25)
  realTorsion : ∀ x : Fin 2 → ℝ, ‖torsion h K omegaStar (fun i => (x i : ℂ))‖ ≤ 496 / 25
  frameL : L1Mat (1 / 50) (tangentMat K) (31 / 10)
  frameN : L1Mat (1 / 50) (normalMat K) (31 / 5)

/-- The entry numbers of the run. -/
def l1Entry : EntryQ :=
  { aN := 62 / 5, aL := 124 / 5, t1 := 496 / 25, tR := 496 / 25, G0 := 551 / 100,
    Gρ := 154 / 100, frame := some (31 / 10, 31 / 5), ei := 3679 / 10000 }

/-- The run with the ℓ¹ entry: the certified constants of `freqVar`, caps and `ϑ` retuned. -/
def l1Var : CAVar where
  sB := 20001 / 10000
  sT := 512 / 100
  sLt := 124001 / 10000
  sN := 62001 / 10000
  sNt := 248003 / 10000
  t := 19861 / 1000
  th := 8 / 100
  c := freqC
  cbar := freqCbar
  ctail := 8144 / 100000
  kp := 3

/-- The threshold of the normalised error. -/
def l1Xs : ℚ := 43 / 2000

theorem l1Var_ok : l1Var.numQ.okL1 l1Entry l1Var.cap caM0 l1Xs = true := by decide +kernel

theorem l1Var_close :
    l1Var.numQ.sumDL1 l1Entry l1Xs / (l1Xs * (333 / 100000) ^ 4 * gammaStar ^ 2) ≤ 795750 := by
  decide +kernel

theorem l1Var_wf : l1Var.numA.Wf := by
  refine CAVar.wf _ (by norm_num [l1Var]) (by norm_num [l1Var]) (by norm_num [l1Var])
    (by norm_num [l1Var]) (by norm_num [l1Var]) (by norm_num [l1Var]) (by norm_num [l1Var])
    (by norm_num [l1Var]) (fun s => ?_) (fun s => ?_) (by norm_num [l1Var])
  · rcases s with _ | _ | s <;> norm_num [l1Var, freqC]
  · rcases s with _ | _ | s <;> norm_num [l1Var, freqCbar]

theorem l1Var_cert : l1Var.numA.Cert (gammaStar : ℝ) ({omegaStar} : Set (Fin 2 → ℝ)) where
  stage := fun s hs => by
    have hs' : s < 3 := hs
    rw [CAVar.numA_δ]
    interval_cases s
    · rw [show (2 : ℝ)⁻¹ ^ 0 * (333 / 100000) = ((333 / 100000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d0
    · rw [show (2 : ℝ)⁻¹ ^ 1 * (333 / 100000) = ((333 / 200000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d1
    · rw [show (2 : ℝ)⁻¹ ^ 2 * (333 / 100000) = ((333 / 400000 : ℚ) : ℝ) by norm_num]
      exact sdConst_d2
  bar := fun s hs => by
    have hs' : s < 3 := hs
    show SDConst 2 1 _ (l1Var.numA.r s) _ _
    rw [CAVar.numA_r]
    interval_cases s
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 0)) = ((1 / 50 : ℚ) : ℝ) by
        norm_num]
      exact sdConst_r0
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 1)) =
        ((1001 / 100000 : ℚ) : ℝ) by norm_num]
      exact sdConst_r1
    · rw [show (1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 2)) =
        ((1003 / 200000 : ℚ) : ℝ) by norm_num]
      exact sdConst_r2
  tail := fun δ hδ hle => by
    have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
    have hle' : δ ≤ 333 / 800000 := by
      refine hle.trans_eq ?_
      rw [CAVar.numA_δ]
      show (2 : ℝ)⁻¹ ^ 3 * (333 / 100000) = _
      norm_num
    refine sdConst_subset (sdConst_classical_tail hγ hδ hle' (by norm_num) ?_ ?_) ?_
    · show (0 : ℝ) ≤ ((8144 / 100000 : ℚ) : ℝ)
      norm_num
    · show _ ≤ (9869 / 1000 * ((8144 / 100000 : ℚ) : ℝ)) ^ 2
      norm_num
    · rintro ω rfl
      exact isDiophantine_omegaStar

theorem einv_le_l1 : Ent.einv ≤ ((l1Entry.ei : ℚ) : ℝ) := by
  have h := Real.exp_one_gt_d9
  unfold Ent.einv
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num [l1Entry])]
  norm_num [l1Entry]
  linarith

open CAVar in
/-- **The core theorem with the ℓ¹ entry at the cA-like data.** -/
theorem cAL1_core {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {e : ℝ}
    (hO : CALike 𝔅 h K omegaStar) (hL : CAL1Like h K e)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K omegaStar θ‖ ≤ e)
    (hsm : e / ((gammaStar : ℝ) ^ 4 * (333 / 100000) ^ 4) < l1Xs) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤
        (l1Var.numQ.sumDL1 l1Entry l1Xs : ℝ) /
          ((l1Xs : ℝ) * (333 / 100000) ^ 4 * (gammaStar : ℝ) ^ 2) * e := by
  set V := l1Var with hVdef
  have hV := l1Var_wf
  have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have hXs : (0 : ℚ) < l1Xs := by norm_num [l1Xs]
  have hXpos : (0 : ℝ) < l1Xs := by exact_mod_cast hXs
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hQ : V.numQ.toA.Wf := by rw [V.numQ_toA]; exact hV
  obtain ⟨hEw, hOk⟩ := NumQ.okL1_sound hQ einv_le_l1 l1Var_ok
  rw [V.numQ_toA, show (fun i => (caM0 i : ℝ)) = _ from initV_eq.symm,
    show (fun i => (V.cap i : ℝ)) = _ from V.capV_eq.symm] at hOk
  have hSv : Standing 2 1 3 (31 / 10 + 1 / 160) (2 + 1 / 160) (50 / 11 + 1 / 160) 𝔅 h omegaStar
      gammaStar :=
    { toParams := ⟨le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      isOpen := hO.isOpen
      transl_mem := hO.transl
      holo := hO.holo
      periodic := hO.periodic
      real := hO.real
      bounds := fun z hz => (hO.bounds z hz).2
      gamma_pos := hγ
      dio := isDiophantine_omegaStar }
  have hK𝔅 : ∀ θ ∈ complexStrip 2 (1 / 50), K θ ∈ 𝔅 := fun θ hθ =>
    hO.ball θ hθ (Metric.mem_ball_self (by norm_num))
  have hGn : ∀ θ ∈ complexStrip 2 (1 / 50), ‖(gramMatrix K θ)⁻¹‖ ≤ 2 := fun θ hθ =>
    norm_le_of_rowSum_le le_rfl (hO.gram θ hθ).2
  have hfb : ∀ θ ∈ complexStrip 2 (1 / 50), _ := fun θ hθ =>
    frame_bounds hSv (hK𝔅 θ hθ) (hO.deriv_le θ hθ) (hO.gram θ hθ).1 (hGn θ hθ) omegaStar
  have hδ0 : V.numA.δ 0 = 333 / 100000 := by
    show Engine.deltaSeq 3 V.numA.ρ V.numA.ρinf 0 = _
    simp [Engine.deltaSeq, V.delta0_eq]
  have hρ : V.numA.ρ = 1 / 50 := by norm_num [CAVar.numA]
  have hRef : RefHypA V.numA caInit 𝔅 h K omegaStar :=
    { dX := fun z hz => (hO.bounds z hz).2.2.1
      d2X := fun z hz => (hO.bounds z hz).2.2.2
      tangentT := fun θ hθ => (hfb θ hθ).2.1.trans_eq (by norm_num [caInit])
      normal := fun θ hθ => (hfb θ hθ).2.2.1.trans_eq (by norm_num [caInit])
      normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1.trans_eq (by norm_num [caInit])
      tors := fun θ hθ => hO.torsion_le θ (by
        have e1 : V.numA.ρ - V.numA.δ 0 = 1 / 50 - 333 / 100000 := by rw [hδ0, hρ]
        rw [← e1]
        exact hθ) }
  have hEH : EntryHypA V.numA l1Entry.toA h K omegaStar e :=
    { l1EtaN := by
        rw [hρ, show l1Entry.toA.aN = 62 / 5 by norm_num [EntryQ.toA, l1Entry]]
        exact hL.l1EtaN
      l1EtaL := by
        rw [hρ, show l1Entry.toA.aL = 124 / 5 by norm_num [EntryQ.toA, l1Entry]]
        exact hL.l1EtaL
      l1Torsion := by
        rw [hρ, hδ0, show l1Entry.toA.t1 = 496 / 25 by norm_num [EntryQ.toA, l1Entry]]
        exact hL.l1Torsion
      realTorsion := fun x => (hL.realTorsion x).trans_eq (by norm_num [EntryQ.toA, l1Entry])
      gam0 := by
        rw [hδ0]
        exact gammaInf_d0.trans_eq (by norm_num [EntryQ.toA, l1Entry])
      gamρ := by
        rw [hρ]
        exact gammaInf_rho.trans_eq (by norm_num [EntryQ.toA, l1Entry])
      frame := fun F hF => by
        simp only [EntryQ.toA, l1Entry, Option.map_some, Option.some.injEq] at hF
        subst hF
        rw [hρ]
        exact ⟨hL.frameL.le (by norm_num), hL.frameN.le (by norm_num)⟩ }
  have hsm' : e / ((gammaStar : ℝ) ^ 4 *
      Engine.delta0 3 V.numA.ρ V.numA.ρinf ^ (2 * (2 * V.numA.τ))) < l1Xs := by
    rw [V.delta0_eq, show 2 * (2 * V.numA.τ) = ((4 : ℕ) : ℝ) by
      show 2 * (2 * (1 : ℝ)) = _
      norm_num, Real.rpow_natCast]
    exact hsm
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_AL1 (N := V.numA) (E := l1Entry.toA)
    (M := 3)
    (σK := 31 / 10 + 1 / 160) (σB := 2 + 1 / 160) (σT := 50 / 11 + 1 / 160) (μ := 1 / 160)
    (γbar := 687 / 5000) (Xs := l1Xs) (I := caInit) hV hEw rfl rfl (by norm_num [CAVar.numA])
    (by norm_num) (by norm_num) rfl (by norm_num [CAVar.numA]) hOk hXpos hO.isOpen hO.transl hO.holo
    hO.periodic hO.real hO.bounds hO.torus_holo hO.primary hO.torus_real
    hO.ball (fun θ hθ => (hO.deriv_le θ hθ).trans_eq (by norm_num))
    (fun θ hθ => ⟨(hO.gram θ hθ).1, fun i => ((hO.gram θ hθ).2 i).trans_eq (by norm_num)⟩)
    hO.twist_unit (fun i => (hO.twist_le i).trans_eq (by norm_num)) hRef (Set.mem_singleton _)
    l1Var_cert hEH hγ (by norm_num [gammaStar]) isDiophantine_omegaStar he0 hE hsm'
  refine ⟨Kinf, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · intro θ hθ
    have := h5 θ hθ
    rwa [show (1 / 160 / 2 : ℝ) = 1 / 320 by norm_num] at this
  · intro θ hθ
    exact (h6 θ hθ).trans_eq (by norm_num)
  · intro θ hθ
    refine (h7 θ hθ).trans ?_
    have hle := NumQ.sumDL1_le hQ hEw einv_le_l1 hXs.le
    rw [V.numQ_toA] at hle
    have hc2 : c2AL1 V.numA l1Entry.toA l1Xs ≤
        (1 / 50) ^ 2 * (V.numQ.sumDL1 l1Entry l1Xs : ℝ) / ((l1Xs : ℝ) * (333 / 100000) ^ 4) := by
      unfold c2AL1
      rw [V.rho_pow, V.delta0_eq, show 4 * V.numA.τ = ((4 : ℕ) : ℝ) by
        show 4 * (1 : ℝ) = _
        norm_num, Real.rpow_natCast]
      gcongr
    have hpos : (0 : ℝ) < (gammaStar : ℝ) ^ 2 * V.numA.ρ ^ (2 * V.numA.τ) := by
      rw [V.rho_pow]; positivity
    calc c2AL1 V.numA l1Entry.toA l1Xs * e / ((gammaStar : ℝ) ^ 2 * V.numA.ρ ^ (2 * V.numA.τ))
        ≤ (1 / 50) ^ 2 * (V.numQ.sumDL1 l1Entry l1Xs : ℝ) / ((l1Xs : ℝ) * (333 / 100000) ^ 4) *
            e / ((gammaStar : ℝ) ^ 2 * V.numA.ρ ^ (2 * V.numA.τ)) := by
          gcongr
      _ = _ := by
          rw [V.rho_pow]
          field_simp

/-- **PlasmaLean's frequency and strip with the ℓ¹ entry.** For `ω* = (ι, 1)` on the strip
`ρ = 1/50` of a canonical two-degree-of-freedom flow: if `h`, `K` satisfy the explicit bounds
`CALike`, the ℓ¹ data `CAL1Like` (assumed data), and the invariance error is at most
`e ≤ 9.4·10⁻¹⁶ = 10^{-15.03}`, there is a true invariant torus `Kinf` on the strip
`ρ∞ = 1/50000`, at distance at most `795750 e` from `K`. -/
theorem plasmaLean_torus_l1 {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {e : ℝ}
    (hO : CALike 𝔅 h K omegaStar) (hL : CAL1Like h K e)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K omegaStar θ‖ ≤ e)
    (he : e ≤ 94 / 10 ^ 17) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤ 795750 * e := by
  have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hsm : e / ((gammaStar : ℝ) ^ 4 * (333 / 100000) ^ 4) < (l1Xs : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    refine he.trans_lt ?_
    norm_num [gammaStar, l1Xs]
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := cAL1_core hO hL hE hsm
  refine ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ he0
  have : ((l1Var.numQ.sumDL1 l1Entry l1Xs / (l1Xs * (333 / 100000) ^ 4 * gammaStar ^ 2) : ℚ) : ℝ) ≤
      ((795750 : ℚ) : ℝ) := Rat.cast_le.mpr l1Var_close
  push_cast at this
  exact this

end KAM.Sharp2.Examples

end
