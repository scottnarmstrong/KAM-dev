/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.TorsionBound
public import KAM.Sharp.ConstantsArith
public import KAM.Apost.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The triangular system and the size of the correction, with general small-divisor data

* Blueprint `bp:p2s:triangular` (`KAM.Sharp.triangular_bounds`): the size clause (c) of
  `KAM.Apost.triangular` with `Γ_δ = c_R γ⁻¹ δ^{-κ}`, for small-divisor data `(κ, c_R)` and
  `0 < δ ≤ 1` (steps `step:p2s:tri-where`, `tri-bounds`: the two cohomological bounds come from
  `CohData.sol`; the qualitative clauses are `KAM.Apost.triangular`).
* Blueprint `bp:p2s:correction` (`KAM.Sharp.correction_bounds`): the bounds of `ξᴺ₀, ξᴺ, gᴸ, ξᴸ, ξ,
  ΔK, ∂_ω ξ` in the separate sizes, with `|T| ≤ H_T` from `KAM.Sharp.torsion_bound` (steps
  `step:p2s:cor-data`, `cor-n`, `cor-l`, `cor-dxi`). The qualitative clauses are the first conjunct
  of `KAM.Apost.correction_spec`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}
variable {τ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2s:triangular`: the size clause (c) of `KAM.Apost.triangular` with
`Γ_δ = c_R γ⁻¹ δ^{-κ}` (clauses (a), (b), (d) are `KAM.Apost.triangular` itself). -/
theorem triangular_bounds (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r)
    {ηL ηN : (Fin n → ℂ) → Fin n → ℂ} {T : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    {HL HN HT σ : ℝ}
    (hηL : DifferentiableOn ℂ ηL (complexStrip n r)) (hηLp : IsPeriodicOn ηL r)
    (hηN : DifferentiableOn ℂ ηN (complexStrip n r)) (hηNp : IsPeriodicOn ηN r)
    (hHL : ∀ θ ∈ complexStrip n r, ‖ηL θ‖ ≤ HL) (hHN : ∀ θ ∈ complexStrip n r, ‖ηN θ‖ ≤ HN)
    (hηN0 : avg ηN = 0) (hT : DifferentiableOn ℂ T (complexStrip n r)) (hTp : IsPeriodicOn T r)
    (hHT : ∀ θ ∈ complexStrip n (r - δ), ‖T θ‖ ≤ HT) (hTinv : IsUnit (avg T).det)
    (hσ : ‖(avg T)⁻¹‖ ≤ σ) :
    ‖triXi0 ω ηL ηN T‖ ≤ σ * (HL + HT * (cR * γ⁻¹ * δ ^ (-κ)) * HN) ∧
    (∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω ηL ηN T θ‖ ≤ ‖triXi0 ω ηL ηN T‖ + cR * γ⁻¹ * δ ^ (-κ) * HN) ∧
    (∀ X, (∀ θ ∈ complexStrip n (r - δ), ‖triXiN ω ηL ηN T θ‖ ≤ X) →
      ∀ θ ∈ complexStrip n (r - δ), ‖triGL ω ηL ηN T θ‖ ≤ HT * X + HL) ∧
    ∀ Y, (∀ θ ∈ complexStrip n (r - δ), ‖triGL ω ηL ηN T θ‖ ≤ Y) →
      ∀ θ ∈ complexStrip n (r - 2 * δ), ‖triXiL ω ηL ηN T θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * Y := by
  have hδr : δ < r := by linarith
  have hr1 : 0 < r - δ := by linarith
  have hδr1 : δ < r - δ := by linarith
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  obtain ⟨⟨hg0, -, -, hgd, hgp, -, -⟩, -, -, -⟩ :=
    triangular hS hr hδ h2δ hηL hηLp hηN hηNp hHL hHN hηN0 hT hTp hHT hTinv hσ
  -- step `tri-bounds`: the first cohomological equation
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU ω ηN θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * HN :=
    hC.sol hS.gamma_pos hS.dio hδ hδ1 hδr ηN HN hηN hηNp hHN hηN0
  refine ⟨Triangular.norm_triXi0_le hr hr1 hHL hHT hU hσ,
    fun θ hθ => Triangular.norm_triXiN_le hU hθ,
    fun X hX θ hθ => Triangular.norm_triGL_le (fun θ hθ => hHL θ (hsub hθ)) hHT hX hθ,
    fun Y hY θ hθ => ?_⟩
  -- step `tri-bounds`: the second cohomological equation, on `T_{r-δ}` with loss `δ`
  have h2 := hC.sol hS.gamma_pos hS.dio (r := r - δ) hδ hδ1 hδr1 (triGL ω ηL ηN T) Y hgd hgp hY hg0
  have e : r - δ - δ = r - 2 * δ := by ring
  rw [e] at h2
  exact h2 θ hθ

namespace CorrectionSharp

/-- `Γ_δ (a ε) = a c_R ε/(γ δ^κ)`. -/
theorem gamma_mul_eq {a γ δ ε : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    cR * γ⁻¹ * δ ^ (-κ) * (a * ε) = a * cR * (ε / (γ * δ ^ κ)) := by
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  rw [Real.rpow_neg hδ.le]
  field_simp

/-- `Γ_δ (c ε/(γ δ^κ)) = c_R c ε/(γ² δ^{2κ})`. -/
theorem gamma_mul_u_eq {c γ δ ε : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    cR * γ⁻¹ * δ ^ (-κ) * (c * (ε / (γ * δ ^ κ))) = cR * c * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  rw [Real.rpow_neg hδ.le, two_mul, Real.rpow_add hδ]
  field_simp

/-- `(K admissible) → (K admissible without the twist)`. -/
theorem admissible_noTwist {σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {r β ε : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : Admissible σK σB σT 𝔅 h ω r β ε K) :
    KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω r β ε K :=
  ⟨hK.r_pos, hK.β_pos, hK.ε_nonneg, hK.ε_le_one, hK.holo, hK.primary, hK.real, hK.ball_sub,
    hK.deriv_le, hK.gram, hK.error_le⟩

end CorrectionSharp

/-- Blueprint `bp:p2s:correction` (the qualitative clauses are the first conjunct of
`KAM.Apost.correction_spec`). -/
theorem correction_bounds (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hγb : γ ≤ γb) {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : Admissible σK σB σT 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r)
    (hεδ : ε ≤ δ)
    (hTS : cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1) :
    (∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤ hT n M σK σB) ∧
    ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ ≤
      cXi0 n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
    (∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cXiN n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cG n cR M σK σB σT γb * ε / (γ * δ ^ κ)) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cR * cG n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ∧
      ‖xi h K ω θ‖ ≤ cXi n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ∧
      ‖correction h K ω θ‖ ≤ cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ∧
      ‖fderiv ℂ (xi h K ω) θ (fun l => (ω l : ℂ))‖ ≤
        cDXi n cR M σK σB σT γb * ε / (γ * δ ^ κ) := by
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hcR := hC.cR_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hσT := hS.σT_pos
  have hM := hS.M_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr1 : 0 < r - δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  -- step `cor-data`
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hTd, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨-, hperiod, -⟩ := periodicity hS hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, -, -, hTp, -, hηp⟩ := hperiod hGu
  have hTavg : torsionAverage h K ω = avg (torsion h K ω) := torsionAverage_eq_avg h K ω hTc
  have hTinv : IsUnit (avg (torsion h K ω)).det := by
    rw [← hTavg]
    exact hK.twist.1
  have hσ : ‖(avg (torsion h K ω))⁻¹‖ ≤ σT := by
    rw [← hTavg]
    exact hK.twist.2
  have hηN0 : avg (etaN h K ω) = 0 := (exactness hS hr hK.holo hK.primary hK𝔅).2
  have hfb : ∀ θ ∈ complexStrip n r, _ := fun θ hθ =>
    frame_bounds hS (hK𝔅 θ hθ) (hK.deriv_le θ hθ) (hGu θ hθ) (hK.gram θ hθ).2 ω
  have hHL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ 2 * n * σK * σB * ε := fun θ hθ =>
    ((hfb θ hθ).2.2.2.2.2.2.2.2.2.2.1 ε (hK.error_le θ hθ)).2.1
  have hHN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ 2 * n * σK * ε := fun θ hθ =>
    ((hfb θ hθ).2.2.2.2.2.2.2.2.2.2.1 ε (hK.error_le θ hθ)).2.2
  -- `|T| ≤ H_T` on `T_{r-δ}` (Lemma `bp:p2s:torsion-bound`)
  have hHT : ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤ hT n M σK σB := by
    intro θ hθ
    have := torsion_bound hC hS (CorrectionSharp.admissible_noTwist hK) hδ hδ1 (by linarith)
      hεδ θ hθ
    unfold hT
    have e : cT0 n M σK σB + cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) =
        cT0 n M σK σB + (cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1))) := by
      ring
    linarith
  -- the triangular system for the data of `K`
  obtain ⟨⟨-, hXNd, -, -, -, hXLd, -⟩, ⟨hdXN, hdXL⟩, -, -⟩ :=
    triangular hS hr hδ h2δ (ηL := etaL h K ω) (ηN := etaN h K ω) (T := torsion h K ω)
      (HL := 2 * n * σK * σB * ε) (HN := 2 * n * σK * ε) (HT := hT n M σK σB) (σ := σT)
      (Correction.diffOn_etaL hηd) (Correction.periodic_etaL hηp)
      (Correction.diffOn_etaN hηd) (Correction.periodic_etaN hηp) hHL hHN hηN0 hTd hTp hHT
      hTinv hσ
  obtain ⟨hxi0, hxiN, hgb, hxiL⟩ :=
    triangular_bounds hC hS hr hδ hδ1 h2δ (ηL := etaL h K ω) (ηN := etaN h K ω)
      (T := torsion h K ω) (HL := 2 * n * σK * σB * ε) (HN := 2 * n * σK * ε)
      (HT := hT n M σK σB) (σ := σT)
      (Correction.diffOn_etaL hηd) (Correction.periodic_etaL hηp)
      (Correction.diffOn_etaN hηd) (Correction.periodic_etaN hηp) hHL hHN hηN0 hTd hTp hHT
      hTinv hσ
  -- step `cor-n`: in terms of `u = ε/(γ δ^κ)` and `E = ε/(γ² δ^{2κ})`
  obtain ⟨⟨hεu, huE⟩, -, -, -⟩ := absorb hC.one_le_kappa hγ hγb hδ hδ1 hε0
  set u := ε / (γ * δ ^ κ) with hu
  set E := ε / (γ ^ 2 * δ ^ (2 * κ)) with hE
  have hu0 : 0 ≤ u := div_nonneg hε0 (mul_pos hγ (Real.rpow_pos_of_pos hδ κ)).le
  have hE0 : 0 ≤ E := div_nonneg hε0 (by positivity)
  have hΓN : cR * γ⁻¹ * δ ^ (-κ) * (2 * n * σK * ε) = 2 * n * σK * cR * u :=
    CorrectionSharp.gamma_mul_eq hγ hδ
  have hhT0 : 0 ≤ hT n M σK σB := by unfold hT cT0; positivity
  have hX0 : ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ ≤
      cXi0 n cR M σK σB σT γb * u := by
    refine hxi0.trans ?_
    rw [mul_assoc (hT n M σK σB), hΓN]
    unfold cXi0
    have h1 : 2 * (n : ℝ) * σK * σB * ε ≤ 2 * n * σK * σB * (γb * u) :=
      mul_le_mul_of_nonneg_left hεu (by positivity)
    have h2 : σT * (2 * n * σK * σB * ε + hT n M σK σB * (2 * n * σK * cR * u)) ≤
        σT * (2 * n * σK * σB * (γb * u) + hT n M σK σB * (2 * n * σK * cR * u)) :=
      mul_le_mul_of_nonneg_left (by linarith) hσT.le
    refine h2.trans (le_of_eq ?_)
    ring
  have hXN : ∀ θ ∈ complexStrip n (r - δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cXiN n cR M σK σB σT γb * u := by
    intro θ hθ
    calc _ ≤ ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ +
          cR * γ⁻¹ * δ ^ (-κ) * (2 * n * σK * ε) := hxiN θ hθ
      _ = ‖triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)‖ + 2 * n * σK * cR * u := by
          rw [hΓN]
      _ ≤ cXi0 n cR M σK σB σT γb * u + 2 * n * σK * cR * u := add_le_add hX0 le_rfl
      _ = cXiN n cR M σK σB σT γb * u := by unfold cXiN; ring
  have hGL : ∀ θ ∈ complexStrip n (r - δ),
      ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ cG n cR M σK σB σT γb * u := by
    intro θ hθ
    have : 2 * (n : ℝ) * σK * σB * ε ≤ 2 * n * σK * σB * (γb * u) :=
      mul_le_mul_of_nonneg_left hεu (by positivity)
    calc _ ≤ hT n M σK σB * (cXiN n cR M σK σB σT γb * u) + 2 * n * σK * σB * ε :=
          hgb _ hXN θ hθ
      _ ≤ hT n M σK σB * (cXiN n cR M σK σB σT γb * u) + 2 * n * σK * σB * (γb * u) :=
          add_le_add le_rfl this
      _ = cG n cR M σK σB σT γb * u := by unfold cG; ring
  -- step `cor-l`
  have hXL : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cR * cG n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
    intro θ hθ
    have := hxiL _ hGL θ hθ
    rwa [CorrectionSharp.gamma_mul_u_eq hγ hδ] at this
  have hXLE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        cR * cG n cR M σK σB σT γb * E := fun θ hθ => by
    rw [hE, ← mul_div_assoc]
    exact hXL θ hθ
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
        γb * cXiN n cR M σK σB σT γb * E := by
    intro θ hθ
    have hc : 0 ≤ cXiN n cR M σK σB σT γb := by
      unfold cXiN cXi0 hT cT0
      positivity
    calc _ ≤ cXiN n cR M σK σB σT γb * u := hXN θ (hsub hθ)
      _ ≤ cXiN n cR M σK σB σT γb * (γb * E) := mul_le_mul_of_nonneg_left huE hc
      _ = γb * cXiN n cR M σK σB σT γb * E := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖xi h K ω θ‖ ≤ cXi n cR M σK σB σT γb * E := by
    intro θ hθ
    refine Correction.norm_sumElim_le ((hXLE θ hθ).trans ?_) ((hXNE θ hθ).trans ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE0
  refine ⟨hHT, by rw [mul_div_assoc]; exact hX0,
    fun θ hθ => ⟨by rw [mul_div_assoc]; exact hXN θ hθ, by rw [mul_div_assoc]; exact hGL θ hθ⟩,
    fun θ hθ => ⟨hXL θ hθ, by rw [mul_div_assoc]; exact hXi θ hθ, ?_, ?_⟩⟩
  · -- `ΔK = L ξᴸ + N ξᴺ`
    have hθr : θ ∈ complexStrip n r := hsub1 (hsub hθ)
    have hP := (hfb θ hθr).2.2.2.2.2.2.2.2.2.2.2
    rw [← norm_sumVec, Correction.sumVec_correction, mul_div_assoc]
    calc ‖frameMat K θ *ᵥ xi h K ω θ‖ ≤
          σK * ‖triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ +
            σK * σB * ‖triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ := hP _ _
      _ ≤ σK * (cR * cG n cR M σK σB σT γb * E) +
            σK * σB * (γb * cXiN n cR M σK σB σT γb * E) :=
          add_le_add (mul_le_mul_of_nonneg_left (hXLE θ hθ) hσK.le)
            (mul_le_mul_of_nonneg_left (hXNE θ hθ) (by positivity))
      _ = cDK n cR M σK σB σT γb * E := by unfold cDK; ring
  · -- step `cor-dxi`: `∂_ω ξ = (gᴸ, -ηᴺ)`
    have hθ1 : θ ∈ complexStrip n (r - δ) := hsub hθ
    have hopen : (complexStrip n (r - 2 * δ)) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    rw [show xi h K ω = fun θ => (Sum.elim
      (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ)
      (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) : Fin n ⊕ Fin n → ℂ) from rfl,
      Correction.fderiv_sumElim_apply (hXLd.differentiableAt hopen)
        ((hXNd.mono hsub).differentiableAt hopen), hdXL θ hθ, hdXN θ hθ1, mul_div_assoc]
    refine Correction.norm_sumElim_le ((hGL θ hθ1).trans ?_) ?_
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu0
    · rw [norm_neg]
      calc ‖etaN h K ω θ‖ ≤ 2 * n * σK * ε := hHN θ (hsub1 hθ1)
        _ ≤ 2 * n * σK * (γb * u) := mul_le_mul_of_nonneg_left hεu (by positivity)
        _ = 2 * n * σK * γb * u := by ring
        _ ≤ cDXi n cR M σK σB σT γb * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0

end KAM.Sharp

end
