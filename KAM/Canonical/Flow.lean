/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Existence
public import KAM.ODE.Uniqueness
public import KAM.Strip.Regularity
public import Mathlib.Analysis.Complex.Basic

/-!
# The canonical flow: gauge interiors, the flow, existence and translations

Blueprint-N Part 5, node `bpN:p5:flow`, parts (a) and (d). The flow is stated for a
finite-dimensional complex normed space `E` and a *gauge* `W : E ≃L[ℂ] E`, so the norm of the
blueprint is `ν x = ‖W x‖` and no second norm instance is needed.

* `KAM.Canonical.gaugeInterior`: `Ω^c = {z | B̄_ν(z, c) ⊆ Ω}`; open (`isOpen_gaugeInterior`),
  monotone (`gaugeInterior_mono`), with `B̄_ν(z, c - c') ⊆ Ω^{c'}` (`ball_subset_gaugeInterior`).
* `KAM.Canonical.flow`: the value at `t` of a chosen solution in `Ω` on `[-1, 1]` through `z`.
  Consumers go through `flow_a`, never through the definition.
* `KAM.Canonical.SmallField`: the standing hypotheses (`Ω` open, `F` holomorphic, `ν(F) ≤ ε ≤ 1/2`).
* `KAM.Canonical.flow_a`: existence on `[-1, 1]`, uniqueness on `J ∩ [-1, 1]`, and the displacement
  bound `ν(X^t z - z) ≤ |t| ε`.
* `KAM.Canonical.flow_d`: translation covariance.

Existence is one Picard step in the conjugated variable `y = W x`, where `ν` becomes the norm of
`E`; the gauge ball of radius `1/2 + η` (which lies in `Ω` for a small `η > 0`, by compactness) and
the time `1 + 2η` give a solution on an open interval around `[-1, 1]`. Uniqueness is
`KAM.ODE.gen_uniqueness`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace KAM.Canonical

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- `Ω^c = {z | B̄_ν(z, c) ⊆ Ω}` for `ν x = ‖W x‖`. -/
def gaugeInterior (W : E ≃L[ℂ] E) (Ω : Set E) (c : ℝ) : Set E :=
  {z | ∀ w, ‖W (w - z)‖ ≤ c → w ∈ Ω}

open Classical in
/-- `X^t(z)`: the value at `t` of a solution in `Ω` on `[-1, 1]` through `z`
(`z` if none exists). -/
def flow (F : E → E) (Ω : Set E) (t : ℝ) (z : E) : E :=
  if h : ∃ γ : ℝ → E, KAM.ODE.IsSolutionIn F Ω (Icc (-1) 1) γ ∧ γ 0 = z then h.choose t else z

/-- Standing hypotheses of `bpN:p5:flow`: `Ω` open, `F` holomorphic on `Ω`, `ν(F) ≤ ε ≤ 1/2`.
(Source premises, not conclusions.) -/
structure SmallField (W : E ≃L[ℂ] E) (Ω : Set E) (F : E → E) (ε : ℝ) : Prop where
  isOpen : IsOpen Ω
  differentiableOn : DifferentiableOn ℂ F Ω
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ 1 / 2
  bound : ∀ z ∈ Ω, ‖W (F z)‖ ≤ ε

/-! ### Gauge balls and interiors -/

/-- Closed gauge balls are compact: they are the image of a closed ball of `E` under the affine
homeomorphism `y ↦ W⁻¹ y + z`. -/
private theorem isCompact_gaugeBall (W : E ≃L[ℂ] E) (z : E) (c : ℝ) :
    IsCompact {w : E | ‖W (w - z)‖ ≤ c} := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : {w : E | ‖W (w - z)‖ ≤ c} = (fun y => W.symm y + z) '' closedBall (0 : E) c := by
    ext w
    simp only [mem_ofPred_eq, mem_image, mem_closedBall, dist_zero_right]
    constructor
    · intro hw
      exact ⟨W (w - z), hw, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact (isCompact_closedBall 0 c).image (W.symm.continuous.add continuous_const)

/-- `Ω^c` is open (`ν`-balls are compact). -/
theorem isOpen_gaugeInterior {Ω : Set E} (hΩ : IsOpen Ω) (W : E ≃L[ℂ] E) (c : ℝ) :
    IsOpen (gaugeInterior W Ω c) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hK : {w : E | ‖W (w - z)‖ ≤ c} ⊆ Ω := fun w hw => hz w hw
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_gaugeBall W z c).exists_cthickening_subset_open hΩ hK
  refine Filter.mem_of_superset (ball_mem_nhds z hδ) fun z' hz' w hw => ?_
  apply hsub
  refine mem_cthickening_of_dist_le w (w - z' + z) δ _ ?_ ?_
  · show ‖W (w - z' + z - z)‖ ≤ c
    simpa using hw
  · rw [dist_eq_norm]
    have : w - (w - z' + z) = z' - z := by abel
    rw [this, ← dist_eq_norm]
    exact mem_ball.1 hz' |>.le

set_option linter.unusedSectionVars false in
theorem gaugeInterior_mono (W : E ≃L[ℂ] E) {Ω : Set E} {c c' : ℝ} (h : c' ≤ c) :
    gaugeInterior W Ω c ⊆ gaugeInterior W Ω c' :=
  fun _ hz w hw => hz w (hw.trans h)

set_option linter.unusedSectionVars false in
/-- `B̄_ν(z, c - c') ⊆ Ω^{c'}` for `z ∈ Ω^c`. -/
theorem ball_subset_gaugeInterior (W : E ≃L[ℂ] E) {Ω : Set E} {c c' : ℝ} {z w : E}
    (hz : z ∈ gaugeInterior W Ω c) (hw : ‖W (w - z)‖ ≤ c - c') : w ∈ gaugeInterior W Ω c' := by
  intro w' hw'
  apply hz
  have : W (w' - z) = W (w' - w) + W (w - z) := by rw [← map_add]; congr 1; abel
  rw [this]
  calc ‖W (w' - w) + W (w - z)‖ ≤ ‖W (w' - w)‖ + ‖W (w - z)‖ := norm_add_le _ _
    _ ≤ c := by linarith

/-- A gauge interior has a little room: if `B̄_ν(z, c) ⊆ Ω` for open `Ω`, then also
`B̄_ν(z, c + η) ⊆ Ω` for some `η > 0`. -/
private theorem exists_gaugeInterior_gt {Ω : Set E} (hΩ : IsOpen Ω) (W : E ≃L[ℂ] E) {c : ℝ}
    {z : E} (hz : z ∈ gaugeInterior W Ω c) : ∃ η > 0, z ∈ gaugeInterior W Ω (c + η) := by
  by_cases hS : ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ).Nonempty
  · have hcomp : IsCompact ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ) :=
      (isCompact_gaugeBall W z (c + 1)).inter_right hΩ.isClosed_compl
    have hcont : ContinuousOn (fun w : E => ‖W (w - z)‖) ({w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ) :=
      (continuous_norm.comp (W.continuous.comp (continuous_id.sub continuous_const))).continuousOn
    obtain ⟨w₀, hw₀, hmin⟩ := hcomp.exists_isMinOn hS hcont
    have hm : c < ‖W (w₀ - z)‖ := by
      by_contra hle
      exact hw₀.2 (hz w₀ (not_lt.1 hle))
    refine ⟨min 1 ((‖W (w₀ - z)‖ - c) / 2), lt_min one_pos (by linarith), fun w hw => ?_⟩
    by_contra hwΩ
    have hwS : w ∈ {w : E | ‖W (w - z)‖ ≤ c + 1} ∩ Ωᶜ :=
      ⟨(hw.trans (by linarith [min_le_left 1 ((‖W (w₀ - z)‖ - c) / 2)])), hwΩ⟩
    have h1 := isMinOn_iff.1 hmin w hwS
    have h2 := min_le_right 1 ((‖W (w₀ - z)‖ - c) / 2)
    linarith
  · refine ⟨1, one_pos, fun w hw => ?_⟩
    by_contra hwΩ
    exact hS ⟨w, hw, hwΩ⟩

/-! ### Regularity of the field and uniqueness -/

private theorem contDiffOn_one_of_smallField {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) : ContDiffOn ℝ 1 F Ω := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  exact ((KAM.contDiffOn_infty_of_differentiableOn h.isOpen h.differentiableOn).restrict_scalars
    ℝ).of_le (by exact_mod_cast le_top)

/-- Two solutions in `Ω` on an order-connected interval through `0` that agree at `0` agree. -/
private theorem solution_eqOn {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {γ₁ γ₂ : ℝ → E} (h₁ : KAM.ODE.IsSolutionIn F Ω J γ₁) (h₂ : KAM.ODE.IsSolutionIn F Ω J γ₂)
    (h00 : γ₁ 0 = γ₂ 0) : EqOn γ₁ γ₂ J :=
  KAM.ODE.gen_uniqueness h.isOpen (contDiffOn_one_of_smallField h) hJ h0 h₁ h₂ h00

/-! ### Existence of a solution on `[-1, 1]` -/

/-- One Picard step in the conjugated variable `y = W x`: for `z ∈ Ω^{1/2}` there is a solution in
`Ω` on `[-1, 1]` through `z` with displacement `ν(γ t - z) ≤ |t| ε`. -/
private theorem exists_solution {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) :
    ∃ γ : ℝ → E, KAM.ODE.IsSolutionIn F Ω (Icc (-1) 1) γ ∧ γ 0 = z ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ‖W (γ t - z)‖ ≤ |t| * ε := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨η, hη, hzη⟩ := exists_gaugeInterior_gt h.isOpen W hz
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 2 + η := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 + 2 * η := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have haT : a / (1 / 2) = T := by rw [ha, hT]; ring
  -- the conjugated field and domain
  obtain ⟨G, hG⟩ : ∃ G : E → E, G = fun y => W (F (W.symm y)) := ⟨_, rfl⟩
  have hΩ'open : IsOpen (W.symm ⁻¹' Ω) := h.isOpen.preimage W.symm.continuous
  have hball : closedBall (W z) a ⊆ W.symm ⁻¹' Ω := by
    intro y hy
    rw [mem_preimage]
    refine hzη _ ?_
    have : W (W.symm y - z) = y - W z := by rw [map_sub]; simp
    rw [this, ← ha]
    simpa [mem_closedBall, dist_eq_norm] using hy
  have hGbd : ∀ y ∈ closedBall (W z) a, ‖G y‖ ≤ ε := by
    intro y hy
    have := h.bound _ (hball hy)
    rw [hG]
    exact this
  have hGC1 : ContDiffOn ℝ 1 G (W.symm ⁻¹' Ω) := by
    have h1 : ContDiffOn ℂ 1 F Ω :=
      (KAM.contDiffOn_infty_of_differentiableOn h.isOpen h.differentiableOn).of_le
        (by exact_mod_cast le_top)
    have h2 : ContDiffOn ℂ 1 (fun y => F (W.symm y)) (W.symm ⁻¹' Ω) :=
      h1.comp W.symm.contDiff.contDiffOn (fun y hy => hy)
    have h3 : ContDiffOn ℂ 1 G (W.symm ⁻¹' Ω) := by
      rw [hG]
      exact W.contDiff.comp_contDiffOn h2
    exact h3.restrict_scalars ℝ
  obtain ⟨-, L, hL⟩ := KAM.ODE.gen_lip hΩ'open hGC1 (isCompact_closedBall (W z) a) hball
  have hMT : ε * T ≤ a := by
    rw [hT, ha]
    nlinarith [mul_nonneg (sub_nonneg.2 h.eps_le) (by linarith : (0 : ℝ) ≤ 1 + 2 * η)]
  obtain ⟨α, hα0, hα⟩ := KAM.ODE.picard_lindelof_ball (F := G) (x := W z) (a := a) (M := ε)
    (T := T) (t₀ := 0) (L := L) ha0 h.eps_nonneg hT0 hGbd hL hMT
  simp only [zero_sub, zero_add] at hα
  have hder : ∀ t ∈ Ioo (-T) T, HasDerivAt α (G (α t)) t := fun t ht =>
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h0J : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith [hT, hη], by linarith [hT, hη]⟩
  have hshort := KAM.ODE.gen_short (F := G) (J := Ioo (-T) T) ordConnected_Ioo h0J hα0 hder
    (M := 1 / 2) (δ := a) (by norm_num) (fun y hy => (hGbd y hy).trans h.eps_le)
  have hconf : ∀ t ∈ Ioo (-T) T, α t ∈ closedBall (W z) a := by
    intro t ht
    refine (hshort t ht ?_).2
    rw [haT, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hsubI : Icc (-1 : ℝ) 1 ⊆ Ioo (-T) T := fun t ht =>
    ⟨by linarith [ht.1, hT, hη], by linarith [ht.2, hT, hη]⟩
  have hγder : ∀ t ∈ Ioo (-T) T, W.symm (α t) ∈ Ω ∧ HasDerivAt (fun s => W.symm (α s))
      (F (W.symm (α t))) t := by
    intro t ht
    refine ⟨hball (hconf t ht), ?_⟩
    have := (W.symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hder t ht)
    have e : W.symm (G (α t)) = F (W.symm (α t)) := by rw [hG]; simp
    simpa [Function.comp_def, e] using this
  refine ⟨fun t => W.symm (α t), fun t ht => hγder t (hsubI ht), by simp [hα0], fun t ht => ?_⟩
  have hseg : uIcc 0 t ⊆ Ioo (-T) T := by
    intro w hw
    rw [mem_uIcc] at hw
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hT, hη], by linarith [ht.2, hT, hη]⟩
    · exact ⟨by linarith [ht.1, hT, hη], by linarith [hT, hη]⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := uIcc 0 t)
    (f := α) (f' := fun w => G (α w)) (C := ε)
    (fun w hw => (hder w (hseg hw)).hasDerivWithinAt)
    (fun w hw => hGbd _ (hconf w (hseg hw))) (convex_uIcc 0 t) left_mem_uIcc right_mem_uIcc
  have e : W (W.symm (α t) - z) = α t - W z := by rw [map_sub]; simp
  rw [e]
  rw [hα0, Real.norm_eq_abs, sub_zero] at hmvt
  linarith

/-! ### The flow: part (a) -/

/-- (a) existence on `[-1, 1]`, uniqueness on `J ∩ [-1, 1]`, displacement `ν(X^t z - z) ≤ |t| ε`. -/
theorem flow_a {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε) {z : E}
    (hz : z ∈ gaugeInterior W Ω (1 / 2)) :
    flow F Ω 0 z = z ∧
    KAM.ODE.IsSolutionIn F Ω (Icc (-1) 1) (fun t => flow F Ω t z) ∧
    (∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ γ : ℝ → E, KAM.ODE.IsSolutionIn F Ω J γ →
      γ 0 = z → ∀ t ∈ J ∩ Icc (-1) 1, γ t = flow F Ω t z) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ‖W (flow F Ω t z - z)‖ ≤ |t| * ε := by
  obtain ⟨γ₀, hγ₀, hγ₀0, hγ₀b⟩ := exists_solution h hz
  have hex : ∃ γ : ℝ → E, KAM.ODE.IsSolutionIn F Ω (Icc (-1) 1) γ ∧ γ 0 = z :=
    ⟨γ₀, hγ₀, hγ₀0⟩
  have hflow : ∀ t, flow F Ω t z = hex.choose t := fun t => by
    simp only [flow, hex, ↓reduceDIte]
  obtain ⟨hspec, hspec0⟩ := hex.choose_spec
  have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hfun : (fun t => flow F Ω t z) = hex.choose := funext hflow
  refine ⟨by rw [hflow]; exact hspec0, by rw [hfun]; exact hspec, ?_, ?_⟩
  · intro J hJ h0 γ hγ hγ0 t ht
    have := solution_eqOn h (hJ.inter ordConnected_Icc) ⟨h0, h0I⟩ (hγ.mono inter_subset_left)
      (hspec.mono inter_subset_right) (by rw [hγ0, hspec0]) ht
    rw [hflow]
    exact this
  · intro t ht
    have := solution_eqOn h ordConnected_Icc h0I hspec hγ₀ (by rw [hspec0, hγ₀0]) ht
    rw [hflow, this]
    exact hγ₀b t ht

/-! ### The flow: part (d) -/

/-- (d) translations. -/
theorem flow_d {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε) {τ : E}
    (hτΩ : (fun w => w + τ) '' Ω = Ω) (hτF : ∀ w ∈ Ω, F (w + τ) = F w) :
    (fun w => w + τ) '' gaugeInterior W Ω (1 / 2) = gaugeInterior W Ω (1 / 2) ∧
    ∀ z ∈ gaugeInterior W Ω (1 / 2), ∀ t ∈ Icc (-1 : ℝ) 1,
      flow F Ω t (z + τ) = flow F Ω t z + τ := by
  have hadd : ∀ z ∈ gaugeInterior W Ω (1 / 2), z + τ ∈ gaugeInterior W Ω (1 / 2) := by
    intro z hz w hw
    have hw' : w - τ ∈ Ω := hz _ (by
      have : w - τ - z = w - (z + τ) := by abel
      rw [this]; exact hw)
    rw [← hτΩ]
    exact ⟨w - τ, hw', by simp⟩
  have hsub : ∀ z ∈ gaugeInterior W Ω (1 / 2), z - τ ∈ gaugeInterior W Ω (1 / 2) := by
    intro z hz w hw
    have hw' : w + τ ∈ Ω := hz _ (by
      have : w + τ - z = w - (z - τ) := by abel
      rw [this]; exact hw)
    rw [← hτΩ] at hw'
    obtain ⟨x, hx, hxw⟩ := hw'
    have : x = w := add_right_cancel hxw
    exact this ▸ hx
  have himg : (fun w => w + τ) '' gaugeInterior W Ω (1 / 2) = gaugeInterior W Ω (1 / 2) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hadd z hz
    · intro z hz
      exact ⟨z - τ, hsub z hz, by simp⟩
  refine ⟨himg, fun z hz t ht => ?_⟩
  have hz' : z + τ ∈ gaugeInterior W Ω (1 / 2) := hadd z hz
  obtain ⟨h0, hsol, -, -⟩ := flow_a h hz
  obtain ⟨-, -, huniq, -⟩ := flow_a h hz'
  have hsol' := KAM.ODE.gen_symmetry_translate hsol hτΩ hτF
  have := huniq (Icc (-1) 1) ordConnected_Icc ⟨by norm_num, by norm_num⟩
    (fun t => flow F Ω t z + τ) hsol' (by simp [h0]) t ⟨ht, ht⟩
  exact this.symm

end Flow

end KAM.Canonical
