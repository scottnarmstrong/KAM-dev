/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Flow
public import KAM.Nekhoroshev.Averaging.CorrectorRegular

/-!
# Part N12: the corrector identity (`bpN:p12:identity`)

Along a maximal orbit `γ_x(u) = (θ(u), I(u))` of the averaging flow, with `Λ(u) = w(γ_x(u))`,
`Q = ∂_θ w ∂_I f + D_I w a` (`avgCorrectionQ`) and `r` (`avgResidual`):
`ι(I(t) - I₀) = ε (Λ(t) - Λ(0)) - ε² ∫₀ᵗ Q + ε ∫₀ᵗ r`.

The proof differentiates `G(u) = ι I(u) - ε Λ(u)` (`id-eq`, `id-chain`), identifies
`G' = ε r - ε² Q` along the orbit (`id-div`) and integrates (FTC), the integrand being continuous
because `w` is `C¹` on the open domain (`wreg`) and the field components `ω`, `a`, `∂_I f` are
continuous there (they are read off from the `C¹` fields of `avgH h f 0` and `avgH h f 1`).

Besides `identity`, the file exports the continuity facts along the flow that `Pointwise` reuses.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

/-- The correction `Q = ∂_θ w ∂_I f + D_I w a` (slow field `a = avgA`, fast field `avgB`). -/
def avgCorrectionQ (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (κ : ℝ) (z : AvgPhase n) : Fin n → ℂ :=
  fderiv ℝ (avgW h f κ) z (avgB f z, 0) + fderiv ℝ (avgW h f κ) z (0, avgA f z)

section Continuity

variable (d : AveragingData n R s h f)
include d

theorem continuousOn_avgA : ContinuousOn (avgA f) (avgDomain n R) := by
  have hc : ContinuousOn (KAM.hamiltonianVectorField (avgH h f 1)) (avgDomain n R) :=
    (avgField_contDiffOn d 1).continuousOn
  refine (continuous_snd.comp_continuousOn hc).congr fun z hz => ?_
  simp [(fbounds d z hz).2.2 1]

theorem continuousOn_avgFreq : ContinuousOn (fun z : AvgPhase n => KAM.frequencyMap h z.2)
    (avgDomain n R) := by
  have hc : ContinuousOn (KAM.hamiltonianVectorField (avgH h f 0)) (avgDomain n R) :=
    (avgField_contDiffOn d 0).continuousOn
  refine (continuous_fst.comp_continuousOn hc).congr fun z hz => ?_
  simp [(fbounds d z hz).2.2 0]

theorem continuousOn_avgB : ContinuousOn (avgB f) (avgDomain n R) := by
  have hc1 : ContinuousOn (KAM.hamiltonianVectorField (avgH h f 1)) (avgDomain n R) :=
    (avgField_contDiffOn d 1).continuousOn
  refine ((continuous_fst.comp_continuousOn hc1).sub (continuousOn_avgFreq d)).congr
    fun z hz => ?_
  simp [(fbounds d z hz).2.2 1]

theorem continuousOn_avgCorrectionQ {κ : ℝ} (hκ : 0 < κ) :
    ContinuousOn (avgCorrectionQ h f κ) (avgDomain n R) := by
  obtain ⟨-, M₂, -, -, -, hM⟩ := avg_compact_bounds d
  have hdw : ContinuousOn (fderiv ℝ (avgW h f κ)) (avgDomain n R) :=
    (wreg d hκ hM).1.continuousOn_fderiv_of_isOpen (isOpen_avgDomain' n R) le_rfl
  exact (hdw.clm_apply ((continuousOn_avgB d).prodMk continuousOn_const)).add
    (hdw.clm_apply (continuousOn_const.prodMk (continuousOn_avgA d)))

theorem continuousOn_avgResidual {κ : ℝ} (hκ : 0 < κ) :
    ContinuousOn (avgResidual h f κ) (avgDomain n R) := by
  obtain ⟨-, M₂, -, -, -, hM⟩ := avg_compact_bounds d
  have hdw : ContinuousOn (fderiv ℝ (avgW h f κ)) (avgDomain n R) :=
    (wreg d hκ hM).1.continuousOn_fderiv_of_isOpen (isOpen_avgDomain' n R) le_rfl
  exact ((KAM.realInclusion n).continuous.comp_continuousOn (continuousOn_avgA d)).sub
    (hdw.clm_apply ((continuousOn_avgFreq d).prodMk continuousOn_const))

theorem differentiableAt_avgW {κ : ℝ} (hκ : 0 < κ) {z : AvgPhase n} (hz : z ∈ avgDomain n R) :
    DifferentiableAt ℝ (avgW h f κ) z := by
  obtain ⟨-, M₂, -, -, -, hM⟩ := avg_compact_bounds d
  exact ((wreg d hκ hM).1.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_avgDomain' n R).mem_nhds hz)

end Continuity

section Orbit

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- A time `u ∈ [0, t]` below `T₊` lies in the maximal interval. -/
theorem mem_eIoo_of_le {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t u : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) (htp : (t : EReal) < avgTp h f R ε x) :
    u ∈ KAM.ODE.eIoo (avgTm h f R ε x) (avgTp h f R ε x) :=
  ⟨lt_of_lt_of_le (avgMaximal_spec d ε hx).neg_lt (EReal.coe_nonneg.2 hu),
    lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hut) htp⟩

/-- The orbit stays in the domain and solves the Hamiltonian equation on `[0, t]`. -/
theorem orbit_hasDerivAt {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t u : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) (htp : (t : EReal) < avgTp h f R ε x) :
    avgFlow h f R ε u x ∈ avgDomain n R ∧
      HasDerivAt (fun v => avgFlow h f R ε v x)
        (KAM.hamiltonianVectorField (avgH h f ε) (avgFlow h f R ε u x)) u :=
  (avgMaximal_spec d ε hx).isSolution u (mem_eIoo_of_le d ε hx hu hut htp)

theorem orbit_continuousOn {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t : ℝ}
    (htp : (t : EReal) < avgTp h f R ε x) :
    ContinuousOn (fun v => avgFlow h f R ε v x) (Icc 0 t) := fun _ hu =>
  (orbit_hasDerivAt d ε hx hu.1 hu.2 htp).2.continuousAt.continuousWithinAt

theorem orbit_mapsTo {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t : ℝ}
    (htp : (t : EReal) < avgTp h f R ε x) :
    MapsTo (fun v => avgFlow h f R ε v x) (Icc 0 t) (avgDomain n R) := fun _ hu =>
  (orbit_hasDerivAt d ε hx hu.1 hu.2 htp).1

end Orbit

section Main

variable (d : AveragingData n R s h f)
include d

theorem identity {ε κ t : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) {x : AvgPhase n} (hx : x ∈ avgDomain n R)
    (ht : 0 ≤ t) (htp : (t : EReal) < avgTp h f R ε x) :
    KAM.realInclusion n ((avgFlow h f R ε t x).2 - x.2) =
      ε • (avgW h f κ (avgFlow h f R ε t x) - avgW h f κ x) -
      ε ^ 2 • (∫ u in (0 : ℝ)..t, avgCorrectionQ h f κ (avgFlow h f R ε u x)) +
      ε • (∫ u in (0 : ℝ)..t, avgResidual h f κ (avgFlow h f R ε u x)) := by
  have _ := hε
  set γ : ℝ → AvgPhase n := fun v => avgFlow h f R ε v x with hγ
  have hcont := orbit_continuousOn d ε hx htp
  have hmaps := orbit_mapsTo d ε hx htp
  have huI : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  -- `id-eq`, `id-chain`, `id-div`: the derivative of `G = ι I - ε Λ` along the orbit
  have hG : ∀ u ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun v => KAM.realInclusion n (γ v).2 - ε • avgW h f κ (γ v))
        (ε • avgResidual h f κ (γ u) - ε ^ 2 • avgCorrectionQ h f κ (γ u)) u := by
    intro u hu
    rw [huI] at hu
    obtain ⟨hz, hder⟩ := orbit_hasDerivAt d ε hx hu.1 hu.2 htp
    have hF := (fbounds d (γ u) hz).2.2 ε
    have hI : HasDerivAt (fun v => KAM.realInclusion n (γ v).2)
        (KAM.realInclusion n (ε • avgA f (γ u))) u := by
      have h1 := (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin n → ℝ) (F := Fin n → ℝ)
        (p := γ u)).comp_hasDerivAt u hder
      rw [hF] at h1
      exact ((KAM.realInclusion n).hasFDerivAt.comp_hasDerivAt u h1)
    have hL := ((differentiableAt_avgW d hκ hz).hasFDerivAt).comp_hasDerivAt u hder
    rw [hF] at hL
    refine (hI.sub (hL.const_smul ε)).congr_deriv ?_
    have hv : ((KAM.frequencyMap h (γ u).2 + ε • avgB f (γ u), ε • avgA f (γ u)) :
        AvgPhase n) = (KAM.frequencyMap h (γ u).2, 0) + ε • (avgB f (γ u), 0) +
          ε • (0, avgA f (γ u)) := by
      ext <;> simp
    simp only [avgResidual, avgCorrectionQ, hv, map_add, map_smul, map_smul]
    module
  have hrc : ContinuousOn (fun v => avgResidual h f κ (γ v)) (uIcc 0 t) := by
    rw [huI]; exact (continuousOn_avgResidual d hκ).comp hcont hmaps
  have hQc : ContinuousOn (fun v => avgCorrectionQ h f κ (γ v)) (uIcc 0 t) := by
    rw [huI]; exact (continuousOn_avgCorrectionQ d hκ).comp hcont hmaps
  have hint1 : IntervalIntegrable (fun v => avgResidual h f κ (γ v)) volume 0 t :=
    hrc.intervalIntegrable
  have hint2 : IntervalIntegrable (fun v => avgCorrectionQ h f κ (γ v)) volume 0 t :=
    hQc.intervalIntegrable
  have i1 : IntervalIntegrable (fun v => ε • avgResidual h f κ (γ v)) volume 0 t := hint1.smul ε
  have i2 : IntervalIntegrable (fun v => ε ^ 2 • avgCorrectionQ h f κ (γ v)) volume 0 t :=
    hint2.smul (ε ^ 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG (i1.sub i2)
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_smul,
    intervalIntegral.integral_smul] at hFTC
  have h0 : γ 0 = x := (avgMaximal_spec d ε hx).init
  rw [h0] at hFTC
  rw [map_sub]
  linear_combination (norm := module) (-1 : ℝ) • hFTC

end Main

end KAM.Nekhoroshev

end
