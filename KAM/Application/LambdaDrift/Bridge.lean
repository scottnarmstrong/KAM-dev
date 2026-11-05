/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.AMD.ConfinementExit
public import KAM.Planetary.StrongAMD.ChartLift.Lift
public import KAM.Planetary.StrongAMD.Momentum

/-!
# The Λ-drift bridge: approximate integrals give the stopped drift

Design `docs/campaign/design/HD11964-PILOT.md` §4 (with the domain fix of AUDIT-HD11964-PILOT-1 §2).
Additive core; reusable for any planar system of `n ≥ 2` planets.

`stoppedDrift_of_approxIntegrals` discharges the `hstop` hypothesis of LP-CONF's
`strongFirstExit_of_stopped_drift` from an *approximate-integral certificate* in LP's Poincaré
chart: functions `F i` on the chart, differentiable on an open `O`, with
* `|dF_i (X_H)| ≤ η_i` on a region `R ⊆ O` (`X_H` the chart field of `liftChartHam ν μ`), and
* `lo_i ≤ F_i - Λ_i ≤ hi_i` on `R`,
* `R` containing every chart point of `chartSafe ν` whose actions are within `d` of `Λ(z₀)` and
  whose chart AMD is at most `C(z₀) + n d`,
* `η_i T + (hi_i - lo_i) < d ≤ r / 2`.

The proof lifts the stopped orbit to the chart (`lpChartLift_of_stopped`, LP-LIFT) and runs a
one-dimensional first exit (`amd_exit_forward`/`amd_exit_backward`) for the action drift at level
`d`: while the drift is `< d`, exact conservation of `L` (`strongAMD_sub_eq_sum`) keeps the chart
AMD below `C(z₀) + n d`, so the orbit is in `R`; the mean value inequality for `F_i` along the lift
and the range of `F_i - Λ_i` then give drift `≤ η_i T + (hi_i - lo_i) < d`.

No periodicity of `F` is needed here: `F` is evaluated along one chart lift. Periodicity enters only
when a cover of a fundamental domain of the angles is turned into a bound on `R`.

## Main results

* `abs_sub_le_of_fderiv_bound`: the mean value step along a chart curve.
* `stoppedDrift_of_approxIntegrals`: the `hstop` hypothesis of `strongFirstExit_of_stopped_drift`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- The mean value step: along a curve `w` that solves `ẇ = X(w)` and stays in `R` on `[a, b]`, a
function `F` differentiable on an open `O ⊇ R`, with `|dF(X)| ≤ η` on `R`, changes by at most
`η (b - a)`. -/
theorem abs_sub_le_of_fderiv_bound {F : Phase (n + n) → ℝ} {O R : Set (Phase (n + n))}
    (hO : IsOpen O) (hRO : R ⊆ O) (hF : DifferentiableOn ℝ F O)
    {X : Phase (n + n) → Phase (n + n)} {η : ℝ} (hη : ∀ w ∈ R, |fderiv ℝ F w (X w)| ≤ η)
    {w : ℝ → Phase (n + n)} {a b : ℝ} (hab : a ≤ b)
    (hw : ∀ u ∈ Icc a b, w u ∈ R ∧ HasDerivAt w (X (w u)) u) :
    |F (w b) - F (w a)| ≤ η * (b - a) := by
  have hderiv : ∀ u ∈ Icc a b,
      HasDerivAt (fun s => F (w s)) (fderiv ℝ F (w u) (X (w u))) u := fun u hu =>
    ((hF.differentiableAt (hO.mem_nhds (hRO (hw u hu).1))).hasFDerivAt).comp_hasDerivAt u
      (hw u hu).2
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => F (w s))
    (fun u hu => (hderiv u hu).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hη _ (hw u (Ico_subset_Icc_self hu)).1) b ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs] at this

private theorem continuous_fast_snd' : Continuous fun w : Phase (n + n) => fast w.2 := by
  unfold fast
  exact continuous_pi fun i => (continuous_apply _).comp continuous_snd

/-- **The Λ-drift bridge** (design §4). An approximate-integral certificate on a chart region `R`
discharges the `hstop` hypothesis of `strongFirstExit_of_stopped_drift` (LP-CONF) with drift
`r / 2`, for every time `|t| ≤ T`.

* `F`, `R`, `O`, `η`, `lo`, `hi`: the certificate (`F` differentiable on the open `O ⊇ R`);
* `hR`: `R` contains the chart points of `chartSafe ν` with actions within `d` of `Λ(z₀)` and chart
  AMD at most `C(z₀) + n d`;
* `hη`: `|dF_i (X_H)| ≤ η_i` on `R`, for the chart field `X_H` of `liftChartHam ν μ`;
* `hG`: `lo_i ≤ F_i - Λ_i ≤ hi_i` on `R`;
* `hd0`, `hT`, `hdr`: `0 < d`, `η_i T + (hi_i - lo_i) < d`, `d ≤ r / 2`. -/
theorem stoppedDrift_of_approxIntegrals {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)}
    {z₀ : Phase (n * 2)} {δ r : ℝ} (hd : LiftData ν U z₀ δ r) {μ T d : ℝ}
    (F : Fin n → Phase (n + n) → ℝ) (R O : Set (Phase (n + n))) (η lo hi : Fin n → ℝ)
    (hO : IsOpen O) (hRO : R ⊆ O) (hF : ∀ i, DifferentiableOn ℝ (F i) O)
    (hR : ∀ w ∈ chartSafe ν, (∀ i, |fast w.2 i - actionVector ν z₀ i| ≤ d) →
      chartAMD w ≤ strongAMD ν z₀ + n * d → w ∈ R)
    (hη : ∀ i, ∀ w ∈ R,
      |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η i)
    (hG : ∀ i, ∀ w ∈ R, lo i ≤ F i w - fast w.2 i ∧ F i w - fast w.2 i ≤ hi i)
    (hd0 : 0 < d) (hT : ∀ i, η i * T + (hi i - lo i) < d) (hdr : d ≤ r / 2) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
      IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J, |t| ≤ T →
        StoppedOn ν z₀ δ r z t →
        ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ r / 2 := by
  intro J hJ h0 z hz hz0 t ht htT hs
  obtain ⟨w, I, -, -, hsub, hwI, hproj, hinit⟩ := hd.lpChartLift_of_stopped hJ h0 hz hz0 ht hs
  have hν := hd.pos_mass
  have hK0 : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  have hKJ : uIcc (0 : ℝ) t ⊆ J := hJ.uIcc_subset h0 ht
  have hdom : ∀ u ∈ uIcc (0 : ℝ) t, w u ∈ poincareProdDom n := fun u hu =>
    chartSafe_subset_dom ν (hwI u (hsub hu)).1
  have hfast : ∀ u ∈ uIcc (0 : ℝ) t, fast (w u).2 = actionVector ν (z u) := fun u hu => by
    funext i
    rw [← lpChart_action hν (hdom u hu) i, hproj u hu]
    rfl
  -- the drift curve and the two sets of the first exit
  set y : ℝ → (Fin n → ℝ) := fun u => fast (w u).2 - actionVector ν z₀ with hy
  set c : Fin n → ℝ := fun i => η i * T + (hi i - lo i) with hc
  set C : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ c i} with hCdef
  set V : Set (Fin n → ℝ) := Metric.ball 0 d with hVdef
  have hy0 : y 0 = 0 := by simp [hy, hinit]
  -- inside the open drift ball the lift is in `R`
  have hinR : ∀ u ∈ uIcc (0 : ℝ) t, y u ∈ V → w u ∈ R := by
    intro u hu hyu
    have hlt : ∀ i, |fast (w u).2 i - actionVector ν z₀ i| < d := fun i => by
      have h1 := norm_le_pi_norm (y u) i
      have h2 : ‖y u‖ < d := by simpa [hVdef] using hyu
      simpa [hy, Real.norm_eq_abs] using lt_of_le_of_lt h1 h2
    refine hR _ (hwI u (hsub hu)).1 (fun i => (hlt i).le) ?_
    have hA : chartAMD (w u) = strongAMD ν (z u) := by
      rw [← lpChart_strongAMD hν (hdom u hu), hproj u hu]
    have hsum := strongAMD_sub_eq_sum hJ hz h0 (hKJ hu)
    have hsum' : ∑ i, (keplerAction ν (z u) i - keplerAction ν (z 0) i) ≤ n * d := by
      calc ∑ i, (keplerAction ν (z u) i - keplerAction ν (z 0) i)
          ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => by
            have h3 := (abs_lt.1 (hlt i)).2
            have h4 : fast (w u).2 i = keplerAction ν (z u) i := by
              rw [hfast u hu]; rfl
            rw [hz0]
            change keplerAction ν (z u) i - actionVector ν z₀ i ≤ d
            linarith
        _ = n * d := by simp
    rw [hz0] at hsum hsum'
    linarith
  have hw0R : w 0 ∈ R := hinR 0 hK0 (by rw [hy0]; exact Metric.mem_ball_self hd0)
  have hη0 : ∀ i, 0 ≤ η i := fun i => (abs_nonneg _).trans (hη i _ hw0R)
  -- the segment estimate between two times of a segment of `uIcc 0 t` inside the drift ball
  have hseg : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ uIcc 0 t → b - a ≤ T → (∀ u ∈ Icc a b, y u ∈ V) →
      ∀ i, |y b i - y a i| ≤ c i := by
    intro a b hab hsubab hT' hV i
    have hwR : ∀ u ∈ Icc a b, w u ∈ R ∧
        HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u := fun u hu =>
      ⟨hinR u (hsubab hu) (hV u hu), (hwI u (hsub (hsubab hu))).2⟩
    have hmv := abs_sub_le_of_fderiv_bound hO hRO (hF i) (hη i) hab hwR
    have hGa := hG i _ (hwR a ⟨le_rfl, hab⟩).1
    have hGb := hG i _ (hwR b ⟨hab, le_rfl⟩).1
    have hyb : y b i - y a i = (F i (w b) - F i (w a)) -
        ((F i (w b) - fast (w b).2 i) - (F i (w a) - fast (w a).2 i)) := by
      simp only [hy, Pi.sub_apply]; ring
    rw [hyb]
    have hηT : η i * (b - a) ≤ η i * T := mul_le_mul_of_nonneg_left hT' (hη0 i)
    have hmv' := abs_le.1 hmv
    show _ ≤ η i * T + (hi i - lo i)
    rw [abs_le]
    constructor <;> linarith [hGa.1, hGa.2, hGb.1, hGb.2, hmv'.1, hmv'.2]
  -- the first exit, forwards and backwards
  have hVo : IsOpen V := Metric.isOpen_ball
  have hCV : C ⊆ V := fun x hx => by
    have hx' : ∀ i, |x i| ≤ c i := hx
    show x ∈ Metric.ball 0 d
    rw [Metric.mem_ball, dist_zero_right]
    exact (pi_norm_lt_iff hd0).2 fun i => by
      rw [Real.norm_eq_abs]; exact lt_of_le_of_lt (hx' i) (hT i)
  have hCc : IsClosed C := by
    have : C = ⋂ i, {x : Fin n → ℝ | |x i| ≤ c i} := by ext x; simp [hCdef]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const
  have hclosed : ∀ (x : ℕ → Fin n → ℝ) (xs : Fin n → ℝ), (∀ k, x k ∈ C) →
      Tendsto x atTop (𝓝 xs) → xs ∈ (univ : Set (Fin n → ℝ)) → xs ∈ C := fun x xs hx hl _ =>
    hCc.mem_of_tendsto hl (Eventually.of_forall hx)
  have hycont : ContinuousOn y (uIcc 0 t) := fun u hu =>
    ((continuous_fast_snd'.continuousAt.comp (hwI u (hsub hu)).2.continuousAt).sub
      continuousAt_const).continuousWithinAt
  have hyV0 : y 0 ∈ V := by rw [hy0]; exact Metric.mem_ball_self hd0
  have htT' : ∀ s ∈ uIcc (0 : ℝ) t, |s| ≤ T := fun s hs => by
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg hs.1]; exact hs.2.trans ((le_abs_self t).trans htT)
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos hs.2]; linarith [neg_le_abs t, hs.1]
  have hfwd := amd_exit_forward ordConnected_uIcc hK0 hycont hVo hCV hclosed
    (fun _ _ => mem_univ _) hyV0 (fun s hs hs0 hV => by
      have hsub' : Icc 0 s ⊆ uIcc 0 t := ordConnected_uIcc.out hK0 hs
      have h := hseg 0 s hs0 hsub' (by simpa [abs_of_nonneg hs0] using htT' s hs)
        (fun u hu => hV u hu.1 hu.2)
      show ∀ i, |y s i| ≤ c i
      intro i
      simpa [hy0] using h i)
  have hbwd := amd_exit_backward ordConnected_uIcc hK0 hycont hVo hCV hclosed
    (fun _ _ => mem_univ _) hyV0 (fun s hs hs0 hV => by
      have hsub' : Icc s 0 ⊆ uIcc 0 t := ordConnected_uIcc.out hs hK0
      have h := hseg s 0 hs0 hsub' (by
          have := htT' s hs
          rw [abs_of_nonpos hs0] at this; linarith)
        (fun u hu => hV u hu.1 hu.2)
      show ∀ i, |y s i| ≤ c i
      intro i
      have := h i
      rw [hy0, Pi.zero_apply, zero_sub, abs_neg] at this
      exact this)
  have hyt : y t ∈ C := by
    rcases le_total 0 t with h | h
    · exact hfwd t right_mem_uIcc h
    · exact hbwd t right_mem_uIcc h
  have hyt' : actionVector ν (z t) - actionVector ν z₀ = y t := by
    simp only [hy, hfast t right_mem_uIcc]
  have hyt2 : ∀ i, |y t i| ≤ c i := hyt
  rw [hyt']
  refine ((pi_norm_le_iff_of_nonneg hd0.le).2 fun i => ?_).trans hdr
  rw [Real.norm_eq_abs]
  exact (hyt2 i).trans (hT i).le

end KAM.Application.LambdaDrift

end
