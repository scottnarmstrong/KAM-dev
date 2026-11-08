/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.Bridge

/-!
# The observable Λ-drift bridge: the first exit driven by an observable `G`

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §4 (branch `lp-redmass-scope`). Additive core;
reusable for any planar system of `n ≥ 2` planets; non-frozen.

`stoppedDrift_of_approxIntegrals` (`Bridge.lean`) charges the whole range of `F_i - Λ_i` against the
certified drift `d`. That range contains the genuine oscillation of the heliocentric action `Λ_i`
along the orbit (for HD 11964 b, `≈ 2 μ ν Λ e`). `stoppedDrift_of_approxIntegrals_obs` runs the same
first exit on the drift `y = G(w u) - G(w 0)` of an observable `G` (for HD 11964 the reduced
Delaunay actions, `ReducedElements.lean`) and charges the range of `G_i - Λ_i` on the stopped tube
(`ε`) against `r / 2 - d` instead:

* `|dF_i (X_H)| ≤ η_i` and `lo_i ≤ F_i - G_i ≤ hi_i` on a region `R ⊆ O` (`F` differentiable on the
  open `O`);
* `G` continuous on the chart tube `chartTube ν z₀ r`, with `loG_i ≤ G_i - Λ_i ≤ hiG_i` there and
  `hiG_i - loG_i ≤ ε`;
* `R` containing every chart point of `chartSafe ν` whose `G`-values are within `d` of those of a
  lift of `z₀`, whose actions are within `d + ε` of `Λ(z₀)` and whose chart AMD is at most
  `C(z₀) + n (d + ε)`;
* `η_i T + (hi_i - lo_i) < d` and `d + ε ≤ r / 2`.

The conclusion is verbatim the `hstop` hypothesis of LP-CONF's `strongFirstExit_of_stopped_drift`,
the conclusion of `stoppedDrift_of_approxIntegrals`.

The proof lifts the stopped orbit to the chart (`lpChartLift_of_stopped`); the stopped conditions
put the lift in `chartTube ν z₀ r` (exact conservation of `L`, `strongAMD_sub_eq_sum`), where the
range of `G - Λ` turns a `G`-drift `< d` into a Λ-drift `≤ d + ε`; then the AMD is at most
`C(z₀) + n (d + ε)` and the lift is in `R`, and the mean value step for `F_i` and the range of
`F_i - G_i` give `G`-drift `≤ η_i T + (hi_i - lo_i) < d`. The final Λ-drift is `≤ d + ε ≤ r / 2`.

## Main results

* `chartTube`: the chart image of the stopped tube.
* `stoppedDrift_of_approxIntegrals_obs`: the `hstop` hypothesis of
  `strongFirstExit_of_stopped_drift`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- The chart stopped tube of `z₀`: chart points of `chartSafe ν` with actions strictly within `r`
of `Λ(z₀)` and chart AMD at most `C(z₀) + n r`. The chart lift of an orbit satisfying the stopped
conditions stays in it (`lift_mem_chartTube`). -/
def chartTube (ν : Fin n → ℝ) (z₀ : Phase (n * 2)) (r : ℝ) : Set (Phase (n + n)) :=
  {w | w ∈ chartSafe ν ∧ ‖fast w.2 - actionVector ν z₀‖ < r ∧
    chartAMD w ≤ strongAMD ν z₀ + n * r}

/-- Along a moving solution, the strong AMD moves by the sum of the action moves, and an action
move `≤ a` per planet bounds the AMD by `C(z₀) + n a`. -/
theorem strongAMD_le_of_action_drift {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z) (h0 : (0 : ℝ) ∈ J) {u : ℝ}
    (hu : u ∈ J) {a : ℝ} (ha : ∀ i, actionVector ν (z u) i - actionVector ν (z 0) i ≤ a) :
    strongAMD ν (z u) ≤ strongAMD ν (z 0) + n * a := by
  have hsum := strongAMD_sub_eq_sum hJ hz h0 hu
  have hle : ∑ i, (keplerAction ν (z u) i - keplerAction ν (z 0) i) ≤ n * a :=
    calc ∑ i, (keplerAction ν (z u) i - keplerAction ν (z 0) i)
        ≤ ∑ _i : Fin n, a := Finset.sum_le_sum fun i _ => ha i
      _ = n * a := by simp
  linarith

/-- **The observable Λ-drift bridge** (scoping note §4). An approximate-integral certificate for
an observable `G` on a chart region `R`, with the range of `G - Λ` on the chart tube, discharges
the `hstop` hypothesis of `strongFirstExit_of_stopped_drift` (LP-CONF) with drift `r / 2`, for
every time `|t| ≤ T`.

* `F`, `R`, `O`, `η`, `lo`, `hi`: the certificate (`F` differentiable on the open `O ⊇ R`);
* `G`, `loG`, `hiG`, `ε`: the observable, continuous on `chartTube ν z₀ r` (`hGc`), with
  `loG_i ≤ G_i - Λ_i ≤ hiG_i` there (`hGΛ`) and `hiG_i - loG_i ≤ ε` (`hε`);
* `hR`: `R` contains the chart points of `chartSafe ν` with `G`-values within `d` of those of a
  chart lift `w₀` of `z₀`, actions within `d + ε` of `Λ(z₀)` and chart AMD at most
  `C(z₀) + n (d + ε)`;
* `hη`: `|dF_i (X_H)| ≤ η_i` on `R`, for the chart field `X_H` of `liftChartHam ν μ`;
* `hFG`: `lo_i ≤ F_i - G_i ≤ hi_i` on `R`;
* `hd0`, `hT`, `hdr`: `0 < d`, `η_i T + (hi_i - lo_i) < d`, `d + ε ≤ r / 2`. -/
theorem stoppedDrift_of_approxIntegrals_obs {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)}
    {z₀ : Phase (n * 2)} {δ r : ℝ} (hd : LiftData ν U z₀ δ r) {μ T d ε : ℝ}
    (G F : Fin n → Phase (n + n) → ℝ) (R O : Set (Phase (n + n)))
    (η lo hi loG hiG : Fin n → ℝ)
    (hO : IsOpen O) (hRO : R ⊆ O) (hF : ∀ i, DifferentiableOn ℝ (F i) O)
    (hGc : ∀ i, ContinuousOn (G i) (chartTube ν z₀ r))
    (hGΛ : ∀ i, ∀ w ∈ chartTube ν z₀ r,
      loG i ≤ G i w - fast w.2 i ∧ G i w - fast w.2 i ≤ hiG i)
    (hR : ∀ w₀ ∈ chartSafe ν, poincareProd ν 1 w₀ = z₀ → ∀ w ∈ chartSafe ν,
      (∀ i, |G i w - G i w₀| ≤ d) → (∀ i, |fast w.2 i - actionVector ν z₀ i| ≤ d + ε) →
      chartAMD w ≤ strongAMD ν z₀ + n * (d + ε) → w ∈ R)
    (hη : ∀ i, ∀ w ∈ R,
      |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η i)
    (hFG : ∀ i, ∀ w ∈ R, lo i ≤ F i w - G i w ∧ F i w - G i w ≤ hi i)
    (hd0 : 0 < d) (hT : ∀ i, η i * T + (hi i - lo i) < d) (hε : ∀ i, hiG i - loG i ≤ ε)
    (hdr : d + ε ≤ r / 2) :
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
  have hAMD : ∀ u ∈ uIcc (0 : ℝ) t, chartAMD (w u) = strongAMD ν (z u) := fun u hu => by
    rw [← lpChart_strongAMD hν (hdom u hu), hproj u hu]
  have hw0 : poincareProd ν 1 (w 0) = z₀ := by rw [hproj 0 hK0, hz0]
  have hw0S : w 0 ∈ chartSafe ν := (hwI 0 (hsub hK0)).1
  -- the stopped conditions put the lift in the chart tube
  have htube : ∀ u ∈ uIcc (0 : ℝ) t, w u ∈ chartTube ν z₀ r := by
    intro u hu
    have hlt := (hs u hu).2.1
    refine ⟨(hwI u (hsub hu)).1, by rw [hfast u hu]; exact hlt, ?_⟩
    rw [hAMD u hu, ← hz0]
    refine strongAMD_le_of_action_drift hJ hz h0 (hKJ hu) fun i => ?_
    rw [hz0]
    have h1 := norm_le_pi_norm (actionVector ν (z u) - actionVector ν z₀) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans hlt.le)
  -- on the tube, the action drift is at most the `G`-drift plus `ε`
  have hΛG : ∀ u ∈ uIcc (0 : ℝ) t, ∀ i,
      |fast (w u).2 i - actionVector ν z₀ i| ≤ |G i (w u) - G i (w 0)| + ε := by
    intro u hu i
    have h1 := hGΛ i _ (htube u hu)
    have h2 := hGΛ i _ (htube 0 hK0)
    have h3 : fast (w 0).2 i = actionVector ν z₀ i := by rw [hinit]
    rw [h3] at h2
    have h4 := hε i
    have h5 := le_abs_self (G i (w u) - G i (w 0))
    have h6 := neg_abs_le (G i (w u) - G i (w 0))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the drift curve of `G` and the two sets of the first exit
  set y : ℝ → (Fin n → ℝ) := fun u i => G i (w u) - G i (w 0) with hy
  set c : Fin n → ℝ := fun i => η i * T + (hi i - lo i) with hc
  set C : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ c i} with hCdef
  set V : Set (Fin n → ℝ) := Metric.ball 0 d with hVdef
  have hy0 : y 0 = 0 := by funext i; simp [hy]
  -- inside the open drift ball the lift is in `R`
  have hinR : ∀ u ∈ uIcc (0 : ℝ) t, y u ∈ V → w u ∈ R := by
    intro u hu hyu
    have hlt : ∀ i, |G i (w u) - G i (w 0)| < d := fun i => by
      have h1 := norm_le_pi_norm (y u) i
      have h2 : ‖y u‖ < d := by simpa [hVdef] using hyu
      simpa [hy, Real.norm_eq_abs] using lt_of_le_of_lt h1 h2
    have hΛ : ∀ i, |fast (w u).2 i - actionVector ν z₀ i| ≤ d + ε := fun i =>
      (hΛG u hu i).trans (by linarith [hlt i])
    refine hR (w 0) hw0S hw0 _ (hwI u (hsub hu)).1 (fun i => (hlt i).le) hΛ ?_
    rw [hAMD u hu, ← hz0]
    refine strongAMD_le_of_action_drift hJ hz h0 (hKJ hu) fun i => ?_
    have h1 := hΛ i
    rw [hfast u hu] at h1
    rw [hz0]
    exact (le_abs_self _).trans h1
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
    have hGa := hFG i _ (hwR a ⟨le_rfl, hab⟩).1
    have hGb := hFG i _ (hwR b ⟨hab, le_rfl⟩).1
    have hyb : y b i - y a i = (F i (w b) - F i (w a)) -
        ((F i (w b) - G i (w b)) - (F i (w a) - G i (w a))) := by
      simp only [hy]; ring
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
  have hwc : ContinuousOn w (uIcc 0 t) := fun u hu =>
    (hwI u (hsub hu)).2.continuousAt.continuousWithinAt
  have hycont : ContinuousOn y (uIcc 0 t) := by
    refine continuousOn_pi.2 fun i => ?_
    exact ((hGc i).comp hwc fun u hu => htube u hu).sub continuousOn_const
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
  have hyt2 : ∀ i, |y t i| ≤ c i := hyt
  -- the final action drift: `≤ d + ε ≤ r / 2`
  have hr2 : 0 ≤ r / 2 := by linarith [hd.r_pos]
  refine (pi_norm_le_iff_of_nonneg hr2).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, ← hfast t right_mem_uIcc]
  have h1 : |G i (w t) - G i (w 0)| ≤ c i := hyt2 i
  have h2 := hT i
  calc |fast (w t).2 i - actionVector ν z₀ i| ≤ |G i (w t) - G i (w 0)| + ε :=
        hΛG t right_mem_uIcc i
    _ ≤ d + ε := by simp only [hc] at h1; linarith
    _ ≤ r / 2 := hdr

end KAM.Application.LambdaDrift

end
