/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.NonresonantAdapter
public import KAM.Planetary.Spatial.NonresonantReuse.Hyp
public import KAM.Planetary.StrongAMD.NonresonantReuse.Drift

/-!
# The spatial stopped drift (package LP-SP-NRR, item 4; MAIN Lemma 13 and Theorem 19)

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Package LP-SP-NRR, MAIN Lemma 13 with `2n` slow pairs and Theorem 19
(`LP:MAIN L13 (429–464)`, `LP:MAIN T19 (599–603)`), amendment N6, track LP, non-frozen.

`spatial_stopped_drift` is the conclusion of Lemma 13 in dimension three: constants
`μ₀, c, T₀` and the fixed widths `s, σ, w` are chosen from `(ν, L, δ, γ, τ, D₀)` only, before `μ`,
the centre `I⁰` and the solution.  For `0 < μ ≤ μ₀`, every centre `I⁰ ∈ 𝓛_δ` with the Diophantine
condition (5), and every physical spatial solution with chart lift satisfying the stopped/outer
domain localization premises of `nonresonant_drift_of_chartDataNM`, the Kepler actions stay within
`D₀√μ/2` of `I⁰` up to time `T₀ exp(c μ^{-a})`.  The premises are the physical solution, its chart
lift and the localization; no drift, confinement or AMD bound is assumed.  The stopped radius is
strictly inside the tube radii (`D₀√μ ≤ ρ < r_*`, audit note on N6).
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

namespace KAM.Planetary.Spatial

variable {n : ℕ}

/-- The block of Lemma 13 at the centre `I⁰` with `2n` slow pairs: slow set the ball (47),
stopped radius `r`, width `w`. -/
def lpBlockNM (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) (r w : ℝ) : PartialBlock n (n + n) :=
  ⟨I0, spatialSecularBall ν δ I0, r, w⟩

/-- **MAIN Lemma 13 with `2n` slow pairs, conclusion; MAIN Theorem 19 engine step**
(`LP:MAIN L13 (429–464)`, `LP:MAIN T19 (599–603)`, N6). -/
theorem spatial_stopped_drift {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ : ℝ} (hδ : 0 < δ)
    {γ τ D₀ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hD : 0 < D₀) :
    ∃ μ₀ c T₀ s σ w : ℝ, 0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < s ∧ 0 < σ ∧ 0 < w ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∀ I0 ∈ strongLevelSet ν L δ,
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * KAM.Fourier.modeSize k ^ (-τ) ≤ |∑ i, (k i : ℝ) * (ν i ^ 3 / I0 i ^ 3)|) →
        ∀ b : PartialBlock n (n + n), b = lpBlockNM ν δ I0 (D₀ * √μ) w →
        ∀ {J : Set ℝ}, J.OrdConnected → (0 : ℝ) ∈ J →
        ∀ (z : ℝ → Phase (n * 3)) (wc : ℝ → Phase (n + (n + n))),
          (∀ u ∈ J, wc u ∈ spatialChartSafe ν ∧ spatialPoincareProd ν (wc u) = z u ∧
            HasDerivAt wc (hamiltonianVectorField (lpChartHamNM ν μ) (wc u)) u) →
          (∀ u ∈ J, lpRescaleNM b.lam (wc u) ∈ b.realDom b.rB) →
          fast (wc 0).2 = I0 →
          ∀ {t1 : ℝ}, t1 ∈ J →
          |t1| ≤ T₀ * Real.exp (c * μ ^ (-scaleExponent τ)) →
          (∀ u ∈ uIcc 0 t1, (slow (wc u).1, slow (wc u).2) ∈ spatialSecularBall ν δ I0) →
          ∀ u ∈ uIcc 0 t1, ‖(fun i => spatialKeplerAction ν (z u) i) - I0‖ ≤ D₀ * √μ / 2 := by
  obtain ⟨rg, hg⟩ := exists_isSharedTube hν hn hL hLch hδ
  obtain ⟨R, hR, M, fc, hhol, hreal, hper, hbd⟩ := exists_spatialStrongTube hν hn hL hLch hg hδ
  have hT : LPChartTubeNM ν L δ rg R (max M 1) fc :=
    ⟨hR, hhol, hreal, hper, fun z hz => (hbd z hz).trans (le_max_left _ _)⟩
  have hLδ := isCompact_strongLevelSet hν hn hL hLch δ
  obtain ⟨Imin, hImin, hIlow⟩ := lp_exists_lower_bound hLδ fun I hI i =>
    (hLch hI.1).1 i
  have hpi := Real.pi_pos
  have hrg := hg.pos
  -- the fixed widths
  set s₀ : ℝ := R / 16 with hs₀
  set b₀ : ℝ := R / 16 with hb₀
  set rs : ℝ := min (4 * rg) (R / 4) with hrs
  have hrs0 : 0 < rs := lt_min (by linarith) (by linarith)
  have hmax : max rs (max (4 * s₀) (4 * b₀)) < R / 2 := by
    have : rs ≤ R / 4 := min_le_right _ _
    simp only [hs₀, hb₀, max_self]
    rw [max_lt_iff]; constructor <;> linarith
  set s : ℝ := s₀ / Real.pi with hs
  set σ : ℝ := s₀ / Real.pi with hσ
  set w : ℝ := 2 * b₀ with hw
  have hs0 : 0 < s := by have : 0 < s₀ := by rw [hs₀]; linarith
                         positivity
  have hw0 : 0 < w := by rw [hw, hb₀]; linarith
  have hwlt : w < 4 * b₀ := by rw [hw, hb₀]; linarith
  have hts : 2 * Real.pi * (s + σ) ≤ 4 * s₀ := by
    rw [hs, hσ]; apply le_of_eq; field_simp; ring
  set ρ : ℝ := min rs Imin / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; have := lt_min hrs0 hImin; linarith
  have hM1 : 0 < max M 1 := lt_max_of_lt_right one_pos
  have hM₂ := lpM₂_pos (n := n) hs0 hM1
  obtain ⟨κ, μ₀, c, T₀, hκ, hμ₀, hc, hT₀, hscale⟩ := lp_scale_choice (γ := γ) (τ := τ)
    (L := lpKeplerLip ν Imin) (M₂ := lpM₂ n σ (max M 1)) (D₀ := D₀) (s := s) (w := w) (ρ := ρ)
    (k := n + n) hγ hτ (lpKeplerLip_nonneg hν Imin) hM₂ hD hs0 hw0 hρ0 (by omega)
  refine ⟨μ₀, c, T₀, s, σ, w, hμ₀, hc, hT₀, hs0, hs0, hw0, ?_⟩
  intro μ hμ hμμ₀ I0 hI0 hdio b hb J hJ h0 z wc hlift hmem hinit t1 ht1 ht hstop
  subst hb
  obtain ⟨⟨hK1, -, -⟩, hKL, hsmall, hSL, hcut, hrρ, hTime⟩ := hscale μ hμ hμμ₀
  have hrB0 : 0 < D₀ * √μ := by have := Real.sqrt_pos.2 hμ; positivity
  have hrB : D₀ * √μ ≤ rs := hrρ.trans (by
    rw [hρ]; have := min_le_left rs Imin; linarith)
  have hρI : D₀ * √μ ≤ Imin / 2 := hrρ.trans (by
    rw [hρ]; have := min_le_right rs Imin; linarith)
  have hI0pos := hIlow I0 hI0
  have hh := lpExtNFHypNM (b := lpBlockNM ν δ I0 (D₀ * √μ) w) hν hn hT hrs0 (min_le_left _ _)
    hmax hI0 rfl rfl hrB hrB0 hw0 hwlt hImin hI0pos hρI hγ hτ hdio hM1 hs0 hs0 hμ hts hK1 hKL
    hSL hcut
  have htr : ∀ y ∈ (lpBlockNM ν δ I0 (D₀ * √μ) w).realDom
      (lpBlockNM ν δ I0 (D₀ * √μ) w).rB,
      ((liftFast (lpKepler ν) + lpPertNM μ (lpBlockNM ν δ I0 (D₀ * √μ) w).lam fc :
          EC n (n + n) → ℂ) (extCx y)).re =
        lpRescaleHamNM (lpBlockNM ν δ I0 (D₀ * √μ) w).lam (lpChartHamNM ν μ) y := fun y hy =>
    lpTraceNM hν hT hrs0 (min_le_left _ _) hmax (by rw [hs₀]; linarith) hI0 rfl rfl hrB hrB0 hw0
      hwlt μ hy
  have hTime' : |t1| ≤ s * (lpBlockNM ν δ I0 (D₀ * √μ) w).rB /
      (5 * (lpM₂ n σ (max M 1) * μ)) *
      Real.exp (2 * Real.pi * scaledCutoff κ τ μ * s / 6) := ht.trans hTime
  have hsub : uIcc (0 : ℝ) t1 ⊆ J := hJ.uIcc_subset h0 ht1
  have hd : ∀ u ∈ J, DifferentiableAt ℝ (lpChartHamNM ν μ) (wc u) := fun u hu =>
    ((analyticOnNhd_spatialHamiltonian_spatialPoincareProd hν μ) _
      (hlift u hu).1).differentiableAt
  have key := nonresonant_drift_of_chartDataNM (lpBlockNM ν δ I0 (D₀ * √μ) w) hh hsmall htr hJ h0
    hd (fun u hu => (hlift u hu).2.2) hmem hinit ht1 hTime' hstop
  intro u hu
  obtain ⟨hws, hzu, -⟩ := hlift u (hsub hu)
  have hact := spatialActionVector_spatialPoincareProd hν (spatialChartSafe_subset_dom ν hws)
  rw [hzu] at hact
  have := key u hu
  have e : (fun i => spatialKeplerAction ν (z u) i) = fast (wc u).2 := hact
  rw [e]
  exact this

end KAM.Planetary.Spatial

end
