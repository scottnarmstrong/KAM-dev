/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsIdent

/-!
# P Part 5: the remainder jet vanishes on the real slice (`bpP:p5:be-jet`)

For `I ∈ V` the complex remainder `pgRemainder` restricted to real vectors is
`ofReal ∘ birkRem`, an analytic `o(‖y‖⁴)` function; hence its real jets vanish through order four
and, a complex multilinear map being determined by its values on real vectors, so do its complex
jets (`remainder_jet_real`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- The complex oscillator actions of a complex jet vector. -/
def cOsc (x : PGComplexPhase b) (j : Fin b) : ℂ := (x.1 j ^ 2 + x.2 j ^ 2) / 2

/-- The Birkhoff polynomial with complex coefficients. -/
def cPoly (c0 : ℂ) (Om : Fin b → ℂ) (be : Matrix (Fin b) (Fin b) ℂ) (x : PGComplexPhase b) : ℂ :=
  c0 + ∑ j, Om j * cOsc x j + (1 / 2 : ℂ) * ∑ i, ∑ j, be i j * cOsc x i * cOsc x j

theorem analyticAt_cOsc (j : Fin b) (z : PGComplexPhase b) :
    AnalyticAt ℂ (fun x : PGComplexPhase b => cOsc x j) z := by
  have h1 : AnalyticAt ℂ (fun x : PGComplexPhase b => x.1 j) z :=
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _)).analyticAt z
  have h2 : AnalyticAt ℂ (fun x : PGComplexPhase b => x.2 j) z :=
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)).analyticAt z
  unfold cOsc
  fun_prop

theorem analyticAt_cPoly (c0 : ℂ) (Om : Fin b → ℂ) (be : Matrix (Fin b) (Fin b) ℂ)
    (z : PGComplexPhase b) : AnalyticAt ℂ (cPoly c0 Om be) z := by
  have h := fun j => analyticAt_cOsc j z
  unfold cPoly
  fun_prop

theorem pgRemainder_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (x : PGComplexPhase b) :
    pgRemainder d mu (KAM.realInclusion a I) x = complexAverage d mu (KAM.realInclusion a I) x -
      cPoly (d.P0 mu I : ℂ) (fun j => (d.Omega mu I j : ℂ))
        (fun i j => (d.beta mu I i j : ℂ)) x := by
  have hf : blockFast (Fin.append (KAM.realInclusion a I) (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2) :
      Fin (a + b) → ℂ) = KAM.realInclusion a I := funext fun i => Fin.append_left _ _ i
  have hs : ∀ j, blockSlow (Fin.append (KAM.realInclusion a I)
      (fun j => (x.1 j ^ 2 + x.2 j ^ 2) / 2) : Fin (a + b) → ℂ) j = cOsc x j := fun j =>
    Fin.append_right _ _ j
  unfold pgRemainder jetPolynomial cPoly
  rw [hf]
  simp only [hs, jetP0_real d hmu hI, jetOmega_real d hmu hI, jetBeta_real d hmu hI]

theorem remainder_jet_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (k : ℕ) (hk : k ≤ 4) :
    iteratedFDeriv ℂ k (pgRemainder d mu (KAM.realInclusion a I)) 0 = 0 := by
  have hAn := complexAverage_analyticAt d hmu (realInclusion_mem_tube d (subset_closure hI))
  have hfun : pgRemainder d mu (KAM.realInclusion a I) = fun x =>
      complexAverage d mu (KAM.realInclusion a I) x -
        cPoly (d.P0 mu I : ℂ) (fun j => (d.Omega mu I j : ℂ))
          (fun i j => (d.beta mu I i j : ℂ)) x :=
    funext fun x => pgRemainder_real d hmu hI x
  have hRc : AnalyticAt ℂ (pgRemainder d mu (KAM.realInclusion a I)) 0 := by
    rw [hfun]; exact hAn.sub (analyticAt_cPoly _ _ _ 0)
  have hev : ∀ᶠ y in 𝓝 (0 : RY b),
      pgRemainder d mu (KAM.realInclusion a I) (KAM.realInclusion₂ b y) =
        (birkRem d mu I y : ℂ) := by
    filter_upwards [complexAverage_realY_eventually d hmu hI] with y hy
    rw [pgRemainder_real d hmu hI, hy]
    have hc : cPoly (d.P0 mu I : ℂ) (fun j => (d.Omega mu I j : ℂ))
        (fun i j => (d.beta mu I i j : ℂ)) (KAM.realInclusion₂ b y) =
          (birkPoly d mu I y : ℂ) := by
      have hs : ∀ j, cOsc (KAM.realInclusion₂ b y) j = (oscS y j : ℂ) := fun j => by
        simp only [cOsc, oscS, KAM.realInclusion₂_apply, KAM.realInclusion_apply]
        push_cast
        ring
      simp only [cPoly, birkPoly, oscPoly, oscQ2, oscQ4, hs]
      push_cast
      ring
    rw [hc, birkRem]
    push_cast
    ring
  have hra : AnalyticAt ℝ (birkRem d mu I) 0 :=
    (realAvg_analyticAt d hmu hI).sub (analyticAt_oscPoly _ _ _ 0)
  have hzero := fourth_jet_unique_gen hra (birkRem_isLittleO d hmu hI) k hk
  refine multilinear_eq_zero_of_real _ fun v => ?_
  rw [jet_real_restrict hRc hev k v, hzero]
  simp

end KAM.Planetary

end
