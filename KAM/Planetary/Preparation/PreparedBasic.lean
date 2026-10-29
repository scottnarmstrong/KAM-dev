/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Planetary.Preparation.SlowAverageDom
public import KAM.Planetary.Preparation.SlowSmall
public import KAM.Planetary.Preparation.SlowDivisor
public import KAM.Weighted.SupWeighted

/-!
# Prepared data: the basic construction (P11A-P8a, `stepP:p11:pr-basic`, `stepP:p11:pr-a`)

The prepared data `Q = p11PreparedCore D nu eps W` is built from the signed `avg_slow`, `avg_fast`,
`holo_chart` data: `N_eps = (h_0 + g_2) o A_eps / eps` and `P_eps = f_3 o A_eps / eps` on the
rescaled domain, and the chain `Phi^1 o Theta-hat o Psi_2 o A_eps` read through the secular chart.
The frequency data `checkW` is a free parameter `W` (supplied by P8b/P8c/P8e).

Exported helper lemmas, one per clause of `P11PreparedSpec` that concerns only `N`, `P`, `chain`:
domain chain (`p11Rescale_*`, `p11PreparedCore_chain_mem`), holomorphy, periodicity, reality,
the sup bound of `P_eps` (`pr-a`) and the fixed Hamiltonian identity (`H_2 o A_eps = eps H-hat`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Core

variable {n : ℕ}

/-- The prepared data of `stepP:p11:pr-basic`, parametrised by the frequency datum `W`. -/
def p11PreparedCoreOf (C : P11SecularData n) (Fast : P11FastData n) (A : P11SlowData n)
    (eps : ℝ) (W : P11Vec (n+n) → P11Vec (n+n)) : P11PreparedData n where
  N := fun I => (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2)/eps
  P := fun z => A.f3 (p11Rescale C.J0 eps z)/eps
  chain := fun z =>
    let w := Fast.map
      (p11PolarC (A.Psi (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))
    C.chart ((fun i => (w.1 i).re), fun i => (w.2 i).re)
  checkW := W

/-- The prepared data of `stepP:p11:pr-basic` for the signed data of a physical datum. -/
def p11PreparedCore (D : P11Physical n) (nu eps : ℝ) (W : P11Vec (n+n) → P11Vec (n+n)) :
    P11PreparedData n :=
  p11PreparedCoreOf (p11SecularData D) (p11FastData D eps) (p11SlowData D nu eps) eps W

/-- Real rescaling of a real phase point (`A_eps` on real points). -/
def p11RescaleReal (J0 : P11Vec n) (eps : ℝ) (x : Phase (n+n)) : Phase (n+n) :=
  (x.1, Fin.append (fun i : Fin n => J0 i+eps*x.2 (Fin.castAdd n i))
    (fun i : Fin n => eps*(2*Real.pi+x.2 (Fin.natAdd n i))))

theorem p11Rescale_real (J0 : P11Vec n) (eps : ℝ) (x : Phase (n+n)) :
    p11Rescale J0 eps (KAM.realInclusion₂ (n+n) x) =
      KAM.realInclusion₂ (n+n) (p11RescaleReal J0 eps x) := by
  refine Prod.ext rfl (funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [p11Rescale, p11RescaleReal, Fin.append_left]
  · simp [p11Rescale, p11RescaleReal, Fin.append_right]

end Core

end KAM.Planetary

end
