/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.PGAssembly.Main

/-!
# Provider for the frozen theorem `KAM.Planetary.properlyDegenerateKAM`

The proof of `KAM.Planetary.properlyDegenerateKAM` is assembled here as
`KAM.Provider.Planetary.properlyDegenerateKAM`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Provider; exact frozen telescope. -/
theorem properlyDegenerateKAM {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (V : Set (Fin a → ℝ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V)
    (W : Set (Fin a → ℝ)) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hboundary : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ t : ℝ, 0 < t → t < d →
        volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t))
    (r0 mu0 B : ℝ)
    (hr0 : 0 < r0) (hmu0 : 0 < mu0) (hB : 0 < B)
    (H0 : (Fin a → ℝ) → ℝ) (P : ℝ → Phase (a + b) → ℝ)
    (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → (Fin b → ℝ))
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (hP : AnalyticOnNhd ℝ (fun z : ℝ × Phase (a + b) => P z.1 z.2)
      (Set.Icc 0 mu0 ×ˢ closure (cylinder V r0)))
    (hperiod : ∀ mu ∈ Set.Icc 0 mu0, ∀ z ∈ cylinder V r0,
      ∀ k : Fin a → ℤ, P mu (z + fastShift k) = P mu z)
    (hfreq : HasFastDiffeomorphism H0 W)
    (hBNF : HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta)
    (htorsion : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, B ≤ |(beta mu I).det|)
    (hsymm : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, (beta mu I).IsSymm) :
    ∃ rStar C c : ℝ, 0 < rStar ∧ rStar < r0 ∧ rStar < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ r mu : ℝ, 0 < r → r < rStar → 0 < mu → mu < mu0 →
        mu < r ^ 6 / (Real.log (1 / r)) ^ c →
        ∃ S : Set (Phase (a + b)),
          IsCylinderKolmogorovSet (degenerateHamiltonian H0 P mu) V r mu C S ∧
          0 < volume (S ∩ cylinderCell V r) ∧
          ENNReal.ofReal (1 - C * Real.sqrt r) * volume (cylinderCell (b := b) V r) <
            volume (S ∩ cylinderCell V r) ∧
          volume (S ∩ cylinderCell V r) < volume (cylinderCell (b := b) V r) :=
  by exact KAM.Planetary.main ha hb V hV hVc hVb W hW hVW hboundary r0 mu0 B hr0 hmu0 hB H0 P P0
      Omega beta hP hperiod hfreq hBNF htorsion hsymm

end KAM.Provider.Planetary

end
