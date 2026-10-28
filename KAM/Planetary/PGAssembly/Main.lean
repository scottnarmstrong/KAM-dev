/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.IsCylinderKolmogorovSet
public import KAM.Planetary.PGAssembly.Strictness
public import KAM.Planetary.PGAssembly.FamilyFreq
public import KAM.Planetary.PGAssembly.CellTransfer
public import KAM.Planetary.Hamiltonian.Diophantine

/-!
# P Part 5: the main theorem (`bpP:p5:main`)

`main` repeats the frozen telescope of `KAM.Planetary.properlyDegenerateKAM` literally, with only
the declaration name changed. The constants are chosen first (`stepP:p5:mn-const`):
`rStar = finalRadius d`, `C = max (pgLoss d + 1) Cw` and `c = 2 * pgTau a b + 2`; for given
`r, mu` the pair is `admissible` (`stepP:p5:mn-given`); the set is `kset` over the surviving
parameters of `strictness` (`stepP:p5:mn-set`), and the measure bounds follow from the strict
slack `ofReal_mul_lt_of_slack` (`stepP:p5:mn-meas`). Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-MAIN; `main` is copied verbatim from
`P45Signatures.lean`.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- The ENNReal strict lower slack of `stepP:p5:mn-meas`. -/
theorem ofReal_mul_lt_of_slack {x y : ℝ} {m v : ENNReal} (hxy : x < y) (hm0 : m ≠ 0)
    (hmt : m ≠ ⊤) (hv : 0 < v) (hle : ENNReal.ofReal y * m ≤ v) :
    ENNReal.ofReal x * m < v := by
  by_cases hx : x ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hx, zero_mul]; exact hv
  · have hx' : 0 < x := not_le.1 hx
    exact lt_of_lt_of_le ((ENNReal.mul_lt_mul_iff_left hm0 hmt).2
      ((ENNReal.ofReal_lt_ofReal_iff (hx'.trans hxy)).2 hxy)) hle

/-- The final constants and the set for the data `d` (`stepP:p5:mn-const`, `-given`, `-set`,
`-meas`), stated for the bundled source data. -/
theorem main_of_data (d : PGData a b) :
    ∃ rStar C c : ℝ, 0 < rStar ∧ rStar < d.r0 ∧ rStar < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ r mu : ℝ, 0 < r → r < rStar → 0 < mu → mu < d.mu0 →
        mu < r ^ 6 / (Real.log (1 / r)) ^ c →
        ∃ S : Set (Phase (a + b)),
          IsCylinderKolmogorovSet (degenerateHamiltonian d.H0 d.P mu) d.V r mu C S ∧
          0 < volume (S ∩ cylinderCell d.V r) ∧
          ENNReal.ofReal (1 - C * Real.sqrt r) * volume (cylinderCell (b := b) d.V r) <
            volume (S ∩ cylinderCell d.V r) ∧
          volume (S ∩ cylinderCell d.V r) < volume (cylinderCell (b := b) d.V r) := by
  obtain ⟨hLpos, -⟩ := lower d
  obtain ⟨Cw, hCw, hfreq⟩ := frequency_bounds d
  obtain ⟨hR0, hRr0, -, -, hR1, -⟩ := (rstar d).choose_spec
  have hfin : 0 < finalRadius d :=
    lt_min hR0 (by have : 0 < pgLoss d + 1 := by linarith
                   positivity)
  refine ⟨finalRadius d, max (pgLoss d + 1) Cw, 2 * pgTau a b + 2, hfin,
    (min_le_left _ _).trans_lt hRr0, (min_le_left _ _).trans_lt hR1,
    lt_of_lt_of_le (by linarith) (le_max_left _ _), by have := pgTau_pos a b; positivity, ?_⟩
  intro r mu hr hrf hmu hmu0 hmur
  have hadm : admissible d (pgRstar d) r mu :=
    ⟨hr, hrf.trans_le (min_le_left _ _), hmu, hmu0, hmur⟩
  obtain ⟨B, hBD, hBσ, hDBσ, hpos, hlow, hup⟩ := strictness d r mu hadm hrf
  have hsub : pgD0 d r mu \ B ⊆ pgD0 d r mu := diff_subset
  obtain ⟨-, hmeas, hcyl, -⟩ := cell_transfer d r mu hadm hDBσ hsub
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hspec := (torus_conv d r mu hadm).choose_spec
  refine ⟨kset d r mu hadm (pgD0 d r mu \ B), ⟨hmeas, hcyl, ?_⟩, hpos, ?_, hup⟩
  · intro z hz
    obtain ⟨J, hJ, θ, hθ⟩ := by simpa [kset] using hz
    have hJD := hsub hJ
    refine ⟨(2 * Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J,
      physicalTorus d r mu hadm (pgFamily d r mu hadm) J, θ, hθ, ?_,
      hspec.2.2.2.2.2.2.2 J hJD, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨θ', rfl⟩ := hy
      exact mem_iUnion₂.2 ⟨J, hJ, θ', rfl⟩
    · have hk0 := pgScales_k0_pos d
      have hrp : 0 < r ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
      have h1 : 0 < (params d r mu).gamma1 := by
        show 0 < (pgScales d).k0 * r ^ (5 / 2 : ℝ); positivity
      have h2 : 0 < (params d r mu).gamma2 := by
        show 0 < mu * (pgScales d).k0 * r ^ (5 / 2 : ℝ); positivity
      have htau : ((a + b : ℕ) : ℝ) < pgTau a b := by unfold pgTau; linarith
      exact (cp10_isDiophantine h1 h2 htau hJD.2).2
    · exact (hfreq r mu hadm J hJD).1.trans ((le_max_right _ _))
    · exact (hfreq r mu hadm J hJD).2.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hmu.le)
  · refine ofReal_mul_lt_of_slack ?_ ?_ ?_ hpos hlow
    · have : pgLoss d + 1 / 2 < max (pgLoss d + 1) Cw :=
        lt_of_lt_of_le (by linarith) (le_max_left _ _)
      nlinarith
    · exact (ENNReal.mul_pos_iff.1
        (by rw [(disc_measure (b := b) d.hV.measurableSet hr).1]
            exact ENNReal.mul_pos (by simp; positivity)
              (ne_of_gt (by have := volume_V_pos d
                            exact (ENNReal.toReal_pos_iff.1 this).1)))).2 |>.ne'
    · exact stCell_ne_top d hr

/-- Exact frozen telescope and conclusion, with only the declaration name changed. -/
theorem main {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
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
  main_of_data ⟨ha, hb, V, hV, hVc, hVb, W, hW, hVW, hboundary, r0, mu0, B, hr0, hmu0, hB, H0, P,
    P0, Omega, beta, hP, hperiod, hfreq, hBNF, htorsion, hsymm⟩

end KAM.Planetary

end
