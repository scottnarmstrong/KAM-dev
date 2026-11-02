/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Nek.Cells
public import KAM.Planetary.StrongAMD.Nek.Kepler
public import KAM.Planetary.Spatial.Nek.Cover

/-!
# The Kepler margin on the spatial cells and the cell-family drift threshold

Source: `LP:MAIN L14 (468–500)` and `LP:MAIN L18 (595–597)`
as planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.3, §2.5 (`k = n + n` slow pairs), track LP,
non-frozen.

The fast Hamiltonian `h = planetaryKeplerC ν` involves only the `n` fast actions, so the planar
the Kepler cell data clauses (`keplerC_clauses`, `keplerCNeg_clauses`, `keplerC_definite`) are reused unchanged.
The planar `lp3_kepler_data` asks `G′ ⊆ cthickening ρ₀ U` with `ρ₀ = Imin/4`; the cell widths are
fixed by `(r_g, R)` and need not be below `Imin/4`, so the margin is instead taken from the plan's
own argument (§2.3, "Kepler data"): every real part of the complex collar of a cell lies in the
closed `rs`-ball about its centre, which lies in the shared tube `U`.

* `nekCell_nbhd_re_mem_ball`: real parts of `actionNbhd G′_j ρ` lie in `ball c_j rs`;
* `spatialNek_kepler_premises`: the fast-Hamiltonian premises of the frozen theorem for `h`, `-h`
  on every `(G′, ρ)` whose complex collar has real parts in a compact `U ⊆ chamber ν`;
* `exists_spatialNek_cell_threshold`: one threshold `ε₀` for a finite family of spatial cells, and
  the two-sided cell drift bound for `h = planetaryKeplerC ν` (`cell_drift_two_sided` at
  `k = n + n`), stated with the planetary exponents.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ}

/-! ### Real parts of the complex collar of a cell -/

/-- The real parts of a point of the complex collar `actionNbhd G′_j ρ` of a cell lie in
`ball c_j rs` (`‖Re z − c_j‖ < 2η + ρ < rs`). -/
theorem nekCell_nbhd_re_mem_ball {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) {c : Fin n → ℝ}
    {z : Fin n → ℂ} (hz : z ∈ KAM.actionNbhd (nekCellOuter rg R c) (nekRho rg R)) :
    (fun i => (z i).re) ∈ ball c (nekWidth rg R) := by
  obtain ⟨J, hJ, hlt⟩ := hz
  have hrs := nekWidth_pos hrg hR
  rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hrs]
  intro i
  have h1 : ‖J - c‖ < 2 * nekEta rg R := by
    have := hJ
    rwa [nekCellOuter, mem_ball, dist_eq_norm] at this
  have h2 : |J i - c i| < 2 * nekEta rg R := by
    have := norm_le_pi_norm (J - c) i
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    exact lt_of_le_of_lt this h1
  have h3 : |(z i).re - J i| < nekRho rg R := by
    have hdiff : ‖z i - (J i : ℂ)‖ ≤ ‖z - fun j => (J j : ℂ)‖ :=
      norm_le_pi_norm (z - fun j => (J j : ℂ)) i
    have hre : |(z i).re - J i| ≤ ‖z i - (J i : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z i - (J i : ℂ))
      simpa using this
    exact lt_of_le_of_lt (hre.trans hdiff) hlt
  have h4 : |(z i).re - c i| ≤ |(z i).re - J i| + |J i - c i| := by
    have := abs_add_le ((z i).re - J i) (J i - c i)
    simpa using this
  rw [Real.norm_eq_abs]
  simp only [Pi.sub_apply]
  unfold nekEta nekRho at *
  linarith

/-! ### The fast-Hamiltonian premises on a collar with real parts in `U` -/

/-- The premises of `partialConvex_nekhoroshev` concerning the fast Hamiltonian, for
`h = planetaryKeplerC ν` and `-h`, on every `(G′, ρ)` whose complex collar has all real parts in
the compact `U ⊆ chamber ν`. The constants depend on `(ν, U)` only. -/
theorem spatialNek_kepler_premises (hn : 1 ≤ n) {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) :
    ∃ g m M : ℝ, 0 < g ∧ 0 < m ∧ 0 < M ∧
      ∀ (G' : Set (Fin n → ℝ)) (ρ : ℝ),
        (∀ z ∈ KAM.actionNbhd G' ρ, (fun i => (z i).re) ∈ U) →
        (DifferentiableOn ℂ (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          ContDiffOn ℂ 2 (planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
            (planetaryKeplerC ν (fun i => (I i : ℂ))).im = 0) ∧
          (∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC ν)) z‖ ≤ M) ∧
          KAM.Nekhoroshev.HasDefiniteFastPart G' ρ g m (planetaryKeplerC ν)) ∧
        (DifferentiableOn ℂ (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          ContDiffOn ℂ 2 (-planetaryKeplerC ν) (KAM.actionNbhd G' ρ) ∧
          (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
            ((-planetaryKeplerC ν) (fun i => (I i : ℂ))).im = 0) ∧
          (∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ (-planetaryKeplerC ν)) z‖ ≤ M) ∧
          KAM.Nekhoroshev.HasDefiniteFastPart G' ρ g m (-planetaryKeplerC ν)) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨Imin, Imax, hmin, hmax, hb⟩ := exists_chamber_bounds hUc hUch
  obtain ⟨νmin, hνmin, hνle⟩ := exists_pos_le_forall_fin ν hν
  refine ⟨νmin ^ 3 / Imax ^ 3, 3 * νmin ^ 3 / Imax ^ 4, keplerHessConst ν Imin,
    by positivity, by positivity, keplerHessConst_pos hν hmin, fun G' ρ hU => ?_⟩
  have hmarg : ∀ z ∈ KAM.actionNbhd G' ρ, ∀ i, Imin ≤ (z i).re :=
    fun z hz i => (hb _ (hU z hz) i).1
  have hreal : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ →
      ∀ i, 0 < I i ∧ I i ≤ Imax := fun I hI i => by
    have := hb _ (hU _ hI) i
    simp only [Complex.ofReal_re] at this
    exact ⟨by linarith [this.1], this.2⟩
  have hdef := keplerC_definite hn hνmin hνle hmax hreal
  obtain ⟨a1, a2, a3, a4⟩ := keplerC_clauses hν hmin hmarg
  obtain ⟨b1, b2, b3, b4⟩ := keplerCNeg_clauses hν hmin hmarg
  exact ⟨⟨a1, a2, a3, a4, hdef⟩, ⟨b1, b2, b3, b4, hasDefiniteFastPart_neg hdef⟩⟩

/-! ### The cell-family drift threshold -/

/-- **One threshold for a finite family of spatial cells** (`k = n + n`). Let `U ⊆ chamber ν` be
compact, `rs = nekWidth rg R` and `s` a finite set of centres with `closedBall c rs ⊆ U`.
Then there is `ε₀ > 0` such that for `0 < ε < ε₀`, every centre `c ∈ s` and every partial
perturbation `P` on `(G′_c, D_c, ρ)`: a solution of the `(h, P)` field on `uIcc 0 t` with fast
actions in `G_c`, initial fast action and all slow pairs in the inner cores (radius `ε^{b_n}`),
and `|t| ≤ ε⁻¹ exp (ε^{-a_n})`, drifts by at most `ε^{b_n}/2` in the fast actions
(a conditional helper, not a source result; the frozen theorem applied cellwise, both signs). -/
theorem exists_spatialNek_cell_threshold (hn : 2 ≤ n) {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {δ rg R : ℝ}
    (hrg : 0 < rg) (hR : 0 < R) (s : Finset (Fin n → ℝ))
    (hs : ∀ c ∈ s, closedBall c (nekWidth rg R) ⊆ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ c ∈ s,
      ∀ P : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ) → ℂ,
        KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (spatialNekCellSlow ν δ c)
          (nekRho rg R) P →
        ∀ (w : ℝ → Phase (n + (n + n))) (t : ℝ),
          |t| ≤ ε⁻¹ * Real.exp (ε ^ (-planetaryTimeExponent n)) →
          KAM.Nekhoroshev.IsSolutionOn (degenerateHamiltonian
            (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
            (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) ε)
            {I | fast (b := n + n) I ∈ nekCellInner rg R c} (uIcc 0 t) w →
          fast (b := n + n) (w 0).2 ∈
            KAM.Nekhoroshev.innerCore (nekCellInner rg R c) (ε ^ planetaryDriftExponent n) →
          (∀ u ∈ uIcc 0 t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
            KAM.Nekhoroshev.innerCore (spatialNekCellSlow ν δ c)
              (ε ^ planetaryDriftExponent n)) →
          ‖fast (b := n + n) (w t).2 - fast (b := n + n) (w 0).2‖ ≤
            ε ^ planetaryDriftExponent n / 2 := by
  obtain ⟨g, m, M, hg, hm, hM, hdata⟩ := spatialNek_kepler_premises (by omega) hν hUc hUch
  have hd : ∀ j : s, _ := fun j => hdata (nekCellOuter rg R j.1) (nekRho rg R)
    (fun z hz => hs j.1 j.2 (ball_subset_closedBall (nekCell_nbhd_re_mem_ball hrg hR hz)))
  obtain ⟨ε₀, hε₀, H⟩ := cell_drift_two_sided (n := n) (k := n + n) hn (by omega)
    (fun j : s => nekCellInner rg R j.1) (fun j : s => nekCellOuter rg R j.1)
    (fun j : s => spatialNekCellSlow ν δ j.1)
    (fun j => isOpen_nekCellInner rg R j.1) (fun j => convex_nekCellInner rg R j.1)
    (fun j => isOpen_nekCellOuter rg R j.1) (fun j => convex_nekCellOuter rg R j.1)
    (fun j => isOpen_spatialNekCellSlow ν δ j.1) (fun _ => nekRho rg R)
    (fun _ => g) (fun _ => m) (fun _ => M) (fun _ => g) (fun _ => m) (fun _ => M)
    (fun _ => nekRho_pos hrg hR) (fun _ => hM) (fun _ => hM)
    (fun j I hI => nekCell_collar hrg hR hI)
    (planetaryKeplerC ν) (fun j => (hd j).1.1) (fun j => (hd j).1.2.1)
    (fun j => (hd j).1.2.2.1) (fun j => (hd j).1.2.2.2.1) (fun j => (hd j).1.2.2.2.2)
    (fun j => (hd j).2.1) (fun j => (hd j).2.2.1) (fun j => (hd j).2.2.2.1)
    (fun j => (hd j).2.2.2.2.1) (fun j => (hd j).2.2.2.2.2)
  refine ⟨ε₀, hε₀, fun ε hε hεlt c hc P hP w t ht hsol h0 hslow => ?_⟩
  rw [planetaryDriftExponent_eq_partial] at h0 hslow ⊢
  rw [planetaryTimeExponent_eq_partial] at ht
  exact H ε hε hεlt ⟨c, hc⟩ P hP w t ht hsol h0 hslow

end KAM.Planetary.Spatial

end
