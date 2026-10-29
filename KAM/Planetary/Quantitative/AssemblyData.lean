/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Interface
public import KAM.Planetary.Quantitative.BudgetAdmissible
public import KAM.Planetary.WeakKAM.PolynomialBudget

/-!
# Quantitative weak KAM assembly: data bridge (P11C-Q6)

The upstream `SelectionData` carrying the quantitative data `d` and the Hamiltonian `h`
(`p11c_selData_exists`), the identification of the norms (`euclid` with `selectionLength`), and the
admissibility of the data-only threshold `thresholds d` at that selection data.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

variable {N : ℕ}

theorem p11c_euclid_eq (x : Fin N → ℝ) : KAM.Nekhoroshev.euclid x = selectionLength x := by
  simp [KAM.Nekhoroshev.euclid, selectionLength, Real.norm_eq_abs, sq_abs]

theorem p11c_selectionReal_eq (y : Fin N → ℝ) : selectionReal y = realInclusion N y := rfl

theorem p11c_thick_eq (d : QuantitativeData N) :
    selectionThick d.K d.vartheta =
      {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta} := by
  ext y
  simp only [selectionThick, mem_ofPred_eq, p11c_euclid_eq]

theorem p11c_scalar_eq (rho : ℕ) (w : (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) :
    selectionScalar rho w c = p11c_scalar rho w c := rfl


/-- Boundedness of the diagonal derivative values of the scalar under the top bounds. -/
theorem p11c_dg_bdd (d : QuantitativeData N) (h : (Fin N → ℂ) → ℂ) (c : Fin N → ℝ)
    (j : ℕ) (hj : j ≤ d.mu) {y : Fin N → ℝ}
    (hy : y ∈ {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta})
    (htop : ∀ j : ℕ, 1 ≤ j → j ≤ d.mu + 1 →
      ∀ y ∈ {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta},
      ∀ v : Fin j → (Fin N → ℝ), (∀ i, KAM.Nekhoroshev.euclid (v i) ≤ 1) →
        |iteratedFDeriv ℝ j (p11c_scalar d.rho (frequencyMap h) c) y v| ≤ d.M) :
    BddAbove {v | ∃ a : Fin N → ℝ, selectionLength a = 1 ∧
      v = |iteratedFDeriv ℝ j (selectionScalar d.rho (frequencyMap h) c) y (fun _ => a)|} := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · refine ⟨|selectionScalar d.rho (frequencyMap h) c y|, ?_⟩
    rintro v ⟨a, -, rfl⟩
    simp [iteratedFDeriv_zero_apply]
  · refine ⟨d.M, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    exact htop j hj0 (by omega) y hy (fun _ => a) (fun _ => by rw [p11c_euclid_eq, ha])


theorem p11c_mem_thick {d : QuantitativeData N} (hv : 0 ≤ d.vartheta) {y : Fin N → ℝ}
    (hy : y ∈ d.K) :
    y ∈ {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta} :=
  ⟨y, hy, by simpa [KAM.Nekhoroshev.euclid] using hv⟩

/-- The selection data of the quantitative data `d` and the Hamiltonian `h`, with the actual
derivative supremum bounded by `d.M0`. -/
theorem p11c_selData_exists (d : QuantitativeData N) (hd : d.NumericalValid)
    (h : (Fin N → ℂ) → ℂ) (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ) (hh : QuantitativeInput d h f) :
    ∃ ds : SelectionData N, ds.h = h ∧ qbcOfSelection ds d.M0 = d ∧
      selectionM₀ ds ≤ d.M0 := by
  obtain ⟨hN, hmu, hrho, hgap, htau, hv0, hv1, hs0, hs1, hC1, hM0, hb0, hbM, hKc, hl0, hlK⟩ := hd
  obtain ⟨hhol, -, -, hreal, -, hfin, htop, hhess, hM0b⟩ := hh
  have hvol : 0 < volume d.K := (ENNReal.ofReal_pos.2 hl0).trans hlK
  have hM0le : ∀ j ≤ d.mu, ∀ y ∈ selectionThick d.K d.vartheta,
      selectionDGVector j (frequencyMap h) y ≤ d.M0 := by
    intro j hj y hy
    rw [p11c_thick_eq] at hy
    refine Real.sSup_le ?_ hM0.le
    rintro v ⟨a, ha, rfl⟩
    have := hM0b j hj y hy a (by rw [p11c_euclid_eq, ha])
    rwa [p11c_euclid_eq] at this
  have hsup : ∀ j ≤ d.mu, ∀ y ∈ selectionThick d.K d.vartheta,
      selectionDGVector j (frequencyMap h) y ≤ d.M0 := hM0le
  refine ⟨SelectionData.mk d.mu d.rho d.tau d.vartheta d.s d.C1 d.beta d.M d.epsLoss d.K h
    hN hmu hrho htau hgap hKc hvol hv0 hv1 hs0 hs1 hC1 hb0 hbM hl0 hlK hhol
    (fun y hy => hreal y hy) hhess ?_ ?_, rfl, rfl, ?_⟩
  · intro c hc y hy
    obtain ⟨j, hj, v, hv, hge⟩ := hfin c (by rw [p11c_euclid_eq]; exact hc) y hy
    refine ⟨j, hj, hge.trans ?_⟩
    exact le_csSup (p11c_dg_bdd d h c j hj (p11c_mem_thick hv0.le hy)
      (htop c (by rw [p11c_euclid_eq]; exact hc)))
      ⟨v, by rw [← p11c_euclid_eq]; exact hv, rfl⟩
  · intro c hc j hj1 hj2 y hy a ha
    rw [p11c_thick_eq] at hy
    exact htop c (by rw [p11c_euclid_eq]; exact hc) j hj1 hj2 y hy a
      (fun i => by rw [p11c_euclid_eq]; exact ha i)
  · exact Real.sSup_le (by
      rintro v ⟨j, hj, y, hy, rfl⟩
      exact hsup j hj y hy) hM0.le

end KAM.Planetary

end
