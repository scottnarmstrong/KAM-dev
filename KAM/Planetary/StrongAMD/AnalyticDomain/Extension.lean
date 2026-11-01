/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Safety
public import KAM.Planetary.Exponential.Perturbation

/-!
# The uniform complex extension of the chart perturbation over the sharp core

Package LP-DOM, `LP:MAIN L8 (259–271)`, track LP, non-frozen.

* D4 `exists_strongTube`: track P's `tube` applied to the compact sharp core inside `chartSafe ν`:
  a shift-periodic holomorphic `fc` on `complexTube core R`, real trace
  `fMov 1 1 ν ∘ poincareProd ν 1` with real point in `chartSafe ν`, and a sup bound `M` on
  `complexTube core (R/2)` (compactness of a thickening of the core, as in
  `KAM.Planetary.perturbation`).
* D6 `movingHamiltonian_poincareProd_split`: the exact split `h + μ f` on `chartSafe ν`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- D4 (`LP:MAIN L8 (259–271)`): `R, M, fc` depend only on `(ν, L, δ, r_g)`. -/
theorem exists_strongTube (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∃ fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ,
      DifferentiableOn ℂ fc (complexTube (strongCore ν L δ r) R) ∧
      (∀ w : Phase (n + n), KAM.Nekhoroshev.complexifyPhase w ∈
          complexTube (strongCore ν L δ r) R →
        w ∈ chartSafe ν ∧
          fc (KAM.Nekhoroshev.complexifyPhase w) = (fMov 1 1 ν (poincareProd ν 1 w) : ℂ)) ∧
      (∀ k : Fin n → ℤ, ∀ z ∈ complexTube (strongCore ν L δ r) R,
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTube (strongCore ν L δ r) R ∧
          fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z) ∧
      ∀ z ∈ complexTube (strongCore ν L δ r) (R / 2), ‖fc z‖ ≤ M := by
  classical
  have hW : IsOpen (chartSafe ν) := isOpen_poincareProd_preimage hν one_pos
  have hKc := isCompact_strongCore hν hn hL hLch (r := r) hδ
  have hKW : strongCore ν L δ r ⊆ chartSafe ν := strongCore_subset_chartSafe hν hn hg hδ
  obtain ⟨R, hR, fc, hfc, hreal, hper⟩ := tube hW hKc hKW
    (chartSafe_shift_iff hν) (chart_perturbation_analytic ν hν)
    (fun k w hw => fMov_poincareProd_shift hν k hw)
  set T := complexTube (strongCore ν L δ r) R with hT
  set C : Set ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) :=
    (fun p : Phase (n + n) × ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) =>
      KAM.Nekhoroshev.complexifyPhase p.1 + p.2) ''
      (strongCore ν L δ r ×ˢ closedBall 0 (R / 2)) with hC
  have hcx : Continuous (KAM.Nekhoroshev.complexifyPhase (n := n + n)) := by
    unfold KAM.Nekhoroshev.complexifyPhase
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_snd)
  have hCc : IsCompact C :=
    (hKc.prod (isCompact_closedBall _ _)).image ((hcx.comp continuous_fst).add continuous_snd)
  have hCT : C ⊆ T := by
    rintro _ ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
    refine ⟨x, mem_periodicOrbitSet_self hx, ?_⟩
    have : ‖v‖ ≤ R / 2 := by simpa using hv
    simp only [add_sub_cancel_left]
    exact this.trans_lt (half_lt_self hR)
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hfc.continuousOn.mono hCT)
  refine ⟨R, hR, M, fc, hfc, hreal, hper, fun z hz => ?_⟩
  obtain ⟨x, ⟨k, x0, hx0, rfl⟩, hn'⟩ := hz
  have hz' : z - KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ C := by
    refine ⟨(x0, z - KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k)), ⟨hx0, ?_⟩, ?_⟩
    · simpa using hn'.le
    · simp only [complexifyPhase_add]; abel
  have h1 := (hper k _ (hCT hz')).2
  rw [sub_add_cancel] at h1
  exact h1 ▸ hM _ hz'

/-- D6 (`LP:MAIN L8 (254)`): on the chart domain, `H_mov ∘ Ψ = h + μ f` exactly (no truncation),
with `h(Λ) = -∑ ν_i³/(2 Λ_i²)` and `f = fMov 1 1 ν ∘ Ψ`. -/
theorem movingHamiltonian_poincareProd_split (hν : ∀ i, 0 < ν i) (μ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ chartSafe ν) :
    movingHamiltonian 1 1 ν μ (poincareProd ν 1 w) =
      -∑ i, ν i ^ 3 / (2 * fast w.2 i ^ 2) + μ * fMov 1 1 ν (poincareProd ν 1 w) := by
  rw [lpChart_hamiltonian hν μ hw.1]
  simp [hProd]

end KAM.Planetary.StrongAMD

end
