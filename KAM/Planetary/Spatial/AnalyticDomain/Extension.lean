/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Safety
public import KAM.Planetary.Spatial.ComplexTube

/-!
# The uniform complex extension of the spatial chart perturbation over the core

Source: `LP:MAIN L18 (595)` with `LP:MAIN L8 (259–271)` and amendment N12, track LP,
non-frozen.

* `spatialChartSafe_shift_iff`: the collision-free chart domain is invariant under the fast lattice.
* D4 `exists_spatialStrongTube`: `tubeNM` (never track P's `n + n` tube) applied to the compact
  spatial core inside `spatialChartSafe ν`: a shift-periodic holomorphic `fc` on
  `complexTubeNM core R`, real trace `fSpatial ν ∘ spatialPoincareProd ν` with real point in
  `spatialChartSafe ν`, and a sup bound `M` on `complexTubeNM core (R/2)`. The constants
  `R, M, fc` are chosen before `I⁰` and `μ`.
* D6 `spatialHamiltonian_split_chartSafe`: the exact split `h + μ f` on `spatialChartSafe ν`
  (SP-PROD `spatialHamiltonian_spatialPoincareProd`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

theorem fastShift_zero_phase {a b : ℕ} : (fastShift (0 : Fin a → ℤ) : Phase (a + b)) = 0 := by
  refine Prod.ext ?_ rfl
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift]

/-- The collision-free chart domain is invariant under the fast lattice. -/
theorem spatialChartSafe_shift_iff (hν : ∀ i, 0 < ν i) (k : Fin n → ℤ)
    (w : Phase (n + (n + n))) :
    w ∈ spatialChartSafe ν ↔ w + fastShift (a := n) (b := n + n) k ∈ spatialChartSafe ν := by
  have fwd : ∀ (k : Fin n → ℤ) (w : Phase (n + (n + n))), w ∈ spatialChartSafe ν →
      w + fastShift (a := n) (b := n + n) k ∈ spatialChartSafe ν := by
    intro k w hw
    obtain ⟨hd, hc⟩ := spatialPoincareProd_lattice hν hw.1 k
    refine ⟨hd, ?_⟩
    show spatialPoincareProd ν (spatialProdShift k w) ∈ spatialCollisionFreeDomain n
    rw [hc]
    exact hw.2
  refine ⟨fwd k w, fun h => ?_⟩
  have := fwd (-k) _ h
  rwa [add_assoc, ← fastShift_add, add_neg_cancel, fastShift_zero_phase, add_zero] at this

theorem fSpatial_spatialPoincareProd_shift (hν : ∀ i, 0 < ν i) (k : Fin n → ℤ)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialChartSafe ν) :
    fSpatial ν (spatialPoincareProd ν (w + fastShift (a := n) (b := n + n) k)) =
      fSpatial ν (spatialPoincareProd ν w) := by
  rw [show w + fastShift (a := n) (b := n + n) k = spatialProdShift k w from rfl,
    (spatialPoincareProd_lattice hν hw.1 k).2]

/-- D4 (`LP:MAIN L18 (595)`, `LP:MAIN L8 (259–271)`, N12): `R, M, fc` depend only on
`(ν, L, δ, r_g)`. -/
theorem exists_spatialStrongTube (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ,
      ∃ fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ,
      DifferentiableOn ℂ fc (complexTubeNM (spatialStrongCore ν L δ r) R) ∧
      (∀ w : Phase (n + (n + n)), KAM.Nekhoroshev.complexifyPhase w ∈
          complexTubeNM (spatialStrongCore ν L δ r) R →
        w ∈ spatialChartSafe ν ∧
          fc (KAM.Nekhoroshev.complexifyPhase w) =
            (fSpatial ν (spatialPoincareProd ν w) : ℂ)) ∧
      (∀ k : Fin n → ℤ, ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) R,
        z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈
            complexTubeNM (spatialStrongCore ν L δ r) R ∧
          fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z) ∧
      ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 2), ‖fc z‖ ≤ M := by
  classical
  have hW : IsOpen (spatialChartSafe ν) := isOpen_spatialPoincareProd_preimage hν
  have hKc := isCompact_spatialStrongCore hν hn hL hLch (r := r) hδ
  have hKW : spatialStrongCore ν L δ r ⊆ spatialChartSafe ν :=
    spatialStrongCore_subset_chartSafe hν hn hg hδ
  obtain ⟨R, hR, fc, hfc, hreal, hper⟩ := tubeNM hW hKc hKW
    (spatialChartSafe_shift_iff hν) (analyticOnNhd_fSpatial_spatialPoincareProd hν)
    (fun k w hw => fSpatial_spatialPoincareProd_shift hν k hw)
  set T := complexTubeNM (spatialStrongCore ν L δ r) R with hT
  set C : Set ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) :=
    (fun p : Phase (n + (n + n)) × ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) =>
      KAM.Nekhoroshev.complexifyPhase p.1 + p.2) ''
      (spatialStrongCore ν L δ r ×ˢ closedBall 0 (R / 2)) with hC
  have hcx : Continuous (KAM.Nekhoroshev.complexifyPhase (n := n + (n + n))) := by
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
    refine ⟨x, ⟨0, x, hx, by rw [fastShift_zero_phase, add_zero]⟩, ?_⟩
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

/-- D6 (`LP:MAIN L18 (595)`, `LP:MAIN L8 (254)`): on the collision-free chart domain,
`H_μ ∘ Ψ = h + μ f` exactly (no truncation), with `h(I) = −Σ ν_i³/(2 I_i²)` and
`f = fSpatial ν ∘ Ψ`. This restates SP-PROD's `spatialHamiltonian_spatialPoincareProd`. -/
theorem spatialHamiltonian_split_chartSafe (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialChartSafe ν) :
    spatialHamiltonian ν μ (spatialPoincareProd ν w) =
      -∑ i, ν i ^ 3 / (2 * fast w.2 i ^ 2) + μ * fSpatial ν (spatialPoincareProd ν w) :=
  spatialHamiltonian_spatialPoincareProd hν μ hw.1

end KAM.Planetary.Spatial

end
