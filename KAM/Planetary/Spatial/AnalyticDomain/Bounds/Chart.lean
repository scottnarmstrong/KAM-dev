/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Extension
public import KAM.Planetary.Spatial.AnalyticDomain.Bounds.Tube

/-!
# The holomorphic spatial chart extension `Ψc` and its sup bound

Package LP-SP-DOMX, `LP:MAIN L18 (595)` with `LP:MAIN L8 (253, 259–271)`, track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `IsSpatialChartExtension`: `Ψc` is a holomorphic shift-periodic extension of the product chart
  `spatialPoincareProd ν` (positions and momenta, `6n` real coordinates) to `complexTubeNM K R'`,
  with real trace on the real points of the tube.
* `exists_spatialChart`: item 1. Such a `Ψc` over `complexTubeNM (spatialStrongCore ν L δ r) R'`
  with a sup bound `M'` on the half tube, `R', Ψc, M'` independent of any `I⁰` or `μ`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- `Ψc` is a holomorphic shift-periodic extension of the spatial chart `spatialPoincareProd ν`
to `complexTubeNM K R'` (positions and momenta; real trace on the real points of the tube). -/
structure IsSpatialChartExtension (ν : Fin n → ℝ) (K : Set (Phase (n + (n + n)))) (R' : ℝ)
    (Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
      (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ)) : Prop where
  holo : DifferentiableOn ℂ Ψc (complexTubeNM K R')
  real : ∀ w : Phase (n + (n + n)),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTubeNM K R' →
      w ∈ spatialChartSafe ν ∧
        Ψc (KAM.Nekhoroshev.complexifyPhase w) =
          KAM.Nekhoroshev.complexifyPhase (spatialPoincareProd ν w)
  periodic : ∀ (k : Fin n → ℤ) (z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)),
    z ∈ complexTubeNM K R' →
      z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + (n + n))) ∈
          complexTubeNM K R' ∧
        Ψc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + (n + n)))) = Ψc z

/-- A spatial chart extension restricts to a smaller tube. -/
theorem IsSpatialChartExtension.toSmallerSpatialTube {K : Set (Phase (n + (n + n)))} {R' R'' : ℝ}
    {Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
      (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ)}
    (h : IsSpatialChartExtension ν K R' Ψc) (hle : R'' ≤ R') :
    IsSpatialChartExtension ν K R'' Ψc where
  holo := h.holo.mono (complexTubeNM_mono K hle)
  real w hw := h.real w (complexTubeNM_mono K hle hw)
  periodic k z hz :=
    ⟨(complexTubeNM_add_fastShift K R'' k z).2 hz,
      (h.periodic k z (complexTubeNM_mono K hle hz)).2⟩

/-- Item 1 (`LP:MAIN L18 (595)`, `LP:MAIN L8 (253, 259–271)`): a holomorphic periodic extension
`Ψc` of the whole spatial chart (positions and momenta, `6n` coordinates) to
`complexTubeNM (spatialStrongCore ν L δ r) R'`, with real trace `spatialPoincareProd ν` and a sup
bound `M'` on the half tube. `R', Ψc, M'` depend only on `(ν, L, δ, r)`, not on any `I⁰` or `μ`. -/
theorem exists_spatialChart (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R' : ℝ, 0 < R' ∧ ∃ Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
        (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ),
      IsSpatialChartExtension ν (spatialStrongCore ν L δ r) R' Ψc ∧
      ∃ M' : ℝ, ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R' / 2), ‖Ψc z‖ ≤ M' := by
  classical
  have hW : IsOpen (spatialChartSafe ν) := isOpen_spatialPoincareProd_preimage hν
  have hKc := isCompact_spatialStrongCore hν hn hL hLch (r := r) hδ
  have hKW : spatialStrongCore ν L δ r ⊆ spatialChartSafe ν :=
    spatialStrongCore_subset_chartSafe hν hn hg hδ
  have hana : AnalyticOnNhd ℝ (spatialPoincareProd ν) (spatialChartSafe ν) :=
    (analyticOnNhd_spatialPoincareProd hν).mono inter_subset_left
  let coord : Fin (n * 3) ⊕ Fin (n * 3) → Phase (n + (n + n)) → ℝ := fun c w =>
    Sum.elim (fun k => (spatialPoincareProd ν w).1 k) (fun k => (spatialPoincareProd ν w).2 k) c
  have hcoord : ∀ c, AnalyticOnNhd ℝ (coord c) (spatialChartSafe ν) := by
    intro c
    rcases c with k | k
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 3) => ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (Fin (n * 3) → ℝ) (Fin (n * 3) → ℝ))).comp_analyticOnNhd hana
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 3) => ℝ) k).comp
        (ContinuousLinearMap.snd ℝ (Fin (n * 3) → ℝ) (Fin (n * 3) → ℝ))).comp_analyticOnNhd hana
  have hper : ∀ c, ∀ (k : Fin n → ℤ), ∀ w ∈ spatialChartSafe ν,
      coord c (w + fastShift k) = coord c w := by
    intro c k w hw
    have := (spatialPoincareProd_lattice hν hw.1 k).2
    rcases c with j | j <;>
      simp [coord, show w + fastShift (a := n) (b := n + n) k = spatialProdShift k w from rfl, this]
  have hloc := fun c => tubeNM hW hKc hKW (spatialChartSafe_shift_iff hν) (hcoord c) (hper c)
  choose rc hrc gc hgc hreal hgper using hloc
  obtain ⟨R', hR', hR'le⟩ := exists_pos_le_half rc hrc Finset.univ
  have hRle : ∀ c, R' ≤ rc c := fun c =>
    (hR'le c (Finset.mem_univ c)).trans (half_le_self (hrc c).le)
  set Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
      (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ) :=
    fun z => (fun k => gc (Sum.inl k) z, fun k => gc (Sum.inr k) z) with hΨ
  have hchart : IsSpatialChartExtension ν (spatialStrongCore ν L δ r) R' Ψc := by
    refine ⟨?_, ?_, ?_⟩
    · exact DifferentiableOn.prodMk
        (differentiableOn_pi.2 fun k =>
          (hgc (Sum.inl k)).mono (complexTubeNM_mono _ (hRle _)))
        (differentiableOn_pi.2 fun k =>
          (hgc (Sum.inr k)).mono (complexTubeNM_mono _ (hRle _)))
    · intro w hw
      have h0 := hreal (Sum.inl (⟨0, by omega⟩ : Fin (n * 3))) w
        (complexTubeNM_mono _ (hRle _) hw)
      refine ⟨h0.1, Prod.ext (funext fun k => ?_) (funext fun k => ?_)⟩
      · exact (hreal (Sum.inl k) w (complexTubeNM_mono _ (hRle _) hw)).2
      · exact (hreal (Sum.inr k) w (complexTubeNM_mono _ (hRle _) hw)).2
    · intro k z hz
      refine ⟨(complexTubeNM_add_fastShift _ R' k z).2 hz,
        Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩
      · exact (hgper (Sum.inl j) k z (complexTubeNM_mono _ (hRle _) hz)).2
      · exact (hgper (Sum.inr j) k z (complexTubeNM_mono _ (hRle _) hz)).2
  obtain ⟨M', hM'⟩ := exists_norm_le_halfTubeNM hKc hR' hchart.holo.continuousOn
    (fun k z hz => (hchart.periodic k z hz).2)
  exact ⟨R', hR', Ψc, hchart, M', hM'⟩

end KAM.Planetary.Spatial

end
