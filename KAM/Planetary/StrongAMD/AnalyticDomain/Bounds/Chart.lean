/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Extension
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.TubeBound

/-!
# The holomorphic chart and momenta over the sharp core

Package LP-DOMX, `LP:MAIN L8 (253, 259–271)`, track LP, non-frozen.

Item 1 of the package brief: track P's `tube` applied to each of the `4n` coordinate functions of
`poincareProd ν 1` on `chartSafe ν` (real analytic, fast-shift periodic) gives one holomorphic,
shift-periodic extension `Ψc` of the whole chart (positions and momenta) to a thin complex tube
around the sharp core, with real trace `poincareProd ν 1` and a sup bound on the half tube.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- `Ψc` is a holomorphic shift-periodic extension of the chart `poincareProd ν 1` to
`complexTube K R'` (positions and momenta; real trace on the real points of the tube). -/
structure IsChartExtension (ν : Fin n → ℝ) (K : Set (Phase (n + n))) (R' : ℝ)
    (Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)) :
    Prop where
  holo : DifferentiableOn ℂ Ψc (complexTube K R')
  real : ∀ w : Phase (n + n), KAM.Nekhoroshev.complexifyPhase w ∈ complexTube K R' →
    w ∈ chartSafe ν ∧
      Ψc (KAM.Nekhoroshev.complexifyPhase w) =
        KAM.Nekhoroshev.complexifyPhase (poincareProd ν 1 w)
  periodic : ∀ (k : Fin n → ℤ) (z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)),
    z ∈ complexTube K R' →
      z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n)) ∈ complexTube K R' ∧
        Ψc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n))) = Ψc z

/-- A chart extension restricts to a smaller tube. -/
theorem IsChartExtension.toSmallerTube {K : Set (Phase (n + n))} {R' R'' : ℝ}
    {Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)}
    (h : IsChartExtension ν K R' Ψc) (hle : R'' ≤ R') : IsChartExtension ν K R'' Ψc where
  holo := h.holo.mono (complexTube_mono hle)
  real w hw := h.real w (complexTube_mono hle hw)
  periodic k z hz :=
    ⟨complexTube_add_shift k hz, (h.periodic k z (complexTube_mono hle hz)).2⟩

/-- Item 1 (`LP:MAIN L8 (253, 259–271)`): a holomorphic periodic extension `Ψc` of the whole chart
(positions and momenta) to `complexTube (strongCore ν L δ r) R'`, with real trace
`poincareProd ν 1` and a sup bound `M'` on the half tube.  `R', Ψc, M'` depend only on
`(ν, L, δ, r)`, not on any `I⁰` or `μ`. -/
theorem exists_strongChart (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R' : ℝ, 0 < R' ∧ ∃ Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) →
        (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ),
      IsChartExtension ν (strongCore ν L δ r) R' Ψc ∧
      ∃ M' : ℝ, ∀ z ∈ complexTube (strongCore ν L δ r) (R' / 2), ‖Ψc z‖ ≤ M' := by
  classical
  have hW : IsOpen (chartSafe ν) := isOpen_poincareProd_preimage hν one_pos
  have hKc := isCompact_strongCore hν hn hL hLch (r := r) hδ
  have hKW : strongCore ν L δ r ⊆ chartSafe ν := strongCore_subset_chartSafe hν hn hg hδ
  have hana : AnalyticOnNhd ℝ (poincareProd ν 1) (chartSafe ν) :=
    (analyticOnNhd_poincareProd hν one_pos).mono inter_subset_left
  let coord : Fin (n * 2) ⊕ Fin (n * 2) → Phase (n + n) → ℝ := fun c w =>
    Sum.elim (fun k => (poincareProd ν 1 w).1 k) (fun k => (poincareProd ν 1 w).2 k) c
  have hcoord : ∀ c, AnalyticOnNhd ℝ (coord c) (chartSafe ν) := by
    intro c
    rcases c with k | k
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))).comp_analyticOnNhd hana
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ) k).comp
        (ContinuousLinearMap.snd ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))).comp_analyticOnNhd hana
  have hper : ∀ c, ∀ (k : Fin n → ℤ), ∀ w ∈ chartSafe ν,
      coord c (w + fastShift k) = coord c w := by
    intro c k w hw
    have := (poincareProd_lattice hν one_pos hw.1 k).2
    rcases c with j | j <;> simp [coord, this]
  have hloc := fun c => tube hW hKc hKW (chartSafe_shift_iff hν) (hcoord c) (hper c)
  choose rc hrc gc hgc hreal hgper using hloc
  obtain ⟨R', hR', hR'le⟩ := exists_pos_le_half rc hrc Finset.univ
  have hRle : ∀ c, R' ≤ rc c := fun c =>
    (hR'le c (Finset.mem_univ c)).trans (half_le_self (hrc c).le)
  set Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ) :=
    fun z => (fun k => gc (Sum.inl k) z, fun k => gc (Sum.inr k) z) with hΨ
  have hchart : IsChartExtension ν (strongCore ν L δ r) R' Ψc := by
    refine ⟨?_, ?_, ?_⟩
    · exact DifferentiableOn.prodMk
        (differentiableOn_pi.2 fun k => (hgc (Sum.inl k)).mono (complexTube_mono (hRle _)))
        (differentiableOn_pi.2 fun k => (hgc (Sum.inr k)).mono (complexTube_mono (hRle _)))
    · intro w hw
      have h0 := hreal (Sum.inl (⟨0, by omega⟩ : Fin (n * 2))) w (complexTube_mono (hRle _) hw)
      refine ⟨h0.1, Prod.ext (funext fun k => ?_) (funext fun k => ?_)⟩
      · exact (hreal (Sum.inl k) w (complexTube_mono (hRle _) hw)).2
      · exact (hreal (Sum.inr k) w (complexTube_mono (hRle _) hw)).2
    · intro k z hz
      refine ⟨complexTube_add_shift k hz, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩
      · exact (hgper (Sum.inl j) k z (complexTube_mono (hRle _) hz)).2
      · exact (hgper (Sum.inr j) k z (complexTube_mono (hRle _) hz)).2
  obtain ⟨M', hM'⟩ := exists_norm_le_halfTube hKc hR' hchart.holo.continuousOn
    (fun k z hz => (hchart.periodic k z hz).2)
  exact ⟨R', hR', Ψc, hchart, M', hM'⟩

end KAM.Planetary.StrongAMD

end
