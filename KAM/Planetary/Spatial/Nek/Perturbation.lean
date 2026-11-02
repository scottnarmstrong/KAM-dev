/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.Cover
public import KAM.Planetary.Spatial.ChartLift.Setting
public import KAM.Planetary.Exponential.Hamiltonian
public import KAM.Planetary.Exponential.Lift

/-!
# The spatial normalized perturbation on every cell

Source: `LP:MAIN L8 (259–271)` and `LP:MAIN L18 (595)` as
planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.3, §2.5, track LP, non-frozen.

The spatial twin of `KAM.Planetary.StrongAMD.Nek.Perturbation`, on `Phase (n + (n + n))` with the
tube `complexTubeNM (spatialStrongCore ν L δ r_g) R` of `exists_spatialStrongTube`.

* `IsSpatialStrongExtension`, `exists_isSpatialStrongExtension`: the four clauses of
  `exists_spatialStrongTube` as a package.
* `spatialNekNormalizedPerturbation`: `P = fc/B₀` on the tube, `0` elsewhere.
* `isPartialPerturbation_spatialNekCell`, `isPartialPerturbation_neg_spatialNekCell`:
  `IsPartialPerturbation G′_j D_j ρ (±P)` on every cell centred in `𝓛_δ`.
* `spatialNekCellRegion`, `isOpen_spatialNekCellRegion`: the open real region `V_j`.
* `spatialNekCell_hamiltonian_eq`: on `V_j`, with `ε = B₀ μ`, the degenerate Hamiltonian
  `h(fast) + ε Re P` equals the spatial chart Hamiltonian `spLiftChartHam ν μ`
  (`spatialHProd ν + μ · fSpatial ν ∘ Ψ`, the Hamiltonian SP-LIFT's lift solves).
* `spatialNekCell_field_eq`: differentiability and equal Hamiltonian fields on `V_j`.
* `exists_spatialNekPerturbation`: the bundled statement, with the quantifier order of the planar
  `exists_nekPerturbation`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ}

/-- The four clauses of `exists_spatialStrongTube` for `(R, M, fc)`. -/
structure IsSpatialStrongExtension (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R M : ℝ)
    (fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ fc (complexTubeNM (spatialStrongCore ν L δ rg) R)
  real : ∀ w : Phase (n + (n + n)), KAM.Nekhoroshev.complexifyPhase w ∈
      complexTubeNM (spatialStrongCore ν L δ rg) R →
    w ∈ spatialChartSafe ν ∧
      fc (KAM.Nekhoroshev.complexifyPhase w) = (fSpatial ν (spatialPoincareProd ν w) : ℂ)
  periodic : ∀ k : Fin n → ℤ, ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R,
    z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈
        complexTubeNM (spatialStrongCore ν L δ rg) R ∧
      fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z
  bound : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2), ‖fc z‖ ≤ M

/-- `exists_spatialStrongTube` as an `IsSpatialStrongExtension`. -/
theorem exists_isSpatialStrongExtension {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L) (hLch : L ⊆ chamber ν)
    (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ,
      ∃ fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ,
      IsSpatialStrongExtension ν L δ rg R M fc := by
  obtain ⟨R, hR, M, fc, h1, h2, h3, h4⟩ := exists_spatialStrongTube hν hn hL hLch hg hδ
  exact ⟨R, hR, M, fc, ⟨h1, h2, h3, h4⟩⟩

open scoped Classical in
/-- The global normalized perturbation `P = fc/B₀` on `complexTubeNM core R`, `0` elsewhere. -/
def spatialNekNormalizedPerturbation (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R : ℝ)
    (fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ) (B0 : ℝ) :
    ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ :=
  fun z => if z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R then fc z / (B0 : ℂ) else 0

section Cell

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R M B0 : ℝ}
  {fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ}

theorem spatialNekNormalizedPerturbation_of_mem
    {z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)}
    (hz : z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R) :
    spatialNekNormalizedPerturbation ν L δ rg R fc B0 z = fc z / (B0 : ℂ) := by
  simp [spatialNekNormalizedPerturbation, hz]

theorem complexTubeNM_half_subset {m : ℕ} {K : Set (Phase (n + m))} {R : ℝ} (hR : 0 < R) :
    complexTubeNM K (R / 2) ⊆ complexTubeNM K R := by
  rintro z ⟨x, hx, hn⟩
  exact ⟨x, hx, hn.trans (half_lt_self hR)⟩

/-- On the cell's complex domain: inside the tube, with `‖fc‖ ≤ B₀`. -/
theorem spatialNekCell_mem_tube (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hMB : M ≤ B0) {c : Fin n → ℝ}
    (hc : c ∈ strongLevelSet ν L δ) {z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)}
    (hz : z ∈ KAM.Nekhoroshev.partialComplexDomain (nekCellOuter rg R c)
      (spatialNekCellSlow ν δ c) (nekRho rg R)) :
    z ∈ complexTubeNM (spatialStrongCore ν L δ rg) R ∧ ‖fc z‖ ≤ B0 := by
  have h := spatialNekCell_containment hrg hR hδ hc hz
  exact ⟨complexTubeNM_half_subset hR h, (hext.bound z h).trans hMB⟩

/-- `IsPartialPerturbation G′_j D_j ρ P` for the global `P = fc/B₀` (`LP3-PLAN` §2.3, §2.5). -/
theorem isPartialPerturbation_spatialNekCell (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (spatialNekCellSlow ν δ c)
      (nekRho rg R) (spatialNekNormalizedPerturbation ν L δ rg R fc B0) := by
  have hFT := fun z hz => spatialNekCell_mem_tube hext hrg hR hδ hMB hc (z := z) hz
  have hdiv : DifferentiableOn ℂ (fun z => fc z / (B0 : ℂ))
      (complexTubeNM (spatialStrongCore ν L δ rg) R) :=
    (hext.differentiableOn.mul_const ((B0 : ℂ)⁻¹)).congr fun z _ => by
      simp [div_eq_mul_inv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hdiv.mono fun z hz => (hFT z hz).1).congr
      fun z hz => spatialNekNormalizedPerturbation_of_mem (hFT z hz).1
  · intro z hz
    rw [spatialNekNormalizedPerturbation_of_mem (hFT z hz).1, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hB0.le]
    exact (div_le_one hB0).2 (hFT z hz).2
  · intro w hw
    obtain ⟨-, hwf⟩ := hext.real w (hFT _ hw).1
    rw [spatialNekNormalizedPerturbation_of_mem (hFT _ hw).1, hwf, ← Complex.ofReal_div]
    exact Complex.ofReal_im _
  · intro z hz l
    obtain ⟨h1, h2⟩ := hext.periodic l z (hFT z hz).1
    rw [spatialNekNormalizedPerturbation_of_mem h1,
      spatialNekNormalizedPerturbation_of_mem (hFT z hz).1, h2]

/-- The same for `-P` (`isPartialPerturbation_neg_of`). -/
theorem isPartialPerturbation_neg_spatialNekCell
    (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (spatialNekCellSlow ν δ c)
      (nekRho rg R) (-spatialNekNormalizedPerturbation ν L δ rg R fc B0) :=
  isPartialPerturbation_neg_of
    (isPartialPerturbation_spatialNekCell hext hrg hR hδ hB0 hMB hc)

/-! ### The open real region `V_j` and the Hamiltonian identity -/

/-- `V_j = {w : fast w.2 ∈ G′_j ∧ (slow w.1, slow w.2) ∈ D_j}` in `Phase (n + (n + n))`. -/
def spatialNekCellRegion (rg R : ℝ) (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) :
    Set (Phase (n + (n + n))) :=
  {w | fast w.2 ∈ nekCellOuter rg R c ∧ (slow w.1, slow w.2) ∈ spatialNekCellSlow ν δ c}

theorem isOpen_spatialNekCellRegion (rg R : ℝ) (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) :
    IsOpen (spatialNekCellRegion rg R ν δ c) := by
  have hf : Continuous fun w : Phase (n + (n + n)) => fast w.2 :=
    continuous_pi fun i => (continuous_apply (Fin.castAdd (n + n) i)).comp continuous_snd
  have hs : Continuous fun w : Phase (n + (n + n)) => (slow w.1, slow w.2) :=
    (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_fst).prodMk
      (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_snd)
  exact ((isOpen_nekCellOuter rg R c).preimage hf).inter
    ((isOpen_spatialNekCellSlow ν δ c).preimage hs)

/-- Real points of `V_j` complexify into the cell's complex domain. -/
theorem complexifyPhase_mem_spatialNekCell {hrg : 0 < rg} {hR : 0 < R} {c : Fin n → ℝ}
    {w : Phase (n + (n + n))} (hw : w ∈ spatialNekCellRegion rg R ν δ c) :
    KAM.Nekhoroshev.complexifyPhase w ∈ KAM.Nekhoroshev.partialComplexDomain
      (nekCellOuter rg R c) (spatialNekCellSlow ν δ c) (nekRho rg R) := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [KAM.Nekhoroshev.complexifyPhase, fast] using h1
  · simpa [KAM.Nekhoroshev.complexifyPhase, slow] using h2
  · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using nekRho_pos hrg hR
  · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using nekRho_pos hrg hR

/-- On `V_j`: the chart domain and the real trace `P(cx w) = fSpatial(Ψ w)/B₀`. -/
theorem spatialNekCell_region_trace (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hMB : M ≤ B0) {c : Fin n → ℝ}
    (hc : c ∈ strongLevelSet ν L δ) {w : Phase (n + (n + n))}
    (hw : w ∈ spatialNekCellRegion rg R ν δ c) :
    w ∈ spatialChartSafe ν ∧ spatialNekNormalizedPerturbation ν L δ rg R fc B0
        (KAM.Nekhoroshev.complexifyPhase w) =
      ((fSpatial ν (spatialPoincareProd ν w) / B0 : ℝ) : ℂ) := by
  have hT := (spatialNekCell_mem_tube hext hrg hR hδ hMB hc
    (complexifyPhase_mem_spatialNekCell (hrg := hrg) (hR := hR) hw)).1
  obtain ⟨hws, hwf⟩ := hext.real w hT
  refine ⟨hws, ?_⟩
  rw [spatialNekNormalizedPerturbation_of_mem hT, hwf, ← Complex.ofReal_div]

/-- The Hamiltonian identity on `V_j` (`LP3-PLAN` §2.3, §2.5): with `ε = B₀ μ`,
`h(fast) + ε Re P = spLiftChartHam ν μ` (`spatialHProd ν + μ · fSpatial ν ∘ Ψ`). -/
theorem spatialNekCell_hamiltonian_eq (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0) (μ : ℝ)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) {w : Phase (n + (n + n))}
    (hw : w ∈ spatialNekCellRegion rg R ν δ c) :
    degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ x => (spatialNekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ) w =
      spLiftChartHam ν μ w := by
  obtain ⟨-, hP⟩ := spatialNekCell_region_trace hext hrg hR hδ hMB hc hw
  have hk : spatialHProd ν w = KAM.Nekhoroshev.realPart (planetaryKeplerC ν) (fast w.2) := by
    rw [realPart_planetaryKeplerC]
    simp [spatialHProd, keplerSumGen, spatialActions]
  unfold degenerateHamiltonian spLiftChartHam
  beta_reduce
  rw [hP, Complex.ofReal_re, ← hk]
  field_simp

/-- Differentiability and equal Hamiltonian fields on `V_j`. -/
theorem spatialNekCell_field_eq (hext : IsSpatialStrongExtension ν L δ rg R M fc)
    (hν : ∀ i, 0 < ν i) (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0)
    (hMB : M ≤ B0) (μ : ℝ) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialNekCellRegion rg R ν δ c) :
    DifferentiableAt ℝ (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ x => (spatialNekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w ∧
      KAM.hamiltonianVectorField
        (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
          (fun _ x => (spatialNekNormalizedPerturbation ν L δ rg R fc B0
            (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w =
      KAM.hamiltonianVectorField (spLiftChartHam ν μ) w := by
  have hEq : ∀ x ∈ spatialNekCellRegion rg R ν δ c,
      degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ y => (spatialNekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase y)).re) (B0 * μ) x = spLiftChartHam ν μ x :=
    fun x hx => spatialNekCell_hamiltonian_eq hext hrg hR hδ hB0 hMB μ hc hx
  have hws : w ∈ spLiftChartSafe ν := (spatialNekCell_region_trace hext hrg hR hδ hMB hc hw).1
  have hU := isOpen_spatialNekCellRegion rg R ν δ c
  refine ⟨?_, hamiltonianVectorField_eq_of_eqOn_open hU hEq hw⟩
  exact (Filter.EventuallyEq.differentiableAt_iff
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) hEq)).2
    (differentiableAt_spatialChartHam hν μ hws)

end Cell

/-! ### The bundled statement -/

/-- The spatial sharp cover, bundled (`LP:MAIN L8 (259–271)`): after the shared tube, one width `R`
and one
normalization `B₀ ≥ 1` give a single global `P` such that, for every cell centred in `𝓛_δ`, `±P`
are partial perturbations on `(G′_j, D_j, ρ)` (with `D_j ⊆ Phase (n + n)`), and on the open real
region `V_j` the degenerate Hamiltonian `h + (B₀ μ) Re P` equals the spatial chart Hamiltonian
`spLiftChartHam ν μ` and has the same field. -/
theorem exists_spatialNekPerturbation {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L) (hLch : L ⊆ chamber ν)
    (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ B0 : ℝ, 1 ≤ B0 ∧
      ∃ P : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ,
        (∀ c ∈ strongLevelSet ν L δ,
          KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c)
            (spatialNekCellSlow ν δ c) (nekRho rg R) P ∧
          KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c)
            (spatialNekCellSlow ν δ c) (nekRho rg R) (-P)) ∧
        ∀ c ∈ strongLevelSet ν L δ, ∀ μ : ℝ, ∀ w ∈ spatialNekCellRegion rg R ν δ c,
          w ∈ spatialChartSafe ν ∧
          degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
              (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ) w =
            spLiftChartHam ν μ w ∧
          DifferentiableAt ℝ (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
              (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w ∧
          KAM.hamiltonianVectorField
              (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
                (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w =
            KAM.hamiltonianVectorField (spLiftChartHam ν μ) w := by
  obtain ⟨R, hR, M, fc, hext⟩ := exists_isSpatialStrongExtension hν hn hL hLch hg hδ
  have hrg := hg.pos
  have hB0 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMB : M ≤ max M 1 := le_max_left _ _
  refine ⟨R, hR, max M 1, le_max_right _ _,
    spatialNekNormalizedPerturbation ν L δ rg R fc (max M 1),
    fun c hc => ⟨isPartialPerturbation_spatialNekCell hext hrg hR hδ hB0 hMB hc,
      isPartialPerturbation_neg_spatialNekCell hext hrg hR hδ hB0 hMB hc⟩,
    fun c hc μ w hw => ⟨(spatialNekCell_region_trace hext hrg hR hδ hMB hc hw).1,
      spatialNekCell_hamiltonian_eq hext hrg hR hδ hB0 hMB μ hc hw,
      spatialNekCell_field_eq hext hν hrg hR hδ hB0 hMB μ hc hw⟩⟩

end KAM.Planetary.Spatial

end
