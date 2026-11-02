/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Nek.Cover
public import KAM.Planetary.StrongAMD.AnalyticDomain.Extension
public import KAM.Planetary.Exponential.Hamiltonian
public import KAM.Planetary.Exponential.Lift

/-!
# The normalized perturbation on every cell

Source: `LP:MAIN L8 (259–271)` as planned in
`docs/tracks/LP/lp3/LP3-PLAN.md` §2.3, track LP, non-frozen.

* `nekNormalizedPerturbation`: the global `P = fc/B₀` on the tube `complexTube core R`, and `0`
  elsewhere (track P's pt-def); one `P` serves every cell.
* `IsStrongExtension`, `exists_isStrongExtension`: the four clauses of `exists_strongTube` as a
  package.
* `isPartialPerturbation_nekCell`, `isPartialPerturbation_neg_nekCell`: `IsPartialPerturbation
  G′_j D_j ρ (±P)` on every cell centred in `𝓛_δ`.
* `nekCellRegion`, `isOpen_nekCellRegion`: the open real region `V_j`.
* `nekCell_hamiltonian_eq`: on `V_j`, with `ε = B₀ μ`, the degenerate Hamiltonian
  `h(fast) + ε Re P` of the frozen theorem equals the chart Hamiltonian `liftChartHam ν μ` (no
  change of time or period).
* `nekCell_field_eq`: equal Hamiltonian fields on `V_j` and differentiability.
* `exists_nekPerturbation`: the bundled statement (one `P`, all cells).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ}

/-- The four clauses of `exists_strongTube` for `(R, M, fc)`. -/
structure IsStrongExtension (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R M : ℝ)
    (fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ fc (complexTube (strongCore ν L δ rg) R)
  real : ∀ w : Phase (n + n), KAM.Nekhoroshev.complexifyPhase w ∈
      complexTube (strongCore ν L δ rg) R →
    w ∈ chartSafe ν ∧
      fc (KAM.Nekhoroshev.complexifyPhase w) = (fMov 1 1 ν (poincareProd ν 1 w) : ℂ)
  periodic : ∀ k : Fin n → ℤ, ∀ z ∈ complexTube (strongCore ν L δ rg) R,
    z + KAM.Nekhoroshev.complexifyPhase (fastShift k) ∈ complexTube (strongCore ν L δ rg) R ∧
      fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k)) = fc z
  bound : ∀ z ∈ complexTube (strongCore ν L δ rg) (R / 2), ‖fc z‖ ≤ M

/-- `exists_strongTube` as an `IsStrongExtension`. -/
theorem exists_isStrongExtension {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L) (hLch : L ⊆ chamber ν)
    (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, ∃ fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ,
      IsStrongExtension ν L δ rg R M fc := by
  obtain ⟨R, hR, M, fc, h1, h2, h3, h4⟩ := exists_strongTube hν hn hL hLch hg hδ
  exact ⟨R, hR, M, fc, ⟨h1, h2, h3, h4⟩⟩

open scoped Classical in
/-- The global normalized perturbation `P = fc/B₀` on `complexTube core R`, `0` elsewhere. -/
def nekNormalizedPerturbation (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R : ℝ)
    (fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ) (B0 : ℝ) :
    ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ :=
  fun z => if z ∈ complexTube (strongCore ν L δ rg) R then fc z / (B0 : ℂ) else 0

section Cell

variable {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R M B0 : ℝ}
  {fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ}

theorem nekNormalizedPerturbation_of_mem {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : z ∈ complexTube (strongCore ν L δ rg) R) :
    nekNormalizedPerturbation ν L δ rg R fc B0 z = fc z / (B0 : ℂ) := by
  simp [nekNormalizedPerturbation, hz]

theorem complexTube_half_subset {K : Set (Phase (n + n))} {R : ℝ} (hR : 0 < R) :
    complexTube K (R / 2) ⊆ complexTube K R := by
  rintro z ⟨x, hx, hn⟩
  exact ⟨x, hx, hn.trans (half_lt_self hR)⟩

/-- On the cell's complex domain: inside the tube, with `‖fc‖ ≤ B₀`. -/
theorem nekCell_mem_tube (hext : IsStrongExtension ν L δ rg R M fc) (hrg : 0 < rg) (hR : 0 < R)
    (hδ : 0 < δ) (hMB : M ≤ B0) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ)
    {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : z ∈ KAM.Nekhoroshev.partialComplexDomain (nekCellOuter rg R c) (nekCellSlow ν δ c)
      (nekRho rg R)) :
    z ∈ complexTube (strongCore ν L δ rg) R ∧ ‖fc z‖ ≤ B0 := by
  have h := nekCell_containment hrg hR hδ hc hz
  exact ⟨complexTube_half_subset hR h, (hext.bound z h).trans hMB⟩

/-- `IsPartialPerturbation G′_j D_j ρ P` for the global `P = fc/B₀` (`LP3-PLAN` §2.3). -/
theorem isPartialPerturbation_nekCell (hext : IsStrongExtension ν L δ rg R M fc) (hrg : 0 < rg)
    (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0) {c : Fin n → ℝ}
    (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (nekCellSlow ν δ c)
      (nekRho rg R) (nekNormalizedPerturbation ν L δ rg R fc B0) := by
  have hFT := fun z hz => nekCell_mem_tube hext hrg hR hδ hMB hc (z := z) hz
  have hdiv : DifferentiableOn ℂ (fun z => fc z / (B0 : ℂ))
      (complexTube (strongCore ν L δ rg) R) :=
    (hext.differentiableOn.mul_const ((B0 : ℂ)⁻¹)).congr fun z _ => by
      simp [div_eq_mul_inv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hdiv.mono fun z hz => (hFT z hz).1).congr
      fun z hz => nekNormalizedPerturbation_of_mem (hFT z hz).1
  · intro z hz
    rw [nekNormalizedPerturbation_of_mem (hFT z hz).1, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hB0.le]
    exact (div_le_one hB0).2 (hFT z hz).2
  · intro w hw
    obtain ⟨-, hwf⟩ := hext.real w (hFT _ hw).1
    rw [nekNormalizedPerturbation_of_mem (hFT _ hw).1, hwf, ← Complex.ofReal_div]
    exact Complex.ofReal_im _
  · intro z hz l
    obtain ⟨h1, h2⟩ := hext.periodic l z (hFT z hz).1
    rw [nekNormalizedPerturbation_of_mem h1, nekNormalizedPerturbation_of_mem (hFT z hz).1, h2]

/-- The same for `-P` (`isPartialPerturbation_neg_of`). -/
theorem isPartialPerturbation_neg_nekCell (hext : IsStrongExtension ν L δ rg R M fc)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0) {c : Fin n → ℝ}
    (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (nekCellSlow ν δ c)
      (nekRho rg R) (-nekNormalizedPerturbation ν L δ rg R fc B0) :=
  isPartialPerturbation_neg_of (isPartialPerturbation_nekCell hext hrg hR hδ hB0 hMB hc)

/-! ### The open real region `V_j` and the Hamiltonian identity -/

/-- `V_j = {w : fast w.2 ∈ G′_j ∧ (slow w.1, slow w.2) ∈ D_j}`. -/
def nekCellRegion (rg R : ℝ) (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) : Set (Phase (n + n)) :=
  {w | fast w.2 ∈ nekCellOuter rg R c ∧ (slow w.1, slow w.2) ∈ nekCellSlow ν δ c}

theorem isOpen_nekCellRegion (rg R : ℝ) (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) :
    IsOpen (nekCellRegion rg R ν δ c) := by
  have hf : Continuous fun w : Phase (n + n) => fast w.2 :=
    continuous_pi fun i => (continuous_apply (Fin.castAdd n i)).comp continuous_snd
  have hs : Continuous fun w : Phase (n + n) => (slow w.1, slow w.2) :=
    (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_fst).prodMk
      (continuous_pi fun i => (continuous_apply (Fin.natAdd n i)).comp continuous_snd)
  exact ((isOpen_nekCellOuter rg R c).preimage hf).inter
    ((isOpen_nekCellSlow ν δ c).preimage hs)

/-- Real points of `V_j` complexify into the cell's complex domain. -/
theorem complexifyPhase_mem_nekCell {hrg : 0 < rg} {hR : 0 < R} {c : Fin n → ℝ}
    {w : Phase (n + n)} (hw : w ∈ nekCellRegion rg R ν δ c) :
    KAM.Nekhoroshev.complexifyPhase w ∈ KAM.Nekhoroshev.partialComplexDomain
      (nekCellOuter rg R c) (nekCellSlow ν δ c) (nekRho rg R) := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [KAM.Nekhoroshev.complexifyPhase, fast] using h1
  · simpa [KAM.Nekhoroshev.complexifyPhase, slow] using h2
  · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using nekRho_pos hrg hR
  · intro i; simpa [KAM.Nekhoroshev.complexifyPhase] using nekRho_pos hrg hR

/-- On `V_j`: the chart domain and the real trace `P(cx w) = fMov(Ψ w)/B₀`. -/
theorem nekCell_region_trace (hext : IsStrongExtension ν L δ rg R M fc) (hrg : 0 < rg)
    (hR : 0 < R) (hδ : 0 < δ) (hMB : M ≤ B0) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ)
    {w : Phase (n + n)} (hw : w ∈ nekCellRegion rg R ν δ c) :
    w ∈ chartSafe ν ∧ nekNormalizedPerturbation ν L δ rg R fc B0
        (KAM.Nekhoroshev.complexifyPhase w) =
      ((fMov 1 1 ν (poincareProd ν 1 w) / B0 : ℝ) : ℂ) := by
  have hT := (nekCell_mem_tube hext hrg hR hδ hMB hc
    (complexifyPhase_mem_nekCell (hrg := hrg) (hR := hR) hw)).1
  obtain ⟨hws, hwf⟩ := hext.real w hT
  refine ⟨hws, ?_⟩
  rw [nekNormalizedPerturbation_of_mem hT, hwf, ← Complex.ofReal_div]

/-- The Hamiltonian identity on `V_j` (`LP3-PLAN` §2.3): with `ε = B₀ μ`,
`h(fast) + ε Re P = liftChartHam ν μ`. -/
theorem nekCell_hamiltonian_eq (hext : IsStrongExtension ν L δ rg R M fc) (hν : ∀ i, 0 < ν i)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0) (μ : ℝ)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) {w : Phase (n + n)}
    (hw : w ∈ nekCellRegion rg R ν δ c) :
    degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ x => (nekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ) w =
      liftChartHam ν μ w := by
  obtain ⟨hws, hP⟩ := nekCell_region_trace hext hrg hR hδ hMB hc hw
  have hmov := movingHamiltonian_poincareProd (μ := μ) (G := 1) (m0 := 1) hν (by norm_num) hws.1
  simp only [mul_one] at hmov
  have hk : hProd 1 ν w = KAM.Nekhoroshev.realPart (planetaryKeplerC ν) (fast w.2) := by
    rw [realPart_planetaryKeplerC]
    simp [hProd, keplerSumGen]
  unfold degenerateHamiltonian liftChartHam
  beta_reduce
  rw [hmov, hP, Complex.ofReal_re, ← hk]
  field_simp

/-- Differentiability and equal Hamiltonian fields on `V_j` (`V_j`-version of track P's
`differentiableAt_hnu_field`). -/
theorem nekCell_field_eq (hext : IsStrongExtension ν L δ rg R M fc) (hν : ∀ i, 0 < ν i)
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) (hB0 : 0 < B0) (hMB : M ≤ B0) (μ : ℝ)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) {w : Phase (n + n)}
    (hw : w ∈ nekCellRegion rg R ν δ c) :
    DifferentiableAt ℝ (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ x => (nekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w ∧
      KAM.hamiltonianVectorField
        (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
          (fun _ x => (nekNormalizedPerturbation ν L δ rg R fc B0
            (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w =
      KAM.hamiltonianVectorField (liftChartHam ν μ) w := by
  have hEq : ∀ x ∈ nekCellRegion rg R ν δ c,
      degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ y => (nekNormalizedPerturbation ν L δ rg R fc B0
          (KAM.Nekhoroshev.complexifyPhase y)).re) (B0 * μ) x = liftChartHam ν μ x :=
    fun x hx => nekCell_hamiltonian_eq hext hν hrg hR hδ hB0 hMB μ hc hx
  have hws := (nekCell_region_trace hext hrg hR hδ hMB hc hw).1
  have hU := isOpen_nekCellRegion rg R ν δ c
  refine ⟨?_, hamiltonianVectorField_eq_of_eqOn_open hU hEq hw⟩
  exact (Filter.EventuallyEq.differentiableAt_iff
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) hEq)).2
    ((analyticOnNhd_liftChartHam hν μ w hws).differentiableAt)

end Cell

/-! ### The bundled statement -/

/-- The normalized perturbation, bundled: after the shared tube, one width `R` and one normalization `B₀ ≥ 1` give a
single global `P` such that, for every cell centred in `𝓛_δ`, `±P` are partial perturbations on
`(G′_j, D_j, ρ)`, and on the open real region `V_j` the degenerate Hamiltonian `h + (B₀μ) Re P`
equals the chart Hamiltonian and has the same field. -/
theorem exists_nekPerturbation {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L) (hLch : L ⊆ chamber ν)
    (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∃ B0 : ℝ, 1 ≤ B0 ∧
      ∃ P : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ,
        (∀ c ∈ strongLevelSet ν L δ,
          KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (nekCellSlow ν δ c)
            (nekRho rg R) P ∧
          KAM.Nekhoroshev.IsPartialPerturbation (nekCellOuter rg R c) (nekCellSlow ν δ c)
            (nekRho rg R) (-P)) ∧
        ∀ c ∈ strongLevelSet ν L δ, ∀ μ : ℝ, ∀ w ∈ nekCellRegion rg R ν δ c,
          w ∈ chartSafe ν ∧
          degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
              (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ) w =
            liftChartHam ν μ w ∧
          DifferentiableAt ℝ (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
              (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w ∧
          KAM.hamiltonianVectorField
              (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
                (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w =
            KAM.hamiltonianVectorField (liftChartHam ν μ) w := by
  obtain ⟨R, hR, M, fc, hext⟩ := exists_isStrongExtension hν hn hL hLch hg hδ
  have hrg := hg.pos
  have hB0 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMB : M ≤ max M 1 := le_max_left _ _
  refine ⟨R, hR, max M 1, le_max_right _ _, nekNormalizedPerturbation ν L δ rg R fc (max M 1),
    fun c hc => ⟨isPartialPerturbation_nekCell hext hrg hR hδ hB0 hMB hc,
      isPartialPerturbation_neg_nekCell hext hrg hR hδ hB0 hMB hc⟩,
    fun c hc μ w hw => ⟨(nekCell_region_trace hext hrg hR hδ hMB hc hw).1,
      nekCell_hamiltonian_eq hext hν hrg hR hδ hB0 hMB μ hc hw,
      (nekCell_field_eq hext hν hrg hR hδ hB0 hMB μ hc hw)⟩⟩

end KAM.Planetary.StrongAMD

end
