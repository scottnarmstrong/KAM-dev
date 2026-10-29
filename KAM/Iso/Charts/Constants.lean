/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Defs
public import KAM.Iso.Linear.FreqMap
public import KAM.Head.DerivativeBounds

/-!
# Part 3 (local charts): the compact action set and the constants are well defined

Blueprint node `bpI:p3:compact`. `n = 2`.

* `compact` (`bpI:p3:compact`): `d_B > 0`, `𝒮 = sSet B B'` is compact with
  `closure B' ⊆ 𝒮 ⊆ B`, and the extrema `m_h`, `M_g`, `S_h` of `bpI:p3:constants` (c) are
  attained on `𝒮`, with `0 < m_h ≤ M_g` and `0 < S_h`.
* Regularity of the frequency map and of the bordered Hessian on the real slice `realAct B r₀`
  (the blueprint's `U`): `contDiffOn_frequencyMap`, `continuousOn_fderiv_frequencyMap`,
  `continuousOn_borderedHessian`, `continuousOn_norm_inv`. They reuse
  `KAM.Iso.Linear.freq_map_contDiff` (the restated `bp:p4:freq-map` (iii)) and Cramer's rule.
* `frequencyMap_ne_zero_of_det_ne_zero`: `∇h(I) ≠ 0` if `det 𝖡_h(I) ≠ 0` (a zero gradient gives
  a zero row of `𝖡_h(I)`); this is `bpI:p3:det-identity` (a), needed here before the identity
  itself (`Charts/Coordinates`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-- The real slice `realAct B r₀` (the blueprint's `U`) is open. -/
theorem isOpen_realAct_charts (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) : IsOpen (realAct B r₀) :=
  (KAM.Head.isOpen_actionNbhd B r₀).preimage
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

/-- `B ⊆ U` for `r₀ > 0`. -/
theorem subset_realAct_charts (hr : 0 < r₀) : B ⊆ realAct B r₀ := fun I hI =>
  ⟨I, hI, by simpa using hr⟩

/-- `∇h` is `C¹` on `U` (`bp:p4:freq-map` (iii), restated as `freq_map_contDiff`). -/
theorem contDiffOn_frequencyMap (hd : HeadData B s₀ r₀ h B' η) :
    ContDiffOn ℝ 1 (frequencyMap h) (realAct B r₀) :=
  (KAM.Iso.Linear.freq_map_contDiff (KAM.Head.isOpen_actionNbhd B r₀) hd.holo hd.real).2.1

/-- The Hessian `D(∇h)` is continuous on `U`. -/
theorem continuousOn_fderiv_frequencyMap (hd : HeadData B s₀ r₀ h B' η) :
    ContinuousOn (fderiv ℝ (frequencyMap h)) (realAct B r₀) :=
  (contDiffOn_frequencyMap hd).continuousOn_fderiv_of_isOpen (isOpen_realAct_charts B r₀) le_rfl

/-- The entries of `𝖡_h(I)` are continuous on `U`. -/
theorem continuousOn_borderedHessian (hd : HeadData B s₀ r₀ h B' η) :
    ContinuousOn (KAM.Iso.borderedHessian h) (realAct B r₀) := by
  have hf : ContinuousOn (frequencyMap h) (realAct B r₀) :=
    (contDiffOn_frequencyMap hd).continuousOn
  have hf' := continuousOn_fderiv_frequencyMap hd
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  rcases i with a | _ <;> rcases j with b | _
  · exact (continuous_apply a).comp_continuousOn (hf'.clm_apply continuousOn_const)
  · exact (continuous_apply a).comp_continuousOn hf
  · exact (continuous_apply b).comp_continuousOn hf
  · exact continuousOn_const

/-- Cramer's rule: `A⁻¹ = (det A)⁻¹ adj A` is continuous where `det A ≠ 0`. -/
theorem continuousOn_inv_of_det_ne_zero {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] {A : X → Matrix ι ι ℝ} {S : Set X} (hA : ContinuousOn A S)
    (hdet : ∀ x ∈ S, (A x).det ≠ 0) : ContinuousOn (fun x => (A x)⁻¹) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hA ⊢
  have : S.domRestrict (fun x => (A x)⁻¹) = fun x : S => (A x).det⁻¹ • (A x).adjugate := by
    funext x
    simp only [Set.domRestrict_apply]
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hA.matrix_det.inv₀ fun x => hdet x x.2).smul hA.matrix_adjugate

/-- `I ↦ ‖𝖡_h(I)⁻¹‖` is continuous on `U` (`det 𝖡_h ≠ 0` there). -/
theorem continuousOn_norm_inv (hd : HeadData B s₀ r₀ h B' η) :
    ContinuousOn (fun I => ‖(KAM.Iso.borderedHessian h I)⁻¹‖) (realAct B r₀) :=
  continuous_norm.comp_continuousOn
    (continuousOn_inv_of_det_ne_zero (continuousOn_borderedHessian hd) fun I hI => hd.iso I hI)

/-- `bpI:p3:det-identity` (a): `det 𝖡_h(I) ≠ 0` forces `∇h(I) ≠ 0` (a zero gradient gives a
zero last row). -/
theorem frequencyMap_ne_zero_of_det_ne_zero {I : Fin 2 → ℝ}
    (hdet : (KAM.Iso.borderedHessian h I).det ≠ 0) : frequencyMap h I ≠ 0 := by
  intro hg
  apply hdet
  apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
  intro j
  rcases j with b | _
  · simp [KAM.Iso.borderedHessian, hg]
  · simp [KAM.Iso.borderedHessian]

/-- The inverse of a matrix with nonzero determinant is nonzero (index set nonempty). -/
theorem inv_ne_zero_of_det_ne_zero {A : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) ℝ}
    (hdet : A.det ≠ 0) : A⁻¹ ≠ 0 := by
  intro h0
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet.isUnit
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-- `bpI:p3:compact`. -/
theorem compact (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) :
    0 < dB B B' ∧ IsCompact (sSet B B') ∧ closure B' ⊆ sSet B B' ∧ sSet B B' ⊆ B ∧
    0 < mhConst h B B' ∧ mhConst h B B' ≤ MgConst h B B' ∧ 0 < ShConst h B B' ∧
    ∀ I ∈ sSet B B', mhConst h B B' ≤ ‖frequencyMap h I‖ ∧ ‖frequencyMap h I‖ ≤ MgConst h B B' ∧
      ‖(KAM.Iso.borderedHessian h I)⁻¹‖ ≤ ShConst h B B' := by
  have hcl : IsCompact (closure B') := hd.compact
  have hclne : (closure B').Nonempty := hne.closure
  -- the distance `dB`
  obtain ⟨δ, hδ, hδsub⟩ := hcl.exists_cthickening_subset_open hd.isOpen hd.inside
  have hBc : (Bᶜ).Nonempty := by
    by_contra hcon
    have hB : B = univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hcon
      exact hcon
    exact NormedSpace.unbounded_univ ℝ (Fin 2 → ℝ) (hB ▸ hd.bounded)
  have hlow : ∀ p ∈ closure B' ×ˢ Bᶜ, δ ≤ ‖p.1 - p.2‖ := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    by_contra hlt
    rw [not_le] at hlt
    apply hy
    apply hδsub
    exact Metric.mem_cthickening_of_dist_le y x δ _ hx
      (by rw [dist_comm, dist_eq_norm]; exact hlt.le)
  have hpne : (closure B' ×ˢ Bᶜ).Nonempty := hclne.prod hBc
  have hdB_ge : δ ≤ dB B B' :=
    le_csInf (hpne.image _) (by rintro _ ⟨p, hp, rfl⟩; exact hlow p hp)
  have hdB_pos : 0 < dB B B' := hδ.trans_le hdB_ge
  have hdB_le : ∀ x ∈ closure B', ∀ y ∈ Bᶜ, dB B B' ≤ ‖x - y‖ := fun x hx y hy =>
    csInf_le ⟨0, by rintro _ ⟨p, _, rfl⟩; exact norm_nonneg _⟩ ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  -- the set `𝒮`
  have hScomp : IsCompact (sSet B B') := hcl.cthickening
  have hsub_cl : closure B' ⊆ sSet B B' := self_subset_cthickening _
  have hSB : sSet B B' ⊆ B := by
    intro I hI
    have hI' : I ∈ cthickening (dB B B' / 2) (closure B') := hI
    rw [hcl.cthickening_eq_biUnion_closedBall (by linarith : 0 ≤ dB B B' / 2)] at hI'
    obtain ⟨x, hx, hIx⟩ := Set.mem_iUnion₂.1 hI'
    by_contra hIB
    have h1 := hdB_le x hx I hIB
    rw [← dist_eq_norm, dist_comm] at h1
    have h2 : dist I x ≤ dB B B' / 2 := hIx
    linarith
  have hSreal : sSet B B' ⊆ realAct B r₀ := hSB.trans (subset_realAct_charts hd.hr)
  have hSne : (sSet B B').Nonempty := hclne.mono hsub_cl
  -- extrema of `‖∇h‖`
  have hnorm : ContinuousOn (fun I => ‖frequencyMap h I‖) (sSet B B') :=
    (continuous_norm.comp_continuousOn (contDiffOn_frequencyMap hd).continuousOn).mono hSreal
  obtain ⟨I₁, hI₁, hmin⟩ := hScomp.exists_isMinOn hSne hnorm
  obtain ⟨I₂, hI₂, hmax⟩ := hScomp.exists_isMaxOn hSne hnorm
  have hmh : mhConst h B B' = ‖frequencyMap h I₁‖ :=
    IsLeast.csInf_eq ⟨⟨I₁, hI₁, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmin hx⟩
  have hMg : MgConst h B B' = ‖frequencyMap h I₂‖ :=
    IsGreatest.csSup_eq ⟨⟨I₂, hI₂, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmax hx⟩
  -- the maximum of the inverse norm
  have hinv : ContinuousOn (fun I => ‖(KAM.Iso.borderedHessian h I)⁻¹‖) (sSet B B') :=
    (continuousOn_norm_inv hd).mono hSreal
  obtain ⟨I₃, hI₃, hmax3⟩ := hScomp.exists_isMaxOn hSne hinv
  have hSh : ShConst h B B' = ‖(KAM.Iso.borderedHessian h I₃)⁻¹‖ :=
    IsGreatest.csSup_eq ⟨⟨I₃, hI₃, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmax3 hx⟩
  refine ⟨hdB_pos, hScomp, hsub_cl, hSB, ?_, ?_, ?_, ?_⟩
  · rw [hmh]
    exact norm_pos_iff.2 (frequencyMap_ne_zero_of_det_ne_zero (hd.iso I₁ (hSreal hI₁)))
  · rw [hmh, hMg]
    exact hmin hI₂
  · rw [hSh]
    exact norm_pos_iff.2 (inv_ne_zero_of_det_ne_zero (hd.iso I₃ (hSreal hI₃)))
  · intro I hI
    refine ⟨?_, ?_, ?_⟩
    · rw [hmh]; exact hmin hI
    · rw [hMg]; exact hmax hI
    · rw [hSh]; exact hmax3 hI

end KAM.Iso.Charts
