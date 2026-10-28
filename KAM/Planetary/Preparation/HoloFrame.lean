/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Patch
public import KAM.Planetary.Preparation.BasePoint
public import KAM.Planetary.SecularSpectrum.LocalAnalytic
public import KAM.Planetary.Nondegeneracy.GoodAxes.SortedAnalytic
public import KAM.Planetary.Nondegeneracy.Frequency

/-!
# The analytic secular frame at the base point (P11A-P2b, `stepP:p11:hc-rot`)

Around `Λ₀ = J₀/(2π)` the patch of `p11PatchData D` is in the actions of ordered axes
(`p11_axis_mem_axes`: the forward tube bounds `|a'ᵢ - aᵢ|` by `p11Zeta`, which is at most a sixth of
every axis gap), and `p11_holo_frame` produces the analytic `SO(n)` eigenframe `R` of the literal
secular Hessian `p11SecularMatrix D` (`SecularSpectrum.local_analytic` for the family
`Λ ↦ coeffs (axis Λ)`), identified with the patch spectrum `(p11PatchData D).sigma`.
-/

@[expose] public noncomputable section
open Set Filter Metric Polynomial
open scoped Topology
namespace KAM.Planetary
open SecularForm

section Frame

variable {n : ℕ}

/-- Actions close to the physical action are positive. -/
theorem p11_pos_of_close (D : P11Physical n) {Λ : P11Vec n}
    (hΛ : ∀ i, |Λ i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| < p11PhysicalDelta D / 8) :
    ∀ i, 0 < Λ i := fun i => by
  have hδ4 : ∀ i, p11PhysicalDelta D ≤ D.m i * Real.sqrt (D.G * D.m0 * D.a i) / 4 :=
    (forward_tube D (p11_zeta_pos D)).choose_spec.2.1
  have hδ0 : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  have h1 := (abs_lt.1 (hΛ i)).1
  have h2 := hδ4 i
  linarith

/-- The forward tube controls the axis gaps: actions `δ/8`-close to the physical action are the
actions of ordered axes. -/
theorem p11_axis_mem_axes (D : P11Physical n) {Λ : P11Vec n}
    (hΛ : ∀ i, |Λ i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| < p11PhysicalDelta D / 8) :
    axis (p11PhysicalData D) Λ ∈ axes n := by
  obtain ⟨hδ0, hδ4, hft⟩ : 0 < p11PhysicalDelta D ∧
      (∀ i, p11PhysicalDelta D ≤ D.m i * Real.sqrt (D.G * D.m0 * D.a i) / 4) ∧
      ∀ w : Phase (n + n),
        (∀ i : Fin n, |w.2 (Fin.castAdd n i) - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| ≤
          p11PhysicalDelta D) →
        (∀ i, poincareGamma (planetBlock w i) ≤ p11PhysicalDelta D) →
        w ∈ poincareProdDom n ∧
          ‖poincareProd D.m (D.G * D.m0) w -
            circularPoint D.G D.m0 D.m D.a
              (fun i => w.1 (Fin.castAdd n i) / (2 * Real.pi))‖ < p11Zeta D :=
    (forward_tube D (p11_zeta_pos D)).choose_spec
  set δ := p11PhysicalDelta D with hδ
  have hpos : ∀ i, 0 < Λ i := p11_pos_of_close D hΛ
  set E := p11PhysicalData D with hE
  have hax : ∀ i, 0 < axis E Λ i := fun i => by
    have h1 := D.m_pos i
    have h2 := D.G_pos
    have h3 := D.m0_pos
    have h4 := hpos i
    simp only [axis, hE, p11PhysicalData]
    positivity
  refine ⟨hax, ?_⟩
  have hact : action E (axis E Λ) = Λ := action_axis E hpos
  set a' := axis E Λ with ha'
  have hcirc := circularPoint_eq_poincareProd D.G_pos D.m0_pos D.m_pos hax
    (fun _ : Fin n => (0 : ℝ))
  have hw : (fun i => D.m i * Real.sqrt (D.G * D.m0 * a' i)) = Λ := hact
  rw [hw] at hcirc
  have hnorm := (hft (assemble Λ (fun _ => 0) 0 0) (fun i => by
      have h8 : δ / 8 ≤ δ := by linarith
      simpa [assemble, fast, slow, Fin.append_left] using ((hΛ i).le.trans h8))
    (fun i => by
      simp [poincareGamma, assemble, planetBlock, slow, hδ0.le]))
  have hnorm' := hnorm.2
  have hP : poincareProd D.m (D.G * D.m0) (assemble Λ (fun _ => 0) 0 0) =
      circularPoint D.G D.m0 D.m a' (fun _ => 0) := by simpa using hcirc.symm
  have hφ : (fun i : Fin n => (assemble Λ (fun _ => 0) 0 0).1 (Fin.castAdd n i) /
      (2 * Real.pi)) = fun _ => 0 := by
    funext i; simp [assemble, Fin.append_left]
  rw [hP, hφ] at hnorm'
  have key : ∀ i, |a' i - D.a i| < p11Zeta D := fun i => by
    set x := circularPoint D.G D.m0 D.m a' (fun _ => 0) -
      circularPoint D.G D.m0 D.m D.a (fun _ => 0) with hx
    have h1 : |x.1 (finProdFinEquiv (i, (0 : Fin 2)))| ≤ ‖x‖ :=
      ((norm_le_pi_norm x.1 _).trans (norm_fst_le x)).trans_eq' (Real.norm_eq_abs _).symm
    have h2 : x.1 (finProdFinEquiv (i, (0 : Fin 2))) = a' i - D.a i := by
      simp only [hx, circularPoint, Prod.fst_sub, Pi.sub_apply, Equiv.symm_apply_apply]
      simp
    rw [h2] at h1
    exact h1.trans_lt hnorm'
  have hgap : ∀ i j : Fin n, i < j → 6 * p11Zeta D ≤ D.a j - D.a i := fun i j hij => by
    have hfin : ({x | ∃ i, x = D.a i} ∪
        {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}).Finite := by
      refine Set.Finite.union ((Set.finite_range D.a).subset ?_) ?_
      · rintro x ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · exact (Set.finite_range (fun p : Fin n × Fin n => |D.a p.1 - D.a p.2|)).subset
          (by rintro x ⟨i, j, -, rfl⟩; exact ⟨(i, j), rfl⟩)
    have hle : sInf ({x | ∃ i, x = D.a i} ∪
        {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}) ≤ |D.a i - D.a j| :=
      csInf_le hfin.bddBelow (Or.inr ⟨i, j, hij.ne, rfl⟩)
    have hz : p11Zeta D ≤ sInf ({x | ∃ i, x = D.a i} ∪
        {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}) / 6 := min_le_right _ _
    have hlt : D.a i < D.a j := D.ordered hij
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 hlt)] at hle
    linarith
  intro i j hij
  have h1 := abs_lt.1 (key i)
  have h2 := abs_lt.1 (key j)
  have h3 := hgap i j hij
  have h4 := p11_zeta_pos D
  linarith

/-- The sorted spectrum of the Part 8 matrix at ordered axes is the patch spectrum. -/
theorem p11_sorted_eq_patch (D : P11Physical n) {L : P11Vec n} (hL : (2 * Real.pi) • L ∈
    (p11PatchData D).V) (hax : axis (p11PhysicalData D) L ∈ axes n) (hpos : ∀ i, 0 < L i) :
    SecularSpectrum.sigma (p11PhysicalData D) (axis (p11PhysicalData D) L) =
      (p11PatchData D).sigma ((2 * Real.pi) • L) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  obtain ⟨hmono, hcp⟩ := (p11PatchData_spec D).1 _ hL
  rw [smul_smul, inv_mul_cancel₀ hpi, one_smul] at hcp
  have hM : p11SecularMatrix D L = coeffs (p11PhysicalData D) (axis (p11PhysicalData D) L) := by
    have := p11SecularMatrix_eq D hax
    rwa [action_axis (p11PhysicalData D) hpos] at this
  rw [hM] at hcp
  have h1 := SecularSpectrum.charpoly_eq_prod_sorted
    (coeffs_hermitian (p11PhysicalData D) (axis (p11PhysicalData D) L))
  exact Nondegeneracy.eq_of_monotone_prod (SecularSpectrum.sorted_monotone _) hmono.monotone
    (h1.symm.trans hcp)

open scoped Matrix.Norms.Elementwise in
/-- `hc-rot` (data): an analytic `SO(n)` frame of the literal secular Hessian near
`Λ₀ = J₀/(2π)`, matched with the patch spectrum. -/
theorem p11_holo_frame (D : P11Physical n) {J0 : P11Vec n} (hJ0 : J0 ∈ (p11PatchData D).K) :
    ∃ t1 : ℝ, 0 < t1 ∧ ∃ R : P11Vec n → Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, AnalyticOnNhd ℝ (fun x => R x i j) (Metric.ball ((2 * Real.pi)⁻¹ • J0) t1)) ∧
      ∀ L ∈ Metric.ball ((2 * Real.pi)⁻¹ • J0) t1,
        (2 * Real.pi) • L ∈ (p11PatchData D).V ∧ L ∈ actionDomain (p11PhysicalData D) ∧
        SecularSpectrum.isSO (R L) ∧
        coeffs (p11PhysicalData D) (axis (p11PhysicalData D) L) =
          R L * Matrix.diagonal (SecularSpectrum.sigma (p11PhysicalData D)
            (axis (p11PhysicalData D) L)) * (R L).transpose ∧
        (p11PatchData D).sigma ((2 * Real.pi) • L) =
          SecularSpectrum.sigma (p11PhysicalData D) (axis (p11PhysicalData D) L) ∧
        (R L).transpose * p11SecularMatrix D L * R L =
          Matrix.diagonal ((p11PatchData D).sigma ((2 * Real.pi) • L)) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set E := p11PhysicalData D with hE
  set Λ0 : P11Vec n := (2 * Real.pi)⁻¹ • J0 with hΛ0
  obtain ⟨-, -, hVo, -, -, -, hKV, -, -, -, -, -, -, -, hKclose⟩ := p11PatchData_spec D
  have hJV : J0 ∈ (p11PatchData D).V := hKV hJ0
  have hclose : ∀ i, |Λ0 i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| <
      p11PhysicalDelta D / 8 := fun i => by
    have := hKclose J0 hJ0 i
    simpa [hΛ0, div_eq_inv_mul] using this
  have hpos0 := p11_pos_of_close D hclose
  have hax0 := p11_axis_mem_axes D hclose
  have hW0 : Λ0 ∈ actionDomain E := ⟨axis E Λ0, hax0, action_axis E hpos0⟩
  have hJV' : (2 * Real.pi) • Λ0 ∈ (p11PatchData D).V := by
    rwa [hΛ0, smul_smul, mul_inv_cancel₀ hpi, one_smul]
  have hsig0 := p11_sorted_eq_patch D hJV' hax0 hpos0
  have hmono0 : StrictMono (SecularSpectrum.sigma E (axis E Λ0)) := by
    rw [hsig0]; exact ((p11PatchData_spec D).1 _ hJV').1
  have hWo := (Nondegeneracy.action_diffeomorphism E).2.2.2.1
  have hMan : AnalyticOnNhd ℝ (fun x => coeffs E (axis E x)) (actionDomain E) := by
    refine (coeffs_analytic E).comp (Nondegeneracy.action_diffeomorphism E).2.2.2.2.2.1 ?_
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rwa [(Nondegeneracy.action_diffeomorphism E).2.2.2.2.2.2.1 a ha]
  obtain ⟨r, hr, hball, s, R, hs, hR, h⟩ := SecularSpectrum.local_analytic hWo
    (fun x _ => coeffs_hermitian E (axis E x)) hMan hW0
    (SecularSpectrum.eigenvalues_injective_of_sorted _ hmono0.injective)
  obtain ⟨r', hr', hr'V⟩ := Metric.isOpen_iff.1
    (hVo.preimage (continuous_const_smul (2 * Real.pi)))
    Λ0 hJV'
  refine ⟨min r r', lt_min hr hr', R, fun i j x hx =>
    SecularSpectrum.analyticAt_mat_entry
      (hR x (Metric.ball_subset_ball (min_le_left _ _) hx)) i j, fun L hL => ?_⟩
  have hL1 : L ∈ Metric.ball Λ0 r := Metric.ball_subset_ball (min_le_left _ _) hL
  have hL2 : L ∈ Metric.ball Λ0 r' := Metric.ball_subset_ball (min_le_right _ _) hL
  have hLV : (2 * Real.pi) • L ∈ (p11PatchData D).V := hr'V hL2
  have hLW := hball hL1
  obtain ⟨a, ha, haL⟩ := hLW
  have hLpos : ∀ i, 0 < L i := fun i => by
    rw [← haL]
    have := ha.1 i
    have := D.m_pos i
    have := D.G_pos
    have := D.m0_pos
    simp only [action, hE, p11PhysicalData]
    positivity
  have hLax : axis E L ∈ axes n := by
    rw [← haL, (Nondegeneracy.action_diffeomorphism E).2.2.2.2.2.2.1 a ha]; exact ha
  obtain ⟨hSO, hmono, hM⟩ := h L hL1
  have hsorted := Nondegeneracy.sorted_eq_of_frame (coeffs_hermitian E (axis E L)) hSO.1 hmono hM
  have hsig : SecularSpectrum.sigma E (axis E L) = s L := hsorted
  have hpat := p11_sorted_eq_patch D hLV hLax hLpos
  have hMeq : p11SecularMatrix D L = coeffs E (axis E L) := by
    have := p11SecularMatrix_eq D hLax
    rwa [action_axis E hLpos] at this
  refine ⟨hLV, ⟨a, ha, haL⟩, hSO, by rw [hsig]; exact hM, by rw [← hpat], ?_⟩
  rw [← hpat, hsig, hMeq, hM]
  calc (R L).transpose * (R L * Matrix.diagonal (s L) * (R L).transpose) * R L
      = ((R L).transpose * R L) * Matrix.diagonal (s L) * ((R L).transpose * R L) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hSO.1, Matrix.one_mul, Matrix.mul_one]

end Frame

end KAM.Planetary

end
