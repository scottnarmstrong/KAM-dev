/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PatchHessian
public import KAM.Planetary.Nondegeneracy.Frequency
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.WeakMeasure.FiniteType

/-!
# The Part 10 patch (P11A-P1, `bpP:p11:sec-A#data`, `bpP:p11:norm-dict`)

`p11_patch`: around the physical action point there is a Part 10 patch of simple axes, and the
`2π`-rescaled cube `K` inside it with the specification `P11PatchSpec`. The clause on the
characteristic polynomial of the literal secular Hessian is the bridge `p11SecularMatrix_eq` to
Part 8's `coeffs`, followed by `charpoly_eq_prod_sorted`; the frequency identity is
`Nondegeneracy.frequency` rescaled, and the amount comes from `rank_compact` and `norm_dict`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace KAM.Planetary

section Patch

variable {n : ℕ}

private theorem patch_simple (E : SecularForm.Data n) {a : SecularForm.Vec n}
    (ha : a ∈ SecularSpectrum.goodAxes E) : a ∈ SecularSpectrum.simpleAxes E := by
  refine ⟨ha.1, fun h => ha.2 ?_⟩
  simp [SecularSpectrum.good, h]

private theorem patch_scale_inv (r : ℝ) (hr : r ≠ 0) (J : P11Vec n) :
    r⁻¹ • (r • J) = J := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- Implementation uses Part 10 interface and shrinks the physical patch to the requested tube. -/
theorem p11_patch {n : ℕ} (D : P11Physical n) : ∃ A, P11PatchSpec D A := by
  have hn : 2 ≤ n := D.n_ge
  have hn1 : 1 ≤ n := by omega
  set E := p11PhysicalData D with hE
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have haD : D.a ∈ SecularForm.axes n := ⟨D.a_pos, D.ordered⟩
  have hδpos : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  set δ := p11PhysicalDelta D with hδ
  have hcont : Continuous (SecularForm.action E) := by unfold SecularForm.action; fun_prop
  set T : Set (P11Vec n) :=
    {L | ∀ i, |L i - D.m i * Real.sqrt (D.G * D.m0 * D.a i)| < δ / 8} with hT
  have hTU : IsOpen (SecularForm.action E ⁻¹' T) := by
    have : IsOpen T := by
      rw [hT, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
    exact this.preimage hcont
  have hDaU : D.a ∈ SecularForm.action E ⁻¹' T := fun i => by
    simpa [SecularForm.action, hE, p11PhysicalData] using (by positivity : 0 < δ / 8)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hTU D.a hDaU
  obtain ⟨a0, c, ha0, hcl⟩ := (Nondegeneracy.good_set E hn).2.2.2 D.a haD η hη
  set B : Set (P11Vec n) := Metric.ball c a0 with hB
  have hBsub : B ⊆ Metric.closedBall c (2 * a0) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hBS : B ⊆ SecularSpectrum.simpleAxes E := fun x hx =>
    patch_simple E (hcl (hBsub hx)).1
  have hBU : B ⊆ SecularForm.action E ⁻¹' T := fun x hx => hball (hcl (hBsub hx)).2
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBc : IsConnected B :=
    ⟨⟨c, Metric.mem_ball_self ha0⟩, (convex_ball c a0).isPreconnected⟩
  obtain ⟨-, -, hAn, hRnd, -, -⟩ := Nondegeneracy.rnd E hn hBo hBc hBS
  set V0 : Set (P11Vec n) := SecularForm.action E '' B with hV0
  have hV0o : IsOpen V0 := by
    have : V0 = SecularForm.actionDomain E ∩ SecularForm.axis E ⁻¹' B := by
      ext L
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, (hBS hb).1, rfl⟩, by simpa [SecularForm.axis_action E (hBS hb).1] using hb⟩
      · rintro ⟨⟨b, hb, rfl⟩, h⟩
        exact ⟨b, by simpa [SecularForm.axis_action E hb] using h, rfl⟩
    rw [this]
    exact (Nondegeneracy.action_diffeomorphism E).2.2.2.1.inter
      (hBo.preimage (SecularForm.continuous_axis E))
  have hV0c : IsConnected V0 := hBc.image _ hcont.continuousOn
  have hΛ0 : SecularForm.action E c ∈ V0 := ⟨c, Metric.mem_ball_self ha0, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hV0o _ hΛ0
  set K0 : Set (P11Vec n) := Metric.closedBall (SecularForm.action E c) (ε / 2) with hK0
  have hK0sub : K0 ⊆ V0 := (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  have hK0c : IsCompact K0 := isCompact_closedBall _ _
  have hK0ne : K0.Nonempty := ⟨_, Metric.mem_closedBall_self (by linarith)⟩
  obtain ⟨mu, hmu, hpos⟩ := rank_compact hn1 (by omega : 1 ≤ n + n) hV0o hV0c.isPreconnected
    hK0c hK0ne hK0sub hAn hRnd (rho := 2) (Or.inr rfl)
  obtain ⟨hAnJ, hRndJ, hamJ⟩ := norm_dict (n := n) (m := n + n) (mu := mu) hn1 (by omega)
    hV0o hK0c hK0ne hK0sub hAn hpos le_rfl
  have hscale : Continuous (fun J : P11Vec n => (2 * Real.pi) • J) := by fun_prop
  have hKeq : (fun J : P11Vec n => (2 * Real.pi) • J) '' K0 =
      Metric.closedBall ((2 * Real.pi) • SecularForm.action E c) (2 * Real.pi * (ε / 2)) := by
    rw [Set.image_smul, hK0, smul_closedBall _ _ (by positivity),
      Real.norm_of_nonneg (by positivity)]
  refine ⟨⟨(fun J : P11Vec n => (2 * Real.pi) • J) '' K0,
    (fun J : P11Vec n => (2 * Real.pi) • J) '' V0,
    fun J => (2 * Real.pi)⁻¹ • Nondegeneracy.frequency E ((2 * Real.pi)⁻¹ • J),
    fun J => SecularSpectrum.sigma E (SecularForm.axis E ((2 * Real.pi)⁻¹ • J)),
    mu, (2 * Real.pi) ^ (-(2 + (mu : ℝ))) * index_def 2 mu
      (Nondegeneracy.frequency E) K0⟩, ?_⟩
  dsimp only [P11PatchSpec]
  refine ⟨?_, ?_, (isOpenMap_smul₀ hpi) _ hV0o,
    hV0c.isPreconnected.image _ hscale.continuousOn, hK0c.image hscale, hK0ne.image _,
    Set.image_mono hK0sub, ?_, ?_, hmu,
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) hpos, hAnJ, hRndJ, hamJ, ?_⟩
  · rintro J ⟨L, ⟨b, hb, rfl⟩, rfl⟩
    simp only [patch_scale_inv _ hpi, SecularForm.axis_action E (hBS hb).1]
    refine ⟨(SecularSpectrum.sorted_monotone
      (SecularForm.coeffs_hermitian E b)).strictMono_of_injective
      ((SecularSpectrum.discriminant_ne_zero_iff _).1 (hBS hb).2), ?_⟩
    rw [p11SecularMatrix_eq D (hBS hb).1]
    exact SecularSpectrum.charpoly_eq_prod_sorted (SecularForm.coeffs_hermitian E b)
  · intro J _
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Nondegeneracy.frequency, Fin.append_left, Pi.smul_apply, smul_eq_mul,
        SecularForm.nu, hE, p11PhysicalData]
      ring
    · simp only [Nondegeneracy.frequency, Fin.append_right, Pi.smul_apply, smul_eq_mul]
      ring
  · rw [hKeq]
    exact (Metric.measure_closedBall_pos volume _ (by positivity))
  · rw [hKeq]
    have := (convex_closedBall ((2 * Real.pi) • SecularForm.action E c)
      (2 * Real.pi * (ε / 2))).addHaar_frontier volume
    rwa [Metric.isClosed_closedBall.frontier_eq] at this
  · rintro J ⟨L, hL, rfl⟩ i
    obtain ⟨b, hb, rfl⟩ := hK0sub hL
    have := hBU hb i
    simpa [mul_div_cancel_left₀ _ hpi] using this

/-- The patch chosen by `p11_patch`. -/
def p11PatchData {n : ℕ} (D : P11Physical n) : P11PatchData n := (p11_patch D).choose

theorem p11PatchData_spec {n : ℕ} (D : P11Physical n) : P11PatchSpec D (p11PatchData D) :=
  (p11_patch D).choose_spec

end Patch

end KAM.Planetary

end
