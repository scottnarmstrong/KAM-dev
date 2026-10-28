/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Orbit

/-!
# Planar quartic torsion: analyticity and symplecticity of the lift near zero angles (package T11)

Blueprint P, Part 11b (`bpP:p11b:lm-prop`).  The orbit of the full lift
(`p11cL_orbit_exists`) stays in one compact subset `K₃` of the domain of the Hamiltonian
`p11cL_ham chi`.  The compact common-neighbourhood flow of package R2 for the full field then
gives a short-time map `Ψ`, jointly real analytic and (package R3) symplectic on a neighbourhood
`U ⊇ K₃`, and by ODE uniqueness `p11c_liftFlow chi.eval` equals the `m`-fold iterate `Ψ^[m]` on
`p11cL_nbhd O' r`.  Hence it is analytic and symplectic there.  No complex domain or `SmallField`
hypothesis enters.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {O O' : Set (Fin 2 → ℝ)}

theorem p11cL_asm_continuous :
    Continuous fun x : (Fin 2 → ℝ) × Phase 2 × (Fin 2 → ℝ) =>
      (assemble x.1 x.2.2 x.2.1.2 x.2.1.1 : Phase (2 + 2)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right] <;> fun_prop

/-- Local statement: the lift is a chart on the zero-angle part of the tube. -/
theorem p11cL_chart_local (hO : IsOpen O) (hO' : IsOpen O')
    (hK : IsCompact (closure O')) (hKO : closure O' ⊆ O) (chi : QuarticFamily O) {r : ℝ}
    (hr : 0 < r) (hfs : p11cL_FlowSpec chi.eval (closure O') (2 * r)) :
    IsChart 1 (p11c_liftFlow chi.eval) (p11cL_nbhd O' r) := by
  set K : Set (Fin 2 → ℝ) := closure O' with hKdef
  have hO'K : O' ⊆ K := subset_closure
  -- a uniform bound for the action derivative of `chi`
  obtain ⟨D, hD0, hD⟩ := p11cL_exists_bound chi hK hKO (2 * r)
  -- the compact set carrying every orbit
  set asm : (Fin 2 → ℝ) × Phase 2 × (Fin 2 → ℝ) → Phase (2 + 2) :=
    fun x => assemble x.1 x.2.2 x.2.1.2 x.2.1.1 with hasm
  set K₃ : Set (Phase (2 + 2)) :=
    asm '' (K ×ˢ (closedBall (0 : Phase 2) (2 * r) ×ˢ closedBall (0 : Fin 2 → ℝ) (1 + D))) with hK₃
  have hK₃c : IsCompact K₃ :=
    (hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image
      p11cL_asm_continuous
  have hK₃W : K₃ ⊆ p11cL_dom O := by
    rintro _ ⟨x, hx, rfl⟩
    show p11cL_act _ ∈ O
    rw [p11cL_act_assemble]; exact hKO hx.1
  have hana : AnalyticOnNhd ℝ (hamiltonianVectorField (p11cL_ham chi)) (p11cL_dom O) :=
    fun w hw => p11c_hamField_analyticAt (p11cL_ham_analytic chi w hw)
  have hC1 : ContDiffOn ℝ 1 (hamiltonianVectorField (p11cL_ham chi)) (p11cL_dom O) :=
    (hana.contDiffOn (p11cL_dom_isOpen hO).uniqueDiffOn).of_le (by norm_cast)
  obtain ⟨U, hUo, hK₃U, hUW, T, hT, Φ, hΦa, hΦs⟩ := p11cQ_flow_compact_nbhd
    (p11cL_dom_isOpen hO) hana hK₃c hK₃W
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / T)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hmT : 1 < m * T := (div_lt_iff₀ hT).1 hm
  set hs : ℝ := 1 / m with hhs
  have hs0 : 0 < hs := by positivity
  have hsT : hs < T := by rw [hhs, div_lt_iff₀ hm0]; linarith
  have hmh : (m : ℝ) * hs = 1 := by rw [hhs]; field_simp
  set Ψ : Phase (2 + 2) → Phase (2 + 2) := fun y => Φ hs y with hΨdef
  have hΨ : AnalyticOnNhd ℝ Ψ U := fun y hy =>
    (hΦa (hs, y) ⟨⟨by linarith, hsT⟩, hy⟩).comp (analyticAt_const.prod analyticAt_id)
  -- the iterates follow the explicit orbit
  have key : ∀ w ∈ p11cL_nbhd O' r, ∃ g : ℝ → Phase (2 + 2), g 1 = p11c_liftFlow chi.eval w ∧
      (∀ j : ℕ, j ≤ m → Ψ^[j] w = g (j * hs)) ∧ ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ K₃ := by
    intro w hw
    obtain ⟨g, hg, hg0, hg1, hgb⟩ := p11cL_orbit_exists chi hKO hr hfs hD0 hD hO'K hw.1 hw.2.1
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ K₃ := by
      intro t ht
      obtain ⟨hA, hB, hC, -⟩ := hgb t ht
      refine ⟨(p11cL_act (g t), p11cL_slow (g t), p11cL_ang (g t)),
        ⟨?_, ?_, ?_⟩, p11cL_assemble_eq (g t)⟩
      · rw [hA]; exact hO'K hw.1
      · simpa using hB
      · have := hw.2.2
        simp only [mem_closedBall, dist_zero_right]
        linarith
    refine ⟨g, hg1, ?_, hmem⟩
    intro j
    induction j with
    | zero => intro _; simp [hg0]
    | succ j ih =>
      intro hj
      have hj' : j ≤ m := Nat.le_of_succ_le hj
      have hjh0 : 0 ≤ (j : ℝ) * hs := by positivity
      have hjh : ((j + 1 : ℕ) : ℝ) * hs ≤ 1 := by
        rw [← hmh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hs0.le
      push_cast at hjh
      have hjt : (j : ℝ) * hs ∈ Icc (0 : ℝ) 1 := ⟨hjh0, by linarith⟩
      rw [Function.iterate_succ_apply', ih hj']
      obtain ⟨h0, hΓ⟩ := hΦs _ (hK₃U (hmem _ hjt))
      have hJ : (Ioo (-T) T ∩ Icc (-((j : ℝ) * hs)) (1 - j * hs)).OrdConnected :=
        ordConnected_Ioo.inter ordConnected_Icc
      have h0J : (0 : ℝ) ∈ Ioo (-T) T ∩ Icc (-((j : ℝ) * hs)) (1 - j * hs) :=
        ⟨⟨by linarith, hT⟩, by linarith, by linarith⟩
      have hg2 : IsSolutionIn (hamiltonianVectorField (p11cL_ham chi)) (p11cL_dom O)
          (Ioo (-T) T ∩ Icc (-((j : ℝ) * hs)) (1 - j * hs)) (fun s => g (s + j * hs)) := by
        intro s hsJ
        have hsg : s + j * hs ∈ Ioo (-1 / 2 : ℝ) (3 / 2) :=
          ⟨by linarith [hsJ.2.1], by linarith [hsJ.2.2]⟩
        obtain ⟨hm1, hm2⟩ := hg _ hsg
        exact ⟨hm1, hm2.comp_add_const s (j * hs)⟩
      have heq := gen_uniqueness (p11cL_dom_isOpen hO) hC1 hJ h0J
        (hΓ.mono inter_subset_left) hg2 (by simp [h0])
        (show hs ∈ Ioo (-T) T ∩ Icc (-((j : ℝ) * hs)) (1 - j * hs) from
          ⟨⟨by linarith, hsT⟩, by linarith, by linarith⟩)
      show Φ hs (g (j * hs)) = _
      rw [show Φ hs (g (j * hs)) = g (hs + j * hs) from heq]
      congr 1
      push_cast; ring
  have horb : ∀ w ∈ p11cL_nbhd O' r, ∀ j < m, Ψ^[j] w ∈ U := by
    intro w hw j hj
    obtain ⟨g, -, hit, hmem⟩ := key w hw
    rw [hit j hj.le]
    refine hK₃U (hmem _ ⟨by positivity, ?_⟩)
    have : (j : ℝ) * hs ≤ m * hs := mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) hs0.le
    linarith
  have hev : ∀ w ∈ p11cL_nbhd O' r, p11c_liftFlow chi.eval =ᶠ[𝓝 w] Ψ^[m] := by
    intro w hw
    filter_upwards [(p11cL_nbhd_isOpen hO' r).mem_nhds hw] with w' hw'
    obtain ⟨g, hg1, hit, -⟩ := key w' hw'
    rw [← hg1, hit m le_rfl, hmh]
  have hanaIt : ∀ w ∈ p11cL_nbhd O' r, AnalyticAt ℝ (Ψ^[m]) w := fun w hw =>
    p11cQ_iterate_analyticAt hΨ (horb w hw)
  -- the short-time map is symplectic
  have hsymp : ∀ y ∈ U, ∀ u v : Phase (2 + 2),
      symplecticForm (fderiv ℝ Ψ y u) (fderiv ℝ Ψ y v) = symplecticForm u v := by
    intro y hy u v
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo y hy
    have h := p11cVar_isSymplecticOn (H := p11cL_ham chi) (W := p11cL_dom O) (x := y) (r := ε)
      (T := T) (Φ := Φ) (p11cL_ham_analytic chi)
      (hΦa.mono (prod_mono subset_rfl hball)) (fun y' hy' => (hΦs y' (hball hy')).2) hT
      (fun y' hy' => (hΦs y' (hball hy')).1) (t := hs) ⟨by linarith, hsT⟩ y (mem_ball_self hε) u v
    simpa using h
  have hsympIt : ∀ w ∈ p11cL_nbhd O' r, ∀ j : ℕ, j ≤ m → ∀ u v : Phase (2 + 2),
      symplecticForm (fderiv ℝ (Ψ^[j]) w u) (fderiv ℝ (Ψ^[j]) w v) = symplecticForm u v := by
    intro w hw j
    induction j with
    | zero => intro _ u v; simp
    | succ j ih =>
      intro hj u v
      have hj' : j ≤ m := Nat.le_of_succ_le hj
      have hdj : DifferentiableAt ℝ (Ψ^[j]) w :=
        (p11cQ_iterate_analyticAt hΨ fun i hi => horb w hw i (lt_of_lt_of_le hi hj')).differentiableAt
      have hdΨ : DifferentiableAt ℝ Ψ (Ψ^[j] w) := (hΨ _ (horb w hw j (by omega))).differentiableAt
      have hc : fderiv ℝ (Ψ^[j + 1]) w = (fderiv ℝ Ψ (Ψ^[j] w)).comp (fderiv ℝ (Ψ^[j]) w) := by
        rw [Function.iterate_succ']
        exact fderiv_comp w hdΨ hdj
      rw [hc]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hsymp _ (horb w hw j (by omega)), ih hj']
  refine ⟨fun w hw => ?_, fun w hw u v => ?_⟩
  · exact (hanaIt w hw).congr (hev w hw).symm
  · rw [(hev w hw).fderiv_eq]
    simpa using hsympIt w hw m le_rfl u v

end KAM.Planetary

end
