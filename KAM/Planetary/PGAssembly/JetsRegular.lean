/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsSlice
public import KAM.Planetary.PGAssembly.JetsIdent
public import KAM.Planetary.PGAssembly.JetsVanish
public import KAM.Planetary.PGAssembly.RealSlice

/-!
# P Part 5: regularity of the jets in the actions (`bpP:p5:be-an`)

On the tube `actionNbhd (closure V) (δ/2)`: `jetP0`, `jetOmega`, `jetBeta` are holomorphic in `I`
for each `mu` and jointly continuous in `(mu, I)`; `jetBeta` is symmetric (permutation symmetry
of the fourth derivative of the analytic average).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem tube_eq_zero_slice (d : PGData a b) :
    {I : Fin a → ℂ | (I, (0 : PGComplexPhase b)) ∈ avgDom d} =
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) :=
  Set.ext fun _ => ⟨fun h => h.1, mem_avgDom_zero d⟩

theorem jetP0_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (jetP0 d mu) (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :=
  (avgFun_differentiableOn d hmu).comp
    (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    (fun _ hI => mem_avgDom_zero d hI)

theorem jetOmega_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (j : Fin b) :
    DifferentiableOn ℂ (fun I => jetOmega d mu I j)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  have := differentiableOn_slice_jet (isOpen_avgDom d) (avgFun_differentiableOn d hmu) 2
    (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))
  rw [tube_eq_zero_slice] at this
  exact this

theorem jetBeta_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (i j : Fin b) :
    DifferentiableOn ℂ (fun I => jetBeta d mu I i j)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  have h4 := fun w : Fin 4 → PGComplexPhase b =>
    differentiableOn_slice_jet (isOpen_avgDom d) (avgFun_differentiableOn d hmu) 4 w
  rw [tube_eq_zero_slice] at h4
  by_cases hij : i = j
  · simp only [jetBeta, hij, ite_true]
    exact (h4 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))).const_smul (1 / 3 : ℂ)
      |>.congr fun I _ => by rfl
  · simp only [jetBeta, hij, ite_false]
    exact h4 _

theorem jet_continuousOn (d : PGData a b) :
    ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) ∧
    (∀ j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) ∧
    (∀ i j, ContinuousOn (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))) := by
  have hT : IsCompact (Icc (0 : ℝ) d.mu0) := isCompact_Icc
  have hd : ∀ μ ∈ Icc (0 : ℝ) d.mu0, DifferentiableOn ℂ (avgFun d μ) (avgDom d) :=
    fun μ hμ => avgFun_differentiableOn d hμ
  have hc := avgFun_continuousOn d
  have hj := fun (k : ℕ) (w : Fin k → PGComplexPhase b) =>
    continuousOn_slice_jet hT (isOpen_avgDom d) hd hc k w
  simp only [tube_eq_zero_slice] at hj
  refine ⟨?_, fun j => ?_, fun i j => ?_⟩
  · have := hj 0 (fun _ => 0)
    refine (this.congr fun z _ => ?_)
    simp [jetP0, complexAverage, avgFun]
  · exact hj 2 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))
  · by_cases hij : i = j
    · simp only [jetBeta, hij, ite_true]
      exact (hj 4 (fun _ => ((0 : Fin b → ℂ), (Pi.single j 1 : Fin b → ℂ)))).const_smul
        (1 / 3 : ℂ) |>.congr fun z _ => by rfl
    · simp only [jetBeta, hij, ite_false]
      exact hj 4 _

theorem jetBeta_isSymm (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    (jetBeta d mu I).IsSymm := by
  have hA := complexAverage_analyticAt d hmu hI
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · rw [hij]
  · have hji : j ≠ i := Ne.symm hij
    simp only [jetBeta, hij, hji, ite_false]
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3 with hσ
    have := hA.contDiffAt.iteratedFDeriv_comp_perm
      (fun k : Fin 4 => if k.val < 2 then
        ((0 : Fin b → ℂ), (Pi.single i (1 : ℂ) : Fin b → ℂ)) else
        ((0 : Fin b → ℂ), (Pi.single j (1 : ℂ) : Fin b → ℂ))) σ (n := 4)
    refine Eq.trans ?_ this
    congr 1
    funext k
    fin_cases k <;> simp [hσ, Equiv.swap_apply_def]

/-- The remainder is holomorphic in `(I, x)` on the product domain. -/
theorem pgRemainder_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (fun z : JetE a b => pgRemainder d mu z.1 z.2) (avgDom d) := by
  have hfst : ∀ z ∈ avgDom d, z.1 ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) :=
    fun z hz => hz.1
  have hI : DifferentiableOn ℂ (fun z : JetE a b => z.1) (avgDom d) :=
    differentiable_fst.differentiableOn
  have hosc : ∀ j, Differentiable ℂ (fun z : JetE a b => cOsc z.2 j) := fun j => by
    unfold cOsc
    have h1 : Differentiable ℂ (fun z : JetE a b => z.2.1 j) :=
      (differentiable_pi.1 (differentiable_fst.comp differentiable_snd)) j
    have h2 : Differentiable ℂ (fun z : JetE a b => z.2.2 j) :=
      (differentiable_pi.1 (differentiable_snd.comp differentiable_snd)) j
    fun_prop
  have hP0 := (jetP0_differentiableOn d hmu).comp hI hfst
  have hOm := fun j => (jetOmega_differentiableOn d hmu j).comp hI hfst
  have hBe := fun i j => (jetBeta_differentiableOn d hmu i j).comp hI hfst
  have hpoly : DifferentiableOn ℂ (fun z : JetE a b => jetPolynomial d mu
      (Fin.append z.1 (fun j => (z.2.1 j ^ 2 + z.2.2 j ^ 2) / 2))) (avgDom d) := by
    have hf : ∀ z : JetE a b, blockFast (Fin.append z.1
        (fun j => (z.2.1 j ^ 2 + z.2.2 j ^ 2) / 2) : Fin (a + b) → ℂ) = z.1 := fun z =>
      funext fun i => Fin.append_left _ _ i
    have hs : ∀ (z : JetE a b) j, blockSlow (Fin.append z.1
        (fun j => (z.2.1 j ^ 2 + z.2.2 j ^ 2) / 2) : Fin (a + b) → ℂ) j = cOsc z.2 j :=
      fun z j => Fin.append_right _ _ j
    simp only [jetPolynomial, hf, hs]
    have hS1 : DifferentiableOn ℂ (fun z : JetE a b => ∑ j, jetOmega d mu z.1 j * cOsc z.2 j)
        (avgDom d) :=
      DifferentiableOn.fun_sum fun j _ => (hOm j).mul (hosc j).differentiableOn
    have hS2 : DifferentiableOn ℂ (fun z : JetE a b =>
        ∑ i, ∑ j, jetBeta d mu z.1 i j * cOsc z.2 i * cOsc z.2 j) (avgDom d) :=
      DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        ((hBe i j).mul (hosc i).differentiableOn).mul (hosc j).differentiableOn
    exact (hP0.add hS1).add (hS2.const_mul (1 / 2 : ℂ))
  exact (avgFun_differentiableOn d hmu).sub hpoly

theorem remainder_jet_tube (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    (k : ℕ) (hk : k ≤ 4) : iteratedFDeriv ℂ k (pgRemainder d mu I) 0 = 0 := by
  have hdelta := (pgExtension d).delta_pos
  have hconn : IsPreconnected (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :=
    (connected_complex_tube d.hVc.closure (by positivity)).isPreconnected
  have hopen := isOpen_actionNbhd (closure d.V) ((pgExtension d).delta / 2)
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hdiff := differentiableOn_slice_jet (isOpen_avgDom d) (pgRemainder_differentiableOn d hmu)
    k v
  rw [tube_eq_zero_slice] at hdiff
  have := real_slice_identity hopen hconn hdiff (differentiableOn_const (0 : ℂ)) d.hV
    d.hVc.nonempty (fun z ⟨x, hx, hxz⟩ => hxz ▸ realInclusion_mem_tube d (subset_closure hx))
    (fun x hx => by
      show iteratedFDeriv ℂ k (pgRemainder d mu (KAM.realInclusion a x)) 0 v = 0
      rw [remainder_jet_real d hmu hx k hk]; rfl) hI
  simpa using this

end KAM.Planetary

end
