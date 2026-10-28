/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsFourth
public import KAM.Planetary.PGAssembly.JetsDefs
public import KAM.Planetary.PGAssembly.JetsRegular

/-!
# P Part 5: the extended Birkhoff data (`bpP:p5:birkhoff-ext`, `stepP:p5:be-*`)

Facade of package P5-JET. `fourth_jet_unique` (`JetsFourth`), the jets `jetP0`, `jetOmega`,
`jetBeta`, `jetPolynomial` and the remainder `pgRemainder` (`JetsDefs`), and the two Birkhoff
extension theorems `birkhoff_ext` and `birkhoff_ext_parameter_regularity`:
identification with the frozen `P0, Omega, beta` on `V` (`JetsIdent`), holomorphy and joint
continuity of the jets, symmetry of `jetBeta` (`JetsRegular`), vanishing of the remainder jet of
order `≤ 4` on the whole tube (`JetsVanish`, identity theorem in `JetsRegular`), and the closure
torsion bound (below).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem jetBeta_det_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) :
    d.B ≤ ‖(jetBeta d mu (KAM.realInclusion a I)).det‖ := by
  have h : jetBeta d mu (KAM.realInclusion a I) =
      Complex.ofRealHom.mapMatrix (d.beta mu I) := by
    ext i j
    simp [jetBeta_real d hmu hI]
  rw [h, ← RingHom.map_det]
  simpa using d.htorsion mu hmu I hI

theorem jetBeta_det_closure (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ closure d.V) :
    d.B ≤ ‖(jetBeta d mu (KAM.realInclusion a I)).det‖ := by
  have hF : ContinuousOn (fun I : Fin a → ℝ => jetBeta d mu (KAM.realInclusion a I))
      (closure d.V) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact (jetBeta_differentiableOn d hmu i j).continuousOn.comp
      (KAM.realInclusion a).continuous.continuousOn fun x hx => realInclusion_mem_tube d hx
  have hcont : ContinuousOn (fun I : Fin a → ℝ =>
      ‖(jetBeta d mu (KAM.realInclusion a I)).det‖) (closure d.V) :=
    ((continuous_id.matrix_det).comp_continuousOn hF).norm
  have hnb : (𝓝[d.V] I).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hI
  exact ge_of_tendsto ((hcont I hI).mono subset_closure).tendsto
    (eventually_nhdsWithin_of_forall fun x hx => jetBeta_det_real d hmu hx)

theorem birkhoff_ext (d : PGData a b) :
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ d.V,
      jetP0 d mu (KAM.realInclusion a I) = (d.P0 mu I : ℂ) ∧
      (∀ j, jetOmega d mu (KAM.realInclusion a I) j = (d.Omega mu I j : ℂ)) ∧
      (∀ i j, jetBeta d mu (KAM.realInclusion a I) i j = (d.beta mu I i j : ℂ))) ∧
    (∀ mu ∈ Icc 0 d.mu0,
      DifferentiableOn ℂ (jetP0 d mu) (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2)) ∧
      (∀ j, DifferentiableOn ℂ (fun I => jetOmega d mu I j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2))) ∧
      (∀ i j, DifferentiableOn ℂ (fun I => jetBeta d mu I i j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2)))) ∧
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
      ∀ k : ℕ, k ≤ 4 → iteratedFDeriv ℂ k (pgRemainder d mu I) 0 = 0) ∧
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ closure d.V,
      d.B ≤ ‖(jetBeta d mu (KAM.realInclusion a I)).det‖) :=
  ⟨fun mu hmu I hI => ⟨jetP0_real d hmu hI, jetOmega_real d hmu hI, jetBeta_real d hmu hI⟩,
    fun mu hmu => ⟨jetP0_differentiableOn d hmu, jetOmega_differentiableOn d hmu,
      jetBeta_differentiableOn d hmu⟩,
    fun mu hmu I hI k hk => remainder_jet_tube d hmu hI k hk,
    fun mu hmu I hI => jetBeta_det_closure d hmu hI⟩

theorem birkhoff_ext_parameter_regularity (d : PGData a b) :
    ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2)) ∧
    (∀ j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ i j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ mu ∈ Icc 0 d.mu0,
      ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
        (jetBeta d mu I).IsSymm) :=
  ⟨(jet_continuousOn d).1, (jet_continuousOn d).2.1, (jet_continuousOn d).2.2,
    fun mu hmu I hI => jetBeta_isSymm d hmu hI⟩

end KAM.Planetary

end
