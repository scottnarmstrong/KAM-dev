/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvLimit

/-!
# Two-scale KAM: the real field of a real holomorphic Hamiltonian

For `G` holomorphic and real on reals on an open `W ⊆ ℂⁿ × ℂⁿ`, the real Hamiltonian field of
`H = Re (G ∘ ι₂)` is continuous on the real points of `W` (`hvf_continuousOn`); it is read through
the complex field `hamiltonianVectorFieldℂ G`, which is continuous because `G` is `C^∞`. Used for
the passage of the field to the limit in `stepP:p3:inv-lim`. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace KAM.Planetary

open KAM.Canonical

/-- The real Hamiltonian field of `Re (G ∘ ι₂)` is continuous on the real points of `W`. -/
theorem hvf_continuousOn {n : ℕ} {W : Set (CPhase n)} {G : CPhase n → ℂ} (hW : IsOpen W)
    (hG : DifferentiableOn ℂ G W)
    (hreal : ∀ x : Phase n, KAM.realInclusion₂ n x ∈ W → (G (KAM.realInclusion₂ n x)).im = 0) :
    ContinuousOn (KAM.hamiltonianVectorField fun z : Phase n => (G (KAM.realInclusion₂ n z)).re)
      (KAM.realInclusion₂ n ⁻¹' W) := by
  have hsm : ContDiffOn ℂ ∞ G W := KAM.contDiffOn_infty_of_differentiableOn hW hG
  have hfd : ContinuousOn (fderiv ℂ G) W := hsm.continuousOn_fderiv_of_isOpen hW (by simp)
  have hiso : Isometry (KAM.realInclusion₂ n) :=
    AddMonoidHomClass.isometry_of_norm _ (KAM.norm_realInclusion₂)
  have hC : ContinuousOn (fun z : CPhase n => KAM.hamiltonianVectorFieldℂ G z) W := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine continuousOn_pi.2 fun i => ?_
      have hc := (ContinuousLinearMap.apply ℂ ℂ
        ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ))).continuous
      exact hc.comp_continuousOn hfd
    · refine continuousOn_pi.2 fun i => ?_
      have hc := (ContinuousLinearMap.apply ℂ ℂ
        ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ))).continuous
      exact (hc.comp_continuousOn hfd).neg
  have hind : Topology.IsInducing (KAM.realInclusion₂ n) := hiso.isEmbedding.isInducing
  rw [hind.continuousOn_iff]
  refine (hC.comp (KAM.realInclusion₂ n).continuous.continuousOn (fun z hz => hz)).congr ?_
  intro z hz
  exact KAM.hamiltonianVectorField_eq_of_real hW hG hreal hz (Eventually.of_forall fun _ => rfl)

end KAM.Planetary

end
