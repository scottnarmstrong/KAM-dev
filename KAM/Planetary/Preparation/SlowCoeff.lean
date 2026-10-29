/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Measure.Lipschitz
public import KAM.Planetary.Preparation.SlowAverage

/-!
# Slow averaging: the zero angle-mode of `f₂` (P11A-P7d)

`p11_slow_coeff_zero`: for any `h₀`, `f₂` satisfying the fast identity and the polar-average
formula of `h₀` (clauses 1-2 of `P11SlowSpecOf`), the zero Fourier mode of `f₂` in the `2n`
angles is the zero mode of `f₁ ∘ Π`, hence of size `(ε M_F)³`: the polar average of `G ∘ Π`
cancels the `ε 𝒜 G` term of `h₀` exactly.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators
namespace KAM.Planetary

section Coeff

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Averaging over the `2n`-torus a function of the last `n` angles only. -/
theorem p11_torusAverage_natAdd (g : (Fin n → ℝ) → ℂ) :
    KAM.torusAverage (fun x : Fin (n + n) → ℝ => g (fun i => x (Fin.natAdd n i))) =
      KAM.torusAverage g := by
  unfold KAM.torusAverage
  have hp := KAM.measurePreserving_appendMeasurableEquiv n
  have hpre : (KAM.appendMeasurableEquiv n) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin (n + n) => Icc (0 : ℝ) 1)) =
      Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ×ˢ
        Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) := by
    ext p
    simp only [mem_preimage, KAM.appendMeasurableEquiv_apply, mem_pi, mem_univ, true_implies,
      mem_prod, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  rw [← hp.setIntegral_preimage_emb (KAM.appendMeasurableEquiv n).measurableEmbedding, hpre]
  have h2 : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (fun i => (KAM.appendMeasurableEquiv n p) (Fin.natAdd n i))) = fun p => g p.2 := by
    funext p
    simp [KAM.appendMeasurableEquiv_apply]
  rw [h2, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_snd]
  simp [Measure.real, Measure.restrict_apply, KAM.volume_unitCube]

end Coeff

end KAM.Planetary

end
