/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.FourierSeries
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Planetary.PGAssembly.ExtensionExists

/-!
# P Part 5: strip estimates for an extension (`bpP:p5:consts`, helpers)

For any `E : PGExtension d`: complex angle strips over the thin domain, periodicity of the angle
slices, and the weighted Fourier bound from `KAM.summableWeighted_torusCoeff`. Also the real
attachment `assembleComplex ∘ ι = ι₂ ∘ assemble`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

theorem assembleComplex_real (I phi : Fin a → ℝ) (p q : Fin b → ℝ) :
    assembleComplex (KAM.realInclusion a I) (KAM.realInclusion a phi) (KAM.realInclusion b p)
      (KAM.realInclusion b q) = KAM.realInclusion₂ (a + b) (assemble I phi p q) := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [assembleComplex, assemble]

theorem strip_mem_extensionDomain (d : PGData a b) {delta : ℝ} (hdelta : 0 < delta)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) (delta / 2))
    {x : PGComplexPhase b} (hx : ‖x‖ < delta / 4) {θ : Fin a → ℂ}
    (hθ : θ ∈ KAM.complexStrip a (delta / (2 * Real.pi))) :
    assembleComplex I ((2 * Real.pi : ℂ) • θ) x.2 x.1 ∈ extensionDomain d delta := by
  obtain ⟨J, hJ, hIJ⟩ := mem_actionNbhd_iff.1 hI
  have hpi := Real.pi_pos
  refine ⟨assemble J (fun j => 2 * Real.pi * (θ j).re) 0 0, ?_, ?_, ?_⟩
  · show blockFast (Fin.append J (0 : Fin b → ℝ)) ∈ closure d.V
    rw [show blockFast (Fin.append J (0 : Fin b → ℝ)) = J from
      funext fun i => Fin.append_left _ _ i]
    exact hJ
  · have h : ∀ u : Fin a → ℝ, blockSlow (Fin.append u (0 : Fin b → ℝ)) = 0 := fun u =>
      funext fun i => Fin.append_right _ _ i
    show ‖(blockSlow (Fin.append J (0 : Fin b → ℝ)),
      blockSlow (Fin.append (fun j => 2 * Real.pi * (θ j).re) (0 : Fin b → ℝ)))‖ ≤ d.r0 / 2
    rw [h, h, Prod.norm_def]
    simp only [norm_zero, max_self]
    linarith [d.hr0]
  · rw [Prod.norm_def]
    have hx1 : ∀ j, ‖x.1 j‖ < delta / 4 := fun j =>
      (norm_le_pi_norm x.1 j).trans_lt
        ((le_max_left _ _).trans_lt (by simpa [Prod.norm_def] using hx))
    have hx2 : ∀ j, ‖x.2 j‖ < delta / 4 := fun j =>
      (norm_le_pi_norm x.2 j).trans_lt
        ((le_max_right _ _).trans_lt (by simpa [Prod.norm_def] using hx))
    refine max_lt ?_ ?_
    · refine (pi_norm_lt_iff hdelta).2 fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [assembleComplex, KAM.realInclusion₂_apply, assemble, Pi.sub_apply, Prod.fst_sub,
          Fin.append_left, KAM.realInclusion_apply]
        have h1 : ((2 * Real.pi : ℂ) • θ) i - ((2 * Real.pi * (θ i).re : ℝ) : ℂ) =
            ((2 * Real.pi : ℝ) : ℂ) * ((θ i).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [h1]
        have := hθ i
        rw [lt_div_iff₀ (by positivity)] at this
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [mul_comm]; exact this
      · simp only [assembleComplex, KAM.realInclusion₂_apply, assemble, Pi.sub_apply,
          Prod.fst_sub, Fin.append_right, KAM.realInclusion_apply, Pi.zero_apply]
        simp only [Complex.ofReal_zero, sub_zero]
        linarith [hx1 i]
    · refine (pi_norm_lt_iff hdelta).2 fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [assembleComplex, KAM.realInclusion₂_apply, assemble, Pi.sub_apply,
          Prod.snd_sub, Fin.append_left, KAM.realInclusion_apply]
        have : ‖I i - (J i : ℂ)‖ < delta / 2 :=
          (norm_le_pi_norm (I - KAM.realInclusion a J) i).trans_lt hIJ
        linarith
      · simp only [assembleComplex, KAM.realInclusion₂_apply, assemble, Pi.sub_apply,
          Prod.snd_sub, Fin.append_right, KAM.realInclusion_apply, Pi.zero_apply]
        simp only [Complex.ofReal_zero, sub_zero]
        linarith [hx2 i]

theorem differentiable_assembleComplex_smul (I : Fin a → ℂ) (p q : Fin b → ℂ) :
    Differentiable ℂ fun θ : Fin a → ℂ => assembleComplex I ((2 * Real.pi : ℂ) • θ) p q := by
  refine Differentiable.prodMk (differentiable_pi.2 fun j => ?_)
    (differentiable_pi.2 fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left, Pi.smul_apply, smul_eq_mul]; fun_prop
    · simp only [Fin.append_right]; fun_prop
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem assembleComplex_shift (I : Fin a → ℂ) (p q : Fin b → ℂ) (θ : Fin a → ℂ) (i : Fin a) :
    assembleComplex I ((2 * Real.pi : ℂ) • (θ + Pi.single i 1)) p q =
      assembleComplex I ((2 * Real.pi : ℂ) • θ) p q +
        KAM.realInclusion₂ (a + b) (fastShift (Pi.single i (1 : ℤ))) := by
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · by_cases hk : k = i <;>
        simp [assembleComplex, fastShift, hk, Pi.single_apply]
    · simp [assembleComplex, fastShift]
  · funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [assembleComplex, fastShift]

variable {d : PGData a b}

theorem PGExtension.angle_periodic (E : PGExtension d) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) (E.delta / 2))
    {x : PGComplexPhase b} (hx : ‖x‖ < E.delta / 4) (i : Fin a) {θ : Fin a → ℂ}
    (hθ : θ ∈ KAM.complexStrip a (E.delta / (2 * Real.pi))) :
    E.P mu (assembleComplex I ((2 * Real.pi : ℂ) • (θ + Pi.single i 1)) x.2 x.1) =
      E.P mu (assembleComplex I ((2 * Real.pi : ℂ) • θ) x.2 x.1) := by
  rw [assembleComplex_shift]
  exact E.periodic mu hmu _ (strip_mem_extensionDomain d E.delta_pos hI hx hθ) _

theorem PGExtension.summable_torus (E : PGExtension d) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) (E.delta / 2))
    {x : PGComplexPhase b} (hx : ‖x‖ < E.delta / 4) :
    KAM.Fourier.SummableWeighted (E.delta / 2)
      (KAM.torusCoeff (fun phi => E.P mu
        (assembleComplex I ((2 * Real.pi : ℂ) • KAM.realInclusion a phi) x.2 x.1))) ∧
    KAM.Fourier.weightedNorm (E.delta / 2)
      (KAM.torusCoeff (fun phi => E.P mu
        (assembleComplex I ((2 * Real.pi : ℂ) • KAM.realInclusion a phi) x.2 x.1))) ≤
      (Real.cosh (Real.pi * (E.delta / (4 * Real.pi))) /
        Real.sinh (Real.pi * (E.delta / (4 * Real.pi)))) ^ a * E.MP := by
  have hpi := Real.pi_pos
  have hd := E.delta_pos
  have hmem : ∀ θ ∈ KAM.complexStrip a (E.delta / (2 * Real.pi)),
      assembleComplex I ((2 * Real.pi : ℂ) • θ) x.2 x.1 ∈ extensionDomain d E.delta :=
    fun θ hθ => strip_mem_extensionDomain d hd hI hx hθ
  have key := KAM.summableWeighted_torusCoeff (n := a) (ρ := E.delta / (2 * Real.pi))
    (δ := E.delta / (4 * Real.pi)) (A := E.MP) (by positivity)
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    (u := fun θ : Fin a → ℂ => E.P mu (assembleComplex I ((2 * Real.pi : ℂ) • θ) x.2 x.1))
    ((E.holo mu hmu).comp (differentiable_assembleComplex_smul I x.2 x.1).differentiableOn hmem)
    (fun i θ hθ => E.angle_periodic hmu hI hx i hθ)
    (fun θ hθ => E.bound mu hmu _ (hmem θ hθ))
  have hw : 2 * Real.pi * (E.delta / (2 * Real.pi) - E.delta / (4 * Real.pi)) = E.delta / 2 := by
    field_simp; ring
  rw [hw] at key
  exact key

end KAM.Planetary

end
