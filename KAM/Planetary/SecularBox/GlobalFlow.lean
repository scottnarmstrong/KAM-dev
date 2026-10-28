/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularBox.SlowFlow

/-!
# The global solution of the full secular system

Blueprint `bpP:p14:sb-global` (steps `sb-gl-1`..`sb-gl-3`).

* `angle_quadrature`: two-sided FTC for the fast angles, `λ(t) = ∫₀ᵗ ω`.
* `sb_global`: the slow flow of `sb_slow` is completed by the quadrature of `ω` to a global
  solution of the frozen Hamiltonian predicate with constant fast actions and AMD.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
open KAM.Kepler

namespace KAM.Planetary

theorem angle_quadrature {omega : ℝ → (Fin 2 → ℝ)}
    (h : Continuous omega) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, omega s) (omega t) t :=
  intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 t)
    (h.stronglyMeasurableAtFilter MeasureTheory.volume _) h.continuousAt

private theorem sbGlobal_eta {a b : ℕ} (w : Phase (a+b)) :
    assemble (fast w.2) (fast w.1) (slow w.2) (slow w.1) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp [assemble, fast, slow]

/-- Membership in `S` depends only on the fast actions and the slow coordinates. -/
private theorem sbGlobal_mem_congr (saturn : ℝ) {a b : Phase (2+2)} (h2 : fast a.2 = fast b.2)
    (h3 : slow a.1 = slow b.1) (h4 : slow a.2 = slow b.2) :
    a ∈ sb_sdef saturn ↔ b ∈ sb_sdef saturn := by
  simp only [sb_sdef, mem_ofPred_eq, secularAxis, secularGamma, oscillatorAction, h2, h3, h4]

private theorem sbGlobal_amd_congr {a b : Phase (2+2)} (h3 : slow a.1 = slow b.1)
    (h4 : slow a.2 = slow b.2) : secularAMD a = secularAMD b := by
  simp only [secularAMD, secularGamma, oscillatorAction, h3, h4]

/-- The fast-angle translation. -/
private def sbGlobalShift (c : Fin 2 → ℝ) : Phase (2+2) := (Fin.append c 0, 0)

private theorem sbGlobal_add_shift (z : Phase (2+2)) (c : Fin 2 → ℝ) :
    z + sbGlobalShift c = assemble (fast z.2) (fast z.1 + c) (slow z.2) (slow z.1) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
    simp only [assemble, sbGlobalShift, fast, slow, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Fin.append_left, Fin.append_right, Pi.zero_apply, add_zero]

private theorem sbGlobal_assemble_shift (I lam : Fin 2 → ℝ) (p q : Fin 2 → ℝ) :
    assemble I lam p q = assemble I 0 p q + sbGlobalShift lam := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
    simp only [assemble, sbGlobalShift, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Fin.append_left, Fin.append_right, Pi.zero_apply, add_zero, zero_add]

/-- `ω` does not depend on the fast angles. -/
private theorem sbGlobal_omega_lam (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    (I lam p q : Fin 2 → ℝ) :
    sb_omega (jupiterSaturnWeights saturn) mu (assemble I lam p q) =
      sb_omega (jupiterSaturnWeights saturn) mu (assemble I 0 p q) := by
  have hH : (fun z => exactSecularHamiltonian (jupiterSaturnWeights saturn) mu
      (z + sbGlobalShift lam)) = exactSecularHamiltonian (jupiterSaturnWeights saturn) mu := by
    funext z
    rw [sbGlobal_add_shift]
    exact (sb_smooth_prop saturn mu hs).2.2 z _ |>.trans rfl
  have hf : fderiv ℝ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
      (assemble I 0 p q + sbGlobalShift lam) =
      fderiv ℝ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (assemble I 0 p q) := by
    rw [← fderiv_comp_add_right, hH]
  rw [sbGlobal_assemble_shift]
  funext i
  simp only [sb_omega, hf]

private theorem sbGlobal_omega_cont (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ContinuousOn (sb_omega (jupiterSaturnWeights saturn) mu) (sb_sdef saturn) := by
  have hc := (sb_smooth_prop saturn mu hs).1.continuousOn_fderiv_of_isOpen
    (sb_s saturn hs).1 (by simp)
  refine continuousOn_pi.2 fun i => ?_
  exact (ContinuousLinearMap.apply ℝ ℝ
    ((0, Fin.append (Pi.single i 1) 0) : Phase (2+2))).continuous.comp_continuousOn hc

theorem sb_global (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w0 : Phase (2+2)} (hw : w0 ∈ sb_sdef saturn)
    (hA : secularAMD w0 < (16373/2500000 : ℝ)) (hI : ∀ i, (87/100 : ℝ) < fast w0.2 i) :
    ∃ w : ℝ → Phase (2+2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn
        (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ univ w ∧
      ∀ t, w t ∈ sb_sdef saturn ∧ fast (w t).2 = fast w0.2 ∧
        secularAMD (w t) = secularAMD w0 := by
  obtain ⟨y, hy0, hy, hyA⟩ := sb_slow saturn mu hs hw hA hI
  set I := fast w0.2 with hIdef
  set H := exactSecularHamiltonian (jupiterSaturnWeights saturn) mu with hHdef
  have hyc : Continuous y := continuous_iff_continuousAt.2
    fun t => (hy t (mem_univ t)).2.continuousAt
  have hgc : Continuous fun t => assemble I 0 (y t).2 (y t).1 := by
    unfold assemble
    refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun k => ?_) <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop
  -- `sb-gl-1`
  have hωc : Continuous fun t => sb_omega (jupiterSaturnWeights saturn) mu
      (assemble I 0 (y t).2 (y t).1) :=
    (sbGlobal_omega_cont saturn mu hs).comp_continuous hgc fun t => (hy t (mem_univ t)).1
  have hq := angle_quadrature hωc
  set lam : ℝ → Fin 2 → ℝ := fun t => fast w0.1 + ∫ s in (0 : ℝ)..t,
    sb_omega (jupiterSaturnWeights saturn) mu (assemble I 0 (y s).2 (y s).1) with hlam
  have hlamd : ∀ t, HasDerivAt lam (sb_omega (jupiterSaturnWeights saturn) mu
      (assemble I 0 (y t).2 (y t).1)) t := fun t => (hq t).const_add (fast w0.1)
  -- `sb-gl-2`
  set w : ℝ → Phase (2+2) := fun t => assemble I (lam t) (y t).2 (y t).1 with hwdef
  have hfast : ∀ t, fast (w t).2 = I := fun t => by funext i; simp [hwdef, assemble, fast]
  have hs1 : ∀ t, slow (w t).1 = (y t).1 := fun t => funext fun i => Fin.append_right _ _ i
  have hs2 : ∀ t, slow (w t).2 = (y t).2 := fun t => funext fun i => Fin.append_right _ _ i
  have hg : ∀ t, assemble I 0 (y t).2 (y t).1 ∈ sb_sdef saturn := fun t => (hy t (mem_univ t)).1
  have hwS : ∀ t, w t ∈ sb_sdef saturn := fun t => by
    refine (sbGlobal_mem_congr saturn (b := assemble I 0 (y t).2 (y t).1) ?_ ?_ ?_).2 (hg t)
    · rw [hfast]; funext i; simp [assemble, fast]
    · rw [hs1]; exact funext fun i => (Fin.append_right _ _ i).symm
    · rw [hs2]; exact funext fun i => (Fin.append_right _ _ i).symm
  have hw0 : w 0 = w0 := by
    simp only [hwdef, hlam, hy0, intervalIntegral.integral_same, add_zero]
    exact sbGlobal_eta w0
  refine ⟨w, hw0, fun t _ => ⟨mem_univ _, ?_, ?_⟩, fun t => ⟨hwS t, hfast t, ?_⟩⟩
  · exact (sb_smooth_prop saturn mu hs).1.differentiableOn (by simp) _ (hwS t) |>.differentiableAt
      ((sb_s saturn hs).1.mem_nhds (hwS t))
  · -- `sb-gl-3`
    obtain ⟨hf1, -⟩ := sb_field saturn mu hs (hwS t)
    obtain ⟨hc1, hc2⟩ := secular_field_components saturn mu hs (hwS t)
    rw [hfast t, hs1 t, hs2 t] at hc2
    have hyd := (hy t (mem_univ t)).2
    rw [← hc2] at hyd
    refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun k => ?_) (hasDerivAt_pi.2 fun k => ?_) <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · have := (hasDerivAt_pi.1 (hlamd t)) j
      have h2 : sb_omega (jupiterSaturnWeights saturn) mu (w t) =
          sb_omega (jupiterSaturnWeights saturn) mu (assemble I 0 (y t).2 (y t).1) :=
        sbGlobal_omega_lam saturn mu hs _ _ _ _
      have e : sb_omega (jupiterSaturnWeights saturn) mu (assemble I 0 (y t).2 (y t).1) j =
          (KAM.hamiltonianVectorField H (w t)).1 (Fin.castAdd 2 j) := by
        rw [← h2]; exact (congrFun hc1 j).symm
      exact (this.congr_deriv e).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x => Fin.append_left _ _ j)
    · have := hasDerivAt_pi.1 hyd.fst j
      exact this.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x => Fin.append_right _ _ j)
    · have h3 : (KAM.hamiltonianVectorField H (w t)).2 (Fin.castAdd 2 j) = 0 := congrFun hf1 j
      exact ((hasDerivAt_const t (I j)).congr_deriv h3.symm).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x => Fin.append_left _ _ j)
    · have := hasDerivAt_pi.1 hyd.snd j
      exact this.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x => Fin.append_right _ _ j)
  · rw [← hyA t]
    refine sbGlobal_amd_congr ?_ ?_
    · rw [hs1]; exact funext fun i => (Fin.append_right _ _ i).symm
    · rw [hs2]; exact funext fun i => (Fin.append_right _ _ i).symm

end KAM.Planetary

end
