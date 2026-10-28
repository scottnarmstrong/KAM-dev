/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Basic

/-!
# Secular spectrum: analyticity of the lift

Blueprint P, Part 9 (`bpP:p9:lift`): `liftMap R` and `liftInv R` are real analytic on
`liftDomain W` when `R` is real analytic on the open set `W`.  The inverse is `liftMap` of the
transposed rotation, which also gives its symplecticity from that of `liftMap`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Analytic

lemma analyticAt_assemble {z : Phase (n+n)} {I φ p q : Phase (n+n) → Vec n}
    (hI : AnalyticAt ℝ I z) (hφ : AnalyticAt ℝ φ z) (hp : AnalyticAt ℝ p z)
    (hq : AnalyticAt ℝ q z) :
    AnalyticAt ℝ (fun w => assemble (I w) (φ w) (p w) (q w)) z := by
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun k => ?_) (analyticAt_pi_iff.2 fun k => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp only [Fin.append_left, Fin.append_right]
    · exact analyticAt_pi_iff.1 hφ j
    · exact analyticAt_pi_iff.1 hq j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp only [Fin.append_left, Fin.append_right]
    · exact analyticAt_pi_iff.1 hI j
    · exact analyticAt_pi_iff.1 hp j

lemma analyticAt_fast_snd (z : Phase (n+n)) : AnalyticAt ℝ (fun w : Phase (n+n) => fast w.2) z :=
  analyticAt_pi_iff.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+n) => ℝ) (Fin.castAdd n i)).comp
      (ContinuousLinearMap.snd ℝ (Fin (n+n) → ℝ) (Fin (n+n) → ℝ))).analyticAt z

lemma analyticAt_fast_fst (z : Phase (n+n)) : AnalyticAt ℝ (fun w : Phase (n+n) => fast w.1) z :=
  analyticAt_pi_iff.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+n) => ℝ) (Fin.castAdd n i)).comp
      (ContinuousLinearMap.fst ℝ (Fin (n+n) → ℝ) (Fin (n+n) → ℝ))).analyticAt z

lemma analyticAt_slow_snd (z : Phase (n+n)) : AnalyticAt ℝ (fun w : Phase (n+n) => slow w.2) z :=
  analyticAt_pi_iff.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+n) => ℝ) (Fin.natAdd n i)).comp
      (ContinuousLinearMap.snd ℝ (Fin (n+n) → ℝ) (Fin (n+n) → ℝ))).analyticAt z

lemma analyticAt_slow_fst (z : Phase (n+n)) : AnalyticAt ℝ (fun w : Phase (n+n) => slow w.1) z :=
  analyticAt_pi_iff.2 fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+n) => ℝ) (Fin.natAdd n i)).comp
      (ContinuousLinearMap.fst ℝ (Fin (n+n) → ℝ) (Fin (n+n) → ℝ))).analyticAt z

lemma analyticAt_matrix_entry {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {M : α → Mat n} {x : α} (h : AnalyticAt ℝ M x) (a b : Fin n) :
    AnalyticAt ℝ (fun y => M y a b) x :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h a) b

lemma fderiv_entry {R : Vec n → Mat n} {I : Vec n} (hR : DifferentiableAt ℝ R I) (v : Vec n)
    (a b : Fin n) : fderiv ℝ R I v a b = fderiv ℝ (fun J => R J a b) I v := by
  have h1 : DifferentiableAt ℝ (fun J => R J a) I :=
    differentiableAt_pi.1 (show DifferentiableAt ℝ (fun J => (R J : Fin n → Fin n → ℝ)) I from hR) a
  have e1 := fderiv_apply (𝕜 := ℝ) (Φ := fun J => (R J : Fin n → Fin n → ℝ)) hR a
  have e2 := fderiv_apply (𝕜 := ℝ) (Φ := fun J => R J a) h1 b
  rw [e2, e1]
  rfl

lemma analyticAt_fderiv_apply {f : Vec n → ℝ} {x : Vec n} (h : AnalyticAt ℝ f x) (v : Vec n) :
    AnalyticAt ℝ (fun J => fderiv ℝ f J v) x :=
  AnalyticAt.comp (g := fun L : Vec n →L[ℝ] ℝ => L v) (f := fderiv ℝ f)
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _) h.fderiv

lemma isOpen_liftDomain {W : Set (Vec n)} (hW : IsOpen W) : IsOpen (liftDomain W) :=
  hW.preimage ((continuous_pi fun _ => (continuous_apply _).comp continuous_snd))

lemma analyticAt_liftMap {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) {z : Phase (n+n)} (hz : z ∈ liftDomain W) :
    AnalyticAt ℝ (liftMap R) z := by
  have hI := analyticAt_fast_snd z
  have hR : AnalyticAt ℝ (fun w : Phase (n+n) => R (fast w.2)) z :=
    AnalyticAt.comp (f := fun w : Phase (n+n) => fast w.2) (hAn _ hz) hI
  have hDe : ∀ l a b, AnalyticAt ℝ
      (fun w : Phase (n+n) => fderiv ℝ R (fast w.2) (Pi.single l 1) a b) z := by
    intro l a b
    have hopen : IsOpen (liftDomain W) := isOpen_liftDomain hW
    have h1 : AnalyticAt ℝ (fun w : Phase (n+n) =>
        fderiv ℝ (fun J => R J a b) (fast w.2) (Pi.single l 1)) z :=
      AnalyticAt.comp (f := fun w : Phase (n+n) => fast w.2)
        (analyticAt_fderiv_apply (analyticAt_matrix_entry (hAn _ hz) a b) _) hI
    refine h1.congr ?_
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (fderiv_entry (hAn _ hw).differentiableAt _ a b).symm
  have hRe : ∀ a b, AnalyticAt ℝ (fun w : Phase (n+n) => R (fast w.2) a b) z :=
    fun a b => analyticAt_matrix_entry hR a b
  have hξ := fun i => analyticAt_pi_iff.1 (analyticAt_slow_fst z) i
  have hη := fun i => analyticAt_pi_iff.1 (analyticAt_slow_snd z) i
  have hθ := fun i => analyticAt_pi_iff.1 (analyticAt_fast_fst z) i
  unfold liftMap
  refine analyticAt_assemble hI (analyticAt_pi_iff.2 fun l => ?_)
    (analyticAt_pi_iff.2 fun k => ?_) (analyticAt_pi_iff.2 fun k => ?_)
  · simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    exact (hθ l).sub (Finset.analyticAt_fun_sum _ fun i _ => (hη i).fun_mul
      (Finset.analyticAt_fun_sum _ fun j _ => (Finset.analyticAt_fun_sum _ fun m _ =>
        (hDe l i m).fun_mul (hRe j m)).fun_mul (hξ j)))
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hRe i k).fun_mul (hη i)
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hRe i k).fun_mul (hξ i)

end Analytic

end SecularSpectrum

end KAM.Planetary

end
