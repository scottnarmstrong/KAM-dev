/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Resonant
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Strip.Bridges

/-!
# The complex Hessian bound of `resonant-prop2` (step `stepN:p7:p2-red`)

From the complex Hessian bound `‖D²h(I)v‖₂ ≤ M ‖v‖₂` on `V_r D` we derive

* `hessBound_of_complex`: the real `HessBound` of `Stability/Energy` on `U_r D`
  (`D²(Re h ∘ ι) = Re (D²h) ∘ ι`, `K:real-restriction`);
* `freqLipschitz_of_complex`: `(N2)` with `L = √n M` (`bpN:p6:lipschitz`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace KAM.Stability

open KAM.Weighted KAM.NormalForm
open KAM.Nekhoroshev (euclid realPart)

variable {n : ℕ}

private theorem realInclusion_mem_polyNbhd'' {D : Set (Fin n → ℝ)} {ϱ : ℝ} {I : Fin n → ℝ}
    (hI : I ∈ realNbhd D ϱ) : KAM.realInclusion n I ∈ polyNbhd (cpx D) ϱ := by
  obtain ⟨J', hJ', hlt⟩ := hI
  exact ⟨KAM.realInclusion n J', ⟨J', hJ', rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩

private theorem euclid_ofReal' (x : Fin n → ℝ) : euclid (fun i => (x i : ℂ)) = euclid x := by
  simp [euclid]

/-- `|L u| ≤ ‖u‖₂ ‖(L eᵢ)ᵢ‖₂` for a `ℂ`-linear form `L`. -/
theorem norm_apply_le_euclid (L : (Fin n → ℂ) →L[ℂ] ℂ) (u : Fin n → ℂ) :
    ‖L u‖ ≤ euclid u * euclid (fun i => L (Pi.single i 1)) := by
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin n → ℂ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖u i‖)
    (fun i => ‖L (Pi.single i 1)‖)
  simpa [euclid] using this

theorem contDiffOn_realPart {D : Set (Fin n → ℝ)} {r : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)) :
    ContDiffOn ℝ ∞ (realPart h) (realNbhd D r) := by
  have hU := isOpen_polyNbhd (cpx D) r
  have h1 : ContDiffOn ℝ ∞ h (polyNbhd (cpx D) r) :=
    ((KAM.holomorphic_regularity hU hh).2.2.1).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun J => h (KAM.realInclusion n J)) (realNbhd D r) :=
    h1.comp (KAM.realInclusion n).contDiff.contDiffOn
      (fun J hJ => realInclusion_mem_polyNbhd'' hJ)
  exact Complex.reCLM.contDiff.comp_contDiffOn h2

/-- The real derivative of `Re h ∘ ι` on `U_r D`. -/
theorem fderiv_realPart {D : Set (Fin n → ℝ)} {r : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)) {J : Fin n → ℝ} (hJ : J ∈ realNbhd D r)
    (e : Fin n → ℝ) :
    fderiv ℝ (realPart h) J e =
      (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n e)).re := by
  have hU := isOpen_polyNbhd (cpx D) r
  have hgd : DifferentiableAt ℂ h (KAM.realInclusion n J) :=
    hh.differentiableAt (hU.mem_nhds (realInclusion_mem_polyNbhd'' hJ))
  have h2 : HasFDerivAt (fun y => h (KAM.realInclusion n y))
      (((fderiv ℂ h (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n)) J :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp J (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt (realPart h) (Complex.reCLM.comp
      (((fderiv ℂ h (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n))) J :=
    Complex.reCLM.hasFDerivAt.comp J h2
  rw [h3.fderiv]
  rfl

/-- The complex Hessian bound gives the real `HessBound` on `U_r D`. -/
theorem hessBound_of_complex {D : Set (Fin n → ℝ)} {r M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hHess : ∀ I ∈ polyNbhd (cpx D) r, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v) :
    HessBound (realNbhd D r) h M := by
  intro I hI ξ η
  have hU := isOpen_polyNbhd (cpx D) r
  have hmem := realInclusion_mem_polyNbhd'' hI
  have hdf : DifferentiableOn ℂ (fderiv ℂ h) (polyNbhd (cpx D) r) :=
    (KAM.holomorphic_regularity hU hh).1
  have hDiff : DifferentiableAt ℝ (fderiv ℝ (realPart h)) I :=
    (((contDiffOn_realPart hh).fderiv_of_isOpen (isOpen_realNbhd D r) (m := 1) (by simp)
      ).differentiableOn one_ne_zero).differentiableAt ((isOpen_realNbhd D r).mem_nhds hI)
  have h1 : hessR (realPart h) I ξ η =
      fderiv ℝ (fun J => fderiv ℝ (realPart h) J η) I ξ := by
    unfold hessR
    rw [fderiv_clm_apply hDiff (differentiableAt_const _)]
    simp
  have hev : (fun J => fderiv ℝ (realPart h) J η) =ᶠ[𝓝 I]
      fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n η)).re := by
    filter_upwards [(isOpen_realNbhd D r).mem_nhds hI] with J hJ
    exact fderiv_realPart hh hJ η
  have hG : DifferentiableAt ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n η))
      (KAM.realInclusion n I) :=
    (hdf.clm_apply (differentiableOn_const _)).differentiableAt (hU.mem_nhds hmem)
  have h2 := (hG.hasFDerivAt.restrictScalars ℝ).comp I (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt
      (fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n η)).re)
      (Complex.reCLM.comp (((fderiv ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n η))
        (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n))) I :=
    Complex.reCLM.hasFDerivAt.comp I h2
  rw [h1, hev.fderiv_eq, h3.fderiv]
  set L := fderiv ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n η)) (KAM.realInclusion n I)
    with hL
  have hb := norm_apply_le_euclid L (KAM.realInclusion n ξ)
  have hw := hHess _ hmem (KAM.realInclusion n η)
  have e1 : euclid (KAM.realInclusion n ξ) = euclid ξ := euclid_ofReal' ξ
  have e2 : euclid (KAM.realInclusion n η) = euclid η := euclid_ofReal' η
  rw [e2] at hw
  have hξ : 0 ≤ euclid ξ := Real.sqrt_nonneg _
  calc |((Complex.reCLM.comp (((L).restrictScalars ℝ).comp (KAM.realInclusion n))) ξ)|
      = |(L (KAM.realInclusion n ξ)).re| := rfl
    _ ≤ ‖L (KAM.realInclusion n ξ)‖ := Complex.abs_re_le_norm _
    _ ≤ euclid ξ * (M * euclid η) := by
        refine hb.trans ?_
        rw [e1]
        exact mul_le_mul_of_nonneg_left hw hξ
    _ = M * euclid ξ * euclid η := by ring

/-- The complex Hessian bound gives `(N2)` with `L = √n M`. -/
theorem freqLipschitz_of_complex {D : Set (Fin n → ℝ)} {r M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hM : 0 ≤ M) (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hHess : ∀ I ∈ polyNbhd (cpx D) r, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v) :
    FreqLipschitz (cpx D) r (Real.sqrt n * M) h := by
  refine lipschitz hh fun I hI => ?_
  have hU := isOpen_polyNbhd (cpx D) r
  have hfd : DifferentiableAt ℂ (freq h) I := differentiableAt_freq hU hh hI
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hcomp : ∀ j, fderiv ℂ (freq h) I v j =
      fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single j 1) := by
    intro j
    rw [fderiv_pi (fun i => (differentiableAt_pi.1 hfd) i)]
    exact (KAM.fderiv_apply_comm_of_differentiableOn hU hh hI v (Pi.single j 1))
  have hvec : fderiv ℂ (freq h) I v =
      fun j => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single j 1) := funext hcomp
  rw [hvec]
  have hv := KAM.Nekhoroshev.norm_le_euclid v
  calc ‖fun j => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single j 1)‖
      ≤ euclid (fun j => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single j 1)) :=
        (KAM.Nekhoroshev.norm_le_euclid _).1
    _ ≤ M * euclid v := hHess I hI v
    _ ≤ M * (Real.sqrt n * ‖v‖) := mul_le_mul_of_nonneg_left hv.2.1 hM
    _ = Real.sqrt n * M * ‖v‖ := by ring

end KAM.Stability

end
