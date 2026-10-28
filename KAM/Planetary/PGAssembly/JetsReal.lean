/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.RealRestriction
public import KAM.Planetary.PGAssembly.JetsPolar

/-!
# P Part 5: complex jets at real vectors (`bpP:p5:be-jet`)

If `R` is complex analytic at `0` and agrees with `ofReal ∘ r` on real vectors near `0`, then the
complex iterated derivative of `R` at real vectors is the real iterated derivative of `r`
(`jet_real_restrict`). A complex multilinear map on `ℂᵇ × ℂᵇ` vanishing on all tuples of real
vectors is zero (`multilinear_eq_zero_of_real`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace KAM.Planetary

variable {b : ℕ}

/-- Local chain rule along a continuous linear map, with smoothness only at the image point. -/
theorem iteratedFDeriv_comp_clm_of_analyticAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace F]
    {f : E → F} (hf : AnalyticAt 𝕜 f 0) (g : G →L[𝕜] E) {i : ℕ} :
    iteratedFDeriv 𝕜 i (f ∘ g) 0 =
      (iteratedFDeriv 𝕜 i f 0).compContinuousLinearMap fun _ => g := by
  obtain ⟨U, hUa, hUo, hU0⟩ := eventually_nhds_iff.1 hf.eventually_analyticAt
  have hcd : ContDiffOn 𝕜 (i : ℕ∞) f U := fun x hx => (hUa x hx).contDiffAt.contDiffWithinAt
  have := iteratedFDeriv_comp_clm_of_isOpen hUo hcd g (x := 0) (by simpa using hU0) le_rfl
  simpa using this

theorem jet_real_restrict {R : (Fin b → ℂ) × (Fin b → ℂ) → ℂ}
    {r : (Fin b → ℝ) × (Fin b → ℝ) → ℝ} (hR : AnalyticAt ℂ R 0)
    (hr : ∀ᶠ y in 𝓝 (0 : (Fin b → ℝ) × (Fin b → ℝ)), R (KAM.realInclusion₂ b y) = (r y : ℂ))
    (k : ℕ) (v : Fin k → (Fin b → ℝ) × (Fin b → ℝ)) :
    iteratedFDeriv ℂ k R 0 (fun i => KAM.realInclusion₂ b (v i)) =
      ((iteratedFDeriv ℝ k r 0 v : ℝ) : ℂ) := by
  have hRr : AnalyticAt ℝ R 0 := hR.restrictScalars
  have hcomp : AnalyticAt ℝ (R ∘ KAM.realInclusion₂ b) 0 :=
    hRr.comp_of_eq ((KAM.realInclusion₂ b).analyticAt 0) (by simp)
  have hrre : r =ᶠ[𝓝 0] fun y => (R (KAM.realInclusion₂ b y)).re :=
    hr.mono fun y hy => by show r y = (R (KAM.realInclusion₂ b y)).re; rw [hy]; simp
  have hra : AnalyticAt ℝ r 0 :=
    (Complex.reCLM.analyticAt _ |>.comp hcomp).congr hrre.symm
  have h1 := iteratedFDeriv_comp_clm_of_analyticAt (𝕜 := ℝ) hRr (KAM.realInclusion₂ b) (i := k)
  have h2 : iteratedFDeriv ℝ k R 0 = (iteratedFDeriv ℂ k R 0).restrictScalars ℝ := by
    have := hR.contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (n := k)
    simpa using this.symm
  have h3 : iteratedFDeriv ℝ k (R ∘ KAM.realInclusion₂ b) 0 =
      iteratedFDeriv ℝ k (fun y => ((r y : ℝ) : ℂ)) 0 := by
    have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := univ) (n := k)
      (f₁ := R ∘ KAM.realInclusion₂ b) (f := fun y => ((r y : ℝ) : ℂ))
      (by rw [nhdsWithin_univ]; exact hr) (by simpa using hr.self_of_nhds)
    simpa [iteratedFDerivWithin_univ] using this
  have h4 : iteratedFDeriv ℝ k (fun y => ((r y : ℝ) : ℂ)) 0 =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ k r 0) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left hra.contDiffAt le_rfl
  have h5 := congrArg (fun M => M v) (h1.symm.trans (h3.trans h4))
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h5
  rw [h2] at h5
  simpa using h5

theorem multilinear_eq_zero_of_real {k : ℕ}
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin b → ℂ) × (Fin b → ℂ)) ℂ)
    (h : ∀ v : Fin k → (Fin b → ℝ) × (Fin b → ℝ),
      M (fun i => KAM.realInclusion₂ b (v i)) = 0) : M = 0 := by
  classical
  let e : Module.Basis (Fin b ⊕ Fin b) ℂ ((Fin b → ℂ) × (Fin b → ℂ)) :=
    (Pi.basisFun ℂ (Fin b)).prod (Pi.basisFun ℂ (Fin b))
  have he : ∀ s : Fin b ⊕ Fin b, e s = KAM.realInclusion₂ b
      (Sum.elim (fun i => (Pi.single i (1 : ℝ), (0 : Fin b → ℝ)))
        (fun i => ((0 : Fin b → ℝ), Pi.single i (1 : ℝ))) s) := by
    intro s
    rcases s with i | i
    · refine Prod.ext ?_ ?_
      · funext j
        by_cases hji : j = i <;> simp [e, hji]
      · simp [e]
    · refine Prod.ext ?_ ?_
      · simp [e]
      · funext j
        by_cases hji : j = i <;> simp [e, hji]
  have := Module.Basis.ext_multilinear (f := M.toMultilinearMap) (g := 0)
    (fun _ => e) (fun v => by
      simp only [he]
      exact h _)
  exact ContinuousMultilinearMap.toMultilinearMap_injective this

end KAM.Planetary

end
