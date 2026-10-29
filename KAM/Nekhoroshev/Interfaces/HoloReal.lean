/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Strip.Bridges
public import KAM.Strip.RealRestriction
public import KAM.ODE.Basic
public import KAM.Nekhoroshev.Interfaces.Domains
public import KAM.Nekhoroshev.Interfaces.Setting

/-!
# Holomorphy gives a real Hamiltonian (`bpN:p1:holo-real`, `bpN:p3:holo-input`)

For `G(θ, I) = h(I) + f(θ, I)`, `H = KAM.realHamiltonian h f` and `ι = KAM.realInclusion₂ n`:

* `holo_real_a`: `G` and `h` are holomorphic and `C^∞` on their complex domains;
* `holo_real_b`: `H` and `h_ℝ` are `C^∞` and real, `H = Re (G ∘ ι)`, and `D^k H = D^k G ∘ ι` at
  every order (the real iterated derivative is the complex one on real arguments);
* `holo_real_c`: `ι X_H = X_G ∘ ι`, the frequency map and the (symmetric) Hessian of `h_ℝ`;
* `holo_real_d`: `H`, `DH`, `D^k H` and `X_H` are periodic in `θ` on `W_s`;
* `holo_real_e`: `ε = 0` forces `f = 0` and `H = h_ℝ ∘ snd`;
* `holo_input`: the corollary Part 3 consumes (`bpN:p3:holo-input`).
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-! ### Generic transfer from complex to real iterated derivatives -/

section Generic

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedSpace ℝ E₂] [IsScalarTower ℝ ℂ E₂]

/-- If `G` is `C^∞` (complex) on the open `U`, `ι` is real linear, and `H` is the real function
with `G ∘ ι = H` on the open `V` (`ι V ⊆ U`), then `D^k H z ζ = D^k G (ι z) (ι ∘ ζ)`. -/
private theorem iteratedFDeriv_real_eq_complex (ι : E₁ →L[ℝ] E₂) {U : Set E₂} (hU : IsOpen U)
    {G : E₂ → ℂ} (hG : ContDiffOn ℂ ∞ G U) {V : Set E₁} (hV : IsOpen V)
    (hVU : ∀ z ∈ V, ι z ∈ U) {H : E₁ → ℝ} (hH : ∀ z ∈ V, G (ι z) = (H z : ℂ)) (k : ℕ)
    {z : E₁} (hz : z ∈ V) (ζ : Fin k → E₁) :
    ((iteratedFDeriv ℝ k H z ζ : ℝ) : ℂ) = iteratedFDeriv ℂ k G (ι z) (fun j => ι (ζ j)) := by
  have hk : ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hGr : ContDiffOn ℝ ∞ G U := hG.restrict_scalars ℝ
  have hg : ContDiffOn ℝ ∞ (G ∘ ι) V := hGr.comp ι.contDiff.contDiffOn hVU
  have hHg : (fun y => H y) =ᶠ[𝓝 z] fun y => Complex.reCLM (G (ι y)) := by
    filter_upwards [hV.mem_nhds hz] with y hy
    rw [hH y hy]
    simp
  have hCD : ContDiffAt ℝ k H z :=
    (Complex.reCLM.contDiff.contDiffAt.comp z
      ((hg.contDiffAt (hV.mem_nhds hz)).of_le hk)).congr_of_eventuallyEq hHg
  have heq : (G ∘ ι) =ᶠ[𝓝 z] (Complex.ofRealCLM ∘ H) := by
    filter_upwards [hV.mem_nhds hz] with y hy
    simpa using hH y hy
  have h2 : iteratedFDeriv ℝ k (G ∘ ι) z = iteratedFDeriv ℝ k (Complex.ofRealCLM ∘ H) z :=
    (heq.iteratedFDeriv ℝ k).self_of_nhds
  have h3 : iteratedFDeriv ℝ k (Complex.ofRealCLM ∘ H) z =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ k H z) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left hCD le_rfl
  have hιU : ι ⁻¹' U ∈ 𝓝 z := (hU.preimage ι.continuous).mem_nhds (hVU z hz)
  have h4 : iteratedFDeriv ℝ k (G ∘ ι) z =
      (iteratedFDeriv ℝ k G (ι z)).compContinuousLinearMap fun _ => ι := by
    have := ι.iteratedFDerivWithin_comp_right (i := k) (hGr.of_le hk) hU.uniqueDiffOn
      (hU.preimage ι.continuous).uniqueDiffOn (hVU z hz) (by exact_mod_cast le_rfl)
    rwa [iteratedFDerivWithin_of_isOpen k (hU.preimage ι.continuous) (hVU z hz),
      iteratedFDerivWithin_of_isOpen k hU (hVU z hz)] at this
  have h5 : iteratedFDeriv ℝ k G (ι z) = (iteratedFDeriv ℂ k G (ι z)).restrictScalars ℝ :=
    ((hG.contDiffAt (hU.mem_nhds (hVU z hz))).of_le hk).restrictScalars_iteratedFDeriv.symm
  calc ((iteratedFDeriv ℝ k H z ζ : ℝ) : ℂ)
      = (Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ k H z)) ζ := rfl
    _ = iteratedFDeriv ℝ k (G ∘ ι) z ζ := by rw [← h3, ← h2]
    _ = iteratedFDeriv ℝ k G (ι z) (fun j => ι (ζ j)) := by rw [h4]; rfl
    _ = iteratedFDeriv ℂ k G (ι z) (fun j => ι (ζ j)) := by rw [h5]; rfl

end Generic

/-! ### Holomorphy and reality on the real points -/

section Helpers

variable {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

private theorem differentiableOn_G (hd : Data n R s ε h f) :
    DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w)
      (complexDomain n R s) :=
  (hd.hh.1.comp differentiableOn_snd (fun _ hw => hw.2)).add hd.hf.2.1

private theorem contDiffOn_G (hd : Data n R s ε h f) :
    ContDiffOn ℂ ∞ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w) (complexDomain n R s) :=
  (KAM.holomorphic_regularity_of_finiteDimensional (isOpen_complexDomain R s)
    (differentiableOn_G hd)).2.2.1

private theorem contDiffOn_h (hd : Data n R s ε h f) :
    ContDiffOn ℂ ∞ h (KAM.actionNbhd (actionBall n R) s) :=
  (KAM.holomorphic_regularity_of_finiteDimensional (isOpen_actionNbhd_ball R s) hd.hh.1).2.2.1

private theorem mem_complexDomain_of_mem_Wdom (hd : Data n R s ε h f)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ Wdom n R s) :
    KAM.realInclusion₂ n z ∈ complexDomain n R s := by
  rw [← realInclusion₂_preimage_complexDomain hd.hR hd.hs] at hz
  exact hz

private theorem mem_Wdom_of_mem_complexDomain (hd : Data n R s ε h f)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : KAM.realInclusion₂ n z ∈ complexDomain n R s) :
    z ∈ Wdom n R s := by
  rw [← realInclusion₂_preimage_complexDomain hd.hR hd.hs]
  exact hz

private theorem snd_mem_realActionDomain (hd : Data n R s ε h f)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ Wdom n R s) :
    z.2 ∈ realActionDomain n R s := by
  rw [realActionDomain_eq hd.hR hd.hs]
  exact hz.2

/-- `G ∘ ι` is real on `W_s`. -/
private theorem G_im_eq_zero (hd : Data n R s ε h f) {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : z ∈ Wdom n R s) :
    (h (KAM.realInclusion₂ n z).2 + f (KAM.realInclusion₂ n z)).im = 0 := by
  have h2 := snd_mem_realActionDomain hd hz
  have hh0 : (h (fun i => (z.2 i : ℂ))).im = 0 := hd.hh.2.2.2.1 z.2 h2
  have hf0 : (f (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ))).im = 0 :=
    hd.hf.2.2.2.2.1 z.1 z.2 h2
  simpa [Complex.add_im, hh0, hf0] using (by rfl :
    (h (KAM.realInclusion₂ n z).2 + f (KAM.realInclusion₂ n z)).im =
      (h (fun i => (z.2 i : ℂ))).im + (f (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ))).im)

private theorem G_eq_ofReal (hd : Data n R s ε h f) {z : (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : z ∈ Wdom n R s) :
    h (KAM.realInclusion₂ n z).2 + f (KAM.realInclusion₂ n z) =
      ((KAM.realHamiltonian h f z : ℝ) : ℂ) :=
  Complex.ext (by rw [Complex.ofReal_re]; rfl) (by simpa using G_im_eq_zero hd hz)

private theorem h_eq_ofReal (hd : Data n R s ε h f) {I : Fin n → ℝ}
    (hI : I ∈ realActionDomain n R s) :
    h (KAM.realInclusion n I) = ((realPart h I : ℝ) : ℂ) :=
  Complex.ext (by rw [Complex.ofReal_re]; rfl)
    ((hd.hh.2.2.2.1 I hI).trans (Complex.ofReal_im _).symm)

/-- `Re g` of a function that is holomorphic on the open `U` and real on the real points of `U` is
differentiable at the real points of `U`, with `D(Re g) e = Dg (ιe)`. -/
private theorem real_fderiv_of_complex {U : Set (Fin n → ℂ)} {g : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ U → (g (KAM.realInclusion n I)).im = 0)
    {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ U) :
    DifferentiableAt ℝ (realPart g) I ∧ ∀ e : Fin n → ℝ,
      ((fderiv ℝ (realPart g) I e : ℝ) : ℂ) =
        fderiv ℂ g (KAM.realInclusion n I) (KAM.realInclusion n e) := by
  have hgd : DifferentiableAt ℂ g (KAM.realInclusion n I) :=
    hg.differentiableAt (hU.mem_nhds hI)
  have h2 : HasFDerivAt (fun y => g (KAM.realInclusion n y))
      (((fderiv ℂ g (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n)) I :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp I (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt (realPart g) (Complex.reCLM.comp
      (((fderiv ℂ g (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n))) I :=
    Complex.reCLM.hasFDerivAt.comp I h2
  refine ⟨h3.differentiableAt, fun e => ?_⟩
  have hmem : ∀ᶠ y in 𝓝 I, KAM.realInclusion n y ∈ U :=
    (KAM.realInclusion n).continuous.continuousAt.eventually_mem (hU.mem_nhds hI)
  have hev : (fun y => g (KAM.realInclusion n y)) =ᶠ[𝓝 I] fun y => ((realPart g y : ℝ) : ℂ) := by
    filter_upwards [hmem] with y hy
    exact Complex.ext (by rw [Complex.ofReal_re]; rfl)
      ((hreal y hy).trans (Complex.ofReal_im _).symm)
  have h5 : HasFDerivAt (fun y => ((realPart g y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (realPart g) I)) I :=
    Complex.ofRealCLM.hasFDerivAt.comp I h3.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  simpa using (congrArg (fun L => L e) h6).symm

end Helpers

/-! ### The theorems of `bpN:p1:holo-real` -/

section HoloReal

/-- (a) `G` and `h` are `C^∞` (holomorphic) on `D_s(R)` and `B(0,R)_s`. -/
theorem holo_real_a {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s ε h f) :
    DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w) (complexDomain n R s) ∧
    ContDiffOn ℂ ∞ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w) (complexDomain n R s) ∧
    ContDiffOn ℂ ∞ h (KAM.actionNbhd (actionBall n R) s) :=
  ⟨differentiableOn_G hd, contDiffOn_G hd, contDiffOn_h hd⟩

/-- (b) `H` is `C^∞` on `W_s`, real, `H = G ∘ ι`, `D^kH = D^kG ∘ ι` at every order; same for
`h_ℝ`. -/
theorem holo_real_b {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s ε h f) :
    ContDiffOn ℝ ∞ (KAM.realHamiltonian h f) (Wdom n R s) ∧
    ContDiffOn ℝ ∞ (realPart h) (realActionDomain n R s) ∧
    (∀ z ∈ Wdom n R s, (h (KAM.realInclusion₂ n z).2 + f (KAM.realInclusion₂ n z)).im = 0 ∧
      KAM.realHamiltonian h f z = (h (KAM.realInclusion₂ n z).2 + f (KAM.realInclusion₂ n z)).re) ∧
    (∀ z ∈ Wdom n R s, ∀ k : ℕ, ∀ ζ : Fin k → (Fin n → ℝ) × (Fin n → ℝ),
      ((iteratedFDeriv ℝ k (KAM.realHamiltonian h f) z ζ : ℝ) : ℂ) =
        iteratedFDeriv ℂ k (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w)
          (KAM.realInclusion₂ n z) (fun j => KAM.realInclusion₂ n (ζ j))) ∧
    (∀ I ∈ realActionDomain n R s, ∀ k : ℕ, ∀ a : Fin k → (Fin n → ℝ),
      ((iteratedFDeriv ℝ k (realPart h) I a : ℝ) : ℂ) =
        iteratedFDeriv ℂ k h (KAM.realInclusion n I) (fun j => KAM.realInclusion n (a j))) := by
  refine ⟨?_, ?_, fun z hz => ⟨G_im_eq_zero hd hz, rfl⟩, ?_, ?_⟩
  · have hGr := (contDiffOn_G hd).restrict_scalars ℝ
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (hGr.comp (KAM.realInclusion₂ n).contDiff.contDiffOn
        (fun _ hz => mem_complexDomain_of_mem_Wdom hd hz))
  · have hGr := (contDiffOn_h hd).restrict_scalars ℝ
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (hGr.comp (KAM.realInclusion n).contDiff.contDiffOn (fun _ hI => hI))
  · intro z hz k ζ
    exact iteratedFDeriv_real_eq_complex (KAM.realInclusion₂ n) (isOpen_complexDomain R s)
      (contDiffOn_G hd) (isOpen_Wdom R s) (fun _ hz => mem_complexDomain_of_mem_Wdom hd hz)
      (fun _ hz => G_eq_ofReal hd hz) k hz ζ
  · intro I hI k a
    exact iteratedFDeriv_real_eq_complex (KAM.realInclusion n) (isOpen_actionNbhd_ball R s)
      (contDiffOn_h hd) (isOpen_realActionDomain hd.hR hd.hs) (fun _ hI => hI)
      (fun _ hI => h_eq_ofReal hd hI) k hI a

/-- The complex Hessian entries `∂ᵢ∂ⱼ h(I)` of the frozen conventions. -/
def complexHessian (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) (i j : Fin n) : ℂ :=
  fderiv ℂ (fun x => fderiv ℂ h x (Pi.single j 1)) I (Pi.single i 1)

/-- (c) the field `X_H(z) = X_{h+f}(ι z)`, the frequency map and the Hessian of `h_ℝ`. -/
theorem holo_real_c {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s ε h f) :
    (∀ z ∈ Wdom n R s, DifferentiableAt ℝ (KAM.realHamiltonian h f) z ∧
      KAM.realInclusion₂ n (KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z) =
        KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2 + f w)
          (KAM.realInclusion₂ n z)) ∧
    (∀ I ∈ realActionDomain n R s, ∀ i,
      ((KAM.frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (KAM.realInclusion n I) (Pi.single i 1)) ∧
    (∀ I ∈ realActionDomain n R s, ∀ i j,
      ((fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) (Pi.single j 1) : ℝ) : ℂ) =
        complexHessian h (KAM.realInclusion n I) i j ∧
      complexHessian h (KAM.realInclusion n I) i j =
        complexHessian h (KAM.realInclusion n I) j i) :=
  by
  have hU : IsOpen (KAM.actionNbhd (actionBall n R) s) := isOpen_actionNbhd_ball R s
  have hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd (actionBall n R) s →
      (h (KAM.realInclusion n I)).im = 0 := fun I hI => hd.hh.2.2.2.1 I hI
  have hfreq : ∀ I ∈ realActionDomain n R s, ∀ i,
      ((KAM.frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (KAM.realInclusion n I) (Pi.single i 1) := by
    intro I hI i
    have h1 := (real_fderiv_of_complex hU hd.hh.1 hreal hI).2 (Pi.single i 1)
    rw [KAM.realInclusion_single] at h1
    exact h1
  refine ⟨fun z hz => ?_, hfreq, fun I hI i j => ?_⟩
  · exact (KAM.hamiltonian_real (H := KAM.realHamiltonian h f) (isOpen_complexDomain R s)
      (differentiableOn_G hd) (fun y hy => G_im_eq_zero hd (mem_Wdom_of_mem_complexDomain hd hy))
      (mem_complexDomain_of_mem_Wdom hd hz) (Filter.Eventually.of_forall fun y => rfl)).1
  · refine ⟨?_, ?_⟩
    · -- the `j`-th partial derivative as a holomorphic function, real on the real points
      have hdf : DifferentiableOn ℂ (fderiv ℂ h) (KAM.actionNbhd (actionBall n R) s) :=
        (KAM.holomorphic_regularity hU hd.hh.1).1
      have hgj : DifferentiableOn ℂ (fun x => fderiv ℂ h x (Pi.single j 1))
          (KAM.actionNbhd (actionBall n R) s) :=
        hdf.clm_apply (differentiableOn_const _)
      have hrealj : ∀ J : Fin n → ℝ, KAM.realInclusion n J ∈ KAM.actionNbhd (actionBall n R) s →
          (fderiv ℂ h (KAM.realInclusion n J) (Pi.single j 1)).im = 0 := by
        intro J hJ
        rw [← hfreq J hJ j]
        exact Complex.ofReal_im _
      have hC := (real_fderiv_of_complex hU hgj hrealj hI).2 (Pi.single i 1)
      rw [KAM.realInclusion_single] at hC
      have hD : DifferentiableAt ℝ (fderiv ℝ (realPart h)) I := by
        have hc : ContDiffOn ℝ ∞ (realPart h) (realActionDomain n R s) :=
          (holo_real_b hd).2.1
        have := (hc.fderiv_of_isOpen (isOpen_realActionDomain hd.hR hd.hs)
          (m := 1) (by simp)).differentiableOn one_ne_zero
        exact this.differentiableAt ((isOpen_realActionDomain hd.hR hd.hs).mem_nhds hI)
      have hstep : fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) (Pi.single j 1) =
          fderiv ℝ (fun J => fderiv ℝ (realPart h) J (Pi.single j 1)) I (Pi.single i 1) := by
        rw [fderiv_clm_apply hD (differentiableAt_const _)]
        simp
      have hev : (fun J => fderiv ℝ (realPart h) J (Pi.single j 1)) =ᶠ[𝓝 I]
          realPart (fun x => fderiv ℂ h x (Pi.single j 1)) := by
        filter_upwards [(isOpen_realActionDomain hd.hR hd.hs).mem_nhds hI] with J hJ
        have := hfreq J hJ j
        have h2 : realPart (fun x => fderiv ℂ h x (Pi.single j 1)) J =
            (fderiv ℂ h (KAM.realInclusion n J) (Pi.single j 1)).re := rfl
        rw [h2, ← this, Complex.ofReal_re]
        rfl
      rw [hstep, hev.fderiv_eq, hC]
      rfl
    · exact (KAM.holomorphic_regularity hU hd.hh.1).2.2.2.2.2 _ hI i j

/-- (d) periodicity of `H`, `DH`, `D^kH`, `X_H` in `θ` on `W_s`, `k ∈ ℤⁿ`. -/
theorem holo_real_d {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s ε h f) :
    ∀ z ∈ Wdom n R s, ∀ k : Fin n → ℤ, z + KAM.ODE.angleShift k ∈ Wdom n R s ∧
      KAM.realHamiltonian h f (z + KAM.ODE.angleShift k) = KAM.realHamiltonian h f z ∧
      fderiv ℝ (KAM.realHamiltonian h f) (z + KAM.ODE.angleShift k) =
        fderiv ℝ (KAM.realHamiltonian h f) z ∧
      KAM.hamiltonianVectorField (KAM.realHamiltonian h f) (z + KAM.ODE.angleShift k) =
        KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z ∧
      ∀ j : ℕ, iteratedFDeriv ℝ j (KAM.realHamiltonian h f) (z + KAM.ODE.angleShift k) =
        iteratedFDeriv ℝ j (KAM.realHamiltonian h f) z := by
  have hper : ∀ y ∈ Wdom n R s, ∀ k : Fin n → ℤ,
      KAM.realHamiltonian h f (y + KAM.ODE.angleShift k) = KAM.realHamiltonian h f y := by
    intro y hy k
    have hp := hd.hf.2.2.2.1 (KAM.realInclusion₂ n y) (mem_complexDomain_of_mem_Wdom hd hy) k
    have e1 : (fun i => (((y + KAM.ODE.angleShift k).1 i : ℝ) : ℂ)) =
        (KAM.realInclusion₂ n y).1 + fun i => (k i : ℂ) := by
      ext i
      simp [KAM.ODE.angleShift]
    have e2 : (fun i => (((y + KAM.ODE.angleShift k).2 i : ℝ) : ℂ)) =
        (KAM.realInclusion₂ n y).2 := by
      ext i
      simp [KAM.ODE.angleShift]
    unfold KAM.realHamiltonian
    rw [e1, e2, hp]
    rfl
  intro z hz k
  have hW : z + KAM.ODE.angleShift k ∈ Wdom n R s :=
    ⟨mem_univ _, by simpa [KAM.ODE.angleShift] using hz.2⟩
  have hev : (fun y => KAM.realHamiltonian h f (y + KAM.ODE.angleShift k)) =ᶠ[𝓝 z]
      KAM.realHamiltonian h f :=
    Filter.eventuallyEq_of_mem ((isOpen_Wdom R s).mem_nhds hz) (fun y hy => hper y hy k)
  have hF : fderiv ℝ (KAM.realHamiltonian h f) (z + KAM.ODE.angleShift k) =
      fderiv ℝ (KAM.realHamiltonian h f) z := by
    rw [← hev.fderiv_eq, fderiv_comp_add_right]
  refine ⟨hW, hper z hz k, hF, ?_, fun j => ?_⟩
  · simp only [KAM.hamiltonianVectorField, hF]
  · rw [← (hev.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_comp_add_right]

/-- (e) `ε = 0` forces `f = 0` and `H = h_ℝ ∘ snd`. -/
theorem holo_real_e {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s 0 h f) :
    (∀ w ∈ complexDomain n R s, f w = 0) ∧
      ∀ z ∈ Wdom n R s, KAM.realHamiltonian h f z = realPart h z.2 := by
  have hf0 : ∀ w ∈ complexDomain n R s, f w = 0 := fun w hw =>
    norm_le_zero_iff.1 (hd.hf.2.2.2.2.2 w hw)
  refine ⟨hf0, fun z hz => ?_⟩
  have h0 : f (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ)) = 0 :=
    hf0 _ (mem_complexDomain_of_mem_Wdom hd hz)
  unfold KAM.realHamiltonian realPart
  rw [h0, add_zero]

/-- The statement Part 3 calls `bpN:p3:holo-input` (a corollary of `holo_real_b,c,d`, proved
here). -/
theorem holo_input {R s ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hd : Data n R s ε h f) :
    ContDiffOn ℝ ∞ (KAM.realHamiltonian h f) (Wdom n R s) ∧
    (∀ z ∈ Wdom n R s,
      KAM.realInclusion₂ n (KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z) =
      KAM.hamiltonianVectorFieldℂ (fun w => h w.2 + f w) (KAM.realInclusion₂ n z)) ∧
    (∀ z ∈ Wdom n R s, ∀ k : Fin n → ℤ,
      KAM.realHamiltonian h f (z + KAM.ODE.angleShift k) = KAM.realHamiltonian h f z) :=
  ⟨(holo_real_b hd).1, fun z hz => ((holo_real_c hd).1 z hz).2,
    fun z hz k => ((holo_real_d hd z hz k).2.1)⟩

end HoloReal

end KAM.Nekhoroshev

end
