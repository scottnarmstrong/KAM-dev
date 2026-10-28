/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.IterativeRemainder
public import KAM.Canonical.Composition
import Mathlib.Tactic.Linarith

/-!
# The Iterative Lemma: reality (`bpN:p6:iterative` (e))

If `h`, `g`, `f` are real on real points and `Λ = -Λ`, then `φ = homGen`, `g₊ = iterG` and
`f₊ = iterF` are real on real points and `Φ = X¹_φ` maps real points of `𝒟_{r-3ρ/2,s-3σ/2}` to real
points. The frequency `ω = ∂_I h` is real at real points because `h` is real on a real neighbourhood
(`freq_im_real`); then `homological_direct` (c), `composition_real` for `H ∘ Φ` and
`canonical_map_b` give the claim. Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-7.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- `h` real on the real points of `𝒟_{r,s}` has real frequency at the real points of `V_r D`. -/
theorem freq_im_real {D : Set (Fin n → ℂ)} {r s : ℝ} {h : (Fin n → ℂ) → ℂ} (hs : 0 < s)
    (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hhr : RealOn (Dom n D r s) (fun w => h w.2)) {I : Fin n → ℝ}
    (hI : KAM.realInclusion n I ∈ polyNbhd D r) (i : Fin n) :
    (freq h (KAM.realInclusion n I) i).im = 0 := by
  set v : Fin n → ℂ := Pi.single i 1 with hv
  set x₀ := KAM.realInclusion n I with hx₀
  let γ : ℝ → Fin n → ℂ := fun t => x₀ + (t : ℂ) • v
  have hγ : HasDerivAt γ v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have := (h1.smul_const v).const_add x₀
    simpa only [one_smul] using this
  have hγ0 : γ 0 = x₀ := by simp [γ]
  have hopen : IsOpen (polyNbhd D r) := isOpen_polyNbhd D r
  have hev : ∀ᶠ t in nhds (0 : ℝ), γ t ∈ polyNbhd D r :=
    hγ.continuousAt.eventually (hopen.mem_nhds (by rwa [hγ0]))
  have hhd : DifferentiableAt ℂ h (γ 0) :=
    hh.differentiableAt (hopen.mem_nhds (by rwa [hγ0]))
  have hcomp : HasDerivAt (fun t => h (γ t)) (fderiv ℂ h (γ 0) v) 0 :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hγ
  have him : HasDerivAt (fun t => (h (γ t)).im) (fderiv ℂ h (γ 0) v).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp
  have hzero : (fun t => (h (γ t)).im) =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with t ht
    have hreal : γ t = KAM.realInclusion n (I + t • (Pi.single i 1 : Fin n → ℝ)) := by
      ext j
      by_cases hj : j = i <;> simp [γ, hx₀, hv, hj]
    have hmem : KAM.realInclusion₂ n (0, I + t • (Pi.single i 1 : Fin n → ℝ)) ∈
        Dom n D r s := by
      refine ⟨fun j => by simpa using hs, ?_⟩
      simpa [KAM.realInclusion₂_apply, ← hreal] using ht
    have := hhr _ hmem
    simpa [KAM.realInclusion₂_apply, ← hreal] using this
  have h0 := him.congr_of_eventuallyEq hzero.symm
  have := h0.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  rw [hγ0] at this
  simpa [freq, hv] using this

/-- `RealOn` restricts to smaller domains. -/
private theorem realOn_mono {U V : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : RealOn U u) (hVU : V ⊆ U) : RealOn V u :=
  fun x hx => hu x (hVU hx)

/-- `RealOn` transports along an equality of radii. -/
private theorem realOn_Dom_congr {D : Set (Fin n → ℂ)} {r s r' s' : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hr : r = r') (hs : s = s') (hu : RealOn (Dom n D r s) u) :
    RealOn (Dom n D r' s') u := by
  subst hr hs; exact hu

section Iterative

variable {D : Set (Fin n → ℂ)} {r s ρ σ K α p δ : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ}
  {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {rj sj Mj : Fin N → ℝ}

/-- `bpN:p6:iterative-direct` (e): reality. -/
theorem iterative_direct_e (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj)
    (hΛ : ∀ k ∈ Λ, -k ∈ Λ) (hhr : RealOn (Dom n D r s) (fun w => h w.2))
    (hgr : RealOn (Dom n D r s) g) (hfr : RealOn (Dom n D r s) f) :
    RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (iterG K Λ g f) ∧
    RealOn (Dom n D (r - 2 * ρ) (s - 2 * σ)) (iterF D r s ρ σ K Λ h g f) ∧
    ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) →
      iterMap D r s ρ σ K Λ h f (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10⟩ :=
    homological_direct H.hp H.hα H.hs H.hK H.h_holo H.divisor H.f_class H.f_bound
  obtain ⟨hφr, hξr⟩ := c10 hΛ hfr fun I hI i => freq_im_real H.hs H.h_holo hhr hI i
  have hgr' : RealOn (Dom n D r s) (iterG K Λ g f) := fun x hx => by
    show (g (KAM.realInclusion₂ n x) + homRes K Λ f (KAM.realInclusion₂ n x)).im = 0
    rw [Complex.add_im, hgr x hx, hξr x hx, add_zero]
  refine ⟨hφr, hgr', ?_, fun x hx => (canonical_map_b H.canon).2 hφr x hx⟩
  have hsub : Dom n D (r - ρ) (s - σ) ⊆ Dom n D r s :=
    Dom_mono (by linarith [H.hρ]) (by linarith [H.hσ])
  have hur : RealOn (Dom n D (r - ρ) (s - σ)) (fun w => h w.2 + g w + f w) :=
    fun x hx => by
      have e2 := hhr x (hsub hx)
      show ((h (KAM.realInclusion₂ n x).2 + g (KAM.realInclusion₂ n x) +
        f (KAM.realInclusion₂ n x))).im = 0
      rw [Complex.add_im, Complex.add_im, e2, hgr x (hsub hx), hfr x (hsub hx)]
      ring
  have hcr := composition_real H.compose hur hφr
  have hcr' : RealOn (Dom n D (r - 2 * ρ) (s - 2 * σ))
      (fun z => (fun w => h w.2 + g w + f w) (iterMap D r s ρ σ K Λ h f z)) :=
    realOn_Dom_congr (by ring) (by ring) hcr
  intro x hx
  have hsub2 : Dom n D (r - 2 * ρ) (s - 2 * σ) ⊆ Dom n D r s :=
    Dom_mono (by linarith [H.hρ]) (by linarith [H.hσ])
  have e1 := hcr' x hx
  have e2 := hhr x (hsub2 hx)
  have e3 := hgr' x (hsub2 hx)
  simp only [iterF, Complex.sub_im]
  simp only [] at e1 e2 ⊢
  rw [e1, e2, e3]
  ring

end Iterative

end KAM.NormalForm

end
