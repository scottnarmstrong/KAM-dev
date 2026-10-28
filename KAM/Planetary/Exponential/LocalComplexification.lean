/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Strip.Analytic
public import KAM.Strip.RealRestriction
public import KAM.Planetary.PGAssembly.ComplexLocal

/-!
# P14 package E5: local complexification wrappers

* `complex_division`: quotient of holomorphic functions with non-vanishing denominator on a
  subset of `ℂᵈ × ℂᵈ` (via `DifferentiableOn.inv` and `DifferentiableOn.mul`).
* `local_complex_restriction`: the real derivative of `Re ∘ f ∘ complexifyPhase` is the real part
  of the complex derivative (local; no strip hypothesis).
* `local_analytic_complexification`: a real-analytic function on phase space is the real trace of
  a holomorphic function on a complex ball around `complexifyPhase x`; obtained from the P5-CL
  `local_real_complexification` on `Fin (d + d) → ℝ` transported by the isometric packing
  `Fin.append`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Planetary

/-- Local replacement for the strip-only restriction cited at p7:ho-hol. -/
theorem local_complex_restriction {d : ℕ}
    {f : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ} {z : Phase d}
    (hf : DifferentiableAt ℂ f (KAM.Nekhoroshev.complexifyPhase z)) (v : Phase d) :
    fderiv ℝ (fun w => (f (KAM.Nekhoroshev.complexifyPhase w)).re) z v =
      (fderiv ℂ f (KAM.Nekhoroshev.complexifyPhase z)
        (KAM.Nekhoroshev.complexifyPhase v)).re := by
  have hc : HasFDerivAt (fun w : Phase d => KAM.Nekhoroshev.complexifyPhase w)
      (KAM.realInclusion₂ d) z := (KAM.realInclusion₂ d).hasFDerivAt
  have h1 : HasFDerivAt f ((fderiv ℂ f (KAM.Nekhoroshev.complexifyPhase z)).restrictScalars ℝ)
      (KAM.Nekhoroshev.complexifyPhase z) := hf.hasFDerivAt.restrictScalars ℝ
  have h2 := (Complex.reCLM.hasFDerivAt (x := f (KAM.Nekhoroshev.complexifyPhase z))).comp z
    (h1.comp z hc)
  rw [show (fun w : Phase d => (f (KAM.Nekhoroshev.complexifyPhase w)).re) =
    Complex.reCLM ∘ f ∘ (fun w : Phase d => KAM.Nekhoroshev.complexifyPhase w) from rfl,
    h2.fderiv]
  rfl

theorem complex_division {d : ℕ}
    {U : Set ((Fin d → ℂ) × (Fin d → ℂ))}
    {f g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / g z) U := by
  simp only [div_eq_mul_inv]
  exact hf.mul (hg.inv hg0)

/-- Packing `ℝᵈ × ℝᵈ → ℝ^(d+d)` (any scalar field) by `Fin.append`; a continuous linear map. -/
def e5Pack (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) :
    ((Fin d → 𝕜) × (Fin d → 𝕜)) →L[𝕜] (Fin (d + d) → 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => Fin.append p.1 p.2
      map_add' := fun p q => by
        ext k; refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
          simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Fin.append_left, Fin.append_right]
      map_smul' := fun c p => by
        ext k; refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
          simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Fin.append_left,
            Fin.append_right, RingHom.id_apply] }

theorem e5Pack_apply (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} (p : (Fin d → 𝕜) × (Fin d → 𝕜)) :
    e5Pack 𝕜 d p = Fin.append p.1 p.2 := rfl

/-- Unpacking `ℝ^(d+d) → ℝᵈ × ℝᵈ`. -/
def e5Unpack (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) :
    (Fin (d + d) → 𝕜) →L[𝕜] ((Fin d → 𝕜) × (Fin d → 𝕜)) :=
  (ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (d + d) => 𝕜) (Fin.castAdd d i)).prod
    (ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (d + d) => 𝕜) (Fin.natAdd d i))

theorem e5Unpack_pack (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} (p : (Fin d → 𝕜) × (Fin d → 𝕜)) :
    e5Unpack 𝕜 d (e5Pack 𝕜 d p) = p := by
  refine Prod.ext ?_ ?_ <;>
    (ext i; simp only [e5Unpack, e5Pack_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.append_left,
    Fin.append_right])

theorem norm_e5Pack (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} (p : (Fin d → 𝕜) × (Fin d → 𝕜)) :
    ‖e5Pack 𝕜 d p‖ = ‖p‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [e5Pack_apply, Fin.append_left]
      exact (norm_le_pi_norm p.1 i).trans (le_max_left _ _)
    · rw [e5Pack_apply, Fin.append_right]
      exact (norm_le_pi_norm p.2 i).trans (le_max_right _ _)
  · have h := (e5Unpack 𝕜 d).le_opNorm (e5Pack 𝕜 d p)
    rw [e5Unpack_pack] at h
    have h1 : ‖e5Unpack 𝕜 d‖ ≤ 1 := by
      refine (e5Unpack 𝕜 d).opNorm_le_bound zero_le_one fun w => ?_
      rw [one_mul, Prod.norm_def]
      refine max_le ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
      · simpa [e5Unpack] using norm_le_pi_norm w (Fin.castAdd d i)
      · simpa [e5Unpack] using norm_le_pi_norm w (Fin.natAdd d i)
    exact h.trans (by nlinarith [norm_nonneg (e5Pack 𝕜 d p)])

theorem e5Pack_complexify {d : ℕ} (y : Phase d) :
    e5Pack ℂ d (KAM.Nekhoroshev.complexifyPhase y) = KAM.realInclusion (d + d) (e5Pack ℝ d y) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [e5Pack_apply, KAM.Nekhoroshev.complexifyPhase, KAM.realInclusion_apply,
      Fin.append_left, Fin.append_right]

theorem local_analytic_complexification {d : ℕ} {f : Phase d → ℝ} {x : Phase d}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ,
      DifferentiableOn ℂ g (Metric.ball (KAM.Nekhoroshev.complexifyPhase x) r) ∧
      ∀ y : Phase d, ‖y-x‖ < r → g (KAM.Nekhoroshev.complexifyPhase y) = (f y : ℂ) := by
  have hf' : AnalyticAt ℝ (fun w : Fin (d + d) → ℝ => f (e5Unpack ℝ d w)) (e5Pack ℝ d x) := by
    have h : AnalyticAt ℝ f (e5Unpack ℝ d (e5Pack ℝ d x)) := by
      rw [e5Unpack_pack]; exact hf
    exact h.comp ((e5Unpack ℝ d).analyticAt _)
  obtain ⟨ρ, M, F, hρ, -, hdiff, hF, -⟩ := local_real_complexification hf'
  refine ⟨ρ, hρ, fun p => F (e5Pack ℂ d p), ?_, ?_⟩
  · refine hdiff.comp (e5Pack ℂ d).differentiableOn fun p hp => ?_
    rw [mem_ball, dist_eq_norm] at hp ⊢
    have : e5Pack ℂ d p - KAM.realInclusion (d + d) (e5Pack ℝ d x) =
        e5Pack ℂ d (p - KAM.Nekhoroshev.complexifyPhase x) := by
      rw [map_sub, e5Pack_complexify]
    rw [this, norm_e5Pack]; exact hp
  · intro y hy
    show F (e5Pack ℂ d (KAM.Nekhoroshev.complexifyPhase y)) = _
    rw [e5Pack_complexify]
    have hy' : e5Pack ℝ d y ∈ ball (e5Pack ℝ d x) ρ := by
      rw [mem_ball, dist_eq_norm, ← map_sub, norm_e5Pack]; exact hy
    have := hF _ hy'
    rw [e5Unpack_pack] at this
    exact this

end KAM.Planetary
