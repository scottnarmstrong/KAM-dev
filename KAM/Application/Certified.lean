/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Ham
public import KAM.Certificate.Sound.Static
public import KAM.Application.RealTorus

/-!
# The certified torus with its witnesses named, in real model coordinates

`CertifiedTorus c ω*` (`KAM/Certificate/Defs.lean`) is an existential over the exact torus `K∞` and
the frequency scalar `s∞`. Physical statements must attach several facts to the same witnesses, so:

* `CertifiedTorusAt c ω* K∞ s∞`: the body of `CertifiedTorus`, verbatim, with the witnesses
  named; `certifiedTorus_iff` is `Iff.rfl`. (LG00's `lg00TorusWith` is its `n = 2` instance.)
* `isRealHolo_of_differentiableOn`, `isRealHolo_of_nonvanishing`, `isRealHolo_of_checkHamBounds`:
  the certificate Hamiltonian `c.H` is holomorphic and real on `c.D` (`IsRealHolo`), from the
  certified denominators (every certifier's `checkHamBounds`, `G1Hyps.hholo` or
  `BaseFacts.hH.1`).
* `CertifiedTorusAt.isRealModelTorus`: the real restriction `k = Re ∘ K∞ ∘ ι` is a real model torus
  of `realHam c.H` at `s∞ ω*` on the level `E₀` (only `checkStatic` is used, for `ρ∞, μ > 0`).
* `CertifiedTorusAt.norm_realRestriction_sub_le`: `‖k θ - Re K(ι θ)‖ ≤ disp` at real angles.
* `CertifiedTorusAt.isDiophantine`, `CertifiedTorusAt.abs_sub_mul_norm_le`: the frequency
  `s∞ ω*` is `(s∞ γ, τ)`-Diophantine and `|s∞ - s| ‖ω*‖ ≤ disp`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- **`CertifiedTorus` with its witnesses named**: the body of `KAM.Certificate.CertifiedTorus`,
verbatim, at the exact torus `Kinf` and the scalar `sinf`. -/
def CertifiedTorusAt (c : TorusCertificate n α) (ωstar : Fin n → ℝ)
    (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ) : Prop :=
  1 < sinf ∧ sinf < c.params.σω ∧ DifferentiableOn ℂ Kinf (complexStrip n c.params.rhoInf) ∧
    IsPrimaryOnStrip Kinf c.params.rhoInf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, invarianceError c.H Kinf (sinf • ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, c.H (Kinf θ) = ((c.params.E0 : ℝ) : ℂ)) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, Metric.ball (Kinf θ) ((c.params.μ : ℝ) / 2) ⊆ c.D) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf,
      ‖fderiv ℂ Kinf θ‖ ≤ (c.params.σK : ℝ) - (c.params.μ : ℝ) / 2) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, ‖Kinf θ - c.K θ‖ ≤ c.params.disp) ∧
    ‖sinf • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ c.params.disp

/-- `CertifiedTorusAt` is the landed `CertifiedTorus` with its witnesses named. -/
theorem certifiedTorus_iff (c : TorusCertificate n α) (ωstar : Fin n → ℝ) :
    CertifiedTorus c ωstar ↔ ∃ Kinf sinf, CertifiedTorusAt c ωstar Kinf sinf :=
  Iff.rfl

/-! ### The certificate Hamiltonian is holomorphic and real -/

omit [CertArith α] in
/-- `c.D` is open and `c.H` real at real points unconditionally; holomorphy is the input. -/
theorem isRealHolo_of_differentiableOn (c : TorusCertificate n α)
    (hholo : DifferentiableOn ℂ c.H c.D) : IsRealHolo c.D c.H :=
  ⟨isOpen_certDomain _ _ _ _, hholo, fun y _ => c.ham.eval_real y.1 y.2⟩

/-- From certified denominators (`G1Hyps`/`BaseFacts` carry them). -/
theorem isRealHolo_of_nonvanishing (c : TorusCertificate n α)
    (hnv : c.ham.NonvanishingOn c.D) : IsRealHolo c.D c.H :=
  isRealHolo_of_differentiableOn c (c.ham_structural hnv).2.2.1

variable [LawfulCertArith α]

/-- From the passing static and Hamiltonian-bound sub-checks (common to every certifier). -/
theorem isRealHolo_of_checkHamBounds {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) : IsRealHolo c.D c.H :=
  isRealHolo_of_nonvanishing c (checkHamBounds_sound hs hh).1

/-! ### The real model torus -/

section At

variable {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

theorem CertifiedTorusAt.realInclusion_mem_D (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (x : Fin n → ℝ) : Kinf (realInclusion n x) ∈ c.D := by
  have S := checkStatic_sound hs
  exact hT.2.2.2.2.2.2.2.1 _ (realInclusion_mem_complexStrip S.hρinf x)
    (Metric.mem_ball_self (half_pos S.hμ))

/-- **The certified torus in real model coordinates**: `k = Re ∘ K∞ ∘ ι` is an analytic real torus,
`k(θ + m) = k(θ) + (m, 0)`, whose lines `s ↦ k(θ + s s∞ ω*)` solve Hamilton's equations of the real
certificate Hamiltonian `realHam c.H`, on the level `realHam c.H = E₀`. -/
theorem CertifiedTorusAt.isRealModelTorus (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (hH : IsRealHolo c.D c.H) :
    IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) := by
  have S := checkStatic_sound hs
  have hKD := hT.realInclusion_mem_D hs
  obtain ⟨-, -, hd, hp, hr, hinv, hE, -, -, -, -⟩ := hT
  exact isRealModelTorus_realRestriction hH S.hρinf hd hp hr hKD hinv hE

omit [CertArith α] [LawfulCertArith α] in
theorem norm_realPartCLM₂_le (v : (Fin n → ℂ) × (Fin n → ℂ)) : ‖realPartCLM₂ n v‖ ≤ ‖v‖ := by
  rw [realPartCLM₂_apply, Prod.norm_def, Prod.norm_def]
  exact max_le_max (norm_realPartCLM_le _) (norm_realPartCLM_le _)

/-- The exact real torus is within `disp` of the real restriction of the certificate's `K`. -/
theorem CertifiedTorusAt.norm_realRestriction_sub_le (hT : CertifiedTorusAt c ωstar Kinf sinf)
    (hs : checkStatic c = true) (θ : Fin n → ℝ) :
    ‖realRestriction Kinf θ - realRestriction c.K θ‖ ≤ c.params.disp := by
  have S := checkStatic_sound hs
  have h := hT.2.2.2.2.2.2.2.2.2.1 _ (realInclusion_mem_complexStrip S.hρinf θ)
  rw [realRestriction, realRestriction, ← map_sub]
  exact (norm_realPartCLM₂_le _).trans h

omit [LawfulCertArith α] in
/-- The frequency `s∞ ω*` is `(s∞ γ, τ)`-Diophantine. -/
theorem CertifiedTorusAt.isDiophantine (hT : CertifiedTorusAt c ωstar Kinf sinf) {γ τ : ℝ}
    (hdio : IsDiophantine γ τ ωstar) : IsDiophantine (sinf * γ) τ (sinf • ωstar) :=
  isDiophantine_mul_smul (by linarith [hT.1]) hdio

omit [LawfulCertArith α] in
/-- The frequency scalar: `|s∞ - s| ‖ω*‖ ≤ disp`. -/
theorem CertifiedTorusAt.abs_sub_mul_norm_le (hT : CertifiedTorusAt c ωstar Kinf sinf) :
    |sinf - c.params.s| * ‖ωstar‖ ≤ c.params.disp := by
  have h := hT.2.2.2.2.2.2.2.2.2.2
  rwa [← sub_smul, norm_smul, Real.norm_eq_abs] at h

end At

end KAM.Application
