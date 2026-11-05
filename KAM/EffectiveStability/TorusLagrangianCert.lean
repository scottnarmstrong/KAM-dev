/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Certified
public import KAM.EffectiveStability.TorusLagrangian
public import KAM.EffectiveStability.TorusProjection
public import KAM.EffectiveStability.TorusRealSlice
public import KAM.Iso.Linear.Tools

/-!
# The exact torus of a certificate: Lagrangian, real slice, frequency identity (track B, B5-LAG)

Corollaries for `KAM.Application.CertifiedTorusAt c ω* K∞ s∞` (the body of
`KAM.Certificate.CertifiedTorus`), under `G1Hyps c ω*` and `IsDiophantine γ τ ω*` as in
`checkTorusCertificate_sound`:

* `g1Hyps_standing`: the standing data of `KAM.Apost` at `s ω*` (`s ≥ 1`);
* `certifiedTorusAt_lagrangian`: `Ω_{K∞} = 0` on `T_{ρ∞ - δ}` (direct argument, no extra data);
* `certifiedTorusAt_realLagrangian`: `(Dx)ᵀ Dv` symmetric for the real slice, at every real `φ`;
* `certifiedTorusAt_frequency`, `certifiedTorusAt_energy`: `D(x, v) φ (s∞ ω*) = X_{hR} (x φ, v φ)`
  and `hR (x φ, v φ) = E₀`, for `hR = KAM.Application.realHam c.H`;
* `certifiedTorusAt_projection`: `‖Du φ‖ ≤ κc + disp/δ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Certificate KAM.Application CertArith

variable {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
  {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {sinf : ℝ}

/-- The standing data of `KAM.Apost` at the frequency `s ω*`, `s ≥ 1`, from `G1Hyps` and the
Diophantine condition on `ω*`. -/
theorem g1Hyps_standing (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) {s : ℝ} (hs : 1 ≤ s) :
    Apost.Standing n (c.params.tau : ℝ) (c.params.M : ℝ) (c.params.σK : ℝ) (c.params.σB : ℝ)
      (c.params.σT : ℝ) c.D c.H (s • ωstar) (c.params.γ : ℝ) :=
  { two_le := hG.hn
    tau_ge := hG.hτ
    M_pos := hG.hM
    σK_pos := hG.hσK
    σB_pos := hG.hσB
    σT_pos := hG.hσT
    isOpen := hG.hopen
    transl_mem := hG.htransl
    holo := hG.hholo
    periodic := hG.hper
    real := hG.hreal
    bounds := fun z hz =>
      ⟨(hG.hbd z hz).2.1, (hG.hbd z hz).2.2.1, (hG.hbd z hz).2.2.2.1⟩
    gamma_pos := hG.hγ
    dio := Iso.Linear.isDiophantine_smul hdio hs }

theorem certifiedTorusAt_mem_D (hG : G1Hyps c ωstar) (hT : CertifiedTorusAt c ωstar Kinf sinf) :
    ∀ θ ∈ complexStrip n (c.params.rhoInf : ℝ), Kinf θ ∈ c.D := fun θ hθ =>
  hT.2.2.2.2.2.2.2.1 θ hθ (Metric.mem_ball_self (half_pos hG.hμ))

/-- **Lagrangian property** (item 1): the exact torus of a certificate is Lagrangian on
`T_{ρ∞ - δ}`, `0 < δ < ρ∞`. -/
theorem certifiedTorusAt_lagrangian (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) {δ : ℝ} (hδ : 0 < δ)
    (hδρ : δ < (c.params.rhoInf : ℝ)) :
    ∀ θ ∈ complexStrip n ((c.params.rhoInf : ℝ) - δ), lagrangeMat Kinf θ = 0 := by
  have hKD := certifiedTorusAt_mem_D hG hT
  obtain ⟨hs1, -, hK, hKp, -, hinv, -⟩ := hT
  exact lagrangeMat_eq_zero_of_exact (g1Hyps_standing hG hdio hs1.le) hG.hρinf hK hKp hKD hinv hδ
    hδρ

/-- **Real Lagrangian condition** (item 2): for every real `φ`, `(Dx)ᵀ Dv` is symmetric, for
`x = Re K∞^θ`, `v = Re K∞^I` on the reals. -/
theorem certifiedTorusAt_realLagrangian (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) {δ : ℝ} (hδ : 0 < δ)
    (hδρ : δ < (c.params.rhoInf : ℝ)) (φ : Fin n → ℝ) (i j : Fin n) :
    ∑ l, (fderiv ℝ (torusRealX Kinf) φ (Pi.single i 1)) l *
        (fderiv ℝ (torusRealV Kinf) φ (Pi.single j 1)) l =
      ∑ l, (fderiv ℝ (torusRealX Kinf) φ (Pi.single j 1)) l *
        (fderiv ℝ (torusRealV Kinf) φ (Pi.single i 1)) l :=
  torusReal_lagrangian hG.hρinf hT.2.2.1 hT.2.2.2.2.1
    (certifiedTorusAt_lagrangian hG hdio hT hδ hδρ _
      (realInclusion_mem_complexStrip (by linarith) φ)) i j

/-- **Frequency identity on reals** (item 3): `D(x, v) φ (s∞ ω*) = X_{hR} (x φ, v φ)` for the
real Hamiltonian `hR = Re c.H ∘ ι₂` of the certificate. -/
theorem certifiedTorusAt_frequency (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (φ : Fin n → ℝ) :
    fderiv ℝ (realRestriction Kinf) φ (sinf • ωstar) =
      hamiltonianVectorField (realHam c.H) (realRestriction Kinf φ) :=
  torusReal_frequency hG.hρinf hT.2.2.1 hT.2.2.2.2.1 hG.hopen hG.hholo
    (isRealHolo_of_differentiableOn c hG.hholo).real
    (certifiedTorusAt_mem_D hG hT) hT.2.2.2.2.2.1 φ

/-- **Energy on reals** (item 3): `hR (x φ, v φ) = E₀`. -/
theorem certifiedTorusAt_energy (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (φ : Fin n → ℝ) :
    realHam c.H (realRestriction Kinf φ) = (c.params.E0 : ℝ) :=
  torusReal_energy hT.2.2.2.2.1 φ
    (hT.2.2.2.2.2.2.1 _ (realInclusion_mem_complexStrip hG.hρinf φ))

/-- **Projection bound** (item 4): from `‖D(K_c^θ - id)(ι φ)‖ ≤ κc` at real points and the
certificate's displacement bound, `‖Du φ‖ ≤ κc + disp/δ` for `0 < δ < ρ∞`. -/
theorem certifiedTorusAt_projection (hG : G1Hyps c ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) {δ κc : ℝ} (hδ : 0 < δ)
    (hδρ : δ < (c.params.rhoInf : ℝ))
    (hκ : ∀ φ : Fin n → ℝ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) (realInclusion n φ)‖ ≤ κc)
    (φ : Fin n → ℝ) :
    ‖fderiv ℝ (torusRealU Kinf) φ‖ ≤ κc + (c.params.disp : ℝ) / δ :=
  torusRealU_fderiv_le hG.hρinf hT.2.2.1
    (hG.hK.mono fun _ hθ i => (hθ i).trans hG.hρinfρ) hT.2.2.2.2.1 hδ hδρ hκ
    hT.2.2.2.2.2.2.2.2.2.1 φ

end KAM.EffectiveStability

end
