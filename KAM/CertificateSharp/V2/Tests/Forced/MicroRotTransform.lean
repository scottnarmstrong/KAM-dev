/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRoutes
public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotRoutes
public import KAM.Certificate.Sound.Invariance

/-!
# The rotated-coordinate normalization of `Micro`, through its checked transformation

`MicroRot` is `Micro` in the rotated variables of the linear symplectic unimodular change of
variables `L = shearMap`, `L ((Q₀, Q₁), (P₀, P₁)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))` (the lunar
client's `soRotMap`), angle block `S`, `S (φ₀, φ₁) = (φ₀ + φ₁, φ₁)`, and `A = S⁻¹`:
* the emitted data are exactly the transforms of `Micro`'s (`ham_eq`, `emb_eq`, and `box_eq` in
  `MicroRotFreq`), so `MicroRot`'s Hamiltonian is `Micro`'s composed with `L` (`H_eq`), its
  embedding is `L⁻¹ ∘ Micro.K ∘ S` (`K_eq`), its reference vector is `A ω*` (`ωstar_eq`);
* `invariance`: `invarianceError_comp` instantiated, the invariance error of `MicroRot` at
  `A ω` is `L⁻¹` of that of `Micro` at `ω`, at `S θ` (in particular at the reference vectors,
  `invariance_ref`);
* the two independently checked residual claims are consistent: on the strip `ρ / 2` (which `S`
  maps into `Micro`'s strip `ρ`) the rotated residual is bounded by its own claim and by twice
  `Micro`'s (`residual_consistent`, from `checkInvariance_sound` of each certificate and
  `‖L⁻¹‖ ≤ 2`);
* both certificates pass the v2 certifier at the landed sharp engine (and frozen A, frozen B),
  and `rot_tori` gives both certified tori;
* `torus_back`: the certified torus of `MicroRot` transported back, `L ∘ K_∞ ∘ A`, is an
  invariant torus of `Micro`'s Hamiltonian at `s_∞ ω*` with energy `E₀` on the strip `ρ_∞ / 2`,
  within `2 disp` of `Micro`'s approximate torus.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Linear

/-- Real data are equal when their constant terms and half lists agree (Boolean list check). -/
theorem realPoly_eq {P Q : CertRealPoly FB} (hz : P.zero = Q.zero)
    (hh : termsBeq P.half Q.half = true) : P = Q := by
  obtain ⟨z, h⟩ := P
  obtain ⟨z', h'⟩ := Q
  simp only at hz hh
  rw [hz, eq_of_termsBeq hh]

/-- The emitted Hamiltonian is the sheared expression of `Micro`'s. -/
theorem ham_eq : cert.ham = hamShear Micro.cert.ham := rfl

theorem u_eq : u = polyShear Micro.u := realPoly_eq (by decide +kernel) (by decide +kernel)

theorem p_eq : p = polyShear Micro.p := realPoly_eq (by decide +kernel) (by decide +kernel)

theorem P1_eq : P1 = polyAdd (polyShear Micro.p) (polyShear Micro.J) :=
  realPoly_eq (by decide +kernel) (by decide +kernel)

/-- The emitted embedding is the sheared embedding of `Micro`'s. -/
theorem emb_eq : cert.emb = embShear (-1) 0 0 Micro.u Micro.p Micro.J := by
  rw [show cert.emb = embForced (-1) 0 0 u p P1 from rfl, u_eq, p_eq, P1_eq]
  rfl

/-- **The Hamiltonian**: `MicroRot.H = Micro.H ∘ L`. -/
theorem H_eq : cert.H = Micro.cert.H ∘ shearMap := by
  funext z
  rw [TorusCertificate.H, ham_eq, eval_hamShear]
  rfl

/-- **The embedding**: `MicroRot.K = L⁻¹ ∘ Micro.K ∘ S`. -/
theorem K_eq : cert.K = shearMapInv ∘ Micro.cert.K ∘ shearAngle := by
  funext θ
  rw [TorusCertificate.K, emb_eq, eval_embShear]
  rfl

/-- **The reference vector**: `MicroRot.ωstar = A Micro.ωstar`. -/
theorem ωstar_eq : (fun i => (ωstar i : ℂ)) = angleCLE fun i => (Micro.ωstar i : ℂ) := by
  ext i
  fin_cases i <;> simp [ωstar, shearAngleInv]

/-- **The checked transformation**: the invariance error of `MicroRot` at `A ω` is `L⁻¹` of the
invariance error of `Micro` at `ω`, evaluated at `S θ` (`invarianceError_comp`). -/
theorem invariance (ω : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    invarianceError cert.H cert.K ![ω 0 - ω 1, ω 1] θ =
      shearMapInv (invarianceError Micro.cert.H Micro.cert.K ω (shearAngle θ)) := by
  rw [H_eq, K_eq]
  exact invarianceError_shear _ _ ω θ

/-- At the reference vectors and the common ray parameter `s`. -/
theorem invariance_ref (θ : Fin 2 → ℂ) :
    invarianceError cert.H cert.K ((cert.params.s : ℝ) • ωstar) θ =
      shearMapInv (invarianceError Micro.cert.H Micro.cert.K
        ((Micro.cert.params.s : ℝ) • Micro.ωstar) (shearAngle θ)) := by
  have hs : cert.params.s = Micro.cert.params.s := by decide +kernel
  have h : (cert.params.s : ℝ) • ωstar = ![((Micro.cert.params.s : ℝ) • Micro.ωstar) 0 -
      ((Micro.cert.params.s : ℝ) • Micro.ωstar) 1,
      ((Micro.cert.params.s : ℝ) • Micro.ωstar) 1] := by
    rw [hs]
    ext i
    fin_cases i <;> simp [ωstar]
    ring
  rw [h]
  exact invariance _ θ

/-- **The two checked residual claims are consistent**: on the strip `ρ / 2` the residual of
`MicroRot` is bounded by its own checked claim and, through the transformation, by twice
`Micro`'s checked claim. -/
theorem residual_consistent (θ : Fin 2 → ℂ) (hθ : θ ∈ complexStrip 2 ((cert.params.rho : ℝ) / 2)) :
    ‖invarianceError cert.H cert.K ((cert.params.s : ℝ) • ωstar) θ‖ ≤ cert.params.err ∧
      ‖invarianceError cert.H cert.K ((cert.params.s : ℝ) • ωstar) θ‖ ≤
        2 * (Micro.cert.params.err : ℝ) := by
  have hρ : cert.params.rho = Micro.cert.params.rho := by decide +kernel
  have hρ0 : (0 : ℝ) ≤ cert.params.rho := by
    have : (0 : ℚ) ≤ cert.params.rho := by decide +kernel
    exact_mod_cast this
  refine ⟨checkInvariance_sound static_ok hamBounds_ok embedding_ok invariance_ok freq θ ?_, ?_⟩
  · intro i
    exact (hθ i).trans_le (by linarith)
  · have hS : shearAngle θ ∈ complexStrip 2 (Micro.cert.params.rho : ℝ) := by
      rw [← hρ]; exact shearAngle_mem_complexStrip hθ
    have hM := checkInvariance_sound Micro.static_ok Micro.hamBounds_ok Micro.embedding_ok
      Micro.invariance_ok Micro.freq (shearAngle θ) hS
    rw [invariance_ref]
    exact (norm_shearMapInv_le _).trans (by linarith)

/-- **Both normalizations are certified** (the landed sharp engine): the tori of `Micro` at `ω*`
and of `MicroRot` at `A ω*`. -/
theorem rot_tori : CertifiedTorus Micro.cert Micro.ωstar ∧
    CertifiedTorus cert ![Micro.ωstar 0 - Micro.ωstar 1, Micro.ωstar 1] :=
  ⟨Micro.sharp_torus, sharp_torus⟩

/-- **Transport back**: the certified torus `K_∞` of `MicroRot` gives the torus `L ∘ K_∞ ∘ A` of
`Micro`'s Hamiltonian at `s_∞ ω*` (`invarianceError_shear_symm`), invariant with energy `E₀` on
the strip `ρ_∞ / 2` (which `A` maps into the strip `ρ_∞`), with `1 < s_∞ < σ_ω`, within
`2 disp` of `Micro`'s approximate torus there (`‖L‖ ≤ 2`). -/
theorem torus_back : ∃ (Kb : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < cert.params.σω ∧
    (∀ θ ∈ complexStrip 2 ((cert.params.rhoInf : ℝ) / 2),
      invarianceError Micro.cert.H Kb (sinf • Micro.ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip 2 ((cert.params.rhoInf : ℝ) / 2),
      Micro.cert.H (Kb θ) = ((cert.params.E0 : ℝ) : ℂ)) ∧
    ∀ θ ∈ complexStrip 2 ((cert.params.rhoInf : ℝ) / 2),
      ‖Kb θ - Micro.cert.K θ‖ ≤ 2 * (cert.params.disp : ℝ) := by
  obtain ⟨Kinf, sinf, h1, h2, -, -, -, hinv, hen, -, -, hdisp, -⟩ := sharp_torus
  have hA : ∀ θ ∈ complexStrip 2 ((cert.params.rhoInf : ℝ) / 2),
      shearAngleInv θ ∈ complexStrip 2 (cert.params.rhoInf : ℝ) := by
    intro θ hθ i
    have h0 := hθ 0
    have h1 := hθ 1
    fin_cases i
    · simp only [shearAngleInv, Fin.zero_eta, Matrix.cons_val_zero, Complex.sub_im]
      exact (abs_sub _ _).trans_lt (by linarith)
    · simp only [shearAngleInv, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : 0 ≤ |(θ 0).im| := abs_nonneg _
      linarith
  refine ⟨shearMap ∘ Kinf ∘ shearAngleInv, sinf, h1, h2, fun θ hθ => ?_, fun θ hθ => ?_,
    fun θ hθ => ?_⟩
  · have hω : sinf • ωstar = ![(sinf • Micro.ωstar) 0 - (sinf • Micro.ωstar) 1,
        (sinf • Micro.ωstar) 1] := by
      ext i
      fin_cases i <;> simp [ωstar]
      ring
    rw [invarianceError_shear_symm, ← hω, ← H_eq, hinv _ (hA θ hθ)]
    exact map_zero shearCLE
  · have h := hen _ (hA θ hθ)
    rw [H_eq] at h
    exact h
  · have hK : Micro.cert.K θ = shearMap (cert.K (shearAngleInv θ)) := by
      rw [K_eq]
      simp only [Function.comp_apply]
      rw [show shearAngle (shearAngleInv θ) = θ from angleCLE.symm_apply_apply θ]
      exact (shearCLE.apply_symm_apply _).symm
    have hsub : (shearMap ∘ Kinf ∘ shearAngleInv) θ - Micro.cert.K θ =
        shearMap (Kinf (shearAngleInv θ) - cert.K (shearAngleInv θ)) := by
      rw [hK]
      exact (map_sub shearCLE _ _).symm
    rw [hsub]
    exact (norm_shearMap_le _).trans (by linarith [hdisp _ (hA θ hθ)])

end KAM.CertificateSharp.V2.Forced.MicroRot

end
