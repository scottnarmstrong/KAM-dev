/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffCalculus3

/-!
# Derivative rules of the total square root

On an open set `S` where `re f > 0`, `√f = sqrtE ∘ f` is smooth and nonvanishing, and with
`w = (√f)⁻¹` its directional derivatives to order three are

* `(√f)_u = ½ w f_u`,
* `(√f)_uv = ½ w f_uv - ¼ w³ f_u f_v`,
* `(√f)_uvw = ½ w f_uvw - ¼ w³ (f_uv f_w + f_v f_uw + f_u f_vw) + ⅜ w⁵ f_u f_v f_w`,

from `hasDerivAt_sqrtE` and the inverse rules of `KAM.Certificate.Expr.DiffCalculus3` (no new jet
primitive: `w`, `w³`, `w⁵` are products of the reciprocal of the root).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

theorem JetSmoothOn.sqrtE {S : Set Ph} {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (hpos : ∀ z ∈ S, 0 < (f z).re) : JetSmoothOn S (fun z => sqrtE (f z)) := fun z hz =>
  (contDiffAt_sqrtE (mem_slitPlane_of_re_pos (hpos z hz))).comp_contDiffWithinAt z (hf z hz)

theorem sqrtE_comp_ne_zero {S : Set Ph} {f : Ph → ℂ} (hpos : ∀ z ∈ S, 0 < (f z).re) :
    ∀ z ∈ S, sqrtE (f z) ≠ 0 := fun z hz => sqrtE_ne_zero (mem_slitPlane_of_re_pos (hpos z hz))

theorem jetDeriv_sqrtE {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) :
    Set.EqOn (jetDeriv u (fun z => sqrtE (f z)))
      (fun z => (1 / 2 : ℂ) * ((sqrtE (f z))⁻¹ * jetDeriv u f z)) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  simp only [jetDeriv]
  have := (hasDerivAt_sqrtE (hpos z hz)).comp_hasFDerivAt z h1.hasFDerivAt
  have e : fderiv ℂ (fun z => sqrtE (f z)) z = (1 / (2 * sqrtE (f z))) • fderiv ℂ f z :=
    this.fderiv
  rw [e]
  simp only [smul_apply, smul_eq_mul]
  rw [one_div, mul_inv]
  ring

theorem jetDeriv_sqrtE_inv {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) :
    Set.EqOn (jetDeriv u (fun z => (sqrtE (f z))⁻¹))
      (fun z => (-1 / 2 : ℂ) * ((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)) *
        jetDeriv u f z) S := by
  intro z hz
  rw [jetDeriv_inv hS u (hf.sqrtE hpos) (sqrtE_comp_ne_zero hpos) hz]
  beta_reduce
  rw [jetDeriv_sqrtE hS u hf hpos hz]
  ring

theorem jetDeriv_sqrtE_inv_cube {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) :
    Set.EqOn (jetDeriv u (fun z => (sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)))
      (fun z => (-3 / 2 : ℂ) * (((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹) *
        ((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹))) * jetDeriv u f z) S := by
  intro z hz
  rw [jetDeriv_inv_cube hS u (hf.sqrtE hpos) (sqrtE_comp_ne_zero hpos) hz]
  beta_reduce
  rw [jetDeriv_sqrtE hS u hf hpos hz]
  ring

theorem jetDeriv2_sqrtE {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => sqrtE (f z))))
      (fun z => (1 / 2 : ℂ) * ((sqrtE (f z))⁻¹ * jetDeriv u (jetDeriv v f) z) +
        (-1 / 4 : ℂ) * (((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)) *
          (jetDeriv u f z * jetDeriv v f z))) S := by
  intro z hz
  have hw := (hf.sqrtE hpos).inv (sqrtE_comp_ne_zero hpos)
  have hfv := hf.jetDeriv hS v
  rw [jetDeriv_congr hS u (jetDeriv_sqrtE hS v hf hpos) hz,
    jetDeriv_cmul hS u _ (hw.mul hfv) hz]
  beta_reduce
  rw [jetDeriv_mul hS u hw hfv hz]
  beta_reduce
  rw [jetDeriv_sqrtE_inv hS u hf hpos hz]
  ring

theorem jetDeriv3_sqrtE {S : Set Ph} (hS : IsOpen S) (u v w : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) :
    Set.EqOn (jetDeriv u (jetDeriv v (jetDeriv w (fun z => sqrtE (f z)))))
      (fun z => (3 / 8 : ℂ) * ((((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹) *
          ((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹))) *
          (jetDeriv u f z * (jetDeriv v f z * jetDeriv w f z))) +
        ((-1 / 4 : ℂ) * (((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)) *
          ((jetDeriv u (jetDeriv v f) z * jetDeriv w f z +
            jetDeriv v f z * jetDeriv u (jetDeriv w f) z) +
            jetDeriv u f z * jetDeriv v (jetDeriv w f) z)) +
        (1 / 2 : ℂ) * ((sqrtE (f z))⁻¹ * jetDeriv u (jetDeriv v (jetDeriv w f)) z))) S := by
  intro z hz
  have hw := (hf.sqrtE hpos).inv (sqrtE_comp_ne_zero hpos)
  have hw3 := hw.mul (hw.mul hw)
  have hfv := hf.jetDeriv hS v
  have hfw := hf.jetDeriv hS w
  have hfvw := hfw.jetDeriv hS v
  have hA : JetSmoothOn S
      (fun z => (1 / 2 : ℂ) * ((sqrtE (f z))⁻¹ * jetDeriv v (jetDeriv w f) z)) :=
    (JetSmoothOn.const S _).mul (hw.mul hfvw)
  have hB : JetSmoothOn S (fun z => (-1 / 4 : ℂ) *
      (((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)) *
        (jetDeriv v f z * jetDeriv w f z))) :=
    (JetSmoothOn.const S _).mul (hw3.mul (hfv.mul hfw))
  rw [jetDeriv_congr hS u (jetDeriv2_sqrtE hS v w hf hpos) hz, jetDeriv_add hS u hA hB hz]
  beta_reduce
  rw [jetDeriv_cmul hS u _ (hw.mul hfvw) hz, jetDeriv_cmul hS u _ (hw3.mul (hfv.mul hfw)) hz]
  beta_reduce
  rw [jetDeriv_mul hS u hw hfvw hz, jetDeriv_mul hS u hw3 (hfv.mul hfw) hz]
  beta_reduce
  rw [jetDeriv_mul hS u hfv hfw hz, jetDeriv_sqrtE_inv hS u hf hpos hz,
    jetDeriv_sqrtE_inv_cube hS u hf hpos hz]
  ring

end KAM.Certificate

end
