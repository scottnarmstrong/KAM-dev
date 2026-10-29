/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Mass
public import KAM.Kepler.Means

/-!
# Kepler scaling: literal exports of the graph nodes

Graph-gap package GAP-P7 (append-only).  Each theorem states the literal conclusion of one node of
the dependency graph, built from the landed declarations of `KAM.Kepler.Energy`, `KAM.Kepler.Orbit`,
`KAM.Kepler.Means` and `KAM.Kepler.Mass`:

* `ci_alg` (`stepI:p7:ci-alg`): the orbit formulas and the three means extend to `e = 0`;
* `sc_alg` (`stepI:p7:sc-alg`): `E_k ∘ S_k = k² E₁`, `DS_k = diag (k⁻¹, k⁻¹, k, k)`, `S_k`
  symplectic of factor one;
* `sc_flow` (`stepI:p7:sc-flow`): the two field identities, the time change, `a_k = a / k` and the
  scaled means;
* `rg_scale` (`stepP:p7:rg-scale`): scaling a physical Kepler point to strength one.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

/-! ### Linear structure of `S_k` -/

private def sclCLM (k : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (k⁻¹ • ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    (k • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

private theorem scaleMK_one_eq_clm (k : ℝ) : scaleMK 1 k = sclCLM k := by
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [scaleMK, sclCLM]

private theorem planeSq_analyticAt (v : Fin 2 → ℝ) : AnalyticAt ℝ planeSq v := by
  have h : planeSq = fun w : Fin 2 → ℝ => w 0 ^ 2 + w 1 ^ 2 :=
    funext fun w => by simp [planeSq, Fin.sum_univ_two]
  rw [h]
  have h0 : AnalyticAt ℝ (fun w : Fin 2 → ℝ => w 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt v
  have h1 : AnalyticAt ℝ (fun w : Fin 2 → ℝ => w 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).analyticAt v
  exact (h0.pow 2).add (h1.pow 2)

private theorem differentiableAt_kE_of_pos {z : Phase 2} (hz : 0 < planeLength z.1) :
    DifferentiableAt ℝ kE z := by
  have hv : z.1 ≠ 0 := planeLength_pos_iff.mp hz
  have hs : AnalyticAt ℝ (fun x : Phase 2 => planeSq x.2) z :=
    (planeSq_analyticAt z.2).comp
      ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).analyticAt z)
  have hi : AnalyticAt ℝ (fun x : Phase 2 => (planeLength x.1)⁻¹) z :=
    (analyticAt_inv_planeLength hv).comp
      ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).analyticAt z)
  have h : AnalyticAt ℝ (fun x : Phase 2 => planeSq x.2 / 2 - (planeLength x.1)⁻¹) z :=
    hs.div_const.sub hi
  have e : kE = fun x : Phase 2 => planeSq x.2 / 2 - (planeLength x.1)⁻¹ :=
    funext fun x => by simp [kE, one_div]
  rw [e]
  exact h.differentiableAt

private theorem differentiableAt_energyMK_of_pos {κ : ℝ} {z : Phase 2} (hz : 0 < planeLength z.1) :
    DifferentiableAt ℝ (energyMK 1 κ) z := by
  have hv : z.1 ≠ 0 := planeLength_pos_iff.mp hz
  have hs : AnalyticAt ℝ (fun x : Phase 2 => planeSq x.2) z :=
    (planeSq_analyticAt z.2).comp
      ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).analyticAt z)
  have hi : AnalyticAt ℝ (fun x : Phase 2 => (planeLength x.1)⁻¹) z :=
    (analyticAt_inv_planeLength hv).comp
      ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).analyticAt z)
  have h : AnalyticAt ℝ
      (fun x : Phase 2 => planeSq x.2 / (2 * 1) - κ * 1 * (planeLength x.1)⁻¹) z :=
    hs.div_const.sub (analyticAt_const.mul hi)
  have e : energyMK 1 κ =
      fun x : Phase 2 => planeSq x.2 / (2 * 1) - κ * 1 * (planeLength x.1)⁻¹ :=
    funext fun x => by simp [energyMK, div_eq_mul_inv]
  rw [e]
  exact h.differentiableAt

private theorem planeLength_scaleMK_fst {κ : ℝ} (hκ : 0 < κ) (z : Phase 2) :
    planeLength (scaleMK 1 κ z).1 = κ⁻¹ * planeLength z.1 := by
  simp only [scaleMK, planeLength_smul, abs_inv, abs_of_pos hκ]

private theorem hamiltonianVectorField_const_mul' {c : ℝ} {H : Phase 2 → ℝ} {z : Phase 2}
    (hH : DifferentiableAt ℝ H z) :
    hamiltonianVectorField (fun w => c * H w) z = c • hamiltonianVectorField H z := by
  have h := fderiv_const_mul hH c
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [hamiltonianVectorField, h]

/-! ### `stepI:p7:sc-alg` -/

/-- `stepI:p7:sc-alg`: for `k > 0`, `E_k (S_k z) = k² E₁ z`, `DS_k = diag (k⁻¹, k⁻¹, k, k)` and
`DS_kᵀ J DS_k = J` (as invariance of the symplectic form).  No restriction `Q ≠ 0` is needed. -/
theorem sc_alg {k : ℝ} (hk : 0 < k) :
    (∀ z : Phase 2, energyMK 1 k (scaleMK 1 k z) = k ^ 2 * kE z) ∧
    (∀ x u : Phase 2, fderiv ℝ (scaleMK 1 k) x u = (k⁻¹ • u.1, k • u.2)) ∧
    IsSymplecticOn 1 (scaleMK 1 k) univ := by
  refine ⟨fun z => ?_, fun x u => ?_, scaleMK_symplectic one_pos hk⟩
  · rw [scaleMK_energy one_pos hk, one_mul]
  · rw [scaleMK_one_eq_clm, ContinuousLinearMap.fderiv]
    rfl

/-! ### `stepI:p7:sc-flow` -/

private theorem fderiv_scaleMK_apply {k : ℝ} (hk : 0 < k) (x u : Phase 2) :
    fderiv ℝ (scaleMK 1 k) x u = scaleMK 1 k u := by
  rw [(sc_alg hk).2.1 x u]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [scaleMK]

/-- `stepI:p7:sc-flow`: the two local field identities
`DS_k X_{E_k ∘ S_k} = X_{E_k} ∘ S_k` and `k² DS_k X_{E₁} = X_{E_k} ∘ S_k` on the collision-free
domain `Q ≠ 0`; the time change (`t ↦ S_k (Q, P)(k² t)` solves `E_k`); and, for a bound Kepler orbit
of strength one with elements `L > 0`, `0 ≤ e < 1` (semi-major axis `a = L²`), the scaled semi-major
axis `a_k = a / k`, the energy `E_k = -k / (2 a_k)` and the mean values `⟨1/|q|⟩ = 1 / a_k`,
`⟨|p|²⟩ = k / a_k`. -/
theorem sc_flow {k : ℝ} (hk : 0 < k) :
    (∀ z : Phase 2, 0 < planeLength z.1 →
      fderiv ℝ (scaleMK 1 k) z (hamiltonianVectorField (energyMK 1 k ∘ scaleMK 1 k) z) =
        hamiltonianVectorField (energyMK 1 k) (scaleMK 1 k z) ∧
      k ^ 2 • fderiv ℝ (scaleMK 1 k) z (hamiltonianVectorField kE z) =
        hamiltonianVectorField (energyMK 1 k) (scaleMK 1 k z)) ∧
    (∀ (Zc : ℝ → Phase 2) (t : ℝ),
      HasDerivAt Zc (hamiltonianVectorField kE (Zc (k ^ 2 * t))) (k ^ 2 * t) →
      0 < planeLength (Zc (k ^ 2 * t)).1 →
      HasDerivAt (fun s => scaleMK 1 k (Zc (k ^ 2 * s)))
        (hamiltonianVectorField (energyMK 1 k) (scaleMK 1 k (Zc (k ^ 2 * t)))) t) ∧
    (∀ (g L e : ℝ), 0 < L → 0 ≤ e → e < 1 →
      (∀ ℓ : ℝ, elemA (orbitMapR ℓ g L e) = L ^ 2 ∧
        axisMK 1 k (scaleMK 1 k (orbitMapR ℓ g L e)) = elemA (orbitMapR ℓ g L e) / k ∧
        energyMK 1 k (scaleMK 1 k (orbitMapR ℓ g L e)) =
          -k / (2 * axisMK 1 k (scaleMK 1 k (orbitMapR ℓ g L e)))) ∧
      (2 * π)⁻¹ * (∫ ℓ in (0 : ℝ)..2 * π,
          1 / planeLength (scaleMK 1 k (orbitMapR ℓ g L e)).1) = 1 / (L ^ 2 / k) ∧
      (2 * π)⁻¹ * (∫ ℓ in (0 : ℝ)..2 * π,
          planeSq (scaleMK 1 k (orbitMapR ℓ g L e)).2) = k / (L ^ 2 / k)) := by
  refine ⟨fun z hz => ?_, fun Zc t hZ hpos => ?_, fun g L e hL he0 he1 => ?_⟩
  · have hS : 0 < planeLength (scaleMK 1 k z).1 := by
      rw [planeLength_scaleMK_fst hk]; positivity
    have hdiff := differentiableAt_energyMK_of_pos (κ := k) hS
    have key := scaleMK_hamiltonianVectorField hk hdiff
    have hcomp : energyMK 1 k ∘ scaleMK 1 k = fun w => k ^ 2 * kE w := by
      funext w; simp only [Function.comp_apply, scaleMK_energy one_pos hk w, one_mul]
    refine ⟨?_, ?_⟩
    · rw [fderiv_scaleMK_apply hk]; exact key
    · rw [hcomp, hamiltonianVectorField_const_mul' (differentiableAt_kE_of_pos hz)] at key
      rw [fderiv_scaleMK_apply hk, ← key]
      rw [scaleMK_one_eq_clm]
      exact (map_smul (sclCLM k) (k ^ 2) _).symm
  · exact scaleMK_flow hk hZ (differentiableAt_kE_of_pos hpos)
  · have hL2 : 0 < L ^ 2 := by positivity
    have hE : ∀ ℓ : ℝ, kE (orbitMapR ℓ g L e) = -1 / (2 * L ^ 2) :=
      fun ℓ => orbitMapR_energy hL he0 he1
    have hA : ∀ ℓ : ℝ, elemA (orbitMapR ℓ g L e) = L ^ 2 := fun ℓ => by
      rw [elemA, hE]; field_simp
    have hAx : ∀ ℓ : ℝ, axisMK 1 k (scaleMK 1 k (orbitMapR ℓ g L e)) = L ^ 2 / k := fun ℓ => by
      rw [axisMK, scaleMK_energy one_pos hk, hE]
      field_simp
    refine ⟨fun ℓ => ⟨hA ℓ, ?_, ?_⟩, ?_, ?_⟩
    · rw [hAx, hA]
    · rw [hAx, scaleMK_energy one_pos hk, hE]
      field_simp
    · have := (delaunayMK_means (m := 1) (κ := k) (g := g) (Λ := L) (e := e) one_pos hk hL he0
        he1).1
      simpa only [div_one, one_pow, one_mul] using this
    · have := (delaunayMK_means (m := 1) (κ := k) (g := g) (Λ := L) (e := e) one_pos hk hL he0
        he1).2.1
      simpa only [div_one, one_pow, one_mul] using this

/-! ### `stepP:p7:rg-scale` -/

/-- `stepP:p7:rg-scale`: for `(q, p) ∈ 𝒦_{m,κ}` and `(Q, P) = S_{m,κ}⁻¹ (q, p) = (κ q, p / (m κ))`:
`E₁ (Q, P) = E_{m,κ} (q, p) / (m κ²)`, `cr (Q, P) = C / m` and
`Λ / m = √(-1 / (2 E₁ (Q, P)))` with `Λ` the physical action. -/
theorem rg_scale {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2} (hz : z ∈ regionMK m κ) :
    scaleMK m κ (κ • z.1, (m * κ)⁻¹ • z.2) = z ∧
    kE (κ • z.1, (m * κ)⁻¹ • z.2) = energyMK m κ z / (m * κ ^ 2) ∧
    planeCross (κ • z.1) ((m * κ)⁻¹ • z.2) = planeCross z.1 z.2 / m ∧
    actionMK m κ z / m = √(-1 / (2 * kE (κ • z.1, (m * κ)⁻¹ • z.2))) := by
  have hmκ : (m * κ) ≠ 0 := (mul_pos hm hκ).ne'
  have hback : scaleMK m κ (κ • z.1, (m * κ)⁻¹ • z.2) = z := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [scaleMK, smul_smul, hκ.ne']
    · simp only [scaleMK, smul_smul, Pi.smul_apply, smul_eq_mul]
      field_simp
  have hE : kE (κ • z.1, (m * κ)⁻¹ • z.2) = energyMK m κ z / (m * κ ^ 2) := by
    have h := scaleMK_energy hm hκ (κ • z.1, (m * κ)⁻¹ • z.2)
    rw [hback] at h
    rw [h]; field_simp
  refine ⟨hback, hE, ?_, ?_⟩
  · have h := scaleMK_cross hm hκ (κ • z.1, (m * κ)⁻¹ • z.2)
    rw [hback] at h
    rw [h]; field_simp
  · have hEneg : energyMK m κ z < 0 := hz.2.1
    have hEne : energyMK m κ z ≠ 0 := hEneg.ne
    have harg : κ * axisMK m κ z = -1 / (2 * kE (κ • z.1, (m * κ)⁻¹ • z.2)) := by
      rw [hE, axisMK]
      field_simp
    unfold actionMK
    rw [harg]
    field_simp

/-! ### `stepI:p7:ci-alg` -/

/-- `stepI:p7:ci-alg`: the orbit formulas (radius, speed, energy, angular momentum) and the three
means hold for all `0 ≤ e < 1` (so at `e = 0`), and at `e = 0`: `u = ℓ`, `r = L²`, `|p| = 1 / L`,
`E = -1 / (2 L²)`, `Γ = L`.  No membership in `𝒞` or chart bijectivity at `e = 0` is asserted. -/
theorem ci_alg {L : ℝ} (hL : 0 < L) (ℓ g : ℝ) :
    (∀ e : ℝ, 0 ≤ e → e < 1 →
      planeLength (orbitMapR ℓ g L e).1 = L ^ 2 * (1 - e * Real.cos (eccAnom ℓ e)) ∧
      planeSq (orbitMapR ℓ g L e).2 =
        (1 + e * Real.cos (eccAnom ℓ e)) / (L ^ 2 * (1 - e * Real.cos (eccAnom ℓ e))) ∧
      kE (orbitMapR ℓ g L e) = -1 / (2 * L ^ 2) ∧
      planeCross (orbitMapR ℓ g L e).1 (orbitMapR ℓ g L e).2 = L * √(1 - e ^ 2) ∧
      (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, 1 / planeLength (orbitMapR s g L e).1 = 1 / L ^ 2 ∧
      (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, planeSq (orbitMapR s g L e).2 = 1 / L ^ 2 ∧
      (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, planeLength (orbitMapR s g L e).1 =
        L ^ 2 * (1 + e ^ 2 / 2) ∧
      (L ^ 2 * (1 - e) ≤ planeLength (orbitMapR ℓ g L e).1 ∧
        planeLength (orbitMapR ℓ g L e).1 ≤ L ^ 2 * (1 + e)) ∧
      planeDot (orbitMapR ℓ g L e).1 (orbitMapR ℓ g L e).2 =
        L * e * Real.sin (eccAnom ℓ e)) ∧
    (eccAnom ℓ 0 = ℓ ∧ planeLength (orbitMapR ℓ g L 0).1 = L ^ 2 ∧
      planeLength (orbitMapR ℓ g L 0).2 = 1 / L ∧ kE (orbitMapR ℓ g L 0) = -1 / (2 * L ^ 2) ∧
      planeCross (orbitMapR ℓ g L 0).1 (orbitMapR ℓ g L 0).2 = L ∧
      (L ^ 2 * (1 - 0) ≤ planeLength (orbitMapR ℓ g L 0).1 ∧
        planeLength (orbitMapR ℓ g L 0).1 ≤ L ^ 2 * (1 + 0)) ∧
      planeDot (orbitMapR ℓ g L 0).1 (orbitMapR ℓ g L 0).2 =
        L * 0 * Real.sin (eccAnom ℓ 0)) := by
  refine ⟨fun e he0 he1 => ⟨orbitMapR_radius hL he0 he1, orbitMapR_speed_sq hL he0 he1,
    orbitMapR_energy hL he0 he1, orbitMapR_cross hL he0 he1,
    orbitMapR_mean_inv_radius hL he0 he1, orbitMapR_mean_speed_sq hL he0 he1,
    orbitMapR_mean_radius hL he0 he1, orbitMapR_radius_bounds hL he0 he1,
    orbitMapR_dot hL he0 he1⟩, ?_⟩
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) < 1 := one_pos
  refine ⟨eccAnom_zero_ecc ℓ, ?_, ?_, orbitMapR_energy hL h0 h1, ?_,
    orbitMapR_radius_bounds hL h0 h1, orbitMapR_dot hL h0 h1⟩
  · rw [orbitMapR_radius hL h0 h1]; ring
  · have hsq := orbitMapR_speed_sq (ℓ := ℓ) (g := g) hL h0 h1
    have hp : planeLength (orbitMapR ℓ g L 0).2 ^ 2 = (1 / L) ^ 2 := by
      rw [planeLength_sq, hsq]
      simp only [zero_mul, add_zero, sub_zero]
      field_simp
    exact (pow_left_inj₀ (planeLength_nonneg _) (by positivity) two_ne_zero).1 hp
  · rw [orbitMapR_cross hL h0 h1]; simp

end KAM.Kepler

end
