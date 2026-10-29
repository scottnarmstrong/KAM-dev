/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff

/-!
# Planar quartic torsion: clause (a) of `birkhoff_form` and the explicit lift map (package GAP-D)

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form` clause (a), `bpP:p11b:lift-map`).  Append-only gap
fill after T16: unsigned lemmas that only consume `birkhoff_form`.

* `birkhoff_form_hamiltonian`: for the map `T` of `birkhoff_form`, on the tube the pullbacks
  `f̂ ∘ T` (`f̂ ∈ {f̂_fix, f̂_mov}`) are real analytic, `2π`-periodic in the angles, and
  `H^Ψ ∘ T = h(Λ) + μ (f̂ ∘ T)` for the moving and fixed physical Hamiltonians in the Poincaré
  product chart.  The identity is the consumer deduction from `movingHamiltonian_poincareProd` and
  `fixedHamiltonian_poincareProd` (action preservation and image in the product-chart domain).
* `lift_map_explicit`: `T (λ, Λ, z) = (λ + g(Λ, z) + H(Λ, Y), Λ, ρ(Λ) Y)` for
  `T = p11c_rotationLift ∘ p11c_liftFlow chi`, with `g` the time integral of `∂_Λ chi` along the
  flow and `H` the frame-rotation angle correction.
* `lift_map_properties`: with the three properties of the node (analytic symplectic chart,
  injectivity, action preservation, commutation with angle translations) for the `T` of
  `birkhoff_form`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- The moving/fixed Hamiltonian splits at a point of the tube, from the product-chart exports. -/
theorem p11cG_split (p : PlanarData) (hp : p.Valid) {w v : Phase (2 + 2)}
    (hact : (fun i => v.2 (Fin.castAdd 2 i)) = fun i => w.2 (Fin.castAdd 2 i))
    (hv : v ∈ poincareProdDom 2) :
    (∀ μ : ℝ, movingHamiltonian p.G p.m0 p.m μ (poincareProd p.m p.kappa v) =
        hProd p.kappa p.m w + μ * p11c_hatMov p v) ∧
      ∀ ε : ℝ, fixedHamiltonian p.G p.m0 p.m ε (poincareProd p.m p.kappa v) =
        hProd p.kappa p.m w + ε * p11c_hatFix p v := by
  obtain ⟨hG, hm0, hm⟩ := hp
  have hκ : 0 < p.G * p.m0 := mul_pos hG hm0
  have hh : hProd p.kappa p.m v = hProd p.kappa p.m w := by
    unfold hProd
    have : ∀ i, fast v.2 i = fast w.2 i := fun i => congrFun hact i
    simp only [this]
  refine ⟨fun μ => ?_, fun ε => ?_⟩
  · have := movingHamiltonian_poincareProd (G := p.G) (m0 := p.m0) (μ := μ) hm hκ hv
    exact this.trans (by rw [← hh]; rfl)
  · have := fixedHamiltonian_poincareProd (G := p.G) (m0 := p.m0) (ε := ε) hm hκ hv
    exact this.trans (by rw [← hh]; rfl)

/-- Angle periodicity of the pullback of a function of the Poincaré product chart. -/
theorem p11cG_periodic (p : PlanarData) (hp : p.Valid) (f : Phase (2 * 2) → ℝ)
    {T : Phase (2 + 2) → Phase (2 + 2)} {w : Phase (2 + 2)} (k : Fin 2 → ℤ)
    (hT : T (w + fastShift (a := 2) (b := 2) k) = T w + fastShift (a := 2) (b := 2) k)
    (hv : T w ∈ poincareProdDom 2) :
    (f ∘ poincareProd p.m p.kappa) (T (w + fastShift (a := 2) (b := 2) k)) =
      (f ∘ poincareProd p.m p.kappa) (T w) := by
  obtain ⟨_, hG, hm0, hm⟩ : True ∧ 0 < p.G ∧ 0 < p.m0 ∧ ∀ i, 0 < p.m i :=
    ⟨trivial, hp.1, hp.2.1, hp.2.2⟩
  have hκ : 0 < p.kappa := mul_pos hG hm0
  simp only [comp_apply, hT]
  rw [(poincareProd_lattice hm hκ hv k).2]

/-- `bpP:p11b:birkhoff-form`, clause (a): for the map `T` of `birkhoff_form`, the pullbacks of both
physical perturbations are real analytic and `2π`-periodic in the angles on the tube, and
`H^Ψ ∘ T = h(Λ) + μ (f̂ ∘ T)` for the moving and the fixed Hamiltonian. -/
theorem birkhoff_form_hamiltonian (p : PlanarData) (hp : p.Valid)
    (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hgoodK : closedBall a0 rho ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0}) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ Oa : Set (Fin 2 → ℝ),
      IsOpen Oa → closedBall a0 rho ⊆ Oa →
      Oa ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0} →
      ∃ O' : Set (Fin 2 → ℝ), IsOpen O' ∧ p.actions '' closedBall a0 rho ⊆ O' ∧
        IsCompact (closure O') ∧ closure O' ⊆ p.actions '' Oa ∧
        ∃ T : Phase (2 + 2) → Phase (2 + 2),
          (∃ chi : QuarticFamily O', T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval) ∧
          (∀ w ∈ p11c_tube O' r, (fun i => (T w).2 (Fin.castAdd 2 i)) =
            fun i => w.2 (Fin.castAdd 2 i)) ∧
          (∀ w ∈ p11c_tube O' r, T w ∈ poincareProdDom 2 ∧
            NoCollision (poincareProd p.m p.kappa (T w)).1) ∧
          ∀ fhat ∈ ({p11c_hatFix p, p11c_hatMov p} : Set (Phase (2 + 2) → ℝ)),
            AnalyticOnNhd ℝ (fhat ∘ T) (p11c_tube O' r) ∧
            (∀ w ∈ p11c_tube O' r, ∀ k : Fin 2 → ℤ,
              (fhat ∘ T) (w + fastShift (a := 2) (b := 2) k) = (fhat ∘ T) w) ∧
            (fhat = p11c_hatMov p → ∀ w ∈ p11c_tube O' r, ∀ μ : ℝ,
              movingHamiltonian p.G p.m0 p.m μ (poincareProd p.m p.kappa (T w)) =
                hProd p.kappa p.m w + μ * (fhat ∘ T) w) ∧
            (fhat = p11c_hatFix p → ∀ w ∈ p11c_tube O' r, ∀ ε : ℝ,
              fixedHamiltonian p.G p.m0 p.m ε (poincareProd p.m p.kappa (T w)) =
                hProd p.kappa p.m w + ε * (fhat ∘ T) w) := by
  obtain ⟨r, C, hr, hC, h⟩ := birkhoff_form p hp a0 rho hgoodK
  refine ⟨r, C, hr, hC, fun Oa hOa hK hOg => ?_⟩
  obtain ⟨O', hO', hKO, hcpt, hcl, F, chi, _, _, T, hT, _, hch, _, hact, htr, hdom, hf⟩ :=
    h Oa hOa hK hOg
  refine ⟨O', hO', hKO, hcpt, hcl, T, ⟨chi, hT⟩, hact, hdom, fun fhat hmem => ?_⟩
  have hper : ∀ w ∈ p11c_tube O' r, ∀ k : Fin 2 → ℤ, (fhat ∘ T) (w + fastShift (a := 2) (b := 2) k)
      = (fhat ∘ T) w := by
    intro w hw k
    have hv := (hdom w hw).1
    have hT' := htr w hw (fun i => 2 * Real.pi * (k i : ℝ))
    have hfh : ∃ f : Phase (2 * 2) → ℝ, fhat = f ∘ poincareProd p.m p.kappa := by
      rcases hmem with rfl | rfl
      · exact ⟨fFix p.G p.m, rfl⟩
      · exact ⟨fMov p.G p.m0 p.m, rfl⟩
    obtain ⟨f, rfl⟩ := hfh
    exact p11cG_periodic p hp f k hT' hv
  refine ⟨(hf fhat hmem).1, hper, ?_, ?_⟩
  · rintro rfl w hw μ
    exact (p11cG_split p hp (hact w hw) (hdom w hw).1).1 μ
  · rintro rfl w hw ε
    exact (p11cG_split p hp (hact w hw) (hdom w hw).1).2 ε

/-- `bpP:p11b:lift-map`, explicit form: `T (λ, Λ, z) = (λ + g(Λ, z) + H(Λ, Y), Λ, ρ(Λ) Y)` for
`T = Φ_ρ⁻¹ ∘ Φ_χ`, where `Y = φ¹_χ(Λ, z)`, `g_l = ∫₀¹ ∂_{Λ_l} χ(Λ, φᵗ_χ(Λ, z)) dt` and
`H_l(Λ, Y) = ỹᵀ (ρᵀ ∂_{Λ_l} ρ) x̃` with `ρ = p11c_frame p (p.axes Λ)`. -/
theorem lift_map_explicit (p : PlanarData) (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (I φ : Fin 2 → ℝ)
    (z : Phase 2) :
    (p11c_rotationLift p ∘ p11c_liftFlow chi) (assemble I φ z.2 z.1) =
      assemble I
        (φ + (fun l => ∫ t in (0 : ℝ)..1,
            fderiv ℝ (fun J => chi J (p11c_flow chi I t z)) I (Pi.single l 1)) +
          fun l => ∑ i, ∑ j, ∑ k, (p11c_flow chi I 1 z).2 i * p11c_frame p (p.axes I) k i *
            fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) *
              (p11c_flow chi I 1 z).1 j)
        (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi I 1 z)).2
        (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi I 1 z)).1 := by
  have h1 : p11c_liftFlow chi (assemble I φ z.2 z.1) =
      assemble I (φ + fun l => ∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun J => chi J (p11c_flow chi I t z)) I (Pi.single l 1))
        (p11c_flow chi I 1 z).2 (p11c_flow chi I 1 z).1 := by
    rw [p11cL_liftFlow_eq, p11cL_act_assemble, p11cL_ang_assemble, p11cL_slow_assemble]
  show p11c_rotationLift p (p11c_liftFlow chi (assemble I φ z.2 z.1)) = _
  rw [h1, p11cB_rotationLift_assemble, add_assoc]

/-- `bpP:p11b:lift-map`: for the `T` of `birkhoff_form`, with `chi` the homological solution,
`T` is the explicit map of `lift_map_explicit` (so `T (λ, Λ, z) = (λ + g + H, Λ, ρ Y)`), a real
analytic symplectic chart that is injective on the tube, preserves `Λ` and commutes with angle
translations. -/
theorem lift_map_properties (p : PlanarData) (hp : p.Valid)
    (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hgoodK : closedBall a0 rho ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0}) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ Oa : Set (Fin 2 → ℝ),
      IsOpen Oa → closedBall a0 rho ⊆ Oa →
      Oa ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0} →
      ∃ O' : Set (Fin 2 → ℝ), IsOpen O' ∧ p.actions '' closedBall a0 rho ⊆ O' ∧
        IsCompact (closure O') ∧ closure O' ⊆ p.actions '' Oa ∧
        ∃ (chi : QuarticFamily O') (T : Phase (2 + 2) → Phase (2 + 2)),
          T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval ∧
          (∀ I φ : Fin 2 → ℝ, ∀ z : Phase 2,
            T (assemble I φ z.2 z.1) =
              assemble I
                (φ + (fun l => ∫ t in (0 : ℝ)..1,
                    fderiv ℝ (fun J => chi.eval J (p11c_flow chi.eval I t z)) I
                      (Pi.single l 1)) +
                  fun l => ∑ i, ∑ j, ∑ k, (p11c_flow chi.eval I 1 z).2 i *
                    p11c_frame p (p.axes I) k i *
                    fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) *
                      (p11c_flow chi.eval I 1 z).1 j)
                (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi.eval I 1 z)).2
                (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi.eval I 1 z)).1) ∧
          IsChart 1 T (p11c_tube O' r) ∧ InjOn T (p11c_tube O' r) ∧
          (∀ w ∈ p11c_tube O' r, (fun i => (T w).2 (Fin.castAdd 2 i)) =
            fun i => w.2 (Fin.castAdd 2 i)) ∧
          ∀ w ∈ p11c_tube O' r, ∀ c : Fin 2 → ℝ,
            T (w + (Fin.append c 0, 0)) = T w + (Fin.append c 0, 0) := by
  obtain ⟨r, C, hr, hC, h⟩ := birkhoff_form p hp a0 rho hgoodK
  refine ⟨r, C, hr, hC, fun Oa hOa hK hOg => ?_⟩
  obtain ⟨O', hO', hKO, hcpt, hcl, F, chi, _, _, T, hT, _, hch, hinj, hact, htr, _⟩ :=
    h Oa hOa hK hOg
  refine ⟨O', hO', hKO, hcpt, hcl, chi, T, hT, ?_, hch, hinj, hact, htr⟩
  intro I φ z
  rw [hT]
  exact lift_map_explicit p chi.eval I φ z

end KAM.Planetary

end
