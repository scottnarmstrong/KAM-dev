/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Tools
public import KAM.Apost.Triangular
public import KAM.Strip.CohomologicalNodes

/-!
# The bordered triangular system: algebra, kernel lemmas and uniqueness

Blueprint node `bpI:p1:border-solve`
(HL19 Lemma 6.1), first module. The uniqueness part (d) of the lemma is split off here:

* `bordMat_mulVec`, `bordAvg_mulVec_bordSol`, `eq_bordSol_of_mulVec`, `bordSol_rows`,
  `eq_bordSol_of_rows`: the bordered average system `𝒯 (ξ₀, ξ^ω) = (⟨ηᴸ⟩ + ⟨T uᴺ⟩, η^ω + ⟨Y uᴺ⟩)`
  read off row by row (step `bs-bordered`).
* `eq_zero_of_fderiv_eq_zero`, `eq_avg_of_fderiv_eq_zero`: a holomorphic `1`-periodic function on a
  strip with `∂_ω u = 0` is constant (the uniqueness clause of `KAM.cohomological` with `g = 0`,
  step `ec-unique`).
* `border_unique`: a solution of the three equations of (b) on `T_{r-2δ}` has the frequency
  correction `ξ^ω` and the normal part `ξᴺ` of `bordSol` (step `bs-unique`); the free constant of
  `ξᴸ` is handled in `KAM.Iso.Linear.BorderSolve`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-! ### The bordered system, row by row -/

/-- The product of a bordered matrix with a vector, row by row. -/
theorem bordMat_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) (x : Fin n ⊕ Unit → ℂ) :
    bordMat A c y *ᵥ x =
      Sum.elim (A *ᵥ (x ∘ Sum.inl) + x (Sum.inr ()) • c) (fun _ => y ⬝ᵥ (x ∘ Sum.inl)) := by
  rw [bordMat, Matrix.fromBlocks_mulVec]
  ext (a | u)
  · simp [Matrix.mulVec, dotProduct, mul_comm]
  · simp [Matrix.mulVec, dotProduct]

/-- The bordered average system `𝒯 (ξ₀, ξ^ω) = rhs` holds for `bordSol`. -/
theorem bordAvg_mulVec_bordSol (ω : Fin n → ℝ) (d : BordData n)
    (hinv : IsUnit (bordAvg ω d).det) :
    bordAvg ω d *ᵥ bordSol ω d =
      Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
        (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) := by
  rw [bordSol, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec]

/-- Uniqueness for the bordered average system: `𝒯 x = rhs` forces `x = bordSol`. -/
theorem eq_bordSol_of_mulVec (ω : Fin n → ℝ) (d : BordData n)
    (hinv : IsUnit (bordAvg ω d).det) {x : Fin n ⊕ Unit → ℂ}
    (hx : bordAvg ω d *ᵥ x =
      Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
        (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ))) :
    x = bordSol ω d := by
  rw [bordSol, ← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]

/-- The two block rows of the bordered average system for `(ξ₀, ξ^ω) = bordSol` (step
`bs-bordered`, (6.10) of HL19). -/
theorem bordSol_rows (ω : Fin n → ℝ) (d : BordData n) (hinv : IsUnit (bordAvg ω d).det) :
    avg d.T *ᵥ bordXi0 ω d + bordXiOmega ω d • (fun a => (ω a : ℂ)) =
        avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ) ∧
      avg d.Y ⬝ᵥ bordXi0 ω d = d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ) := by
  have h := bordAvg_mulVec_bordSol ω d hinv
  have e : bordSol ω d ∘ Sum.inl = bordXi0 ω d := rfl
  have e' : bordSol ω d (Sum.inr ()) = bordXiOmega ω d := rfl
  rw [bordAvg, bordMat_mulVec, e, e'] at h
  refine ⟨funext fun a => ?_, ?_⟩
  · simpa using congrFun h (Sum.inl a)
  · simpa using congrFun h (Sum.inr ())

/-- The bordered average system read backwards: constants `(c, ξω)` solving the two block rows are
`(ξ₀, ξ^ω)`. -/
theorem eq_bordSol_of_rows (ω : Fin n → ℝ) (d : BordData n) (hinv : IsUnit (bordAvg ω d).det)
    {c : Fin n → ℂ} {ξω : ℂ}
    (h1 : avg d.T *ᵥ c + ξω • (fun a => (ω a : ℂ)) =
      avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
    (h2 : avg d.Y ⬝ᵥ c = d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) :
    c = bordXi0 ω d ∧ ξω = bordXiOmega ω d := by
  have hx : bordAvg ω d *ᵥ Sum.elim c (fun _ => ξω) =
      Sum.elim (avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ))
        (fun _ => d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ)) := by
    rw [bordAvg, bordMat_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_inr]
    rw [h1, h2]
  have h := eq_bordSol_of_mulVec ω d hinv hx
  exact ⟨funext fun a => by simpa [bordXi0] using congrFun h (Sum.inl a),
    by simpa [bordXiOmega] using congrFun h (Sum.inr ())⟩

/-! ### Averages -/

section Average

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Functions that agree on a strip of positive width have the same average. -/
theorem avg_congr {f g : (Fin n → ℂ) → F} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ θ ∈ complexStrip n ρ, f θ = g θ) : avg f = avg g :=
  congrArg torusAverage (funext fun x => h _ (ofReal_mem_complexStrip hρ x))

variable [CompleteSpace F] in
/-- The average of a constant is the constant. -/
theorem avg_const (c : F) : avg (fun _ : Fin n → ℂ => c) = c := by
  unfold avg torusAverage
  rw [setIntegral_const, measureReal_def, volume_unitCube]
  simp

/-- Averaging is additive on functions that are continuous along the real torus. -/
theorem avg_add_of_continuous {f g : (Fin n → ℂ) → F}
    (hf : Continuous fun x : Fin n → ℝ => f (fun i => (x i : ℂ)))
    (hg : Continuous fun x : Fin n → ℝ => g (fun i => (x i : ℂ))) :
    avg (fun θ => f θ + g θ) = avg f + avg g :=
  integral_add (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

/-- Averaging is subtractive on functions that are continuous along the real torus. -/
theorem avg_sub_of_continuous {f g : (Fin n → ℂ) → F}
    (hf : Continuous fun x : Fin n → ℝ => f (fun i => (x i : ℂ)))
    (hg : Continuous fun x : Fin n → ℝ => g (fun i => (x i : ℂ))) :
    avg (fun θ => f θ - g θ) = avg f - avg g :=
  integral_sub (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

end Average

/-- Averaging commutes with the dot product against a constant vector. -/
theorem avg_dotProduct_const {Y : (Fin n → ℂ) → Fin n → ℂ}
    (hY : Continuous fun x : Fin n → ℝ => Y (fun i => (x i : ℂ))) (v : Fin n → ℂ) :
    avg (fun θ => Y θ ⬝ᵥ v) = avg Y ⬝ᵥ v := by
  let L : (Fin n → ℂ) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun a => a ⬝ᵥ v
      map_add' := fun a b => add_dotProduct a b v
      map_smul' := fun c a => by simp [smul_dotProduct] }
  exact L.integral_comp_comm (μ := volume.restrict (Set.pi Set.univ
    fun _ : Fin n => Set.Icc (0 : ℝ) 1)) (φ := fun x : Fin n → ℝ => Y (fun i => (x i : ℂ)))
    (integrableOn_unitCube_of_continuous hY)

/-! ### Kernel of `∂_ω` -/

/-- A holomorphic `1`-periodic function with zero average and `∂_ω u = 0` on a strip vanishes there
(the uniqueness clause of `KAM.cohomological` with `g = 0`; step `ec-unique`). -/
theorem eq_zero_of_fderiv_eq_zero {γ τ : ℝ} {ω : Fin n → ℝ} (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hdio : IsDiophantine γ τ ω) {ρ : ℝ} (hρ : 0 < ρ) {p : ℕ} {u : (Fin n → ℂ) → Fin p → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ)) (hup : IsPeriodicOn u ρ) (hu0 : avg u = 0)
    (hd : ∀ θ ∈ complexStrip n ρ, fderiv ℂ u θ (fun l => (ω l : ℂ)) = 0) :
    ∀ θ ∈ complexStrip n ρ, u θ = 0 := by
  obtain ⟨-, hvec⟩ := KAM.cohomological hdio hγ hτ (zero_lt_one' ℝ)
    (show (1 : ℝ) < ρ + 1 by linarith)
  have hg0 : torusAverage (fun x : Fin n → ℝ =>
      (fun _ : Fin n → ℂ => (0 : Fin p → ℂ)) fun j => (x j : ℂ)) = 0 := by
    simp [torusAverage]
  obtain ⟨-, -, -, -, -, -, huniq⟩ := hvec (p := p) (fun _ => (0 : Fin p → ℂ)) 0
    (differentiableOn_const _) (fun _ _ _ => rfl) (fun _ _ => by simp) hg0
  simp only [add_sub_cancel_right] at huniq
  intro θ hθ
  have h1 := huniq u hu hup hu0 hd θ hθ
  have h2 := huniq (fun _ => 0) (differentiableOn_const _) (fun _ _ _ => rfl) hg0
    (fun θ _ => by simp) θ hθ
  rw [h1, ← h2]

/-- A holomorphic `1`-periodic function with `∂_ω u = 0` on a strip equals its average there. -/
theorem eq_avg_of_fderiv_eq_zero {γ τ : ℝ} {ω : Fin n → ℝ} (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hdio : IsDiophantine γ τ ω) {ρ : ℝ} (hρ : 0 < ρ) {p : ℕ} {u : (Fin n → ℂ) → Fin p → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ)) (hup : IsPeriodicOn u ρ)
    (hd : ∀ θ ∈ complexStrip n ρ, fderiv ℂ u θ (fun l => (ω l : ℂ)) = 0) :
    ∀ θ ∈ complexStrip n ρ, u θ = avg u := by
  have hc : Continuous fun x : Fin n → ℝ => u (fun i => (x i : ℂ)) :=
    Triangular.continuous_ofReal_comp hρ hu
  have hw0 : avg (fun θ => u θ - avg u) = 0 := by
    rw [avg_sub_of_continuous hc continuous_const, avg_const, sub_self]
  intro θ hθ
  have := eq_zero_of_fderiv_eq_zero hγ hτ hdio hρ (u := fun θ => u θ - avg u)
    (hu.sub (differentiableOn_const _)) (fun i z hz => by simp only [hup i z hz]) hw0
    (fun θ hθ => by rw [fderiv_sub_const]; exact hd θ hθ) θ hθ
  exact sub_eq_zero.1 this

/-! ### Uniqueness (d) -/

/-- Uniqueness in `bpI:p1:border-solve` (d), first two assertions (step `bs-unique`): a holomorphic
`1`-periodic solution `(ξᴸ', ξᴺ', ξ^ω')` of the three equations of (b) on `T_{r-2δ}` has the
frequency correction `ξ^ω` and the normal part `ξᴺ` of `bordSol`. -/
theorem border_unique {γ τ : ℝ} {ω : Fin n → ℝ} (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hdio : IsDiophantine γ τ ω) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (h2δ : 2 * δ < r)
    (d : BordData n) {HN : ℝ}
    (hηN : DifferentiableOn ℂ d.ηN (complexStrip n r)) (hηNp : IsPeriodicOn d.ηN r)
    (hHN : ∀ θ ∈ complexStrip n r, ‖d.ηN θ‖ ≤ HN) (hηN0 : avg d.ηN = 0)
    (hT : DifferentiableOn ℂ d.T (complexStrip n r))
    (hY : DifferentiableOn ℂ d.Y (complexStrip n r))
    (hinv : IsUnit (bordAvg ω d).det)
    {ξL' ξN' : (Fin n → ℂ) → Fin n → ℂ} {ξω' : ℂ}
    (hξL : DifferentiableOn ℂ ξL' (complexStrip n (r - 2 * δ)))
    (hξLp : IsPeriodicOn ξL' (r - 2 * δ))
    (hξN : DifferentiableOn ℂ ξN' (complexStrip n (r - 2 * δ)))
    (hξNp : IsPeriodicOn ξN' (r - 2 * δ))
    (e1 : ∀ θ ∈ complexStrip n (r - 2 * δ), d.T θ *ᵥ ξN' θ -
      fderiv ℂ ξL' θ (fun l => (ω l : ℂ)) + ξω' • (fun a => (ω a : ℂ)) = d.ηL θ)
    (e2 : ∀ θ ∈ complexStrip n (r - 2 * δ), -fderiv ℂ ξN' θ (fun l => (ω l : ℂ)) = d.ηN θ)
    (e3 : avg (fun θ => d.Y θ ⬝ᵥ ξN' θ) = d.ηω) :
    ξω' = bordXiOmega ω d ∧ ∀ θ ∈ complexStrip n (r - 2 * δ), ξN' θ = bordXiN ω d θ := by
  have hr2 : 0 < r - 2 * δ := by linarith
  have hδr : δ < r := by linarith
  have hr1 : 0 < r - δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  -- `uᴺ = 𝓡 ηᴺ` on `T_{r-δ}`
  obtain ⟨-, hvec⟩ := KAM.cohomological hdio hγ hτ hδ hδr (ρ := r)
  obtain ⟨hU1, hU2, -, hU4, -, -, -⟩ := hvec (p := n) d.ηN HN hηN hηNp hHN hηN0
  have hUd : DifferentiableOn ℂ (triU ω d.ηN) (complexStrip n (r - δ)) := hU1
  have hUp : IsPeriodicOn (triU ω d.ηN) (r - δ) := hU2
  have hUderiv : ∀ θ ∈ complexStrip n (r - δ),
      fderiv ℂ (triU ω d.ηN) θ (fun l => (ω l : ℂ)) = d.ηN θ := hU4
  have hUd2 := hUd.mono hsub
  have hUp2 : IsPeriodicOn (triU ω d.ηN) (r - 2 * δ) :=
    Triangular.isPeriodicOn_mono (by linarith) hUp
  -- `ξᴺ' + uᴺ` is constant
  have hv : DifferentiableOn ℂ (fun θ => ξN' θ + triU ω d.ηN θ) (complexStrip n (r - 2 * δ)) :=
    hξN.add hUd2
  have hvp : IsPeriodicOn (fun θ => ξN' θ + triU ω d.ηN θ) (r - 2 * δ) :=
    fun i z hz => by simp only [hξNp i z hz, hUp2 i z hz]
  have hvd : ∀ θ ∈ complexStrip n (r - 2 * δ),
      fderiv ℂ (fun θ => ξN' θ + triU ω d.ηN θ) θ (fun l => (ω l : ℂ)) = 0 := by
    intro θ hθ
    have hopen := (isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ
    rw [fderiv_fun_add (hξN.differentiableAt hopen) (hUd2.differentiableAt hopen)]
    simp only [_root_.add_apply]
    rw [hUderiv θ (hsub hθ)]
    have := e2 θ hθ
    rw [neg_eq_iff_eq_neg] at this
    rw [this]
    abel
  set c : Fin n → ℂ := avg (fun θ => ξN' θ + triU ω d.ηN θ) with hc
  have hconst : ∀ θ ∈ complexStrip n (r - 2 * δ), ξN' θ = c - triU ω d.ηN θ := fun θ hθ =>
    eq_sub_of_add_eq (eq_avg_of_fderiv_eq_zero hγ hτ hdio hr2 hv hvp hvd θ hθ)
  -- continuity along the real torus
  have hcT : Continuous fun x : Fin n → ℝ => d.T (fun i => (x i : ℂ)) :=
    Triangular.continuous_ofReal_comp hr hT
  have hcY : Continuous fun x : Fin n → ℝ => d.Y (fun i => (x i : ℂ)) :=
    Triangular.continuous_ofReal_comp hr hY
  have hcU : Continuous fun x : Fin n → ℝ => triU ω d.ηN (fun i => (x i : ℂ)) :=
    Triangular.continuous_ofReal_comp hr1 hUd
  have hcLd : Continuous fun x : Fin n → ℝ =>
      fderiv ℂ ξL' (fun i => (x i : ℂ)) (fun l => (ω l : ℂ)) :=
    Triangular.continuous_ofReal_comp hr2
      (Tools.differentiableOn_fderiv_apply hξL fun l => (ω l : ℂ))
  have hcA : Continuous fun x : Fin n → ℝ =>
      d.T (fun i => (x i : ℂ)) *ᵥ c := hcT.matrix_mulVec continuous_const
  have hcB : Continuous fun x : Fin n → ℝ =>
      d.T (fun i => (x i : ℂ)) *ᵥ triU ω d.ηN (fun i => (x i : ℂ)) := hcT.matrix_mulVec hcU
  -- first row of the bordered average system
  have hrow1 : avg d.T *ᵥ c + ξω' • (fun a => (ω a : ℂ)) =
      avg d.ηL + avg (fun θ => d.T θ *ᵥ triU ω d.ηN θ) := by
    have hpt : ∀ θ ∈ complexStrip n (r - 2 * δ),
        ((d.T θ *ᵥ c - d.T θ *ᵥ triU ω d.ηN θ) -
          fderiv ℂ ξL' θ (fun l => (ω l : ℂ))) + ξω' • (fun a => (ω a : ℂ)) = d.ηL θ :=
      fun θ hθ => by
        rw [← Matrix.mulVec_sub, ← hconst θ hθ]
        exact e1 θ hθ
    have havg := avg_congr hr2 hpt
    rw [avg_add_of_continuous ((hcA.sub hcB).sub hcLd) continuous_const,
      avg_sub_of_continuous (hcA.sub hcB) hcLd, avg_sub_of_continuous hcA hcB,
      avg_const, Triangular.avg_mulVec_const hcT] at havg
    have hL0 : avg (fun θ => fderiv ℂ ξL' θ (fun l => (ω l : ℂ))) = 0 :=
      Tools.torusAverage_fderiv_apply_eq_zero hr2 hξL hξLp (fun l => (ω l : ℂ))
    rw [hL0, sub_zero] at havg
    rw [← havg]
    abel
  -- second row of the bordered average system
  have hrow2 : avg d.Y ⬝ᵥ c = d.ηω + avg (fun θ => d.Y θ ⬝ᵥ triU ω d.ηN θ) := by
    have hpt : ∀ θ ∈ complexStrip n (r - 2 * δ),
        d.Y θ ⬝ᵥ c - d.Y θ ⬝ᵥ triU ω d.ηN θ = d.Y θ ⬝ᵥ ξN' θ := fun θ hθ => by
      rw [hconst θ hθ, dotProduct_sub]
    have havg := avg_congr hr2 hpt
    rw [avg_sub_of_continuous (hcY.dotProduct continuous_const) (hcY.dotProduct hcU),
      avg_dotProduct_const hcY, e3] at havg
    rw [← havg]
    ring
  obtain ⟨hc0, hω⟩ := eq_bordSol_of_rows ω d hinv hrow1 hrow2
  refine ⟨hω, fun θ hθ => ?_⟩
  rw [hconst θ hθ, hc0]
  rfl

end KAM.Iso.Linear

end
