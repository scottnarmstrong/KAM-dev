/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.PolyDomain

/-!
# Torus (strip × polydisc) domains, gauge, small field, lattice equivariance (track B, B4-TDOM)

Geometric glue for the torus checker: the complex domain `cstripOpen σ ρ` (angles in a strip of
half-width `σ`, actions in a polydisc of radius `ρ`), the gauge interior criterion for the gauge
`scaleCLE ρ' σ'` (angles weighted by `σ'`, actions by `ρ'`), the `SmallField` hypothesis from
coordinate derivative bounds, equivariance of the (complex and real) flows under real angle shifts,
and inclusions of the real cylinder and of Cauchy polydiscs.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- The open complex strip × polydisc: `|Im θ_i| < σ`, `‖J_i‖ < ρ`. -/
def cstripOpen (σ ρ : ℝ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {z | ∀ i, |(z.1 i).im| < σ ∧ ‖z.2 i‖ < ρ}

theorem isOpen_cstripOpen (σ ρ : ℝ) : IsOpen (cstripOpen (n := n) σ ρ) := by
  have : cstripOpen (n := n) σ ρ =
      ⋂ i, ({z : (Fin n → ℂ) × (Fin n → ℂ) | |(z.1 i).im| < σ} ∩ {z | ‖z.2 i‖ < ρ}) := by
    ext z; simp [cstripOpen]
  rw [this]
  exact isOpen_iInter_of_finite fun i => IsOpen.inter
    (isOpen_lt ((Complex.continuous_im.comp ((continuous_apply i).comp continuous_fst)).abs)
      continuous_const)
    (isOpen_lt (((continuous_apply i).comp continuous_snd).norm) continuous_const)

/-- The real angle shift `θ ↦ θ + s` as a vector of `ℂⁿ × ℂⁿ`. -/
def cshiftVec (s : Fin n → ℝ) : (Fin n → ℂ) × (Fin n → ℂ) := (fun i => (s i : ℂ), 0)

theorem cshiftVec_integer (m : Fin n → ℤ) :
    cshiftVec (fun i => (m i : ℝ)) = ((fun i => (m i : ℂ)), 0) := by
  simp [cshiftVec]

theorem add_cshiftVec_mem_cstripOpen {σ ρ : ℝ} (s : Fin n → ℝ)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ cstripOpen σ ρ) :
    z + cshiftVec s ∈ cstripOpen σ ρ := by
  intro i
  obtain ⟨h1, h2⟩ := hz i
  simpa [cshiftVec] using And.intro h1 h2

/-- Translation invariance of the strip under real angle shifts. -/
theorem image_add_cshiftVec_cstripOpen (σ ρ : ℝ) (s : Fin n → ℝ) :
    (fun w => w + cshiftVec s) '' cstripOpen σ ρ = cstripOpen σ ρ := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact add_cshiftVec_mem_cstripOpen s hz
  · intro z hz
    refine ⟨z - cshiftVec s, ?_, by simp⟩
    intro i
    obtain ⟨h1, h2⟩ := hz i
    simpa [cshiftVec] using And.intro h1 h2

/-! ### Gauge -/

private theorem coord_le_of_scale {ρ' σ' : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ')
    {v : (Fin n → ℂ) × (Fin n → ℂ)} {c : ℝ} (h : ‖scaleCLE ρ' σ' hρ' hσ' v‖ ≤ c) (i : Fin n) :
    ‖v.1 i‖ ≤ c * σ' ∧ ‖v.2 i‖ ≤ c * ρ' := by
  rw [norm_scaleCLE, scaledNorm, max_le_iff, div_le_iff₀ hσ', div_le_iff₀ hρ'] at h
  exact ⟨(norm_le_pi_norm v.1 i).trans h.1, (norm_le_pi_norm v.2 i).trans h.2⟩

/-- Gauge interior of the strip × polydisc. -/
theorem mem_gaugeInterior_cstripOpen {σ ρ ρ' σ' c : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ')
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : ∀ i, |(z.1 i).im| + c * σ' < σ ∧ ‖z.2 i‖ + c * ρ' < ρ) :
    z ∈ gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) c := by
  intro w hw i
  obtain ⟨h1, h2⟩ := coord_le_of_scale hρ' hσ' hw i
  have e1 : |(w.1 i).im| ≤ |(z.1 i).im| + ‖(w - z).1 i‖ := by
    have : (w.1 i).im = (z.1 i).im + ((w - z).1 i).im := by simp
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add_right (Complex.abs_im_le_norm _) _)
  have e2 : ‖w.2 i‖ ≤ ‖z.2 i‖ + ‖(w - z).2 i‖ := by
    simpa using norm_add_le (z.2 i) ((w - z).2 i)
  have := hz i
  constructor <;> linarith

/-! ### Small field -/

/-- Complex differentiability of the Hamiltonian field of a holomorphic function on the strip. -/
theorem differentiableOn_hamVFℂ_strip {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ : ℝ}
    (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ)) :
    DifferentiableOn ℂ (KAM.hamiltonianVectorFieldℂ φ) (cstripOpen σ ρ) :=
  differentiableOn_hamVFℂ_poly (isOpen_cstripOpen σ ρ) hφ

/-- Small field from coordinate derivative bounds: the angle velocity `∂_{J_i} φ` is at most
`ε σ'` and the action velocity `∂_{φ_i} φ` at most `ε ρ'`. -/
theorem smallField_of_strip_bounds {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ σ' ρ' ε : ℝ}
    (hρ' : 0 < ρ') (hσ' : 0 < σ') (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hJ : ∀ z ∈ cstripOpen (n := n) σ ρ, ∀ i, ‖fderiv ℂ φ z (0, Pi.single i 1)‖ ≤ ε * σ')
    (hθ : ∀ z ∈ cstripOpen (n := n) σ ρ, ∀ i, ‖fderiv ℂ φ z (Pi.single i 1, 0)‖ ≤ ε * ρ') :
    SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε where
  isOpen := isOpen_cstripOpen σ ρ
  differentiableOn := differentiableOn_hamVFℂ_strip hφ
  eps_nonneg := hε0
  eps_le := hε
  bound z hz := by
    rw [norm_scaleCLE, scaledNorm, max_le_iff, div_le_iff₀ hσ', div_le_iff₀ hρ']
    constructor
    · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hε0 hσ'.le)).2 fun i => ?_
      simpa [KAM.hamiltonianVectorFieldℂ] using hJ z hz i
    · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hε0 hρ'.le)).2 fun i => ?_
      simpa [KAM.hamiltonianVectorFieldℂ] using hθ z hz i

/-! ### Lattice equivariance -/

/-- Shift invariance of `φ` on the strip gives shift invariance of its derivative, hence of the
Hamiltonian field. -/
theorem hamVFℂ_shift {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ : ℝ} (s : Fin n → ℝ)
    (hper : ∀ w ∈ cstripOpen (n := n) σ ρ, φ (w + cshiftVec s) = φ w) :
    ∀ w ∈ cstripOpen (n := n) σ ρ,
      KAM.hamiltonianVectorFieldℂ φ (w + cshiftVec s) = KAM.hamiltonianVectorFieldℂ φ w := by
  intro w hw
  have hev : (fun x => φ (x + cshiftVec s)) =ᶠ[nhds w] φ :=
    Filter.eventually_of_mem ((isOpen_cstripOpen σ ρ).mem_nhds hw) hper
  have hd : fderiv ℂ φ (w + cshiftVec s) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right (cshiftVec s) (f := φ) (x := w)]
    exact hev.fderiv_eq
  simp [KAM.hamiltonianVectorFieldℂ, hd]

/-- Equivariance of the complex flow under real angle shifts, on the half interior. -/
theorem flow_shift_equivariant {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ σ' ρ' ε : ℝ}
    {hρ' : 0 < ρ'} {hσ' : 0 < σ'}
    (h : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε)
    (s : Fin n → ℝ) (hper : ∀ w ∈ cstripOpen (n := n) σ ρ, φ (w + cshiftVec s) = φ w)
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    flow (KAM.hamiltonianVectorFieldℂ φ) (cstripOpen σ ρ) t (z + cshiftVec s) =
      flow (KAM.hamiltonianVectorFieldℂ φ) (cstripOpen σ ρ) t z + cshiftVec s :=
  (flow_d h (image_add_cshiftVec_cstripOpen σ ρ s) (hamVFℂ_shift s hper)).2 z hz t ht

/-- The real shift `angleShift`-type vector for real `s`. -/
def rshiftVec (s : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) := (s, 0)

theorem rshiftVec_integer (m : Fin n → ℤ) :
    rshiftVec (fun i => (m i : ℝ)) = KAM.ODE.angleShift m := rfl

theorem realInclusion₂_rshiftVec (s : Fin n → ℝ) :
    KAM.realInclusion₂ n (rshiftVec s) = cshiftVec s := by
  ext i <;> simp [rshiftVec, cshiftVec]

theorem realInterior_add_rshiftVec {σ ρ σ' ρ' : ℝ} {hρ' : 0 < ρ'} {hσ' : 0 < σ'}
    (s : Fin n → ℝ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (h : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    x + rshiftVec s ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) := by
  intro w hw
  have hw' : w - cshiftVec s ∈ cstripOpen σ ρ := h _ (by
    have : w - cshiftVec s - KAM.realInclusion₂ n x =
        w - KAM.realInclusion₂ n (x + rshiftVec s) := by
      rw [map_add, realInclusion₂_rshiftVec]; abel
    rw [this]; exact hw)
  have := add_cshiftVec_mem_cstripOpen s hw'
  simpa using this

/-- Equivariance of the real flow under real angle shifts. -/
theorem realFlow_shift_equivariant {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ σ' ρ' ε : ℝ}
    {hρ' : 0 < ρ'} {hσ' : 0 < σ'}
    (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ))
    (h : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cstripOpen σ ρ →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    (s : Fin n → ℝ) (hper : ∀ w ∈ cstripOpen (n := n) σ ρ, φ (w + cshiftVec s) = φ w)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    realFlow φ (cstripOpen σ ρ) t (x + rshiftVec s) =
      realFlow φ (cstripOpen σ ρ) t x + rshiftVec s := by
  have hΩ := isOpen_cstripOpen (n := n) σ ρ
  have hx' := realInterior_add_rshiftVec (σ := σ) (ρ := ρ) s hx
  apply KAM.realInclusion₂_injective n
  rw [realInclusion₂_realFlow hΩ hφ h hreal hx' ht, map_add, map_add,
    realInclusion₂_realFlow hΩ hφ h hreal hx ht, realInclusion₂_rshiftVec]
  have := flow_shift_equivariant h s hper hx ht
  exact this

/-- Integer-lattice version, in terms of `KAM.ODE.angleShift`. -/
theorem realFlow_angleShift_equivariant {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ σ' ρ' ε : ℝ}
    {hρ' : 0 < ρ'} {hσ' : 0 < σ'}
    (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ))
    (h : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cstripOpen σ ρ →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    (m : Fin n → ℤ)
    (hper : ∀ w ∈ cstripOpen (n := n) σ ρ, φ (w + ((fun i => (m i : ℂ)), 0)) = φ w)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    realFlow φ (cstripOpen σ ρ) t (x + KAM.ODE.angleShift m) =
      realFlow φ (cstripOpen σ ρ) t x + KAM.ODE.angleShift m := by
  have := realFlow_shift_equivariant hφ h hreal (fun i => (m i : ℝ))
    (by simpa [cshiftVec_integer] using hper) hx ht
  simpa [rshiftVec_integer] using this

/-- If `H` is angle-periodic on the real interior, so is `H ∘ realFlow`. -/
theorem comp_realFlow_angleShift {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {σ ρ σ' ρ' ε : ℝ}
    {hρ' : 0 < ρ'} {hσ' : 0 < σ'}
    (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ))
    (h : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cstripOpen σ ρ →
      (φ (KAM.realInclusion₂ n x)).im = 0)
    (m : Fin n → ℤ)
    (hper : ∀ w ∈ cstripOpen (n := n) σ ρ, φ (w + ((fun i => (m i : ℂ)), 0)) = φ w)
    (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (hH : ∀ y, H (y + KAM.ODE.angleShift m) = H y)
    {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    H (realFlow φ (cstripOpen σ ρ) t (x + KAM.ODE.angleShift m)) =
      H (realFlow φ (cstripOpen σ ρ) t x) := by
  rw [realFlow_angleShift_equivariant hφ h hreal m hper hx ht, hH]

/-! ### Real cylinder and Cauchy discs -/

/-- The open real cylinder `cyl c` lies in the real interior (radius `1`) when `σ' < σ` and
`c i + ρ' ≤ ρ`. -/
theorem cyl_subset_realInterior_cstrip {σ ρ σ' ρ' : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ')
    {c : Fin n → ℝ} (hσ : σ' < σ) (hc : ∀ i, c i + ρ' ≤ ρ) :
    cyl c ⊆ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) 1 := by
  intro x hx
  refine mem_gaugeInterior_cstripOpen hρ' hσ' fun i => ?_
  have := hx i
  have := hc i
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero,
    Complex.norm_real, Real.norm_eq_abs, one_mul]
  constructor <;> linarith

/-- Closed version: `c i + ρ' < ρ`. -/
theorem cylClosed_subset_realInterior_cstrip {σ ρ σ' ρ' : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ')
    {c : Fin n → ℝ} (hσ : σ' < σ) (hc : ∀ i, c i + ρ' < ρ) :
    cylClosed c ⊆ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) 1 := by
  intro x hx
  refine mem_gaugeInterior_cstripOpen hρ' hσ' fun i => ?_
  have := hx i
  have := hc i
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero,
    Complex.norm_real, Real.norm_eq_abs, one_mul]
  constructor <;> linarith

/-- The Cauchy polydisc of radius `δc` around a real point with `|x.2 i| ≤ r i` lies in the half
interior. -/
theorem cauchyDisc_subset_gaugeInterior_strip {σ ρ σ' ρ' δc : ℝ} (hρ' : 0 < ρ')
    (hσ' : 0 < σ') {r : Fin n → ℝ} (hσ : δc + σ' / 2 < σ) (hr : ∀ i, r i + δc + ρ' / 2 < ρ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ i, |x.2 i| ≤ r i) :
    {w : (Fin n → ℂ) × (Fin n → ℂ) | ∀ i, ‖w.1 i - (KAM.realInclusion₂ n x).1 i‖ ≤ δc ∧
        ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ ≤ δc} ⊆
      gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) := by
  intro w hw
  refine mem_gaugeInterior_cstripOpen hρ' hσ' fun i => ?_
  obtain ⟨a1, a2⟩ := hw i
  have h1 := hx i
  have h2 := hr i
  have e1 : |(w.1 i).im| ≤ δc := by
    have : (w.1 i).im = (w.1 i - (KAM.realInclusion₂ n x).1 i).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans a1
  have e2 : ‖w.2 i‖ ≤ ‖(KAM.realInclusion₂ n x).2 i‖ +
      ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).2 i)
      (w.2 i - (KAM.realInclusion₂ n x).2 i)
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
    Real.norm_eq_abs] at e1 e2 a2 ⊢
  constructor <;> linarith

/-! ### Smoke test -/

theorem smallField_strip_zero_smoke {σ ρ σ' ρ' : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ') :
    SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen (n := n) σ ρ)
      (KAM.hamiltonianVectorFieldℂ (0 : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)) 0 := by
  refine smallField_of_strip_bounds hρ' hσ' (differentiableOn_const 0) le_rfl (by norm_num) ?_ ?_
    <;> intro z _ i <;> simp

theorem zero_mem_gaugeInterior_strip_smoke {σ ρ σ' ρ' c : ℝ} (hρ' : 0 < ρ') (hσ' : 0 < σ')
    (h1 : c * σ' < σ) (h2 : c * ρ' < ρ) :
    (0 : (Fin n → ℂ) × (Fin n → ℂ)) ∈
      gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) c :=
  mem_gaugeInterior_cstripOpen hρ' hσ' fun i => by simp [h1, h2]

end KAM.EffectiveStability

end
