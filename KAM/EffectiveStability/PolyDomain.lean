/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.RealFlow.Basic
public import KAM.EffectiveStability.Domains
public import KAM.Strip.Regularity

/-!
# Polydisc domains, scalar gauge, small-field check (track B)

Geometric glue for the one-step soundness theorem: the open complex polydisc `cpolyOpen ρ`, the
scalar gauge `gaugeScalar δ hδ` (`‖W v‖ = ‖v‖ / δ`), the gauge interior of a polydisc, the
`SmallField` hypothesis from coordinate derivative bounds, and the inclusions of real chart
domains and Cauchy polydiscs in the real / half interior.
-/

@[expose] public noncomputable section

open Set KAM.Canonical
open scoped ContDiff

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- The open complex polydisc of polyradius `ρ` in `ℂⁿ × ℂⁿ`. -/
def cpolyOpen (ρ : ℝ) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  {z | ∀ i, ‖z.1 i‖ < ρ ∧ ‖z.2 i‖ < ρ}

theorem isOpen_cpolyOpen (ρ : ℝ) : IsOpen (cpolyOpen (n := n) ρ) := by
  have : cpolyOpen (n := n) ρ =
      ⋂ i, ({z : (Fin n → ℂ) × (Fin n → ℂ) | ‖z.1 i‖ < ρ} ∩ {z | ‖z.2 i‖ < ρ}) := by
    ext z; simp [cpolyOpen]
  rw [this]
  exact isOpen_iInter_of_finite fun i => IsOpen.inter
    (isOpen_lt (((continuous_apply i).comp continuous_fst).norm) continuous_const)
    (isOpen_lt (((continuous_apply i).comp continuous_snd).norm) continuous_const)

/-- The scalar gauge: multiplication by `δ⁻¹`. -/
def gaugeScalar (δ : ℝ) (hδ : 0 < δ) :
    ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((δ : ℂ)⁻¹) (inv_ne_zero (by exact_mod_cast hδ.ne')))

theorem gaugeScalar_apply (δ : ℝ) (hδ : 0 < δ) (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    gaugeScalar δ hδ v = (δ : ℂ)⁻¹ • v := rfl

theorem norm_gaugeScalar_apply (δ : ℝ) (hδ : 0 < δ) (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖gaugeScalar δ hδ v‖ = ‖v‖ / δ := by
  rw [gaugeScalar_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hδ.le,
    inv_mul_eq_div]

private theorem gauge_le_iff (δ : ℝ) (hδ : 0 < δ) (v : (Fin n → ℂ) × (Fin n → ℂ)) (c : ℝ) :
    ‖gaugeScalar δ hδ v‖ ≤ c ↔ ‖v‖ ≤ c * δ := by
  rw [norm_gaugeScalar_apply, div_le_iff₀ hδ]

private theorem coord_le_of_gauge (δ : ℝ) (hδ : 0 < δ) {v : (Fin n → ℂ) × (Fin n → ℂ)} {c : ℝ}
    (h : ‖gaugeScalar δ hδ v‖ ≤ c) (i : Fin n) : ‖v.1 i‖ ≤ c * δ ∧ ‖v.2 i‖ ≤ c * δ := by
  have h' := (gauge_le_iff δ hδ v c).1 h
  exact ⟨(norm_le_pi_norm v.1 i).trans ((le_max_left _ _).trans h'),
    (norm_le_pi_norm v.2 i).trans ((le_max_right _ _).trans h')⟩

/-- (3) Gauge interior of a polydisc. -/
theorem mem_gaugeInterior_cpolyOpen {δ ρ c : ℝ} (hδ : 0 < δ) (_hc : 0 ≤ c)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : ∀ i, ‖z.1 i‖ + c * δ < ρ ∧ ‖z.2 i‖ + c * δ < ρ) :
    z ∈ gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) c := by
  intro w hw i
  obtain ⟨h1, h2⟩ := coord_le_of_gauge δ hδ hw i
  have e1 : ‖w.1 i‖ ≤ ‖z.1 i‖ + ‖(w - z).1 i‖ := by
    simpa using norm_add_le (z.1 i) ((w - z).1 i)
  have e2 : ‖w.2 i‖ ≤ ‖z.2 i‖ + ‖(w - z).2 i‖ := by
    simpa using norm_add_le (z.2 i) ((w - z).2 i)
  have := hz i
  constructor <;> linarith

/-- The complexified Hamiltonian field of a holomorphic function is holomorphic. -/
theorem differentiableOn_hamVFℂ_poly {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω) :
    DifferentiableOn ℂ (KAM.hamiltonianVectorFieldℂ φ) Ω := by
  have h1 : ContDiffOn ℂ ∞ φ Ω := KAM.contDiffOn_infty_of_differentiableOn hΩ hφ
  have h2 : ContDiffOn ℂ ∞ (fun z => fderiv ℂ φ z) Ω := h1.fderiv_of_isOpen hΩ (by simp)
  have h3 : ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ φ z v) Ω := fun v =>
    ((h2.clm_apply contDiffOn_const).differentiableOn (by simp))
  refine DifferentiableOn.prodMk ?_ ?_
  · exact differentiableOn_pi.2 fun i => h3 _
  · exact differentiableOn_pi.2 fun i => (h3 _).neg

/-- (4) Small field from coordinate derivative bounds. -/
theorem smallField_of_coord_bounds {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ρ δ ε : ℝ}
    (hδ : 0 < δ) (hφ : DifferentiableOn ℂ φ (cpolyOpen ρ)) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h1 : ∀ z ∈ cpolyOpen (n := n) ρ, ∀ i, ‖fderiv ℂ φ z (Pi.single i 1, 0)‖ ≤ ε * δ)
    (h2 : ∀ z ∈ cpolyOpen (n := n) ρ, ∀ i, ‖fderiv ℂ φ z (0, Pi.single i 1)‖ ≤ ε * δ) :
    SmallField (gaugeScalar δ hδ) (cpolyOpen ρ) (KAM.hamiltonianVectorFieldℂ φ) ε where
  isOpen := isOpen_cpolyOpen ρ
  differentiableOn := differentiableOn_hamVFℂ_poly (isOpen_cpolyOpen ρ) hφ
  eps_nonneg := hε0
  eps_le := hε
  bound z hz := by
    rw [norm_gaugeScalar_apply, div_le_iff₀ hδ]
    have hεδ : 0 ≤ ε * δ := mul_nonneg hε0 hδ.le
    refine (Prod.norm_def _).trans_le (max_le ?_ ?_) <;>
      refine (pi_norm_le_iff_of_nonneg hεδ).2 fun i => ?_
    · exact h2 z hz i
    · simpa [KAM.hamiltonianVectorFieldℂ] using h1 z hz i

/-! ### Real chart domains and Cauchy discs -/

/-- (5) A real point with coordinates in `[-r, r]` and `r + δ < ρ` is in the real interior. -/
theorem mem_realInterior_cpolyOpen {δ ρ : ℝ} (hδ : 0 < δ) {r : Fin n → ℝ}
    (hr : ∀ i, r i + δ < ρ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i) :
    x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 := by
  refine mem_gaugeInterior_cpolyOpen hδ zero_le_one fun i => ?_
  have h1 := hx i
  have h2 := hr i
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
    Real.norm_eq_abs, one_mul]
  constructor <;> linarith

/-- (5) Oscillator form: if `2 c i ≤ r i ^ 2`, `0 ≤ r i`, `r i + δ < ρ`, then `osc c` lies in
the real interior. -/
theorem osc_subset_realInterior {δ ρ : ℝ} (hδ : 0 < δ) {c r : Fin n → ℝ}
    (hc : ∀ i, 2 * c i ≤ r i ^ 2) (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i + δ < ρ) :
    osc c ⊆ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 := by
  intro w hw
  refine mem_realInterior_cpolyOpen hδ hr fun i => ?_
  have h := hw i
  simp only [KAM.Planetary.oscillatorAction] at h
  have h2 := hc i
  constructor
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.2 i)]) (hr0 i)
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.1 i)]) (hr0 i)

/-- (5) Closed oscillator form. -/
theorem oscClosed_subset_realInterior {δ ρ : ℝ} (hδ : 0 < δ) {c r : Fin n → ℝ}
    (hc : ∀ i, 2 * c i ≤ r i ^ 2) (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i + δ < ρ) :
    oscClosed c ⊆ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 := by
  intro w hw
  refine mem_realInterior_cpolyOpen hδ hr fun i => ?_
  have h := hw i
  simp only [KAM.Planetary.oscillatorAction] at h
  have h2 := hc i
  constructor
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.2 i)]) (hr0 i)
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (w.1 i)]) (hr0 i)

/-- (6) The Cauchy polydisc around a real chart point lies in the half interior. -/
theorem cauchyDisc_subset_gaugeInterior {δ δc ρ : ℝ} (hδ : 0 < δ) {r : Fin n → ℝ}
    (hr : ∀ i, r i + δc + δ / 2 < ρ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i) :
    {w : (Fin n → ℂ) × (Fin n → ℂ) | ∀ i, ‖w.1 i - (KAM.realInclusion₂ n x).1 i‖ ≤ δc ∧
        ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ ≤ δc} ⊆
      gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2) := by
  intro w hw
  refine mem_gaugeInterior_cpolyOpen hδ (by norm_num) fun i => ?_
  obtain ⟨a1, a2⟩ := hw i
  have h1 := hx i
  have h2 := hr i
  have e1 : ‖w.1 i‖ ≤ ‖(KAM.realInclusion₂ n x).1 i‖ + ‖w.1 i - (KAM.realInclusion₂ n x).1 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).1 i) (w.1 i - (KAM.realInclusion₂ n x).1 i)
  have e2 : ‖w.2 i‖ ≤ ‖(KAM.realInclusion₂ n x).2 i‖ + ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).2 i) (w.2 i - (KAM.realInclusion₂ n x).2 i)
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
    Real.norm_eq_abs] at e1 e2 a1 a2
  constructor <;> linarith [h1.1, h1.2]

/-- (7) The flow stays in the polydisc. -/
theorem flow_mem_cpolyOpen {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {ρ ε : ℝ} {F : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (h : SmallField W (cpolyOpen ρ) F ε) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior W (cpolyOpen ρ) (1 / 2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    flow F (cpolyOpen ρ) t z ∈ cpolyOpen ρ :=
  (flow_b h).2.2.1 t ht z hz

/-- (8) Smoke test: `φ = 0` gives a small field with `ε = 0`, and items (3) applies. -/
theorem smallField_zero_smoke {ρ δ : ℝ} (hδ : 0 < δ) :
    SmallField (gaugeScalar δ hδ) (cpolyOpen (n := n) ρ)
      (KAM.hamiltonianVectorFieldℂ (0 : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)) 0 := by
  refine smallField_of_coord_bounds hδ (differentiableOn_const 0) le_rfl (by norm_num) ?_ ?_ <;>
    intro z _ i <;> simp

theorem zero_mem_gaugeInterior_smoke {ρ δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (h : c * δ < ρ) :
    (0 : (Fin n → ℂ) × (Fin n → ℂ)) ∈ gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) c :=
  mem_gaugeInterior_cpolyOpen hδ hc fun i => by simp [h]

end KAM.EffectiveStability

end
