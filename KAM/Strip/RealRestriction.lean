/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.OmegaZero
public import KAM.Strip.Analytic

/-!
# Real restrictions of holomorphic maps on strips

Blueprint Part 1, "Real points". For a map `K : ℂⁿ → ℂⁿ × ℂⁿ` that is real on reals, the real
restriction is `KAM.realRestriction K = Re ∘ K ∘ ι`, where `ι : ℝⁿ → ℂⁿ` is
`KAM.realInclusion` and `Re` is the componentwise real part (`KAM.realPartCLM₂`). Then
`K (ι x) = ι (realRestriction K x)` (`KAM.isRealOnReals_iff`).

* `KAM.norm_realRestriction_le_of_linear`, `KAM.realRestriction_add_int` (blueprint
  `bp:p1:real-restriction-consequences`): the real restriction of a `ℂ`-linear map has no larger
  operator norm, and a primary `K` has `k (x + m) = k x + (m, 0)` on real points.
* `KAM.real_restriction` (blueprint `bp:p1:real-restriction`), with steps
  `KAM.analyticOnNhd_realRestriction`, `KAM.realRestriction_fderiv` and
  `KAM.norm_fderiv_realRestriction_le`: for `K` holomorphic on the strip `T_ρ` and real on reals,
  `k` is real-analytic, its real derivative is the restriction of the complex derivative, and
  `‖Dk(x)‖ ≤ ‖DK(x)‖`.
* `KAM.hamiltonian_real` (blueprint `bp:p1:hamiltonian-real`), with steps
  `KAM.hamiltonian_real_fderiv`, `KAM.hamiltonianVectorField_eq_of_real` and
  `KAM.hamiltonianVectorFieldℂ_eq_neg_omegaZero`: if `H` agrees with `Re h` near a real point and
  `h` is holomorphic and real on reals, then `X_H(z) = X_h(z)`; and `X_φ = J (Dφ)ᵀ` with
  `J = -Ω₀`, equivalently `Ω₀ X_φ = (Dφ)ᵀ`.
-/

@[expose] public noncomputable section

open Metric Set Filter
open scoped Topology

namespace KAM

/-- The real-linear inclusion `ℝⁿ × ℝⁿ → ℂⁿ × ℂⁿ`. -/
def realInclusion₂ (n : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
  (realInclusion n).prodMap (realInclusion n)

@[simp] theorem realInclusion₂_apply {n : ℕ} (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    realInclusion₂ n z = (realInclusion n z.1, realInclusion n z.2) := rfl

theorem norm_realInclusion₂ {n : ℕ} (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖realInclusion₂ n z‖ = ‖z‖ := by
  simp [Prod.norm_def, norm_realInclusion]

theorem realInclusion_injective (n : ℕ) : Function.Injective (realInclusion n) := by
  intro a b h
  ext i
  simpa using congrFun h i

theorem realInclusion₂_injective (n : ℕ) : Function.Injective (realInclusion₂ n) := by
  intro a b h
  exact Prod.ext (realInclusion_injective n (congrArg Prod.fst h))
    (realInclusion_injective n (congrArg Prod.snd h))

/-- The componentwise real part `ℂⁿ × ℂⁿ → ℝⁿ × ℝⁿ`. -/
def realPartCLM₂ (n : ℕ) : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (realPartCLM n).prodMap (realPartCLM n)

@[simp] theorem realPartCLM₂_apply {n : ℕ} (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    realPartCLM₂ n v = (realPartCLM n v.1, realPartCLM n v.2) := rfl

@[simp] theorem realPartCLM₂_realInclusion₂ {n : ℕ} (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    realPartCLM₂ n (realInclusion₂ n z) = z := by
  simp

/-- The restriction `k = Re ∘ K ∘ ι` of `K` to the real points. When `K` is real on reals,
`K (ι x) = ι (k x)` (`KAM.isRealOnReals_iff`). -/
def realRestriction {n : ℕ} (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  realPartCLM₂ n (K (realInclusion n x))

theorem isRealOnReals_iff {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} :
    IsRealOnReals K ↔
      ∀ x : Fin n → ℝ, K (realInclusion n x) = realInclusion₂ n (realRestriction K x) := by
  constructor
  · intro h x
    obtain ⟨z, hz⟩ := h x
    have : K (realInclusion n x) = realInclusion₂ n z := by
      rw [realInclusion₂_apply]; exact hz
    rw [this, realRestriction, this, realPartCLM₂_realInclusion₂]
  · intro h x
    exact ⟨realRestriction K x, h x⟩


/-- The restriction of a `ℂ`-linear map along isometric real inclusions has no larger operator
norm: the supremum runs over a subset of the unit ball. -/
theorem norm_le_of_isometric_restriction {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {ιE : E → E'} {ιF : F → F'} (hE : ∀ x, ‖ιE x‖ = ‖x‖) (hF : ∀ y, ‖ιF y‖ = ‖y‖)
    (ℓ : E' →L[ℂ] F') (ℓR : E →L[ℝ] F) (h : ∀ x, ℓ (ιE x) = ιF (ℓR x)) : ‖ℓR‖ ≤ ‖ℓ‖ := by
  refine ℓR.opNorm_le_bound (norm_nonneg ℓ) fun x => ?_
  rw [← hF, ← h, ← hE x]
  exact ℓ.le_opNorm _

/-- Blueprint `bp:p1:real-restriction-consequences`, first claim: a `ℂ`-linear map
`ℓ : ℂⁿ → ℂᵖ` that maps `ℝⁿ` into `ℝᵖ` has a real restriction `ℓR`, and any such restriction has
operator norm at most `‖ℓ‖` (max norms). -/
theorem norm_realRestriction_le_of_linear {n p : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (ℓR : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ))
    (h : ∀ x, ℓ (realInclusion n x) = realInclusion p (ℓR x)) : ‖ℓR‖ ≤ ‖ℓ‖ :=
  norm_le_of_isometric_restriction (norm_realInclusion) (norm_realInclusion) ℓ ℓR h

/-- Existence of the real restriction `ℓ_ℝ` of a `ℂ`-linear map with `ℓ (ℝⁿ) ⊆ ℝᵖ`. -/
theorem exists_realRestriction_of_linear {n p : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hreal : ∀ x : Fin n → ℝ, ∃ y : Fin p → ℝ, ℓ (realInclusion n x) = realInclusion p y) :
    ∃ ℓR : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ), ∀ x, ℓ (realInclusion n x) = realInclusion p (ℓR x) := by
  refine ⟨(realPartCLM p).comp ((ℓ.restrictScalars ℝ).comp (realInclusion n)), fun x => ?_⟩
  obtain ⟨y, hy⟩ := hreal x
  simp [hy]

/-- Blueprint `bp:p1:real-restriction-consequences`, second claim: if `K` is primary on `T_ρ`
and real on reals, its restriction `k` to `ℝⁿ` satisfies `k (x + m) = k x + (m, 0)`. -/
theorem realRestriction_add_int {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}
    (hρ : 0 < ρ) (hK : IsPrimaryOnStrip K ρ) (hreal : IsRealOnReals K) (x : Fin n → ℝ)
    (m : Fin n → ℤ) :
    realRestriction K (x + fun i => (m i : ℝ)) =
      realRestriction K x + (fun i => (m i : ℝ), 0) := by
  have hx : realInclusion n x ∈ complexStrip n ρ := fun i => by simpa using hρ
  have h1 := hK _ hx m
  have hι : realInclusion n x + (fun i => (m i : ℂ)) =
      realInclusion n (x + fun i => (m i : ℝ)) := by
    ext i; simp
  rw [hι] at h1
  refine realInclusion₂_injective n ?_
  rw [← isRealOnReals_iff.mp hreal, h1, isRealOnReals_iff.mp hreal, map_add]
  ext i <;> simp


/-- Blueprint `bp:p1:real-restriction-consequences`. (1) The real restriction `ℓ_ℝ` of a
`ℂ`-linear `ℓ : ℂⁿ → ℂᵖ` has `‖ℓ_ℝ‖ ≤ ‖ℓ‖` (max norms), and such a restriction exists when
`ℓ (ℝⁿ) ⊆ ℝᵖ`. (2) If `K : T_ρ → ℂⁿ × ℂⁿ` is primary on `T_ρ` (`ρ > 0`) and real on reals, its
restriction `k` to `ℝⁿ` satisfies `k (x + m) = k x + (m, 0)` for `m ∈ ℤⁿ`. -/
theorem real_restriction_consequences :
    (∀ {n p : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ)),
      (∀ x : Fin n → ℝ, ∃ y : Fin p → ℝ, ℓ (realInclusion n x) = realInclusion p y) →
      ∃ ℓR : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        (∀ x, ℓ (realInclusion n x) = realInclusion p (ℓR x)) ∧ ‖ℓR‖ ≤ ‖ℓ‖) ∧
    (∀ {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}, 0 < ρ →
      IsPrimaryOnStrip K ρ → IsRealOnReals K → ∀ (x : Fin n → ℝ) (m : Fin n → ℤ),
        realRestriction K (x + fun i => (m i : ℝ)) =
          realRestriction K x + (fun i => (m i : ℝ), 0)) := by
  refine ⟨fun ℓ hreal => ?_, fun hρ hK hreal x m => realRestriction_add_int hρ hK hreal x m⟩
  obtain ⟨ℓR, hℓR⟩ := exists_realRestriction_of_linear ℓ hreal
  exact ⟨ℓR, hℓR, norm_realRestriction_le_of_linear ℓ ℓR hℓR⟩

section RealRestriction

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

theorem realInclusion_mem_complexStrip (hρ : 0 < ρ) (x : Fin n → ℝ) :
    realInclusion n x ∈ complexStrip n ρ := fun i => by simpa using hρ

/-- Blueprint `step:p1:rr-analytic`. The restriction of a holomorphic `K` on `T_ρ` to `ℝⁿ` is
real-analytic, by `KAM.holomorphic_analytic` (b) with `U = T_ρ`. -/
theorem analyticOnNhd_realRestriction (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ)) :
    AnalyticOnNhd ℝ (realRestriction K) univ := by
  have h := (holomorphic_analytic (isOpen_complexStrip n ρ) hK).2.2
  intro x _
  exact ((realPartCLM₂ n).analyticAt _).comp (h x (realInclusion_mem_complexStrip hρ x))

/-- Blueprint `step:p1:rr-derivative`. The restriction `k` of a holomorphic `K` that is real on
reals is differentiable, and its real derivative is the restriction of the complex derivative:
`Dk(x) h = DK(x) h` for real `h`. -/
theorem realRestriction_fderiv (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (realRestriction K) x ∧ ∀ h : Fin n → ℝ,
      realInclusion₂ n (fderiv ℝ (realRestriction K) x h) =
        fderiv ℂ K (realInclusion n x) (realInclusion n h) := by
  have hKd : DifferentiableAt ℂ K (realInclusion n x) :=
    hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds (realInclusion_mem_complexStrip hρ x))
  have h2 : HasFDerivAt (fun y => K (realInclusion n y))
      (((fderiv ℂ K (realInclusion n x)).restrictScalars ℝ).comp (realInclusion n)) x :=
    (hKd.hasFDerivAt.restrictScalars ℝ).comp x ((realInclusion n).hasFDerivAt)
  have h3 : HasFDerivAt (realRestriction K) ((realPartCLM₂ n).comp
      (((fderiv ℂ K (realInclusion n x)).restrictScalars ℝ).comp (realInclusion n))) x :=
    (realPartCLM₂ n).hasFDerivAt.comp x h2
  refine ⟨h3.differentiableAt, fun h => ?_⟩
  have h4 := (realInclusion₂ n).hasFDerivAt.comp x h3
  have hfun : (fun y => realInclusion₂ n (realRestriction K y)) = fun y => K (realInclusion n y) :=
    funext fun y => (isRealOnReals_iff.mp hreal y).symm
  have h5 : (realInclusion₂ n).comp ((realPartCLM₂ n).comp
      (((fderiv ℂ K (realInclusion n x)).restrictScalars ℝ).comp (realInclusion n))) =
      ((fderiv ℂ K (realInclusion n x)).restrictScalars ℝ).comp (realInclusion n) := by
    have h4' : HasFDerivAt (fun y => K (realInclusion n y)) ((realInclusion₂ n).comp
      ((realPartCLM₂ n).comp
      (((fderiv ℂ K (realInclusion n x)).restrictScalars ℝ).comp (realInclusion n)))) x := by
      rw [← hfun]; exact h4
    exact h4'.unique h2
  rw [h3.fderiv]
  exact congrArg (fun L => L h) h5

/-- Blueprint `step:p1:rr-consequences`, norm bound: `|Dk(x)| ≤ |DK(x)|` for operator norms of
the max norms. -/
theorem norm_fderiv_realRestriction_le (hρ : 0 < ρ)
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hreal : IsRealOnReals K) (x : Fin n → ℝ) :
    ‖fderiv ℝ (realRestriction K) x‖ ≤ ‖fderiv ℂ K (realInclusion n x)‖ :=
  norm_le_of_isometric_restriction (norm_realInclusion) (norm_realInclusion₂)
    (fderiv ℂ K (realInclusion n x)) (fderiv ℝ (realRestriction K) x)
    fun h => ((realRestriction_fderiv hρ hK hreal x).2 h).symm

/-- Blueprint `bp:p1:real-restriction`. Let `K` be holomorphic on `T_ρ` (`ρ > 0`) and real on
reals, with real restriction `k = Re ∘ K ∘ ι`. Then `k` is real-analytic on `ℝⁿ`; it is
differentiable with real derivative the restriction of the complex derivative,
`ι (Dk(x) h) = DK(x) (ι h)`; `‖Dk(x)‖ ≤ ‖DK(x)‖`; and if `K` is primary on `T_ρ`,
`k (x + m) = k x + (m, 0)` for `m ∈ ℤⁿ`. -/
theorem real_restriction (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) :
    AnalyticOnNhd ℝ (realRestriction K) univ ∧
    (∀ x : Fin n → ℝ, DifferentiableAt ℝ (realRestriction K) x ∧ ∀ h : Fin n → ℝ,
      realInclusion₂ n (fderiv ℝ (realRestriction K) x h) =
        fderiv ℂ K (realInclusion n x) (realInclusion n h)) ∧
    (∀ x : Fin n → ℝ, ‖fderiv ℝ (realRestriction K) x‖ ≤ ‖fderiv ℂ K (realInclusion n x)‖) ∧
    (IsPrimaryOnStrip K ρ → ∀ (x : Fin n → ℝ) (m : Fin n → ℤ),
      realRestriction K (x + fun i => (m i : ℝ)) =
        realRestriction K x + (fun i => (m i : ℝ), 0)) :=
  ⟨analyticOnNhd_realRestriction hρ hK, realRestriction_fderiv hρ hK hreal,
    norm_fderiv_realRestriction_le hρ hK hreal,
    fun hp x m => realRestriction_add_int hρ hp hreal x m⟩

end RealRestriction

theorem realInclusion_single {n : ℕ} (i : Fin n) :
    realInclusion n (Pi.single i 1) = Pi.single i 1 := by
  ext j
  by_cases h : j = i <;> simp [h]

section Hamiltonian

variable {n : ℕ} {V : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {z : (Fin n → ℝ) × (Fin n → ℝ)} {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

/-- Blueprint `step:p1:hr-derivative`. If `h` is holomorphic on the open `V` and real at real
points, and `H` agrees with `Re h` near the real point `z`, then `H` is differentiable at `z` and
`DH(z) e = Dh(z) e` for real `e` (a real number). -/
theorem hamiltonian_real_fderiv (hV : IsOpen V) (hh : DifferentiableOn ℂ h V)
    (hreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ V →
      (h (realInclusion₂ n y)).im = 0)
    (hz : realInclusion₂ n z ∈ V) (hH : ∀ᶠ y in 𝓝 z, H y = (h (realInclusion₂ n y)).re) :
    DifferentiableAt ℝ H z ∧ ∀ e : (Fin n → ℝ) × (Fin n → ℝ),
      ((fderiv ℝ H z e : ℝ) : ℂ) = fderiv ℂ h (realInclusion₂ n z) (realInclusion₂ n e) := by
  have hhd : DifferentiableAt ℂ h (realInclusion₂ n z) := hh.differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun y => h (realInclusion₂ n y))
      (((fderiv ℂ h (realInclusion₂ n z)).restrictScalars ℝ).comp (realInclusion₂ n)) z :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp z ((realInclusion₂ n).hasFDerivAt)
  have h3 : HasFDerivAt (fun y => (h (realInclusion₂ n y)).re)
      (Complex.reCLM.comp
      (((fderiv ℂ h (realInclusion₂ n z)).restrictScalars ℝ).comp (realInclusion₂ n))) z :=
    Complex.reCLM.hasFDerivAt.comp z h2
  have h4 : HasFDerivAt H (Complex.reCLM.comp
      (((fderiv ℂ h (realInclusion₂ n z)).restrictScalars ℝ).comp (realInclusion₂ n))) z :=
    h3.congr_of_eventuallyEq hH
  refine ⟨h4.differentiableAt, fun e => ?_⟩
  have hmem : ∀ᶠ y in 𝓝 z, realInclusion₂ n y ∈ V :=
    (realInclusion₂ n).continuous.continuousAt.eventually_mem (hV.mem_nhds hz)
  have hev : (fun y => h (realInclusion₂ n y)) =ᶠ[𝓝 z] fun y => ((H y : ℝ) : ℂ) := by
    filter_upwards [hH, hmem] with y hy hyV
    rw [hy]
    exact Complex.ext (by simp) (by simpa using hreal y hyV)
  have h5 : HasFDerivAt (fun y => ((H y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ H z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h4.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  simpa using (congrArg (fun L => L e) h6).symm

/-- Blueprint `step:p1:hr-components`. Under the hypotheses of the lemma, the real Hamiltonian
vector field of `H` at `z` is the complex Hamiltonian vector field of `h` at `z`, identifying
`ℝⁿ × ℝⁿ` with the real points of `ℂⁿ × ℂⁿ`. -/
theorem hamiltonianVectorField_eq_of_real (hV : IsOpen V) (hh : DifferentiableOn ℂ h V)
    (hreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ V →
      (h (realInclusion₂ n y)).im = 0)
    (hz : realInclusion₂ n z ∈ V) (hH : ∀ᶠ y in 𝓝 z, H y = (h (realInclusion₂ n y)).re) :
    realInclusion₂ n (hamiltonianVectorField H z) =
      hamiltonianVectorFieldℂ h (realInclusion₂ n z) := by
  have hd := (hamiltonian_real_fderiv hV hh hreal hz hH).2
  have h0 : ∀ e, ((fderiv ℝ H z e : ℝ) : ℂ) = fderiv ℂ h (realInclusion₂ n z) (realInclusion₂ n e)
    := hd
  ext i
  · simpa [hamiltonianVectorField, hamiltonianVectorFieldℂ, realInclusion_single] using
      h0 (0, Pi.single i 1)
  · simpa [hamiltonianVectorField, hamiltonianVectorFieldℂ, realInclusion_single] using
      h0 (Pi.single i 1, 0)

end Hamiltonian

section MatrixForm

variable {n : ℕ}

/-- The column `(Dφ)ᵀ = (∂_θ φ, ∂_I φ)` of partial derivatives of `φ` at `w`, `θ`-block
first. -/
def gradientColumn (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => fderiv ℂ φ w (Pi.single i 1, 0), fun i => fderiv ℂ φ w (0, Pi.single i 1))

/-- The map `J : L(ℂ²ⁿ, ℂ) → ℂ²ⁿ`, `J(ℓ) = ((ℓ(0, eᵢ))ᵢ, (-ℓ(eᵢ, 0))ᵢ)`. -/
def hamiltonianJ (ℓ : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => ℓ (0, Pi.single i 1), fun i => -ℓ (Pi.single i 1, 0))

/-- The frozen complex Hamiltonian vector field is `J` applied to the derivative. -/
theorem hamiltonianVectorFieldℂ_eq_J (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    hamiltonianVectorFieldℂ φ w = hamiltonianJ (fderiv ℂ φ w) := rfl

/-- Blueprint `step:p1:hr-matrix`: `X_φ = J (Dφ)ᵀ` with `J = -Ω₀`. -/
theorem hamiltonianVectorFieldℂ_eq_neg_omegaZero (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    hamiltonianVectorFieldℂ φ w = -omegaZero (gradientColumn φ w) := by
  ext i <;> simp [hamiltonianVectorFieldℂ, omegaZero, gradientColumn]

/-- Blueprint `step:p1:hr-matrix`, equivalent form: `Ω₀ X_φ = (Dφ)ᵀ`. -/
theorem omegaZero_hamiltonianVectorFieldℂ (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    omegaZero (hamiltonianVectorFieldℂ φ w) = gradientColumn φ w := by
  ext i <;> simp [hamiltonianVectorFieldℂ, omegaZero, gradientColumn]

end MatrixForm

section HamiltonianReal

variable {n : ℕ} {V : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {z : (Fin n → ℝ) × (Fin n → ℝ)}
  {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}

/-- Blueprint `bp:p1:hamiltonian-real`. Let `V ⊆ ℂⁿ × ℂⁿ` be open, `h` holomorphic on `V` and
real at the real points of `V`, `z` a real point of `V`, and `H : ℝⁿ × ℝⁿ → ℝ` agree with `Re h`
near `z`. Then `H` is differentiable at `z` and `X_H(z) = X_h(z)` (real points identified with
their images in `ℂⁿ × ℂⁿ`). For every `φ` (holomorphy is not needed for the algebraic identity),
`X_φ = J (Dφ)ᵀ` with `J = -Ω₀`, equivalently `Ω₀ X_φ = (Dφ)ᵀ`. -/
theorem hamiltonian_real (hV : IsOpen V) (hh : DifferentiableOn ℂ h V)
    (hreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), realInclusion₂ n y ∈ V →
      (h (realInclusion₂ n y)).im = 0)
    (hz : realInclusion₂ n z ∈ V) (hH : ∀ᶠ y in 𝓝 z, H y = (h (realInclusion₂ n y)).re) :
    (DifferentiableAt ℝ H z ∧ realInclusion₂ n (hamiltonianVectorField H z) =
      hamiltonianVectorFieldℂ h (realInclusion₂ n z)) ∧
    ∀ (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (w : (Fin n → ℂ) × (Fin n → ℂ)),
      hamiltonianVectorFieldℂ φ w = -omegaZero (gradientColumn φ w) ∧
      omegaZero (hamiltonianVectorFieldℂ φ w) = gradientColumn φ w :=
  ⟨⟨(hamiltonian_real_fderiv hV hh hreal hz hH).1,
      hamiltonianVectorField_eq_of_real hV hh hreal hz hH⟩,
    fun φ w => ⟨hamiltonianVectorFieldℂ_eq_neg_omegaZero φ w,
      omegaZero_hamiltonianVectorFieldℂ φ w⟩⟩

end HamiltonianReal


end KAM
