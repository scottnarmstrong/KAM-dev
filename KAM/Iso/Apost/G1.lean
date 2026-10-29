/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Limit
public import KAM.Iso.Charts.Inputs
import KAM.Iso.Linear.Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# I-G1 with explicit constants

Blueprint node `bpI:p2:g1`
(`KAM.Iso.Apost.g1_explicit`): the frozen statement of `KAM.Iso.isoenergetic_kam` with the explicit
constants

* `C₁ = ρ^{4τ} max {γ̄⁴, ĉ_* δ₀^{-2a}}` (`KAM.Iso.Apost.isoC1`),
* `C₂ = C₃ = 2 Ĉ_Δ ρ^{2τ} δ₀^{-a}` (`KAM.Iso.Apost.isoC2`).

The body of the frozen statement after `∃ C₁ C₂ C₃, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧` is the definition
`KAM.Iso.Charts.IG1Body` (decision D20), so `g1_explicit` concludes
`0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ IG1Body … C₁ C₂ C₃` at the explicit constants, with the frozen binders
in the frozen order. The provider `KAM.Provider.Iso.isoenergetic_kam` is the anonymous constructor
`⟨_, _, _, g1_explicit …⟩`.

The proof follows the blueprint and `KAM/Apost/G1.lean`.

* `step:p2:g1-constants`: `0 < C₁` and `0 < C₂` (`isoC1_pos`, `isoC2_pos`) from `one_le_hatCDelta`
  and `KAM.Apost.delta0_pos`.
* `step:p2:g1-standing`: the structure `IsoStanding` is built from (I1)–(I4) (five bounds), the
  parameter binders, `σ_ω > 1`, `ν > 0`, `ω* ≠ 0` and `ω* ∈ Dio_{γ,τ}`.
* `step:p2:g1-e`: `KAM.Apost.g1_error_small_aux` gives `e < 1` and `ĉ_* e/(γ⁴ δ₀^{2a}) < 1`.
* `step:p2:g1-apply`: the row sums of (I7), (I8) become operator norms
  (`norm_le_of_rowSum_le_of_nonempty`, from `KAM.norm_le_iff_forall_rowSum`), the two inequalities
  of (I9) become `ν ≤ ν(s)` (`margin_of_le`), and `limit`, `energy_limit` apply.
* `step:p2:g1-check`: the clauses of the conclusion are those of `limit`; the energy clause (O3) is
  `energy_limit` (`Ē_H(K_∞) = E₀`) combined with `KAM.Iso.Linear.energy_conservation` at the
  frequency `s_∞ ω*` (no frame of `K_∞` is used); and
  `2 Ĉ_Δ e/(γ² δ₀^a) = C₂ e/(γ² ρ^{2τ})` (`KAM.Apost.g1_closeness_eq`).

`T_r` is `complexStrip n r`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

/-- Step `step:p2:g1-constants`: `C₁ > 0`. -/
theorem isoC1_pos {n : ℕ} {τ ρ ρinf M σK σB σT μ ν γbar : ℝ} (hρ : 0 < ρ) (hγbar : 0 < γbar) :
    0 < isoC1 n τ ρ ρinf M σK σB σT μ ν γbar :=
  mul_pos (Real.rpow_pos_of_pos hρ _) (lt_max_of_lt_left (pow_pos hγbar 4))

/-- Step `step:p2:g1-constants`: `C₂ > 0`. -/
theorem isoC2_pos {n : ℕ} {τ ρ ρinf M σK σB σT : ℝ} (hP : Params n τ M σK σB σT) (hρ : 0 < ρ)
    (hρinf : ρinf < ρ) : 0 < isoC2 n τ ρ ρinf M σK σB σT :=
  mul_pos (mul_pos (mul_pos two_pos (zero_lt_one.trans_le (one_le_hatCDelta hP)))
    (Real.rpow_pos_of_pos hρ _)) (Real.rpow_pos_of_pos (delta0_pos hρinf) _)

/-- A bound on all absolute row sums of a square matrix with at least one row is a bound on its
operator norm (the bound is nonnegative since a row sum is). Index-generic: this is used for the
bordered matrices over `Fin n ⊕ Unit`. -/
theorem norm_le_of_rowSum_le_of_nonempty {m : Type*} [Fintype m] [Nonempty m]
    {M : Matrix m m ℂ} {B : ℝ} (h : ∀ i, ∑ j, ‖M i j‖ ≤ B) : ‖M‖ ≤ B := by
  obtain ⟨i₀⟩ := ‹Nonempty m›
  have hB : 0 ≤ B := (Finset.sum_nonneg fun j _ => norm_nonneg (M i₀ j)).trans (h i₀)
  exact (norm_le_iff_forall_rowSum hB).2 h

/-- Step `step:p2:g1-apply`: the two inequalities `ν ≤ (s - 1)|ω*|`, `ν ≤ (σ_ω - s)|ω*|` of (I9)
give `ν ≤ ν(s)`. -/
theorem margin_of_le {n : ℕ} {σω ν s : ℝ} {ωstar : Fin n → ℝ} (h1 : ν ≤ (s - 1) * ‖ωstar‖)
    (h2 : ν ≤ (σω - s) * ‖ωstar‖) : ν ≤ rayMargin σω ωstar s := by
  unfold rayMargin
  rw [min_mul_of_nonneg _ _ (norm_nonneg ωstar)]
  exact le_min h1 h2

/-- Step `step:p2:g1-e`: the hypothesis `C₁ e/(γ⁴ ρ^{4τ}) < 1` of `bpI:p2:g1`, with
`C₁ = ρ^{4τ} max {γ̄⁴, ĉ_* δ₀^{-2a}}`, gives `e < 1` and `ĉ_* e/(γ⁴ δ₀^{2a}) < 1`. -/
theorem iso_g1_error_small {n : ℕ} {τ M σK σB σT : ℝ} (hP : Params n τ M σK σB σT)
    {ρ ρinf γ γbar μ ν e : ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (h : isoC1 n τ ρ ρinf M σK σB σT μ ν γbar * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1) :
    e < 1 ∧ hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) < 1 :=
  g1_error_small_aux (hρinf.trans hρ) hγ hγγbar (delta0_pos hρ)
    (zero_le_one.trans (one_le_hatcStar hP μ ν)) h

/-- Blueprint `bpI:p2:g1`: the frozen I-G1 with the explicit `C₁ = isoC1`, `C₂ = C₃ = isoC2`
(the frozen body is `IG1Body`, verbatim; the binders are the frozen ones, in the frozen order). -/
theorem g1_explicit {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0) :
    0 < isoC1 n τ ρ ρinf M σK σB σT μ ν γbar ∧ 0 < isoC2 n τ ρ ρinf M σK σB σT ∧
      0 < isoC2 n τ ρ ρinf M σK σB σT ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (isoC1 n τ ρ ρinf M σK σB σT μ ν γbar) (isoC2 n τ ρ ρinf M σK σB σT)
        (isoC2 n τ ρ ρinf M σK σB σT) := by
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  refine ⟨isoC1_pos hρ0 hγbar, isoC2_pos hP hρ0 hρinfρ, isoC2_pos hP hρ0 hρinfρ, ?_⟩
  intro D H K s γ e E₀ hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ
    hν1 hν2 hγ hγγbar hdio he0 hE hEn hC1
  -- step `g1-standing`
  have hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ :=
    { toParams := hP
      σω_gt := hσω
      ν_pos := hν
      ωstar_ne := hωstar
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := hbd
      gamma_pos := hγ
      dio := hdio }
  -- step `g1-e`
  obtain ⟨he1, hsm⟩ := iso_g1_error_small hP hρinf hρinfρ hγ hγγbar hC1
  -- step `g1-apply`: row sums become operator norms
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hG': ∀ θ ∈ complexStrip n ρ,
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ := fun θ hθ =>
    ⟨(hG θ hθ).1, norm_le_of_rowSum_le_of_nonempty (m := Fin n) (hG θ hθ).2⟩
  have hT' : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det ∧
      ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ σT - μ :=
    ⟨hTu, norm_le_of_rowSum_le_of_nonempty hTb⟩
  have hIter : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s K :=
    { holo := hK
      primary := hKp
      real := hKr
      ball_sub := hball
      deriv_le := hDK
      gram := hG'
      twist := hT'
      s_gt := hs1
      margin := margin_of_le hν1 hν2
      error_le := hE
      energy_le := hEn }
  obtain ⟨⟨-, -, -, hholoK, hprim, hrealK⟩, ⟨hclose, hsclose, -, -⟩, ⟨hs1', hsσ', -⟩, hmarg,
      hinv⟩ :=
    limit hS hρinf hρinfρ hμ hIter he1.le hsm.le
  -- step `g1-check`: the energy clause (O3), pointwise, by invariance and nonresonance
  have hEnergy := (energy_limit hS hρinf hρinfρ hμ hIter he1.le hsm.le).1
  have hKD : ∀ θ ∈ complexStrip n ρinf, isoLimit H K ωstar E₀ s ρ ρinf θ ∈ D := fun θ hθ =>
    (hmarg θ hθ).1 (Metric.mem_ball_self (half_pos hμ))
  have hcons := (energy_conservation (hS.setting hs1'.le) hρinf hholoK hprim hrealK hKD hinv).2.1
    (E₀ : ℂ) hEnergy
  have hd0 := delta0_pos hρinfρ
  have hcl : 2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) =
      isoC2 n τ ρ ρinf M σK σB σT * e / (γ ^ 2 * ρ ^ (2 * τ)) :=
    g1_closeness_eq (τ' := τ) hρ0 hγ hd0
  refine ⟨isoLimit H K ωstar E₀ s ρ ρinf, isoSLimit H K ωstar E₀ s ρ ρinf, hs1', hsσ', hholoK,
    hprim, hrealK, hinv, hcons, fun θ hθ => (hmarg θ hθ).1, fun θ hθ => (hmarg θ hθ).2,
    fun θ hθ => ?_, ?_⟩
  · exact (hclose θ hθ).trans_eq hcl
  · exact hsclose.trans_eq hcl

end KAM.Iso.Apost

end
