/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.PPlusOne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# P96-K Lemma 2 in the `λ`-weighted field norms (`bpW:w4:lemma2`)

Off-frontier, source-faithful infrastructure (W4-COMPLETE); the dependency graph is still
being built. Blueprint label: `bpW:w4:lemma2`.

The blueprint writes `|X|^λ = ε_X + λ ε_X^L` for a field (family `ξ ↦ X_ξ`) with uniform bound
`ε_X` and Lipschitz constant `ε_X^L` on the relevant domain. Here these are the best constants,
as extended reals (so that an unbounded field has norm `⊤`):

* `homFieldSup_gen r s' T = sup_{ξ ∈ Π} sup_{w ∈ D(s',r)} |X_{T(ξ)}(w)|_r`;
* `homFieldLip_gen r s' T = sup_{ξ ≠ ζ ∈ Π} sup_{w ∈ D(s',r)} |X_{T(ξ)}(w) - X_{T(ζ)}(w)|_r/|ξ-ζ|`
  (the field of `T(ξ) - T(ζ)` is `X_{T(ξ)} - X_{T(ζ)}`, fields being linear in the components;
  this is the convention of the landed `homLemma1_lipschitz_gen`);
* `homLamFieldNorm_gen r s' λ T = homFieldSup_gen r s' T + λ · homFieldLip_gen r s' T`.

`homFieldSup_le_ofReal_iff`, `homFieldLip_le_ofReal_iff` identify a bound on these suprema with
the pointwise bounds `HomFieldBound_gen` used by the landed W4 theorems.

Main result `homLemma2Complete_gen` (and `homLemma2Complete` at `p_+ = p + 1`): in the setting of
Theorem `bpW:w4:lemma1` with `M = M_ω + M_Ω > 0` and `0 ≤ λ ≤ α/M`,
`|X_{N̂}|^λ_{r,D(s,r)} ≤ 2|X_R|^λ_{r,D(s,r)}`,
`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^W_σ/α)|X_R|^λ_{r,D(s,r)}`, `3C₁ < 108`, and, for `σ ≤ 1`,
`B^W_σ ≤ b_W(τ) σ^{-(2τ+3)}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM
open scoped ENNReal

variable {a p pb s : ℝ}

/-- The uniform part `ε_X = sup_{ξ ∈ Π} sup_{w ∈ D(s',r)} |X_{T(ξ)}(w)|_r` of the `λ`-norm. -/
def homFieldSup_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (r s' : ℝ)
    {Par : Set (Fin 2 → ℝ)} (T : Par → HomTaylor_gen a p pb s) : ℝ≥0∞ :=
  ⨆ ξ : Par, ⨆ θ : Fin 2 → ℂ, ⨆ y : Fin 2 → ℂ, ⨆ z : HomL2, ⨆ zb : HomL2,
    ⨆ (_ : HomDomain s' r θ y z zb), ENNReal.ofReal (homXnorm_gen ha hp hpb r (T ξ) θ y z zb)

/-- The Lipschitz part
`ε_X^L = sup_{ξ ≠ ζ ∈ Π} sup_{w ∈ D(s',r)} |X_{T(ξ)}(w) - X_{T(ζ)}(w)|_r / |ξ - ζ|`. -/
def homFieldLip_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (r s' : ℝ)
    {Par : Set (Fin 2 → ℝ)} (T : Par → HomTaylor_gen a p pb s) : ℝ≥0∞ :=
  ⨆ ξ : Par, ⨆ ζ : Par, ⨆ (_ : ξ ≠ ζ), ⨆ θ : Fin 2 → ℂ, ⨆ y : Fin 2 → ℂ, ⨆ z : HomL2,
    ⨆ zb : HomL2, ⨆ (_ : HomDomain s' r θ y z zb),
      ENNReal.ofReal (homXnorm_gen ha hp hpb r ((T ξ).homSub (T ζ)) θ y z zb /
        ‖(ξ : Fin 2 → ℝ) - ζ‖)

/-- **The `λ`-weighted field norm** `|X|^λ_{r,D(s',r)} = ε_X + λ ε_X^L` (`bpW:w4:lemma2`) of the
field family `ξ ↦ X_{T(ξ)}`. -/
def homLamFieldNorm_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (r s' lam : ℝ)
    {Par : Set (Fin 2 → ℝ)} (T : Par → HomTaylor_gen a p pb s) : ℝ≥0∞ :=
  homFieldSup_gen ha hp hpb r s' T + ENNReal.ofReal lam * homFieldLip_gen ha hp hpb r s' T

theorem homFieldSup_le_ofReal_iff (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r s' ε : ℝ}
    (hε : 0 ≤ ε) {Par : Set (Fin 2 → ℝ)} (T : Par → HomTaylor_gen a p pb s) :
    homFieldSup_gen ha hp hpb r s' T ≤ ENNReal.ofReal ε ↔
      ∀ ξ : Par, ∀ θ y z zb, HomDomain s' r θ y z zb →
        homXnorm_gen ha hp hpb r (T ξ) θ y z zb ≤ ε := by
  simp only [homFieldSup_gen, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hε]

theorem homPar_norm_sub_pos {Par : Set (Fin 2 → ℝ)} {ξ ζ : Par} (h : ξ ≠ ζ) :
    0 < ‖(ξ : Fin 2 → ℝ) - ζ‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (Subtype.coe_injective.ne h))

theorem homFieldLip_le_ofReal_iff (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r s' ε : ℝ}
    (hε : 0 ≤ ε) {Par : Set (Fin 2 → ℝ)} (T : Par → HomTaylor_gen a p pb s) :
    homFieldLip_gen ha hp hpb r s' T ≤ ENNReal.ofReal ε ↔
      ∀ ξ ζ : Par, ξ ≠ ζ → ∀ θ y z zb, HomDomain s' r θ y z zb →
        homXnorm_gen ha hp hpb r ((T ξ).homSub (T ζ)) θ y z zb ≤ ε * ‖(ξ : Fin 2 → ℝ) - ζ‖ := by
  simp only [homFieldLip_gen, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hε]
  constructor
  · intro H ξ ζ h θ y z zb hD
    exact (div_le_iff₀ (homPar_norm_sub_pos h)).mp (H ξ ζ h θ y z zb hD)
  · intro H ξ ζ h θ y z zb hD
    exact (div_le_iff₀ (homPar_norm_sub_pos h)).mpr (H ξ ζ h θ y z zb hD)

/-- `B^W_σ > 0` for `τ ≥ 0`, `σ > 0`. -/
theorem homWaveBW_pos {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) : 0 < waveBW τ σ := by
  have hle := (waveBW_summable hτ hσ).le_tsum 0 (fun k _ => by
    have := Fourier.modeSize_nonneg k; have := waveA_ge_one (τ := τ) k; positivity)
  refine lt_of_lt_of_le ?_ hle
  have := Fourier.modeSize_nonneg (0 : Fin 2 → ℤ)
  have := waveA_ge_one (τ := τ) (0 : Fin 2 → ℤ)
  positivity

section nhat

/-- `ε_{X_{N̂}} ≤ 2 ε_{X_R}` on `D(s,r)`. -/
theorem homNhat_fieldSup_le (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r : ℝ} (hr : 0 < r)
    (hs : 0 < s) {Par : Set (Fin 2 → ℝ)} (R : Par → HomTaylor_gen a p pb s) :
    homFieldSup_gen ha hp hpb r s (fun ξ => homNhatTaylor_gen (R ξ)) ≤
      2 * homFieldSup_gen ha hp hpb r s R := by
  by_cases hu : homFieldSup_gen ha hp hpb r s R = ⊤
  · rw [hu, ENNReal.mul_top (by norm_num)]; exact le_top
  · have hb := (homFieldSup_le_ofReal_iff ha hp hpb ENNReal.toReal_nonneg R).mp
      (ENNReal.ofReal_toReal hu).ge
    calc _ ≤ ENNReal.ofReal (2 * (homFieldSup_gen ha hp hpb r s R).toReal) :=
          (homFieldSup_le_ofReal_iff ha hp hpb (by positivity) _).mpr fun ξ =>
            homNhat_fieldBound_gen ha hp hpb hr hs (R ξ) (hb ξ)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hu]; simp

/-- `ε^L_{X_{N̂}} ≤ 2 ε^L_{X_R}` on `D(s,r)`. -/
theorem homNhat_fieldLip_le (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r : ℝ} (hr : 0 < r)
    (hs : 0 < s) {Par : Set (Fin 2 → ℝ)} (R : Par → HomTaylor_gen a p pb s) :
    homFieldLip_gen ha hp hpb r s (fun ξ => homNhatTaylor_gen (R ξ)) ≤
      2 * homFieldLip_gen ha hp hpb r s R := by
  by_cases hu : homFieldLip_gen ha hp hpb r s R = ⊤
  · rw [hu, ENNReal.mul_top (by norm_num)]; exact le_top
  · have hb := (homFieldLip_le_ofReal_iff ha hp hpb ENNReal.toReal_nonneg R).mp
      (ENNReal.ofReal_toReal hu).ge
    calc _ ≤ ENNReal.ofReal (2 * (homFieldLip_gen ha hp hpb r s R).toReal) :=
          (homFieldLip_le_ofReal_iff ha hp hpb (by positivity) _).mpr fun ξ ζ hne θ y z zb hD =>
            (homNhat_lipschitz_gen ha hp hpb hr hs (R ξ) (R ζ) (hb ξ ζ hne) θ y z zb hD).trans_eq
              (by ring)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hu]; simp

end nhat

section solve

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ σ τ α : ℝ}

/-- The family `ξ ↦ F(·,ξ)` of solutions of the homological equation (`bpW:w4:lemma1`). -/
def homSolveFamily_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (R : Par → HomTaylor_gen a p pb s) :
    Par → HomTaylor_gen a p pb (s - σ) :=
  fun ξ => homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH ξ.2) (R ξ)

/-- `ε_{X_F} ≤ (C₁B^W_σ/α) ε_{X_R}` (`F` on `D(s-σ,r)`, `R` on `D(s,r)`). -/
theorem homSolve_fieldSup_le (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) (R : Par → HomTaylor_gen a p pb s) :
    homFieldSup_gen ha hp hpb r (s - σ) (homSolveFamily_gen h hH hτ hα hσ hσs R) ≤
      ENNReal.ofReal ((7 + 10 * homKS) * waveBW τ σ / α) * homFieldSup_gen ha hp hpb r s R := by
  have hK : 0 < (7 + 10 * homKS) * waveBW τ σ / α := by
    have := homWaveBW_pos hτ hσ; have := one_le_homKS; positivity
  by_cases hu : homFieldSup_gen ha hp hpb r s R = ⊤
  · rw [hu, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK).ne']; exact le_top
  · set ε := (homFieldSup_gen ha hp hpb r s R).toReal with hεdef
    have hε : 0 ≤ ε := ENNReal.toReal_nonneg
    have hb := (homFieldSup_le_ofReal_iff ha hp hpb hε R).mp (ENNReal.ofReal_toReal hu).ge
    have hE0 : 0 ≤ (7 + 10 * homKS) * (waveBW τ σ * ε / α) := by
      have := waveBW_nonneg τ σ; have := one_le_homKS; positivity
    calc _ ≤ ENNReal.ofReal ((7 + 10 * homKS) * (waveBW τ σ * ε / α)) :=
          (homFieldSup_le_ofReal_iff ha hp hpb hE0 _).mpr fun ξ =>
            homLemma1_fieldBound_gen h hH ha hp hpb hr hτ hα hσ hσs ξ.2 (R ξ) (hb ξ)
      _ = ENNReal.ofReal ((7 + 10 * homKS) * waveBW τ σ / α) * ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring
      _ = _ := by rw [hεdef, ENNReal.ofReal_toReal hu]

/-- `ε^L_{X_F} ≤ (C₁B^W_σ/α)(ε^L_{X_R} + (2M/α) ε_{X_R})` (`M = M_ω + M_Ω > 0`). -/
theorem homSolve_fieldLip_le (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) (hM : 0 < Mω + MΩ) (R : Par → HomTaylor_gen a p pb s) :
    homFieldLip_gen ha hp hpb r (s - σ) (homSolveFamily_gen h hH hτ hα hσ hσs R) ≤
      ENNReal.ofReal ((7 + 10 * homKS) * waveBW τ σ / α) *
        (homFieldLip_gen ha hp hpb r s R +
          ENNReal.ofReal (2 * (Mω + MΩ) / α) * homFieldSup_gen ha hp hpb r s R) := by
  have hK : 0 < (7 + 10 * homKS) * waveBW τ σ / α := by
    have := homWaveBW_pos hτ hσ; have := one_le_homKS; positivity
  have hm : 0 < 2 * (Mω + MΩ) / α := by positivity
  have hK0 := (ENNReal.ofReal_pos.mpr hK).ne'
  by_cases hl : homFieldLip_gen ha hp hpb r s R = ⊤
  · rw [hl, top_add, ENNReal.mul_top hK0]; exact le_top
  by_cases hu : homFieldSup_gen ha hp hpb r s R = ⊤
  · rw [hu, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hm).ne', add_top, ENNReal.mul_top hK0]
    exact le_top
  set ε := (homFieldSup_gen ha hp hpb r s R).toReal with hεdef
  set εL := (homFieldLip_gen ha hp hpb r s R).toReal with hεLdef
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg
  have hεL : 0 ≤ εL := ENNReal.toReal_nonneg
  have hb := (homFieldSup_le_ofReal_iff ha hp hpb hε R).mp (ENNReal.ofReal_toReal hu).ge
  have hbL := (homFieldLip_le_ofReal_iff ha hp hpb hεL R).mp (ENNReal.ofReal_toReal hl).ge
  have hE : 0 ≤ (7 + 10 * homKS) * waveBW τ σ / α * (εL + 2 * (Mω + MΩ) / α * ε) := by
    have := waveBW_nonneg τ σ; have := one_le_homKS; positivity
  calc _ ≤ ENNReal.ofReal ((7 + 10 * homKS) * waveBW τ σ / α *
          (εL + 2 * (Mω + MΩ) / α * ε)) :=
        (homFieldLip_le_ofReal_iff ha hp hpb hE _).mpr fun ξ ζ hne θ y z zb hD =>
          (homLemma1_lipschitz_gen h hH ha hp hpb hr hτ hα hεL hσ hσs ξ.2 ζ.2 (R ξ) (R ζ)
            (hb ξ) (hb ζ) (hbL ξ ζ hne) θ y z zb hD).trans_eq (by ring)
    _ = _ := by
        rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_add hεL (by positivity),
          ENNReal.ofReal_mul hm.le, hεdef, hεLdef, ENNReal.ofReal_toReal hu,
          ENNReal.ofReal_toReal hl]

end solve

section main

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ σ τ α : ℝ}

/-- **P96-K Lemma 2 in the `λ`-weighted field norms** (blueprint `bpW:w4:lemma2`; general `p_+`):
in the setting of Theorem `bpW:w4:lemma1` with `M = M_ω + M_Ω > 0` and `0 ≤ λ ≤ α/M`, for every
family `R : Π → 𝒯_s`, with `F = homSolveFamily_gen … R` and `N̂ = homNhatTaylor_gen R`:
`|X_{N̂}|^λ_{r,D(s,r)} ≤ 2|X_R|^λ_{r,D(s,r)}`,
`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^W_σ/α)|X_R|^λ_{r,D(s,r)}` (`C₁ = 7 + 10K_S`), `3C₁ < 108`, and,
for `0 < σ ≤ 1`, `B^W_σ ≤ b_W(τ) σ^{-(2τ+3)}` (bound (4) of P96-K with `n = 2`). -/
theorem homLemma2Complete_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r lam : ℝ}
    (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hM : 0 < Mω + MΩ)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ α / (Mω + MΩ)) (R : Par → HomTaylor_gen a p pb s) :
    homLamFieldNorm_gen ha hp hpb r s lam (fun ξ => homNhatTaylor_gen (R ξ)) ≤
        2 * homLamFieldNorm_gen ha hp hpb r s lam R ∧
      homLamFieldNorm_gen ha hp hpb r (s - σ) lam (homSolveFamily_gen h hH hτ hα hσ hσs R) ≤
        ENNReal.ofReal (3 * (7 + 10 * homKS) * waveBW τ σ / α) *
          homLamFieldNorm_gen ha hp hpb r s lam R ∧
      3 * (7 + 10 * homKS) < 108 ∧
      (σ ≤ 1 → waveBW τ σ ≤ waveBWconst τ / σ ^ (2 * τ + 3)) := by
  have hs : 0 < s := hσ.trans hσs
  refine ⟨?_, ?_, ?_, fun hσ1 => waveBW_le hτ hσ hσ1⟩
  · unfold homLamFieldNorm_gen
    calc _ ≤ 2 * homFieldSup_gen ha hp hpb r s R +
          ENNReal.ofReal lam * (2 * homFieldLip_gen ha hp hpb r s R) :=
          add_le_add (homNhat_fieldSup_le ha hp hpb hr hs R)
            (mul_le_mul' le_rfl (homNhat_fieldLip_le ha hp hpb hr hs R))
      _ = _ := by ring
  · unfold homLamFieldNorm_gen
    set K := ENNReal.ofReal ((7 + 10 * homKS) * waveBW τ σ / α)
    set m := ENNReal.ofReal (2 * (Mω + MΩ) / α)
    set u := homFieldSup_gen ha hp hpb r s R
    set l := homFieldLip_gen ha hp hpb r s R
    set L := ENNReal.ofReal lam
    have hLm : L * m ≤ 2 := by
      rw [← ENNReal.ofReal_mul hlam0, ← ENNReal.ofReal_ofNat 2]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : lam * (Mω + MΩ) ≤ α := by rwa [le_div_iff₀ hM] at hlam
      rw [mul_div_assoc', div_le_iff₀ hα]
      nlinarith
    have h3 : (ENNReal.ofReal (3 * (7 + 10 * homKS) * waveBW τ σ / α)) = 3 * K := by
      rw [show 3 * (7 + 10 * homKS) * waveBW τ σ / α = 3 * ((7 + 10 * homKS) * waveBW τ σ / α)
        by ring, ENNReal.ofReal_mul (by norm_num)]
      simp [K]
    rw [h3]
    calc _ ≤ K * u + L * (K * (l + m * u)) :=
          add_le_add (homSolve_fieldSup_le h hH ha hp hpb hr hτ hα hσ hσs R)
            (mul_le_mul' le_rfl (homSolve_fieldLip_le h hH ha hp hpb hr hτ hα hσ hσs hM R))
      _ = K * (u + (L * m) * u + L * l) := by ring
      _ ≤ K * (u + 2 * u + 3 * (L * l)) := by
          have h1 : L * m * u ≤ 2 * u := mul_le_mul' hLm le_rfl
          have h2 : L * l ≤ 3 * (L * l) := le_mul_of_one_le_left' (by norm_num)
          exact mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl h1) h2)
      _ = 3 * K * (u + L * l) := by ring
  · have hK := homKS_lt_29
    norm_num at hK ⊢
    linarith

/-- The `λ`-weighted field norm at `p_+ = p + 1`. -/
abbrev homLamFieldNorm (ha : 0 ≤ a) (hp : 0 ≤ p) (r s' lam : ℝ) {Par : Set (Fin 2 → ℝ)}
    (T : Par → HomTaylor a p s) : ℝ≥0∞ :=
  homLamFieldNorm_gen ha hp (homPlusOne_le p) r s' lam T

/-- **P96-K Lemma 2 in the `λ`-weighted field norms, `p_+ = p + 1`** (blueprint
`bpW:w4:lemma2`; the original W4 setting): the statement of `homLemma2Complete_gen`. -/
theorem homLemma2Complete (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) {r lam : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ)
    (hσs : σ < s) (hM : 0 < Mω + MΩ) (hlam0 : 0 ≤ lam) (hlam : lam ≤ α / (Mω + MΩ))
    (R : Par → HomTaylor a p s) :
    homLamFieldNorm ha hp r s lam (fun ξ => homNhatTaylor (R ξ)) ≤
        2 * homLamFieldNorm ha hp r s lam R ∧
      homLamFieldNorm ha hp r (s - σ) lam (homSolveFamily_gen h hH hτ hα hσ hσs R) ≤
        ENNReal.ofReal (3 * (7 + 10 * homKS) * waveBW τ σ / α) *
          homLamFieldNorm ha hp r s lam R ∧
      3 * (7 + 10 * homKS) < 108 ∧
      (σ ≤ 1 → waveBW τ σ ≤ waveBWconst τ / σ ^ (2 * τ + 3)) :=
  homLemma2Complete_gen h hH ha hp (homPlusOne_le p) hr hτ hα hσ hσs hM hlam0 hlam R

end main

end KAM.Wave
