/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Embed
public import KAM.Frozen.Wave.Defs.WaveSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# KAM phase space, domains and norms (blueprint-W `bpW:w1:kam-space`, `bpW:w1:kam-conventions`,
`bpW:w1:kam-domain`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

The complex phase space `𝒫^{a,p}_ℂ = ℂ² × ℂ² × ℓ^{a,p}_ℂ × ℓ^{a,p}_ℂ` is represented in weighted
coordinates (`KamPhase`): the last two factors are `ℓ²_ℂ`, and the norm `‖u‖_{a,p}` of a point of
`ℓ^{a,p}` is the `ℓ²` norm of its representative. The weights therefore only enter through the
representatives: the inclusion `𝒫^{a,p} ⊂ 𝒫^{a,p̄}` (`p̄ ≤ p`) is `kamEmbed`, the diagonal
operator of `bpW:w1:embed`.

* `kamNorm r W = |W|_{p̄,r}` and `kamDomain s r = D(s,r)` (`bpW:w1:kam-space`);
* `kamOpNorm L = |L|_{r,s}` on `KamBoundedMap r s` (positive radii, bounded maps): the least
  admissible constant (`kamOpNorm_isLeast`, `kamOpNorm_apply_le`); `kamNorm` is a norm only for
  `0 < r` (`kamNorm_eq_zero`);
* `kamDomain_isOpen`, `kamDomain_convex`, `kamDomain_mono`, `kamDomain_add_mem`,
  `kamNorm_embed_le`, `kamNorm_le_of_le_radius` (`bpW:w1:kam-domain`);
* the conventions of `bpW:w1:kam-conventions`: `kam_conj_relabel`, `kam_wave_norm_sum_le`,
  `kam_wave_norm_sum_ge`, `kam_strip_period_conversion`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open Metric

/-- The complex phase space `ℂ² × ℂ² × ℓ² × ℓ²` in weighted coordinates, points `(θ, y, u, v)`. -/
abbrev KamPhase : Type :=
  (Fin 2 → ℂ) × (Fin 2 → ℂ) × lp (fun _ : ℕ+ => ℂ) 2 × lp (fun _ : ℕ+ => ℂ) 2

/-- The norm `|W|_{p̄,r} = |Θ| + |Y|/r² + ‖U‖/r + ‖V‖/r` (max norm on `ℂ²`, `ℓ²` norms of the
representatives). (blueprint `bpW:w1:kam-space`) -/
def kamNorm (r : ℝ) (W : KamPhase) : ℝ :=
  ‖W.1‖ + ‖W.2.1‖ / r ^ 2 + ‖W.2.2.1‖ / r + ‖W.2.2.2‖ / r

/-- The domain `D(s,r) = {max_i |Im θ_i| < s, |y| < r², ‖u‖ + ‖v‖ < r}`.
(blueprint `bpW:w1:kam-space`) -/
def kamDomain (s r : ℝ) : Set KamPhase :=
  {z | (∀ i, |(z.1 i).im| < s) ∧ ‖z.2.1‖ < r ^ 2 ∧ ‖z.2.2.1‖ + ‖z.2.2.2‖ < r}

/-- The inclusion `𝒫^{a,p}_ℂ ⊂ 𝒫^{a,p̄}_ℂ` (`p̄ ≤ p`) in weighted coordinates: the diagonal operator
`D_μ`, `μ_j = ω_{a,p̄}(j)/ω_{a,p}(j)`, on the two sequence factors. -/
def kamEmbed (a p p' : ℝ) (hp : p' ≤ p) (W : KamPhase) : KamPhase :=
  (W.1, W.2.1, embedCLM a p a p' le_rfl hp W.2.2.1, embedCLM a p a p' le_rfl hp W.2.2.2)

/-- `C` is an admissible constant for `L` at radii `r, s`: `C ≥ 0` and `|L W|_r ≤ C |W|_s`. -/
def KamOpAdmissible (r s : ℝ) (L : KamPhase →ₗ[ℂ] KamPhase) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ W, kamNorm r (L W) ≤ C * kamNorm s W

/-- The source carrier of `|L|_{r,s}` (blueprint `bpW:w1:kam-space`): positive radii and a
linear map with an admissible bound (a bounded map). -/
structure KamBoundedMap (r s : ℝ) where
  /-- The underlying linear map. -/
  toLinear : KamPhase →ₗ[ℂ] KamPhase
  pos_r : 0 < r
  pos_s : 0 < s
  bounded : ∃ C, KamOpAdmissible r s toLinear C

/-- `|L|_{r,s}`: the least admissible `C ≥ 0` with `|L W|_{r} ≤ C |W|_{s}` for all `W`
(blueprint `bpW:w1:kam-space`; the operator norm for the norms `kamNorm`). Defined on bounded maps
with positive radii only; `kamOpNorm_isLeast` is the least-admissible characterization. -/
def kamOpNorm {r s : ℝ} (L : KamBoundedMap r s) : ℝ :=
  sInf {C : ℝ | KamOpAdmissible r s L.toLinear C}

theorem kamNorm_nonneg {r : ℝ} (hr : 0 ≤ r) (W : KamPhase) : 0 ≤ kamNorm r W := by
  unfold kamNorm; positivity

theorem kamNorm_eq_zero {r : ℝ} (hr : 0 < r) {W : KamPhase} (h : kamNorm r W = 0) : W = 0 := by
  unfold kamNorm at h
  have h1 : 0 ≤ ‖W.1‖ := norm_nonneg _
  have h2 : 0 ≤ ‖W.2.1‖ / r ^ 2 := by positivity
  have h3 : 0 ≤ ‖W.2.2.1‖ / r := by positivity
  have h4 : 0 ≤ ‖W.2.2.2‖ / r := by positivity
  have e1 : ‖W.1‖ = 0 := by linarith
  have e2 : ‖W.2.1‖ / r ^ 2 = 0 := by linarith
  have e3 : ‖W.2.2.1‖ / r = 0 := by linarith
  have e4 : ‖W.2.2.2‖ / r = 0 := by linarith
  have e2' : ‖W.2.1‖ = 0 := by
    rcases div_eq_zero_iff.mp e2 with h | h
    · exact h
    · exact absurd h (by positivity)
  have e3' : ‖W.2.2.1‖ = 0 := by
    rcases div_eq_zero_iff.mp e3 with h | h
    · exact h
    · exact absurd h hr.ne'
  have e4' : ‖W.2.2.2‖ = 0 := by
    rcases div_eq_zero_iff.mp e4 with h | h
    · exact h
    · exact absurd h hr.ne'
  exact Prod.ext (norm_eq_zero.mp e1) (Prod.ext (norm_eq_zero.mp e2')
    (Prod.ext (norm_eq_zero.mp e3') (norm_eq_zero.mp e4')))

/-- The operator norm is admissible: `|L W|_r ≤ |L|_{r,s} |W|_s`. -/
theorem kamOpNorm_apply_le {r s : ℝ} (L : KamBoundedMap r s) (W : KamPhase) :
    kamNorm r (L.toLinear W) ≤ kamOpNorm L * kamNorm s W := by
  obtain ⟨C, hC0, hC⟩ := L.bounded
  by_cases hW : kamNorm s W = 0
  · have := kamNorm_eq_zero L.pos_s hW
    subst this
    simp [kamNorm]
  · have hpos : 0 < kamNorm s W :=
      lt_of_le_of_ne (kamNorm_nonneg L.pos_s.le _) (Ne.symm hW)
    rw [← div_le_iff₀ hpos]
    refine le_csInf ⟨C, hC0, hC⟩ ?_
    rintro C' ⟨-, hC'⟩
    rw [div_le_iff₀ hpos]
    exact hC' W

theorem kamOpNorm_nonneg {r s : ℝ} (L : KamBoundedMap r s) : 0 ≤ kamOpNorm L :=
  Real.sInf_nonneg fun _ h => h.1

/-- The operator norm is below every admissible constant. -/
theorem kamOpNorm_le {r s C : ℝ} (L : KamBoundedMap r s) (hC : KamOpAdmissible r s L.toLinear C) :
    kamOpNorm L ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ hC

/-- **Least admissible constant**: `|L|_{r,s}` is admissible and below every admissible `C`. -/
theorem kamOpNorm_isLeast {r s : ℝ} (L : KamBoundedMap r s) :
    IsLeast {C : ℝ | KamOpAdmissible r s L.toLinear C} (kamOpNorm L) :=
  ⟨⟨kamOpNorm_nonneg L, kamOpNorm_apply_le L⟩, fun _ hC => kamOpNorm_le L hC⟩

/-! ### Domains (`bpW:w1:kam-domain`) -/

theorem kamDomain_isOpen (s r : ℝ) : IsOpen (kamDomain s r) := by
  have h1 : IsOpen {z : KamPhase | ∀ i, |(z.1 i).im| < s} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    exact isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {z : KamPhase | ‖z.2.1‖ < r ^ 2} := isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {z : KamPhase | ‖z.2.2.1‖ + ‖z.2.2.2‖ < r} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

theorem kam_convex_lt {x y a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : x < r)
    (hy : y < r) : a * x + b * y < r := by
  rcases ha.eq_or_lt with rfl | hapos
  · have : b = 1 := by linarith
    subst this
    simpa using hy
  · have h1 : a * x < a * r := mul_lt_mul_of_pos_left hx hapos
    have h2 : b * y ≤ b * r := mul_le_mul_of_nonneg_left hy.le hb
    have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    linarith

theorem kam_norm_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ :=
  (norm_add_le _ _).trans
    (by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb])

theorem kamDomain_convex (s r : ℝ) : Convex ℝ (kamDomain s r) := by
  intro z hz w hw a b ha hb hab
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨hw1, hw2, hw3⟩ := hw
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have him : ((a • z + b • w).1 i).im = a * (z.1 i).im + b * (w.1 i).im := by simp
    rw [him]
    calc |a * (z.1 i).im + b * (w.1 i).im| ≤ |a * (z.1 i).im| + |b * (w.1 i).im| := abs_add_le _ _
      _ = a * |(z.1 i).im| + b * |(w.1 i).im| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < s := kam_convex_lt ha hb hab (hz1 i) (hw1 i)
  · exact (kam_norm_comb z.2.1 w.2.1 ha hb).trans_lt (kam_convex_lt ha hb hab hz2 hw2)
  · have h1 := kam_norm_comb z.2.2.1 w.2.2.1 ha hb
    have h2 := kam_norm_comb z.2.2.2 w.2.2.2 ha hb
    have := kam_convex_lt ha hb hab hz3 hw3
    show ‖a • z.2.2.1 + b • w.2.2.1‖ + ‖a • z.2.2.2 + b • w.2.2.2‖ < r
    nlinarith

theorem kamDomain_mono {s s' r r' : ℝ} (hs : s' ≤ s) (hr' : 0 < r') (hr : r' ≤ r) :
    kamDomain s' r' ⊆ kamDomain s r := by
  rintro z ⟨h1, h2, h3⟩
  exact ⟨fun i => (h1 i).trans_le hs, h2.trans_le (pow_le_pow_left₀ hr'.le hr 2), h3.trans_le hr⟩

/-- **Margin** (blueprint `bpW:w1:kam-domain`): for `0 < σ ≤ 1`, `2σ < s`, `r > 0`, every
`W₀ ∈ D(s-2σ, r/2)` and `W` with `|W|_r < σ/2` give `W₀ + W ∈ D(s-σ, r)`. -/
theorem kamDomain_add_mem {s σ r : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (_hσs : 2 * σ < s) (hr : 0 < r)
    {W₀ W : KamPhase} (hW₀ : W₀ ∈ kamDomain (s - 2 * σ) (r / 2)) (hW : kamNorm r W < σ / 2) :
    W₀ + W ∈ kamDomain (s - σ) r := by
  obtain ⟨h1, h2, h3⟩ := hW₀
  unfold kamNorm at hW
  have n1 : 0 ≤ ‖W.1‖ := norm_nonneg _
  have n2 : 0 ≤ ‖W.2.1‖ / r ^ 2 := by positivity
  have n3 : 0 ≤ ‖W.2.2.1‖ / r := by positivity
  have n4 : 0 ≤ ‖W.2.2.2‖ / r := by positivity
  have c1 : ‖W.1‖ < σ / 2 := by linarith
  have c2 : ‖W.2.1‖ < r ^ 2 * (σ / 2) := by
    have : ‖W.2.1‖ / r ^ 2 < σ / 2 := by linarith
    rwa [div_lt_iff₀ (by positivity), mul_comm] at this
  have c3 : ‖W.2.2.1‖ + ‖W.2.2.2‖ < r * (σ / 2) := by
    have : ‖W.2.2.1‖ / r + ‖W.2.2.2‖ / r < σ / 2 := by linarith
    rw [← add_div, div_lt_iff₀ hr, mul_comm] at this
    exact this
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have him : ((W₀ + W).1 i).im = (W₀.1 i).im + (W.1 i).im := by simp
    rw [him]
    have hi : |(W.1 i).im| ≤ ‖W.1‖ := (Complex.abs_im_le_norm _).trans (norm_le_pi_norm W.1 i)
    calc |(W₀.1 i).im + (W.1 i).im| ≤ |(W₀.1 i).im| + |(W.1 i).im| := abs_add_le _ _
      _ < (s - 2 * σ) + σ / 2 := add_lt_add_of_lt_of_le (h1 i) (hi.trans c1.le)
      _ < s - σ := by linarith
  · have : ‖(W₀ + W).2.1‖ ≤ ‖W₀.2.1‖ + ‖W.2.1‖ := norm_add_le _ _
    have hrr : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
    have : ‖W₀.2.1‖ < r ^ 2 / 4 := by rw [← hrr]; exact h2
    have hσr : r ^ 2 * (σ / 2) ≤ r ^ 2 / 2 := by nlinarith [sq_nonneg r]
    show ‖W₀.2.1 + W.2.1‖ < r ^ 2
    nlinarith [norm_add_le W₀.2.1 W.2.1, sq_nonneg r]
  · have e1 : ‖W₀.2.2.1 + W.2.2.1‖ ≤ ‖W₀.2.2.1‖ + ‖W.2.2.1‖ := norm_add_le _ _
    have e2 : ‖W₀.2.2.2 + W.2.2.2‖ ≤ ‖W₀.2.2.2‖ + ‖W.2.2.2‖ := norm_add_le _ _
    show ‖W₀.2.2.1 + W.2.2.1‖ + ‖W₀.2.2.2 + W.2.2.2‖ < r
    nlinarith

/-- `|W|_{p̄,r} ≤ |W|_{p,r}` for `p̄ ≤ p` (blueprint `bpW:w1:kam-domain`, via `bpW:w1:embed` (i)).
-/
theorem kamNorm_embed_le (a p p' : ℝ) (hp : p' ≤ p) {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    kamNorm r (kamEmbed a p p' hp W) ≤ kamNorm r W := by
  unfold kamNorm kamEmbed
  have hN : ∀ y : lp (fun _ : ℕ+ => ℂ) 2, ‖embedCLM a p a p' le_rfl hp y‖ ≤ ‖y‖ := fun y => by
    have := ContinuousLinearMap.le_of_opNorm_le (embedCLM (K := ℂ) a p a p' le_rfl hp)
      (norm_embedCLM_le (K := ℂ) a p a p' le_rfl hp) y
    simpa using this
  simp only
  gcongr <;> exact hN _

/-- `|W|_{p,r} ≤ |W|_{p,r'}` for `0 < r' ≤ r` (blueprint `bpW:w1:kam-domain`). -/
theorem kamNorm_le_of_le_radius {r r' : ℝ} (hr' : 0 < r') (hr : r' ≤ r) (W : KamPhase) :
    kamNorm r W ≤ kamNorm r' W := by
  unfold kamNorm
  have hr0 : 0 < r := hr'.trans_le hr
  have h2 : 1 / r ^ 2 ≤ 1 / r' ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr'.le hr 2)
  have h1 : 1 / r ≤ 1 / r' := one_div_le_one_div_of_le hr' hr
  have e2 : ‖W.2.1‖ / r ^ 2 ≤ ‖W.2.1‖ / r' ^ 2 := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div ‖W.2.1‖]; gcongr
  have e3 : ‖W.2.2.1‖ / r ≤ ‖W.2.2.1‖ / r' := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div ‖W.2.2.1‖]; gcongr
  have e4 : ‖W.2.2.2‖ / r ≤ ‖W.2.2.2‖ / r' := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div ‖W.2.2.2‖]; gcongr
  linarith

/-! ### Conventions (`bpW:w1:kam-conventions`) -/

/-- P96-K's `z = (u - iv)/√2` is the complex conjugate of W0's `z = (q + ip)/√2` (for real `q, p`):
a relabelling `z ↔ z̄`. -/
theorem kam_conj_relabel (q p : ℝ) :
    starRingEnd ℂ (((q : ℂ) + p * Complex.I) / Real.sqrt 2) =
      ((q : ℂ) - p * Complex.I) / Real.sqrt 2 := by
  simp [Complex.conj_ofReal, sub_eq_add_neg, add_div]

/-- The sum norm of `D(s,r)` versus the max norm of `WaveSpace`: `‖z‖ ≤ ‖u‖ + ‖v‖`. -/
theorem kam_wave_norm_sum_ge (z : WaveSpace) : ‖z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  rw [Prod.norm_def]
  exact max_le (by linarith [norm_nonneg z.2]) (by linarith [norm_nonneg z.1])

/-- The sum norm of `D(s,r)` versus the max norm of `WaveSpace`: `‖u‖ + ‖v‖ ≤ 2 ‖z‖`. -/
theorem kam_wave_norm_sum_le (z : WaveSpace) : ‖z.1‖ + ‖z.2‖ ≤ 2 * ‖z‖ := by
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  linarith

/-- Period conversion: a P96-K strip `|Im x| < s_K` with `x = 2πθ` is `|Im θ| < s_K/(2π)`. -/
theorem kam_strip_period_conversion (θ : ℂ) (sK : ℝ) :
    |(2 * Real.pi * θ).im| < sK ↔ |θ.im| < sK / (2 * Real.pi) := by
  have : (2 * (Real.pi : ℂ) * θ).im = 2 * Real.pi * θ.im := by
    simp [Complex.mul_im]
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    lt_div_iff₀ (by positivity), mul_comm]

end KAM.Wave
