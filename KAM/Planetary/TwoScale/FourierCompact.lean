/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.FourierCompactCauchy
public import KAM.Strip.Analytic
public import KAM.Strip.FourierBasic
public import KAM.Strip.Limits
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Compactness of bounded periodic holomorphic sequences (`bpP:p3:fourier-compact`)

A sequence `F j` of `1`-periodic holomorphic functions on the strip of width `w`, bounded by `B`
and converging uniformly on the real torus to `f`, converges, with all iterated Fréchet derivatives,
uniformly on every closed strip of width `v < w` to a holomorphic periodic limit `G` extending `f`.

* `stepP:p3:fc-decay`: the Fourier coefficients of `F j` satisfy `e^{-2π w |k|₁} B`.
* `stepP:p3:fc-coef`: the coefficients converge, since the torus average is `1`-Lipschitz for the
  sup norm; the limit coefficients obey the same bound.
* `stepP:p3:fc-tail`: the finitely many modes plus the summable exponential tail
  `2 B e^{-2π (w - ρ) |k|₁}` give uniform convergence of the series on each strip of width
  `ρ < w` by dominated convergence; the Cauchy induction of `FourierCompactCauchy` upgrades this
  to all iterated derivatives.
-/

@[expose] public section

open Set Filter Topology

namespace KAM.Planetary

variable {n : ℕ}

private theorem intCast_single (i : Fin n) :
    (fun i' => (((Pi.single i 1 : Fin n → ℤ) i' : ℤ) : ℂ)) = Pi.single i 1 := by
  funext i'
  by_cases h : i' = i
  · subst h; simp
  · simp [h]

private theorem continuous_ofReal_pi : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- `stepP:p3:fc-decay`: the Fourier coefficients of a member of the sequence. -/
private theorem coeff_decay {w B : ℝ} (hw : 0 < w) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n w))
    (hper : ∀ θ, θ ∈ complexStrip n w → ∀ k : Fin n → ℤ, u (θ + fun i => (k i : ℂ)) = u θ)
    (hb : ∀ θ ∈ complexStrip n w, ‖u θ‖ ≤ B) (k : Fin n → ℤ) :
    ‖torusCoeff (fun x => u (fun j => (x j : ℂ))) k‖ ≤
      Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B :=
  norm_torusCoeff_le hw hu (fun i z hz => by
    have := hper z hz (Pi.single i 1)
    rwa [intCast_single] at this) hb k

/-- `stepP:p3:fc-coef`: coefficients of the sequence converge to those of the limit. -/
private theorem tendsto_coeff {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℂ} {w : ℝ}
    (hw : 0 < w) (hhol : ∀ j, DifferentiableOn ℂ (F j) (complexStrip n w))
    (hconv : TendstoUniformly (fun j x => F j (realInclusion n x)) f atTop) (k : Fin n → ℤ) :
    Tendsto (fun j => torusCoeff (fun x => F j (fun i => (x i : ℂ))) k) atTop
      (𝓝 (torusCoeff f k)) := by
  have hcF : ∀ j, Continuous fun x : Fin n → ℝ => F j (fun i => (x i : ℂ)) := fun j =>
    (hhol j).continuousOn.comp_continuous continuous_ofReal_pi
      fun x => ofReal_mem_complexStrip hw x
  have hcf : Continuous f := hconv.continuous (Eventually.of_forall hcF).frequently
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hconv (ε / 2) (by positivity)] with j hj
  rw [Real.dist_eq, sub_zero, abs_norm, ← torusCoeff_sub (hcF j) hcf]
  refine lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
  refine norm_torusAverage_le fun x _ => ?_
  rw [norm_mul, norm_character_real, one_mul]
  have := hj x
  change dist (f x) (F j fun i => (x i : ℂ)) < ε / 2 at this
  rw [dist_comm, dist_eq_norm] at this
  exact this.le

private theorem periodic_single {w : ℝ} {u : (Fin n → ℂ) → ℂ}
    (hper : ∀ θ, θ ∈ complexStrip n w → ∀ k : Fin n → ℤ, u (θ + fun i => (k i : ℂ)) = u θ)
    (i : Fin n) (z : Fin n → ℂ) (hz : z ∈ complexStrip n w) : u (z + Pi.single i 1) = u z := by
  have := hper z hz (Pi.single i 1)
  rwa [intCast_single] at this

private theorem exp_mul_exp_aux (w ρ m : ℝ) :
    Real.exp (-(2 * Real.pi * w * m)) * Real.exp (2 * Real.pi * ρ * m) =
      Real.exp (-(2 * Real.pi * (w - ρ)) * m) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- `stepP:p3:fc-tail`: uniform convergence of the series on strips of width `ρ < w`. -/
private theorem eventually_norm_sub_lt {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℂ}
    {w B : ℝ} (hw : 0 < w) (hhol : ∀ j, DifferentiableOn ℂ (F j) (complexStrip n w))
    (hper : ∀ j θ, θ ∈ complexStrip n w → ∀ k : Fin n → ℤ,
      F j (θ + fun i => (k i : ℂ)) = F j θ)
    (hb : ∀ j θ, θ ∈ complexStrip n w → ‖F j θ‖ ≤ B)
    (hconv : TendstoUniformly (fun j x => F j (realInclusion n x)) f atTop)
    {ρ : ℝ} (hρ : ρ < w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ z ∈ complexStrip n ρ,
      ‖F j z - fourierSum (torusCoeff f) z‖ < ε := by
  set a := torusCoeff f with ha
  set c : ℕ → (Fin n → ℤ) → ℂ := fun j => torusCoeff fun x => F j fun i => (x i : ℂ) with hc
  have hcd : ∀ j k, ‖c j k‖ ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B :=
    fun j k => coeff_decay hw (hhol j) (hper j) (hb j) k
  have had : ∀ k, ‖a k‖ ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B :=
    fun k => le_of_tendsto (tendsto_coeff hw hhol hconv k).norm
      (Eventually.of_forall fun j => hcd j k)
  have hx : 0 < 2 * Real.pi * (w - ρ) := by
    have := Real.pi_pos
    nlinarith [sub_pos.mpr hρ]
  have hgeom := Fourier.hasSum_exp_neg_modeSize n hx
  set bd : (Fin n → ℤ) → ℝ := fun k =>
    2 * B * Real.exp (-(2 * Real.pi * (w - ρ)) * Fourier.modeSize k) with hbd
  have hbsum : Summable bd := hgeom.summable.mul_left (2 * B)
  have hterm : ∀ j k, ‖c j k - a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) ≤ bd k := by
    intro j k
    have h1 : ‖c j k - a k‖ ≤ 2 * (Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B) := by
      have := norm_sub_le (c j k) (a k)
      linarith [hcd j k, had k]
    calc ‖c j k - a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)
        ≤ 2 * (Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B) *
          Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = bd k := by
          rw [hbd]
          simp only
          rw [← exp_mul_exp_aux w ρ]
          ring
  have hsumW : ∀ g : (Fin n → ℤ) → ℂ,
      (∀ k, ‖g k‖ ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B) →
      Fourier.SummableWeighted (2 * Real.pi * ρ) g := by
    intro g hg
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      (hgeom.summable.mul_left B)
    calc ‖g k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)
        ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B *
          Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) :=
          mul_le_mul_of_nonneg_right (hg k) (Real.exp_pos _).le
      _ = B * Real.exp (-(2 * Real.pi * (w - ρ)) * Fourier.modeSize k) := by
          rw [mul_comm _ B, mul_assoc, exp_mul_exp_aux]
  have hE : Tendsto (fun j => ∑' k, ‖c j k - a k‖ *
      Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun j k => ‖c j k - a k‖ *
      Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) (g := fun _ => (0 : ℝ)) (bound := bd)
      hbsum (fun k => by
        have h := ((tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_coeff hw hhol hconv k)).mul_const
          (Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)))
        simpa using h)
      (Eventually.of_forall fun j k => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hterm j k)
    simpa using this
  filter_upwards [hE.eventually (gt_mem_nhds hε)] with j hj z hz
  have hzw : z ∈ complexStrip n w := fun i => (hz i).trans hρ
  rw [eq_fourierSum_torusCoeff hw (hhol j) (periodic_single (hper j)) (hb j) hzw]
  have hsc := summable_coeff_mul_character (hsumW (c j) (hcd j)) hz
  have hsa := summable_coeff_mul_character (hsumW a had) hz
  have hdiff : fourierSum (c j) z - fourierSum a z =
      ∑' k, (c j k * character k z - a k * character k z) := by
    rw [fourierSum, fourierSum, ← hsc.tsum_sub hsa]
  have hsb : Summable fun k => ‖c j k - a k‖ *
      Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (hterm j) hbsum
  rw [hdiff]
  refine lt_of_le_of_lt (tsum_of_norm_bounded hsb.hasSum fun k => ?_) hj
  rw [← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_character_le k hz) (norm_nonneg _)

/-- **Compactness of bounded periodic holomorphic sequences** (`bpP:p3:fourier-compact`): all
iterated Fréchet derivatives converge uniformly on every closed strip of width `v < w`. -/
theorem fourier_compact {n : ℕ} {w B : ℝ} (hw : 0 < w) (hB : 0 ≤ B)
    {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℂ}
    (hhol : ∀ j, DifferentiableOn ℂ (F j) (complexStrip n w))
    (hper : ∀ j θ, θ ∈ complexStrip n w → ∀ k : Fin n → ℤ,
      F j (θ + fun i => (k i : ℂ)) = F j θ)
    (hb : ∀ j θ, θ ∈ complexStrip n w → ‖F j θ‖ ≤ B)
    (hconv : TendstoUniformly (fun j x => F j (realInclusion n x)) f atTop) :
    ∃ G : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ G (complexStrip n w) ∧
      (∀ x, G (realInclusion n x) = f x) ∧
      (∀ z ∈ complexStrip n w, ‖G z‖ ≤ B) ∧
      (∀ θ ∈ complexStrip n w, ∀ k : Fin n → ℤ, G (θ + fun i => (k i : ℂ)) = G θ) ∧
      ∀ v : ℝ, 0 < v → v < w → ∀ m : ℕ,
        TendstoUniformlyOn (fun j => iteratedFDeriv ℂ m (F j)) (iteratedFDeriv ℂ m G)
          atTop {z | ∀ i, |(z i).im| ≤ v} := by
  have _ := hB
  set a := torusCoeff f with ha
  have hunif := fun {ρ : ℝ} (hρ : ρ < w) {ε : ℝ} (hε : 0 < ε) =>
    eventually_norm_sub_lt hw hhol hper hb hconv hρ hε
  -- pointwise convergence on the open strip
  have hpt : ∀ z ∈ complexStrip n w, Tendsto (fun j => F j z) atTop (𝓝 (fourierSum a z)) := by
    intro z hz
    obtain ⟨ε₀, hε₀, hz'⟩ := exists_mem_complexStrip_sub hz
    rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hunif (by linarith : w - ε₀ < w) hε] with j hj
    rw [Real.dist_eq, sub_zero, abs_norm]
    exact hj z hz'
  have hG : DifferentiableOn ℂ (fourierSum a) (complexStrip n w) := by
    intro z hz
    obtain ⟨ε₀, hε₀, hz'⟩ := exists_mem_complexStrip_sub hz
    have hsum : Fourier.SummableWeighted (2 * Real.pi * (w - ε₀)) a := by
      have hx : 0 < 2 * Real.pi * ε₀ := by positivity
      have hgeom := Fourier.hasSum_exp_neg_modeSize n hx
      have had : ∀ k, ‖a k‖ ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B :=
        fun k => le_of_tendsto (tendsto_coeff hw hhol hconv k).norm
          (Eventually.of_forall fun j => coeff_decay hw (hhol j) (hper j) (hb j) k)
      refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
        (hgeom.summable.mul_left B)
      calc ‖a k‖ * Real.exp (2 * Real.pi * (w - ε₀) * Fourier.modeSize k)
          ≤ Real.exp (-(2 * Real.pi * w * Fourier.modeSize k)) * B *
            Real.exp (2 * Real.pi * (w - ε₀) * Fourier.modeSize k) :=
            mul_le_mul_of_nonneg_right (had k) (Real.exp_pos _).le
        _ = B * Real.exp (-(2 * Real.pi * ε₀) * Fourier.modeSize k) := by
            rw [mul_comm _ B, mul_assoc, exp_mul_exp_aux]
            congr 3
            ring
    exact ((differentiableOn_fourierSum hsum).differentiableAt
      ((isOpen_complexStrip n _).mem_nhds hz')).differentiableWithinAt
  refine ⟨fourierSum a, hG, ?_, ?_, ?_, ?_⟩
  · intro x
    exact tendsto_nhds_unique (hpt _ (ofReal_mem_complexStrip hw x))
      (hconv.tendsto_at x)
  · intro z hz
    exact le_of_tendsto (hpt z hz).norm (Eventually.of_forall fun j => hb j z hz)
  · intro θ hθ k
    exact tendsto_nhds_unique (hpt _ (add_intCast_mem_complexStrip hθ k))
      ((hpt θ hθ).congr fun j => (hper j θ hθ k).symm)
  · intro v hv hvw m
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (v + w) / 2 := ⟨_, rfl⟩
    have hρw : ρ < w := by rw [hρ]; linarith
    have hvρ : v < ρ := by rw [hρ]; linarith
    set H : ℕ → (Fin n → ℂ) → ℂ := fun j => F j - fourierSum a with hH
    have hHd : ∀ j, DifferentiableOn ℂ (H j) (complexStrip n w) := fun j => (hhol j).sub hG
    have h0 : StripDecay n w fun j z => ‖H j z‖ := fun ρ' hρ' ε' hε' => by
      filter_upwards [hunif hρ' hε'] with j hj z hz
      exact hj z hz
    have hdec := stripDecay_iteratedFDeriv hHd h0 m ρ hρw ε hε
    filter_upwards [hdec] with j hj z hz
    have hzρ : z ∈ complexStrip n ρ := fun i => (hz i).trans_lt hvρ
    have hzw : z ∈ complexStrip n w := fun i => (hzρ i).trans hρw
    have hat : ∀ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g (complexStrip n w) →
        ContDiffAt ℂ m g z := fun g hg =>
      (analyticOnNhd_of_differentiableOn (isOpen_complexStrip n w) hg z hzw).contDiffAt
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℂ) (i := m) (hat _ (hhol j)) (hat _ hG)
    rw [dist_comm, dist_eq_norm, ← hsub]
    exact hj z hzρ

end KAM.Planetary

end
