/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Sequence
public import KAM.Wave.Iteration.ConvArith
public import KAM.Wave.Iteration.Limits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# W6: convergence of the frequencies (`bpW:w6:convergence` (i), (ii))

Blueprint label `bpW:w6:convergence` (milestone W6), steps `c-par`, `c-freq`.

For the iteration `S_ν = w6Seq d (w6Start …) ν` of Proposition `bpW:w6:convergence`
(hypotheses `W6ConvHyp`), with `Π_* = ⋂_ν Π_ν` (`w6PiStarIt`), `ω_* = lim ω_ν`, `Ω_* = lim Ω_ν`
(`w6OmStar`, `w6OmStar7`, W7 index):

* `w6_uniform_limit`: sequences with increments `≤ C 4^{-n}` converge uniformly, with tail
  `≤ (4/3) C 4^{-n}` (no W5 input);
* the hypothesis-taking variants (hypothesis `W6StepReal`, W5's reality clause; not the label; the
  unconditional statements are in `KAM.Wave.Iteration.ConvSource`):
  `w6Seq_Pi_eq_of_stepReal` and `w6ConvParams_of_stepReal` (clause (i): `Π_ν` is W6-PREP's
  `w6PiSeq` of the output frequencies, `Π_{-1} ∖ Π_* = ⋃_ν ⋃_{|k| > K_{ν-1}} R^ν_{kl}`), and
  `w6ConvFreq_of_stepReal` (clause (ii): uniform convergence on `Π_*`, `|ω_* - ω_0| ≤ 8πε₀`,
  Lipschitz `≤ 64πε₀/λ₀`, `sup_j (j+2)^{1/2} |Ω_{*,j} - Ω_{0,j}| ≤ 4ε₀`, Lipschitz `≤ 16ε₀/λ₀`, the
  same bounds for `(ω_ν, Ω_ν)` on `Π_{ν-1}`, and `|⟨k, ω_*⟩ + ⟨l, Ω_*⟩| ≥ (α₀/2)⟨l⟩/A_k` on `Π_*`).
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

/-- **Uniform limits** of sequences with increments `‖f_{n+1} - f_n‖ ≤ C 4^{-n}` on `A`: pointwise
convergence to `limUnder`, the tail bound `≤ (4/3) C 4^{-n}`, and uniform convergence on `A`. -/
theorem w6_uniform_limit {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → α → E}
    {A : Set α} {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, ∀ x ∈ A, ‖f (n + 1) x - f n x‖ ≤ C / 4 ^ n) :
    (∀ x ∈ A, Tendsto (fun n => f n x) atTop (𝓝 (limUnder atTop fun n => f n x))) ∧
    (∀ x ∈ A, ∀ n, ‖(limUnder atTop fun m => f m x) - f n x‖ ≤ 4 / 3 * C / 4 ^ n) ∧
    TendstoUniformlyOn f (fun x => limUnder atTop fun n => f n x) atTop A := by
  have hsum : Summable fun n : ℕ => C / 4 ^ n := by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left C
    refine this.congr fun n => ?_
    rw [one_div_pow]; ring
  have hdist : ∀ x ∈ A, ∀ n, dist (f n x) (f n.succ x) ≤ C / 4 ^ n := fun x hx n => by
    rw [dist_comm, dist_eq_norm]; exact h n x hx
  have hlim : ∀ x ∈ A, Tendsto (fun n => f n x) atTop (𝓝 (limUnder atTop fun n => f n x)) :=
    fun x hx => (cauchySeq_of_dist_le_of_summable _ (hdist x hx) hsum).tendsto_limUnder
  have htail : ∀ x ∈ A, ∀ n, ‖(limUnder atTop fun m => f m x) - f n x‖ ≤ 4 / 3 * C / 4 ^ n := by
    intro x hx n
    rw [← dist_eq_norm, dist_comm]
    refine le_of_tendsto (tendsto_const_nhds.dist (hlim x hx))
      (eventually_atTop.2 ⟨n, fun m hnm => ?_⟩)
    refine (dist_le_Ico_sum_of_dist_le hnm fun {k} _ _ => hdist x hx k).trans ?_
    have hg := sum_inv_pow_Ico_le (by norm_num : (1 : ℝ) < 4) n m
    have e : ∑ i ∈ Finset.Ico n m, C / 4 ^ i = C * ∑ i ∈ Finset.Ico n m, 1 / (4 : ℝ) ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc C * ∑ i ∈ Finset.Ico n m, 1 / (4 : ℝ) ^ i ≤ C * (4 / (4 - 1) / 4 ^ n) :=
          mul_le_mul_of_nonneg_left hg hC
      _ = 4 / 3 * C / 4 ^ n := by ring
  refine ⟨hlim, htail, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  have ht : Tendsto (fun n : ℕ => 4 / 3 * C / (4 : ℝ) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul (4 / 3 * C)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div_pow]; ring
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (htail x hx n) hn

/-- A map with `‖f ξ - f ζ‖ ≤ L ‖ξ - ζ‖` on `A` is continuous on `A`. -/
theorem w6_continuousOn_of_lip {E : Type*} [SeminormedAddCommGroup E] {f : (Fin 2 → ℝ) → E}
    {A : Set (Fin 2 → ℝ)} {L : ℝ} (h : ∀ ξ ∈ A, ∀ ζ ∈ A, ‖f ξ - f ζ‖ ≤ L * ‖ξ - ζ‖) :
    ContinuousOn f A := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal L) fun x hx y hy => ?_).continuousOn
  rw [dist_eq_norm, dist_eq_norm]
  exact (h x hx y hy).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))

section conv

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

/-- `Π_* = ⋂_ν Π_ν` for the iteration started at `S₀`. -/
def w6PiStarIt (d : W6SeqData) (S0 : W6State) : Set (Fin 2 → ℝ) := ⋂ ν, (w6Seq d S0 ν).Pi

/-- `ω_* = lim ω_ν`. -/
def w6OmStar (d : W6SeqData) (S0 : W6State) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  limUnder atTop fun ν => (w6Seq d S0 ν).om ξ

/-- `Ω_* = lim Ω_ν` (W7 index). -/
def w6OmStar7 (d : W6SeqData) (S0 : W6State) (ξ : Fin 2 → ℝ) (n : ℕ) : ℝ :=
  limUnder atTop fun ν => w6Om7 ((w6Seq d S0 ν).Om ξ) n

variable (hR : W6StepReal) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀)
include hR hC

theorem w6Seq_succ_eq (ν : ℕ) :
    w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1) =
      ⟨W6Stage.PiN hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν),
        W6Stage.omN hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν),
        W6Stage.OmN hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν),
        W6Stage.PN hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν),
        W6Stage.XN hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν)⟩ :=
  (w6Seq_succ d _ ν).trans (W6State.w6next_eq hC.valid hC.small (w6Seq_stage_of_stepReal hR hC ν))

/-- The increments of `ω` along the iteration (Lemma `bpW:w6:iter-lemma`), on `Π_ν`. -/
theorem w6Seq_om_inc (ν : ℕ) :
    ∀ ξ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Pi,
      ‖(w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).om ξ -
        (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).om ξ‖ ≤ 6 * π * d.eps ν ∧
      ∀ ζ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Pi,
        ‖((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).om ξ -
            (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).om ξ) -
          ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).om ζ -
            (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).om ζ)‖ ≤
          6 * π * d.eps ν / d.lam ν * ‖ξ - ζ‖ := by
  have hs := w6Seq_stage_of_stepReal hR hC ν
  obtain ⟨b₀, b₁, h0, h1, hbs, hbb, hbl⟩ := W6Stage.omN_inc hC.valid hC.small hs
  have hl := W6SeqData.lam_pos hC.valid ν
  have hb1 : b₁ ≤ 6 * π * d.eps ν / d.lam ν := by
    rw [le_div_iff₀ hl]; nlinarith
  rw [w6Seq_succ_eq hR hC ν]
  intro ξ hξ
  refine ⟨?_, fun ζ hζ => (hbl ξ hξ ζ hζ).trans
    (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))⟩
  have := hbb ξ hξ
  have : 0 ≤ d.lam ν * b₁ := mul_nonneg hl.le h1
  exact le_trans (hbb ξ hξ) (by linarith)

/-- The increments of `Ω` along the iteration (W7 index), on `Π_ν`. -/
theorem w6Seq_Om_inc (ν : ℕ) :
    ∀ ξ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Pi, ∀ n : ℕ,
      normLab n ^ (1 / 2 : ℝ) * |w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).Om ξ) n -
        w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Om ξ) n| ≤ 3 * d.eps ν ∧
      ∀ ζ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Pi,
        normLab n ^ (1 / 2 : ℝ) *
          |(w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).Om ξ) n -
              w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Om ξ) n) -
            (w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) (ν + 1)).Om ζ) n -
              w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Om ζ) n)| ≤
          3 * d.eps ν / d.lam ν * ‖ξ - ζ‖ := by
  have hs := w6Seq_stage_of_stepReal hR hC ν
  obtain ⟨c₀, c₁, h0, h1, hcs, hcb, hcl⟩ := W6Stage.OmN_inc hC.valid hC.small hs
  have hl := W6SeqData.lam_pos hC.valid ν
  have hc1 : c₁ ≤ 3 * d.eps ν / d.lam ν := by
    rw [le_div_iff₀ hl]; nlinarith
  rw [w6Seq_succ_eq hR hC ν]
  intro ξ hξ n
  refine ⟨?_, fun ζ hζ => (hcl ξ hξ ζ hζ n).trans
    (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _))⟩
  have : 0 ≤ d.lam ν * c₁ := mul_nonneg hl.le h1
  exact le_trans (hcb ξ hξ n) (by linarith)

local notation "𝒮" => w6Seq d (w6Start d Pm ω0 Ω0 P0 X0)

/-- **Parameters** (`bpW:w6:convergence` (i)): `Π_ν` is W6-PREP's `w6PiSeq` (index `ν + 1`) of the
output frequencies `(ω_n, Ω_n)`, levels `α_n` and thresholds `K_{n-1}`. -/
theorem w6Seq_Pi_eq_of_stepReal (ν : ℕ) :
    (𝒮 ν).Pi = w6PiSeq Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu
      (ν + 1) := by
  induction ν with
  | zero => rfl
  | succ ν ih =>
    rw [w6PiSeq_succ, ← ih]
    unfold w6Removed
    simp only []
    rw [w6Seq_succ_eq hR hC ν]
    rfl

/-- `Π_* = ⋂_ν Π_ν` is W6-PREP's `w6PiStar` of the output frequencies. -/
theorem w6PiStarIt_eq_of_stepReal :
    w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0) =
      w6PiStar Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu := by
  unfold w6PiStarIt w6PiStar
  ext ξ
  simp only [Set.mem_iInter]
  constructor
  · intro h n
    cases n with
    | zero => exact w6Pi0_subset (h 0)
    | succ n => rw [← w6Seq_Pi_eq_of_stepReal hR hC n]; exact h n
  · intro h ν
    rw [w6Seq_Pi_eq_of_stepReal hR hC ν]; exact h (ν + 1)

/-- **Convergence (i)** (`bpW:w6:convergence` (i), hypothesis-taking variant): for the iteration,
`Π_{-1} ∖ Π_* = ⋃_{ν ≥ 0} ⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}`, with `R^ν_{kl}` the zone of
`(ω_ν, Ω_ν)` at level `α_ν` in `Π_{ν-1}`. -/
theorem w6ConvParams_of_stepReal :
    Pm \ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0) =
      ⋃ (ν : ℕ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ d.KprevNu ν < kAbs k),
        zoneSet (w6PiSeq Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu ν)
          ((𝒮 ν).om) (fun ξ => w6Om7 ((𝒮 ν).Om ξ)) (d.alpha ν) k l := by
  rw [w6PiStarIt_eq_of_stepReal hR hC]
  exact w6Convergence_params Pm _ _ d.alpha d.KprevNu

/-- Partial sums of the `ω` increments: `|ω_n - ω_0| ≤ ∑_{μ<n} 6πε_μ ≤ 8πε₀` and the Lipschitz
part `≤ ∑_{μ<n} 6πε_μ/λ_μ ≤ 64πε₀/λ₀`, on `Π_{n-1}` (`ξ ∈ Π_μ` for `μ < n`). -/
theorem w6Seq_om_partial (n : ℕ) {ξ ζ : Fin 2 → ℝ} (hξ : ∀ μ < n, ξ ∈ (𝒮 μ).Pi)
    (hζ : ∀ μ < n, ζ ∈ (𝒮 μ).Pi) :
    ‖(𝒮 n).om ξ - ω0 ξ‖ ≤ 8 * π * d.eps0 ∧
      ‖((𝒮 n).om ξ - ω0 ξ) - ((𝒮 n).om ζ - ω0 ζ)‖ ≤ 64 * π * d.eps0 / d.lam 0 * ‖ξ - ζ‖ := by
  obtain ⟨hs1, -⟩ := W6SeqData.freq_sum_le hC.valid hC.small n
  obtain ⟨hl1, -⟩ := W6SeqData.freq_lip_sum_le hC.valid hC.small n
  constructor
  · have h := dist_le_range_sum_of_dist_le (f := fun μ => (𝒮 μ).om ξ) n
      (d := fun μ => 6 * π * d.eps μ) fun {k} hk => by
        rw [dist_comm, dist_eq_norm]; exact (w6Seq_om_inc hR hC k ξ (hξ k hk)).1
    rw [dist_comm, dist_eq_norm] at h
    exact h.trans hs1
  · have h := dist_le_range_sum_of_dist_le (f := fun μ => (𝒮 μ).om ξ - (𝒮 μ).om ζ) n
      (d := fun μ => 6 * π * d.eps μ / d.lam μ * ‖ξ - ζ‖) fun {k} hk => by
        rw [dist_comm, dist_eq_norm]
        have := (w6Seq_om_inc hR hC k ξ (hξ k hk)).2 ζ (hζ k hk)
        refine le_of_eq_of_le ?_ this
        congr 1; abel
    rw [dist_comm, dist_eq_norm, ← Finset.sum_mul] at h
    have e : (𝒮 n).om ξ - ω0 ξ - ((𝒮 n).om ζ - ω0 ζ) =
        (𝒮 n).om ξ - (𝒮 n).om ζ - ((𝒮 0).om ξ - (𝒮 0).om ζ) := by
      show _ = _ - (ω0 ξ - ω0 ζ); abel
    rw [e]
    exact h.trans (mul_le_mul_of_nonneg_right hl1 (norm_nonneg _))

/-- Partial sums of the `Ω` increments (W7 index): `(j+2)^{1/2} |Ω_{n,j} - Ω_{0,j}| ≤ 4ε₀` and the
Lipschitz part `≤ 16ε₀/λ₀`, on `Π_{n-1}`. -/
theorem w6Seq_Om_partial (n : ℕ) {ξ ζ : Fin 2 → ℝ} (hξ : ∀ μ < n, ξ ∈ (𝒮 μ).Pi)
    (hζ : ∀ μ < n, ζ ∈ (𝒮 μ).Pi) (j : ℕ) :
    normLab j ^ (1 / 2 : ℝ) * |w6Om7 ((𝒮 n).Om ξ) j - w6Om7 (Ω0 ξ) j| ≤ 4 * d.eps0 ∧
      normLab j ^ (1 / 2 : ℝ) * |(w6Om7 ((𝒮 n).Om ξ) j - w6Om7 (Ω0 ξ) j) -
        (w6Om7 ((𝒮 n).Om ζ) j - w6Om7 (Ω0 ζ) j)| ≤ 16 * d.eps0 / d.lam 0 * ‖ξ - ζ‖ := by
  obtain ⟨-, hs1⟩ := W6SeqData.freq_sum_le hC.valid hC.small n
  obtain ⟨-, hl1⟩ := W6SeqData.freq_lip_sum_le hC.valid hC.small n
  set w := normLab j ^ (1 / 2 : ℝ)
  have hw : 0 ≤ w := le_trans zero_le_one (one_le_normLab_rpow_half j)
  constructor
  · have h := dist_le_range_sum_of_dist_le (f := fun μ => w * w6Om7 ((𝒮 μ).Om ξ) j) n
      (d := fun μ => 3 * d.eps μ) fun {k} hk => by
        rw [dist_comm, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hw]
        exact (w6Seq_Om_inc hR hC k ξ (hξ k hk) j).1
    rw [dist_comm, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hw] at h
    exact h.trans hs1
  · have h := dist_le_range_sum_of_dist_le
      (f := fun μ => w * (w6Om7 ((𝒮 μ).Om ξ) j - w6Om7 ((𝒮 μ).Om ζ) j)) n
      (d := fun μ => 3 * d.eps μ / d.lam μ * ‖ξ - ζ‖) fun {k} hk => by
        rw [dist_comm, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hw]
        have := (w6Seq_Om_inc hR hC k ξ (hξ k hk) j).2 ζ (hζ k hk)
        refine le_of_eq_of_le ?_ this
        congr 2; ring
    rw [dist_comm, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hw, ← Finset.sum_mul] at h
    have e : w6Om7 ((𝒮 n).Om ξ) j - w6Om7 (Ω0 ξ) j - (w6Om7 ((𝒮 n).Om ζ) j - w6Om7 (Ω0 ζ) j) =
        w6Om7 ((𝒮 n).Om ξ) j - w6Om7 ((𝒮 n).Om ζ) j -
          (w6Om7 ((𝒮 0).Om ξ) j - w6Om7 ((𝒮 0).Om ζ) j) := by
      show _ = _ - (w6Om7 (Ω0 ξ) j - w6Om7 (Ω0 ζ) j); ring
    rw [e]
    exact h.trans (mul_le_mul_of_nonneg_right hl1 (norm_nonneg _))

omit hR hC in
theorem mem_w6PiStarIt {S0 : W6State} {ξ : Fin 2 → ℝ} (h : ξ ∈ w6PiStarIt d S0) (μ : ℕ) :
    ξ ∈ (w6Seq d S0 μ).Pi := Set.mem_iInter.1 h μ

/-- The pointwise and uniform convergence of `ω_ν` on `Π_*`, with tails `≤ 8πε₀ 4^{-n}`. -/
theorem w6Seq_om_limit :
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      Tendsto (fun ν => (𝒮 ν).om ξ) atTop (𝓝 (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ))) ∧
    TendstoUniformlyOn (fun ν => (𝒮 ν).om) (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0)) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) := by
  have he := hC.valid.eps0_pos
  obtain ⟨h1, -, h3⟩ := w6_uniform_limit (f := fun ν => (𝒮 ν).om)
    (A := w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) (C := 6 * π * d.eps0) (by positivity)
    fun n ξ hξ => by
      refine (w6Seq_om_inc hR hC n ξ (mem_w6PiStarIt hξ n)).1.trans ?_
      have := W6SeqData.eps_le_four_pow hC.valid hC.small n
      have hπ := Real.pi_pos
      calc 6 * π * d.eps n ≤ 6 * π * (d.eps0 / 4 ^ n) := by gcongr
        _ = 6 * π * d.eps0 / 4 ^ n := by ring
  exact ⟨h1, h3⟩

/-- The pointwise and uniform convergence of `Ω_{ν,j}` (W7 index) on `Π_*`. -/
theorem w6Seq_Om_limit (j : ℕ) :
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      Tendsto (fun ν => w6Om7 ((𝒮 ν).Om ξ) j) atTop
        (𝓝 (w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j))) ∧
    TendstoUniformlyOn (fun ν ξ => w6Om7 ((𝒮 ν).Om ξ) j)
      (fun ξ => w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) := by
  have he := hC.valid.eps0_pos
  obtain ⟨h1, -, h3⟩ := w6_uniform_limit (f := fun ν ξ => w6Om7 ((𝒮 ν).Om ξ) j)
    (A := w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) (C := 3 * d.eps0) (by positivity)
    fun n ξ hξ => by
      have h := (w6Seq_Om_inc hR hC n ξ (mem_w6PiStarIt hξ n) j).1
      have hw := one_le_normLab_rpow_half j
      have ha := abs_nonneg (w6Om7 ((𝒮 (n + 1)).Om ξ) j - w6Om7 ((𝒮 n).Om ξ) j)
      have := W6SeqData.eps_le_four_pow hC.valid hC.small n
      rw [Real.norm_eq_abs]
      have h2 : |w6Om7 ((𝒮 (n + 1)).Om ξ) j - w6Om7 ((𝒮 n).Om ξ) j| ≤ 3 * d.eps n := by nlinarith
      calc |w6Om7 ((𝒮 (n + 1)).Om ξ) j - w6Om7 ((𝒮 n).Om ξ) j| ≤ 3 * d.eps n := h2
        _ ≤ 3 * (d.eps0 / 4 ^ n) := by gcongr
        _ = 3 * d.eps0 / 4 ^ n := by ring
  exact ⟨h1, h3⟩

/-- **Convergence (ii)** (`bpW:w6:convergence` (ii); hypothesis-taking variant on `W6StepReal`, not
the label): `ω_ν → ω_*`, `Ω_ν → Ω_*` uniformly on `Π_*` (each `Ω_{·,j}`, W7 index), with
`|ω_* - ω_0| ≤ 8πε₀`, `|ω_* - ω_0|^ℒ ≤ 64πε₀/λ₀`, `sup_j (j+2)^{1/2} |Ω_{*,j} - Ω_{0,j}| ≤ 4ε₀`,
its Lipschitz constant `≤ 16ε₀/λ₀`, and `|⟨k, ω_*⟩ + ⟨l, Ω_*⟩| ≥ (α₀/2)⟨l⟩/A_k` for `(k,l) ∈ Z`.
(The same bounds for `(ω_ν, Ω_ν)` on `Π_{ν-1}`: `w6Seq_om_partial`, `w6Seq_Om_partial`.) -/
theorem w6ConvFreq_of_stepReal :
    TendstoUniformlyOn (fun ν => (𝒮 ν).om) (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0)) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) ∧
    (∀ j, TendstoUniformlyOn (fun ν ξ => w6Om7 ((𝒮 ν).Om ξ) j)
      (fun ξ => w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0))) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ‖w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ - ω0 ξ‖ ≤ 8 * π * d.eps0) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ∀ ζ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ‖(w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ - ω0 ξ) -
        (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ζ - ω0 ζ)‖ ≤
        64 * π * d.eps0 / d.lam 0 * ‖ξ - ζ‖) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) * |w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j - w6Om7 (Ω0 ξ) j| ≤
        4 * d.eps0) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ∀ ζ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) *
        |(w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j - w6Om7 (Ω0 ξ) j) -
          (w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ζ j - w6Om7 (Ω0 ζ) j)| ≤
        16 * d.eps0 / d.lam 0 * ‖ξ - ζ‖) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ), InZ k l →
      d.al0 / 2 * japL l / kAk k ≤
        |∑ i, (k i : ℝ) * w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ i +
          linF l (w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ)|) := by
  obtain ⟨hωp, hωu⟩ := w6Seq_om_limit hR hC
  have hΩp := fun j => (w6Seq_Om_limit hR hC j).1
  have hmem : ∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ n, ∀ μ < n, ξ ∈ (𝒮 μ).Pi :=
    fun ξ hξ _ μ _ => mem_w6PiStarIt hξ μ
  refine ⟨hωu, fun j => (w6Seq_Om_limit hR hC j).2, fun ξ hξ => ?_, fun ξ hξ ζ hζ => ?_,
    fun ξ hξ j => ?_, fun ξ hξ ζ hζ j => ?_, fun ξ hξ k l hkl => ?_⟩
  · exact le_of_tendsto' ((hωp ξ hξ).sub_const (ω0 ξ)).norm fun n =>
      (w6Seq_om_partial hR hC n (hmem ξ hξ n) (hmem ξ hξ n)).1
  · exact le_of_tendsto' (((hωp ξ hξ).sub_const (ω0 ξ)).sub
      ((hωp ζ hζ).sub_const (ω0 ζ))).norm fun n =>
      (w6Seq_om_partial hR hC n (hmem ξ hξ n) (hmem ζ hζ n)).2
  · exact le_of_tendsto' (((hΩp j ξ hξ).sub_const _).abs.const_mul _) fun n =>
      (w6Seq_Om_partial hR hC n (hmem ξ hξ n) (hmem ξ hξ n) j).1
  · exact le_of_tendsto' ((((hΩp j ξ hξ).sub_const _).sub
      ((hΩp j ζ hζ).sub_const _)).abs.const_mul _) fun n =>
      (w6Seq_Om_partial hR hC n (hmem ξ hξ n) (hmem ζ hζ n) j).2
  · refine w6_divisor_limit (hωp ξ hξ) (fun j => hΩp j ξ hξ)
      (fun ν => W6SeqData.half_le_alpha hC.valid ν) k l fun ν => ?_
    exact (w6Seq_stage_of_stepReal hR hC ν).mel ξ (mem_w6PiStarIt hξ ν) k l hkl

/-- **Convergence (i), Borel** (`bpW:w6:convergence` (i); hypothesis-taking variant): if `Π_{-1}` is
Borel, every `Π_ν` and `Π_*` are Borel (the `ω_ν`, `Ω_{ν,j}` are Lipschitz, hence continuous, on
`Π_{ν-1}`). -/
theorem w6ConvBorel_of_stepReal (hPm : MeasurableSet Pm) :
    (∀ ν, MeasurableSet (𝒮 ν).Pi) ∧ MeasurableSet (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) := by
  obtain ⟨T, Mω, MΩ, hf, -⟩ := hC.freq
  set ωs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ := fun n => (𝒮 n).om
  set Ωs : ℕ → (Fin 2 → ℝ) → ℕ → ℝ := fun n ξ => w6Om7 ((𝒮 n).Om ξ)
  have hsub : ∀ n, w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n ⊆ Pm := w6PiSeq_subset Pm ωs Ωs _ _
  have hmem : ∀ n, ∀ ξ ∈ w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n, ∀ μ < n, ξ ∈ (𝒮 μ).Pi := by
    intro n ξ hξ μ hμ
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← w6Seq_Pi_eq_of_stepReal hR hC n] at hξ
    exact w6Seq_Pi_antitone d _ (Nat.lt_succ_iff.1 hμ) hξ
  have hω : ∀ n, ContinuousOn (ωs n) (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) := by
    intro n
    have h1 : ContinuousOn (fun ξ => (𝒮 n).om ξ - ω0 ξ) (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) :=
      w6_continuousOn_of_lip fun ξ hξ ζ hζ =>
        (w6Seq_om_partial hR hC n (hmem n ξ hξ) (hmem n ζ hζ)).2
    have h0 : ContinuousOn ω0 (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) :=
      w6_continuousOn_of_lip fun ξ hξ ζ hζ => hf.lipOmega ξ (hsub n hξ) ζ (hsub n hζ)
    exact (h1.add h0).congr fun ξ _ => by simp [ωs]
  have hΩ : ∀ n j, ContinuousOn (fun ξ => Ωs n ξ j) (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) := by
    intro n j
    have hw := one_le_normLab_rpow_half j
    have h1 : ContinuousOn (fun ξ => w6Om7 ((𝒮 n).Om ξ) j - w6Om7 (Ω0 ξ) j)
        (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) :=
      w6_continuousOn_of_lip (L := 16 * d.eps0 / d.lam 0) fun ξ hξ ζ hζ => by
        have h := (w6Seq_Om_partial hR hC n (hmem n ξ hξ) (hmem n ζ hζ) j).2
        rw [Real.norm_eq_abs]
        have ha := abs_nonneg ((w6Om7 ((𝒮 n).Om ξ) j - w6Om7 (Ω0 ξ) j) -
          (w6Om7 ((𝒮 n).Om ζ) j - w6Om7 (Ω0 ζ) j))
        nlinarith
    have h0 : ContinuousOn (fun ξ => w6Om7 (Ω0 ξ) j) (w6PiSeq Pm ωs Ωs d.alpha d.KprevNu n) :=
      w6_continuousOn_of_lip (L := MΩ) fun ξ hξ ζ hζ => by
        have h := hf.lipTail ξ (hsub n hξ) ζ (hsub n hζ) j.succPNat
        have hw' : 1 ≤ ((j.succPNat : ℕ+) : ℝ) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast j.succPNat.pos) (by norm_num)
        rw [Real.norm_eq_abs]
        have ha := abs_nonneg (Ω0 ξ j.succPNat - Ω0 ζ j.succPNat)
        show |Ω0 ξ j.succPNat - Ω0 ζ j.succPNat| ≤ _
        nlinarith
    exact (h1.add h0).congr fun ξ _ => by simp [Ωs]
  obtain ⟨hall, hstar⟩ := w6PiSeq_measurableSet Pm ωs Ωs d.alpha d.KprevNu hPm hω hΩ
  refine ⟨fun ν => ?_, ?_⟩
  · rw [w6Seq_Pi_eq_of_stepReal hR hC ν]; exact hall (ν + 1)
  · rw [w6PiStarIt_eq_of_stepReal hR hC]; exact hstar

end conv

end KAM.Wave
