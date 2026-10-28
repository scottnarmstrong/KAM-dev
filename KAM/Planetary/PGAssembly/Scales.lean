/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyBounds

/-!
# P Part 5: the data-only scales `k0, k1, G` (`bpP:p5:kam-cond`)

`kam_c1` is the stable numeric constant `C1` (`bpP:p5:kam-hyp#C1`). `log_power_dominated` is the
growth comparison `K^2 / (log K)^p → ∞` (`isLittleO_log_rpow_rpow_atTop`). `PGScaleSpec` lists the
inequalities of `bpP:p5:kam-cond`, `kam_cond` chooses `k0` first, `k1` second and `G` third, and
`pgScales` selects the witness. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-SCALE.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

/-- Arbitrarily large `K` with `A (log K)^p < K^2`; the unbounded form of `log_power_dominated`. -/
theorem log_power_dominated_large {p A : ℝ} (hp : 0 < p) (hA : 0 < A) (M : ℝ) :
    ∃ K : ℝ, M ≤ K ∧ 1 < K ∧ A*(Real.log K)^p < K^2 := by
  have ho := (isLittleO_log_rpow_rpow_atTop p (s := 2) (by norm_num)).def
    (c := 1/(2*A)) (by positivity)
  obtain ⟨K, hK, hM, h1⟩ := (ho.and ((eventually_ge_atTop M).and (eventually_gt_atTop 1))).exists
  refine ⟨K, hM, h1, ?_⟩
  have hK0 : 0 < K := by linarith
  have hl : 0 ≤ Real.log K := Real.log_nonneg h1.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl p), Real.norm_of_nonneg (Real.rpow_nonneg hK0.le 2),
    Real.rpow_two] at hK
  have hK2 : 0 < K^2 := by positivity
  have : A*(Real.log K)^p ≤ K^2/2 := by
    calc A*(Real.log K)^p ≤ A*(1/(2*A)*K^2) := by gcongr
      _ = K^2/2 := by field_simp
  linarith

theorem log_power_dominated {p A : ℝ} (hp : 0 < p) (hA : 0 < A) :
    ∃ K : ℝ, 1 < K ∧ A*(Real.log K)^p < K^2 := by
  obtain ⟨K, -, h1, h2⟩ := log_power_dominated_large hp hA 0
  exact ⟨K, h1, h2⟩

/-- Stable numeric constant C1, before r and mu; period factors included. -/
def kam_c1 (d : PGData a b) : ℝ :=
  max 1 (max (2*Real.pi*pgCU (pgAnalytic d))
    ((2^5*(pgAnalytic d).CQ+2*(pgAnalytic d).LP)*
      KAM.Weighted.coth (pgWidth d/24)^(a+b)/(2*Real.pi)))

structure PGScales where
  k0 : ℝ
  k1 : ℝ
  G : ℝ

def pgTau (a b : ℕ) : ℝ := (a+b:ℕ)+1

def pgK0 (d : PGData a b) (s : PGScales) : ℝ :=
  6/(pgWidth d/60)*max 1 (Real.log (s.k0^2/(kam_c1 d)^4))

def pgChat (a b : ℕ) : ℝ := max (2^13*(a+b:ℕ)) (24^(pgTau a b+1)/3)

def PGScaleSpec (d : PGData a b) (s : PGScales) : Prop :=
  (kam_c1 d)^2 ≤ s.k0 ∧ 0 < s.k1 ∧
  9*pgChat a b*(kam_c1 d)^4*(pgK0 d s)^(2*pgTau a b+2) < s.k0^2 ∧
  4*pgChat a b*(kam_c1 d)^2 < s.k1^2 ∧
  max (2*(pgAnalytic d).M0*s.k1)
    (max (Real.sqrt (2^14*(1+b)*(pgAnalytic d).M0))
      (Real.sqrt (1600*(1+b)*(pgAnalytic d).M0/pgWidth d))) ≤ s.G

theorem pgTau_pos (a b : ℕ) : 0 < pgTau a b := by
  unfold pgTau; positivity

theorem pgChat_pos (a b : ℕ) : 0 < pgChat a b :=
  lt_max_of_lt_right (by have := pgTau_pos a b; positivity)

theorem pgWidth_pos (d : PGData a b) : 0 < pgWidth d := by
  unfold pgWidth; linarith [(pgExtension d).delta_pos]

theorem one_le_kam_c1 (d : PGData a b) : 1 ≤ kam_c1 d := le_max_left _ _

theorem kam_cond (d : PGData a b) : ∃ s : PGScales, PGScaleSpec d s := by
  set C := kam_c1 d with hC
  have hC1 : 1 ≤ C := one_le_kam_c1 d
  have hCpos : 0 < C := by linarith
  have hw := pgWidth_pos d
  have hc := pgChat_pos a b
  set p : ℝ := 2*pgTau a b+2 with hpdef
  have hp : 0 < p := by have := pgTau_pos a b; positivity
  obtain ⟨K, hKe, hK1, hK⟩ := log_power_dominated_large hp
    (A := 9*pgChat a b*(720/pgWidth d)^p) (by positivity) (Real.exp 1)
  have hK0 : 0 < K := by linarith
  have hlog1 : 1 ≤ Real.log K := by
    rw [Real.le_log_iff_exp_le hK0]; exact hKe
  have hsq : (C^2*K)^2/C^4 = K^2 := by field_simp
  have hlog : Real.log ((C^2*K)^2/C^4) = 2*Real.log K := by
    rw [hsq, Real.log_pow]; push_cast; ring
  refine ⟨⟨C^2*K, 4*pgChat a b*C^2+1, max (2*(pgAnalytic d).M0*(4*pgChat a b*C^2+1))
    (max (Real.sqrt (2^14*(1+b)*(pgAnalytic d).M0))
      (Real.sqrt (1600*(1+b)*(pgAnalytic d).M0/pgWidth d)))⟩, ?_, ?_, ?_, ?_, le_rfl⟩
  · show C^2 ≤ C^2*K
    nlinarith [sq_nonneg C]
  · show 0 < 4*pgChat a b*C^2+1
    positivity
  · show 9*pgChat a b*C^4*(pgK0 d ⟨C^2*K, _, _⟩)^p < (C^2*K)^2
    have hk : pgK0 d ⟨C^2*K, 0, 0⟩ = 720/pgWidth d*Real.log K := by
      unfold pgK0
      show 6/(pgWidth d/60)*max 1 (Real.log ((C^2*K)^2/C^4)) = _
      rw [hlog, max_eq_right (by linarith)]
      field_simp; ring
    show 9*pgChat a b*C^4*(pgK0 d ⟨C^2*K, 0, 0⟩)^p < (C^2*K)^2
    rw [hk, Real.mul_rpow (by positivity) (by linarith)]
    have : (C^2*K)^2 = C^4*K^2 := by ring
    rw [this]
    have h4 : 0 < C^4 := by positivity
    calc 9*pgChat a b*C^4*((720/pgWidth d)^p*Real.log K^p)
        = C^4*(9*pgChat a b*(720/pgWidth d)^p*Real.log K^p) := by ring
      _ < C^4*K^2 := by gcongr
  · show 4*pgChat a b*C^2 < (4*pgChat a b*C^2+1)^2
    have : 0 ≤ 4*pgChat a b*C^2 := by positivity
    nlinarith

def pgScales (d : PGData a b) : PGScales := (kam_cond d).choose

theorem pgScales_spec (d : PGData a b) : PGScaleSpec d (pgScales d) := (kam_cond d).choose_spec

end KAM.Planetary

end
