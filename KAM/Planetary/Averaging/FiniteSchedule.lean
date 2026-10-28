/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Splitting
public import KAM.Nekhoroshev.NormalForm.Telescope

/-!
# P Part 2: the finite averaging iteration, schedule and stage data (`bpP:p2:nfb`)

`Sched` is a loss schedule `(ρᵢ, σᵢ)`; `Sched.seq` is the recursive sequence `(gᵢ, fᵢ)` of the
finite iteration (`f₀ = f`, `g₀ = 0`, one step of the N `iterG`, `iterF` with `Λ = {0}` at
stage `i`).
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Start radii and the per-step losses of a finite iteration. -/
structure Sched where
  r : ℝ
  s : ℝ
  ρ : ℕ → ℝ
  σ : ℕ → ℝ

namespace Sched

/-- Action radius at stage `i`: `R₀ = r`, `Rᵢ₊₁ = Rᵢ - 2ρᵢ`. -/
def R (c : Sched) : ℕ → ℝ
  | 0 => c.r
  | i + 1 => c.R i - 2 * c.ρ i

/-- Strip width at stage `i`: `S₀ = s`, `Sᵢ₊₁ = Sᵢ - 2σᵢ`. -/
def S (c : Sched) : ℕ → ℝ
  | 0 => c.s
  | i + 1 => c.S i - 2 * c.σ i

variable {n : ℕ}

/-- The pairs `(gᵢ, fᵢ)`: accumulated normal form before stage `i` and current remainder. -/
def seq (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) :
    ℕ → CHam n × CHam n
  | 0 => (0, f)
  | i + 1 => (iterG K {0} (seq c D K h f i).1 (seq c D K h f i).2,
      iterF D (c.R i) (c.S i) (c.ρ i) (c.σ i) K {0} h (seq c D K h f i).1 (seq c D K h f i).2)

def G (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (i : ℕ) :
    CHam n := (c.seq D K h f i).1

def F (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (i : ℕ) :
    CHam n := (c.seq D K h f i).2

/-- The time-one map of stage `i`. -/
def Φ (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n) (i : ℕ) :
    CPhase n → CPhase n :=
  iterMap D (c.R i) (c.S i) (c.ρ i) (c.σ i) K {0} h (c.F D K h f i)

variable (c : Sched) (D : Set (Fin n → ℂ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam n)

theorem G_zero : c.G D K h f 0 = 0 := rfl

theorem F_zero : c.F D K h f 0 = f := rfl

theorem G_succ (i : ℕ) :
    c.G D K h f (i + 1) = iterG K {0} (c.G D K h f i) (c.F D K h f i) := rfl

theorem F_succ (i : ℕ) :
    c.F D K h f (i + 1) =
      iterF D (c.R i) (c.S i) (c.ρ i) (c.σ i) K {0} h (c.G D K h f i) (c.F D K h f i) := rfl

theorem R_succ (i : ℕ) : c.R (i + 1) = c.R i - 2 * c.ρ i := rfl

theorem S_succ (i : ℕ) : c.S (i + 1) = c.S i - 2 * c.σ i := rfl

theorem R_anti {i j : ℕ} (hρ : ∀ l, l < j → 0 ≤ c.ρ l) (hij : i ≤ j) : c.R j ≤ c.R i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := ih fun l hl => hρ l (hl.trans (Nat.lt_succ_self j))
    have := hρ j (Nat.lt_succ_self j)
    rw [R_succ]; linarith

theorem S_anti {i j : ℕ} (hσ : ∀ l, l < j → 0 ≤ c.σ l) (hij : i ≤ j) : c.S j ≤ c.S i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := ih fun l hl => hσ l (hl.trans (Nat.lt_succ_self j))
    have := hσ j (Nat.lt_succ_self j)
    rw [S_succ]; linarith

/-- `gᵢ` is the sum of the zero-mode increments of the earlier stages. -/
theorem G_eq_sum (i : ℕ) :
    c.G D K h f i = fun z => ∑ j : Fin i, homRes K {0} (c.F D K h f j) z := by
  induction i with
  | zero => funext z; simp [G_zero]
  | succ i ih =>
    funext z
    rw [G_succ, Fin.sum_univ_castSucc]
    show c.G D K h f i z + homRes K {0} (c.F D K h f i) z = _
    rw [ih]
    simp

end Sched

section Zero

variable {n : ℕ}

/-- For `K ≥ 0` the resonant part at `Λ = {0}` is the Fourier zero mode. -/
theorem homRes_zero {D : Set (Fin n → ℂ)} {r s K M : ℝ} {f : CHam n} (hs : 0 < s) (hK : 0 ≤ K)
    (hu : InClass D r s f) (hb : WBound D r s f M) {z : CPhase n} (hz : z ∈ Dom n D r s) :
    homRes K {0} f z = coeff f z.2 0 := by
  have e : homRes K {0} f = modeAverage (truncate K f) := by
    rw [modeAverage_eq_projMode]; rfl
  rw [e]
  show coeff (truncate K f) z.2 0 = _
  have := (projections hs hu hb {k | KAM.Fourier.modeSize k ≤ K}).2.1 z.2 hz.2 0
  rw [show truncate K f = projMode {k | KAM.Fourier.modeSize k ≤ K} f from rfl, this,
    Set.indicator_of_mem]
  show KAM.Fourier.modeSize (0 : Fin n → ℤ) ≤ K
  simpa [KAM.Fourier.modeSize] using hK

variable {D : Set (Fin n → ℂ)} {r s K α q δ : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam n}

/-- Class, bound and reality of the resonant part at a stage. -/
theorem homRes_stage (H : DirectHyp D r s K α q δ {0} h f) :
    InClass D r s (homRes K {0} f) ∧ WBound D r s (homRes K {0} f) δ ∧
    (RealOn (Dom n D r s) (fun w => h w.2) → RealOn (Dom n D r s) f →
      RealOn (Dom n D r s) (homRes K {0} f)) := by
  have hα : 0 < 2 * α / q := by
    have := H.α_pos
    have := H.q_ge
    positivity
  obtain ⟨-, c2, -, -, -, -, c7, -, -, c10⟩ :=
    homological_direct (p := 2) (by norm_num) hα H.s_pos H.K_nonneg H.holo (divisor_two H)
      H.cls H.bound
  refine ⟨c2, c7, fun hhr hfr => ?_⟩
  exact (c10 (fun k hk => by rw [Set.mem_singleton_iff] at hk ⊢; rw [hk]; simp) hfr
    (fun I hI i => freq_im_real H.s_pos H.holo hhr hI i)).2

/-- The N iteration hypotheses (`p = 2`, `α_N = 2α/q`) behind `direct_step`. -/
theorem iterHyp_two {J : ℕ} {ρ σ : ℝ} {Λ : Set (Fin n → ℤ)}
    {gj : Fin J → CHam n} {rj sj Mj : Fin J → ℝ}
    (H : DirectHyp D r s K α q δ Λ h f)
    (hρ : 0 < ρ ∧ 2 * ρ < r) (hσ : 0 < σ ∧ 2 * σ < s)
    (hsmall : q * δ / (2 * π * α * ρ * σ) ≤ 1 / 4)
    (hg : ∀ j, InClass D (rj j) (sj j) (gj j) ∧ WBound D (rj j) (sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ s ≤ sj j) :
    IterHyp D r s ρ σ K (2 * α / q) 2 δ Λ h (fun z => ∑ j, gj j z) f gj rj sj Mj := by
  have hα : 0 < 2 * α / q := by
    have := H.α_pos
    have := H.q_ge
    positivity
  have hu := iterU_two H ρ σ
  exact
    { hp := by norm_num
      hα := hα
      hK := H.K_nonneg
      hs := H.s_pos
      hρ := hρ.1
      hρr := hρ.2
      hσ := hσ.1
      hσs := hσ.2
      h_holo := H.holo
      divisor := divisor_two H
      decomp := ⟨rfl, fun j => (hg j).2.2.1, fun j => (hg j).2.2.2, fun j => (hg j).1,
        fun j => (hg j).2.1⟩
      f_class := H.cls
      f_bound := H.bound
      δ_nonneg := H.δ_nonneg
      δ_small := by
        have h1 : iterU (2 * α / q) 2 δ ρ σ ≤ 1 / 4 := hu ▸ hsmall
        unfold iterU at h1
        rw [div_le_iff₀ (by have := hρ.1; have := hσ.1; positivity)] at h1
        rw [le_div_iff₀ (by rw [conjExp_two]; norm_num)]
        linarith }

end Zero

end KAM.Planetary

end
