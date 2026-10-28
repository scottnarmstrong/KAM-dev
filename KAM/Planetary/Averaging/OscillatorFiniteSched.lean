/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorStepComplete
public import KAM.Planetary.Averaging.OscillatorClassAlgebra
public import KAM.Planetary.Averaging.FiniteSchedule

/-!
# P Part 2: the oscillator finite averaging iteration, schedule and stages
(`stepP:p2:oa-iter`)

`OSched` is a loss schedule for the four radii `(r, rp, rq, S)`, one `Sched` for each of the action,
the oscillator coordinates and the strip (the `Sched` fields `r`, `ρ` are the radius and loss;
`s`, `σ` of the first component are the strip). `OSched.seq` is the recursive sequence `(gᵢ, fᵢ)`:
`g₀ = 0`, `f₀ = f`, `gᵢ₊₁ = gᵢ + f̂ᵢ,₀`, and `fᵢ₊₁` the remainder `fp` of the complete step
`osc_iter` applied at stage `i`. `OIter` is the premise bundle with claimed remainder bounds `ε`;
`OStepConc` is everything one stage delivers, obtained from `osc_iter` on the same maps.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Schedules of the action radius (`x`), the oscillator radius `rp` (`p`), the oscillator radius
`rq` (`q`); the strip is the `S`, `σ` of `x`. -/
structure OSched where
  x : Sched
  p : Sched
  q : Sched

namespace OSched

variable {n m : ℕ}

/-- The time-one map of the step at stage `i` for the current remainder `F`. -/
def Φ0 (c : OSched) (D : Set (Fin n → ℝ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (F : CHam (n + m))
    (i : ℕ) : CPhase (n + m) → CPhase (n + m) :=
  oscStepMap D (c.x.R i) (c.p.R i) (c.q.R i) (c.x.S i) (c.x.ρ i) (c.p.ρ i) (c.q.ρ i)
    (c.x.σ i) K h F

/-- The pairs `(gᵢ, fᵢ)`. -/
def seq (c : OSched) (D : Set (Fin n → ℝ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) :
    ℕ → CHam (n + m) × CHam (n + m)
  | 0 => (fun _ => 0, f)
  | i + 1 =>
    (fun z => (seq c D K h f i).1 z + coeff (oscFunction (seq c D K h f i).2) (oscPack z).2 0,
      fun z => h (firstBlock (b := m) (c.Φ0 D K h (seq c D K h f i).2 i z).2) +
        (seq c D K h f i).1 (c.Φ0 D K h (seq c D K h f i).2 i z) +
        (seq c D K h f i).2 (c.Φ0 D K h (seq c D K h f i).2 i z) -
        h (firstBlock (b := m) z.2) -
        ((seq c D K h f i).1 z + coeff (oscFunction (seq c D K h f i).2) (oscPack z).2 0))

variable (c : OSched) (D : Set (Fin n → ℝ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m))

def G (i : ℕ) : CHam (n + m) := (c.seq D K h f i).1

def F (i : ℕ) : CHam (n + m) := (c.seq D K h f i).2

/-- The time-one map of stage `i`. -/
def Φ (i : ℕ) : CPhase (n + m) → CPhase (n + m) := c.Φ0 D K h (c.F D K h f i) i

/-- The zero-mode increment of stage `i`. -/
def inc (i : ℕ) : CHam (n + m) := fun z => coeff (oscFunction (c.F D K h f i)) (oscPack z).2 0

/-- The stage domain `oscDom (Rᵢ, Rpᵢ, Rqᵢ, Sᵢ)`. -/
def U (i : ℕ) : Set (CPhase (n + m)) :=
  oscDom D (c.x.R i) (c.p.R i) (c.q.R i) (c.x.S i)

theorem G_zero : c.G D K h f 0 = fun _ => 0 := rfl

theorem F_zero : c.F D K h f 0 = f := rfl

theorem G_succ (i : ℕ) : c.G D K h f (i + 1) = fun z => c.G D K h f i z + c.inc D K h f i z := rfl

theorem F_succ (i : ℕ) :
    c.F D K h f (i + 1) = fun z =>
      h (firstBlock (b := m) (c.Φ D K h f i z).2) + c.G D K h f i (c.Φ D K h f i z) +
        c.F D K h f i (c.Φ D K h f i z) - h (firstBlock (b := m) z.2) - c.G D K h f (i + 1) z :=
  rfl

/-- `gᵢ` is the sum of the zero-mode increments of the earlier stages. -/
theorem G_eq_sum (i : ℕ) : c.G D K h f i = fun z => ∑ j : Fin i, c.inc D K h f j z := by
  induction i with
  | zero => funext z; simp [G_zero]
  | succ i ih =>
    funext z
    rw [G_succ, Fin.sum_univ_castSucc, ih]
    simp

end OSched

/-- Source premises and numerical budget of the oscillator iteration up to stage `M`. -/
structure OIter {n m : ℕ} (D : Set (Fin n → ℝ)) (c : OSched) (K α : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) (ε : ℕ → ℝ) (M : ℕ) : Prop where
  n_pos : 1 ≤ n
  m_pos : 1 ≤ m
  K_nonneg : 0 ≤ K
  α_pos : 0 < α
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D c.x.r)
  div : DivisorBound (KAM.actionNbhd D c.x.r) K {0} h α
  real_h : RealOn (oscDom (m := m) D c.x.r c.p.r c.q.r c.x.s)
    (fun z => h (firstBlock (b := m) z.2))
  real_f : RealOn (oscDom (m := m) D c.x.r c.p.r c.q.r c.x.s) f
  cls : oscClass D c.x.r c.p.r c.q.r c.x.s f
  bound : oscBound D c.x.r c.p.r c.q.r c.x.s f (ε 0)
  widths : ∀ i ≤ M, 0 < c.x.ρ i ∧ 2 * c.x.ρ i < c.x.R i ∧ 0 < c.p.ρ i ∧ 2 * c.p.ρ i < c.p.R i ∧
    0 < c.q.ρ i ∧ 2 * c.q.ρ i < c.q.R i ∧ 0 < c.x.σ i ∧ 2 * c.x.σ i < c.x.S i
  ε_nonneg : ∀ i ≤ M + 1, 0 ≤ ε i
  small : ∀ i ≤ M, ε i ≤ (2 * π * α) * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i) /
    (16 * (1 + (m : ℝ)))
  step : ∀ i ≤ M,
    (1 - 2 * exp 1 * (1 + (m : ℝ)) * ε i /
        (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)))⁻¹ *
      (2 * (1 + (m : ℝ)) / (2 * π * α * min (c.x.ρ i * c.x.σ i) (c.p.ρ i * c.q.ρ i)) *
        (∑ j : Fin i, max (max (c.x.ρ i / (c.x.R j - c.x.R i + c.x.ρ i))
            (c.x.σ i / (c.x.S j - c.x.S i + c.x.σ i)))
          (max (c.p.ρ i / (c.p.R j - c.p.R i + c.p.ρ i))
            (c.q.ρ i / (c.q.R j - c.q.R i + c.q.ρ i))) * ε j + ε i) +
        exp (-(2 * π * K * c.x.σ i))) * ε i ≤ ε (i + 1)

section Stage

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {c : OSched} {K α : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)} {ε : ℕ → ℝ} {M : ℕ}

/-- The invariant of stage `j`: class, claimed bound and reality of the current remainder, class and
reality of the accumulated normal form. -/
def OInv (D : Set (Fin n → ℝ)) (c : OSched) (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m))
    (ε : ℕ → ℝ) (j : ℕ) : Prop :=
  oscClass D (c.x.R j) (c.p.R j) (c.q.R j) (c.x.S j) (c.F D K h f j) ∧
    oscBound D (c.x.R j) (c.p.R j) (c.q.R j) (c.x.S j) (c.F D K h f j) (ε j) ∧
    RealOn (c.U (m := m) D j) (c.F D K h f j) ∧
    oscClass D (c.x.R j) (c.p.R j) (c.q.R j) (c.x.S j) (c.G D K h f j) ∧
    RealOn (c.U (m := m) D j) (c.G D K h f j)

/-- Everything stage `i` delivers. -/
structure OStepConc (D : Set (Fin n → ℝ)) (c : OSched) (K α : ℝ) (h : (Fin n → ℂ) → ℂ)
    (f : CHam (n + m)) (ε : ℕ → ℝ) (i : ℕ) : Prop where
  diff : DifferentiableOn ℂ (c.Φ D K h f i) (oscDom D (c.x.R i - 3 * c.x.ρ i / 2)
    (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2))
  mapsTo : MapsTo (c.Φ D K h f i) (oscDom D (c.x.R i - 3 * c.x.ρ i / 2)
    (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2))
    (oscDom D (c.x.R i - c.x.ρ i) (c.p.R i - c.p.ρ i) (c.q.R i - c.q.ρ i) (c.x.S i - c.x.σ i))
  inj : InjOn (c.Φ D K h f i) (c.U (m := m) D (i + 1))
  sympl : ∀ z ∈ oscDom (m := m) D (c.x.R i - 3 * c.x.ρ i / 2)
    (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2),
    ∀ v w, symplFormC (fderiv ℂ (c.Φ D K h f i) z v) (fderiv ℂ (c.Φ D K h f i) z w) =
      symplFormC v w
  trans : ∀ k : Fin n → ℤ, ∀ z ∈ oscDom (m := m) D (c.x.R i - 3 * c.x.ρ i / 2)
    (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2),
    c.Φ D K h f i (z + (Fin.append (fun j => (k j : ℂ)) 0, 0)) =
      c.Φ D K h f i z + (Fin.append (fun j => (k j : ℂ)) 0, 0)
  disp : ∀ z ∈ oscDom (m := m) D (c.x.R i - 3 * c.x.ρ i / 2)
    (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2),
    ‖firstBlock (b := m) ((c.Φ D K h f i z).1 - z.1)‖ ≤ ε i / (2 * π * α * c.x.ρ i) ∧
    ‖firstBlock (b := m) ((c.Φ D K h f i z).2 - z.2)‖ ≤
      ε i / (exp 1 * (2 * π * α) * c.x.σ i) ∧
    ‖lastBlock (a := n) ((c.Φ D K h f i z).1 - z.1)‖ ≤ ε i / (2 * π * α * c.p.ρ i) ∧
    ‖lastBlock (a := n) ((c.Φ D K h f i z).2 - z.2)‖ ≤ ε i / (2 * π * α * c.q.ρ i)
  cls : oscClass D (c.x.R (i + 1)) (c.p.R (i + 1)) (c.q.R (i + 1)) (c.x.S (i + 1))
    (c.F D K h f (i + 1))
  bound : oscBound D (c.x.R (i + 1)) (c.p.R (i + 1)) (c.q.R (i + 1)) (c.x.S (i + 1))
    (c.F D K h f (i + 1)) (ε (i + 1))
  real_F : RealOn (c.U (m := m) D (i + 1)) (c.F D K h f (i + 1))
  cls_G : oscClass D (c.x.R i) (c.p.R i) (c.q.R i) (c.x.S i) (c.G D K h f (i + 1))
  real_G : RealOn (c.U (m := m) D (i + 1)) (c.G D K h f (i + 1))
  inc_cls : oscClass D (c.x.R i) (c.p.R i) (c.q.R i) (c.x.S i) (c.inc D K h f i)
  inc_bound : oscBound D (c.x.R i) (c.p.R i) (c.q.R i) (c.x.S i) (c.inc D K h f i) (ε i)
  real_Φ : ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ c.U (m := m) D (i + 1) →
    c.Φ D K h f i (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))
  ident : ∀ z ∈ c.U (m := m) D (i + 1),
    h (firstBlock (b := m) (c.Φ D K h f i z).2) + c.G D K h f i (c.Φ D K h f i z) +
        c.F D K h f i (c.Φ D K h f i z) =
      h (firstBlock (b := m) z.2) + c.G D K h f (i + 1) z + c.F D K h f (i + 1) z

theorem OIter.R_anti (hS : OIter D c K α h f ε M) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M + 1) :
    c.x.R j ≤ c.x.R i ∧ c.p.R j ≤ c.p.R i ∧ c.q.R j ≤ c.q.R i ∧ c.x.S j ≤ c.x.S i := by
  have hw := hS.widths
  refine ⟨c.x.R_anti (fun l hl => (hw l (by omega)).1.le) hij,
    c.p.R_anti (fun l hl => (hw l (by omega)).2.2.1.le) hij,
    c.q.R_anti (fun l hl => (hw l (by omega)).2.2.2.2.1.le) hij,
    c.x.S_anti (fun l hl => (hw l (by omega)).2.2.2.2.2.2.1.le) hij⟩

theorem OIter.U_succ_subset (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M) :
    c.U (m := m) D (i + 1) ⊆ c.U (m := m) D i := by
  obtain ⟨a, b, d, e⟩ := hS.R_anti (Nat.le_succ i) (by omega)
  exact oscDom_mono a b d e

theorem OIter.U_sub_start (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M + 1) :
    c.U (m := m) D i ⊆ oscDom D c.x.r c.p.r c.q.r c.x.s := by
  obtain ⟨a, b, d, e⟩ := hS.R_anti (Nat.zero_le i) hi
  exact oscDom_mono a b d e

theorem OIter.U_sub_big (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M) :
    c.U (m := m) D (i + 1) ⊆ oscDom D (c.x.R i - 3 * c.x.ρ i / 2)
      (c.p.R i - 3 * c.p.ρ i / 2) (c.q.R i - 3 * c.q.ρ i / 2) (c.x.S i - 3 * c.x.σ i / 2) := by
  obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := hS.widths i hi
  refine oscDom_mono ?_ ?_ ?_ ?_
  · rw [Sched.R_succ c.x]; linarith
  · rw [Sched.R_succ c.p]; linarith
  · rw [Sched.R_succ c.q]; linarith
  · rw [Sched.S_succ c.x]; linarith

end Stage

end KAM.Planetary

end
