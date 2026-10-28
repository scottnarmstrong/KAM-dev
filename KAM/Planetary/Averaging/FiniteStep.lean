/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteSchedule

/-!
# P Part 2: one stage of the finite averaging iteration (`bpP:p2:nfb`, `stepP:p2:nfb-ind`)

`IterSetup` is the premise bundle of a finite iteration on a schedule with claimed remainder bounds
`ε`; `StepConc` is everything one stage delivers: it combines `direct_step`, `split` and the N
`iterative_direct_a` (the integer translation law on the same flow). `step_conc` proves it from the
stage invariant `Inv` of all earlier stages, and `inv_all` propagates `Inv`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ}

/-- Source premises and numerical budget of the finite iteration up to stage `m`. -/
structure IterSetup (Dc : Set (Fin (a + b) → ℂ)) (c : Sched) (K α₁ α₂ : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) (ε : ℕ → ℝ) (m : ℕ) : Prop where
  K_nonneg : 0 ≤ K
  α₂_pos : 0 < α₂
  α_order : α₂ ≤ α₁
  holo : DifferentiableOn ℂ h (polyNbhd Dc c.r)
  real_h : RealOn (Dom (a + b) Dc c.r c.s) (fun z => h z.2)
  real_f : RealOn (Dom (a + b) Dc c.r c.s) f
  cls : InClass Dc c.r c.s f
  bound : WBound Dc c.r c.s f (ε 0)
  div : TwoDiv (polyNbhd Dc c.r) K α₁ α₂ 1 h
  ρ_pos : ∀ i ≤ m, 0 < c.ρ i
  ρ_lt : ∀ i ≤ m, 2 * c.ρ i < c.R i
  σ_pos : ∀ i ≤ m, 0 < c.σ i
  σ_lt : ∀ i ≤ m, 2 * c.σ i < c.S i
  ε_nonneg : ∀ i ≤ m + 1, 0 ≤ ε i
  small : ∀ i ≤ m, 1 * ε i / (2 * π * α₂ * c.ρ i * c.σ i) ≤ 1 / 4
  step : ∀ i ≤ m,
    (1 - 2 * (1 * ε i / (2 * π * α₂ * c.ρ i * c.σ i)))⁻¹ *
      (2 * 1 / (exp 1 * (2 * π * α₂) * c.ρ i * c.σ i) *
        (∑ j : Fin i, (1 / 2) * (c.ρ i / (c.R j - c.R i + c.ρ i) +
          c.σ i / (c.S j - c.S i + c.σ i)) * ε j + ε i) +
        exp (-(2 * π * K * c.σ i))) * ε i ≤ ε (i + 1)

/-- The invariant of stage `j`: class, claimed bound and reality of the current remainder. -/
def Inv (Dc : Set (Fin (a + b) → ℂ)) (c : Sched) (K : ℝ) (h : (Fin (a + b) → ℂ) → ℂ)
    (f : CHam (a + b)) (ε : ℕ → ℝ) (j : ℕ) : Prop :=
  InClass Dc (c.R j) (c.S j) (c.F Dc K h f j) ∧
    WBound Dc (c.R j) (c.S j) (c.F Dc K h f j) (ε j) ∧
    RealOn (Dom (a + b) Dc (c.R j) (c.S j)) (c.F Dc K h f j)

/-- Everything stage `i` delivers. -/
structure StepConc (Dc : Set (Fin (a + b) → ℂ)) (c : Sched) (K α₁ α₂ : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) (ε : ℕ → ℝ) (i : ℕ) : Prop where
  diff : DifferentiableOn ℂ (c.Φ Dc K h f i)
    (Dom (a + b) Dc (c.R i - 3 * c.ρ i / 2) (c.S i - 3 * c.σ i / 2))
  mapsTo : MapsTo (c.Φ Dc K h f i) (Dom (a + b) Dc (c.R i - 3 * c.ρ i / 2) (c.S i - 3 * c.σ i / 2))
    (Dom (a + b) Dc (c.R i - c.ρ i) (c.S i - c.σ i))
  inj : InjOn (c.Φ Dc K h f i) (Dom (a + b) Dc (c.R (i + 1)) (c.S (i + 1)))
  sympl : ∀ z ∈ Dom (a + b) Dc (c.R (i + 1)) (c.S (i + 1)), ∀ v w,
    symplFormC (fderiv ℂ (c.Φ Dc K h f i) z v) (fderiv ℂ (c.Φ Dc K h f i) z w) = symplFormC v w
  trans : ∀ k : Fin (a + b) → ℤ,
    ∀ z ∈ Dom (a + b) Dc (c.R i - 3 * c.ρ i / 2) (c.S i - 3 * c.σ i / 2),
      c.Φ Dc K h f i (z.1 + (fun j => (k j : ℂ)), z.2) =
        c.Φ Dc K h f i z + ((fun j => (k j : ℂ)), 0)
  disp : ∀ z ∈ Dom (a + b) Dc (c.R i - 3 * c.ρ i / 2) (c.S i - 3 * c.σ i / 2),
    ‖firstBlock (b := b) ((c.Φ Dc K h f i z).2 - z.2)‖ ≤
        1 * ε i / (exp 1 * (2 * π * α₁) * c.σ i) ∧
    ‖lastBlock (a := a) ((c.Φ Dc K h f i z).2 - z.2)‖ ≤
        1 * ε i / (exp 1 * (2 * π * α₂) * c.σ i) ∧
    ‖(c.Φ Dc K h f i z).1 - z.1‖ ≤ 1 * ε i / (2 * π * α₂ * c.ρ i)
  cls : InClass Dc (c.R (i + 1)) (c.S (i + 1)) (c.F Dc K h f (i + 1))
  bound : WBound Dc (c.R (i + 1)) (c.S (i + 1)) (c.F Dc K h f (i + 1)) (ε (i + 1))
  real_F : RealOn (Dom (a + b) Dc (c.R (i + 1)) (c.S (i + 1))) (c.F Dc K h f (i + 1))
  real_G : RealOn (Dom (a + b) Dc (c.R (i + 1)) (c.S (i + 1))) (c.G Dc K h f (i + 1))
  real_Φ : ∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ Dom (a + b) Dc (c.R (i + 1))
    (c.S (i + 1)) → c.Φ Dc K h f i (KAM.realInclusion₂ (a + b) x) ∈
      range (KAM.realInclusion₂ (a + b))
  ident : ∀ z ∈ Dom (a + b) Dc (c.R (i + 1)) (c.S (i + 1)),
    h (c.Φ Dc K h f i z).2 + c.G Dc K h f i (c.Φ Dc K h f i z) + c.F Dc K h f i (c.Φ Dc K h f i z) =
      h z.2 + c.G Dc K h f (i + 1) z + c.F Dc K h f (i + 1) z

section Stage

variable {Dc : Set (Fin (a + b) → ℂ)} {c : Sched} {K α₁ α₂ E : ℝ} {h : (Fin (a + b) → ℂ) → ℂ}
  {f : CHam (a + b)} {ε : ℕ → ℝ} {m : ℕ}

theorem twoDiv_mono {V V' : Set (Fin (a + b) → ℂ)} (hV : V' ⊆ V) {K α₁ α₂ q : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} (hd : TwoDiv V K α₁ α₂ q h) : TwoDiv V' K α₁ α₂ q h :=
  fun I hI => hd I (hV hI)

theorem setting_of_twoDiv {V : Set (Fin (a + b) → ℂ)} {K α₁ α₂ : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} (hd : TwoDiv V K α₁ α₂ 1 h) (hα : α₂ ≤ α₁) :
    DivisorBound V K {0} h (α₂ / 1) := by
  intro I hI k hk
  have hk0 : k ≠ 0 := fun e => hk.2 (by simp [e])
  have := hd I hI k hk0 hk.1
  split_ifs at this
  · exact this
  · exact le_trans (by linarith) this

theorem R_le_start (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) : c.R i ≤ c.r := by
  have := c.R_anti (i := 0) (j := i) (fun l hl => (hS.ρ_pos l (by omega)).le) (Nat.zero_le i)
  simpa [Sched.R] using this

theorem S_le_start (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) : c.S i ≤ c.s := by
  have := c.S_anti (i := 0) (j := i) (fun l hl => (hS.σ_pos l (by omega)).le) (Nat.zero_le i)
  simpa [Sched.S] using this

theorem R_pos (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) : 0 < c.R i := by
  have := hS.ρ_pos i hi
  have := hS.ρ_lt i hi
  linarith

theorem S_pos (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m) : 0 < c.S i := by
  have := hS.σ_pos i hi
  have := hS.σ_lt i hi
  linarith

theorem directHyp_stage (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m)
    (hinv : Inv Dc c K h f ε i) :
    DirectHyp Dc (c.R i) (c.S i) K α₂ 1 (ε i) {0} h (c.F Dc K h f i) :=
  { r_pos := R_pos hS hi
    s_pos := S_pos hS hi
    K_nonneg := hS.K_nonneg
    α_pos := hS.α₂_pos
    q_ge := le_rfl
    δ_nonneg := hS.ε_nonneg i (by omega)
    holo := hS.holo.mono (polyNbhd_mono (R_le_start hS hi))
    div := setting_of_twoDiv (twoDiv_mono (polyNbhd_mono (R_le_start hS hi)) hS.div) hS.α_order
    cls := hinv.1
    bound := hinv.2.1 }

theorem inv_zero (hS : IterSetup Dc c K α₁ α₂ h f ε m) : Inv Dc c K h f ε 0 :=
  ⟨hS.cls, hS.bound, hS.real_f⟩

theorem step_conc (hS : IterSetup Dc c K α₁ α₂ h f ε m) {i : ℕ} (hi : i ≤ m)
    (inv : ∀ j ≤ i, Inv Dc c K h f ε j) : StepConc Dc c K α₁ α₂ h f ε i := by
  have hH := directHyp_stage hS hi (inv i le_rfl)
  have hρ : 0 < c.ρ i ∧ 2 * c.ρ i < c.R i := ⟨hS.ρ_pos i hi, hS.ρ_lt i hi⟩
  have hσ : 0 < c.σ i ∧ 2 * c.σ i < c.S i := ⟨hS.σ_pos i hi, hS.σ_lt i hi⟩
  have hsmall := hS.small i hi
  have hRi : ∀ j : Fin i, c.R i ≤ c.R j := fun j =>
    c.R_anti (i := (j : ℕ)) (j := i) (fun l _ => (hS.ρ_pos l (by omega)).le) (le_of_lt j.2)
  have hSi : ∀ j : Fin i, c.S i ≤ c.S j := fun j =>
    c.S_anti (i := (j : ℕ)) (j := i) (fun l _ => (hS.σ_pos l (by omega)).le) (le_of_lt j.2)
  have hHj : ∀ j : Fin i, DirectHyp Dc (c.R j) (c.S j) K α₂ 1 (ε j) {0} h (c.F Dc K h f j) :=
    fun j => directHyp_stage hS (by have := j.2; omega) (inv j (le_of_lt j.2))
  have hg : ∀ j : Fin i, InClass Dc (c.R j) (c.S j) (homRes K {0} (c.F Dc K h f j)) ∧
      WBound Dc (c.R j) (c.S j) (homRes K {0} (c.F Dc K h f j)) (ε j) ∧
      c.R i ≤ c.R j ∧ c.S i ≤ c.S j := fun j =>
    ⟨(homRes_stage (hHj j)).1, (homRes_stage (hHj j)).2.1, hRi j, hSi j⟩
  have hdirect := direct_step (gj := fun j : Fin i => homRes K {0} (c.F Dc K h f j))
    (rj := fun j : Fin i => c.R j) (sj := fun j : Fin i => c.S j) (Mj := fun j : Fin i => ε j)
    hH hρ hσ hsmall hg
  have hsp := split (α₁ := α₁) hH hS.α_order
    (twoDiv_mono (polyNbhd_mono (R_le_start hS hi)) hS.div) hρ.1 hρ.2 hσ.1 hσ.2 hsmall
  have hI := iterHyp_two (gj := fun j : Fin i => homRes K {0} (c.F Dc K h f j))
    (rj := fun j : Fin i => c.R j) (sj := fun j : Fin i => c.S j) (Mj := fun j : Fin i => ε j)
    hH hρ hσ hsmall hg
  have ha := iterative_direct_a hI
  have hhr : RealOn (Dom (a + b) Dc (c.R i) (c.S i)) (fun w => h w.2) := fun x hx =>
    hS.real_h x (Dom_mono (R_le_start hS hi) (S_le_start hS hi) hx)
  have hgr : ∀ j : Fin i, RealOn (Dom (a + b) Dc (c.R j) (c.S j))
      (homRes K {0} (c.F Dc K h f j)) := fun j =>
    (homRes_stage (hHj j)).2.2
      (fun x hx => hS.real_h x (Dom_mono (R_le_start hS (by have := j.2; omega))
        (S_le_start hS (by have := j.2; omega)) hx)) (inv j (le_of_lt j.2)).2.2
  obtain ⟨d1, d2, d3, d4, d5, d6, -, d8⟩ := hdirect
  obtain ⟨rG, rF, rΦ⟩ := d8 (fun k hk => by rw [Set.mem_singleton_iff] at hk ⊢; rw [hk]; simp)
    hhr (inv i le_rfl).2.2 hgr
  have eF := Sched.F_succ c Dc K h f i
  have eG := Sched.G_succ c Dc K h f i
  have eGs := Sched.G_eq_sum c Dc K h f i
  refine ⟨d1, d2, d3, d4, ha.2.2.2.1, hsp.2.2, ?_, ?_, ?_, ?_, rΦ, fun z _ => ?_⟩
  · rw [eF, eGs]; exact d5
  · rw [eF, eGs]; exact d6.mono le_rfl le_rfl (hS.step i hi)
  · rw [eF, eGs]; exact rF
  · rw [eG, eGs]; exact rG
  · rw [eF, eG]
    simp only [iterF, iterG, Sched.Φ]
    ring

theorem inv_all (hS : IterSetup Dc c K α₁ α₂ h f ε m) :
    ∀ i ≤ m + 1, ∀ j ≤ i, Inv Dc c K h f ε j := by
  intro i
  induction i with
  | zero =>
    intro _ j hj
    obtain rfl : j = 0 := by omega
    exact inv_zero hS
  | succ i ih =>
    intro hi j hj
    rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · exact ih (by omega) j (by omega)
    · obtain rfl : j = i + 1 := by omega
      have hsc := step_conc hS (by omega) (ih (by omega))
      exact ⟨hsc.cls, hsc.bound, hsc.real_F⟩

end Stage

end KAM.Planetary

end
