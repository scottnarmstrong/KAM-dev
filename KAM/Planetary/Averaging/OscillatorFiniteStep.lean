/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteSched

/-!
# P Part 2: one stage of the oscillator finite averaging iteration (`stepP:p2:oa-iter`)

`ostep_conc` proves `OStepConc` for stage `i` by applying the complete step `osc_iter` on the
stage domain, with the earlier zero-mode increments as the decomposition `g = ∑ⱼ gⱼ`; it uses the
invariant `OInv` of stage `i` and the stage data of the earlier stages, and `oinv_all` propagates
both. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Stage

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {c : OSched} {K α : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)} {ε : ℕ → ℝ} {M : ℕ}

theorem actionNbhd_sub {r r' : ℝ} (hr : r ≤ r') : KAM.actionNbhd D r ⊆ KAM.actionNbhd D r' :=
  fun _ ⟨J, hJ, hlt⟩ => ⟨J, hJ, hlt.trans_le hr⟩

theorem oinv_zero (hS : OIter D c K α h f ε M) : OInv D c K h f ε 0 :=
  ⟨hS.cls, hS.bound, hS.real_f, by rw [OSched.G_zero]; exact oscClass.zero,
    fun x _ => by simp [OSched.G_zero]⟩

theorem ostep_conc (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M)
    (inv : OInv D c K h f ε i) (hsc : ∀ j < i, OStepConc D c K α h f ε j) :
    OStepConc D c K α h f ε i := by
  obtain ⟨hρ, hρl, hρp, hρpl, hρq, hρql, hσ, hσl⟩ := hS.widths i hi
  obtain ⟨hf_cls, hf_bd, hf_real, hG_cls, hG_real⟩ := inv
  have hanti := hS.R_anti (Nat.zero_le i) (by omega)
  have hh : DifferentiableOn ℂ h (KAM.actionNbhd D (c.x.R i)) :=
    hS.holo.mono (actionNbhd_sub hanti.1)
  have hdiv : DivisorBound (KAM.actionNbhd D (c.x.R i)) K {0} h α :=
    fun I hI k hk => hS.div I (actionNbhd_sub hanti.1 hI) k hk
  have hg : ∀ j : Fin i, oscClass D (c.x.R j) (c.p.R j) (c.q.R j) (c.x.S j) (c.inc D K h f j) ∧
      oscBound D (c.x.R j) (c.p.R j) (c.q.R j) (c.x.S j) (c.inc D K h f j) (ε j) ∧
      c.x.R i ≤ c.x.R j ∧ c.p.R i ≤ c.p.R j ∧ c.q.R i ≤ c.q.R j ∧ c.x.S i ≤ c.x.S j :=
    fun j => ⟨(hsc j j.2).inc_cls, (hsc j j.2).inc_bound,
      (hS.R_anti (le_of_lt j.2) (by omega))⟩
  have hGa : ∀ w, ∑ j : Fin i, c.inc D K h f j w = c.G D K h f i w := fun w => by rw [OSched.G_eq_sum]
  have H := osc_iter (n := n) (m := m) (J := i) (D := D) (r := c.x.R i) (rp := c.p.R i)
    (rq := c.q.R i) (S := c.x.S i) (ρ := c.x.ρ i) (ρp := c.p.ρ i) (ρq := c.q.ρ i)
    (σ := c.x.σ i) (K := K) (α := α) (δ := ε i) (h := h) (f := c.F D K h f i)
    (gj := fun j : Fin i => c.inc D K h f j) (rj := fun j : Fin i => c.x.R j)
    (rpj := fun j : Fin i => c.p.R j) (rqj := fun j : Fin i => c.q.R j)
    (Sj := fun j : Fin i => c.x.S j) (Mj := fun j : Fin i => ε j)
    hS.n_pos hS.m_pos hS.α_pos hS.K_nonneg ⟨hρ, hρl, hρp, hρpl, hρq, hρql, hσ, hσl⟩ hh hdiv
    hf_cls hf_bd (hS.ε_nonneg i (by omega)) (hS.small i hi) hg
  dsimp only at H
  obtain ⟨-, -, a3, a4, a5, a6, -, a8, a9, a10, -, -, a13, a14, a15, a16, a17⟩ := H
  simp only [hGa] at a8 a9 a10 a14 a15 a17
  have hm := hS.U_succ_subset hi
  have hbig := hS.U_sub_big hi
  have hgp_real := (a17 (fun x hx => hS.real_h x (hS.U_sub_start (by omega) hx))
    hG_real hf_real)
  have e : c.inc D K h f i = fun z => (c.G D K h f i z +
      coeff (oscFunction (c.F D K h f i)) (oscPack z).2 0) - c.G D K h f i z := by
    funext z; simp [OSched.inc]
  refine ⟨a3, a4, a5, a13, fun k z hz => a6 z hz k, a16, a14,
    a15.mono_gen le_rfl le_rfl le_rfl le_rfl (hS.step i hi), hgp_real.2.2.1, a8,
    fun x hx => hgp_real.2.1 x (hm hx), ?_, ?_, fun x hx => hgp_real.2.2.2 x (hbig hx), a10⟩
  · rw [e]; exact a8.sub hG_cls
  · rw [e]; exact a9

theorem oinv_succ (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M)
    (hsc : OStepConc D c K α h f ε i) : OInv D c K h f ε (i + 1) := by
  obtain ⟨a, b, d, e⟩ := hS.R_anti (Nat.le_succ i) (by omega)
  exact ⟨hsc.cls, hsc.bound, hsc.real_F, hsc.cls_G.mono a b d e, hsc.real_G⟩

theorem oinv_all (hS : OIter D c K α h f ε M) :
    ∀ i ≤ M + 1, OInv D c K h f ε i ∧ ∀ j < i, OStepConc D c K α h f ε j := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨oinv_zero hS, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i ih =>
    intro hi
    obtain ⟨hinv, hsc⟩ := ih (by omega)
    have hst := ostep_conc hS (by omega) hinv hsc
    refine ⟨oinv_succ hS (by omega) hst, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · exact hsc j hlt
    · exact hst

theorem OIter.stage (hS : OIter D c K α h f ε M) {i : ℕ} (hi : i ≤ M) :
    OStepConc D c K α h f ε i := (oinv_all hS (i + 1) (by omega)).2 i (Nat.lt_succ_self i)

end Stage

end KAM.Planetary

end
