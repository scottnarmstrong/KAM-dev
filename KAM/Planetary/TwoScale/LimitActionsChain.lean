/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Iteration

/-!
# Two-scale KAM: the composed action maps (`bpP:p3:limit-actions`, well-posedness and steps)

The private conditional interface of the local obligation `limit_actions` (design package P23-17).
`ActionSteps` collects exactly the outputs of `iterative` (P23-16) that concern the action maps
`ĩ_j`; the real iterate chain `actionChain` is `ǐ_j = ĩ_j ∘ ⋯ ∘ ĩ_1` on real points. Here: the
chain stays in the stage domains (`stepP:p3:la-wp`), consecutive differences are controlled
blockwise by the step bounds (first part of `stepP:p3:la-tele`), the frequency identity
(`bpP:p3:limit-actions` (iv)) and the Lipschitz recursion of `stepP:p3:la-lip`.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The outputs of `iterative` concerning the action maps `ĩ_j`, on the shared stage witnesses. -/
structure ActionSteps {a b : ℕ} (sbar : ℝ) (p : ScaleData)
    (h : (Fin (a + b) → ℂ) → ℂ)
    (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
    (fs : ℕ → CHam (a + b)) (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)) : Prop where
  hs_zero : hs 0 = h
  hyp : ∀ j, KamHyp (Ds j) sbar (seq p j) (hs j) (fs j)
  step : ∀ j, ∀ I ∈ KAM.actionNbhd (Ds j) (rhoHat (seq p j) / 16),
    freq (hs (j + 1)) (is (j + 1) I) = freq (hs j) I ∧
    ‖firstBlock (b := b) (is (j + 1) I - I)‖ ≤
      10 * (p.Mbar₁ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) (is (j + 1) I - I)‖ ≤
      10 * (p.Mbar₂ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j)
  lip : ∀ j, ∀ I ∈ Ds j, ∀ J ∈ Ds j,
    ‖(is (j + 1) (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
      (is (j + 1) (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
        640 * (a + b) * eHat (seq p j) * ‖I - J‖
  Ds_succ : ∀ j, Ds (j + 1) =
    (fun I => fun k => (is (j + 1) (KAM.realInclusion (a + b) I) k).re) '' Ds j
  maps : ∀ j, MapsTo (is (j + 1)) (realBase (Ds j)) (realBase (Ds (j + 1)))
  eHat_sq : ∀ j, eHat (seq p (j + 1)) < eHat (seq p j) ^ 2
  rho_hi : ∀ j, rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16

/-- `ǐ_j = ĩ_j ∘ ⋯ ∘ ĩ_1`, read on real points. -/
def actionChain {N : ℕ} (is : ℕ → (Fin N → ℂ) → (Fin N → ℂ)) : ℕ → (Fin N → ℝ) → (Fin N → ℝ)
  | 0 => id
  | j + 1 => fun I => fun k => (is (j + 1) (KAM.realInclusion N (actionChain is j I)) k).re

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData} {h : (Fin (a + b) → ℂ) → ℂ}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}

namespace ActionSteps

theorem chain_mem (S : ActionSteps sbar p h Ds hs fs is) {I : Fin (a + b) → ℝ} (hI : I ∈ Ds 0)
    (j : ℕ) : actionChain is j I ∈ Ds j := by
  induction j with
  | zero => exact hI
  | succ j ih => rw [S.Ds_succ j]; exact ⟨_, ih, rfl⟩

/-- The real chain is the real part of the complex one: `ι ǐ_{j+1} = ĩ_{j+1} ι ǐ_j`. -/
theorem incl_chain_succ (S : ActionSteps sbar p h Ds hs fs is) {I : Fin (a + b) → ℝ}
    (hI : I ∈ Ds 0) (j : ℕ) :
    KAM.realInclusion (a + b) (actionChain is (j + 1) I) =
      is (j + 1) (KAM.realInclusion (a + b) (actionChain is j I)) := by
  obtain ⟨y', -, hy'⟩ := S.maps j ⟨_, S.chain_mem hI j, rfl⟩
  have : actionChain is (j + 1) I = y' := by
    funext k
    have := congrFun hy' k
    simp only [KAM.realInclusion_apply] at this
    show (is (j + 1) (KAM.realInclusion (a + b) (actionChain is j I)) k).re = y' k
    rw [← this]; simp
  rw [this]; exact hy'

theorem norm_first_incl (v : Fin (a + b) → ℝ) :
    ‖firstBlock (b := b) (KAM.realInclusion (a + b) v)‖ = ‖firstBlock (b := b) v‖ := by
  have : firstBlock (b := b) (KAM.realInclusion (a + b) v) =
      KAM.realInclusion a (firstBlock (b := b) v) := rfl
  rw [this, KAM.norm_realInclusion]

theorem norm_last_incl (v : Fin (a + b) → ℝ) :
    ‖lastBlock (a := a) (KAM.realInclusion (a + b) v)‖ = ‖lastBlock (a := a) v‖ := by
  have : lastBlock (a := a) (KAM.realInclusion (a + b) v) =
      KAM.realInclusion b (lastBlock (a := a) v) := rfl
  rw [this, KAM.norm_realInclusion]

/-- One step of the chain, blockwise. -/
theorem chain_step (S : ActionSteps sbar p h Ds hs fs is) {I : Fin (a + b) → ℝ}
    (hI : I ∈ Ds 0) (j : ℕ) :
    ‖firstBlock (b := b) (actionChain is (j + 1) I - actionChain is j I)‖ ≤
      10 * (p.Mbar₁ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) (actionChain is (j + 1) I - actionChain is j I)‖ ≤
      10 * (p.Mbar₂ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j) := by
  have hR := (S.hyp j).R_pos
  have hmem : KAM.realInclusion (a + b) (actionChain is j I) ∈
      KAM.actionNbhd (Ds j) (rhoHat (seq p j) / 16) :=
    ⟨_, S.chain_mem hI j, by
      change ‖KAM.realInclusion (a + b) _ - KAM.realInclusion (a + b) _‖ < _
      rw [sub_self, norm_zero]; positivity⟩
  obtain ⟨-, h1, h2⟩ := S.step j _ hmem
  rw [← S.incl_chain_succ hI j] at h1 h2
  rw [← norm_first_incl, ← norm_last_incl]
  refine ⟨?_, ?_⟩
  · convert h1 using 2; simp [map_sub]
  · convert h2 using 2; simp [map_sub]

/-- The frequency identity of `bpP:p3:limit-actions` (iv). -/
theorem chain_freq (S : ActionSteps sbar p h Ds hs fs is) {I : Fin (a + b) → ℝ}
    (hI : I ∈ Ds 0) (j : ℕ) : realFreq (hs j) (actionChain is j I) = realFreq h I := by
  induction j with
  | zero => simp [actionChain, S.hs_zero]
  | succ j ih =>
    have hR := (S.hyp j).R_pos
    have hmem : KAM.realInclusion (a + b) (actionChain is j I) ∈
        KAM.actionNbhd (Ds j) (rhoHat (seq p j) / 16) :=
      ⟨_, S.chain_mem hI j, by
      change ‖KAM.realInclusion (a + b) _ - KAM.realInclusion (a + b) _‖ < _
      rw [sub_self, norm_zero]; positivity⟩
    have e := (S.step j _ hmem).1
    rw [← ih]
    unfold realFreq
    rw [S.incl_chain_succ hI j, e]

end ActionSteps

end KAM.Planetary

end
