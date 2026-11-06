/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.BracketList
public import KAM.EffectiveStability.Tube.Check.Bracket
public import KAM.EffectiveStability.Tube.Witness.BinomialProd

/-!
# The bound of the reduced bracket on the tube (T2-CONF, N9 (B))

Let `f = Σ_{i ∈ Fl} u^{μ_i} g_i` (a list observable) and let `h̃ = Σ_{e ∈ Hl} u^{ν_e} h_e + R` with
true coefficients `h_e`, a remainder `R`, and models `k_e` with `C¹` certificates
`C1Close h_e k_e e₀_e e₁_e`. On the box `|u_l| ≤ r` (`reducedBracket_bound`):

  `|{f, h̃}(u, φ)| ≤ KEPT + DROP + ERR + TAIL`,

* `KEPT = Σ_{p ∈ truncSet L} r^{|p|} G_p`, where `G_p` bounds, for every `φ`, the grouped value
  `|Σ_{b ∈ bterms, mon b = p} coef b · val b φ|` of the model bracket (N7's kernel bounds);
* `DROP = Σ_{b ∈ bterms, |mon b| > L} |coef b| r^{|mon b|} V_b`, with `|val b φ| ≤ V_b`;
* `ERR = Σ_a [Fd_a Σ_e r^{|ν_e|} e₁_e +
    Fp_a Σ_e (ν_e(a) r^{|ν_e - e_a|} + ν_e(2) r^{|ν_e - e_2|}) e₀_e]`;
* `TAIL = Σ_a [Fd_a Rp + Fp_a (Ru_a + Ru_2)]`,

where `Fd_a ≥ |(∂_{u_a} - ∂_{u_2}) f|`, `Fp_a ≥ |∂_{φ_a} f|` at `(u, φ)`, and `Ru_l`, `Rp` bound the
slice partials of `R` at `(u, φ)` (N5a's `hRem_tube`). Joint differentiability of `R` at `(u, φ)` is
a hypothesis (slice regularity does not suffice, N3 audit); the models and `f` are jointly smooth.

Ingredients: `reducedBracket` is additive in its second argument (`reducedBracket_add`), bounded by
the partials (`abs_reducedBracket_le`); the model part is N9 (A) `reducedBracket_listObs`, split by
monomial over `truncSet` (`list_sum_split_truncSet`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

/-! ### The kept/dropped split -/

theorem mem_truncSet_iff {L : ℕ} {p : Fin 3 → ℕ} : p ∈ truncSet (Fin 3) L ↔ mdeg p ≤ L := by
  simp only [truncSet, mem_filter, Fintype.mem_piFinset, mem_range, mdeg]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (mem_univ j)
  omega

/-- Split a list sum by the fibres of `m` over a finset `S`, and the rest. -/
theorem list_sum_split_fiber {β γ : Type*} [DecidableEq γ] (l : List β) (m : β → γ)
    (S : Finset γ) (F : β → ℝ) :
    (l.map F).sum = ∑ p ∈ S, ((l.filter fun x => decide (m x = p)).map F).sum +
      ((l.filter fun x => decide (m x ∉ S)).map F).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hx : m x ∈ S
    · have e : ∀ p ∈ S, ((if decide (m x = p) = true then x :: l.filter (fun x => decide (m x = p))
          else l.filter fun x => decide (m x = p)).map F).sum =
          (if m x = p then F x else 0) + ((l.filter fun x => decide (m x = p)).map F).sum := by
        intro p _
        by_cases h : m x = p <;> simp [h]
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq S (m x) (fun _ => F x)]
      simp only [hx, ite_true, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rw [ih]; ring
    · have e : ∀ p ∈ S, ((if decide (m x = p) = true then x :: l.filter (fun x => decide (m x = p))
          else l.filter fun x => decide (m x = p)).map F).sum =
          ((l.filter fun x => decide (m x = p)).map F).sum := by
        intro p hp
        have : m x ≠ p := fun h => hx (h ▸ hp)
        simp [this]
      rw [Finset.sum_congr rfl e]
      simp only [hx, not_false_eq_true, decide_true, ite_true, List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- The split over `truncSet L`: kept monomials `|p| ≤ L` and the dropped ones `|p| > L`. -/
theorem list_sum_split_truncSet {β : Type*} (l : List β) (m : β → Fin 3 → ℕ) (L : ℕ)
    (F : β → ℝ) :
    (l.map F).sum = ∑ p ∈ truncSet (Fin 3) L, ((l.filter fun x => decide (m x = p)).map F).sum +
      ((l.filter fun x => decide (L < mdeg (m x))).map F).sum := by
  have hf : l.filter (fun x => decide (m x ∉ truncSet (Fin 3) L)) =
      l.filter (fun x => decide (L < mdeg (m x))) :=
    List.filter_congr fun x _ => by simp only [mem_truncSet_iff, not_le]
  rw [list_sum_split_fiber l m (truncSet (Fin 3) L) F, hf]

/-! ### Additivity and the generic bound -/

/-- `reducedBracket` is additive in its second argument. -/
theorem reducedBracket_add {f h₁ h₂ : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {p : (Fin 3 → ℝ) × (Fin 2 → ℝ)} (h1 : DifferentiableAt ℝ h₁ p)
    (h2 : DifferentiableAt ℝ h₂ p) :
    reducedBracket f (fun q => h₁ q + h₂ q) p = reducedBracket f h₁ p + reducedBracket f h₂ p := by
  simp only [reducedBracket, fderiv_fun_add h1 h2, _root_.add_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The generic bound** `|{f, h}| ≤ Σ_a (Fd_a Hp_a + Fp_a (Hu_a + Hu_2))` from bounds of the
partials at `p`. -/
theorem abs_reducedBracket_le {f h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {p : (Fin 3 → ℝ) × (Fin 2 → ℝ)} {Fd Fp Hp : Fin 2 → ℝ} {Hu : Fin 3 → ℝ}
    (hFd : ∀ a : Fin 2, |fderiv ℝ f p (Pi.single a.castSucc 1, 0) -
      fderiv ℝ f p (Pi.single 2 1, 0)| ≤ Fd a)
    (hFp : ∀ a : Fin 2, |fderiv ℝ f p (0, Pi.single a 1)| ≤ Fp a)
    (hHp : ∀ a : Fin 2, |fderiv ℝ h p (0, Pi.single a 1)| ≤ Hp a)
    (hHu : ∀ l : Fin 3, |fderiv ℝ h p (Pi.single l 1, 0)| ≤ Hu l) :
    |reducedBracket f h p| ≤ ∑ a : Fin 2, (Fd a * Hp a + Fp a * (Hu a.castSucc + Hu 2)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hFd0 : 0 ≤ Fd a := (abs_nonneg _).trans (hFd a)
  have hFp0 : 0 ≤ Fp a := (abs_nonneg _).trans (hFp a)
  have hD : |fderiv ℝ h p (Pi.single a.castSucc 1, 0) - fderiv ℝ h p (Pi.single 2 1, 0)| ≤
      Hu a.castSucc + Hu 2 := (abs_sub _ _).trans (add_le_add (hHu _) (hHu _))
  refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul (hFd a) (hHp a) (abs_nonneg _) hFd0
  · exact mul_le_mul (hFp a) hD (abs_nonneg _) hFp0

/-! ### The four budgets -/

/-- `KEPT = Σ_{p ∈ truncSet L} r^{|p|} G_p`. -/
def bracketKept (L : ℕ) (r : ℝ) (G : (Fin 3 → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ truncSet (Fin 3) L, r ^ mdeg p * G p

/-- `DROP = Σ_{b, |mon b| > L} |coef b| r^{|mon b|} V_b`. -/
def bracketDrop {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ) (Hl : List κ)
    (ν : κ → Fin 3 → ℕ) (L : ℕ) (r : ℝ) (V : BT ι κ → ℝ) : ℝ :=
  (((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon μ ν))).map fun b =>
    |(b.coef μ ν : ℝ)| * r ^ mdeg (b.mon μ ν) * V b).sum

/-- `ERR = Σ_a [Fd_a Σ_e r^{|ν_e|} e₁_e +
Fp_a Σ_e (ν_e(a) r^{|ν_e - e_a|} + ν_e(2) r^{|ν_e - e_2|}) e₀_e]`. -/
def bracketErr {κ : Type*} (Hl : List κ) (ν : κ → Fin 3 → ℕ) (r : ℝ) (e₀ e₁ : κ → ℝ)
    (Fd Fp : Fin 2 → ℝ) : ℝ :=
  ∑ a : Fin 2, (Fd a * (Hl.map fun e => r ^ mdeg (ν e) * e₁ e).sum +
    Fp a * ((Hl.map fun e => (ν e a.castSucc : ℝ) * r ^ mdeg (ν e - Pi.single a.castSucc 1) *
        e₀ e).sum +
      (Hl.map fun e => (ν e 2 : ℝ) * r ^ mdeg (ν e - Pi.single 2 1) * e₀ e).sum))

/-- `TAIL = Σ_a [Fd_a Rp + Fp_a (Ru_a + Ru_2)]`. -/
def bracketTail (Fd Fp : Fin 2 → ℝ) (Ru : Fin 3 → ℝ) (Rp : ℝ) : ℝ :=
  ∑ a : Fin 2, (Fd a * Rp + Fp a * (Ru a.castSucc + Ru 2))

/-! ### The model part -/

/-- The model bracket is at most `KEPT + DROP` on the box. -/
theorem abs_reducedBracket_listObs_le {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ) (k : κ → (Fin 2 → ℝ) → ℝ)
    (hg : ∀ i ∈ Fl, Differentiable ℝ (g i)) (hk : ∀ e ∈ Hl, Differentiable ℝ (k e))
    {L : ℕ} {r : ℝ} {G : (Fin 3 → ℕ) → ℝ} {V : BT ι κ → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L, ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ ν = p)).map (fun b => (b.coef μ ν : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    (hV : ∀ b ∈ bterms Fl Hl, ∀ φ, |b.val g k φ| ≤ V b)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ) :
    |reducedBracket (listObs Fl μ g) (listObs Hl ν k) (u, φ)| ≤
      bracketKept L r G + bracketDrop Fl μ Hl ν L r V := by
  have hbox : InBox r u := hu
  rw [reducedBracket_listObs Fl μ g Hl ν k hg hk u φ,
    list_sum_split_truncSet _ (fun b => b.mon μ ν) L]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have e : (((bterms Fl Hl).filter fun b => decide (b.mon μ ν = p)).map fun b =>
        (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ).sum =
        umon p u * (((bterms Fl Hl).filter fun b => decide (b.mon μ ν = p)).map fun b =>
          (b.coef μ ν : ℝ) * b.val g k φ).sum := by
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
      rw [(by simpa using (List.mem_filter.1 hb).2 : b.mon μ ν = p)]
      ring
    rw [e, abs_mul]
    exact mul_le_mul (abs_umon_le hbox p) (hG p hp φ) (abs_nonneg _) (by
      have := hbox.nonneg; positivity)
  · refine abs_list_sum_le _ _ _ fun b hb => ?_
    rw [abs_mul, abs_mul]
    have hb' := (List.mem_filter.1 hb).1
    exact mul_le_mul (mul_le_mul_of_nonneg_left (abs_umon_le hbox _) (abs_nonneg _))
      (hV b hb' φ) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (by have := hbox.nonneg; positivity))

/-- The model bracket is at most `KEPT + D`, given a bound `D` of the whole dropped part at
`(u, φ)` (e.g. a kernel-checked rational). -/
theorem abs_reducedBracket_listObs_le_of_drop {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ) (k : κ → (Fin 2 → ℝ) → ℝ)
    (hg : ∀ i ∈ Fl, Differentiable ℝ (g i)) (hk : ∀ e ∈ Hl, Differentiable ℝ (k e))
    {L : ℕ} {r D : ℝ} {G : (Fin 3 → ℕ) → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L, ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ ν = p)).map (fun b => (b.coef μ ν : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ)
    (hDrop : |((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon μ ν))).map
      (fun b => (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ) |>.sum| ≤ D) :
    |reducedBracket (listObs Fl μ g) (listObs Hl ν k) (u, φ)| ≤ bracketKept L r G + D := by
  have hbox : InBox r u := hu
  rw [reducedBracket_listObs Fl μ g Hl ν k hg hk u φ,
    list_sum_split_truncSet _ (fun b => b.mon μ ν) L]
  refine (abs_add_le _ _).trans (add_le_add ?_ hDrop)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have e : (((bterms Fl Hl).filter fun b => decide (b.mon μ ν = p)).map fun b =>
      (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ).sum =
      umon p u * (((bterms Fl Hl).filter fun b => decide (b.mon μ ν = p)).map fun b =>
        (b.coef μ ν : ℝ) * b.val g k φ).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
    rw [(by simpa using (List.mem_filter.1 hb).2 : b.mon μ ν = p)]
    ring
  rw [e, abs_mul]
  exact mul_le_mul (abs_umon_le hbox p) (hG p hp φ) (abs_nonneg _) (by
    have := hbox.nonneg; positivity)

/-! ### The main bound -/

theorem listObs_add_sub {κ : Type*} (Hl : List κ) (ν : κ → Fin 3 → ℕ)
    (hc k : κ → (Fin 2 → ℝ) → ℝ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    listObs Hl ν hc p = listObs Hl ν k p + listObs Hl ν (fun e φ => hc e φ - k e φ) p := by
  unfold listObs
  rw [list_sum_add]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  ring

/-- **(B) The bound of the reduced bracket on the tube.** See the module docstring. -/
theorem reducedBracket_bound {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ)
    (k hc : κ → (Fin 2 → ℝ) → ℝ) (hg : ∀ i ∈ Fl, Differentiable ℝ (g i))
    {e₀ e₁ : κ → ℝ} (hcert : ∀ e ∈ Hl, C1Close (hc e) (k e) (e₀ e) (e₁ e))
    {h R : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} (hdec : ∀ p, h p = listObs Hl ν hc p + R p)
    {L : ℕ} {r : ℝ} {G : (Fin 3 → ℕ) → ℝ} {V : BT ι κ → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L, ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ ν = p)).map (fun b => (b.coef μ ν : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    (hV : ∀ b ∈ bterms Fl Hl, ∀ φ, |b.val g k φ| ≤ V b)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ)
    {Fd Fp : Fin 2 → ℝ}
    (hFd : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single a.castSucc 1, 0) -
      fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single 2 1, 0)| ≤ Fd a)
    (hFp : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (0, Pi.single a 1)| ≤ Fp a)
    {Ru : Fin 3 → ℝ} {Rp : ℝ} (hRd : DifferentiableAt ℝ R (u, φ))
    (hRu : ∀ l, |fderiv ℝ (fun v => R (v, φ)) u (Pi.single l 1)| ≤ Ru l)
    (hRp : ∀ a, |fderiv ℝ (fun ψ => R (u, ψ)) φ (Pi.single a 1)| ≤ Rp) :
    |reducedBracket (listObs Fl μ g) h (u, φ)| ≤
      bracketKept L r G + bracketDrop Fl μ Hl ν L r V + bracketErr Hl ν r e₀ e₁ Fd Fp +
        bracketTail Fd Fp Ru Rp := by
  have hbox : InBox r u := hu
  have hk : ∀ e ∈ Hl, Differentiable ℝ (k e) := fun e he => (hcert e he).differentiable_right
  set d : κ → (Fin 2 → ℝ) → ℝ := fun e φ => hc e φ - k e φ with hd
  have hdd : ∀ e ∈ Hl, Differentiable ℝ (d e) := fun e he =>
    (hcert e he).differentiable_left.sub (hcert e he).differentiable_right
  -- the decomposition as functions
  have hfun : h = fun q => (listObs Hl ν k q + listObs Hl ν d q) + R q := by
    funext q; rw [hdec q, listObs_add_sub Hl ν hc k q]
  have hM := differentiable_listObs Hl ν hk (u, φ)
  have hD := differentiable_listObs Hl ν hdd (u, φ)
  rw [hfun, reducedBracket_add (h₁ := fun q => listObs Hl ν k q + listObs Hl ν d q) (h₂ := R)
      (hM.add hD) hRd,
    reducedBracket_add (h₁ := listObs Hl ν k) (h₂ := listObs Hl ν d) hM hD]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact abs_reducedBracket_listObs_le Fl μ g Hl ν k hg hk hG hV hu φ
  · -- the certificate error
    refine (abs_reducedBracket_le (Hp := fun _ => (Hl.map fun e => r ^ mdeg (ν e) * e₁ e).sum)
      (Hu := fun l => (Hl.map fun e => (ν e l : ℝ) * r ^ mdeg (ν e - Pi.single l 1) * e₀ e).sum)
      hFd hFp (fun a => ?_) (fun l => ?_)).trans (le_of_eq ?_)
    · exact abs_fderiv_listObs_φ_le Hl ν hdd (G' := e₁)
        (fun e he φ' => by
          rw [show fderiv ℝ (d e) φ' (Pi.single a 1) =
              pderiv (hc e) φ' a - pderiv (k e) φ' a from
            C1Close.pderiv_sub (hcert e he).differentiable_left
              (hcert e he).differentiable_right φ' a]
          exact (hcert e he).abs_pderiv_sub_le φ' a) hu φ
    · exact abs_fderiv_listObs_u_le Hl ν hdd (G := e₀)
        (fun e he φ' => (hcert e he).abs_sub_le φ') hu φ l
    · simp only [bracketErr]
  · -- the remainder
    refine abs_reducedBracket_le hFd hFp (Hp := fun _ => Rp) (fun a => ?_) (fun l => ?_)
    · rw [fderiv_apply_single_snd_eq_pderiv hRd]; exact hRp a
    · rw [fderiv_apply_single_fst_eq_upd hRd]; exact hRu l

/-- **(B), with a direct bound `D` of the dropped part** (N7's kernel-checked `sjsu_drop_bound`)
in place of the term bounds `V` and `bracketDrop`. -/
theorem reducedBracket_bound_of_drop {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ)
    (k hc : κ → (Fin 2 → ℝ) → ℝ) (hg : ∀ i ∈ Fl, Differentiable ℝ (g i))
    {e₀ e₁ : κ → ℝ} (hcert : ∀ e ∈ Hl, C1Close (hc e) (k e) (e₀ e) (e₁ e))
    {h R : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} (hdec : ∀ p, h p = listObs Hl ν hc p + R p)
    {L : ℕ} {r D : ℝ} {G : (Fin 3 → ℕ) → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L, ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ ν = p)).map (fun b => (b.coef μ ν : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ)
    (hDrop : |((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon μ ν))).map
      (fun b => (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ) |>.sum| ≤ D)
    {Fd Fp : Fin 2 → ℝ}
    (hFd : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single a.castSucc 1, 0) -
      fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single 2 1, 0)| ≤ Fd a)
    (hFp : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (0, Pi.single a 1)| ≤ Fp a)
    {Ru : Fin 3 → ℝ} {Rp : ℝ} (hRd : DifferentiableAt ℝ R (u, φ))
    (hRu : ∀ l, |fderiv ℝ (fun v => R (v, φ)) u (Pi.single l 1)| ≤ Ru l)
    (hRp : ∀ a, |fderiv ℝ (fun ψ => R (u, ψ)) φ (Pi.single a 1)| ≤ Rp) :
    |reducedBracket (listObs Fl μ g) h (u, φ)| ≤
      bracketKept L r G + D + bracketErr Hl ν r e₀ e₁ Fd Fp +
        bracketTail Fd Fp Ru Rp := by
  have hbox : InBox r u := hu
  have hk : ∀ e ∈ Hl, Differentiable ℝ (k e) := fun e he => (hcert e he).differentiable_right
  set d : κ → (Fin 2 → ℝ) → ℝ := fun e φ => hc e φ - k e φ with hd
  have hdd : ∀ e ∈ Hl, Differentiable ℝ (d e) := fun e he =>
    (hcert e he).differentiable_left.sub (hcert e he).differentiable_right
  -- the decomposition as functions
  have hfun : h = fun q => (listObs Hl ν k q + listObs Hl ν d q) + R q := by
    funext q; rw [hdec q, listObs_add_sub Hl ν hc k q]
  have hM := differentiable_listObs Hl ν hk (u, φ)
  have hD := differentiable_listObs Hl ν hdd (u, φ)
  rw [hfun, reducedBracket_add (h₁ := fun q => listObs Hl ν k q + listObs Hl ν d q) (h₂ := R)
      (hM.add hD) hRd,
    reducedBracket_add (h₁ := listObs Hl ν k) (h₂ := listObs Hl ν d) hM hD]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact abs_reducedBracket_listObs_le_of_drop Fl μ g Hl ν k hg hk hG hu φ hDrop
  · -- the certificate error
    refine (abs_reducedBracket_le (Hp := fun _ => (Hl.map fun e => r ^ mdeg (ν e) * e₁ e).sum)
      (Hu := fun l => (Hl.map fun e => (ν e l : ℝ) * r ^ mdeg (ν e - Pi.single l 1) * e₀ e).sum)
      hFd hFp (fun a => ?_) (fun l => ?_)).trans (le_of_eq ?_)
    · exact abs_fderiv_listObs_φ_le Hl ν hdd (G' := e₁)
        (fun e he φ' => by
          rw [show fderiv ℝ (d e) φ' (Pi.single a 1) =
              pderiv (hc e) φ' a - pderiv (k e) φ' a from
            C1Close.pderiv_sub (hcert e he).differentiable_left
              (hcert e he).differentiable_right φ' a]
          exact (hcert e he).abs_pderiv_sub_le φ' a) hu φ
    · exact abs_fderiv_listObs_u_le Hl ν hdd (G := e₀)
        (fun e he φ' => (hcert e he).abs_sub_le φ') hu φ l
    · simp only [bracketErr]
  · -- the remainder
    refine abs_reducedBracket_le hFd hFp (Hp := fun _ => Rp) (fun a => ?_) (fun l => ?_)
    · rw [fderiv_apply_single_snd_eq_pderiv hRd]; exact hRp a
    · rw [fderiv_apply_single_fst_eq_upd hRd]; exact hRu l

end KAM.EffectiveStability.Tube

end
