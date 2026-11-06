/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Obs.Sparse

/-!
# Kernel checks of a literal observable (T2-CONF, N8)

A literal observable is a list `L` of `(u-monomial, sparse model)` pairs:
`f(u, φ) = Σ_{(t, d) ∈ L} u^t · d.eval(φ)` (`litObs`). On the box `|u| ≤ ρ`:

* `obsFuOK` ⇒ `|∂_{u_l} f| ≤ FuMax_l` (`obsFuOK_sound`);
* `obsPhiOK` ⇒ `|∂_{φ_b} f| ≤ FphiMax_b` (`obsPhiOK_sound`);
* `obsFaceOK` ⇒ `|f - c̃ - u_j| ≤ ε` (`obsFaceOK_sound`), from the centred bounds
  `|d.eval - κ_t|` with `κ = c̃` for `t = 0`, `κ = 1` for `t = e_j`, `κ = 0` otherwise; exactly one
  entry has `t = 0` and one
  has `t = e_j`.

Every check is a rational sum over the entries (`obsWF` is the shared well-formedness check:
`SpD.ok`, even parity). `litObs_add_two_pi` and `differentiable_litObs` need no check.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

/-- The literal observable `Σ_{(t, d) ∈ L} u^t · d.eval(φ)`. -/
def litObs (w S : ℕ) (L : List ((ℕ × ℕ × ℕ) × SpD)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (L.map fun e => umon (monOf e.1) p.1 * (e.2.opd w S).eval S p.2).sum

theorem litObs_eq_listObs (w S : ℕ) (L : List ((ℕ × ℕ × ℕ) × SpD)) :
    litObs w S L = listObs L (fun e => monOf e.1) (fun e => (e.2.opd w S).eval S) := rfl

theorem differentiable_litObs (w S : ℕ) (L : List ((ℕ × ℕ × ℕ) × SpD)) :
    Differentiable ℝ (litObs w S L) := by
  rw [litObs_eq_listObs]
  exact differentiable_listObs L _ fun e _ => SpD.differentiable_eval w S e.2

theorem litObs_add_two_pi (w S : ℕ) (L : List ((ℕ × ℕ × ℕ) × SpD)) :
    ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      litObs w S L (u, φ + fun a => 2 * Real.pi * m a) = litObs w S L (u, φ) := by
  rw [litObs_eq_listObs]
  exact listObs_add_two_pi L _ fun e _ => SpD.eval_add_two_pi w S e.2

/-! ### Monomial arithmetic on triples -/

/-- The degree of a triple. -/
def degT (t : ℕ × ℕ × ℕ) : ℕ := t.1 + t.2.1 + t.2.2

/-- The component `l` of a triple. -/
def compT (t : ℕ × ℕ × ℕ) (l : Fin 3) : ℕ := ![t.1, t.2.1, t.2.2] l

/-- The triple minus the unit `e_l` (truncated). -/
def subT (t : ℕ × ℕ × ℕ) (l : Fin 3) : ℕ × ℕ × ℕ :=
  ![(t.1 - 1, t.2.1, t.2.2), (t.1, t.2.1 - 1, t.2.2), (t.1, t.2.1, t.2.2 - 1)] l

/-- The unit triple `e_j`. -/
def unitT (j : Fin 3) : ℕ × ℕ × ℕ := ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] j

theorem mdeg_monOf (t : ℕ × ℕ × ℕ) : mdeg (monOf t) = degT t := by
  simp [mdeg, monOf, degT, Fin.sum_univ_three, add_assoc]

theorem mdeg_monOf_sub (t : ℕ × ℕ × ℕ) (l : Fin 3) :
    mdeg (monOf t - Pi.single l 1) = degT (subT t l) := by
  fin_cases l <;> simp [mdeg, monOf, degT, subT, Fin.sum_univ_three, add_assoc]

theorem monOf_apply (t : ℕ × ℕ × ℕ) (l : Fin 3) : monOf t l = compT t l := rfl

theorem umon_monOf_zero (u : Fin 3 → ℝ) : umon (monOf (0, 0, 0)) u = 1 := by
  simp [umon, monOf, Fin.prod_univ_three]

theorem umon_monOf_unitT (u : Fin 3 → ℝ) (j : Fin 3) : umon (monOf (unitT j)) u = u j := by
  fin_cases j <;> simp [umon, monOf, unitT, Fin.prod_univ_three]

theorem unitT_ne_zero (j : Fin 3) : unitT j ≠ (0, 0, 0) := by fin_cases j <;> simp [unitT]

/-! ### The checks -/

/-- Shared well-formedness: every model in the box, of even parity. -/
def obsWF (S : ℕ) (L : List ((ℕ × ℕ × ℕ) × SpD)) : Bool :=
  L.all fun e => e.2.ok S && e.2.par == false

/-- `Σ_e t_l ρ^{|t - e_l|} |q| Σ|m|`, a bound of `|∂_{u_l} f|`. -/
def fuSum (ρ : ℚ) (l : Fin 3) (L : List ((ℕ × ℕ × ℕ) × SpD)) : ℚ :=
  (L.map fun e => (compT e.1 l : ℚ) * ρ ^ degT (subT e.1 l) * (|e.2.q| * e.2.l1E)).sum

/-- `Σ_e ρ^{|t|} |q| Σ|k_b||m|`, a bound of `|∂_{φ_b} f|`. -/
def phiSum (ρ : ℚ) (b : Fin 2) (L : List ((ℕ × ℕ × ℕ) × SpD)) : ℚ :=
  (L.map fun e => ρ ^ degT e.1 * (|e.2.q| * spW e.2.C e.2.es b)).sum

/-- The face target of a monomial: `c̃` for `0`, `1` for `e_j`, `0` otherwise. -/
def kapT (j : Fin 3) (ct : ℚ) (t : ℕ × ℕ × ℕ) : ℚ :=
  if t = (0, 0, 0) then ct else if t = unitT j then 1 else 0

/-- `Σ_e ρ^{|t|} (|q m₀ - κ_t| + |q| Σ_{k≠0}|m|)`, a bound of `|f - c̃ - u_j|`. -/
def faceSum (ρ : ℚ) (j : Fin 3) (ct : ℚ) (L : List ((ℕ × ℕ × ℕ) × SpD)) : ℚ :=
  (L.map fun e => ρ ^ degT e.1 *
    (|e.2.q * spZ0 e.2.C e.2.es - kapT j ct e.1| + |e.2.q| * spNZ e.2.C e.2.es)).sum

/-- The `u`-partial check. -/
def obsFuOK (S : ℕ) (ρ : ℚ) (FuMax : Fin 3 → ℚ) (L : List ((ℕ × ℕ × ℕ) × SpD)) : Bool :=
  obsWF S L && decide (0 ≤ ρ) && decide (fuSum ρ 0 L ≤ FuMax 0) && decide (fuSum ρ 1 L ≤ FuMax 1) &&
    decide (fuSum ρ 2 L ≤ FuMax 2)

/-- The `φ`-partial check. -/
def obsPhiOK (S : ℕ) (ρ : ℚ) (FphiMax : Fin 2 → ℚ) (L : List ((ℕ × ℕ × ℕ) × SpD)) : Bool :=
  obsWF S L && decide (0 ≤ ρ) && decide (phiSum ρ 0 L ≤ FphiMax 0) &&
    decide (phiSum ρ 1 L ≤ FphiMax 1)

/-- The face check. -/
def obsFaceOK (S : ℕ) (ρ : ℚ) (j : Fin 3) (ct ε : ℚ) (L : List ((ℕ × ℕ × ℕ) × SpD)) : Bool :=
  obsWF S L && decide (0 ≤ ρ) && decide (L.countP (fun e => e.1 == (0, 0, 0)) = 1) &&
    decide (L.countP (fun e => e.1 == unitT j) = 1) && decide (faceSum ρ j ct L ≤ ε)

theorem obsWF_spec {S : ℕ} {L : List ((ℕ × ℕ × ℕ) × SpD)} (h : obsWF S L = true) :
    ∀ e ∈ L, e.2.ok S = true ∧ e.2.par = false := by
  intro e he
  have := List.all_eq_true.mp h e he
  simpa [Bool.and_eq_true] using this

theorem obs_cast_list_sum {β : Type*} (L : List β) (f : β → ℚ) :
    (((L.map f).sum : ℚ) : ℝ) = (L.map fun x => (f x : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem obsFuOK_sound {w S : ℕ} {ρ : ℚ} {FuMax : Fin 3 → ℚ} {L : List ((ℕ × ℕ × ℕ) × SpD)}
    (h : obsFuOK S ρ FuMax L = true) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (hu : ∀ l, |u l| ≤ ρ)
    (l : Fin 3) : |fderiv ℝ (litObs w S L) (u, φ) (Pi.single l 1, 0)| ≤ FuMax l := by
  simp only [obsFuOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hwf, -⟩, h0⟩, h1⟩, h2⟩ := h
  have hwf' := obsWF_spec hwf
  rw [litObs_eq_listObs]
  refine (abs_fderiv_listObs_u_le L _ (fun e _ => SpD.differentiable_eval w S e.2)
    (G := fun e => |(e.2.q : ℝ)| * e.2.l1E) (fun e he φ => SpD.abs_eval_le' (hwf' e he).1 φ)
    hu φ l).trans ?_
  have hc : ((fuSum ρ l L : ℚ) : ℝ) = (L.map fun e => ((monOf e.1 l : ℕ) : ℝ) *
      (ρ : ℝ) ^ mdeg (monOf e.1 - Pi.single l 1) * (|(e.2.q : ℝ)| * e.2.l1E)).sum := by
    rw [fuSum, obs_cast_list_sum]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    rw [mdeg_monOf_sub, monOf_apply]; push_cast; ring
  rw [← hc]
  fin_cases l
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2

theorem obsPhiOK_sound {w S : ℕ} {ρ : ℚ} {FphiMax : Fin 2 → ℚ} {L : List ((ℕ × ℕ × ℕ) × SpD)}
    (h : obsPhiOK S ρ FphiMax L = true) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (hu : ∀ l, |u l| ≤ ρ)
    (b : Fin 2) : |fderiv ℝ (litObs w S L) (u, φ) (0, Pi.single b 1)| ≤ FphiMax b := by
  simp only [obsPhiOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hwf, -⟩, h0⟩, h1⟩ := h
  have hwf' := obsWF_spec hwf
  rw [litObs_eq_listObs]
  refine (abs_fderiv_listObs_φ_le L _ (fun e _ => SpD.differentiable_eval w S e.2)
    (G' := fun e => |(e.2.q : ℝ)| * spW e.2.C e.2.es b)
    (fun e he φ => SpD.abs_fderiv_eval_le (hwf' e he).1 φ b) hu φ).trans ?_
  have hc : ((phiSum ρ b L : ℚ) : ℝ) = (L.map fun e => (ρ : ℝ) ^ mdeg (monOf e.1) *
      (|(e.2.q : ℝ)| * spW e.2.C e.2.es b)).sum := by
    rw [phiSum, obs_cast_list_sum]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    rw [mdeg_monOf]; push_cast; ring
  rw [← hc]
  fin_cases b
  · exact_mod_cast h0
  · exact_mod_cast h1

theorem sum_umon_kapT (j : Fin 3) (ct : ℚ) (u : Fin 3 → ℝ) (L : List ((ℕ × ℕ × ℕ) × SpD)) :
    (L.map fun e => umon (monOf e.1) u * ((kapT j ct e.1 : ℚ) : ℝ)).sum =
      (L.countP (fun e => e.1 == (0, 0, 0)) : ℝ) * ct +
        (L.countP (fun e => e.1 == unitT j) : ℝ) * u j := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h0 : e.1 = (0, 0, 0)
    · simp [kapT, h0, umon_monOf_zero, (unitT_ne_zero j).symm]
      ring
    · by_cases h1 : e.1 = unitT j
      · simp [kapT, h1, umon_monOf_unitT, unitT_ne_zero j]
        ring
      · simp [kapT, h0, h1]

theorem obsFaceOK_sound {w S : ℕ} {ρ : ℚ} {j : Fin 3} {ct ε : ℚ} {L : List ((ℕ × ℕ × ℕ) × SpD)}
    (h : obsFaceOK S ρ j ct ε L = true) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (hu : ∀ l, |u l| ≤ ρ) :
    |litObs w S L (u, φ) - ct - u j| ≤ ε := by
  simp only [obsFaceOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hwf, -⟩, hc0⟩, hc1⟩, hε⟩ := h
  have hwf' := obsWF_spec hwf
  have key := abs_listObs_sub_le L (fun e => monOf e.1) (fun e => (e.2.opd w S).eval S)
    (κ := fun e => ((kapT j ct e.1 : ℚ) : ℝ))
    (D := fun e => |(e.2.q : ℝ) * spZ0 e.2.C e.2.es - ((kapT j ct e.1 : ℚ) : ℝ)| +
      |(e.2.q : ℝ)| * spNZ e.2.C e.2.es)
    (fun e he φ => SpD.abs_eval_sub_le (hwf' e he).1 (hwf' e he).2 _ φ) hu φ
  rw [sum_umon_kapT, hc0, hc1] at key
  push_cast at key
  rw [← litObs_eq_listObs] at key
  have hs : (((faceSum ρ j ct L : ℚ) : ℝ)) = (L.map fun e => (ρ : ℝ) ^ mdeg (monOf e.1) *
      (|(e.2.q : ℝ) * spZ0 e.2.C e.2.es - ((kapT j ct e.1 : ℚ) : ℝ)| +
        |(e.2.q : ℝ)| * spNZ e.2.C e.2.es)).sum := by
    rw [faceSum, obs_cast_list_sum]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    rw [mdeg_monOf]; push_cast; ring
  have hε' : ((faceSum ρ j ct L : ℚ) : ℝ) ≤ ε := by exact_mod_cast hε
  rw [hs] at hε'
  calc |litObs w S L (u, φ) - ct - u j| = |litObs w S L (u, φ) - (1 * (ct : ℝ) + 1 * u j)| := by
        ring_nf
    _ ≤ _ := key
    _ ≤ ε := hε'

end KAM.EffectiveStability.Tube

end
