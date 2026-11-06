/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.BTerm
public import KAM.EffectiveStability.Tube.Obs.ListObs

/-!
# The bracket terms of one `u`-monomial (T2-CONF, N7)

For `h = Σ_{t ∈ Hl} u^t k_t` with the monomials stored as triples (`ν = monOf`, `Hl` without
duplicates) the terms `b` of `bterms Fl Hl` with `mon b = p` and `coef b ≠ 0` are determined by
`(a, i, kind, sh)`: the `H`-monomial is `t = p + e_axis - μ_i` (`tgt`), which must be a valid
(`tvalid`) member of `Hl`. `brList Fl μ inH p` lists them without enumerating `Hl`, and
`sum_filter_mon` sums any `F` that vanishes on zero coefficients over the filter as over
`brList`. The kernel runs `brList` (`2 · |Fl| · 4` cheap candidates per `p`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- `1` on the axis, `0` elsewhere. -/
def dl (ax k : Fin 3) : ℕ := if ax = k then 1 else 0

/-- The `H`-monomial `p + e_ax - m` of a bracket term. -/
def tgt (m : Fin 3 → ℕ) (ax : Fin 3) (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (p.1 + dl ax 0 - m 0, p.2.1 + dl ax 1 - m 1, p.2.2 + dl ax 2 - m 2)

/-- `m ≤ p + e_ax` componentwise. -/
def tvalid (m : Fin 3 → ℕ) (ax : Fin 3) (p : ℕ × ℕ × ℕ) : Bool :=
  decide (m 0 ≤ p.1 + dl ax 0) && decide (m 1 ≤ p.2.1 + dl ax 1) && decide (m 2 ≤ p.2.2 + dl ax 2)

/-- The candidate term of `(a, i, kind, sh)` for the monomial `p`. -/
def brCand {ι : Type*} (μ : ι → Fin 3 → ℕ) (p : ℕ × ℕ × ℕ) (a : Fin 2) (i : ι) (kind sh : Bool) :
    BT ι (ℕ × ℕ × ℕ) :=
  ⟨a, i, tgt (μ i) (if sh then 2 else a.castSucc) p, kind, sh⟩

/-- The candidate is kept. -/
def brKeep {ι : Type*} (μ : ι → Fin 3 → ℕ) (inH : ℕ × ℕ × ℕ → Bool) (p : ℕ × ℕ × ℕ) (a : Fin 2)
    (i : ι) (kind sh : Bool) : Bool :=
  tvalid (μ i) (if sh then 2 else a.castSucc) p && inH (brCand μ p a i kind sh).e &&
    ((brCand μ p a i kind sh).coef μ monOf != 0)

/-- The terms of the monomial `p` (kernel). -/
def brList {ι : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ) (inH : ℕ × ℕ × ℕ → Bool)
    (p : ℕ × ℕ × ℕ) : List (BT ι (ℕ × ℕ × ℕ)) :=
  ([0, 1] : List (Fin 2)).flatMap fun a => Fl.flatMap fun i =>
    ([false, true] : List Bool).flatMap fun kind => ([false, true] : List Bool).flatMap fun sh =>
      if brKeep μ inH p a i kind sh then [brCand μ p a i kind sh] else []

/-! ### List sums -/

theorem sum_map_filter_ite {α : Type*} (l : List α) (P : α → Bool) (F : α → ℝ) :
    ((l.filter P).map F).sum = (l.map fun x => if P x then F x else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.filter_cons]
    split_ifs with h <;> simp [h, ih]

theorem sum_map_flatMap' {α β : Type*} (l : List α) (f : α → List β) (F : β → ℝ) :
    ((l.flatMap f).map F).sum = (l.map fun x => ((f x).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem sum_map_comm' {α β : Type*} (l : List α) (m : List β) (f : α → β → ℝ) :
    (l.map fun x => (m.map fun y => f x y).sum).sum =
      (m.map fun y => (l.map fun x => f x y).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, ← List.sum_map_add]

theorem sum_map_ite_eq_of_nodup {β : Type*} [DecidableEq β] {l : List β} (hnd : l.Nodup) (t : β)
    (X : β → ℝ) : (l.map fun e => if e = t then X e else 0).sum = if t ∈ l then X t else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases hx : x = t
    · subst hx; simp [hnd.1]
    · have : t ≠ x := fun h => hx h.symm
      simp [hx, this]

/-! ### The monomial of a term -/

theorem monOf_apply (t : ℕ × ℕ × ℕ) :
    monOf t 0 = t.1 ∧ monOf t 1 = t.2.1 ∧ monOf t 2 = t.2.2 := by
  simp [monOf]

theorem one_le_of_coef_ne_zero {ι : Type*} (μ : ι → Fin 3 → ℕ) (b : BT ι (ℕ × ℕ × ℕ))
    (h : b.coef μ monOf ≠ 0) : 1 ≤ μ b.i b.axis + monOf b.e b.axis := by
  obtain ⟨a, i, e, kind, sh⟩ := b
  cases kind <;> cases sh <;> simp only [BT.coef, BT.axis, ite_true, Bool.false_eq_true,
    ite_false] at h ⊢ <;> omega

theorem eq_tgt_iff (M : Fin 3 → ℕ) (ax : Fin 3) (p e : ℕ × ℕ × ℕ) :
    e = tgt M ax p ↔ ∀ k, monOf e k = monOf p k + dl ax k - M k := by
  obtain ⟨e0, e1, e2⟩ := e
  obtain ⟨p0, p1, p2⟩ := p
  constructor
  · intro h k
    simp only [tgt, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    fin_cases k <;> simp [monOf]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp [monOf] at h0 h1 h2
    simp only [tgt, h0, h1, h2]

theorem tvalid_iff (M : Fin 3 → ℕ) (ax : Fin 3) (p : ℕ × ℕ × ℕ) :
    tvalid M ax p = true ↔ ∀ k, M k ≤ monOf p k + dl ax k := by
  obtain ⟨p0, p1, p2⟩ := p
  simp only [tvalid, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ k
    fin_cases k <;> simpa [monOf]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp [monOf] at h0 h1 h2
    exact ⟨⟨h0, h1⟩, h2⟩

theorem single_eq_dl (ax k : Fin 3) : (Pi.single ax 1 : Fin 3 → ℕ) k = dl ax k := by
  simp only [Pi.single_apply, dl]
  by_cases h : ax = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **The monomial condition**, for a term with a nonzero coefficient. -/
theorem mon_eq_iff {ι : Type*} (μ : ι → Fin 3 → ℕ) (b : BT ι (ℕ × ℕ × ℕ)) (p : ℕ × ℕ × ℕ)
    (hc : b.coef μ monOf ≠ 0) :
    b.mon μ monOf = monOf p ↔ b.e = tgt (μ b.i) b.axis p ∧ tvalid (μ b.i) b.axis p = true := by
  have hpos := one_le_of_coef_ne_zero μ b hc
  rw [eq_tgt_iff, tvalid_iff]
  constructor
  · intro h
    have hk : ∀ k, μ b.i k + monOf b.e k - dl b.axis k = monOf p k := fun k => by
      have := congrFun h k
      simpa [BT.mon, single_eq_dl] using this
    have hk' : ∀ k, μ b.i k + monOf b.e k = monOf p k + dl b.axis k := fun k => by
      have := hk k
      by_cases hax : b.axis = k
      · subst hax; simp only [dl, ite_true] at this ⊢; omega
      · simp only [dl, hax, ite_false] at this ⊢; omega
    exact ⟨fun k => by have := hk' k; omega, fun k => by have := hk' k; omega⟩
  · rintro ⟨he, hv⟩
    funext k
    have h1 := he k
    have h2 := hv k
    simp only [BT.mon, Pi.add_apply, Pi.sub_apply, single_eq_dl]
    omega

/-- **The regrouping.** -/
theorem sum_filter_mon {ι : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ) {Hl : List (ℕ × ℕ × ℕ)}
    (hnd : Hl.Nodup) {inH : ℕ × ℕ × ℕ → Bool} (hin : ∀ t, inH t = true ↔ t ∈ Hl)
    (F : BT ι (ℕ × ℕ × ℕ) → ℝ) (hF : ∀ b, b.coef μ monOf = 0 → F b = 0) (p : ℕ × ℕ × ℕ) :
    (((bterms Fl Hl).filter fun b => decide (b.mon μ monOf = monOf p)).map F).sum =
      ((brList Fl μ inH p).map F).sum := by
  rw [sum_map_filter_ite]
  simp only [bterms, brList, sum_map_flatMap']
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [sum_map_comm']
  refine congrArg List.sum (List.map_congr_left fun kind _ => ?_)
  simp only [List.map_map, Function.comp_def]
  rw [sum_map_comm']
  refine congrArg List.sum (List.map_congr_left fun sh _ => ?_)
  -- one `(a, i, kind, sh)`
  set t := tgt (μ i) (if sh then 2 else a.castSucc) p with ht
  have hterm : ∀ e ∈ Hl,
      (if decide ((⟨a, i, e, kind, sh⟩ : BT ι (ℕ × ℕ × ℕ)).mon μ monOf = monOf p) = true then
        F ⟨a, i, e, kind, sh⟩ else 0) =
      if e = t then (if brKeep μ inH p a i kind sh = true then F ⟨a, i, e, kind, sh⟩ else 0)
        else 0 := by
    intro e he
    by_cases hc : (⟨a, i, e, kind, sh⟩ : BT ι (ℕ × ℕ × ℕ)).coef μ monOf = 0
    · rw [hF _ hc]; simp
    · have hm : (⟨a, i, e, kind, sh⟩ : BT ι (ℕ × ℕ × ℕ)).mon μ monOf = monOf p ↔
          e = t ∧ tvalid (μ i) (if sh then 2 else a.castSucc) p = true :=
        mon_eq_iff μ ⟨a, i, e, kind, sh⟩ p hc
      by_cases het : e = t
      · have hinH : inH (brCand μ p a i kind sh).e = true := (hin t).2 (het ▸ he)
        have hct : (brCand μ p a i kind sh).coef μ monOf ≠ 0 := by
          have : brCand μ p a i kind sh = ⟨a, i, e, kind, sh⟩ := by rw [het]; rfl
          rw [this]; exact hc
        have hkeep :
            brKeep μ inH p a i kind sh = tvalid (μ i) (if sh then 2 else a.castSucc) p := by
          unfold brKeep
          rw [hinH]
          simp [hct]
        rw [if_pos het, hkeep]
        by_cases hv : tvalid (μ i) (if sh then 2 else a.castSucc) p = true
        · rw [if_pos hv, if_pos (by simpa using hm.2 ⟨het, hv⟩)]
        · rw [if_neg hv, if_neg]
          simp only [decide_eq_true_eq]
          exact fun h => hv (hm.1 h).2
      · rw [if_neg het, if_neg]
        simp only [decide_eq_true_eq]
        exact fun h => het (hm.1 h).1
  rw [List.map_congr_left hterm, sum_map_ite_eq_of_nodup hnd t (fun e =>
    if brKeep μ inH p a i kind sh = true then F ⟨a, i, e, kind, sh⟩ else 0)]
  by_cases hk : brKeep μ inH p a i kind sh = true
  · have htin : t ∈ Hl := by
      rw [← hin]
      simp only [brKeep, Bool.and_eq_true] at hk
      exact hk.1.2
    rw [if_pos htin, if_pos hk, if_pos hk]
    simp [brCand, ht]
  · rw [if_neg hk]
    simp [hk]

end KAM.EffectiveStability.Tube

end
