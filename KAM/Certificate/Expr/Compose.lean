/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.ComposeModels

/-!
# Composition of a straight-line program with a certified embedding

`Slp.compose n p K wit W cfg pe wanted` runs the program `p` slot by slot on Fourier models of
`θ ↦ slot(K θ)` (SO design §1.7) and returns the models of the requested slots, or `none` if a
witness check fails (fail closed). Slot by slot:

* `const`: `constModel` (key `[]`); `action j`: the exact data `(2π)^{dA_j} A_j`;
* `char k`: `χ_k ∘ K = χ_k · exp(2πi k·(2π)^{dU} U)`. The character witness is looked up under
  the normalized index `K.normKey n k` (coordinates with syntactically zero `U_j` zeroed); if
  that key has none (or its check fails), the witness of `-k` is used through
  `CertPoly.reflectSorted` (`conjReflect`, order kept ascending). Each table witness is an
  `ExpWitness` checked once by `expWitnessRadius` against `charPhaseModel` (its pin
  `exp(2πi k·U(0))` goes through `certCExpReduced`; a failed reduction fails the composition);
  certified witnesses and reflections are cached under their normalized key; the slot model is
  the exact shift by `k` (`shiftModel`);
* `add`: `CertModel.add`, the second operand re-expressed at the first operand's degree;
* `mul`: `CertModel.mul` at the product key `[0, slot]`, with the factors' weighted norms cached
  per slot (`CertModel.mulN`, SO-MALG signal 1(c)). A constant operand (every key zero) is a
  scalar multiplication (`CertModel.polyProduct`'s scalar route, SO-ADVCOUNT lever 1);
* `exp`: the next exp witness (slot order) against the operand at degree `0`;
* `inv`: the next reciprocal witness, which certifies its own nonvanishing (`invWitness_sound`).

Exp witness number `i` reads the advice keys `[1, i, j]` (re-keyed to `[1, j]`), character
witness number `c` (position in `charWit`) the keys `[1, expWit.length + c, j]`, reciprocal
witness number `i` the key `[2, i]` (re-keyed to `[2]`): `ModelConfig.forWitness`.

`Slp.compose_sound` holds on success, unconditionally in the domain.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- Witnesses: one per `exp` slot and one per `inv` slot of the jet program (slot order), and
the character table keyed by the normalized index (coordinates with syntactically zero `U_j`
zeroed; `-k` uses `conjReflect`). Exp and character witnesses are `ExpWitness`es: each carries
its own pin halving count and order, and its pin `exp(2πi k·U(0))` (characters) or
`exp g₀(0)` goes through `certCExpReduced` (Revision 4, F10). -/
structure Witnesses (α : Type) where
  expWit : List (ExpWitness α)
  invWit : List (CertPoly α)
  charWit : List (CertKey × ExpWitness α)

section Defs

variable {α : Type} [CertArith α]

/-- `CertModel.mul` with the factors' weighted norms `na`, `nb` supplied (cached per slot). -/
def CertModel.mulN (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey) (a : CertModel α)
    (na : α) (b : CertModel α) (nb : α) : CertModel α :=
  match CertModel.polyProduct W cfg key a.poly b.poly with
  | some out =>
    ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
      upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
        (upAdd (upAdd (crossUp na b.rad) (crossUp nb a.rad)) (upMul a.rad b.rad))⟩
  | none => ⟨a.deg + b.deg, ⟨[]⟩, upMul (upAdd na a.rad) (upAdd nb b.rad)⟩

/-- The state of the composition: per slot its model and the model's weighted norm, the
numbers of exp and reciprocal witnesses used, and the certified character witnesses. -/
structure ComposeState (α : Type) where
  slots : List (CertModel α × α)
  nExp : ℕ
  nInv : ℕ
  cache : List (CertKey × CertPoly α × α)

/-- A slot entry: the model and its weighted norm. -/
def slotEntry (W : CertWeight) (m : CertModel α) : CertModel α × α := (m, m.poly.supNormUp W)

theorem pair_snd {β γ : Type} (b : β) (c : γ) : (b, c).2 = c := rfl

-- through `pair_snd`: a bare `rfl` lets lazy delta unfold `supNormUp` first (timeout)
theorem slotEntry_fst (W : CertWeight) (m : CertModel α) : (slotEntry W m).1 = m := by
  unfold slotEntry; rfl

theorem slotEntry_snd (W : CertWeight) (m : CertModel α) :
    (slotEntry W m).2 = m.poly.supNormUp W := by
  unfold slotEntry; exact pair_snd _ _

/-- The entry of slot `i` (the zero model off the program). -/
def ComposeState.slot (W : CertWeight) (st : ComposeState α) (i : ℕ) : CertModel α × α :=
  st.slots.getD i (slotEntry W zeroModel)

/-- Append a slot. -/
def ComposeState.push (W : CertWeight) (st : ComposeState α) (m : CertModel α) :
    ComposeState α :=
  { st with slots := st.slots ++ [slotEntry W m] }

/-- The certified character witness `(E, r)` of the table key `k'`, from the cache or checked
now (`none`: no witness under `k'`, or its check failed), with the new cache. -/
def charResolve (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (cache : List (CertKey × CertPoly α × α))
    (k' : CertKey) : Option ((CertPoly α × α) × List (CertKey × CertPoly α × α)) :=
  match findKeyIdx k' cache with
  | some e => some (e.2, cache)
  | none =>
    match findKeyIdx k' wit.charWit with
    | some (c, E) =>
      match expWitnessRadius n W (cfg.forWitness 1 (wit.expWit.length + c))
          (charPhaseModel n K W pe k') E with
      | some r => some ((E.poly, r), (k', E.poly, r) :: cache)
      | none => none
    | none => none

/-- The certified character witness of the normalized key `kk`: its own (`charResolve`), or
else the reflection `CertPoly.reflectSorted` of the witness of `-kk`, cached under `kk`. -/
def charEntry (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (cache : List (CertKey × CertPoly α × α))
    (kk : CertKey) : Option ((CertPoly α × α) × List (CertKey × CertPoly α × α)) :=
  match charResolve n K wit W cfg pe cache kk with
  | some e => some e
  | none =>
    match charResolve n K wit W cfg pe cache (kk.map Neg.neg) with
    | some (e, c) => some ((e.1.reflectSorted, e.2), (kk, e.1.reflectSorted, e.2) :: c)
    | none => none

/-- The model of the character slot `χ_k ∘ K`, with the new cache. -/
def charSlot (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (cache : List (CertKey × CertPoly α × α))
    (k : CertKey) : Option (CertModel α × List (CertKey × CertPoly α × α)) :=
  match charEntry n K wit W cfg pe cache (K.normKey n k) with
  | some (e, c) => some (shiftModel W (padKey n k) e.1 e.2, c)
  | none => none

/-- One slot of the composition. -/
def composeStep (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) :
    SlpOp → Option (ComposeState α)
  | .const re im deg => some (st.push W (constModel n re im deg))
  | .action j => some (st.push W
      (if j < n then realCompModel n (K.actionDeg.getD j 0) K.action[j]? else zeroModel))
  | .char k =>
    match charSlot n K wit W cfg pe st.cache k with
    | some (m, c) => some { st.push W m with cache := c }
    | none => none
  | .add a b => some (st.push W (CertModel.add W (st.slot W a).1
      (CertModel.toDeg W pe (st.slot W a).1.deg (st.slot W b).1)))
  | .mul a b => some (st.push W (CertModel.mulN W cfg [0, st.slots.length]
      (st.slot W a).1 (st.slot W a).2 (st.slot W b).1 (st.slot W b).2))
  | .exp a =>
    match wit.expWit[st.nExp]? with
    | some E =>
      match expWitnessRadius n W (cfg.forWitness 1 st.nExp)
          (CertModel.toDeg W pe 0 (st.slot W a).1) E with
      | some r => some { st.push W ⟨0, E.poly, r⟩ with nExp := st.nExp + 1 }
      | none => none
    | none => none
  | .inv a =>
    match wit.invWit[st.nInv]? with
    | some Q =>
      match invWitnessRadius n W (cfg.forWitness 2 st.nInv) (st.slot W a).1 Q with
      | some r => some { st.push W ⟨-(st.slot W a).1.deg, Q, r⟩ with nInv := st.nInv + 1 }
      | none => none
    | none => none

/-- The composition state after a list of operations (`none` once a check fails). -/
def composeOps (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (ops : List SlpOp) : Option (ComposeState α) :=
  ops.foldl (fun st op => st.bind fun st => composeStep n K wit W cfg pe st op)
    (some ⟨[], 0, 0, []⟩)

end Defs

/-- Composition of the jet slots with `K`: one model per requested slot, or `none` if a witness
check fails (including a failed range reduction of an exp or character pin: fail closed). -/
def Slp.compose {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) :=
  match composeOps n K wit W cfg pe p.ops with
  | some st => some (wanted.map fun i => (st.slot W i).1)
  | none => none

/-! ### Soundness -/

section Sound

variable {α : Type} [CertArith α]

theorem CertModel.mulN_supNormUp (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertModel α) : CertModel.mulN W cfg key a (a.poly.supNormUp W) b (b.poly.supNormUp W) =
      CertModel.mul W cfg key a b := rfl

/-- Every cached character witness encloses its character exponential. -/
def CacheValid (n : ℕ) (K : CertEmbedding α) (ρ : ℝ) (cache : List (CertKey × CertPoly α × α)) :
    Prop :=
  ∀ e ∈ cache, (⟨0, e.2.1, e.2.2⟩ : CertModel α).Encloses n ρ (charExpFun n K e.1)

/-- The invariant of the composition after the operations `ops`. -/
def ComposeState.Valid (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (ops : List SlpOp)
    (st : ComposeState α) : Prop :=
  st.slots.length = ops.length ∧
    (∀ i, (st.slot W i).1.Encloses n W.rho (fun θ => (Slp.vals n (K.eval n θ) ops).getD i 0) ∧
      (st.slot W i).2 = (st.slot W i).1.poly.supNormUp W) ∧
    CacheValid n K W.rho st.cache

variable [LawfulCertArith α]

theorem ComposeState.valid_nil (n : ℕ) (K : CertEmbedding α) (W : CertWeight) :
    (⟨[], 0, 0, []⟩ : ComposeState α).Valid n K W [] := by
  have e1 : ∀ i, (⟨[], 0, 0, []⟩ : ComposeState α).slot W i = slotEntry W zeroModel := fun i => by
    simp only [ComposeState.slot, List.getD_nil]
  refine ⟨rfl, fun i => ?_, fun e he => by simp at he⟩
  rw [e1, slotEntry_fst, slotEntry_snd]
  refine ⟨?_, rfl⟩
  intro θ hθ
  have : (Slp.vals n (K.eval n θ) []).getD i 0 = 0 := by simp [Slp.vals]
  beta_reduce
  rw [this]
  exact zeroModel_encloses (α := α) n W.rho θ hθ

/-- Appending a slot whose model encloses the new slot's value. -/
theorem ComposeState.Valid.push {n : ℕ} {K : CertEmbedding α} {W : CertWeight}
    {ops : List SlpOp} {op : SlpOp} {st : ComposeState α} (hv : st.Valid n K W ops)
    {m : CertModel α}
    (hm : m.Encloses n W.rho (fun θ => op.step n (K.eval n θ) (Slp.vals n (K.eval n θ) ops)))
    (st' : ComposeState α) (hs : st'.slots = st.slots ++ [slotEntry W m])
    (hc : CacheValid n K W.rho st'.cache) : st'.Valid n K W (ops ++ [op]) := by
  obtain ⟨hl, hi, -⟩ := hv
  refine ⟨by simp [hs, hl], fun i => ?_, hc⟩
  rcases lt_trichotomy i st.slots.length with h | h | h
  · have e1 : st'.slot W i = st.slot W i := by
      simp only [ComposeState.slot, hs, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h]
    rw [e1]
    refine ⟨?_, (hi i).2⟩
    intro θ hθ
    beta_reduce
    rw [Slp.val_append n _ ops [op] (hl ▸ h)]
    exact (hi i).1 θ hθ
  · have e1 : st'.slot W i = slotEntry W m := by
      subst h
      simp only [ComposeState.slot, hs, List.getD_eq_getElem?_getD,
        List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some]
    rw [e1, slotEntry_fst, slotEntry_snd]
    refine ⟨?_, rfl⟩
    intro θ hθ
    beta_reduce
    rw [h, hl, Slp.val_snoc_self]
    exact hm θ hθ
  · have e1 : st'.slot W i = slotEntry W zeroModel := by
      simp only [ComposeState.slot, hs, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [e1, slotEntry_fst, slotEntry_snd]
    refine ⟨?_, rfl⟩
    intro θ hθ
    have : (Slp.vals n (K.eval n θ) (ops ++ [op])).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [Slp.vals_length]; simp; omega)]
      rfl
    beta_reduce
    rw [this]
    exact zeroModel_encloses (α := α) n W.rho θ hθ

theorem charResolve_sound {n : ℕ} {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) {cfg : ModelConfig α} {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {cache : List (CertKey × CertPoly α × α)}
    (hc : CacheValid n K W.rho cache) {k' : CertKey} {e : CertPoly α × α}
    {c : List (CertKey × CertPoly α × α)} (h : charResolve n K wit W cfg pe cache k' = some (e, c)) :
    (⟨0, e.1, e.2⟩ : CertModel α).Encloses n W.rho (charExpFun n K k') ∧
      CacheValid n K W.rho c := by
  unfold charResolve at h
  cases hf : findKeyIdx k' cache with
  | some f =>
    rw [hf] at h
    have h' := Option.some.inj h
    rw [Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    subst h1 h2
    have hm := hc _ (findKeyIdx_mem (c := f.1) (b := f.2) hf)
    simp only at hm
    exact ⟨hm, hc⟩
  | none =>
    rw [hf] at h
    cases ht : findKeyIdx k' wit.charWit with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some t =>
      obtain ⟨i, E⟩ := t
      rw [ht] at h
      dsimp only at h
      cases hr : expWitnessRadius n W (cfg.forWitness 1 (wit.expWit.length + i))
          (charPhaseModel n K W pe k') E with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some r =>
        rw [hr] at h
        have h' := Option.some.inj h
        rw [Prod.mk.injEq] at h'
        obtain ⟨h1, h2⟩ := h'
        subst h1 h2
        obtain ⟨h0, hg⟩ := charPhaseModel_encloses (n := n) K hW hpe k'
        have hE := expWitness_sound hW _ hg h0 hr
        refine ⟨hE, fun f hf => ?_⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hE
        · exact hc f hf

theorem charEntry_sound {n : ℕ} {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) {cfg : ModelConfig α} {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {cache : List (CertKey × CertPoly α × α)}
    (hc : CacheValid n K W.rho cache) {kk : CertKey} {e : CertPoly α × α}
    {c : List (CertKey × CertPoly α × α)} (h : charEntry n K wit W cfg pe cache kk = some (e, c)) :
    (⟨0, e.1, e.2⟩ : CertModel α).Encloses n W.rho (charExpFun n K kk) ∧
      CacheValid n K W.rho c := by
  unfold charEntry at h
  cases h1 : charResolve n K wit W cfg pe cache kk with
  | some f =>
    rw [h1] at h
    rw [Option.some.inj h] at h1
    exact charResolve_sound hW hpe hc h1
  | none =>
    rw [h1] at h
    cases h2 : charResolve n K wit W cfg pe cache (kk.map Neg.neg) with
    | none => rw [h2] at h; exact absurd h (by simp)
    | some f =>
      obtain ⟨f1, c'⟩ := f
      rw [h2] at h
      dsimp only at h
      have h' := Option.some.inj h
      rw [Prod.mk.injEq] at h'
      obtain ⟨he, hc'⟩ := h'
      subst he hc'
      obtain ⟨hE, hcv⟩ := charResolve_sound hW hpe hc h2
      have hR := charExpFun_reflectSorted K kk hE
      refine ⟨hR, fun g hg => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hR
      · exact hcv g hg

theorem charSlot_sound {n : ℕ} {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) {cfg : ModelConfig α} {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {cache : List (CertKey × CertPoly α × α)}
    (hc : CacheValid n K W.rho cache) {k : CertKey} {m : CertModel α}
    {c : List (CertKey × CertPoly α × α)} (h : charSlot n K wit W cfg pe cache k = some (m, c)) :
    m.Encloses n W.rho (fun θ => Complex.exp (Complex.I * modePhase n k (K.eval n θ).1)) ∧
      CacheValid n K W.rho c := by
  have hval : (fun θ => Complex.exp (Complex.I * modePhase n k (K.eval n θ).1)) =
      fun θ => character (certKeyFun n (padKey n k)) θ * charExpFun n K k θ := by
    funext θ
    rw [exp_I_modePhase_eval, certKeyFun_padKey]
  rw [hval]
  unfold charSlot at h
  cases h1 : charEntry n K wit W cfg pe cache (K.normKey n k) with
  | none => rw [h1] at h; exact absurd h (by simp)
  | some f =>
    obtain ⟨e, c'⟩ := f
    rw [h1] at h
    dsimp only at h
    have h' := Option.some.inj h
    rw [Prod.mk.injEq] at h'
    obtain ⟨hm, hc'⟩ := h'
    subst hm hc'
    obtain ⟨hE, hcv⟩ := charEntry_sound hW hpe hc h1
    rw [charExpFun_normKey] at hE
    exact ⟨shiftModel_encloses hW (padKey_length n k) hE, hcv⟩

theorem composeStep_sound {n : ℕ} {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) {cfg : ModelConfig α} {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {ops : List SlpOp} {st st' : ComposeState α}
    (hv : st.Valid n K W ops) {op : SlpOp} (h : composeStep n K wit W cfg pe st op = some st') :
    st'.Valid n K W (ops ++ [op]) := by
  have hop : ∀ a, (st.slot W a).1.Encloses n W.rho
      (fun θ => (Slp.vals n (K.eval n θ) ops).getD a 0) := fun a => (hv.2.1 a).1
  cases op with
  | const re im deg =>
    simp only [composeStep, Option.some.injEq] at h
    subst h
    exact hv.push (constModel_encloses n W.rho re im deg) _ rfl hv.2.2
  | action j =>
    simp only [composeStep, Option.some.injEq] at h
    subst h
    refine hv.push ?_ _ rfl hv.2.2
    by_cases hj : j < n
    · simp only [hj, ↓reduceIte, SlpOp.step, ↓reduceDIte]
      exact realCompModel_encloses n W.rho _ _
    · simp only [hj, ↓reduceIte, SlpOp.step, ↓reduceDIte]
      exact zeroModel_encloses n W.rho
  | char k =>
    simp only [composeStep] at h
    split at h
    · rename_i m c hm
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hm', hc'⟩ := charSlot_sound hW hpe hv.2.2 hm
      exact hv.push hm' _ rfl hc'
    · simp at h
  | add a b =>
    simp only [composeStep, Option.some.injEq] at h
    subst h
    exact hv.push (CertModel.Encloses.add hW (hop a) ((hop b).toDeg hW hpe _)
      (toDeg_deg W pe _ _).symm) _ rfl hv.2.2
  | mul a b =>
    simp only [composeStep, Option.some.injEq] at h
    subst h
    rw [(hv.2.1 a).2, (hv.2.1 b).2, CertModel.mulN_supNormUp]
    exact hv.push (CertModel.Encloses.mul hW cfg _ (hop a) (hop b)) _ rfl hv.2.2
  | exp a =>
    simp only [composeStep] at h
    split at h
    · rename_i E _
      split at h
      · rename_i r hr
        simp only [Option.some.injEq] at h
        subst h
        exact hv.push (expWitness_sound hW _ ((hop a).toDeg hW hpe 0) (toDeg_deg W pe 0 _) hr)
          _ rfl hv.2.2
      · simp at h
    · simp at h
  | inv a =>
    simp only [composeStep] at h
    split at h
    · rename_i Q _
      split at h
      · rename_i r hr
        simp only [Option.some.injEq] at h
        subst h
        exact hv.push (invWitness_sound hW _ (hop a) hr).2 _ rfl hv.2.2
      · simp at h
    · simp at h

theorem composeOps_sound {n : ℕ} {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) {cfg : ModelConfig α} {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (ops : List SlpOp) {st : ComposeState α}
    (h : composeOps n K wit W cfg pe ops = some st) : st.Valid n K W ops := by
  induction ops using List.reverseRecOn generalizing st with
  | nil =>
    simp only [composeOps, List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ComposeState.valid_nil n K W
  | append_singleton ops op ih =>
    unfold composeOps at h
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    obtain ⟨st₀, h₀, h₁⟩ := Option.bind_eq_some_iff.mp h
    exact composeStep_sound hW hpe (ih h₀) h₁

end Sound

/-- Unconditional in the domain: reciprocal witnesses certify their own nonvanishing. -/
theorem Slp.compose_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (p : Slp)
    (K : CertEmbedding α) (wit : Witnesses α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (wanted : List ℕ) {ms : List (CertModel α)}
    (h : Slp.compose n p K wit W cfg pe wanted = some ms) :
    ms.length = wanted.length ∧ ∀ idx (hidx : idx < ms.length), ms[idx].Encloses n W.rho
      (fun θ => p.val n (K.eval n θ) (wanted.getD idx 0)) := by
  unfold Slp.compose at h
  split at h
  · rename_i st hst
    simp only [Option.some.injEq] at h
    subst h
    have hv := composeOps_sound hW hpe p.ops hst
    refine ⟨List.length_map _, fun idx hidx => ?_⟩
    rw [List.length_map] at hidx
    rw [List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    exact (hv.2.1 _).1
  · simp at h

end KAM.Certificate
