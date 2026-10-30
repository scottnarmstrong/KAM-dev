/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.SegDefs

/-!
# Segmented composition: agreement of the shadow run with the landed run (SO-CSEG-A)

`ComposeState.AgreeOn W R st st'`: equal metadata and equal whole slot pairs on the slots `R` (below
the length). The landed `composeStep` reads only the metadata and the pairs of its operands
(`composeStep_congr`, all eight arms), and its four infallible arms push one slot without touching
the metadata (`composeStep_infallible`). Hence the shadow run of a segment, seeded with the ledger
pairs of its imports, agrees with the landed run on the imported slots and on the computed new slots
(`shadowRun_agree`), provided the retained set lies in the initial prefix (`hR`; without it the
statement is false: `shadowRun_agree_needs_hR` in `Tests/Seg.lean`). Slots below the length persist
(`composeOpsAux_slot_persist`). Everything here is an equation between computable terms.
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α]

/-- Agreement of two states on the slots `R`: equal metadata, equal whole pairs on `R`. -/
def ComposeState.AgreeOn (W : CertWeight) (R : ℕ → Prop) (st st' : ComposeState α) : Prop :=
  st.len = st'.len ∧ st.nExp = st'.nExp ∧ st.nInv = st'.nInv ∧ st.cache = st'.cache ∧
    ∀ i, R i → i < st.len → st.slot W i = st'.slot W i

/-! ### Slots of a pushed state -/

theorem ComposeState.slot_of_cons (W : CertWeight) {st t : ComposeState α} {e : CertModel α × α}
    (hr : t.rev = e :: st.rev) (hl : t.len = st.len + 1) {i : ℕ} (hi : i < st.len) :
    t.slot W i = st.slot W i := by
  simp only [ComposeState.slot, hr, hl, hi, (by omega : i < st.len + 1), ↓reduceIte]
  rw [show st.len + 1 - 1 - i = (st.len - 1 - i) + 1 by omega, List.getD_cons_succ]

theorem ComposeState.slot_of_cons_self (W : CertWeight) {st t : ComposeState α}
    {e : CertModel α × α} (hr : t.rev = e :: st.rev) (hl : t.len = st.len + 1) :
    t.slot W st.len = e := by
  simp only [ComposeState.slot, hr, hl, (by omega : st.len < st.len + 1), ↓reduceIte]
  rw [show st.len + 1 - 1 - st.len = 0 by omega, List.getD_cons_zero]

theorem pushSlot_slot_lt (W : CertWeight) (st : ComposeState α) (m : CertModel α) {i : ℕ}
    (hi : i < st.len) : (st.pushSlot W m).slot W i = st.slot W i :=
  ComposeState.slot_of_cons W rfl rfl hi

theorem ComposeState.AgreeOn.retain {W : CertWeight} {R R' : ℕ → Prop} {st st' : ComposeState α}
    (h : st.AgreeOn W R st') (hRR : ∀ i, R' i → R i) : st.AgreeOn W R' st' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun i hi hlt => h.2.2.2.2 i (hRR i hi) hlt⟩

/-- Two states extending agreeing states by the same entry agree on the old slots and the new
one. -/
theorem ComposeState.AgreeOn.of_push {W : CertWeight} {R : ℕ → Prop} {st st' t t' : ComposeState α}
    (h : st.AgreeOn W R st') {e : CertModel α × α}
    (hr : t.rev = e :: st.rev) (hr' : t'.rev = e :: st'.rev)
    (hl : t.len = st.len + 1) (hl' : t'.len = st'.len + 1)
    (he : t.nExp = t'.nExp) (hi : t.nInv = t'.nInv) (hc : t.cache = t'.cache) :
    t.AgreeOn W (fun i => R i ∨ i = st.len) t' := by
  obtain ⟨hlen, -, -, -, hs⟩ := h
  refine ⟨by rw [hl, hl', hlen], he, hi, hc, fun i hRi hlt => ?_⟩
  rw [hl] at hlt
  rcases Nat.lt_or_ge i st.len with h1 | h1
  · rw [ComposeState.slot_of_cons W hr hl h1, ComposeState.slot_of_cons W hr' hl' (hlen ▸ h1)]
    exact hs i (hRi.resolve_right (by omega)) h1
  · obtain rfl : i = st.len := by omega
    rw [ComposeState.slot_of_cons_self W hr hl, hlen, ComposeState.slot_of_cons_self W hr' hl']

/-! ### The landed step -/

theorem composeStep_infallible (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) {op : SlpOp}
    (hop : op.fallible = false) :
    ∃ m, composeStep n K wit W cfg pe st op = some (st.pushSlot W m) := by
  cases op <;> simp_all [SlpOp.fallible, composeStep]

/-- Every successful step pushes exactly one entry. -/
theorem composeStep_push (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) {st st' : ComposeState α} {op : SlpOp}
    (h : composeStep n K wit W cfg pe st op = some st') :
    ∃ e, st'.rev = e :: st.rev ∧ st'.len = st.len + 1 := by
  cases op with
  | const re im d =>
    simp only [composeStep, Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
  | action j =>
    simp only [composeStep, Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
  | add a b =>
    simp only [composeStep, Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
  | mul a b =>
    simp only [composeStep, Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
  | char k =>
    simp only [composeStep] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
    · simp at h
  | exp a =>
    simp only [composeStep] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
      · simp at h
    · simp at h
  | inv a =>
    simp only [composeStep] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
      · simp at h
    · simp at h
  | sqrt a =>
    simp only [composeStep] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
      · simp at h
    · simp at h

/-- **Congruence of the landed step**: agreeing states whose operands agree step alike. -/
theorem composeStep_congr (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) {R : ℕ → Prop} {st st' : ComposeState α}
    (h : st.AgreeOn W R st') {op : SlpOp} (hr : ∀ a ∈ opDeps op, R a ∧ a < st.len) :
    Option.Rel (ComposeState.AgreeOn W fun i => R i ∨ i = st.len)
      (composeStep n K wit W cfg pe st op) (composeStep n K wit W cfg pe st' op) := by
  have hsl : ∀ a ∈ opDeps op, st.slot W a = st'.slot W a :=
    fun a ha => h.2.2.2.2 a (hr a ha).1 (hr a ha).2
  have hlen := h.1
  have hexp := h.2.1
  have hinv := h.2.2.1
  have hcache := h.2.2.2.1
  cases op with
  | const re im d => exact .some (h.of_push rfl rfl rfl rfl hexp hinv hcache)
  | action j => exact .some (h.of_push rfl rfl rfl rfl hexp hinv hcache)
  | add a b =>
    have ha := hsl a (by simp [opDeps])
    have hb := hsl b (by simp [opDeps])
    simp only [composeStep]
    rw [ha, hb]
    exact .some (h.of_push rfl rfl rfl rfl hexp hinv hcache)
  | mul a b =>
    have ha := hsl a (by simp [opDeps])
    have hb := hsl b (by simp [opDeps])
    simp only [composeStep]
    rw [ha, hb, hlen]
    exact .some (by rw [← hlen]; exact h.of_push rfl rfl rfl rfl hexp hinv hcache)
  | char k =>
    simp only [composeStep]
    rw [hcache]
    rcases charSlot n K wit W cfg pe st'.cache k with _ | ⟨m, c⟩
    · exact .none
    · exact .some (h.of_push rfl rfl rfl rfl hexp hinv rfl)
  | exp a =>
    have ha := hsl a (by simp [opDeps])
    simp only [composeStep]
    rw [ha, hexp]
    rcases wit.expWit[st'.nExp]? with _ | E
    · exact .none
    · dsimp only
      rcases expWitnessRadius n W (cfg.forWitness 1 st'.nExp)
          (CertModel.toDeg W pe 0 (st'.slot W a).1) E with _ | r
      · exact .none
      · exact .some (h.of_push rfl rfl rfl rfl rfl hinv hcache)
  | inv a =>
    have ha := hsl a (by simp [opDeps])
    simp only [composeStep]
    rw [ha, hinv]
    rcases wit.invWit[st'.nInv]? with _ | Q
    · exact .none
    · dsimp only
      rcases invWitnessRadius n W (cfg.forWitness 2 st'.nInv) (st'.slot W a).1 Q with _ | r
      · exact .none
      · exact .some (h.of_push rfl rfl rfl rfl hexp rfl hcache)
  | sqrt a =>
    have ha := hsl a (by simp [opDeps])
    simp only [composeStep]
    rw [ha, hlen]
    split
    next =>
      split
      next => exact .some (by rw [← hlen]; exact h.of_push rfl rfl rfl rfl hexp hinv hcache)
      next => exact .none
    next => exact .none

/-! ### Seeds -/

theorem seed_len (W : CertWeight) (m : ComposeMeta α) (C : ComposeCkpt α) (imps : List ℕ) :
    (ComposeState.seed W m C imps).len = m.len := rfl

theorem seed_stateMeta (W : CertWeight) (m : ComposeMeta α) (C : ComposeCkpt α) (imps : List ℕ) :
    (ComposeState.seed W m C imps).stateMeta = m := rfl

theorem seed_slot_of_mem (W : CertWeight) (m : ComposeMeta α) (C : ComposeCkpt α)
    {imps : List ℕ} {a : ℕ} (ha : imps.contains a = true) (hlt : a < m.len) :
    (ComposeState.seed W m C imps).slot W a = C.slotPair W a := by
  simp only [ComposeState.slot, ComposeState.seed, hlt, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simp; omega),
    List.length_range, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show m.len - 1 - (m.len - 1 - a) = a by omega, ite_eq_left_iff.mpr (fun h => absurd ha h)]

/-- The seed agrees with a landed state of the same metadata on the imported slots. -/
theorem seed_agree (W : CertWeight) {m : ComposeMeta α} (C : ComposeCkpt α) {imps : List ℕ}
    {X : ComposeState α} (hX : X.stateMeta = m)
    (hs : ∀ a, imps.contains a = true → a < m.len → X.slot W a = C.slotPair W a) :
    (ComposeState.seed W m C imps).AgreeOn W (fun a => imps.contains a = true) X := by
  obtain ⟨len, e, i, c⟩ := m
  simp only [ComposeState.stateMeta, ComposeMeta.mk.injEq] at hX
  obtain ⟨h1, h2, h3, h4⟩ := hX
  refine ⟨h1.symm, h2.symm, h3.symm, h4.symm, fun a ha hlt => ?_⟩
  rw [seed_slot_of_mem W _ C ha hlt, hs a ha hlt]

/-! ### The shadow run -/

theorem live_cons_zero {s : SegSpec} {op : SlpOp} {rest : List SlpOp} (b : ℕ) :
    (s.live.contains b || ((op :: rest).getD (b - b) nopOp).fallible) =
      (s.live.contains b || op.fallible) := by
  rw [Nat.sub_self, List.getD_cons_zero]

theorem live_cons_succ {s : SegSpec} {op : SlpOp} {rest : List SlpOp} {b a : ℕ} (h : b < a) :
    (s.live.contains a || ((op :: rest).getD (a - b) nopOp).fallible) =
      (s.live.contains a || (rest.getD (a - (b + 1)) nopOp).fallible) := by
  rw [show a - b = (a - (b + 1)) + 1 by omega, List.getD_cons_succ]

theorem shadowStep_len (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) {s : SegSpec} {st st' : ComposeState α}
    {op : SlpOp} (h : shadowStep n K wit W cfg pe s st op = some st') : st'.len = st.len + 1 := by
  unfold shadowStep at h
  split at h
  · exact (composeStep_push n K wit W cfg pe h).choose_spec.2
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem shadowRun_len (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (s : SegSpec) :
    ∀ {os : List SlpOp} {σ σ' : ComposeState α},
      shadowRun n K wit W cfg pe s (some σ) os = some σ' → σ'.len = σ.len + os.length
  | [], σ, σ', h => by simp only [shadowRun, Option.some.injEq] at h; subst h; rfl
  | op :: rest, σ, σ', h => by
    simp only [shadowRun] at h
    cases hst : shadowStep n K wit W cfg pe s σ op with
    | none => rw [hst] at h; simp [shadowRun] at h
    | some σ1 =>
      rw [hst] at h
      rw [shadowRun_len n K wit W cfg pe s h, shadowStep_len n K wit W cfg pe hst,
        List.length_cons]
      omega

/-- **Agreement of the shadow run with the landed run** on the retained slots `R` (inside the
initial prefix, `hR`) and on the computed new slots. -/
theorem shadowRun_agree (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (s : SegSpec) {os : List SlpOp} {R : ℕ → Prop}
    {σ X σ' : ComposeState α} (hR : ∀ i, R i → i < σ.len) (hagree : σ.AgreeOn W R X)
    (hreads : ∀ (k : ℕ) (hk : k < os.length),
      (s.live.contains (σ.len + k) || os[k].fallible) = true →
        ∀ a ∈ opDeps os[k], a < σ.len + k ∧
          (R a ∨ (σ.len ≤ a ∧ (s.live.contains a || (os.getD (a - σ.len) nopOp).fallible) = true)))
    (hrun : shadowRun n K wit W cfg pe s (some σ) os = some σ') :
    ∃ X', composeOpsAux n K wit W cfg pe (some X) os = some X' ∧
      σ'.AgreeOn W (fun i => R i ∨
        (σ.len ≤ i ∧ (s.live.contains i || (os.getD (i - σ.len) nopOp).fallible) = true)) X' := by
  induction os generalizing R σ X with
  | nil =>
    simp only [shadowRun, Option.some.injEq] at hrun
    subst hrun
    refine ⟨X, rfl, hagree.1, hagree.2.1, hagree.2.2.1, hagree.2.2.2.1, fun i hi hlt => ?_⟩
    rcases hi with hi | ⟨hge, -⟩
    · exact hagree.2.2.2.2 i hi hlt
    · omega
  | cons op rest ih =>
    simp only [shadowRun] at hrun
    cases hst : shadowStep n K wit W cfg pe s σ op with
    | none => rw [hst] at hrun; simp [shadowRun] at hrun
    | some σ1 =>
      rw [hst] at hrun
      have hlen1 : σ1.len = σ.len + 1 := shadowStep_len n K wit W cfg pe hst
      -- the reads of the remaining operations, shifted by one
      have hreads0 := fun (k : ℕ) (hk : k < rest.length) => hreads (k + 1) (by simp; omega)
      by_cases hlive : (s.live.contains σ.len || op.fallible) = true
      · -- a computed operation: the landed step on both sides
        have hstep : composeStep n K wit W cfg pe σ op = some σ1 := by
          unfold shadowStep at hst
          split at hst
          · exact hst
          · exact absurd hlive ‹_›
        have hrd : ∀ a ∈ opDeps op, R a ∧ a < σ.len := by
          intro a ha
          obtain ⟨hlt, hRa | ⟨hge, -⟩⟩ :=
            hreads 0 (by simp) (by simpa using hlive) a (by simpa using ha)
          · exact ⟨hRa, by omega⟩
          · omega
        have hc := composeStep_congr n K wit W cfg pe hagree hrd
        rw [hstep] at hc
        cases hX : composeStep n K wit W cfg pe X op with
        | none => rw [hX] at hc; cases hc
        | some X1 =>
          rw [hX] at hc
          have hag1 : σ1.AgreeOn W (fun i => R i ∨ i = σ.len) X1 := by cases hc; assumption
          obtain ⟨X', hX', hag'⟩ := ih (R := fun i => R i ∨ i = σ.len) (σ := σ1) (X := X1)
            (fun i hi => by rcases hi with hi | rfl <;> [have := hR i hi; skip] <;> omega) hag1
            (fun k hk hl a ha => by
              have hl' : (s.live.contains (σ.len + (k + 1)) ||
                  ((op :: rest)[k + 1]'(by simp; omega)).fallible) = true := by
                rw [List.getElem_cons_succ, show σ.len + (k + 1) = σ1.len + k by omega]; exact hl
              obtain ⟨hlt, hRa | ⟨hge, hL⟩⟩ := hreads0 k hk hl' a (by simpa using ha)
              · exact ⟨by omega, .inl (.inl hRa)⟩
              · rcases Nat.lt_or_ge σ.len a with hgt | hle
                · rw [live_cons_succ hgt] at hL
                  exact ⟨by omega, .inr ⟨by omega, by rw [hlen1]; exact hL⟩⟩
                · exact ⟨by omega, .inl (.inr (by omega))⟩)
            hrun
          refine ⟨X', by simp only [composeOpsAux, hX]; exact hX', hag'.retain fun i hi => ?_⟩
          rcases hi with hi | ⟨hge, hL⟩
          · exact .inl (.inl hi)
          · rcases Nat.lt_or_ge σ.len i with hgt | hle
            · rw [live_cons_succ hgt] at hL
              exact .inr ⟨by omega, by rw [hlen1]; exact hL⟩
            · exact .inl (.inr (by omega))
      · -- a dead infallible operation: a placeholder against the landed push
        have hfal : op.fallible = false := by
          revert hlive; cases op.fallible <;> simp
        have hσ1 : σ1 = σ.pushSlot W zeroModel := by
          unfold shadowStep at hst
          split at hst
          · exact absurd ‹_› hlive
          · exact (Option.some.inj hst).symm
        obtain ⟨m, hX⟩ := composeStep_infallible n K wit W cfg pe X hfal
        have hag1 : σ1.AgreeOn W R (X.pushSlot W m) := by
          subst hσ1
          refine ⟨by simp [ComposeState.pushSlot, hagree.1], hagree.2.1, hagree.2.2.1,
            hagree.2.2.2.1,
            fun i hi hlt => ?_⟩
          have h1 := hR i hi
          rw [pushSlot_slot_lt W σ zeroModel h1, pushSlot_slot_lt W X m (hagree.1 ▸ h1)]
          exact hagree.2.2.2.2 i hi h1
        have hdead : ∀ a, σ.len ≤ a →
            (s.live.contains a || ((op :: rest).getD (a - σ.len) nopOp).fallible) = true →
            σ.len < a := by
          intro a hge hL
          rcases Nat.lt_or_ge σ.len a with hgt | hle
          · exact hgt
          · obtain rfl : a = σ.len := by omega
            rw [live_cons_zero] at hL
            exact absurd hL hlive
        obtain ⟨X', hX', hag'⟩ := ih (R := R) (σ := σ1) (X := X.pushSlot W m)
          (fun i hi => by have := hR i hi; omega) hag1
          (fun k hk hl a ha => by
            have hl' : (s.live.contains (σ.len + (k + 1)) ||
                ((op :: rest)[k + 1]'(by simp; omega)).fallible) = true := by
              rw [List.getElem_cons_succ, show σ.len + (k + 1) = σ1.len + k by omega]; exact hl
            obtain ⟨hlt, hRa | ⟨hge, hL⟩⟩ := hreads0 k hk hl' a (by simpa using ha)
            · exact ⟨by omega, .inl hRa⟩
            · have hgt := hdead a hge hL
              rw [live_cons_succ hgt] at hL
              exact ⟨by omega, .inr ⟨by omega, by rw [hlen1]; exact hL⟩⟩)
          hrun
        refine ⟨X', by simp only [composeOpsAux, hX]; exact hX', hag'.retain fun i hi => ?_⟩
        rcases hi with hi | ⟨hge, hL⟩
        · exact .inl hi
        · have hgt := hdead i hge hL
          rw [live_cons_succ hgt] at hL
          exact .inr ⟨by omega, by rw [hlen1]; exact hL⟩

/-- Slots below the starting length persist, and the length does not decrease. -/
theorem composeOpsAux_slot_persist_le (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) :
    ∀ {os : List SlpOp} {st st' : ComposeState α},
      composeOpsAux n K wit W cfg pe (some st) os = some st' →
      ∀ {i : ℕ}, i < st.len → st'.slot W i = st.slot W i ∧ st.len ≤ st'.len
  | [], st, st', h, i, _ => by
    simp only [composeOpsAux, Option.some.injEq] at h; subst h; exact ⟨rfl, le_rfl⟩
  | op :: rest, st, st', h, i, hi => by
    simp only [composeOpsAux] at h
    cases hst : composeStep n K wit W cfg pe st op with
    | none => rw [hst] at h; simp [composeOpsAux] at h
    | some st1 =>
      rw [hst] at h
      obtain ⟨e, hr, hl⟩ := composeStep_push n K wit W cfg pe hst
      have hi1 : i < st1.len := by omega
      obtain ⟨h1, h2⟩ := composeOpsAux_slot_persist_le n K wit W cfg pe h hi1
      exact ⟨h1.trans (ComposeState.slot_of_cons W hr hl hi), by omega⟩

/-- Slots below the starting length persist. -/
theorem composeOpsAux_slot_persist (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) {os : List SlpOp}
    {st st' : ComposeState α} (h : composeOpsAux n K wit W cfg pe (some st) os = some st')
    {i : ℕ} (hi : i < st.len) : st'.slot W i = st.slot W i :=
  (composeOpsAux_slot_persist_le n K wit W cfg pe h hi).1

end KAM.Certificate
