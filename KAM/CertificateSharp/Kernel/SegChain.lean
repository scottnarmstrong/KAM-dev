/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.SegAgree

/-!
# Segmented composition: the chain theorem (SO-CSEG-B)

`ComposeCkpt.compose_eq`: a checkpoint whose plan check `planOk` and every segment check `segOk`
pass, and whose ledger holds the wanted slots, gives the landed `Slp.compose` of the whole program:
`some (wanted.map fun i => (C.pair W i).1)`.

The proof is an induction over the tiling (`chain_go`). Its invariant at the start `a` of segment
`j`: the landed run on `ops.take a` succeeds with the metadata `metas[j]`, and agrees with the
ledger on the exports of the earlier segments. One segment (`seg_step`) seeds the shadow run with
the ledger pairs of its imports (`seed_agree`; the imports lie below the start,
`imports_lt_seed_len`, and were exported by an earlier segment, since every later segment starts at
or after `a`), and `shadowRun_agree` carries the agreement to its exports and its output metadata.
Nothing is evaluated: this is a statement about the landed functions.
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α]

/-! ### Lists and tilings -/

theorem composeOpsAux_none (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (l : List SlpOp) :
    composeOpsAux n K wit W cfg pe none l = none := by
  cases l <;> rfl

theorem composeOpsAux_append (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) :
    ∀ (o : Option (ComposeState α)) (l₁ l₂ : List SlpOp),
      composeOpsAux n K wit W cfg pe o (l₁ ++ l₂) =
        composeOpsAux n K wit W cfg pe (composeOpsAux n K wit W cfg pe o l₁) l₂
  | none, l₁, l₂ => by rw [composeOpsAux_none, composeOpsAux_none, composeOpsAux_none]
  | some _, [], _ => rfl
  | some st, op :: l₁, l₂ => by
    rw [List.cons_append]
    exact composeOpsAux_append n K wit W cfg pe _ l₁ l₂

theorem segsTile_cons {s : SegSpec} {ss : List SegSpec} {a b : ℕ}
    (h : segsTile (s :: ss) a b = true) :
    s.start = a ∧ s.start ≤ s.stop ∧ segsTile ss s.stop b = true := by
  simp only [segsTile, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem segsTile_start_ge : ∀ {ss : List SegSpec} {a b : ℕ}, segsTile ss a b = true →
    ∀ s ∈ ss, a ≤ s.start
  | [], _, _, _, _, hs => absurd hs List.not_mem_nil
  | s :: ss, a, b, h, t, ht => by
    obtain ⟨h1, h2, h3⟩ := segsTile_cons h
    rcases List.mem_cons.mp ht with rfl | ht
    · omega
    · have := segsTile_start_ge h3 t ht
      omega

/-- The operations of a segment, read in the program. -/
theorem SegSpec.ops_getD {s : SegSpec} {ops : List SlpOp} {k : ℕ} (hk : k < s.stop - s.start)
    (d : SlpOp) :
    (s.ops ops).getD k d = ops.getD (s.start + k) d := by
  simp only [SegSpec.ops, List.getD_eq_getElem?_getD, List.getElem?_take, hk, ↓reduceIte,
    List.getElem?_drop]

theorem SegSpec.ops_length {s : SegSpec} {ops : List SlpOp} (h : s.stop ≤ ops.length) :
    (s.ops ops).length = s.stop - s.start := by
  simp only [SegSpec.ops, List.length_take, List.length_drop]
  omega

/-- A Boolean implication. -/
theorem segBoolImp {b c : Bool} (h : (!b || c) = true) (hb : b = true) : c = true := by
  subst hb; simpa using h

/-! ### The intended caller of `shadowRun_agree` -/

/-- With `R := imports`, the plan's import bound and the prefix check's `m.len = s.start` put every
import below the seed's length (`seed_stateMeta`): the premise `hR` of `shadowRun_agree`. -/
theorem ComposeCkpt.imports_lt_seed_len (W : CertWeight) {C : ComposeCkpt α} {len : ℕ}
    {ops : List SlpOp} {j : ℕ} {s : SegSpec} {m : ComposeMeta α}
    (hplan : C.planOk len = true) (hpre : C.segPrefixOk ops j = true)
    (hs : C.segs[j]? = some s) (hm : C.metas[j]? = some m) :
    ∀ i, s.imports.contains i = true → i < (ComposeState.seed W m C s.imports).len := by
  intro i hi
  have hlen : m.len = s.start := by
    cases h1 : C.metas[j + 1]? with
    | none => simp only [ComposeCkpt.segPrefixOk, hs, hm, h1] at hpre; exact absurd hpre (by simp)
    | some m' =>
      simp only [ComposeCkpt.segPrefixOk, hs, hm, h1, Bool.and_eq_true, decide_eq_true_eq] at hpre
      exact hpre.1.1.1
  have hmem : s ∈ C.segs := List.mem_of_getElem? hs
  have hi' : i ∈ s.imports := by simpa using hi
  unfold ComposeCkpt.planOk at hplan
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hplan
  have hlt := (hplan.1.2 s hmem i hi').1
  change i < m.len
  omega

/-! ### One segment -/

/-- **One segment**: from the landed run at its start (metadata `metas[j]`, the ledger pairs at the
imports) to the landed run at its stop (metadata `metas[j+1]`, the ledger pairs at the exports). -/
theorem ComposeCkpt.seg_step [DecidableEq α] {C : ComposeCkpt α} {n : ℕ} {ops : List SlpOp}
    {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {len : ℕ} (hplan : C.planOk len = true) {j : ℕ} {s : SegSpec}
    {X : ComposeState α} (hs : C.segs[j]? = some s) (hm : C.metas[j]? = some X.stateMeta)
    (hX : composeOps n K wit W cfg pe (ops.take s.start) = some X)
    (himp : ∀ a, s.imports.contains a = true → X.slot W a = C.pair W a)
    (hseg : C.segOk n ops K wit W cfg pe j = true) :
    ∃ Y, composeOps n K wit W cfg pe (ops.take s.stop) = some Y ∧
      C.metas[j + 1]? = some Y.stateMeta ∧
      (∀ e ∈ s.exports, Y.slot W e = C.pair W e ∧ e < s.stop) ∧
      (∀ i < s.start, Y.slot W i = X.slot W i) ∧ Y.len = s.stop := by
  have hseg' := hseg
  simp only [ComposeCkpt.segOk, Bool.and_eq_true, hs, hm] at hseg'
  obtain ⟨hpre, hrun⟩ := hseg'
  -- the prefix check: the next meta, the lengths, the reads
  cases h1 : C.metas[j + 1]? with
  | none => simp only [ComposeCkpt.segPrefixOk, hs, hm, h1] at hpre; exact absurd hpre (by simp)
  | some m' =>
  have hpre' := hpre
  simp only [ComposeCkpt.segPrefixOk, hs, hm, h1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpre'
  obtain ⟨⟨⟨hXlen, hss⟩, hstop⟩, hreads⟩ := hpre'
  change X.len = s.start at hXlen
  -- the shadow run
  set σ := ComposeState.seed W X.stateMeta C s.imports with hσ
  cases hr : shadowRun n K wit W cfg pe s (some σ) (s.ops ops) with
  | none => rw [hr] at hrun; exact absurd hrun (by simp)
  | some st =>
  rw [hr] at hrun
  have hσlen : σ.len = s.start := hXlen
  have hlenOs := SegSpec.ops_length (s := s) hstop
  have hstlen : st.len = s.stop := by
    rw [shadowRun_len n K wit W cfg pe s hr, hσlen, hlenOs]; omega
  -- agreement of the seed with the landed state on the imports
  have hagree : σ.AgreeOn W (fun a => s.imports.contains a = true) X :=
    seed_agree W C rfl fun a ha _ => himp a ha
  have hR := ComposeCkpt.imports_lt_seed_len W hplan hpre hs hm
  obtain ⟨X', hX', hag⟩ := shadowRun_agree n K wit W cfg pe s hR hagree (fun k hk hl a ha => by
    rw [hσlen] at hl ⊢
    have hk' : k < s.stop - s.start := hlenOs ▸ hk
    have hget : (s.ops ops)[k] = ops.getD (s.start + k) nopOp := by
      rw [← SegSpec.ops_getD hk' nopOp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    rw [hget] at hl ha
    have hi := hreads (s.start + k) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hdeps := segBoolImp hi (by simpa [SegSpec.liveEff] using hl)
    rw [List.all_eq_true] at hdeps
    have hd := hdeps a ha
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hd
    obtain ⟨hlt, hd⟩ := hd
    refine ⟨hlt, ?_⟩
    rcases hd with hd | ⟨hge, hL⟩
    · exact .inl hd
    · refine .inr ⟨hge, ?_⟩
      rw [SegSpec.ops_getD (by omega) nopOp, show s.start + (a - s.start) = a by omega]
      exact hL) hr
  -- the landed run on the segment
  have hY : composeOps n K wit W cfg pe (ops.take s.stop) = some X' := by
    rw [show s.stop = s.start + (s.stop - s.start) by omega, List.take_add]
    unfold composeOps at hX ⊢
    rw [composeOpsAux_append, hX]
    exact hX'
  -- the result check
  simp only [ComposeCkpt.segResultOk, hs, h1, Bool.and_eq_true, List.all_eq_true] at hrun
  obtain ⟨hmeta, hexp⟩ := hrun
  have hmeta' := ComposeMeta.eq_of_beq hmeta
  have hX'meta : X'.stateMeta = st.stateMeta := by
    simp only [ComposeState.stateMeta, ComposeMeta.mk.injEq]
    exact ⟨hag.1.symm, hag.2.1.symm, hag.2.2.1.symm, hag.2.2.2.1.symm⟩
  refine ⟨X', hY, by rw [hX'meta, hmeta'], fun e he => ?_, fun i hi => ?_, ?_⟩
  · have he' := hexp e he
    simp only [decide_eq_true_eq] at he'
    obtain ⟨⟨⟨hge, hlt⟩, hlive⟩, hp⟩ := he'
    cases hpo : C.pairOpt e with
    | none => rw [hpo] at hp; exact absurd hp (by simp)
    | some p =>
    rw [hpo] at hp
    have hst := eq_of_pairBeq hp
    have hT : s.start ≤ e ∧ (s.live.contains e ||
        ((s.ops ops).getD (e - σ.len) nopOp).fallible) = true := by
      rw [hσlen, SegSpec.ops_getD (by omega) nopOp, show s.start + (e - s.start) = e by omega]
      exact ⟨hge, hlive⟩
    have := hag.2.2.2.2 e (.inr (hσlen ▸ hT)) (by omega)
    refine ⟨?_, hlt⟩
    rw [← this, hst, ComposeCkpt.pair, hpo, Option.getD_some]
  · exact composeOpsAux_slot_persist n K wit W cfg pe hX' (by omega)
  · rw [← hag.1, hstlen]

/-! ### The chain -/

/-- The induction over the remaining segments. -/
theorem ComposeCkpt.chain_go [DecidableEq α] {C : ComposeCkpt α} {n : ℕ} {ops : List SlpOp}
    {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {len : ℕ} (hplan : C.planOk len = true)
    (hseg : ∀ j < C.segs.length, C.segOk n ops K wit W cfg pe j = true) :
    ∀ (k j a : ℕ) (X : ComposeState α), j + k = C.segs.length →
      segsTile (C.segs.drop j) a len = true →
      composeOps n K wit W cfg pe (ops.take a) = some X → C.metas[j]? = some X.stateMeta →
      X.len = a → (∀ s ∈ C.segs.take j, ∀ e ∈ s.exports, e < a ∧ X.slot W e = C.pair W e) →
      ∃ Y, composeOps n K wit W cfg pe (ops.take len) = some Y ∧
        ∀ s ∈ C.segs, ∀ e ∈ s.exports, Y.slot W e = C.pair W e
  | 0, j, a, X, hjk, htile, hX, _, _, hinv => by
    rw [Nat.add_zero] at hjk
    rw [hjk, List.drop_length] at htile
    simp only [segsTile, beq_iff_eq] at htile
    subst htile
    refine ⟨X, hX, fun s hs e he => (hinv s ?_ e he).2⟩
    rwa [hjk, List.take_length]
  | k + 1, j, a, X, hjk, htile, hX, hm, hXlen, hinv => by
    have hj : j < C.segs.length := by omega
    rw [List.drop_eq_getElem_cons hj] at htile
    obtain ⟨hstart, hss, hrest⟩ := segsTile_cons htile
    have hs : C.segs[j]? = some C.segs[j] := List.getElem?_eq_getElem hj
    -- the imports were exported by an earlier segment
    have himp : ∀ b, C.segs[j].imports.contains b = true → X.slot W b = C.pair W b := by
      intro b hb
      have hb' : b ∈ C.segs[j].imports := by simpa using hb
      unfold ComposeCkpt.planOk at hplan
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hplan
      obtain ⟨hblt, hbex⟩ := hplan.1.2 _ (List.getElem_mem hj) b hb'
      simp only [ComposeCkpt.exported, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hbex
      obtain ⟨t, ht, ⟨htb, hbt⟩, hbe⟩ := hbex
      have ht' : t ∈ C.segs.take j ++ C.segs.drop j := by rwa [List.take_append_drop]
      rcases List.mem_append.mp ht' with ht' | ht'
      · exact (hinv t ht' b (by simpa using hbe)).2
      · have := segsTile_start_ge htile t (by rwa [← List.drop_eq_getElem_cons hj])
        omega
    obtain ⟨Y, hY, hYm, hYe, hYp, hYlen⟩ := ComposeCkpt.seg_step hplan hs hm
      (by rw [hstart]; exact hX) himp (hseg j hj)
    refine ComposeCkpt.chain_go hplan hseg k (j + 1) _ Y (by omega)
      (by rw [← List.drop_drop]; simp only [List.drop_one, List.drop_eq_getElem_cons hj,
        List.tail_cons]; exact hrest) hY hYm hYlen ?_
    intro t ht e he
    rw [List.take_add_one, hs, Option.toList_some] at ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨hlt, hslot⟩ := hinv t ht e he
      refine ⟨by omega, ?_⟩
      rw [hYp e (by omega), hslot]
    · rw [List.mem_singleton] at ht
      subst ht
      exact ⟨(hYe e he).2, (hYe e he).1⟩

/-- **The chain theorem.** -/
theorem ComposeCkpt.compose_eq [DecidableEq α] (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (C : ComposeCkpt α)
    {p : Slp} {wanted : List ℕ} (hplan : C.planOk p.ops.length = true)
    (hseg : ∀ j < C.segs.length, C.segOk n p.ops K wit W cfg pe j = true)
    (hw : C.wantedOk wanted = true) :
    Slp.compose n p K wit W cfg pe wanted = some (wanted.map fun i => (C.pair W i).1) := by
  have hplan' := hplan
  unfold ComposeCkpt.planOk at hplan'
  simp only [Bool.and_eq_true, List.all_eq_true] at hplan'
  obtain ⟨⟨⟨⟨⟨htile, -⟩, hm0⟩, -⟩, -⟩, hled⟩ := hplan'
  cases h0 : C.metas[0]? with
  | none => rw [h0] at hm0; exact absurd hm0 (by simp)
  | some m0 =>
  rw [h0] at hm0
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hm0
  obtain ⟨⟨⟨hl0, he0⟩, hi0⟩, hc0⟩ := hm0
  have hinit : m0 = (⟨[], 0, 0, 0, []⟩ : ComposeState α).stateMeta := by
    obtain ⟨l, e, i, c⟩ := m0
    simp only at hl0 he0 hi0 hc0
    subst hl0 he0 hi0 hc0
    rfl
  obtain ⟨Y, hY, hYe⟩ := ComposeCkpt.chain_go (ops := p.ops) hplan hseg C.segs.length 0 0
    ⟨[], 0, 0, 0, []⟩ (by omega) (by rw [List.drop_zero]; exact htile)
    (by rw [List.take_zero]; rfl) (by rw [h0, hinit]) rfl (by simp)
  rw [List.take_length] at hY
  unfold Slp.compose
  rw [hY]
  dsimp only
  congr 1
  refine List.map_congr_left fun i hi => ?_
  -- a wanted slot is on the ledger, hence exported by a segment
  have hwi : (C.pairOpt i).isSome = true := List.all_eq_true.mp hw i hi
  cases hf : C.ledger.find? (fun e => e.1 == i) with
  | none => simp [ComposeCkpt.pairOpt, hf] at hwi
  | some e =>
  have hei : e.1 = i := by simpa using List.find?_some hf
  have hex := hled e (List.mem_of_find?_eq_some hf)
  simp only [ComposeCkpt.exported, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hex
  obtain ⟨t, ht, -, hte⟩ := hex
  rw [hei] at hte
  rw [hYe t ht i (by simpa using hte)]

end KAM.Certificate
