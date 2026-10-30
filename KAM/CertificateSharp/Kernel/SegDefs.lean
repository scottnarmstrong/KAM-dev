/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.Prune
public import KAM.Certificate.Model.FixedEq

/-!
# Segmented composition: definitions (SO-CSEG-A)

The data and checks of the segmented proof of `Slp.compose` (design
`docs/tracks/SO/design/SO-CSPLIT.md` §3.2–3.3, mechanism M1, and the jet bridge M0):

* Boolean equalities, tail-recursive (`&&` with the recursive call in tail position, so the kernel
  iterates): `keyBeq`, `SlpOp.beq`, `opsBeq`, `HamJet.beq` (the jet bridge), and on models
  `ccBeq`, `termsBeq`, `CertPoly.segBeq`, `CertModel.segBeq`, `pairBeq` (model and cached norm),
  `cacheBeq`, `ComposeMeta.beq`; each with its reflection lemma. Fixed-point leaves compare by
  mantissa (`instDecidableEqCertFixedSeg`).
* The untrusted checkpoint data: `ComposeMeta` (the non-slot fields of a `ComposeState`), `SegSpec`
  (one segment), `ComposeCkpt` (segments, boundary metadata, the ledger of slot pairs).
* The shadow run: `shadowStep` runs the landed `composeStep` on live or fallible operations and
  pushes a zero placeholder on dead infallible ones; `shadowRun` is its strict loop, started from
  `ComposeState.seed` (the ledger pairs at the imported slots).
* The checks: `segOk` (`segPrefixOk`: bounds, input length, reads; the shadow run; `segResultOk`:
  output metadata and exports) and `planOk` (tiling, initial metadata, ascending ledger, imports
  earlier and exported, every ledger slot exported), with `wantedOk` per projection.

Nothing here is trusted: the chain theorem `ComposeCkpt.compose_eq` (`SegChain.lean`) proves the
landed `Slp.compose` from passing checks.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

/-! ### Boolean equalities of keys, operations and jets -/

/-- Tail-recursive equality of keys. -/
def keyBeq : CertKey → CertKey → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a = b) && keyBeq as bs
  | _, _ => false

theorem eq_of_keyBeq : ∀ {k k' : CertKey}, keyBeq k k' = true → k = k'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [keyBeq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, eq_of_keyBeq h.2]
  | [], _ :: _, h => by simp [keyBeq] at h
  | _ :: _, [], h => by simp [keyBeq] at h

/-- Equality of operations. -/
def SlpOp.beq : SlpOp → SlpOp → Bool
  | .const re im d, .const re' im' d' => decide (re = re') && decide (im = im') && decide (d = d')
  | .action j, .action j' => j == j'
  | .char k, .char k' => keyBeq k k'
  | .add a b, .add a' b' => a == a' && b == b'
  | .mul a b, .mul a' b' => a == a' && b == b'
  | .exp a, .exp a' => a == a'
  | .inv a, .inv a' => a == a'
  | .sqrt a, .sqrt a' => a == a'
  | _, _ => false

theorem SlpOp.eq_of_beq {o o' : SlpOp} (h : o.beq o' = true) : o = o' := by
  cases o <;> cases o' <;>
    simp_all [SlpOp.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact eq_of_keyBeq h

/-- Tail-recursive equality of operation lists. -/
def opsBeq : List SlpOp → List SlpOp → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && opsBeq as bs
  | _, _ => false

theorem eq_of_opsBeq : ∀ {l l' : List SlpOp}, opsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [opsBeq, Bool.and_eq_true] at h
    rw [SlpOp.eq_of_beq h.1, eq_of_opsBeq h.2]
  | [], _ :: _, h => by simp [opsBeq] at h
  | _ :: _, [], h => by simp [opsBeq] at h

/-- Equality of jets: the program and the four index tables (the jet bridge M0). -/
def HamJet.beq (J J' : HamJet) : Bool :=
  opsBeq J.prog.ops J'.prog.ops && J.v0 == J'.v0 && J.d1 == J'.d1 && J.d2 == J'.d2 &&
    J.d3 == J'.d3

theorem HamJet.eq_of_beq {J J' : HamJet} (h : J.beq J' = true) : J = J' := by
  obtain ⟨⟨ops⟩, v0, d1, d2, d3⟩ := J
  obtain ⟨⟨ops'⟩, v0', d1', d2', d3'⟩ := J'
  simp only [HamJet.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rw [eq_of_opsBeq h1]

/-- Fixed-point numbers compare by mantissa. -/
instance instDecidableEqCertFixedSeg (P : ℕ) : DecidableEq (CertFixed P) := fun a b =>
  decidable_of_iff (a.m = b.m) ⟨CertFixed.eq_of_m, fun h => h ▸ rfl⟩

/-! ### Boolean equalities of models -/

section Beq

variable {α : Type} [DecidableEq α]

def ccBeq (c d : CC α) : Bool := decide (c.re = d.re) && decide (c.im = d.im)

/-- Tail-recursive equality of term lists. -/
def termsBeq : List (CertKey × CC α) → List (CertKey × CC α) → Bool
  | [], [] => true
  | t :: ts, u :: us => keyBeq t.1 u.1 && ccBeq t.2 u.2 && termsBeq ts us
  | _, _ => false

/-- Equality of polynomials (ordered terms). -/
def CertPoly.segBeq (P Q : CertPoly α) : Bool := termsBeq P.terms Q.terms

/-- Equality of models: degree, radius, polynomial. -/
def CertModel.segBeq (a b : CertModel α) : Bool :=
  decide (a.deg = b.deg) && decide (a.rad = b.rad) && a.poly.segBeq b.poly

/-- Equality of slot pairs: the model and the cached norm. -/
def pairBeq (x y : CertModel α × α) : Bool := decide (x.2 = y.2) && x.1.segBeq y.1

/-- Equality of character caches: keys, polynomials, radii, in order. -/
def cacheBeq : List (CertKey × CertPoly α × α) → List (CertKey × CertPoly α × α) → Bool
  | [], [] => true
  | e :: es, f :: fs =>
    keyBeq e.1 f.1 && decide (e.2.2 = f.2.2) && e.2.1.segBeq f.2.1 && cacheBeq es fs
  | _, _ => false

theorem eq_of_ccBeq {c d : CC α} (h : ccBeq c d = true) : c = d := by
  obtain ⟨re, im⟩ := c
  obtain ⟨re', im'⟩ := d
  simp only [ccBeq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1, h.2]

theorem eq_of_termsBeq : ∀ {l l' : List (CertKey × CC α)}, termsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [termsBeq, Bool.and_eq_true] at h
    obtain ⟨⟨hk, hc⟩, hr⟩ := h
    rw [eq_of_termsBeq hr, Prod.ext (eq_of_keyBeq hk) (eq_of_ccBeq hc)]
  | [], _ :: _, h => by simp [termsBeq] at h
  | _ :: _, [], h => by simp [termsBeq] at h

theorem CertPoly.eq_of_segBeq {P Q : CertPoly α} (h : P.segBeq Q = true) : P = Q := by
  obtain ⟨P⟩ := P
  obtain ⟨Q⟩ := Q
  rw [eq_of_termsBeq (l := P) (l' := Q) h]

theorem CertModel.eq_of_segBeq {a b : CertModel α} (h : a.segBeq b = true) : a = b := by
  obtain ⟨d, P, r⟩ := a
  obtain ⟨d', P', r'⟩ := b
  simp only [CertModel.segBeq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hP⟩ := h
  rw [CertPoly.eq_of_segBeq hP]

theorem eq_of_pairBeq {x y : CertModel α × α} (h : pairBeq x y = true) : x = y := by
  simp only [pairBeq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Prod.ext (CertModel.eq_of_segBeq h.2) h.1

theorem eq_of_cacheBeq_aux :
    ∀ {l l' : List (CertKey × CertPoly α × α)}, cacheBeq l l' = true → l = l'
  | [], [], _ => rfl
  | e :: es, f :: fs, h => by
    simp only [cacheBeq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hk, hr⟩, hP⟩, hs⟩ := h
    rw [eq_of_cacheBeq_aux hs,
      Prod.ext (eq_of_keyBeq hk) (Prod.ext (CertPoly.eq_of_segBeq hP) hr)]
  | [], _ :: _, h => by simp [cacheBeq] at h
  | _ :: _, [], h => by simp [cacheBeq] at h

theorem eq_of_cacheBeq {l l' : List (CertKey × CertPoly α × α)} (h : cacheBeq l l' = true) :
    l = l' :=
  eq_of_cacheBeq_aux h

end Beq

/-! ### Checkpoint data -/

/-- The non-slot fields of a `ComposeState`. -/
structure ComposeMeta (α : Type) where
  len : ℕ
  nExp : ℕ
  nInv : ℕ
  cache : List (CertKey × CertPoly α × α)

/-- One segment: ops `[start, stop)`; `live` the slots of the segment computed faithfully;
`imports` the ledger slots `< start` read by live ops; `exports` the ledger slots it publishes. -/
structure SegSpec where
  start : ℕ
  stop : ℕ
  live : List ℕ
  imports : List ℕ
  exports : List ℕ

/-- A checkpointed composition (untrusted data): segments, boundary metadata
(`metas.length = segs.length + 1`), and the ledger `(slot, (model, cached norm))`. -/
structure ComposeCkpt (α : Type) where
  segs : List SegSpec
  metas : List (ComposeMeta α)
  ledger : List (ℕ × (CertModel α × α))

/-- The fallible operations (always computed by the shadow run). -/
def SlpOp.fallible : SlpOp → Bool
  | .char _ | .exp _ | .inv _ | .sqrt _ => true
  | _ => false

section Chain

variable {α : Type} [CertArith α]

/-- The metadata of a state. -/
def ComposeState.stateMeta (st : ComposeState α) : ComposeMeta α :=
  ⟨st.len, st.nExp, st.nInv, st.cache⟩

/-- The ledger pair of slot `i` (first match), if any. -/
def ComposeCkpt.pairOpt (C : ComposeCkpt α) (i : ℕ) : Option (CertModel α × α) :=
  (C.ledger.find? fun e => e.1 == i).map Prod.snd

/-- The ledger pair of slot `i`; the zero entry off the ledger (the default of
`ComposeState.slot`). -/
def ComposeCkpt.pair (W : CertWeight) (C : ComposeCkpt α) (i : ℕ) : CertModel α × α :=
  (C.pairOpt i).getD (slotEntry W zeroModel)

/-- Whether slot `i` of the program `ops` is computed in segment `s`. -/
def SegSpec.liveEff (s : SegSpec) (ops : List SlpOp) (i : ℕ) : Bool :=
  s.live.contains i || (ops.getD i nopOp).fallible

/-- The operations of segment `s`. -/
def SegSpec.ops (s : SegSpec) (ops : List SlpOp) : List SlpOp :=
  (ops.drop s.start).take (s.stop - s.start)

/-- The seed of a segment: dense `rev` of length `m.len`, the ledger pair at imported slots and the
zero entry elsewhere; the metadata `m`. -/
def ComposeState.seed (W : CertWeight) (m : ComposeMeta α) (C : ComposeCkpt α)
    (imps : List ℕ) : ComposeState α :=
  { rev := (List.range m.len).reverse.map fun i =>
      if imps.contains i then C.pair W i else slotEntry W zeroModel
    len := m.len, nExp := m.nExp, nInv := m.nInv, cache := m.cache }

/-- One step of the shadow run: the landed step on live or fallible operations, a zero placeholder
on dead infallible ones. -/
def shadowStep (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (s : SegSpec) (st : ComposeState α) (op : SlpOp) :
    Option (ComposeState α) :=
  if s.live.contains st.len || op.fallible then composeStep n K wit W cfg pe st op
  else some (st.pushSlot W zeroModel)

/-- The shadow run (strict loop, as `composeOpsAux`). -/
def shadowRun (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (s : SegSpec) :
    Option (ComposeState α) → List SlpOp → Option (ComposeState α)
  | none, _ => none
  | some st, [] => some st
  | some st, op :: ops => shadowRun n K wit W cfg pe s (shadowStep n K wit W cfg pe s st op) ops

/-- Equality of metadata. -/
def ComposeMeta.beq [DecidableEq α] (m m' : ComposeMeta α) : Bool :=
  m.len == m'.len && m.nExp == m'.nExp && m.nInv == m'.nInv && cacheBeq m.cache m'.cache

omit [CertArith α] in
theorem ComposeMeta.eq_of_beq [DecidableEq α] {m m' : ComposeMeta α} (h : m.beq m' = true) :
    m = m' := by
  obtain ⟨l, e, i, c⟩ := m
  obtain ⟨l', e', i', c'⟩ := m'
  simp only [ComposeMeta.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hc⟩ := h
  rw [eq_of_cacheBeq hc]

/-- S1 and S2 with all bounds: the segment and both boundary metas exist, the input meta's length
is `start`, `start ≤ stop ≤ ops.length`, and every live or fallible operation of the segment reads
only earlier slots that are imported or computed earlier in the segment. -/
def ComposeCkpt.segPrefixOk (C : ComposeCkpt α) (ops : List SlpOp) (j : ℕ) : Bool :=
  match C.segs[j]?, C.metas[j]?, C.metas[j + 1]? with
  | some s, some m, some _ =>
    decide (m.len = s.start) && decide (s.start ≤ s.stop) && decide (s.stop ≤ ops.length) &&
      (List.range' s.start (s.stop - s.start)).all fun i =>
        !s.liveEff ops i || (opDeps (ops.getD i nopOp)).all fun a =>
          decide (a < i) && (s.imports.contains a || (decide (s.start ≤ a) && s.liveEff ops a))
  | _, _, _ => false

/-- S3 (metadata part) and S4: the output meta is `metas[j+1]`; every export lies in the segment,
is computed, and its whole pair equals its ledger pair. -/
def ComposeCkpt.segResultOk [DecidableEq α] (C : ComposeCkpt α) (W : CertWeight)
    (ops : List SlpOp) (j : ℕ) (st : ComposeState α) : Bool :=
  match C.segs[j]?, C.metas[j + 1]? with
  | some s, some m' =>
    st.stateMeta.beq m' && s.exports.all fun e =>
      decide (s.start ≤ e) && decide (e < s.stop) && s.liveEff ops e &&
        match C.pairOpt e with
        | some p => pairBeq (st.slot W e) p
        | none => false
  | _, _ => false

/-- **The segment check** (S1–S4). -/
def ComposeCkpt.segOk [DecidableEq α] (C : ComposeCkpt α) (n : ℕ) (ops : List SlpOp)
    (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (j : ℕ) : Bool :=
  C.segPrefixOk ops j &&
    match C.segs[j]?, C.metas[j]? with
    | some s, some m =>
      match shadowRun n K wit W cfg pe s (some (ComposeState.seed W m C s.imports)) (s.ops ops) with
      | some st => C.segResultOk W ops j st
      | none => false
    | _, _ => false

/-- The segments tile `[a, b)` in order. -/
def segsTile : List SegSpec → ℕ → ℕ → Bool
  | [], a, b => a == b
  | s :: ss, a, b => s.start == a && decide (s.start ≤ s.stop) && segsTile ss s.stop b

/-- Strictly increasing ledger slots. -/
def ledgerAsc {β : Type} : List (ℕ × β) → Bool
  | a :: b :: r => decide (a.1 < b.1) && ledgerAsc (b :: r)
  | _ => true

/-- Slot `a` is exported by a segment containing it. -/
def ComposeCkpt.exported (C : ComposeCkpt α) (a : ℕ) : Bool :=
  C.segs.any fun s => decide (s.start ≤ a) && decide (a < s.stop) && s.exports.contains a

/-- **The plan check** (indices only; independent of the wanted slots, so one proof serves every
projection): tiling of `[0, len)`, `metas.length = segs.length + 1`, the empty initial meta,
ascending ledger, imports earlier and exported, every ledger slot exported. -/
def ComposeCkpt.planOk (C : ComposeCkpt α) (len : ℕ) : Bool :=
  segsTile C.segs 0 len && decide (C.metas.length = C.segs.length + 1) &&
    (match C.metas[0]? with
     | some m => m.len == 0 && m.nExp == 0 && m.nInv == 0 && m.cache.isEmpty
     | none => false) &&
    ledgerAsc C.ledger &&
    (C.segs.all fun s => s.imports.all fun a => decide (a < s.start) && C.exported a) &&
    (C.ledger.all fun e => C.exported e.1)

/-- The wanted slots are on the ledger (checked per projection). -/
def ComposeCkpt.wantedOk (C : ComposeCkpt α) (wanted : List ℕ) : Bool :=
  wanted.all fun i => (C.pairOpt i).isSome

end Chain

end KAM.Certificate
