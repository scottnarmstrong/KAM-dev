/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetIngest

/-!
# Staged exponentials and powers

`JetChar.lean` computes each exponential `exp(σ i 2π angleAt_j)` in one block (`jExpNode`: the
whole Taylor sum and its remainder) and its powers from the exponential itself (`jPowsAux` from
`m = 1`). On a large box (the cfgFull chain, `V2-PACKED.md` §12.12) one block of a whole Taylor sum
exceeds the memory of one process, so this file splits both:

* `TKey`: the ledger keys of a staged exponential: `w = σ i 2π angleAt_j`, the Taylor term
  `w^m / m!` and the partial sum `Σ_{i ≤ m} w^i / i!` (`tkeyFn`);
* `jTStep`, `jTSteps`: Taylor steps from any `(term, partial sum)` at `m`, the steps of `jTaylor`;
* `jExpFin`: the partial sum of degree `N` plus the remainder `jExpRem` (as `jExpNode`);
* `JBlockT` adds to `JBlockW` the blocks `tstart` (`w` and the constant `1`), `tstep` (`k` Taylor
  steps), `texp` (the exponential node) and `pows` (powers from any power `m`);
* `jChainT_sound`, `jChainT_slot`: the chain theorem over the keys `JKeyT = JKey ⊕ TKey`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- A ledger key of a staged exponential of the angle `j` with sign `σ < 0` (`neg`). -/
inductive TKey where
  | w (j : ℕ) (neg : Bool)
  | term (j : ℕ) (neg : Bool) (m : ℕ)
  | sum (j : ℕ) (neg : Bool) (m : ℕ)

/-- A ledger key of the staged chain. -/
abbrev JKeyT := JKey ⊕ TKey

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- The function of a staged-exponential key. -/
def tkeyFn (K : CertEmbedding α) : TKey → (Fin n → ℂ) → ℂ
  | .w j neg => wFn n K j neg
  | .term j neg m => fun θ => wFn n K j neg θ ^ m / (m.factorial : ℂ)
  | .sum j neg m => fun θ => expSum (wFn n K j neg θ) m

/-- The function of a ledger key of the staged chain. -/
def keyFnT (K : CertEmbedding α) (p : Slp) : JKeyT → (Fin n → ℂ) → ℂ
  | .inl k => keyFn n K p k
  | .inr t => tkeyFn n K t

/-- One Taylor step from `m` (the step of `jTaylor`): the term times `w / (m + 1)`, added to the
partial sum. -/
def jTStep (w : JNode α) (m : ℕ) (t s : JNode α) : Option (JNode α × JNode α) :=
  match jMul n W jb t w jb.P with
  | some t1 =>
    match jNorm n W jb t1, jConstQ n W pe cfg jb (1 / ((m : ℚ) + 1)) with
    | some t2, some c =>
      match jMul n W jb t2 c jb.P with
      | some t3 =>
        match jNorm n W jb t3 with
        | some t4 =>
          match jAdd n jb s t4 with
          | some s' => some (t4, s')
          | none => none
        | none => none
      | none => none
    | _, _ => none
  | none => none

/-- `k` Taylor steps from `m`. -/
def jTSteps (w : JNode α) : ℕ → ℕ → JNode α → JNode α → Option (JNode α × JNode α)
  | _, 0, t, s => some (t, s)
  | m, k + 1, t, s =>
    match jTStep n W pe cfg jb w m t s with
    | some (t', s') => jTSteps w (m + 1) k t' s'
    | none => none

/-- The exponential node from `w` and the partial sum `s` of degree `N`: `s` with the remainder
`jExpRem w N` added to its radius (the last step of `jExpNode`). -/
def jExpFin (w s : JNode α) (N : ℕ) : Option (JNode α) :=
  match jExpRem w N with
  | some rem => some ⟨s.u, s.A, s.e, s.x, upAdd s.r rem, s.nb⟩
  | none => none

end Defs

/-- A block of the staged chain. -/
inductive JBlockT (α : Type) where
  | lift (b : JBlockW α)
  | tstart (j : ℕ) (neg : Bool) (wo one : JNode α)
  | tstep (j : ℕ) (neg : Bool) (m k : ℕ) (w t s t' s' : JNode α)
  | texp (j : ℕ) (neg : Bool) (N : ℕ) (w s out : JNode α)
  | pows (j : ℕ) (neg : Bool) (m : ℕ) (base cur : JNode α) (outs : List (JNode α))

namespace JBlockT

variable {α : Type}

def imports : JBlockT α → List (JKeyT × JNode α)
  | .lift b => b.imports.map fun m => (.inl m.1, m.2)
  | .tstart .. => []
  | .tstep j neg m _ w t s _ _ =>
    [(.inr (.w j neg), w), (.inr (.term j neg m), t), (.inr (.sum j neg m), s)]
  | .texp j neg N w s _ => [(.inr (.w j neg), w), (.inr (.sum j neg N), s)]
  | .pows j neg m base cur _ => [(.inl (.inr (j, neg, 1)), base), (.inl (.inr (j, neg, m)), cur)]

def exports : JBlockT α → List (JKeyT × JNode α)
  | .lift b => b.exports.map fun m => (.inl m.1, m.2)
  | .tstart j neg wo one =>
    [(.inr (.w j neg), wo), (.inr (.term j neg 0), one), (.inr (.sum j neg 0), one)]
  | .tstep j neg m k _ _ _ t' s' =>
    [(.inr (.term j neg (m + k)), t'), (.inr (.sum j neg (m + k)), s')]
  | .texp j neg _ _ _ out => [(.inl (.inr (j, neg, 1)), out)]
  | .pows j neg m _ _ outs =>
    (List.range outs.length).zipWith (fun i o => (.inl (.inr (j, neg, m + 1 + i)), o)) outs

def isGiven : JBlockT α → Bool
  | .lift b => b.isGiven
  | _ => false

variable [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (cfg : ModelConfig α)
  (jb : JBook)

def ok (K : CertEmbedding α) (p : Slp) : JBlockT α → Bool
  | .lift b => b.ok n W pe cfg jb K p
  | .tstart j neg wo one =>
    (match jW n W pe cfg jb K j neg with
      | some x => jExportOk x wo
      | none => false) &&
    (match jConstQ n W pe cfg jb 1 with
      | some o => jExportOk o one
      | none => false)
  | .tstep _ _ m k w t s t' s' =>
    match jTSteps n W pe cfg jb w m k t s with
    | some (t1, s1) => jExportOk t1 t' && jExportOk s1 s'
    | none => false
  | .texp _ _ N w s out =>
    match jExpFin w s N with
    | some e => jExportOk e out
    | none => false
  | .pows _ _ _ base cur outs => jPowsAux n W jb base cur outs

end JBlockT

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

theorem jTStep_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {w : JNode α}
    {wf : (Fin n → ℂ) → ℂ} (hw : JEnc n W jb w wf) {m : ℕ} {t s t' s' : JNode α}
    (ht : JEnc n W jb t (fun θ => wf θ ^ m / (m.factorial : ℂ)))
    (hs : JEnc n W jb s (fun θ => expSum (wf θ) m))
    (h : jTStep n W pe cfg jb w m t s = some (t', s')) :
    JEnc n W jb t' (fun θ => wf θ ^ (m + 1) / ((m + 1).factorial : ℂ)) ∧
      JEnc n W jb s' (fun θ => expSum (wf θ) (m + 1)) := by
  unfold jTStep at h
  split at h
  · rename_i t1 h1
    split at h
    · rename_i t2 c h2 hc
      split at h
      · rename_i t3 h3
        split at h
        · rename_i t4 h4
          split at h
          · rename_i s1 hs1
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have e1 := jMul_sound hW B ht hw h1
            have e2 := jNorm_sound hW B e1 h2
            have e3 := jMul_sound hW B e2 (jConstQ_sound hW hpe B hc) h3
            have e4 := jNorm_sound hW B e3 h4
            have hterm : JEnc n W jb t4
                (fun θ => wf θ ^ (m + 1) / ((m + 1).factorial : ℂ)) :=
              PEnc.congr e4 fun θ _ => by
                rw [Nat.factorial_succ]
                push_cast
                field_simp
                ring
            refine ⟨hterm, PEnc.congr (jAdd_sound B hs hterm hs1) fun θ _ => ?_⟩
            simp only [expSum]
            rw [Finset.sum_range_succ _ (m + 1)]
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem jTSteps_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {w : JNode α}
    {wf : (Fin n → ℂ) → ℂ} (hw : JEnc n W jb w wf) :
    ∀ (k m : ℕ) {t s t' s' : JNode α},
      JEnc n W jb t (fun θ => wf θ ^ m / (m.factorial : ℂ)) →
      JEnc n W jb s (fun θ => expSum (wf θ) m) →
      jTSteps n W pe cfg jb w m k t s = some (t', s') →
      JEnc n W jb t' (fun θ => wf θ ^ (m + k) / ((m + k).factorial : ℂ)) ∧
        JEnc n W jb s' (fun θ => expSum (wf θ) (m + k))
  | 0, m, t, s, t', s', ht, hs, h => by
    simp only [jTSteps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ht, hs⟩
  | k + 1, m, t, s, t', s', ht, hs, h => by
    simp only [jTSteps] at h
    split at h
    · rename_i t1 s1 h1
      obtain ⟨ht1, hs1⟩ := jTStep_sound hW hpe B hw ht hs h1
      have := jTSteps_sound hW hpe B hw k (m + 1) ht1 hs1 h
      rwa [show m + 1 + k = m + (k + 1) by ring] at this
    · cases h

/-- **The exponential from a partial sum**: with `w` enclosing `wf` and `s` the partial sum of
degree `N`, `jExpFin` encloses `exp ∘ wf` (`Complex.exp_bound'`, as in `jExpNode_sound`). -/
theorem jExpFin_sound {w s e : JNode α} {wf : (Fin n → ℂ) → ℂ} {N : ℕ}
    (hw : JEnc n W jb w wf) (hs : JEnc n W jb s (fun θ => expSum (wf θ) N))
    (h : jExpFin w s N = some e) : JEnc n W jb e (fun θ => Complex.exp (wf θ)) := by
  unfold jExpFin at h
  split at h
  · rename_i rem hR
    simp only [Option.some.injEq] at h
    subst h
    unfold jExpRem at hR
    split_ifs at hR with hc
    simp only [Option.some.injEq] at hR
    subst hR
    obtain ⟨F, hF, hb⟩ := hs
    refine ⟨F, hF, fun θ hθ => ⟨?_, (hb θ hθ).2⟩⟩
    set x := wf θ
    have hx := PEnc.norm_le hw hθ
    have hM := LawfulCertArith.upAdd_ge w.nb w.r
    have hM0 : 0 ≤ val (upAdd w.nb w.r) := by linarith [norm_nonneg x]
    have hxM : ‖x‖ ≤ val (upAdd w.nb w.r) := by linarith
    have hq := LawfulCertArith.ofRatUp_ge (α := α) (1 / ((N : ℚ) + 2))
    have hq0 : (0 : ℝ) ≤ val (ofRatUp (1 / ((N : ℚ) + 2)) : α) :=
      le_trans (by push_cast; positivity) hq
    have hc1 := LawfulCertArith.upMul_ge _ _ hM0 hq0
    have hc2 := LawfulCertArith.ble_sound _ _ hc
    have hc3 := LawfulCertArith.ofRatDown_le (α := α) (1 / 2)
    have hqr : ((1 / ((N : ℚ) + 2) : ℚ) : ℝ) = 1 / ((N + 1).succ : ℝ) := by
      push_cast
      ring
    have hcond : ‖x‖ / ((N + 1).succ : ℝ) ≤ 1 / 2 := by
      have h4 : ‖x‖ / ((N + 1).succ : ℝ) ≤
          val (upAdd w.nb w.r) * val (ofRatUp (1 / ((N : ℚ) + 2)) : α) := by
        rw [div_eq_mul_one_div, ← hqr]
        exact mul_le_mul hxM hq (by rw [hqr]; positivity) hM0
      have h5 : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by push_cast; ring
      linarith
    have hexp := Complex.exp_bound' hcond
    obtain ⟨hP1, hP2⟩ := upPow_ge hM0 (N + 1)
    have hf := LawfulCertArith.ofRatUp_ge (α := α) (2 / ((N + 1).factorial : ℚ))
    have hf0 : (0 : ℝ) ≤ val (ofRatUp (2 / ((N + 1).factorial : ℚ)) : α) :=
      le_trans (by push_cast; positivity) hf
    have hrem := LawfulCertArith.upMul_ge _ _ hf0 hP2
    have hbound : ‖Complex.exp x - expSum x N‖ ≤
        val (upMul (ofRatUp (2 / ((N + 1).factorial : ℚ))) (upPow (upAdd w.nb w.r) (N + 1)) :
          α) := by
      refine hexp.trans ?_
      refine le_trans ?_ hrem
      have : ‖x‖ ^ (N + 1) ≤ val (upPow (upAdd w.nb w.r) (N + 1)) :=
        (pow_le_pow_left₀ (norm_nonneg x) hxM _).trans hP1
      have hfr : ((2 / ((N + 1).factorial : ℚ) : ℚ) : ℝ) = 2 / ((N + 1).factorial : ℝ) := by
        push_cast
        ring
      have h2 : (2 / ((N + 1).factorial : ℝ)) ≤
          val (ofRatUp (2 / ((N + 1).factorial : ℚ)) : α) := hfr ▸ hf
      calc ‖x‖ ^ (N + 1) / ((N + 1).factorial : ℝ) * 2
          = (2 / ((N + 1).factorial : ℝ)) * ‖x‖ ^ (N + 1) := by ring
        _ ≤ val (ofRatUp (2 / ((N + 1).factorial : ℚ)) : α) *
            val (upPow (upAdd w.nb w.r) (N + 1)) :=
          mul_le_mul h2 this (by positivity) hf0
    have hu := LawfulCertArith.upAdd_ge s.r
      (upMul (ofRatUp (2 / ((N + 1).factorial : ℚ))) (upPow (upAdd w.nb w.r) (N + 1)))
    have h1 := (hb θ hθ).1
    have hsplit : Complex.exp x - F θ / 2 ^ s.e =
        (Complex.exp x - expSum x N) + (expSum x N - F θ / 2 ^ s.e) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith
  · cases h

/-- A block of the staged chain is sound. -/
theorem JBlockT.sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {b : JBlockT α} (hok : b.ok n W pe cfg jb K p = true)
    (hgiven : b.isGiven = true → ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFnT n K p m.1))
    (himp : ∀ m ∈ b.imports, JEnc n W jb m.2 (keyFnT n K p m.1)) :
    ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFnT n K p m.1) := by
  cases b with
  | lift b0 =>
    intro m hm
    simp only [JBlockT.exports, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have himp' : ∀ m ∈ b0.imports, JEnc n W jb m.2 (keyFn n K p m.1) := by
      intro m hm
      have hmem : ((.inl m.1, m.2) : JKeyT × JNode α) ∈ (JBlockT.lift b0).imports := by
        simp only [JBlockT.imports, List.mem_map]
        exact ⟨m, hm, rfl⟩
      exact himp _ hmem
    have hg' : b0.isGiven = true → ∀ m ∈ b0.exports, JEnc n W jb m.2 (keyFn n K p m.1) := by
      intro hg m hm
      have hmem : ((.inl m.1, m.2) : JKeyT × JNode α) ∈ (JBlockT.lift b0).exports := by
        simp only [JBlockT.exports, List.mem_map]
        exact ⟨m, hm, rfl⟩
      exact hgiven hg _ hmem
    exact JBlockW.sound hW hpe B K p hok hg' himp' m0 hm0
  | tstart j neg wo one =>
    simp only [JBlockT.ok, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := hok
    have hwo : JEnc n W jb wo (wFn n K j neg) := by
      split at h1
      · rename_i x hx
        exact jExportOk_enc (jW_sound hW hpe B hx) h1
      · cases h1
    have hone : JEnc n W jb one (fun _ => (1 : ℂ)) := by
      split at h2
      · rename_i o ho
        have := jExportOk_enc (jConstQ_sound hW hpe B ho) h2
        refine PEnc.congr this fun θ _ => ?_
        simp
      · cases h2
    intro m hm
    simp only [JBlockT.exports, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact hwo
    · exact PEnc.congr hone fun θ _ => by simp [keyFnT, tkeyFn]
    · exact PEnc.congr hone fun θ _ => by simp [keyFnT, tkeyFn, expSum]
  | tstep j neg m k w t s t' s' =>
    have hw : JEnc n W jb w (wFn n K j neg) :=
      himp (.inr (.w j neg), w) (by simp [JBlockT.imports])
    have ht : JEnc n W jb t (fun θ => wFn n K j neg θ ^ m / (m.factorial : ℂ)) :=
      himp (.inr (.term j neg m), t) (by simp [JBlockT.imports])
    have hs : JEnc n W jb s (fun θ => expSum (wFn n K j neg θ) m) :=
      himp (.inr (.sum j neg m), s) (by simp [JBlockT.imports])
    simp only [JBlockT.ok] at hok
    split at hok
    · rename_i t1 s1 h1
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hx1, hx2⟩ := hok
      obtain ⟨ht1, hs1⟩ := jTSteps_sound hW hpe B hw k m ht hs h1
      intro m' hm
      simp only [JBlockT.exports, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact jExportOk_enc ht1 hx1
      · exact jExportOk_enc hs1 hx2
    · cases hok
  | texp j neg N w s out =>
    have hw : JEnc n W jb w (wFn n K j neg) :=
      himp (.inr (.w j neg), w) (by simp [JBlockT.imports])
    have hs : JEnc n W jb s (fun θ => expSum (wFn n K j neg θ) N) :=
      himp (.inr (.sum j neg N), s) (by simp [JBlockT.imports])
    simp only [JBlockT.ok] at hok
    split at hok
    · rename_i e he
      intro m hm
      simp only [JBlockT.exports, List.mem_singleton] at hm
      subst hm
      have := jExportOk_enc (jExpFin_sound hw hs he) hok
      refine PEnc.congr this fun θ _ => ?_
      simp [keyFnT, keyFn, auxFn, wFn]
    · cases hok
  | pows j neg m base cur outs =>
    have hb : JEnc n W jb base (auxFn n K j neg 1) :=
      himp (.inl (.inr (j, neg, 1)), base) (by simp [JBlockT.imports])
    have hc : JEnc n W jb cur (auxFn n K j neg m) :=
      himp (.inl (.inr (j, neg, m)), cur) (by simp [JBlockT.imports])
    simp only [JBlockT.ok] at hok
    intro m' hm
    simp only [JBlockT.exports] at hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    simp only [List.getElem_zipWith, List.getElem_range]
    have hi' : i < outs.length := by simp at hi; omega
    simpa [keyFnT, keyFn] using jPowsAux_sound hW B hb outs cur m hc hok i hi'

/-- **The staged chain**: every export of every block encloses the function of its key. -/
theorem jChainT_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlockT α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hgiven : ∀ b ∈ blocks, b.isGiven = true →
      ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFnT n K p m.1))
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFnT n K p m.1) := by
  have B := jBookOk_spec hb
  have hc := chain_sound (fun m : JKeyT × JNode α => JEnc n W jb m.2 (keyFnT n K p m.1)) blocks
    JBlockT.imports JBlockT.exports
    (fun b hbm himp => JBlockT.sound hW hpe B K p (hok b hbm) (hgiven b hbm) himp) hfirst
  intro b hbm m hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
  exact hc k hk m hm

/-- **The staged packed jet chain, end to end.** With no given block, every program slot exported
by a block has a packed model of its function at the embedding, `θ ↦ p.val n (K.eval n θ) j`. -/
theorem jChainT_slot {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlockT α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hng : ∀ b ∈ blocks, b.isGiven = false)
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ (j : ℕ) (nd : JNode α), (Sum.inl (Sum.inl j), nd) ∈ b.exports →
      JEnc n W jb nd (fun θ => p.val n (K.eval n θ) j) := by
  intro b hbm j nd hm
  exact jChainT_sound hW hpe hb K p blocks hok
    (fun b hbm hg => absurd hg (by simp [hng b hbm])) hfirst b hbm _ hm

end Sound

end KAM.CertificateSharp.Packed
