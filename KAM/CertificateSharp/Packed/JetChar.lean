/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetChain

/-!
# Packed characters

The character slot `char k` has the value `exp(i modePhase k (K θ).1)`, which is
`χ_k(θ) · ∏_j exp(σ_j i 2π angleAt_j(θ))^{|k_j|}` (`σ_j` the sign of `k_j`; the landed
`exp_I_modePhase_eval`). The packed chain computes it from the angle displacements alone:

* `jW`: the node of `w = σ i 2π angleAt_j` (the landed angle model packed by `jLeaf`, times the
  constant `σ i 2π`);
* `jTaylor`: the terms `w^m / m!` and the partial sums, by node products, constants `1/m` and sums;
  `jExpNode` adds the Taylor remainder `2 ‖w‖^{N+1}/(N+1)!` (`Complex.exp_bound'`, with
  `‖w‖ ≤ nb + r`) to the radius: a node of `exp(w)`;
* the powers `exp(w)^m` by node products (`jPowsAux`);
* `jCharsOk`: each character slot as the unit at `k` times the powers.

The ledger keys are the program slots and the auxiliary powers `(j, σ, m)`
(`keyFn`); `JBlockX` adds the three block kinds to `JBlock`, and `jChainX_sound_of_given` is the
chain theorem over both kinds of keys.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- A ledger key: a program slot, or an auxiliary power `(j, σ < 0, m)`. -/
abbrev JKey := ℕ ⊕ (ℕ × Bool × ℕ)

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- `exp(σ i 2π angleAt_j)^m`. -/
def auxFn (K : CertEmbedding α) (j : ℕ) (neg : Bool) (m : ℕ) (θ : Fin n → ℂ) : ℂ :=
  Complex.exp ((if neg then -1 else 1) * (Complex.I * (2 * (Real.pi : ℂ) * K.angleAt n j θ))) ^ m

/-- The function of a ledger key. -/
def keyFn (K : CertEmbedding α) (p : Slp) : JKey → (Fin n → ℂ) → ℂ
  | .inl j => embFn n K p j
  | .inr (j, neg, m) => auxFn n K j neg m

/-- A node above the scale `2^P` reduced to it. -/
def jNorm (nd : JNode α) : Option (JNode α) :=
  if jb.P < nd.e then jRed n W jb nd jb.P else some nd

/-- The constant `q` on the one-slot layout. -/
def jConstQ (q : ℚ) : Option (JNode α) := jLeaf W pe cfg jb true jb.aC (constModel n q 0 0)

/-- The landed model of the angle displacement `j`. -/
def angleModel (K : CertEmbedding α) (j : ℕ) : CertModel α :=
  realCompModel n (K.angleDeg.getD j 0) K.angle[j]?

/-- The node of `σ i 2π angleAt_j`. -/
def jW (K : CertEmbedding α) (j : ℕ) (neg : Bool) : Option (JNode α) :=
  match jLeaf W pe cfg jb false (2 ^ jb.lb) (angleModel n K j),
      jLeaf W pe cfg jb true jb.aC (constModel n 0 (if neg then -1 else 1) 1) with
  | some A, some c =>
    match jMul n W jb c A jb.P with
    | some m => jNorm n W jb m
    | none => none
  | _, _ => none

/-- After `m` steps: the term `w^m / m!` and the partial sum `Σ_{i ≤ m} w^i / i!`. -/
def jTaylor (w : JNode α) : ℕ → Option (JNode α × JNode α)
  | 0 =>
    match jConstQ n W pe cfg jb 1 with
    | some o => some (o, o)
    | none => none
  | m + 1 =>
    match jTaylor w m with
    | some (t, s) =>
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
    | none => none

/-- `M^k` rounded up. -/
def upPow (M : α) : ℕ → α
  | 0 => ofInt 1
  | k + 1 => upMul (upPow M k) M

/-- The Taylor remainder after the terms `m ≤ N`, when `‖w‖ / (N + 2) ≤ 1/2`. -/
def jExpRem (w : JNode α) (N : ℕ) : Option α :=
  if ble (upMul (upAdd w.nb w.r) (ofRatUp (1 / ((N : ℚ) + 2)))) (ofRatDown (1 / 2)) then
    some (upMul (ofRatUp (2 / ((N + 1).factorial : ℚ))) (upPow (upAdd w.nb w.r) (N + 1)))
  else none

/-- **The node of `exp(σ i 2π angleAt_j)`** (Taylor polynomial of degree `N` and remainder). -/
def jExpNode (K : CertEmbedding α) (j : ℕ) (neg : Bool) (N : ℕ) : Option (JNode α) :=
  match jW n W pe cfg jb K j neg with
  | some w =>
    match jTaylor n W pe cfg jb w N, jExpRem w N with
    | some (_, s), some rem => some ⟨s.u, s.A, s.e, s.x, upAdd s.r rem, s.nb⟩
    | _, _ => none
  | none => none

/-- The powers `base^2, base^3, …` against the ledger entries `outs` (each product from the
previous entry). -/
def jPowsAux (base : JNode α) : JNode α → List (JNode α) → Bool
  | _, [] => true
  | cur, o :: os =>
    match jMul n W jb cur base jb.P with
    | some c =>
      match jNorm n W jb c with
      | some c' => jExportOk c' o && jPowsAux base o os
      | none => false
    | none => false

/-- The unit at the key `k` (the character `χ_k`). -/
def unitModel (k : CertKey) : CertModel α := ⟨0, ⟨[(padKey n k, ⟨ofInt 1, ofInt 0⟩)]⟩, ofInt 0⟩

/-- The factor of the coordinate `i` of the key `k`: the power from the ledger, `1` at `0`. -/
def jFactor (facs : List (JKey × JNode α)) (k : CertKey) (i : ℕ) : Option (JNode α) :=
  if k.getD i 0 = 0 then jConstQ n W pe cfg jb 1
  else facs.lookup (.inr (i, decide (k.getD i 0 < 0), (k.getD i 0).natAbs))

/-- `χ_k · ∏_{i < m} factor_i`. -/
def jCharProd (facs : List (JKey × JNode α)) (k : CertKey) : ℕ → Option (JNode α)
  | 0 => jLeaf W pe cfg jb false (2 ^ jb.lb) (unitModel n k)
  | m + 1 =>
    match jCharProd facs k m, jFactor n W pe cfg jb facs k m with
    | some a, some f =>
      match jMul n W jb a f jb.P with
      | some c => jNorm n W jb c
      | none => none
    | _, _ => none

/-- **The character block**: every entry is a character slot, packed from the factors. -/
def jCharsOk (p : Slp) (facs : List (JKey × JNode α)) (es : List (ℕ × JNode α)) : Bool :=
  es.all fun m =>
    match p.ops.getD m.1 (.const 0 0 0) with
    | .char k =>
      decide (m.1 < p.ops.length) &&
        match jCharProd n W pe cfg jb facs k n with
        | some nd => jExportOk nd m.2
        | none => false
    | _ => false

end Defs

/-- A block of the extended chain. -/
inductive JBlockX (α : Type) where
  | base (b : JBlock α)
  | expo (j : ℕ) (neg : Bool) (N : ℕ) (out : JNode α)
  | pows (j : ℕ) (neg : Bool) (base : JNode α) (outs : List (JNode α))
  | chars (facs : List (JKey × JNode α)) (entries : List (ℕ × JNode α))

namespace JBlockX

variable {α : Type}

def imports : JBlockX α → List (JKey × JNode α)
  | .base b => b.imports.map fun m => (.inl m.1, m.2)
  | .expo .. => []
  | .pows j neg b0 _ => [(.inr (j, neg, 1), b0)]
  | .chars facs _ => facs

def exports : JBlockX α → List (JKey × JNode α)
  | .base b => b.exports.map fun m => (.inl m.1, m.2)
  | .expo j neg _ out => [(.inr (j, neg, 1), out)]
  | .pows j neg _ outs =>
    (List.range outs.length).zipWith (fun i o => (.inr (j, neg, i + 2), o)) outs
  | .chars _ es => es.map fun m => (.inl m.1, m.2)

def isGiven : JBlockX α → Bool
  | .base b => b.isGiven
  | _ => false

variable [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (cfg : ModelConfig α)
  (jb : JBook)

def ok (K : CertEmbedding α) (p : Slp) : JBlockX α → Bool
  | .base b => b.ok n W pe cfg jb K p
  | .expo j neg N out =>
    match jExpNode n W pe cfg jb K j neg N with
    | some e => jExportOk e out
    | none => false
  | .pows _ _ b0 outs => jPowsAux n W jb b0 b0 outs
  | .chars facs es => jCharsOk n W pe cfg jb p facs es

end JBlockX

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

omit [LawfulCertArith α] in
/-- A packed model bounds its function by the norm bound plus the radius. -/
theorem PEnc.norm_le {L : PackLayout} {A e : ℕ} {x : PC} {r nb : α} {ρ : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hx : PEnc L A e x r nb n ρ f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) : ‖f θ‖ ≤ val r + val nb := by
  obtain ⟨F, -, hb⟩ := hx
  obtain ⟨h1, h2⟩ := hb θ hθ
  have := norm_add_le (f θ - F θ / 2 ^ e) (F θ / 2 ^ e)
  rw [sub_add_cancel] at this
  linarith

theorem jNorm_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {nd nd' : JNode α} {f : (Fin n → ℂ) → ℂ} (hx : JEnc n W jb nd f)
    (h : jNorm n W jb nd = some nd') : JEnc n W jb nd' f := by
  unfold jNorm at h
  split_ifs at h
  · exact jRed_sound hW B hx h
  · cases h
    exact hx

theorem jConstQ_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {q : ℚ} {c : JNode α}
    (h : jConstQ n W pe cfg jb q = some c) : JEnc n W jb c (fun _ => (q : ℂ)) := by
  have := jLeaf_sound hW hpe B (constModel_encloses n W.rho q 0 0) h
  refine PEnc.congr this fun θ _ => ?_
  simp [slpConstVal]

/-- The function of `jW`. -/
def wFn (n : ℕ) (K : CertEmbedding α) (j : ℕ) (neg : Bool) (θ : Fin n → ℂ) : ℂ :=
  (if neg then -1 else 1) * (Complex.I * (2 * (Real.pi : ℂ) * K.angleAt n j θ))

theorem jW_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {K : CertEmbedding α} {j : ℕ}
    {neg : Bool} {w : JNode α} (h : jW n W pe cfg jb K j neg = some w) :
    JEnc n W jb w (wFn n K j neg) := by
  unfold jW at h
  split at h
  · rename_i A c hA hc
    split at h
    · rename_i m hm
      have hA' := jLeaf_sound hW hpe B (realCompModel_encloses (α := α) n W.rho
        (K.angleDeg.getD j 0) K.angle[j]?) hA
      have hc' := jLeaf_sound hW hpe B (constModel_encloses (α := α) n W.rho 0
        (if neg then -1 else 1) 1) hc
      have := jNorm_sound hW B (jMul_sound hW B hc' hA' hm) h
      refine PEnc.congr this fun θ _ => ?_
      simp only [wFn, slpConstVal, CertEmbedding.angleAt]
      cases neg <;> simp <;> ring
    · cases h
  · cases h

/-- The partial sums of the exponential series. -/
def expSum (x : ℂ) (m : ℕ) : ℂ := ∑ i ∈ Finset.range (m + 1), x ^ i / (i.factorial : ℂ)

theorem jTaylor_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {w : JNode α}
    {wf : (Fin n → ℂ) → ℂ} (hw : JEnc n W jb w wf) :
    ∀ (m : ℕ) {t s : JNode α}, jTaylor n W pe cfg jb w m = some (t, s) →
      JEnc n W jb t (fun θ => wf θ ^ m / (m.factorial : ℂ)) ∧
        JEnc n W jb s (fun θ => expSum (wf θ) m)
  | 0, t, s, h => by
    simp only [jTaylor] at h
    split at h
    · rename_i o ho
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := jConstQ_sound hW hpe B ho
      refine ⟨PEnc.congr this fun θ _ => ?_, PEnc.congr this fun θ _ => ?_⟩
      · simp
      · simp [expSum]
    · cases h
  | m + 1, t, s, h => by
    simp only [jTaylor] at h
    split at h
    · rename_i t0 s0 h0
      obtain ⟨ht0, hs0⟩ := jTaylor_sound hW hpe B hw m h0
      split at h
      · rename_i t1 h1
        split at h
        · rename_i t2 c h2 hc
          split at h
          · rename_i t3 h3
            split at h
            · rename_i t4 h4
              split at h
              · rename_i s' hs'
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have e1 := jMul_sound hW B ht0 hw h1
                have e2 := jNorm_sound hW B e1 h2
                have e3 := jMul_sound hW B e2 (jConstQ_sound hW hpe B hc) h3
                have e4 := jNorm_sound hW B e3 h4
                have hterm : JEnc n W jb t4 (fun θ => wf θ ^ (m + 1) / ((m + 1).factorial : ℂ)) :=
                  PEnc.congr e4 fun θ _ => by
                    rw [Nat.factorial_succ]
                    push_cast
                    field_simp
                    ring
                refine ⟨hterm, PEnc.congr (jAdd_sound B hs0 hterm hs') fun θ _ => ?_⟩
                simp only [expSum]
                rw [Finset.sum_range_succ _ (m + 1)]
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h

theorem upPow_ge {M : α} (hM : 0 ≤ val M) :
    ∀ k : ℕ, val M ^ k ≤ val (upPow M k) ∧ 0 ≤ val (upPow M k)
  | 0 => by simp [upPow, LawfulCertArith.val_ofInt]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := upPow_ge hM k
    have h3 := LawfulCertArith.upMul_ge (upPow M k) M h2 hM
    refine ⟨?_, ?_⟩
    · simp only [upPow]
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right h1 hM).trans h3
    · simp only [upPow]
      exact (mul_nonneg h2 hM).trans h3

/-- **The exponential node.** -/
theorem jExpNode_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {K : CertEmbedding α} {j : ℕ}
    {neg : Bool} {N : ℕ} {e : JNode α} (h : jExpNode n W pe cfg jb K j neg N = some e) :
    JEnc n W jb e (auxFn n K j neg 1) := by
  unfold jExpNode at h
  split at h
  · rename_i w hw
    have hw' := jW_sound hW hpe B hw
    split at h
    · rename_i t0 s0 rem hT hR
      simp only [Option.some.injEq] at h
      subst h
      have hs := (jTaylor_sound hW hpe B hw' N hT).2
      unfold jExpRem at hR
      split_ifs at hR with hc
      simp only [Option.some.injEq] at hR
      subst hR
      obtain ⟨F, hF, hb⟩ := hs
      refine ⟨F, hF, fun θ hθ => ⟨?_, (hb θ hθ).2⟩⟩
      set x := wFn n K j neg θ
      have hx := PEnc.norm_le hw' hθ
      have hM := LawfulCertArith.upAdd_ge w.nb w.r
      have hnb := (PEnc.nonneg hw' hθ)
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
        have h2 : (2 / ((N + 1).factorial : ℝ)) ≤ val (ofRatUp (2 / ((N + 1).factorial : ℚ)) : α) :=
          hfr ▸ hf
        calc ‖x‖ ^ (N + 1) / ((N + 1).factorial : ℝ) * 2
            = (2 / ((N + 1).factorial : ℝ)) * ‖x‖ ^ (N + 1) := by ring
          _ ≤ val (ofRatUp (2 / ((N + 1).factorial : ℚ)) : α) *
              val (upPow (upAdd w.nb w.r) (N + 1)) :=
            mul_le_mul h2 this (by positivity) hf0
      have hu := LawfulCertArith.upAdd_ge s0.r
        (upMul (ofRatUp (2 / ((N + 1).factorial : ℚ))) (upPow (upAdd w.nb w.r) (N + 1)))
      have h1 := (hb θ hθ).1
      have hsplit : auxFn n K j neg 1 θ - F θ / 2 ^ s0.e =
          (Complex.exp x - expSum x N) + (expSum x N - F θ / 2 ^ s0.e) := by
        simp only [auxFn, pow_one, x, wFn]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      simp only [x] at hbound
      linarith
    · cases h
  · cases h

theorem jPowsAux_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {K : CertEmbedding α} {j : ℕ} {neg : Bool} {base : JNode α}
    (hb : JEnc n W jb base (auxFn n K j neg 1)) :
    ∀ (outs : List (JNode α)) (cur : JNode α) (m : ℕ), JEnc n W jb cur (auxFn n K j neg m) →
      jPowsAux n W jb base cur outs = true →
      ∀ i (hi : i < outs.length), JEnc n W jb outs[i] (auxFn n K j neg (m + 1 + i))
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | o :: os, cur, m, hc, h, i, hi => by
    simp only [jPowsAux] at h
    split at h
    · rename_i c hcm
      split at h
      · rename_i c' hc'
        simp only [Bool.and_eq_true] at h
        obtain ⟨hex, hrest⟩ := h
        have e1 := jNorm_sound hW B (jMul_sound hW B hc hb hcm) hc'
        have ho : JEnc n W jb o (auxFn n K j neg (m + 1)) := by
          simp only [jExportOk, Bool.and_eq_true, beq_iff_eq] at hex
          obtain ⟨⟨⟨⟨⟨⟨hu, hA⟩, he⟩, hre⟩, him⟩, hr⟩, hnb⟩ := hex
          have hx : c'.x = o.x := by
            cases hx1 : c'.x
            cases hx2 : o.x
            rw [hx1, hx2] at hre him
            simp only at hre him
            rw [hre, him]
          unfold JEnc at e1 ⊢
          rw [hu, hA, he, hx] at e1
          refine (e1.weaken (LawfulCertArith.ble_sound _ _ hr)
            (LawfulCertArith.ble_sound _ _ hnb)).congr fun θ _ => ?_
          simp only [auxFn]
          ring
        cases i with
        | zero => simpa using ho
        | succ i =>
          have := jPowsAux_sound hW B hb os o (m + 1) ho hrest i (by simpa using hi)
          simpa [show m + 1 + 1 + i = m + 1 + (i + 1) by ring] using this
      · cases h
    · cases h

omit [CertArith α] [LawfulCertArith α] in
theorem mem_of_lookupK {κ β : Type} [BEq κ] [LawfulBEq κ] {st : List (κ × β)} {a : κ} {x : β}
    (h : st.lookup a = some x) : (a, x) ∈ st := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- An exported entry encloses what its computed node encloses. -/
theorem jExportOk_enc {nd m : JNode α} {f : (Fin n → ℂ) → ℂ} (hnd : JEnc n W jb nd f)
    (h : jExportOk nd m = true) : JEnc n W jb m f := by
  simp only [jExportOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, hA⟩, he⟩, hre⟩, him⟩, hr⟩, hnb⟩ := h
  have hx : nd.x = m.x := by
    cases hx1 : nd.x
    cases hx2 : m.x
    rw [hx1, hx2] at hre him
    simp only at hre him
    rw [hre, him]
  unfold JEnc at hnd ⊢
  rw [hu, hA, he, hx] at hnd
  exact hnd.weaken (LawfulCertArith.ble_sound _ _ hr) (LawfulCertArith.ble_sound _ _ hnb)

omit [LawfulCertArith α] in
theorem unitModel_encloses [LawfulCertArith α] (k : CertKey) (ρ : ℝ) :
    (unitModel n k : CertModel α).Encloses n ρ (character (certKeyFun n k)) := by
  intro θ _
  have h1 : (⟨ofInt 1, ofInt 0⟩ : CC α).toC = 1 := by
    simp [CC.toC, LawfulCertArith.val_ofInt, Complex.ext_iff]
  simp [unitModel, CertPoly.eval, h1, LawfulCertArith.val_ofInt, certKeyFun_padKey]

/-- The factor of the coordinate `i` of the key `k`. -/
def charFac (n : ℕ) (K : CertEmbedding α) (k : CertKey) (i : ℕ) (θ : Fin n → ℂ) : ℂ :=
  if k.getD i 0 = 0 then 1 else auxFn n K i (decide (k.getD i 0 < 0)) (k.getD i 0).natAbs θ

omit [LawfulCertArith α] in
theorem charExpFun_prod (K : CertEmbedding α) (k : CertKey) (θ : Fin n → ℂ) :
    charExpFun n K k θ = ∏ i ∈ Finset.range n, charFac n K k i θ := by
  rw [← Fin.prod_univ_eq_prod_range (fun i => charFac n K k i θ)]
  unfold charExpFun modePhase
  rw [Finset.mul_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [certKeyFun, charFac]
  split_ifs with h0
  · rw [h0]
    simp
  · unfold auxFn
    rw [← Complex.exp_nat_mul]
    congr 1
    rcases lt_or_gt_of_ne h0 with hlt | hgt
    · have hc : ((k.getD i.val 0).natAbs : ℂ) = -((k.getD i.val 0 : ℤ) : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_neg hlt]
        push_cast
        ring
      simp only [hlt, decide_true, ↓reduceIte, hc]
      ring
    · have hc : ((k.getD i.val 0).natAbs : ℂ) = ((k.getD i.val 0 : ℤ) : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_pos hgt]
      have hn : ¬ k.getD i.val 0 < 0 := not_lt.mpr hgt.le
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, hc]
      ring

theorem jCharProd_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {K : CertEmbedding α} {p : Slp}
    {facs : List (JKey × JNode α)} (hfacs : ∀ m ∈ facs, JEnc n W jb m.2 (keyFn n K p m.1))
    (k : CertKey) :
    ∀ (m : ℕ) {nd : JNode α}, jCharProd n W pe cfg jb facs k m = some nd →
      JEnc n W jb nd (fun θ => character (certKeyFun n k) θ * ∏ i ∈ Finset.range m,
        charFac n K k i θ)
  | 0, nd, h => by
    have := jLeaf_sound hW hpe B (unitModel_encloses (α := α) k W.rho) h
    exact PEnc.congr this fun θ _ => by simp
  | m + 1, nd, h => by
    simp only [jCharProd] at h
    split at h
    · rename_i a f ha hf
      split at h
      · rename_i c hc
        have hA := jCharProd_sound hW hpe B hfacs k m ha
        have hF : JEnc n W jb f (charFac n K k m) := by
          unfold jFactor at hf
          split_ifs at hf with h0
          · exact PEnc.congr (jConstQ_sound hW hpe B hf) fun θ _ => by
              simp only [charFac, h0, ↓reduceIte, Rat.cast_one]
          · have := hfacs _ (mem_of_lookupK hf)
            exact PEnc.congr this fun θ _ => by
              simp only [keyFn, charFac, h0, ↓reduceIte]
        have := jNorm_sound hW B (jMul_sound hW B hA hF hc) h
        refine PEnc.congr this fun θ _ => ?_
        rw [Finset.prod_range_succ]
        ring
      · cases h
    · cases h

theorem slpVal_char (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) {i : ℕ} {k : CertKey}
    (h : p.ops.getD i (.const 0 0 0) = .char k) (hi : i < p.ops.length) :
    p.val n z i = Complex.exp (Complex.I * modePhase n k z.1) := by
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  rfl

theorem jCharsOk_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {facs : List (JKey × JNode α)} (hfacs : ∀ m ∈ facs, JEnc n W jb m.2 (keyFn n K p m.1))
    {es : List (ℕ × JNode α)} (h : jCharsOk n W pe cfg jb p facs es = true) :
    ∀ m ∈ es, JEnc n W jb m.2 (embFn n K p m.1) := by
  intro m hm
  have hm' := List.all_eq_true.mp h m hm
  split at hm'
  · rename_i k hop
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
    obtain ⟨hi, hm''⟩ := hm'
    split at hm''
    · rename_i nd hnd
      have := jExportOk_enc (jCharProd_sound hW hpe B hfacs k n hnd) hm''
      refine PEnc.congr this fun θ _ => ?_
      simp only [embFn, slotFn]
      rw [slpVal_char p _ hop hi, exp_I_modePhase_eval, charExpFun_prod]
    · cases hm''
  · cases hm'

/-- An extended block is sound (a given block by hypothesis). -/
theorem JBlockX.sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {b : JBlockX α} (hok : b.ok n W pe cfg jb K p = true)
    (hgiven : b.isGiven = true → ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1))
    (himp : ∀ m ∈ b.imports, JEnc n W jb m.2 (keyFn n K p m.1)) :
    ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1) := by
  cases b with
  | base b0 =>
    intro m hm
    simp only [JBlockX.exports, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have himp' : ∀ m ∈ b0.imports, JEnc n W jb m.2 (embFn n K p m.1) := by
      intro m hm
      have hmem : ((.inl m.1, m.2) : JKey × JNode α) ∈ (JBlockX.base b0).imports := by
        simp only [JBlockX.imports, List.mem_map]
        exact ⟨m, hm, rfl⟩
      exact himp _ hmem
    have hg' : b0.isGiven = true → ∀ m ∈ b0.exports, JEnc n W jb m.2 (embFn n K p m.1) := by
      intro hg m hm
      have hmem : ((.inl m.1, m.2) : JKey × JNode α) ∈ (JBlockX.base b0).exports := by
        simp only [JBlockX.exports, List.mem_map]
        exact ⟨m, hm, rfl⟩
      exact hgiven hg _ hmem
    exact JBlock.sound hW hpe B K p hok hg' himp' m0 hm0
  | expo j neg N out =>
    intro m hm
    simp only [JBlockX.exports, List.mem_singleton] at hm
    subst hm
    simp only [JBlockX.ok] at hok
    split at hok
    · rename_i e he
      exact jExportOk_enc (jExpNode_sound hW hpe B he) hok
    · cases hok
  | pows j neg b0 outs =>
    have hb : JEnc n W jb b0 (auxFn n K j neg 1) :=
      himp (.inr (j, neg, 1), b0) (by simp [JBlockX.imports])
    simp only [JBlockX.ok] at hok
    intro m hm
    simp only [JBlockX.exports] at hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    simp only [List.getElem_zipWith, List.getElem_range]
    have hi' : i < outs.length := by simp at hi; omega
    have := jPowsAux_sound hW B hb outs b0 1 hb hok i hi'
    simpa [keyFn, show 1 + 1 + i = i + 2 by ring] using this
  | chars facs es =>
    intro m hm
    simp only [JBlockX.exports, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact jCharsOk_sound hW hpe B K p himp hok m0 hm0

/-- **The extended packed jet chain, with the given blocks as hypotheses.** -/
theorem jChainX_sound_of_given {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlockX α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hgiven : ∀ b ∈ blocks, b.isGiven = true →
      ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1))
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1) := by
  have B := jBookOk_spec hb
  have hc := chain_sound (fun m : JKey × JNode α => JEnc n W jb m.2 (keyFn n K p m.1)) blocks
    JBlockX.imports JBlockX.exports
    (fun b hbm himp => JBlockX.sound hW hpe B K p (hok b hbm) (hgiven b hbm) himp) hfirst
  intro b hbm m hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
  exact hc k hk m hm

end Sound

end KAM.CertificateSharp.Packed
