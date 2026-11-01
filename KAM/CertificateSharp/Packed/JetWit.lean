/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetChar

/-!
# Packed witness operations: `inv` and `sqrt`

The candidate value of an `inv` or a `sqrt` slot is an untrusted packed box array `x` (validated by
`boxOk`, radius `0`: `jCand`); the kernel bounds its residual and turns the residual into a radius:

* `inv a`: with `d = 1 - a · x` and `δ ≥ sup |d|` (norm bound plus radius), `δ ≤ 1/2` gives
  `a ≠ 0` and `|a⁻¹ - x| ≤ |x| δ / (1 - 1/2)` (`inv_sub_le`);
* `sqrt a`: with constants `c_A`, `c_S > 0`, `|a - c_A| ≤ c_A/2` gives `Re a > 0` (so `a` is in the
  slit plane, where the landed `sqrtE` is the principal root), `|x - c_S| ≤ c_S - s₀` gives
  `Re x ≥ s₀ > 0`, and with `δ ≥ sup |x² - a|`, `|sqrtE a - x| ≤ δ / s₀` (`sqrtE_sub_le`).

`JBlockW` adds the two blocks to `JBlockX`; `jChainW_sound` is the chain theorem with them.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith Complex

/-! ### The two estimates -/

theorem inv_sub_le {z g : ℂ} {δ c : ℝ} (h : ‖1 - z * g‖ ≤ δ) (hδ : δ ≤ c) (hc : c < 1) :
    ‖z⁻¹ - g‖ ≤ ‖g‖ * δ / (1 - c) := by
  have hzg : 1 - c ≤ ‖z * g‖ := by
    have := norm_sub_norm_le (1 : ℂ) (z * g)
    simp only [norm_one] at this
    linarith
  have hpos : 0 < 1 - c := by linarith
  have hz : z ≠ 0 := by
    rintro rfl
    simp at hzg
    linarith
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hzg
    linarith
  have hzg0 : 0 < ‖z * g‖ := lt_of_lt_of_le hpos hzg
  have heq : z⁻¹ - g = (1 - z * g) * g / (z * g) := by
    field_simp
  rw [heq, norm_div, norm_mul]
  calc ‖1 - z * g‖ * ‖g‖ / ‖z * g‖ ≤ δ * ‖g‖ / ‖z * g‖ := by
        gcongr
    _ ≤ δ * ‖g‖ / (1 - c) := by
        exact div_le_div_of_nonneg_left (mul_nonneg ((norm_nonneg _).trans h) (norm_nonneg _))
          hpos hzg
    _ = ‖g‖ * δ / (1 - c) := by ring

theorem sqrtE_sub_le {f s : ℂ} {δ s0 : ℝ} (hf : 0 < f.re) (hs : s0 ≤ s.re) (hs0 : 0 < s0)
    (h : ‖s ^ 2 - f‖ ≤ δ) : ‖sqrtE f - s‖ ≤ δ / s0 := by
  have hsl : f ∈ slitPlane := Or.inl hf
  have hf0 : f ≠ 0 := slitPlane_ne_zero hsl
  rw [sqrtE_eq_exp hsl]
  set r := exp (log f * (1 / 2))
  have hr2 : r ^ 2 = f := by
    rw [← exp_nat_mul]
    push_cast
    rw [show (2 : ℂ) * (log f * (1 / 2)) = log f by ring, exp_log hf0]
  have hre : 0 ≤ r.re := by
    rw [exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · have := neg_pi_lt_arg f
      simp only [mul_im, log_im, log_re, one_div]
      norm_num
      linarith
    · have := arg_le_pi f
      simp only [mul_im, log_im, log_re, one_div]
      norm_num
      linarith
  have hsum : s0 ≤ ‖r + s‖ := by
    have h1 : (r + s).re ≤ ‖r + s‖ := re_le_norm _
    simp only [add_re] at h1
    linarith
  have hrs : r + s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsum
    linarith
  have heq : r - s = (f - s ^ 2) / (r + s) := by
    rw [← hr2]
    field_simp
    ring
  rw [heq, norm_div, norm_sub_rev]
  calc ‖s ^ 2 - f‖ / ‖r + s‖ ≤ δ / ‖r + s‖ := by gcongr
    _ ≤ δ / s0 := by
      have hδ : 0 ≤ δ := (norm_nonneg _).trans h
      exact div_le_div_of_nonneg_left hδ hs0 hsum

/-! ### The blocks -/

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- The negated node. -/
def jNeg (nd : JNode α) : JNode α := ⟨nd.u, nd.A, nd.e, pcNeg nd.x, nd.r, nd.nb⟩

/-- The node with its norm bound recomputed from its packed value (the bound of a sum adds the
bounds of its terms, which is far too large for a residual whose terms cancel). -/
def jRenorm (nd : JNode α) : Option (JNode α) :=
  if nd.A ≤ jb.aB then
    some ⟨nd.u, nd.A, nd.e, nd.x, nd.r, pnorm W jb.q (jRedL jb nd.u) (jLay jb nd.u) nd.e nd.x⟩
  else none

/-- A candidate box array as a node of radius `0`. -/
def jCand (x : PC) : JNode α :=
  ⟨false, 2 ^ jb.lb, jb.P, x, ofInt 0, pnorm W jb.q jb.ln jb.Lb jb.P x⟩

/-- **The `inv` check**: the node of `a`, the candidate `x`, the exported entry. -/
def jInvOk (na : JNode α) (x : PC) (out : JNode α) : Bool :=
  boxOk jb.Lb jb.lb x.re && boxOk jb.Lb jb.lb x.im &&
    match jMul n W jb na (jCand W jb x) jb.P, jConstQ n W pe cfg jb 1 with
    | some pr, some one =>
      match jAdd n jb one (jNeg pr) with
      | some d0 =>
        match jRenorm W jb d0 with
        | some d =>
        ble (upAdd d.r d.nb) (ofRatDown (1 / 2)) &&
          jExportOk ⟨false, 2 ^ jb.lb, jb.P, x,
            upMul (upMul (jCand W jb x : JNode α).nb (upAdd d.r d.nb)) (ofRatUp 2),
            (jCand W jb x : JNode α).nb⟩ out
        | none => false
      | none => false
    | _, _ => false

/-- **The `sqrt` check**: the node of `a`, the candidate `x`, the constants `c_A`, `c_S`, `s₀`. -/
def jSqrtOk (na : JNode α) (x : PC) (cA cS s0 : ℚ) (out : JNode α) : Bool :=
  boxOk jb.Lb jb.lb x.re && boxOk jb.Lb jb.lb x.im && decide (0 < cA) && decide (0 < s0) &&
    match jConstQ n W pe cfg jb cA, jConstQ n W pe cfg jb cS,
        jMul n W jb (jCand W jb x) (jCand W jb x) jb.P with
    | some a0, some c0, some sq =>
      match (jAdd n jb na (jNeg a0)).bind (jRenorm W jb),
          (jAdd n jb (jCand W jb x) (jNeg c0)).bind (jRenorm W jb),
          (jAdd n jb sq (jNeg na)).bind (jRenorm W jb) with
      | some dA, some dS, some e =>
        ble (upAdd dA.r dA.nb) (ofRatDown (cA / 2)) &&
          ble (upAdd (upAdd dS.r dS.nb) (ofRatUp s0)) (ofRatDown cS) &&
          jExportOk ⟨false, 2 ^ jb.lb, jb.P, x, upMul (upAdd e.r e.nb) (ofRatUp (1 / s0)),
            (jCand W jb x : JNode α).nb⟩ out
      | _, _, _ => false
    | _, _, _ => false

end Defs

/-- A block of the chain with the witness operations. -/
inductive JBlockW (α : Type) where
  | x (b : JBlockX α)
  | inv (a j : ℕ) (na : JNode α) (cand : PC) (out : JNode α)
  | sqrt (a j : ℕ) (na : JNode α) (cand : PC) (cA cS s0 : ℚ) (out : JNode α)

namespace JBlockW

variable {α : Type}

def imports : JBlockW α → List (JKey × JNode α)
  | .x b => b.imports
  | .inv a _ na _ _ => [(.inl a, na)]
  | .sqrt a _ na _ _ _ _ _ => [(.inl a, na)]

def exports : JBlockW α → List (JKey × JNode α)
  | .x b => b.exports
  | .inv _ j _ _ out => [(.inl j, out)]
  | .sqrt _ j _ _ _ _ _ out => [(.inl j, out)]

def isGiven : JBlockW α → Bool
  | .x b => b.isGiven
  | _ => false

variable [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (cfg : ModelConfig α)
  (jb : JBook)

def ok (K : CertEmbedding α) (p : Slp) : JBlockW α → Bool
  | .x b => b.ok n W pe cfg jb K p
  | .inv a j na c out =>
    match p.ops.getD j (.const 0 0 0) with
    | .inv a' => a' == a && decide (a < j) && decide (j < p.ops.length) &&
        jInvOk n W pe cfg jb na c out
    | _ => false
  | .sqrt a j na c cA cS s0 out =>
    match p.ops.getD j (.const 0 0 0) with
    | .sqrt a' => a' == a && decide (a < j) && decide (j < p.ops.length) &&
        jSqrtOk n W pe cfg jb na c cA cS s0 out
    | _ => false

end JBlockW

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

omit [LawfulCertArith α] in
theorem jNeg_sound {nd : JNode α} {f : (Fin n → ℂ) → ℂ} (h : JEnc n W jb nd f) :
    JEnc n W jb (jNeg nd) (fun θ => -f θ) :=
  PEnc.neg h

/-- A candidate passing `boxOk` is the packed model, of radius `0`, of its own function. -/
theorem jCand_rep {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb) {x : PC}
    (hre : boxOk jb.Lb jb.lb x.re = true) (him : boxOk jb.Lb jb.lb x.im = true) :
    ∃ G : (Fin n → ℂ) → ℂ, PCRep jb.Lb (2 ^ jb.lb) x n G ∧
      JEnc n W jb (jCand W jb x : JNode α) (fun θ => G θ / 2 ^ jb.P) := by
  obtain ⟨G, hG⟩ := PCRep.ofBoxOk (n := n) hre him
  refine ⟨G, hG, ?_⟩
  have hG' : PCRep jb.Lb (2 ^ jb.lb) x n (fun θ => G θ / 2 ^ jb.P * 2 ^ jb.P) := by
    obtain ⟨dr, di, hr, hi, hF⟩ := hG
    refine ⟨dr, di, hr, hi, fun θ => ?_⟩
    show G θ / 2 ^ jb.P * 2 ^ jb.P = _
    rw [div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]
    exact hF θ
  exact PEnc.ofPCRep hW B.nN hG' fun θ _ => by simp [jCand, LawfulCertArith.val_ofInt]

omit [LawfulCertArith α] in
/-- The exported node of a witness: the candidate with a radius bounding `f - candidate`. -/
theorem jWit_out {G : (Fin n → ℂ) → ℂ} {x : PC} (hG : PCRep jb.Lb (2 ^ jb.lb) x n G)
    {nb R : α} (hnb : ∀ θ ∈ complexStrip n W.rho, ‖G θ / 2 ^ jb.P‖ ≤ val nb)
    {f : (Fin n → ℂ) → ℂ} (hR : ∀ θ ∈ complexStrip n W.rho, ‖f θ - G θ / 2 ^ jb.P‖ ≤ val R) :
    JEnc n W jb (⟨false, 2 ^ jb.lb, jb.P, x, R, nb⟩ : JNode α) f :=
  ⟨G, by simpa [jLay] using hG, fun θ hθ => ⟨hR θ hθ, hnb θ hθ⟩⟩

/-- The candidate's function is bounded by the candidate's norm bound. -/
theorem jCand_norm {x : PC} {G : (Fin n → ℂ) → ℂ}
    (hc : JEnc n W jb (jCand W jb x : JNode α) (fun θ => G θ / 2 ^ jb.P)) :
    ∀ θ ∈ complexStrip n W.rho, ‖G θ / 2 ^ jb.P‖ ≤ val (jCand W jb x : JNode α).nb := by
  intro θ hθ
  obtain ⟨F, -, hb⟩ := hc
  obtain ⟨h0, h1⟩ := hb θ hθ
  have h0' : ‖G θ / 2 ^ jb.P - F θ / 2 ^ jb.P‖ ≤ 0 := by
    simpa [jCand, LawfulCertArith.val_ofInt] using h0
  have heq : G θ / 2 ^ jb.P = F θ / 2 ^ jb.P := sub_eq_zero.mp (norm_le_zero_iff.mp h0')
  rw [heq]
  exact h1

theorem jRenorm_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {nd nd' : JNode α} {f : (Fin n → ℂ) → ℂ} (hx : JEnc n W jb nd f)
    (h : jRenorm W jb nd = some nd') : JEnc n W jb nd' f := by
  unfold jRenorm at h
  split_ifs at h with hA
  cases h
  unfold JEnc at hx ⊢
  cases hu : nd.u
  · simp only [hu, jLay, jRedL, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact hx.renorm hW (normOk_mono B.nB (le_trans hA (Nat.le_add_right _ _)))
  · simp only [hu, jLay, jRedL, ↓reduceIte] at hx ⊢
    exact hx.renorm hW (normOk_mono B.nBc (le_trans hA (Nat.le_add_right _ _)))

theorem jInvOk_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {na out : JNode α} {x : PC}
    {fa : (Fin n → ℂ) → ℂ} (ha : JEnc n W jb na fa) (h : jInvOk n W pe cfg jb na x out = true) :
    JEnc n W jb out (fun θ => (fa θ)⁻¹) := by
  unfold jInvOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hre, him⟩, h⟩ := h
  obtain ⟨G, hG, hc⟩ := jCand_rep (α := α) hW B hre him
  have hgn := jCand_norm hc
  split at h
  · rename_i pr one hpr hone
    split at h
    · rename_i d0 hd0
      split at h
      · rename_i d hd
        simp only [Bool.and_eq_true] at h
        obtain ⟨hδ, hex⟩ := h
        have hpr' := jMul_sound hW B ha hc hpr
        have hd' := jRenorm_sound hW B
          (jAdd_sound B (jConstQ_sound hW hpe B hone) (jNeg_sound hpr') hd0) hd
        refine jExportOk_enc (jWit_out hG hgn fun θ hθ => ?_) hex
        set g := G θ / 2 ^ jb.P
        set δ := upAdd d.r d.nb
        have hu := LawfulCertArith.upAdd_ge d.r d.nb
        have hn : ‖1 - fa θ * g‖ ≤ val d.r + val d.nb := by
          calc ‖1 - fa θ * g‖ = ‖((1 : ℚ) : ℂ) + -(fa θ * g)‖ := by
                congr 1
                push_cast
                ring
            _ ≤ val d.r + val d.nb := PEnc.norm_le hd' hθ
        have hres : ‖1 - fa θ * g‖ ≤ val δ := by linarith
        have hle : val δ ≤ 1 / 2 := by
          have := (LawfulCertArith.ble_sound _ _ hδ).trans
            (LawfulCertArith.ofRatDown_le (α := α) (1 / 2))
          push_cast at this
          exact this
        have hδ0 : 0 ≤ val δ := (norm_nonneg _).trans hres
        have hnb0 : 0 ≤ val (jCand W jb x : JNode α).nb := (norm_nonneg _).trans (hgn θ hθ)
        have hinv := inv_sub_le hres hle (by norm_num : (1 / 2 : ℝ) < 1)
        have h1 := LawfulCertArith.upMul_ge _ δ hnb0 hδ0
        have h3 := LawfulCertArith.ofRatUp_ge (α := α) 2
        push_cast at h3
        have h2 := LawfulCertArith.upMul_ge (upMul (jCand W jb x : JNode α).nb δ) (ofRatUp 2)
          ((mul_nonneg hnb0 hδ0).trans h1) (by linarith)
        calc ‖(fa θ)⁻¹ - g‖ ≤ ‖g‖ * val δ / (1 - 1 / 2) := hinv
          _ = ‖g‖ * val δ * 2 := by ring
          _ ≤ val (jCand W jb x : JNode α).nb * val δ * 2 := by
              have := hgn θ hθ
              gcongr
          _ ≤ val (upMul (jCand W jb x : JNode α).nb δ) * val (ofRatUp 2 : α) := by
              apply mul_le_mul h1 h3 (by norm_num) ((mul_nonneg hnb0 hδ0).trans h1)
          _ ≤ _ := h2
      · cases h
    · cases h
  · cases h

theorem jSqrtOk_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) {na out : JNode α} {x : PC}
    {cA cS s0 : ℚ} {fa : (Fin n → ℂ) → ℂ} (ha : JEnc n W jb na fa)
    (h : jSqrtOk n W pe cfg jb na x cA cS s0 out = true) :
    JEnc n W jb out (fun θ => sqrtE (fa θ)) := by
  unfold jSqrtOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hre, him⟩, hcA⟩, hs0⟩, h⟩ := h
  obtain ⟨G, hG, hc⟩ := jCand_rep (α := α) hW B hre him
  have hgn := jCand_norm hc
  split at h
  · rename_i a0 c0 sq ha0 hc0 hsq
    split at h
    · rename_i dA dS e hdA hdS he
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hA, hS⟩, hex⟩ := h
      obtain ⟨dA0, hdA0, hdA1⟩ := Option.bind_eq_some_iff.mp hdA
      obtain ⟨dS0, hdS0, hdS1⟩ := Option.bind_eq_some_iff.mp hdS
      obtain ⟨e0, he0, he1⟩ := Option.bind_eq_some_iff.mp he
      have hdA' := jRenorm_sound hW B
        (jAdd_sound B ha (jNeg_sound (jConstQ_sound hW hpe B ha0)) hdA0) hdA1
      have hdS' := jRenorm_sound hW B
        (jAdd_sound B hc (jNeg_sound (jConstQ_sound hW hpe B hc0)) hdS0) hdS1
      have he' := jRenorm_sound hW B (jAdd_sound B (jMul_sound hW B hc hc hsq) (jNeg_sound ha) he0)
        he1
      refine jExportOk_enc (jWit_out hG hgn fun θ hθ => ?_) hex
      set g := G θ / 2 ^ jb.P
      -- `Re fa > 0`
      have hfa : 0 < (fa θ).re := by
        have hn : ‖fa θ - (cA : ℂ)‖ ≤ val dA.r + val dA.nb := by
          calc ‖fa θ - (cA : ℂ)‖ = ‖fa θ + -((cA : ℚ) : ℂ)‖ := by
                rw [sub_eq_add_neg]
            _ ≤ val dA.r + val dA.nb := PEnc.norm_le hdA' hθ
        have hu := LawfulCertArith.upAdd_ge dA.r dA.nb
        have hb := (LawfulCertArith.ble_sound _ _ hA).trans
          (LawfulCertArith.ofRatDown_le (α := α) _)
        have h1 : ‖fa θ - (cA : ℂ)‖ ≤ (cA : ℝ) / 2 := by
          push_cast at hb
          linarith
        have h2 := abs_re_le_norm (fa θ - (cA : ℂ))
        simp only [sub_re] at h2
        have : (((cA : ℚ) : ℂ)).re = (cA : ℝ) := by simp
        rw [abs_le] at h2
        have hc0 : (0 : ℝ) < cA := by exact_mod_cast hcA
        simp only [Complex.ratCast_re] at h2
        linarith [h2.1]
      -- `Re g ≥ s₀`
      have hg : (s0 : ℝ) ≤ g.re := by
        have hn : ‖g - (cS : ℂ)‖ ≤ val dS.r + val dS.nb := by
          calc ‖g - (cS : ℂ)‖ = ‖g + -((cS : ℚ) : ℂ)‖ := by
                rw [sub_eq_add_neg]
            _ ≤ val dS.r + val dS.nb := PEnc.norm_le hdS' hθ
        have hu := LawfulCertArith.upAdd_ge dS.r dS.nb
        have hu2 := LawfulCertArith.upAdd_ge (upAdd dS.r dS.nb) (ofRatUp s0)
        have hq := LawfulCertArith.ofRatUp_ge (α := α) s0
        have hb := (LawfulCertArith.ble_sound _ _ hS).trans
          (LawfulCertArith.ofRatDown_le (α := α) cS)
        have h1 : ‖g - (cS : ℂ)‖ ≤ (cS : ℝ) - s0 := by
          linarith
        have h2 := abs_re_le_norm (g - (cS : ℂ))
        simp only [sub_re, Complex.ratCast_re] at h2
        rw [abs_le] at h2
        linarith [h2.1]
      -- the residual
      have hres : ‖g ^ 2 - fa θ‖ ≤ val (upAdd e.r e.nb) := by
        have hn : ‖g ^ 2 - fa θ‖ ≤ val e.r + val e.nb := by
          calc ‖g ^ 2 - fa θ‖ = ‖g * g + -fa θ‖ := by
                congr 1
                ring
            _ ≤ val e.r + val e.nb := PEnc.norm_le he' hθ
        have hu := LawfulCertArith.upAdd_ge e.r e.nb
        linarith
      have hs0r : (0 : ℝ) < s0 := by exact_mod_cast hs0
      have hsq := sqrtE_sub_le hfa hg hs0r hres
      have hδ0 : 0 ≤ val (upAdd e.r e.nb) := (norm_nonneg _).trans hres
      have hq := LawfulCertArith.ofRatUp_ge (α := α) (1 / s0)
      push_cast at hq
      have h1 := LawfulCertArith.upMul_ge (upAdd e.r e.nb) (ofRatUp (1 / s0)) hδ0
        ((by positivity : (0 : ℝ) ≤ 1 / s0).trans hq)
      calc ‖sqrtE (fa θ) - g‖ ≤ val (upAdd e.r e.nb) / s0 := hsq
        _ = val (upAdd e.r e.nb) * (1 / s0) := by ring
        _ ≤ val (upAdd e.r e.nb) * val (ofRatUp (1 / s0) : α) :=
            mul_le_mul_of_nonneg_left hq hδ0
        _ ≤ _ := h1
    · cases h
  · cases h

theorem slpVal_inv (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) {i a : ℕ}
    (h : p.ops.getD i (.const 0 0 0) = .inv a) (hi : i < p.ops.length) (ha : a < i) :
    p.val n z i = (p.val n z a)⁻¹ := by
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  simp only [SlpOp.step]
  rw [slpVals_take_getD n p z hi.le ha]

theorem slpVal_sqrt (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) {i a : ℕ}
    (h : p.ops.getD i (.const 0 0 0) = .sqrt a) (hi : i < p.ops.length) (ha : a < i) :
    p.val n z i = sqrtE (p.val n z a) := by
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  simp only [SlpOp.step]
  rw [slpVals_take_getD n p z hi.le ha]

/-- A block with the witness operations is sound (a given block by hypothesis). -/
theorem JBlockW.sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {b : JBlockW α} (hok : b.ok n W pe cfg jb K p = true)
    (hgiven : b.isGiven = true → ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1))
    (himp : ∀ m ∈ b.imports, JEnc n W jb m.2 (keyFn n K p m.1)) :
    ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1) := by
  cases b with
  | x b0 => exact JBlockX.sound hW hpe B K p hok hgiven himp
  | inv a j na c out =>
    intro m hm
    simp only [JBlockW.exports, List.mem_singleton] at hm
    subst hm
    have ha : JEnc n W jb na (embFn n K p a) := himp (.inl a, na) (by simp [JBlockW.imports])
    simp only [JBlockW.ok] at hok
    split at hok
    · rename_i a' hop
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨rfl, hlt⟩, hj⟩, hk⟩ := hok
      have := jInvOk_sound hW hpe B ha hk
      exact PEnc.congr this fun θ _ => by
        simp only [keyFn, embFn, slotFn]
        rw [slpVal_inv p _ hop hj hlt]
    · cases hok
  | sqrt a j na c cA cS s0 out =>
    intro m hm
    simp only [JBlockW.exports, List.mem_singleton] at hm
    subst hm
    have ha : JEnc n W jb na (embFn n K p a) := himp (.inl a, na) (by simp [JBlockW.imports])
    simp only [JBlockW.ok] at hok
    split at hok
    · rename_i a' hop
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨rfl, hlt⟩, hj⟩, hk⟩ := hok
      have := jSqrtOk_sound hW hpe B ha hk
      exact PEnc.congr this fun θ _ => by
        simp only [keyFn, embFn, slotFn]
        rw [slpVal_sqrt p _ hop hj hlt]
    · cases hok

/-- **The packed jet chain with the witness operations.** With no given block, every export of
every block encloses its function: the slot functions `θ ↦ p.val n (K.eval n θ) j` and the
auxiliary powers. -/
theorem jChainW_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlockW α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hgiven : ∀ b ∈ blocks, b.isGiven = true →
      ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1))
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ m ∈ b.exports, JEnc n W jb m.2 (keyFn n K p m.1) := by
  have B := jBookOk_spec hb
  have hc := chain_sound (fun m : JKey × JNode α => JEnc n W jb m.2 (keyFn n K p m.1)) blocks
    JBlockW.imports JBlockW.exports
    (fun b hbm himp => JBlockW.sound hW hpe B K p (hok b hbm) (hgiven b hbm) himp) hfirst
  intro b hbm m hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
  exact hc k hk m hm

/-- **The packed jet chain, end to end.** With no given block, every program slot exported by a
block has a packed model of its function at the embedding, `θ ↦ p.val n (K.eval n θ) j` (the
contract of the landed `Slp.compose_sound` for the wanted slots). -/
theorem jChainW_slot {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlockW α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hng : ∀ b ∈ blocks, b.isGiven = false)
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ (j : ℕ) (nd : JNode α), (Sum.inl j, nd) ∈ b.exports →
      JEnc n W jb nd (fun θ => p.val n (K.eval n θ) j) := by
  intro b hbm j nd hm
  have := jChainW_sound hW hpe hb K p blocks hok
    (fun b hbm hg => absurd hg (by simp [hng b hbm])) hfirst b hbm _ hm
  exact this

end Sound

end KAM.CertificateSharp.Packed
