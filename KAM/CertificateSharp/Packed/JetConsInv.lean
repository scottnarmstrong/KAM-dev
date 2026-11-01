/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsTorsSound
public import KAM.CertificateSharp.Packed.Frames

/-!
# The packed invariance check on the jet's boundary

The landed `checkInvariance` (`KAM/Certificate/Defs.lean`) composes `∂_a H ∘ K` at `cfgFull`
(`Slp.compose`) and bounds `sup |invarianceModel a| ≤ e`. `checkInvarianceJ` certifies **the same
proposition** (`checkInvarianceJ_sound`: the conclusion of `checkInvariance_sound_of`) from

* the jet's packed models of the `d1` slots (`jetFullOk`: the keyed chain at `cfgFull`,
  `jetPacked_sound`, on the box `ib.Lb` at scale `2^P`);
* the packed `DK` entries (B2's Gram memo `mm`, checked by `pgEntries` inside the packed Gram
  check; packed on the jet's box) and the packed frequency coordinates `(s ω)_l` (centre and box
  radius, as B3);

as one exact packed array per coordinate `a < 2n` on `win Lb LU0` at scale `2^(2P)`:
`(X_H ∘ K)_a · 2^P - Σ_l DK_{al} (s ω)_l` (`ivX`), whose sup is bounded by **one packed weighted
norm plus the radii** (`ivRowOk`). The book `PIBook` is untrusted metadata (`ivGuard` checks it).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith

/-- The untrusted metadata of the packed invariance and energy checks. -/
structure PIBook where
  /-- the scale of the jet nodes and of the `DK` memo -/
  P : ℕ
  /-- the jet's box (the `cfgFull` chain's) and the one-slot layout of the constants -/
  Lb : PackLayout
  LU0 : PackLayout
  /-- load bounds: the jet nodes, the `DK` mantissas, the frequency mantissas -/
  bJ : ℕ
  bK : ℕ
  bF : ℕ
  /-- norm precision and offsets: the `DK` entries, the invariance arrays -/
  q : ℕ
  lK : ℕ
  lI : ℕ

namespace PIBook

variable (ib : PIBook)

/-- The book of `Tors.lean` for `DK` (on the box) and the frequency (on `LU0`). -/
def toT : PTorsBook where
  P := ib.P
  L1 := ib.Lb
  LB := ib.Lb
  LA := ib.Lb
  LU0 := ib.LU0
  LU1 := ib.LU0
  LU2 := ib.LU0
  bK := ib.bK
  bB := 0
  bD := 0
  bA := ib.bJ
  bF := ib.bF
  q := ib.q
  lK := ib.lK
  lB := 0
  lD := 0
  lA := 0
  lDL := 0
  lN := 0
  lDG := 0
  lC := 0
  lDGi := 0
  lXN := 0

/-- The layout of the invariance arrays. -/
def LI : PackLayout := win ib.Lb ib.LU0

/-- The load of the invariance arrays. -/
def aI (n : ℕ) : ℕ :=
  mulLoad ib.Lb ib.LU0 ib.bJ (2 ^ ib.P) + n * mulLoad ib.Lb ib.LU0 ib.bK ib.bF

end PIBook

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (J : HamJet)
  (js : JSlots α) (ib : PIBook) (mm : PGramMemo)

/-- The slot of `∂_{a'} H`, `a' = swapNat n a`: coordinate `a` of `X_H` up to sign. -/
def ivSlot (a : ℕ) : ℕ := J.d1.getD (swapNat n a) 0

/-- `(X_H ∘ K)_a` from the jet (sign `+` for `a < n`), on the box at scale `2^P`. -/
def ivXH (a : ℕ) : PC := if a < n then js.x (ivSlot n J a) else pcNeg (js.x (ivSlot n J a))

/-- `(DK (s ω))_a = Σ_l DK_{al} (s ω)_l` on `win Lb LU0` at scale `2^(2P)`. -/
def ivDK (a : ℕ) : PC :=
  pcSumN (fun l => pcMul ((ptK (α := α) W ib.toT mm).x a l) (ptF n box s ib.toT l)) n

/-- **The invariance array** of coordinate `a`: `(X_H ∘ K)_a · 2^P - (DK (s ω))_a`, exact, on
`win Lb LU0` at scale `2^(2P)`. -/
def ivX (a : ℕ) : PC :=
  pcAdd (pcMul (ivXH n J js a) (pcUnit ib.LU0.width (zslot n ib.LU0) (2 ^ ib.P)))
    (pcNeg (ivDK (α := α) n W box s ib mm a))

/-- The radius of the invariance array: the jet slot's, then `pmulRad` of every product. -/
def ivR (a : ℕ) : α :=
  upAdd (js.r (ivSlot n J a)) (sumUp (fun l => pmulRad ((ptK (α := α) W ib.toT mm).nb a l)
    ((ptK (α := α) W ib.toT mm).r a l) (ofRatUp (|(ptFc box s ib.toT l : ℚ)| / 2 ^ ib.P))
    (ofRatUp (ptFr box s ib.toT l))) (List.range n))

/-- **One coordinate**: the packed weighted norm of the invariance array plus its radius is at
most `err`. -/
def ivRowOk (err : ℚ) (a : ℕ) : Bool :=
  ble (upAdd (pnorm W ib.q ib.lI ib.LI (ib.P + ib.P) (ivX n W box s J js ib mm a))
    (ivR n W box s J js ib mm a)) (ofRatDown err)

/-- The guards: layouts, the norm guards of `DK` and of the invariance arrays, the packing of the
`DK` memo on the box, the frequency mantissas. -/
def ivGuard : Bool :=
  layoutWf ib.Lb && layoutWf ib.LU0 && PackLayout.compat n ib.Lb ib.LU0 &&
    (ib.LU0.slot (List.replicate n 0)).isSome && normOk W ib.q ib.lK ib.bK ib.Lb &&
    normOk W ib.q ib.lI (ib.aI n) ib.LI &&
    ((List.range (n + n)).all fun r => (List.range n).all fun a =>
      packRepOk ib.Lb (mm.reAt r a) ib.bK && packRepOk ib.Lb (mm.imAt r a) ib.bK) &&
    (List.range n).all fun l => decide ((ptFc box s ib.toT l).natAbs ≤ ib.bF)

end Defs

/-- **The jet chain at `cfgFull`** for `v0` and the `d1` slots, on the box and scale of the book,
with load at most `ib.bJ` (`jetCheck`; the box agreement is checked). -/
def jetFullOk {n : ℕ} {α : Type} [CertArith α] (ib : PIBook) (jd : JetData)
    (c : TorusCertificate n α) : Bool :=
  layoutEq jd.jb.Lb ib.Lb && jd.jb.P == ib.P &&
    jetCheck n c.weight c.piEnc c.cfgFull c.emb c.ham.jet.prog jd ib.bJ
      (c.ham.jet.v0 :: d1Slots n c.ham.jet)

/-- **The packed invariance check on the jet's boundary** at the certificate's data: the packed
Gram check (its `pgEntries` validate the `DK` memo; the same Boolean term as `checkGramPacked`),
the jet chain at `cfgFull`, the guards, then every coordinate. No landed `Slp.compose`. -/
def checkInvarianceJ {n : ℕ} {α : Type} [CertArith α] (bk : PGramBook) (mm : PGramMemo)
    (ib : PIBook) (jd : JetData) (c : TorusCertificate n α) : Bool :=
  (gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ)).isSome &&
    ib.P == bk.P && jetFullOk ib jd c && ivGuard n c.weight c.freqBox c.params.s ib mm &&
    (List.range (n + n)).all fun a =>
      ivRowOk n c.weight c.freqBox c.params.s c.ham.jet (jetSlots (α := α) jd) ib mm
        c.params.err a

/-! ### Soundness -/

/-- The guard facts of a passing `ivGuard`. -/
structure IVGuard (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (ib : PIBook) (mm : PGramMemo) :
    Prop where
  wb : layoutWf ib.Lb = true
  w0 : layoutWf ib.LU0 = true
  cb0 : PackLayout.compat n ib.Lb ib.LU0 = true
  s0 : ib.LU0.slot (List.replicate n 0) = some (zslot n ib.LU0)
  nK : normOk W ib.q ib.lK ib.bK ib.Lb = true
  nI : normOk W ib.q ib.lI (ib.aI n) ib.LI = true
  pK : ∀ r < n + n, ∀ a < n, packRepOk ib.Lb (mm.reAt r a) ib.bK = true ∧
    packRepOk ib.Lb (mm.imAt r a) ib.bK = true
  fF : ∀ l < n, (ptFc box s ib.toT l).natAbs ≤ ib.bF

theorem ivGuard_spec {n : ℕ} {W : CertWeight} {box : FreqBox} {s : ℚ} {ib : PIBook}
    {mm : PGramMemo} (h : ivGuard n W box s ib mm = true) : IVGuard n W box s ib mm := by
  simp only [ivGuard, Bool.and_eq_true, and_assoc, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, slot_zslot h4, h5, h6, h7, h8⟩

/-- Coordinate `x` of the invariance error: `± ∂_{x.swap} H ∘ K - Σ_l ω_l DK_{xl}`. -/
theorem sumVec_invarianceError {n : ℕ} (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (θ : Fin n → ℂ)
    (x : Fin n ⊕ Fin n) :
    sumVec n (invarianceError H K ω θ) x =
      hamSign x * fderiv ℂ H (K θ) (phaseBasis x.swap) +
        -∑ l, ((ω l : ℝ) : ℂ) * tangentMat K θ x l := by
  rw [invarianceError, map_sub, Pi.sub_apply, sumVec_hamiltonianVectorFieldℂ,
    sumVec_fderiv_apply, sub_eq_add_neg]

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The invariance array encloses coordinate `x` of the invariance error.** -/
theorem ivX_encloses {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    {box : FreqBox} {s : ℚ} {ω : Fin n → ℝ} {ib : PIBook} {mm : PGramMemo} {js : JSlots α}
    (g : IVGuard n W box s ib mm)
    (hK : PMat.Encloses ib.Lb ib.bK ib.P n W.rho phaseNat Fin.val (ptK (α := α) W ib.toT mm)
      (tangentMat (K.eval n)))
    (hF : ∀ l : Fin n, PEnc ib.LU0 ib.bF ib.P (ptF n box s ib.toT l.val)
      (ofRatUp (ptFr box s ib.toT l.val) : α) (ofRatUp (|(ptFc box s ib.toT l.val : ℚ)| / 2 ^ ib.P))
      n W.rho (fun _ => ((((s : ℝ) • ω) l : ℝ) : ℂ)))
    (hJ : ∀ y : Fin n ⊕ Fin n, PEnc ib.Lb ib.bJ ib.P (js.x (e.jet.d1.getD (phaseNat y) 0))
      (js.r (e.jet.d1.getD (phaseNat y) 0)) (js.nb (e.jet.d1.getD (phaseNat y) 0)) n W.rho
      (fun θ => e.jet.prog.val n (K.eval n θ) (e.jet.d1.getD (phaseNat y) 0)))
    (x : Fin n ⊕ Fin n) :
    PEnc ib.LI (ib.aI n) (ib.P + ib.P) (ivX n W box s e.jet js ib mm (phaseNat x))
      (ivR n W box s e.jet js ib mm (phaseNat x))
      (pnorm W ib.q ib.lI ib.LI (ib.P + ib.P) (ivX n W box s e.jet js ib mm (phaseNat x))) n W.rho
      (fun θ => sumVec n (invarianceError e.eval (K.eval n) ((s : ℝ) • ω) θ) x) := by
  -- the coordinate of `X_H ∘ K` from the jet
  have hslot : ivSlot n e.jet (phaseNat x) = e.jet.d1.getD (phaseNat x.swap) 0 := by
    unfold ivSlot
    rw [swapNat_phaseNat]
  have hj := (hJ x.swap).congr (g := fun θ => fderiv ℂ e.eval (K.eval n θ) (phaseBasis x.swap))
    fun θ hθ => e.jet_d1 hD hnv (hKD θ hθ) x.swap
  have hX : PEnc ib.Lb ib.bJ ib.P (ivXH n e.jet js (phaseNat x))
      (js.r (ivSlot n e.jet (phaseNat x))) (js.nb (ivSlot n e.jet (phaseNat x))) n W.rho
      (fun θ => hamSign x * fderiv ℂ e.eval (K.eval n θ) (phaseBasis x.swap)) := by
    unfold ivXH
    rw [hslot]
    rcases x with i | i
    · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
      simp only [hlt, ↓reduceIte]
      exact hj.congr fun θ _ => by simp [hamSign]
    · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
      simp only [hlt, ↓reduceIte]
      exact hj.neg.congr fun θ _ => by simp [hamSign]
  have hXs := hX.shift g.cb0 g.wb g.w0 (pow_unit_rep g.w0 g.s0 ib.P)
  -- `DK (s ω)` from the Gram memo and the frequency
  let fk : ℕ → (Fin n → ℂ) → ℂ := fun l θ => if hl : l < n then
    tangentMat (K.eval n) θ x ⟨l, hl⟩ * ((((s : ℝ) • ω) ⟨l, hl⟩ : ℝ) : ℂ) else 0
  have hk : ∀ l < n, PEnc (win ib.Lb ib.LU0) (mulLoad ib.Lb ib.LU0 ib.bK ib.bF) (ib.P + ib.P)
      (pcMul ((ptK (α := α) W ib.toT mm).x (phaseNat x) l) (ptF n box s ib.toT l))
      (pmulRad ((ptK (α := α) W ib.toT mm).nb (phaseNat x) l)
        ((ptK (α := α) W ib.toT mm).r (phaseNat x) l)
        (ofRatUp (|(ptFc box s ib.toT l : ℚ)| / 2 ^ ib.P)) (ofRatUp (ptFr box s ib.toT l)))
      (upMul ((ptK (α := α) W ib.toT mm).nb (phaseNat x) l)
        (ofRatUp (|(ptFc box s ib.toT l : ℚ)| / 2 ^ ib.P))) n W.rho (fk l) := by
    intro l hl
    refine (PEnc.mul g.cb0 g.wb g.w0 (hK x ⟨l, hl⟩) (hF ⟨l, hl⟩)).congr fun θ _ => ?_
    simp only [fk, hl, ↓reduceDIte]
  have hs := PEnc.sumN n hk
  have hload : ((List.range n).map fun _ : ℕ => mulLoad ib.Lb ib.LU0 ib.bK ib.bF).sum =
      n * mulLoad ib.Lb ib.LU0 ib.bK ib.bF := by simp
  rw [hload] at hs
  -- the invariance array
  have h2 := (hXs.add hs.neg).renorm hW g.nI
  refine h2.congr fun θ _ => ?_
  rw [sumVec_invarianceError]
  congr 2
  rw [← Fin.sum_univ_eq_sum_range (fun k => fk k θ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [fk, l.isLt, ↓reduceDIte, Fin.eta]
  ring

/-- The jet chain at `cfgFull` gives packed models of `v0` and the `d1` slots on the book's box. -/
theorem jetFullOk_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {ib : PIBook}
    {jd : JetData} (h : jetFullOk ib jd c = true) :
    JSlotsEnc ib.Lb ib.bJ ib.P (jetSlots (α := α) jd) n c.weight.rho c.ham.jet.prog c.emb
      (c.ham.jet.v0 :: d1Slots n c.ham.jet) := by
  have S := checkStatic_sound hs
  simp only [jetFullOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hL, hP⟩, hj⟩ := h
  have hJ := jetPacked_sound S.hW S.hpe hj
  rw [layoutEq_eq hL, hP] at hJ
  exact hJ

/-- The slot of `∂_y H` is a wanted slot of the `cfgFull` chain. -/
theorem d1Slot_mem_full (J : HamJet) (y : Fin n ⊕ Fin n) :
    J.d1.getD (phaseNat y) 0 ∈ J.v0 :: d1Slots n J :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨phaseNat y, List.mem_range.mpr (phaseNat_lt_add y),
    rfl⟩)

/-- **Soundness of the packed invariance sub-check on the jet's boundary**: the conclusion of
the landed `checkInvariance_sound_of`, under its hypotheses. -/
theorem checkInvarianceJ_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {ib : PIBook} {jd : JetData}
    (h : checkInvarianceJ bk mm ib jd c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  simp only [checkInvarianceJ, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hGs, hP⟩, hjet⟩, hg⟩, hrow⟩ := h
  obtain ⟨δβ, hG⟩ := Option.isSome_iff_exists.mp hGs
  have g := ivGuard_spec hg
  have hJ := jetFullOk_sound hs hjet
  have hK := ptK_encloses (tb := ib.toT) S.hW S.hpe c.emb (pgEntries_of_check hG) hP g.wb g.pK
    g.nK
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := ib.toT) g.w0 g.s0 (s := c.params.s) hω
    l (g.fF l.val l.isLt) c.weight.rho
  have hx := fun x => ivX_encloses (isOpen_certDomain n c.weightH.rho c.centre c.radius) hH.1
    S.hW hKD g hK hF (fun y => hJ _ (d1Slot_mem_full c.ham.jet y)) x
  intro θ hθ
  rw [← S.hrho] at hθ
  rw [← norm_sumVec, pi_norm_le_iff_of_nonneg S.he0]
  intro x
  have hb := (LawfulCertArith.ble_sound _ _ (hrow _ (phaseNat_lt_add x))).trans
    (LawfulCertArith.ofRatDown_le _)
  exact (PEnc.norm_le_bound (hx x) hθ).trans hb

omit [LawfulCertArith α] in
/-- The packed invariance check on the jet's boundary from its parts: the shared Gram check and
jet chain, the guards, and every coordinate (each in its own declaration if needed). -/
theorem checkInvarianceJ_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {ib : PIBook} {jd : JetData} {δβ : α × α}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (hP : ib.P = bk.P) (hjet : jetFullOk ib jd c = true)
    (hg : ivGuard n c.weight c.freqBox c.params.s ib mm = true)
    (hrow : ∀ a < n + n, ivRowOk n c.weight c.freqBox c.params.s c.ham.jet
      (jetSlots (α := α) jd) ib mm c.params.err a = true) :
    checkInvarianceJ bk mm ib jd c = true := by
  simp only [checkInvarianceJ, hG, Option.isSome_some, hP, beq_self_eq_true, hjet, hg,
    Bool.and_self, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hrow

end Sound

end KAM.CertificateSharp.Packed
