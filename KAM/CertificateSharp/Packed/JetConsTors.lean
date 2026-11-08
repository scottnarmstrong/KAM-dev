/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsRSound

/-!
# The rounded packed torsion on the jet's boundary: definitions and boundary models

B3b's `checkTorsionR` (`TorsR.lean`) reads `DX_H ∘ K` and `DH ∘ K` from memo entries checked against
the landed `cfgLow` composition (`ptAOk`, `ptD1Ok`). Here they are read from the packed jet nodes
of the wanted slots (design `V2-PACKED.md` §12.2):

* `JSlots`: the packed value, radius and norm bound of every program slot (for a keyed jet chain,
  `jetNode`, `jetRad`, `jetNb`); `JSlotsEnc`: every slot of a list has a packed model of its slot
  function at the embedding (the conclusion of `jetPacked_sound`, taken as a hypothesis here and
  discharged by `jetPacked_sound` in `JetConsTorsSound.lean`);
* `trAJ` (`DX_H ∘ K`: entry `(a, b)` is `± ∂_{a'} ∂_b H ∘ K`, `a' = swapNat n a`, the slot read by
  the landed `dxhModels`) and `trD1J` (`DH ∘ K`);
* the stages that read them: `trMXNJ`, `trStXNJ` (`X_N = A N - DN`), `trYJ`, `trYCheckJ`
  (`Y = DH N`); every other stage of B3b is reused verbatim;
* `ptD2All` (the `D²K` boundary of `ptEntries`), `torsRCoreJ` (`torsRCore` with the two stages
  above) and `trTChainOkJ` (the guards and stages of `T`, for the frames);
* the boundary models `trAJ_encloses`, `trD1J_encloses` and the stage models `trXNmJ_encloses`,
  `trYJ_encloses`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix

/-- The packed models of the program slots of a jet chain: value, radius and norm bound of every
slot (untrusted until `JSlotsEnc` is shown). -/
structure JSlots (α : Type) where
  x : ℕ → PC
  r : ℕ → α
  nb : ℕ → α

/-- Every slot `i ∈ ws` has a packed model (layout `L`, load `A`, scale `2^e`) of its slot function
`θ ↦ p.val n (K.eval n θ) i` on `T_ρ`: the conclusion of `jetPacked_sound`. -/
def JSlotsEnc {α : Type} [CertArith α] (L : PackLayout) (A e : ℕ) (js : JSlots α) (n : ℕ)
    (ρ : ℝ) (p : Slp) (K : CertEmbedding α) (ws : List ℕ) : Prop :=
  ∀ i ∈ ws, PEnc L A e (js.x i) (js.r i) (js.nb i) n ρ (fun θ => p.val n (K.eval n θ) i)

section Defs

variable {α : Type} [CertArith α]

/-- The slot of `(DX_H ∘ K)_{ab} = ± ∂_{a'} ∂_b H ∘ K`, `a' = swapNat n a` (as `dxhModels`). -/
def dxhSlot (n : ℕ) (J : HamJet) (a b : ℕ) : ℕ := (J.d2.getD (swapNat n a) []).getD b 0

/-- `DX_H ∘ K` from the jet slots (sign `+` on the rows `a < n`). -/
def trAJ (n : ℕ) (J : HamJet) (js : JSlots α) : PMat α :=
  ⟨fun a b => if a < n then js.x (dxhSlot n J a b) else pcNeg (js.x (dxhSlot n J a b)),
    fun a b => js.r (dxhSlot n J a b), fun a b => js.nb (dxhSlot n J a b)⟩

/-- `DH ∘ K` (one row) from the jet slots. -/
def trD1J (J : HamJet) (js : JSlots α) : PMat α :=
  ⟨fun _ a => js.x (J.d1.getD a 0), fun _ a => js.r (J.d1.getD a 0),
    fun _ a => js.nb (J.d1.getD a 0)⟩

/-- The exact product of `X_N = A N - DN` on `Lw` (scale `2^(2P)`), `A` from the jet. -/
def trMXNJ (n : ℕ) (J : HamJet) (js : JSlots α) (rb : PRBook) (rm : PRMemo) : PMat α :=
  PMat.add (PMat.mul (n + n) (trAJ n J js) (trN n rb rm))
    (PMat.shift (pcUnit rb.Lu.width (zslot n rb.Lu) (2 ^ rb.P)) (PMat.neg (trDN n rb rm)))

/-- The node `X_N` checked on the window. -/
def trStXNJ (n : ℕ) (J : HamJet) (js : JSlots α) (W : CertWeight) (rb : PRBook) (rm : PRMemo) :
    Bool :=
  trStage n W rb (n + n) n (trMXNJ n J js rb rm) rm.XN

/-- `Y = DH N` on `Lw`, scale `2^(2P)`, `DH` from the jet. -/
def trYJ (n : ℕ) (J : HamJet) (js : JSlots α) (rb : PRBook) (rm : PRMemo) : PMat α :=
  PMat.mul (n + n) (trD1J J js) (trN n rb rm)

/-- The averages of `Y` against the tables. -/
def trYCheckJ (n : ℕ) (J : HamJet) (js : JSlots α) (rb : PRBook) (rm : PRMemo) : Bool :=
  (List.range n).all fun j =>
    decide (ptDigit n rb.Lw (2 * rb.P) ((trYJ n J js rb rm).x 0 j) = rm.CY.getD j (0, 0)) &&
      ble ((trYJ n J js rb rm).r 0 j) (ofRatDown (rm.RY.getD j 0))

/-- The `D²K` boundary entries (the first conjunct of `ptEntries`). -/
def ptD2All (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (tb : PTorsBook) (tm : PTorsMemo) : Bool :=
  (List.range (n + n)).all fun r => (List.range n).all fun j => (List.range n).all fun l =>
    ptD2Ok n K W cfg pe tb tm r j l

/-- **The core of the rounded packed torsion check on the jet's boundary**: `torsRCore` with
`trStXNJ` and `trYCheckJ` in place of `trStXN` and `trYCheck`. -/
def torsRCoreJ (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight) (cfg : ModelConfig α)
    (box : FreqBox) (s : ℚ) (J : HamJet) (js : JSlots α) (rb : PRBook) (mm : PGramMemo)
    (tm : PTorsMemo) (rm : PRMemo) (eps : α) (S : List (List (CC α))) (σTμ : ℚ) : Bool :=
  trLayOk n rb && trNormOk n W box s rb && ptPackOk n Binv cfg rb.toT mm tm &&
    trStN n Binv W cfg rb mm rm eps && trStDL (α := α) n W box s rb tm rm &&
    trStDG (α := α) n W rb mm rm && trStC n Binv W cfg rb rm eps &&
    trStDGi n Binv W cfg rb rm eps && trStDN n Binv W cfg rb mm rm eps &&
    trStXNJ n J js W rb rm && trTCheck (α := α) n rb rm && trYCheckJ n J js rb rm &&
    tabFinal n cfg rb.P (trCentre n box s rm) (trRad n box s rm) S σTμ

/-- The guards and the stage checks of the packed torsion block `T` on the jet's boundary (the
conjuncts of `torsRCoreJ` before its averaged and final tests; `trTChainOk` with `trStXNJ`). -/
def trTChainOkJ (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight) (cfg : ModelConfig α)
    (box : FreqBox) (s : ℚ) (J : HamJet) (js : JSlots α) (rb : PRBook) (mm : PGramMemo)
    (tm : PTorsMemo) (rm : PRMemo) (eps : α) : Bool :=
  trLayOk n rb && trNormOk n W box s rb && ptPackOk n Binv cfg rb.toT mm tm &&
    trStN n Binv W cfg rb mm rm eps && trStDL (α := α) n W box s rb tm rm &&
    trStDG (α := α) n W rb mm rm && trStC n Binv W cfg rb rm eps &&
    trStDGi n Binv W cfg rb rm eps && trStDN n Binv W cfg rb mm rm eps &&
    trStXNJ n J js W rb rm

end Defs

/-! ### The boundary models -/

section Base

variable {α : Type} [CertArith α] {n : ℕ}

theorem getD_mem_of_lt {β : Type} {l : List β} {i : ℕ} (h : i < l.length) (d : β) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- The slot of `(DX_H ∘ K)_{ab}` is a torsion slot. -/
theorem dxhSlot_mem (J : HamJet) (a b : Fin n ⊕ Fin n) :
    dxhSlot n J (phaseNat a) (phaseNat b) ∈ torsionSlots n J := by
  have ha := phaseNat_lt_add a.swap
  have hb := phaseNat_lt_add b
  have hq : n + n + (n + n) * phaseNat a.swap + phaseNat b < (torsionSlots n J).length := by
    rw [torsionSlots_length]; nlinarith
  unfold dxhSlot
  rw [swapNat_phaseNat, ← torsionSlots_getD_d2 J ha hb]
  exact getD_mem_of_lt hq 0

/-- The slot of `∂_a H` is a torsion slot. -/
theorem d1Slot_mem (J : HamJet) (a : Fin n ⊕ Fin n) :
    J.d1.getD (phaseNat a) 0 ∈ torsionSlots n J := by
  have ha := phaseNat_lt_add a
  have hq : phaseNat a < (torsionSlots n J).length := by rw [torsionSlots_length]; omega
  rw [← torsionSlots_getD_d1 J ha]
  exact getD_mem_of_lt hq 0

/-- `DX_H ∘ K` from the jet's packed models of the torsion slots. -/
theorem trAJ_encloses {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {ρ : ℝ}
    (hKD : ∀ θ ∈ complexStrip n ρ, K.eval n θ ∈ D) {L : PackLayout} {A P : ℕ} {js : JSlots α}
    (hJ : JSlotsEnc L A P js n ρ e.jet.prog K (torsionSlots n e.jet)) :
    PMat.Encloses L A P n ρ phaseNat phaseNat (trAJ n e.jet js) (linMat e.eval (K.eval n)) := by
  intro a b
  have hs := (hJ _ (dxhSlot_mem e.jet a b)).congr (g := fun θ =>
      iteratedFDeriv ℂ 2 e.eval (K.eval n θ) ![phaseBasis a.swap, phaseBasis b]) fun θ hθ => by
    show e.jet.prog.val n (K.eval n θ) (dxhSlot n e.jet (phaseNat a) (phaseNat b)) = _
    unfold dxhSlot
    rw [swapNat_phaseNat]
    exact e.jet_d2 hD hnv (hKD θ hθ) a.swap b
  have hlin : ∀ θ ∈ complexStrip n ρ, linMat e.eval (K.eval n) θ a b = hamSign a *
      iteratedFDeriv ℂ 2 e.eval (K.eval n θ) ![phaseBasis a.swap, phaseBasis b] := fun θ hθ =>
    linMat_apply_eq (((e.contDiffOn_eval hD hnv).contDiffAt
      (hD.mem_nhds (hKD θ hθ))).of_le le_top) a b
  rcases a with i | i
  · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
    simp only [trAJ, hlt, ↓reduceIte]
    exact hs.congr fun θ hθ => by rw [hlin θ hθ]; simp [hamSign]
  · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
    simp only [trAJ, hlt, ↓reduceIte]
    exact hs.neg.congr fun θ hθ => by rw [hlin θ hθ]; simp [hamSign]

/-- `DH ∘ K` from the jet's packed models of the torsion slots. -/
theorem trD1J_encloses {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {ρ : ℝ}
    (hKD : ∀ θ ∈ complexStrip n ρ, K.eval n θ ∈ D) {L : PackLayout} {A P : ℕ} {js : JSlots α}
    (hJ : JSlotsEnc L A P js n ρ e.jet.prog K (torsionSlots n e.jet)) :
    PMat.Encloses L A P n ρ (fun _ : Unit => 0) phaseNat (trD1J e.jet js)
      (fun θ => Matrix.of fun _ a => fderiv ℂ e.eval (K.eval n θ) (phaseBasis a)) := by
  intro _ a
  exact (hJ _ (d1Slot_mem e.jet a)).congr fun θ hθ => e.jet_d1 hD hnv (hKD θ hθ) a

end Base

/-! ### The stages that read the jet -/

section Chain

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {sw Nw : ℕ}
  {rb : PRBook} {rm : PRMemo} {box : FreqBox} {s : ℚ} {J : HamJet} {js : JSlots α}
  {FN FDN : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
  {FA : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}

/-- `X_N = A N - DN`, `A` from the jet. -/
theorem trXNmJ_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hA : PMat.Encloses rb.Lb rb.bA rb.P n W.rho phaseNat phaseNat (trAJ n J js) FA)
    (hN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trN (α := α) n rb rm) FN)
    (hDN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trDN (α := α) n rb rm) FDN)
    (h : trStXNJ n J js W rb rm = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (nodeMat (α := α) rb.Lb rm.XN)
      (fun θ => FA θ * FN θ + -FDN θ) := by
  have h1 := hA.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN
  have h2 := (hDN.neg.shift lay.cbu lay.wb lay.wu (pow_unit_rep lay.wu lay.su rb.P)).cast lay.eu
    rfl rfl
  exact trStage_encloses hW lay nrm phaseNat_lt_add (fun j => j.isLt) nrm.hXN (h1.add h2) h

/-- `Y = DH N` on the window, `DH` from the jet. -/
theorem trYJ_encloses (lay : TRLay n rb) {FD1 : (Fin n → ℂ) → Matrix Unit (Fin n ⊕ Fin n) ℂ}
    (hD1 : PMat.Encloses rb.Lb rb.bA rb.P n W.rho (fun _ : Unit => 0) phaseNat (trD1J J js) FD1)
    (hN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trN (α := α) n rb rm) FN) :
    PMat.Encloses rb.Lw (rb.aY n) (2 * rb.P) n W.rho (fun _ : Unit => 0) Fin.val
      (trYJ n J js rb rm) (fun θ => FD1 θ * FN θ) :=
  (hD1.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN).cast rfl rfl
    (two_mul rb.P).symm

end Chain

end KAM.CertificateSharp.Packed
