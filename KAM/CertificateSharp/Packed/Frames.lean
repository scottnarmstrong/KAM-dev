/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsRBase
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# Packed frame majorants and the packed route-A-refined engine

Route A refined (`KAM/CertificateSharp/V2/RouteARefinedEngine.lean`) tests `checkFrameMajorants`
(`KAM/CertificateSharp/Frame/Majorants.lean`, unchanged), whose `checkFrameN` and `checkFrameT`
re-evaluate the landed Gram check and the landed `torsionModels`. The packed frames read the same
bounds from the packed objects of B2/B3b:

* `|Lᵀ|` (`checkFrameLR`): column sums of the packed `DK` entries (the Gram memo, checked by
  `pgEntries`): `Σ_r (‖DK_{rj}‖ bound + radius)`;
* `|N|`, `|Nᵀ|` (`checkFrameNR`): row and column sums of `N = Ω₀ (L G⁻¹)`, from the verified node
  memo (`trStN`) through its norm bounds and radii;
* `sup |T|` (`checkFrameTR`): row sums of the packed torsion block `T` on the window (every stage of
  B3b verified), by its packed weighted norm and radius;
* `|ω*|`: the landed `checkFrameOmega`.

Each packed frame check repeats the conjuncts it shares with `checkTorsionR` (the packed Gram check,
the composition, the boundary entries, the guards, the stages), so a production proof establishes
them once for both. `checkFrameMajorantsR_sound` has the conclusion of the landed
`checkFrameMajorants_sound` (`FrameMajorants`), under its hypotheses. `routeARefinedPacked` is route
A refined with the packed frames; `checkV2With_packed_sound` gives the landed `CertifiedTorus` for
the v2 certifier with the packed Gram, torsion and frames (`torsRBase`, `routeARefinedPacked`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith KAM.CertificateSharp
  KAM.CertificateSharp.V2
open scoped Matrix Matrix.Norms.Operator

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (rb : PRBook) (mm : PGramMemo)
  (rm : PRMemo)

/-- The bound `nb + r` of `‖f‖` for an entry of a packed model matrix. -/
def pmBound (M : PMat α) (i j : ℕ) : α := upAdd (M.nb i j) (M.r i j)

/-- `|Lᵀ| ≤ b` from the packed `DK` entries. -/
def trFrameLOk (b : ℚ) : Bool :=
  (List.range n).all fun j =>
    ble (sumUp (fun r => pmBound (ptK (α := α) W rb.toT mm) r j) (List.range (n + n))) (ofRatDown b)

/-- `|N| ≤ bN`, `|Nᵀ| ≤ bNt` from the node memo of `N`. -/
def trFrameNOk (bN bNt : ℚ) : Bool :=
  ((List.range (n + n)).all fun r =>
      ble (sumUp (fun j => pmBound (trN (α := α) n rb rm) r j) (List.range n)) (ofRatDown bN)) &&
    (List.range n).all fun j =>
      ble (sumUp (fun r => pmBound (trN (α := α) n rb rm) r j) (List.range (n + n))) (ofRatDown bNt)

/-- `sup |T| ≤ bT` from the packed torsion block on the window. -/
def trFrameTOk (bT : ℚ) : Bool :=
  decide (rb.aT n ≤ rb.aW) &&
    (List.range n).all fun i =>
      ble (sumUp (fun j => upAdd (pnorm W rb.q rb.lW rb.Lw (2 * rb.P)
        ((trT (α := α) n rb rm).x i j)) ((trT (α := α) n rb rm).r i j)) (List.range n))
        (ofRatDown bT)

end Defs

section Checks

variable {n : ℕ} {α : Type} [CertArith α]

/-- **Packed `|Lᵀ| ≤ b`.** The guards are the very terms of `checkTorsionR` (`trLayOk`,
`trNormOk`, `ptPackOk`), so a production proof establishes each once. -/
def checkFrameLR (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (c : TorusCertificate n α) (b : ℚ) : Bool :=
  (gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ)).isSome &&
    rb.P == bk.P && trLayOk n rb && trNormOk n c.weight c.freqBox c.params.s rb &&
    ptPackOk n c.gramInv c.cfgLow rb.toT mm tm && trFrameLOk (α := α) n c.weight rb mm b

/-- **Packed `|N| ≤ bN`, `|Nᵀ| ≤ bNt`.** -/
def checkFrameNR (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (c : TorusCertificate n α) (bN bNt : ℚ) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && trLayOk n rb && trNormOk n c.weight c.freqBox c.params.s rb &&
        ptPackOk n c.gramInv c.cfgLow rb.toT mm tm &&
        trStN n c.gramInv c.weight c.cfgLow rb mm rm eps && trFrameNOk (α := α) n rb rm bN bNt
    | none => false
  | none => false

/-- The guards and the stage checks of the packed torsion block `T` (the conjuncts of `torsRCore`
before its averaged and final tests). -/
def trTChainOk (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight) (cfg : ModelConfig α)
    (box : FreqBox) (s : ℚ) (rb : PRBook) (mm : PGramMemo) (tm : PTorsMemo) (rm : PRMemo)
    (eps : α) : Bool :=
  trLayOk n rb && trNormOk n W box s rb && ptPackOk n Binv cfg rb.toT mm tm &&
    trStN n Binv W cfg rb mm rm eps && trStDL (α := α) n W box s rb tm rm &&
    trStDG (α := α) n W rb mm rm && trStC n Binv W cfg rb rm eps &&
    trStDGi n Binv W cfg rb rm eps &&
    trStDN n Binv W cfg rb mm rm eps && trStXN (α := α) n W rb tm rm

/-- **Packed `sup |T| ≤ bT`.** -/
def checkFrameTR (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (c : TorusCertificate n α) (bT : ℚ) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ, Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
        (torsionSlots n c.ham.jet) with
    | some eps, some ms =>
      rb.P == bk.P && ptEntries n c.emb c.weight c.cfgLow c.piEnc rb.toT tm ms &&
        trTChainOk n c.gramInv c.weight c.cfgLow c.freqBox c.params.s rb mm tm rm eps &&
        trFrameTOk (α := α) n c.weight rb rm bT
    | _, _ => false
  | none => false

/-- **The packed frame majorants.** -/
def checkFrameMajorantsR (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (c : TorusCertificate n α) (b : FrameBounds) : Bool :=
  checkFrameLR bk mm rb tm c b.bL && checkFrameNR bk mm rb tm rm c b.bN b.bNt &&
    checkFrameTR bk mm rb tm rm c b.bT && checkFrameOmega c b.bOm

end Checks

/-! ### Soundness -/

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- A sum over the phase indices as a sum over `range (n + n)`. -/
theorem sum_phaseNat_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ x : Fin n ⊕ Fin n, g (phaseNat x) = ∑ k ∈ Finset.range (n + n), g k := by
  rw [← Fin.sum_univ_eq_sum_range, ← finSumFinEquiv.symm.sum_comp]
  exact Finset.sum_congr rfl fun k _ => by rw [phaseNat_finSumFinEquiv_symm]

/-- An entry of a packed model is bounded by its norm bound plus its radius. -/
theorem PEnc.norm_le_bound {L : PackLayout} {A e : ℕ} {x : PC} {r nb : α} {ρ : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hx : PEnc L A e x r nb n ρ f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) : ‖f θ‖ ≤ val (upAdd nb r) := by
  obtain ⟨F, -, hb⟩ := hx
  obtain ⟨h1, h2⟩ := hb θ hθ
  have := norm_add_le (f θ - F θ / 2 ^ e) (F θ / 2 ^ e)
  rw [sub_add_cancel] at this
  have hu := LawfulCertArith.upAdd_ge nb r
  linarith

/-- A sum of `pmBound`s over `range m` bounds the sum of the entries' norms. -/
theorem sum_le_sumUp_bound {m : ℕ} {g : ℕ → ℝ} {B : ℕ → α} (h : ∀ k < m, g k ≤ val (B k))
    {b : ℚ} (hb : ble (sumUp B (List.range m)) (ofRatDown b) = true) :
    ∑ k ∈ Finset.range m, g k ≤ b := by
  refine le_trans ?_ ((LawfulCertArith.ble_sound _ _ hb).trans (LawfulCertArith.ofRatDown_le _))
  refine le_trans ?_ (sumUp_ge _ _)
  rw [list_sum_map_range_eq]
  exact Finset.sum_le_sum fun k hk => h k (Finset.mem_range.mp hk)

/-- **The packed torsion block** from the stage checks (the chain of `torsR_sound`). -/
theorem trT_chain {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hn : 1 ≤ n) (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    (hP : rb.P = bk.P) (hent : ptEntries n K W cfg pe rb.toT tm ms = true) {box : FreqBox} {s : ℚ}
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) (hlay : trLayOk n rb = true)
    (hnrm : trNormOk n W box s rb = true) (hpk : ptPackOk n Binv cfg rb.toT mm tm = true)
    (hN : trStN n Binv W cfg rb mm rm eps = true) (hDL : trStDL (α := α) n W box s rb tm rm = true)
    (hDG : trStDG (α := α) n W rb mm rm = true) (hC : trStC n Binv W cfg rb rm eps = true)
    (hDGi : trStDGi n Binv W cfg rb rm eps = true) (hDN : trStDN n Binv W cfg rb mm rm eps = true)
    (hXN : trStXN (α := α) n W rb tm rm = true) :
    PMat.Encloses rb.Lw (rb.aT n) (2 * rb.P) n W.rho Fin.val Fin.val (trT (α := α) n rb rm)
      (fun θ => Matrix.of fun i j =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j)) := by
  obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  have lay := trLayOk_spec hlay
  have nrm := trNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  obtain ⟨eD2, eA, -⟩ := ptEntries_spec hent
  have hK := ptK_encloses (tb := rb.toT) hW hpe K (pgEntries_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2 := ptD2_encloses (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := rb.toT) lay.w0 lay.s0 (s := s) hω l
    (nrm.fF l.val l.isLt) W.rho
  have hA := ptA_encloses (tb := rb.toT) hW hpe hD hnv hKD hms lay.wb eA pk.pA nrm.nA
  have hNN := (trNm_encloses hW lay nrm hK hB hN).omega
  have hDLm := trDLm_encloses hW lay nrm (trDL0_encloses K lay hD2 hF) hDL
  have hDGm := trDGm_encloses hW lay nrm hK hDLm hDG
  have hCm := trCm_encloses hW lay nrm hB hDGm hC
  have hDGim := trDGi_encloses hW lay nrm hCm hB hDGi
  have hDNm := trDN_encloses hW lay nrm hK hB hDLm hDGim hDN
  have hXNm := trXNm_encloses hW lay nrm hA hNN hDNm hXN
  intro i j
  refine (trT_encloses lay hNN hXNm i j).congr fun θ hθ => ?_
  show _ = torsion e.eval (K.eval n) ((s : ℝ) • ω) θ i j
  rw [torsion_eq_models (K.differentiable_eval n) hGu _ hθ]

/-- The packed `|Lᵀ|` bound. -/
theorem checkFrameLR_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {b : ℚ}
    (h : checkFrameLR bk mm rb tm c b = true) :
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ b := by
  have S := checkStatic_sound hs
  simp only [checkFrameLR, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hGs, hP⟩, hlay⟩, hnrm⟩, hpk⟩, hLok⟩ := h
  obtain ⟨δβ, hG⟩ := Option.isSome_iff_exists.mp hGs
  have hK := ptK_encloses (tb := rb.toT) S.hW S.hpe c.emb (pgEntries_of_check hG) hP
    (trLayOk_spec hlay).wb (ptPackOk_spec hpk).pK (trNormOk_spec hnrm).nK
  simp only [trFrameLOk, List.all_eq_true, List.mem_range] at hLok
  intro θ hθ j
  calc ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤
        ∑ r : Fin n ⊕ Fin n, val (pmBound (ptK (α := α) c.weight rb.toT mm) (phaseNat r) j.val) :=
        Finset.sum_le_sum fun r _ => PEnc.norm_le_bound (hK r j) hθ
    _ = ∑ k ∈ Finset.range (n + n), val (pmBound (ptK (α := α) c.weight rb.toT mm) k j.val) :=
        sum_phaseNat_eq (fun k => val (pmBound (ptK (α := α) c.weight rb.toT mm) k j.val))
    _ ≤ b := sum_le_sumUp_bound (fun k _ => le_rfl) (hLok j.val j.isLt)

/-- The packed `|N|`, `|Nᵀ|` bounds. -/
theorem checkFrameNR_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {bN bNt : ℚ}
    (h : checkFrameNR bk mm rb tm rm c bN bNt = true) :
    (∀ θ ∈ complexStrip n c.weight.rho, ∀ r : Fin n ⊕ Fin n,
      ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ bN) ∧
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ bNt := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  unfold checkFrameNR at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨hP, hlay⟩, hnrm⟩, hpk⟩, hN⟩, hNok⟩ := h
      obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn c.emb c.gramInv S.hW c.cfgLow S.hpe bk mm _ hG
      have lay := trLayOk_spec hlay
      have nrm := trNormOk_spec hnrm
      have pk := ptPackOk_spec hpk
      have hK := ptK_encloses (tb := rb.toT) S.hW S.hpe c.emb (pgEntries_of_check hG) hP lay.wb
        pk.pK nrm.nK
      have hB := ptB_encloses (tb := rb.toT) (eps := eps) S.hW lay.wb pk.pB nrm.nB fun θ hθ =>
        ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
      have hNN := (trNm_encloses S.hW lay nrm hK hB hN).omega
      have hnm : ∀ θ, normalMat c.K θ =
          omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ * (gramMatrix (c.emb.eval n) θ)⁻¹) :=
        fun θ => by unfold normalMat; rw [Matrix.mul_assoc]; rfl
      simp only [trFrameNOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hNok
      obtain ⟨hrow, hcol⟩ := hNok
      refine ⟨fun θ hθ r => ?_, fun θ hθ j => ?_⟩
      · rw [hnm θ]
        calc ∑ j : Fin n, ‖(omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
              (gramMatrix (c.emb.eval n) θ)⁻¹)) r j‖ ≤
              ∑ j : Fin n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) j.val) :=
              Finset.sum_le_sum fun j _ => PEnc.norm_le_bound (hNN r j) hθ
          _ = ∑ k ∈ Finset.range n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) k) :=
              Fin.sum_univ_eq_sum_range
                (fun k => val (pmBound (trN (α := α) n rb rm) (phaseNat r) k)) n
          _ ≤ bN := sum_le_sumUp_bound (fun k _ => le_rfl) (hrow _ (phaseNat_lt_add r))
      · rw [hnm θ]
        calc ∑ r : Fin n ⊕ Fin n, ‖(omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
              (gramMatrix (c.emb.eval n) θ)⁻¹)) r j‖ ≤
              ∑ r : Fin n ⊕ Fin n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) j.val) :=
              Finset.sum_le_sum fun r _ => PEnc.norm_le_bound (hNN r j) hθ
          _ = ∑ k ∈ Finset.range (n + n), val (pmBound (trN (α := α) n rb rm) k j.val) :=
              sum_phaseNat_eq (fun k => val (pmBound (trN (α := α) n rb rm) k j.val))
          _ ≤ bNt := sum_le_sumUp_bound (fun k _ => le_rfl) (hcol j.val j.isLt)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `trT_chain` from the bundled guards and stages. -/
theorem trT_chainOk {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hn : 1 ≤ n) (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    (hP : rb.P = bk.P) (hent : ptEntries n K W cfg pe rb.toT tm ms = true) {box : FreqBox} {s : ℚ}
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω)
    (hch : trTChainOk n Binv W cfg box s rb mm tm rm eps = true) :
    PMat.Encloses rb.Lw (rb.aT n) (2 * rb.P) n W.rho Fin.val Fin.val (trT (α := α) n rb rm)
      (fun θ => Matrix.of fun i j =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j)) := by
  simp only [trTChainOk, Bool.and_eq_true] at hch
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlay, hnrm⟩, hpk⟩, hN⟩, hDL⟩, hDG⟩, hC⟩, hDGi⟩, hDN⟩, hXN⟩ := hch
  exact trT_chain hD hnv hW hKD Binv cfg hpe hn hG heps hms hP hent hω hlay hnrm hpk hN hDL hDG
    hC hDGi hDN hXN

/-- Row sums of a matrix function from entrywise packed models whose packed weighted norms plus
radii pass a row-sum test (stated for any packed matrix, so `trT` is never unfolded). -/
theorem frameT_bound {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    {L : PackLayout} {q l A e : ℕ} {M : PMat α} {F : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    (hT : PMat.Encloses L A e n W.rho Fin.val Fin.val M F) (hok : normOk W q l A L = true)
    {bT : ℚ} (hrow : ∀ i < n, ble (sumUp (fun j => upAdd (pnorm W q l L e (M.x i j)) (M.r i j))
      (List.range n)) (ofRatDown bT) = true) :
    ∀ θ ∈ complexStrip n W.rho, ∀ i : Fin n, ∑ j : Fin n, ‖F θ i j‖ ≤ bT := by
  intro θ hθ i
  calc ∑ j : Fin n, ‖F θ i j‖ ≤
        ∑ j : Fin n, val (upAdd (pnorm W q l L e (M.x i.val j.val)) (M.r i.val j.val)) :=
        Finset.sum_le_sum fun j _ => PEnc.norm_le_bound ((hT i j).renorm hW hok) hθ
    _ = ∑ k ∈ Finset.range n, val (upAdd (pnorm W q l L e (M.x i.val k)) (M.r i.val k)) :=
        Fin.sum_univ_eq_sum_range (fun k => val (upAdd (pnorm W q l L e (M.x i.val k))
          (M.r i.val k))) n
    _ ≤ bT := sum_le_sumUp_bound (fun k _ => le_rfl) (hrow i.val i.isLt)

/-- The packed `sup |T|` bound. -/
theorem checkFrameTR_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D)
    (hE : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {bT : ℚ}
    (h : checkFrameTR bk mm rb tm rm c bT = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ i : Fin n, ∑ j : Fin n,
      ‖KAM.Iso.extendedTorsion c.H c.K ((c.params.s : ℝ) • ωstar) θ (Sum.inl i) (Sum.inl j)‖ ≤
        bT := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE θ hθ (Metric.mem_ball_self S.hμ)
  unfold checkFrameTR at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps ms heps hcomp
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hP, hent⟩, hch⟩, hTok⟩ := h
      have hms : SlotsEnclose n c.ham c.emb c.weight.rho ms := by
        have := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgLow S.hpe _ hcomp
        exact ⟨this.1, this.2⟩
      have hT := trT_chainOk (isOpen_certDomain _ _ _ _) hH S.hW hKD c.gramInv c.cfgLow S.hpe hn
        hG heps hms hP hent hω hch
      have nrm := trNormOk_spec (by simp only [trTChainOk, Bool.and_eq_true] at hch; tauto)
      simp only [trFrameTOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at hTok
      obtain ⟨haT, hrow⟩ := hTok
      exact frameT_bound S.hW (hT.mono (le_trans haT (Nat.le_add_right _ _))) nrm.nW hrow
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Soundness of the packed frame majorants**: the conclusion of the landed
`checkFrameMajorants_sound`, under its hypotheses. -/
theorem checkFrameMajorantsR_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {b : FrameBounds} (h : checkFrameMajorantsR bk mm rb tm rm c b = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) : FrameMajorants c b ωstar := by
  have S := checkStatic_sound hs
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ
    rwa [S.hrho]
  simp only [checkFrameMajorantsR, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hNc⟩, hTc⟩, hOm⟩ := h
  obtain ⟨hNr, hNt⟩ := checkFrameNR_sound hs hNc
  refine ⟨fun θ hθ j => checkFrameLR_sound hs hL θ (hstrip θ hθ) j,
    fun θ hθ r => hNr θ (hstrip θ hθ) r, fun θ hθ j => hNt θ (hstrip θ hθ) j,
    fun θ hθ i => checkFrameTR_sound hs hH.1 hE.1 hTc hω θ (hstrip θ hθ) i, ?_⟩
  unfold checkFrameOmega at hOm
  simp only [decide_eq_true_eq] at hOm
  exact (norm_le_freqNormUp hω).trans (by exact_mod_cast hOm)

omit [LawfulCertArith α] in
/-- The packed frame majorants from their parts: the facts shared with `checkTorsionR` (the Gram
check, the composition, the boundary entries, the guards, the stages) and the four frame tests
(for proofs split across declarations: each shared fact is established once). -/
theorem checkFrameMajorantsR_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {δβ : α × α} {eps : α} {ms : List (CertModel α)}
    {b : FrameBounds}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hcomp : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some ms) (hP : rb.P = bk.P)
    (hent : ptEntries n c.emb c.weight c.cfgLow c.piEnc rb.toT tm ms = true)
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n c.weight c.freqBox c.params.s rb = true)
    (hpk : ptPackOk n c.gramInv c.cfgLow rb.toT mm tm = true)
    (hN : trStN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hDL : trStDL (α := α) n c.weight c.freqBox c.params.s rb tm rm = true)
    (hDG : trStDG (α := α) n c.weight rb mm rm = true)
    (hC : trStC n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDGi : trStDGi n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDN : trStDN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hXN : trStXN (α := α) n c.weight rb tm rm = true)
    (hL : trFrameLOk (α := α) n c.weight rb mm b.bL = true)
    (hNok : trFrameNOk (α := α) n rb rm b.bN b.bNt = true)
    (hT : trFrameTOk (α := α) n c.weight rb rm b.bT = true) (hOm : checkFrameOmega c b.bOm = true) :
    checkFrameMajorantsR bk mm rb tm rm c b = true := by
  unfold checkFrameMajorantsR checkFrameLR checkFrameNR checkFrameTR trTChainOk
  rw [hG]
  dsimp only
  rw [heps, hcomp]
  dsimp only
  rw [hP, hent, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hL, hNok, hT, hOm]
  simp

end Sound

/-! ### The engine and the certifier -/

/-- The test of route A refined with the packed frames. -/
def refinedTestPacked (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) (w : RefinedWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorantsR bk mm rb tm rm c (w.R.frame c.freqBox) &&
    refinedCore n c.params c.freqBox w

/-- **Route A refined with the packed frames** (the landed disc pass and refined core). -/
def routeARefinedPacked (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) : EngineV2 where
  Wit := RefinedWit
  test := fun c w => refinedTestPacked bk mm rb tm rm c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestPacked, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    obtain ⟨h1, h2, h3, h4, -⟩ := checkFrameMajorantsR_sound B.hs B.hH B.hEm hF hω
    exact refinedCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) ⟨h1, h2, h3, h4⟩ hc

/-- **End to end**: a certificate passing the v2 certifier with the packed Gram, torsion and frame
checks (`torsRBase`, `routeARefinedPacked`) is a landed `CertifiedTorus`. -/
theorem checkV2With_packed_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    {c : TorusCertificate n α} {w : RefinedWit}
    (h : checkV2With (torsRBase bk mm rb tm rm) (routeARefinedPacked bk mm rb tm rm) c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound (torsRBase bk mm rb tm rm) (routeARefinedPacked bk mm rb tm rm) h hω hdio

end KAM.CertificateSharp.Packed
