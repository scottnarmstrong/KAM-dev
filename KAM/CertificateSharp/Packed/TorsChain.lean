/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Tors

/-!
# The packed torsion stage: the chain

The guards (`ptLayOk_spec`, `ptNormOk_spec`, `ptPackOk_spec`), the base packed models (`L = DK`
from the Gram memo, `G⁻¹` from the witness and the Gram check's radius, `∂_l L`, the frequency,
`D L`, `DX_H ∘ K`, `DH ∘ K`, each against its landed model) and the chain up to `T = Nᵀ (Ω₀ X_N)`
and `Y = DH N` (`ptT_encloses`, `ptY_encloses`): packed models of the matrices of the landed
`torsion_eq_models`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

/-! ### The guards -/

theorem layoutEq_eq {L L' : PackLayout} (h : layoutEq L L' = true) : L = L' := by
  cases L
  cases L'
  simp only [layoutEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4 h5
  rfl

theorem slot_zslot {n : ℕ} {L : PackLayout} (h : (L.slot (List.replicate n 0)).isSome = true) :
    L.slot (List.replicate n 0) = some (zslot n L) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  simp [zslot, hp]

/-- The layout facts of a passing `ptLayOk`. -/
structure PTLay (n : ℕ) (tb : PTorsBook) : Prop where
  w1 : layoutWf tb.L1 = true
  wB : layoutWf tb.LB = true
  wA : layoutWf tb.LA = true
  wU0 : layoutWf tb.LU0 = true
  wU1 : layoutWf tb.LU1 = true
  wU2 : layoutWf tb.LU2 = true
  cDL : PackLayout.compat n tb.L1 tb.LU0 = true
  cN : PackLayout.compat n tb.L1 tb.LB = true
  cDG1 : PackLayout.compat n tb.LDL tb.L1 = true
  cDG2 : PackLayout.compat n tb.L1 tb.LDL = true
  cC : PackLayout.compat n tb.LB tb.LDG = true
  cDGi : PackLayout.compat n tb.LC tb.LB = true
  cDLB : PackLayout.compat n tb.LDL tb.LB = true
  cU1 : PackLayout.compat n tb.LDLB tb.LU1 = true
  cLD : PackLayout.compat n tb.L1 tb.LDGi = true
  cAN : PackLayout.compat n tb.LA tb.LN = true
  cU2 : PackLayout.compat n tb.LAN tb.LU2 = true
  cT : PackLayout.compat n tb.LN tb.LDN = true
  eDG : win tb.L1 tb.LDL = tb.LDG
  eU1 : win tb.LDLB tb.LU1 = tb.LDN
  eU2 : win tb.LAN tb.LU2 = tb.LDN
  sU0 : tb.LU0.slot (List.replicate n 0) = some (zslot n tb.LU0)
  sU1 : tb.LU1.slot (List.replicate n 0) = some (zslot n tb.LU1)
  sU2 : tb.LU2.slot (List.replicate n 0) = some (zslot n tb.LU2)
  sT : tb.LT.slot (List.replicate n 0) = some (zslot n tb.LT)
  sAN : tb.LAN.slot (List.replicate n 0) = some (zslot n tb.LAN)

theorem ptLayOk_spec {n : ℕ} {tb : PTorsBook} (h : ptLayOk n tb = true) : PTLay n tb := by
  simp only [ptLayOk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    layoutEq_eq h19, layoutEq_eq h20, layoutEq_eq h21, slot_zslot h22, slot_zslot h23,
    slot_zslot h24, slot_zslot h25, slot_zslot h26⟩

namespace PTLay

variable {n : ℕ} {tb : PTorsBook} (lay : PTLay n tb)
include lay

theorem wDL : layoutWf tb.LDL = true := win_wf lay.cDL lay.w1 lay.wU0
theorem wN : layoutWf tb.LN = true := win_wf lay.cN lay.w1 lay.wB
theorem wDG : layoutWf tb.LDG = true := win_wf lay.cDG1 lay.wDL lay.w1
theorem wC : layoutWf tb.LC = true := win_wf lay.cC lay.wB lay.wDG
theorem wDGi : layoutWf tb.LDGi = true := win_wf lay.cDGi lay.wC lay.wB
theorem wDLB : layoutWf tb.LDLB = true := win_wf lay.cDLB lay.wDL lay.wB
theorem wDN : layoutWf tb.LDN = true := win_wf lay.cLD lay.w1 lay.wDGi
theorem wAN : layoutWf tb.LAN = true := win_wf lay.cAN lay.wA lay.wN
theorem wT : layoutWf tb.LT = true := win_wf lay.cT lay.wN lay.wDN

theorem dimsT : tb.LT.dims.length = n := by
  simp [PTorsBook.LT, win, (compat_spec lay.cT).1]

theorem dimsAN : tb.LAN.dims.length = n := by
  simp [PTorsBook.LAN, win, (compat_spec lay.cAN).1]

end PTLay

/-- The load facts of a passing `ptNormOk`. -/
structure PTNorm (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (tb : PTorsBook) : Prop where
  nK : normOk W tb.q tb.lK tb.bK tb.L1 = true
  nB : normOk W tb.q tb.lB tb.bB tb.LB = true
  nD : normOk W tb.q tb.lD tb.bD tb.L1 = true
  nA : normOk W tb.q tb.lA tb.bA tb.LA = true
  nDL : normOk W tb.q tb.lDL (tb.aDL n) tb.LDL = true
  nN : normOk W tb.q tb.lN (tb.aN n) tb.LN = true
  nDG : normOk W tb.q tb.lDG (tb.aDG n) tb.LDG = true
  nC : normOk W tb.q tb.lC (tb.aC n) tb.LC = true
  nDGi : normOk W tb.q tb.lDGi (tb.aDGi n) tb.LDGi = true
  nXN : normOk W tb.q tb.lXN (tb.aXN n) tb.LDN = true
  fT : 2 * tb.aT n < 2 ^ tb.LT.width
  fY : 2 * tb.aY n < 2 ^ tb.LAN.width
  fF : ∀ l < n, (ptFc box s tb l).natAbs ≤ tb.bF

theorem ptNormOk_spec {n : ℕ} {W : CertWeight} {box : FreqBox} {s : ℚ} {tb : PTorsBook}
    (h : ptNormOk n W box s tb = true) : PTNorm n W box s tb := by
  simp only [ptNormOk, Bool.and_eq_true, and_assoc, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The packing facts of a passing `ptPackOk`. -/
structure PTPack {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α)))
    (cfg : ModelConfig α) (tb : PTorsBook) (mm : PGramMemo) (tm : PTorsMemo) : Prop where
  pK : ∀ r < n + n, ∀ a < n, packRepOk tb.L1 (mm.reAt r a) tb.bK = true ∧
    packRepOk tb.L1 (mm.imAt r a) tb.bK = true
  pB : ∀ i < n, ∀ k < n, pcOfPolyOk cfg.toMant tb.P tb.LB tb.bB (gramInvPoly Binv i k) = true
  pD : ∀ r < n + n, ∀ j < n, ∀ l < n,
    memoPackOk tb.L1 tb.bD (tm.d2.getD (d2Idx n r j l) ([], [], 0)) = true
  pA : ∀ a < n + n, ∀ b < n + n,
    memoPackOk tb.LA tb.bA (tm.ax.getD (a * (n + n) + b) ([], [], 0)) = true
  pD1 : ∀ a < n + n, memoPackOk tb.LA tb.bA (tm.d1.getD a ([], [], 0)) = true

theorem ptPackOk_spec {α : Type} [CertArith α] {n : ℕ} {Binv : List (List (CertPoly α))}
    {cfg : ModelConfig α} {tb : PTorsBook} {mm : PGramMemo} {tm : PTorsMemo}
    (h : ptPackOk n Binv cfg tb mm tm = true) : PTPack n Binv cfg tb mm tm := by
  simp only [ptPackOk, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ### The base packed models -/

section Base

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {sw Nw : ℕ}
  {cfg : ModelConfig α} {pe : PiEnclosure α} {tb : PTorsBook} {mm : PGramMemo} {tm : PTorsMemo}

omit [LawfulCertArith α] in
theorem PMat.Encloses.cast {ι κ : Type*} {ri : ι → ℕ} {ci : κ → ℕ} {L L' : PackLayout}
    {A A' e e' : ℕ} {ρ : ℝ} {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (h : PMat.Encloses L A e n ρ ri ci M F) (hL : L = L') (hA : A = A') (he : e = e') :
    PMat.Encloses L' A' e' n ρ ri ci M F := by
  subst hL hA he
  exact h

/-- `L = DK` from the Gram memo. -/
theorem ptK_encloses (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) {bk : PGramBook} (he : pgEntries n K W cfg pe bk mm = true)
    (hP : tb.P = bk.P) (hw : layoutWf tb.L1 = true)
    (hpk : ∀ r < n + n, ∀ a < n, packRepOk tb.L1 (mm.reAt r a) tb.bK = true ∧
      packRepOk tb.L1 (mm.imAt r a) tb.bK = true)
    (hok : normOk W tb.q tb.lK tb.bK tb.L1 = true) :
    PMat.Encloses tb.L1 tb.bK tb.P n W.rho phaseNat Fin.val (ptK (α := α) W tb mm)
      (tangentMat (K.eval n)) := by
  intro x a
  have hr : phaseNat x < 2 * n := by have := phaseNat_lt_add x; omega
  obtain ⟨hd, hmt, hrad⟩ := pgEntries_spec he hr a.isLt
  have hm := dkModels_encloses hW hpe K x a
  rw [dkModels, buildMat_entry _ (phaseNat_lt_add _) a.isLt] at hm
  have hm' : (dkModel n K W pe (phaseNat x) a.val).Encloses n W.rho
      (fun θ => tangentMat (K.eval n) θ x a) := hm
  rw [← hP] at hmt
  obtain ⟨hre, him⟩ := hpk _ (phaseNat_lt_add x) _ a.isLt
  exact PEnc.ofPCRep hW hok (PCRep.ofMants hmt hw hre him) fun θ hθ =>
    (encloses_deg0 hm' hd hθ).trans (LawfulCertArith.ble_sound _ _ hrad)

/-- `G⁻¹` from the witness `B` and a radius. -/
theorem ptB_encloses (hW : checkWeight W sw Nw = true) {Binv : List (List (CertPoly α))}
    (hw : layoutWf tb.LB = true)
    (hpk : ∀ i < n, ∀ k < n, pcOfPolyOk cfg.toMant tb.P tb.LB tb.bB (gramInvPoly Binv i k) = true)
    (hok : normOk W tb.q tb.lB tb.bB tb.LB = true) {eps : α}
    {F : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ θ ∈ complexStrip n W.rho, ‖F θ - polyMatrix n Binv θ‖ ≤ val eps) :
    PMat.Encloses tb.LB tb.bB tb.P n W.rho Fin.val Fin.val (ptB Binv W cfg tb eps) F := by
  intro i k
  refine PEnc.ofPCRep hW hok (PCRep.ofPoly hw (hpk i i.isLt k k.isLt) n) fun θ hθ => ?_
  have := (norm_entry_le (F θ - polyMatrix n Binv θ) i k).trans (hF θ hθ)
  rwa [Matrix.sub_apply, polyMatrix_apply] at this

/-- `∂_l L` from the torsion memo. -/
theorem ptD2_encloses (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) (hw : layoutWf tb.L1 = true)
    (hent : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe tb tm r j l = true)
    (hpk : ∀ r < n + n, ∀ j < n, ∀ l < n,
      memoPackOk tb.L1 tb.bD (tm.d2.getD (d2Idx n r j l) ([], [], 0)) = true)
    (hok : normOk W tb.q tb.lD tb.bD tb.L1 = true) (l : Fin n) :
    PMat.Encloses tb.L1 tb.bD tb.P n W.rho phaseNat Fin.val (ptD2 (α := α) n W tb tm l.val)
      (fun θ => Matrix.of fun x j =>
        fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1)) := by
  intro x j
  exact (PEnc.ofMemo hW hok hw (d2kModel_encloses hW hpe K x j l)
    (hent _ (phaseNat_lt_add x) _ j.isLt _ l.isLt)
    (hpk _ (phaseNat_lt_add x) _ j.isLt _ l.isLt)).congr fun θ _ => by simp

/-- The frequency coordinate `(s ω)_l` as a packed constant. -/
theorem ptF_encloses (hw : layoutWf tb.LU0 = true)
    (hs0 : tb.LU0.slot (List.replicate n 0) = some (zslot n tb.LU0)) {box : FreqBox} {s : ℚ}
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) (l : Fin n)
    (hbF : (ptFc box s tb l.val).natAbs ≤ tb.bF) (ρ : ℝ) :
    PEnc tb.LU0 tb.bF tb.P (ptF n box s tb l.val) (ofRatUp (ptFr box s tb l.val) : α)
      (ofRatUp (|(ptFc box s tb l.val : ℚ)| / 2 ^ tb.P)) n ρ
      (fun _ => ((((s : ℝ) • ω) l : ℝ) : ℂ)) := by
  refine ⟨_, (PCRep.unit hw hs0 (ptFc box s tb l.val)).mono hbF, fun θ _ => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (LawfulCertArith.ofRatUp_ge _)
    set c := (box.getD l.val (0, 0)).1
    set r := (box.getD l.val (0, 0)).2
    set fc := ptFc box s tb l.val
    have hb : |ω l - (c : ℝ)| ≤ (r : ℝ) := hω l
    have e1 : ((((s : ℝ) • ω) l : ℝ) : ℂ) - (fc : ℂ) / 2 ^ tb.P =
        (((s : ℝ) * (ω l - c) + ((s : ℝ) * c - (fc : ℝ) / 2 ^ tb.P) : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1, Complex.norm_real, Real.norm_eq_abs]
    have hfr : (ptFr box s tb l.val : ℝ) =
        |(s : ℝ)| * r + |(s : ℝ) * c - (fc : ℝ) / 2 ^ tb.P| := by
      simp only [ptFr]
      push_cast
      rfl
    rw [hfr]
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  · refine le_trans (le_of_eq ?_) (LawfulCertArith.ofRatUp_ge _)
    rw [norm_div, norm_pow, Complex.norm_intCast, Complex.norm_two]
    push_cast
    rfl

/-- `D L = Σ_l (s ω)_l ∂_l L`. -/
theorem ptDL_encloses (hW : checkWeight W sw Nw = true) (K : CertEmbedding α)
    (lay : PTLay n tb) {box : FreqBox} {s : ℚ} {ω : Fin n → ℝ}
    (hD2 : ∀ l : Fin n, PMat.Encloses tb.L1 tb.bD tb.P n W.rho phaseNat Fin.val
      (ptD2 (α := α) n W tb tm l.val) (fun θ => Matrix.of fun x j =>
        fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1)))
    (hF : ∀ l : Fin n, PEnc tb.LU0 tb.bF tb.P (ptF n box s tb l.val)
      (ofRatUp (ptFr box s tb l.val) : α) (ofRatUp (|(ptFc box s tb l.val : ℚ)| / 2 ^ tb.P)) n
      W.rho (fun _ => ((((s : ℝ) • ω) l : ℝ) : ℂ)))
    (hok : normOk W tb.q tb.lDL (tb.aDL n) tb.LDL = true) :
    PMat.Encloses tb.LDL (tb.aDL n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptDL (α := α) n W box s tb tm)
      (fun θ => fderiv ℂ (tangentMat (K.eval n)) θ (fun l => ((((s : ℝ) • ω) l : ℝ) : ℂ))) := by
  intro x j
  let fk : ℕ → (Fin n → ℂ) → ℂ := fun l θ => if hl : l < n then
    fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single ⟨l, hl⟩ 1) *
      ((((s : ℝ) • ω) ⟨l, hl⟩ : ℝ) : ℂ) else 0
  have hk : ∀ l < n, PEnc (win tb.L1 tb.LU0) (mulLoad tb.L1 tb.LU0 tb.bD tb.bF) (tb.P + tb.P)
      (pcMul ((ptD2 (α := α) n W tb tm l).x (phaseNat x) j.val) (ptF n box s tb l))
      (pmulRad ((ptD2 (α := α) n W tb tm l).nb (phaseNat x) j.val)
        ((ptD2 (α := α) n W tb tm l).r (phaseNat x) j.val)
        (ofRatUp (|(ptFc box s tb l : ℚ)| / 2 ^ tb.P)) (ofRatUp (ptFr box s tb l)))
      (upMul ((ptD2 (α := α) n W tb tm l).nb (phaseNat x) j.val)
        (ofRatUp (|(ptFc box s tb l : ℚ)| / 2 ^ tb.P))) n W.rho (fk l) := by
    intro l hl
    refine (PEnc.mul lay.cDL lay.w1 lay.wU0 (hD2 ⟨l, hl⟩ x j) (hF ⟨l, hl⟩)).congr fun θ _ => ?_
    simp only [fk, hl, ↓reduceDIte, Matrix.of_apply]
  have hs := (PEnc.sumN n hk).renorm hW (L := tb.LDL) (by
    have hload : ((List.range n).map fun _ : ℕ => mulLoad tb.L1 tb.LU0 tb.bD tb.bF).sum =
        tb.aDL n := by simp [PTorsBook.aDL]
    rw [hload]
    exact hok)
  have hload : ((List.range n).map fun _ : ℕ => mulLoad tb.L1 tb.LU0 tb.bD tb.bF).sum =
      tb.aDL n := by simp [PTorsBook.aDL]
  rw [hload, ← two_mul] at hs
  unfold ptDL PMat.renorm
  dsimp only
  refine hs.congr fun θ hθ => ?_
  have hLd := differentiableOn_tangentMat (r := W.rho) (K.differentiable_eval n).differentiableOn
  rw [fderiv_tangentMat_eq_sum_partials
    (hLd.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ)),
    ← Fin.sum_univ_eq_sum_range (fun l => fk l θ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [fk, l.isLt, ↓reduceDIte, Fin.eta]
  ring

/-- `DX_H ∘ K` from the torsion memo. -/
theorem ptA_encloses (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α}
    (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) (hw : layoutWf tb.LA = true)
    (hent : ∀ a < n + n, ∀ b < n + n, ptAOk n W cfg pe tb tm ms a b = true)
    (hpk : ∀ a < n + n, ∀ b < n + n,
      memoPackOk tb.LA tb.bA (tm.ax.getD (a * (n + n) + b) ([], [], 0)) = true)
    (hok : normOk W tb.q tb.lA tb.bA tb.LA = true) :
    PMat.Encloses tb.LA tb.bA tb.P n W.rho phaseNat phaseNat (ptA (α := α) n W tb tm)
      (linMat e.eval (K.eval n)) := by
  intro a b
  exact PEnc.ofMemo hW hok hw ((dxhModels_encloses hD hnv hKD hms a b).toDeg hW hpe 0)
    (hent _ (phaseNat_lt_add a) _ (phaseNat_lt_add b))
    (hpk _ (phaseNat_lt_add a) _ (phaseNat_lt_add b))

/-- `DH ∘ K` from the torsion memo. -/
theorem ptD1_encloses (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α}
    (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) (hw : layoutWf tb.LA = true)
    (hent : ∀ a < n + n, ptD1Ok n W cfg pe tb tm ms a = true)
    (hpk : ∀ a < n + n, memoPackOk tb.LA tb.bA (tm.d1.getD a ([], [], 0)) = true)
    (hok : normOk W tb.q tb.lA tb.bA tb.LA = true) :
    PMat.Encloses tb.LA tb.bA tb.P n W.rho (fun _ : Unit => 0) phaseNat (ptD1 (α := α) W tb tm)
      (fun θ => Matrix.of fun _ a => fderiv ℂ e.eval (K.eval n θ) (phaseBasis a)) := by
  intro u a
  exact PEnc.ofMemo hW hok hw ((d1Models_encloses hD hnv hKD hms u a).toDeg hW hpe 0)
    (hent _ (phaseNat_lt_add a)) (hpk _ (phaseNat_lt_add a))

/-- The unit `2^(3P)` at the zero key of a shift layout. -/
theorem ptU_rep {L : PackLayout} (hw : layoutWf L = true)
    (hs : L.slot (List.replicate n 0) = some (zslot n L)) :
    PCRep L (2 ^ (3 * tb.P)) (ptU n tb L) n (fun _ => (2 : ℂ) ^ (3 * tb.P)) := by
  have h := PCRep.unit hw hs ((2 : ℤ) ^ (3 * tb.P))
  rw [Int.natAbs_pow] at h
  exact h.congr fun θ => by push_cast; rfl

end Base

/-! ### The chain -/

section Chain

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {sw Nw : ℕ}
  {cfg : ModelConfig α} {tb : PTorsBook} {mm : PGramMemo} {tm : PTorsMemo}
  {Binv : List (List (CertPoly α))} {box : FreqBox} {s : ℚ} {eps : α}
  {FL FDL FN FDN FXN : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
  {FG FDG FC FDGi : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
  {FA : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}

/-- `N = Ω₀ (L G⁻¹)`. -/
theorem ptN_encloses (hW : checkWeight W sw Nw = true) (lay : PTLay n tb)
    (nrm : PTNorm n W box s tb)
    (hK : PMat.Encloses tb.L1 tb.bK tb.P n W.rho phaseNat Fin.val (ptK (α := α) W tb mm) FL)
    (hB : PMat.Encloses tb.LB tb.bB tb.P n W.rho Fin.val Fin.val (ptB Binv W cfg tb eps) FG) :
    PMat.Encloses tb.LN (tb.aN n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptN n Binv W cfg tb mm eps) (fun θ => omegaZeroMatrix n * (FL θ * FG θ)) := by
  have h := (hK.mul lay.cN lay.w1 lay.wB (Equiv.refl (Fin n)) (fun _ => rfl) hB).omega
  exact (h.cast rfl rfl (two_mul _).symm).renorm hW nrm.nN

/-- `DG = D Lᵀ L + Lᵀ D L`. -/
theorem ptDG_encloses (hW : checkWeight W sw Nw = true) (lay : PTLay n tb)
    (nrm : PTNorm n W box s tb)
    (hK : PMat.Encloses tb.L1 tb.bK tb.P n W.rho phaseNat Fin.val (ptK (α := α) W tb mm) FL)
    (hDL : PMat.Encloses tb.LDL (tb.aDL n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptDL (α := α) n W box s tb tm) FDL) :
    PMat.Encloses tb.LDG (tb.aDG n) (3 * tb.P) n W.rho Fin.val Fin.val
      (ptDG (α := α) n W box s tb mm tm) (fun θ => (FDL θ)ᵀ * FL θ + (FL θ)ᵀ * FDL θ) := by
  have h1 := hDL.tr.mul lay.cDG1 lay.wDL lay.w1 finSumFinEquiv.symm
    phaseNat_finSumFinEquiv_symm hK
  have h2 := hK.tr.mul lay.cDG2 lay.w1 lay.wDL finSumFinEquiv.symm
    phaseNat_finSumFinEquiv_symm hDL
  have h1' := h1.cast rfl rfl (by ring : 2 * tb.P + tb.P = 3 * tb.P)
  have h2' := h2.cast lay.eDG rfl (by ring : tb.P + 2 * tb.P = 3 * tb.P)
  exact (h1'.add h2').renorm hW nrm.nDG

/-- `C = G⁻¹ DG`. -/
theorem ptC_encloses (hW : checkWeight W sw Nw = true) (lay : PTLay n tb)
    (nrm : PTNorm n W box s tb)
    (hB : PMat.Encloses tb.LB tb.bB tb.P n W.rho Fin.val Fin.val (ptB Binv W cfg tb eps) FG)
    (hDG : PMat.Encloses tb.LDG (tb.aDG n) (3 * tb.P) n W.rho Fin.val Fin.val
      (ptDG (α := α) n W box s tb mm tm) FDG) :
    PMat.Encloses tb.LC (tb.aC n) (4 * tb.P) n W.rho Fin.val Fin.val
      (ptC n Binv W cfg box s tb mm tm eps) (fun θ => FG θ * FDG θ) := by
  have h := hB.mul lay.cC lay.wB lay.wDG (Equiv.refl (Fin n)) (fun _ => rfl) hDG
  exact (h.cast rfl rfl (by ring)).renorm hW nrm.nC

/-- `D(G⁻¹) = -(C G⁻¹)`. -/
theorem ptDGi_encloses (hW : checkWeight W sw Nw = true) (lay : PTLay n tb)
    (nrm : PTNorm n W box s tb)
    (hC : PMat.Encloses tb.LC (tb.aC n) (4 * tb.P) n W.rho Fin.val Fin.val
      (ptC n Binv W cfg box s tb mm tm eps) FC)
    (hB : PMat.Encloses tb.LB tb.bB tb.P n W.rho Fin.val Fin.val (ptB Binv W cfg tb eps) FG) :
    PMat.Encloses tb.LDGi (tb.aDGi n) (5 * tb.P) n W.rho Fin.val Fin.val
      (ptDGi n Binv W cfg box s tb mm tm eps) (fun θ => -(FC θ * FG θ)) := by
  have h := hC.mul lay.cDGi lay.wC lay.wB (Equiv.refl (Fin n)) (fun _ => rfl) hB
  exact ((h.cast rfl rfl (by ring)).renorm hW nrm.nDGi).neg

/-- `DN = Ω₀ (D L G⁻¹ + L D(G⁻¹))`. -/
theorem ptDN_encloses (lay : PTLay n tb)
    (hK : PMat.Encloses tb.L1 tb.bK tb.P n W.rho phaseNat Fin.val (ptK (α := α) W tb mm) FL)
    (hB : PMat.Encloses tb.LB tb.bB tb.P n W.rho Fin.val Fin.val (ptB Binv W cfg tb eps) FG)
    (hDL : PMat.Encloses tb.LDL (tb.aDL n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptDL (α := α) n W box s tb tm) FDL)
    (hDGi : PMat.Encloses tb.LDGi (tb.aDGi n) (5 * tb.P) n W.rho Fin.val Fin.val
      (ptDGi n Binv W cfg box s tb mm tm eps) FDGi) :
    PMat.Encloses tb.LDN (tb.aDN n) (6 * tb.P) n W.rho phaseNat Fin.val
      (ptDN n Binv W cfg box s tb mm tm eps)
      (fun θ => omegaZeroMatrix n * (FDL θ * FG θ + FL θ * FDGi θ)) := by
  have h1 := (hDL.mul lay.cDLB lay.wDL lay.wB (Equiv.refl (Fin n)) (fun _ => rfl) hB).shift
    lay.cU1 lay.wDLB lay.wU1 (ptU_rep (tb := tb) lay.wU1 lay.sU1)
  have h2 := hK.mul lay.cLD lay.w1 lay.wDGi (Equiv.refl (Fin n)) (fun _ => rfl) hDGi
  exact ((h1.cast lay.eU1 rfl (by ring)).add (h2.cast rfl rfl (by ring))).omega

/-- `X_N = A N - DN`. -/
theorem ptXN_encloses (hW : checkWeight W sw Nw = true) (lay : PTLay n tb)
    (nrm : PTNorm n W box s tb)
    (hA : PMat.Encloses tb.LA tb.bA tb.P n W.rho phaseNat phaseNat (ptA (α := α) n W tb tm) FA)
    (hN : PMat.Encloses tb.LN (tb.aN n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptN n Binv W cfg tb mm eps) FN)
    (hDN : PMat.Encloses tb.LDN (tb.aDN n) (6 * tb.P) n W.rho phaseNat Fin.val
      (ptDN n Binv W cfg box s tb mm tm eps) FDN) :
    PMat.Encloses tb.LDN (tb.aXN n) (6 * tb.P) n W.rho phaseNat Fin.val
      (ptXN n Binv W cfg box s tb mm tm eps) (fun θ => FA θ * FN θ + -FDN θ) := by
  have h1 := (hA.mul lay.cAN lay.wA lay.wN finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm
    hN).shift lay.cU2 lay.wAN lay.wU2 (ptU_rep (tb := tb) lay.wU2 lay.sU2)
  exact ((h1.cast lay.eU2 rfl (by ring)).add hDN.neg).renorm hW nrm.nXN

/-- `T = Nᵀ (Ω₀ X_N)`. -/
theorem ptT_encloses (lay : PTLay n tb)
    (hN : PMat.Encloses tb.LN (tb.aN n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptN n Binv W cfg tb mm eps) FN)
    (hXN : PMat.Encloses tb.LDN (tb.aXN n) (6 * tb.P) n W.rho phaseNat Fin.val
      (ptXN n Binv W cfg box s tb mm tm eps) FXN) :
    PMat.Encloses tb.LT (tb.aT n) (8 * tb.P) n W.rho Fin.val Fin.val
      (ptT n Binv W cfg box s tb mm tm eps)
      (fun θ => (FN θ)ᵀ * (omegaZeroMatrix n * FXN θ)) := by
  have h := hN.tr.mul lay.cT lay.wN lay.wDN finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm
    hXN.omega
  exact h.cast rfl rfl (by ring)

/-- `Y = DH N`. -/
theorem ptY_encloses (lay : PTLay n tb) {FD1 : (Fin n → ℂ) → Matrix Unit (Fin n ⊕ Fin n) ℂ}
    (hD1 : PMat.Encloses tb.LA tb.bA tb.P n W.rho (fun _ : Unit => 0) phaseNat
      (ptD1 (α := α) W tb tm) FD1)
    (hN : PMat.Encloses tb.LN (tb.aN n) (2 * tb.P) n W.rho phaseNat Fin.val
      (ptN n Binv W cfg tb mm eps) FN) :
    PMat.Encloses tb.LAN (tb.aY n) (3 * tb.P) n W.rho (fun _ : Unit => 0) Fin.val
      (ptY n Binv W cfg tb mm tm eps) (fun θ => FD1 θ * FN θ) := by
  have h := hD1.mul lay.cAN lay.wA lay.wN finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN
  exact h.cast rfl rfl (by ring)

end Chain

end KAM.CertificateSharp.Packed
