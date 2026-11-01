/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsR

/-!
# The rounded packed torsion stage: the chain

The guards (`trLayOk_spec`, `trNormOk_spec`), the exact `D L` on the box (`trDL0_encloses`), and the
memoized nodes as packed models of the matrices of the landed `torsion_eq_models`
(`trNm_encloses … trXNm_encloses`), each through `PMat.Encloses.stage`; then `T` and `Y` on the
window (`trT_encloses`, `trY_encloses`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

/-- The layout facts of a passing `trLayOk`. -/
structure TRLay (n : ℕ) (rb : PRBook) : Prop where
  wb : layoutWf rb.Lb = true
  wu : layoutWf rb.Lu = true
  w0 : layoutWf rb.LU0 = true
  cbb : PackLayout.compat n rb.Lb rb.Lb = true
  cbu : PackLayout.compat n rb.Lb rb.Lu = true
  cb0 : PackLayout.compat n rb.Lb rb.LU0 = true
  eu : win rb.Lb rb.Lu = rb.Lw
  su : rb.Lu.slot (List.replicate n 0) = some (zslot n rb.Lu)
  s0 : rb.LU0.slot (List.replicate n 0) = some (zslot n rb.LU0)
  sw : rb.Lw.slot (List.replicate n 0) = some (zslot n rb.Lw)

theorem trLayOk_spec {n : ℕ} {rb : PRBook} (h : trLayOk n rb = true) : TRLay n rb := by
  simp only [trLayOk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, layoutEq_eq h7, slot_zslot h8, slot_zslot h9, slot_zslot h10⟩

theorem TRLay.wW {n : ℕ} {rb : PRBook} (lay : TRLay n rb) : layoutWf rb.Lw = true :=
  win_wf lay.cbb lay.wb lay.wb

theorem TRLay.dimsW {n : ℕ} {rb : PRBook} (lay : TRLay n rb) : rb.Lw.dims.length = n := by
  simp [PRBook.Lw, win, (compat_spec lay.cbb).1]

/-- The load facts of a passing `trNormOk`. -/
structure TRNorm (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (rb : PRBook) : Prop where
  nK : normOk W rb.q rb.lK rb.bK rb.Lb = true
  nB : normOk W rb.q rb.lB rb.bB rb.Lb = true
  nD : normOk W rb.q rb.lD rb.bD rb.Lb = true
  nA : normOk W rb.q rb.lA rb.bA rb.Lb = true
  nR : normOk W rb.q rb.lR rb.bR rb.Lb = true
  nW : normOk W rb.q rb.lW (rb.aW + mulLoad rb.Lb rb.Lu rb.bR (2 ^ rb.P)) rb.Lw = true
  nL : normOk W rb.q rb.lL (rb.aL + mulLoad rb.Lb rb.LU0 rb.bR (2 ^ rb.P)) rb.LL = true
  hN : rb.aN n ≤ rb.aW
  hDL : rb.aDL n ≤ rb.aL
  hDG : rb.aDG n ≤ rb.aW
  hC : rb.aC n ≤ rb.aW
  hDGi : rb.aDGi n ≤ rb.aW
  hDN : rb.aDN n ≤ rb.aW
  hXN : rb.aXN n ≤ rb.aW
  fT : 2 * rb.aT n < 2 ^ rb.Lw.width
  fY : 2 * rb.aY n < 2 ^ rb.Lw.width
  fF : ∀ l < n, (ptFc box s rb.toT l).natAbs ≤ rb.bF

theorem trNormOk_spec {n : ℕ} {W : CertWeight} {box : FreqBox} {s : ℚ} {rb : PRBook}
    (h : trNormOk n W box s rb = true) : TRNorm n W box s rb := by
  simp only [trNormOk, Bool.and_eq_true, and_assoc, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

section Chain

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {sw Nw : ℕ}
  {cfg : ModelConfig α} {rb : PRBook} {mm : PGramMemo} {tm : PTorsMemo} {rm : PRMemo}
  {Binv : List (List (CertPoly α))} {box : FreqBox} {s : ℚ} {eps : α}
  {FL FDL FN FDN FXN : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
  {FG FDG FC : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
  {FA : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}

/-- The power `2^k` at the zero key of a layout. -/
theorem pow_unit_rep {L : PackLayout} (hw : layoutWf L = true)
    (hs : L.slot (List.replicate n 0) = some (zslot n L)) (k : ℕ) :
    PCRep L (2 ^ k) (pcUnit L.width (zslot n L) (2 ^ k)) n (fun _ => (2 : ℂ) ^ k) := by
  have h := PCRep.unit hw hs ((2 : ℤ) ^ k)
  rw [Int.natAbs_pow] at h
  exact h.congr fun θ => by push_cast; rfl

/-- `D L = Σ_l (s ω)_l ∂_l L` exactly, on the box times the zero key. -/
theorem trDL0_encloses (K : CertEmbedding α) (lay : TRLay n rb) {ω : Fin n → ℝ}
    (hD2 : ∀ l : Fin n, PMat.Encloses rb.Lb rb.bD rb.P n W.rho phaseNat Fin.val
      (ptD2 (α := α) n W rb.toT tm l.val) (fun θ => Matrix.of fun x j =>
        fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1)))
    (hF : ∀ l : Fin n, PEnc rb.LU0 rb.bF rb.P (ptF n box s rb.toT l.val)
      (ofRatUp (ptFr box s rb.toT l.val) : α)
      (ofRatUp (|(ptFc box s rb.toT l.val : ℚ)| / 2 ^ rb.P)) n W.rho
      (fun _ => ((((s : ℝ) • ω) l : ℝ) : ℂ))) :
    PMat.Encloses rb.LL (rb.aDL n) (2 * rb.P) n W.rho phaseNat Fin.val
      (trDL0 (α := α) n W box s rb tm)
      (fun θ => fderiv ℂ (tangentMat (K.eval n)) θ (fun l => ((((s : ℝ) • ω) l : ℝ) : ℂ))) := by
  intro x j
  let fk : ℕ → (Fin n → ℂ) → ℂ := fun l θ => if hl : l < n then
    fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single ⟨l, hl⟩ 1) *
      ((((s : ℝ) • ω) ⟨l, hl⟩ : ℝ) : ℂ) else 0
  have hk : ∀ l < n, PEnc (win rb.Lb rb.LU0) (mulLoad rb.Lb rb.LU0 rb.bD rb.bF) (rb.P + rb.P)
      (pcMul ((ptD2 (α := α) n W rb.toT tm l).x (phaseNat x) j.val) (ptF n box s rb.toT l))
      (pmulRad ((ptD2 (α := α) n W rb.toT tm l).nb (phaseNat x) j.val)
        ((ptD2 (α := α) n W rb.toT tm l).r (phaseNat x) j.val)
        (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P)) (ofRatUp (ptFr box s rb.toT l)))
      (upMul ((ptD2 (α := α) n W rb.toT tm l).nb (phaseNat x) j.val)
        (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P))) n W.rho (fk l) := by
    intro l hl
    refine (PEnc.mul lay.cb0 lay.wb lay.w0 (hD2 ⟨l, hl⟩ x j) (hF ⟨l, hl⟩)).congr fun θ _ => ?_
    simp only [fk, hl, ↓reduceDIte, Matrix.of_apply]
  have hs := PEnc.sumN n hk
  have hload : ((List.range n).map fun _ : ℕ => mulLoad rb.Lb rb.LU0 rb.bD rb.bF).sum =
      rb.aDL n := by simp [PRBook.aDL]
  rw [hload, ← two_mul] at hs
  unfold trDL0
  dsimp only
  refine hs.congr fun θ hθ => ?_
  have hLd := differentiableOn_tangentMat (r := W.rho) (K.differentiable_eval n).differentiableOn
  rw [fderiv_tangentMat_eq_sum_partials
    (hLd.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ)),
    ← Fin.sum_univ_eq_sum_range (fun l => fk l θ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [fk, l.isLt, ↓reduceDIte, Fin.eta]
  ring

omit [LawfulCertArith α] in
theorem two_mul_sub (P : ℕ) : 2 * P - P = P := by omega

/-- A node checked on the window: from the exact product to the memo. -/
theorem trStage_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb) {R C : ℕ} {ι κ : Type*} {ri : ι → ℕ} {ci : κ → ℕ}
    (hri : ∀ i, ri i < R) (hci : ∀ j, ci j < C) {A : ℕ} (hA : A ≤ rb.aW) {M : PMat α}
    {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hM : PMat.Encloses rb.Lw A (rb.P + rb.P) n W.rho ri ci M F) {tab : List (List NodeEntry)}
    (h : trStage n W rb R C M tab = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho ri ci (nodeMat (α := α) rb.Lb tab) F := by
  have h1 := (hM.mono hA).cast rfl rfl (two_mul rb.P).symm
  have h2 := h1.stage hW lay.cbu lay.wb lay.wu lay.eu lay.su (by omega) nrm.nW nrm.nR hri hci h
  exact h2.cast rfl rfl (two_mul_sub rb.P)

/-- `N` (before `Ω₀`): `L G⁻¹`. -/
theorem trNm_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hK : PMat.Encloses rb.Lb rb.bK rb.P n W.rho phaseNat Fin.val (ptK (α := α) W rb.toT mm) FL)
    (hB : PMat.Encloses rb.Lb rb.bB rb.P n W.rho Fin.val Fin.val (ptB Binv W cfg rb.toT eps) FG)
    (h : trStN n Binv W cfg rb mm rm eps = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (nodeMat (α := α) rb.Lb rm.N)
      (fun θ => FL θ * FG θ) :=
  trStage_encloses hW lay nrm phaseNat_lt_add (fun j => j.isLt) nrm.hN
    (hK.mul lay.cbb lay.wb lay.wb (Equiv.refl (Fin n)) (fun _ => rfl) hB) h

/-- `D L`: from the exact sum on the box. -/
theorem trDLm_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hDL : PMat.Encloses rb.LL (rb.aDL n) (2 * rb.P) n W.rho phaseNat Fin.val
      (trDL0 (α := α) n W box s rb tm) FDL)
    (h : trStDL (α := α) n W box s rb tm rm = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (nodeMat (α := α) rb.Lb rm.DL) FDL := by
  have h2 := (hDL.mono nrm.hDL).stage hW lay.cb0 lay.wb lay.w0 rfl lay.s0 (by omega) nrm.nL nrm.nR
    phaseNat_lt_add (fun j => j.isLt) h
  exact h2.cast rfl rfl (two_mul_sub rb.P)

/-- `DG = D Lᵀ L + Lᵀ D L`. -/
theorem trDGm_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hK : PMat.Encloses rb.Lb rb.bK rb.P n W.rho phaseNat Fin.val (ptK (α := α) W rb.toT mm) FL)
    (hDL : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val
      (nodeMat (α := α) rb.Lb rm.DL) FDL)
    (h : trStDG (α := α) n W rb mm rm = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val (nodeMat (α := α) rb.Lb rm.DG)
      (fun θ => (FDL θ)ᵀ * FL θ + (FL θ)ᵀ * FDL θ) :=
  trStage_encloses hW lay nrm (fun i => i.isLt) (fun j => j.isLt) nrm.hDG
    ((hDL.tr.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hK).add
      (hK.tr.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hDL)) h

/-- `C = G⁻¹ DG`. -/
theorem trCm_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hB : PMat.Encloses rb.Lb rb.bB rb.P n W.rho Fin.val Fin.val (ptB Binv W cfg rb.toT eps) FG)
    (hDG : PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val
      (nodeMat (α := α) rb.Lb rm.DG) FDG)
    (h : trStC n Binv W cfg rb rm eps = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val (nodeMat (α := α) rb.Lb rm.C)
      (fun θ => FG θ * FDG θ) :=
  trStage_encloses hW lay nrm (fun i => i.isLt) (fun j => j.isLt) nrm.hC
    (hB.mul lay.cbb lay.wb lay.wb (Equiv.refl (Fin n)) (fun _ => rfl) hDG) h

/-- `D(G⁻¹) = -(C G⁻¹)`. -/
theorem trDGi_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hC : PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val (nodeMat (α := α) rb.Lb rm.C) FC)
    (hB : PMat.Encloses rb.Lb rb.bB rb.P n W.rho Fin.val Fin.val (ptB Binv W cfg rb.toT eps) FG)
    (h : trStDGi n Binv W cfg rb rm eps = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val (trDGi (α := α) rb rm)
      (fun θ => -(FC θ * FG θ)) :=
  (trStage_encloses hW lay nrm (fun i => i.isLt) (fun j => j.isLt) nrm.hDGi
    (hC.mul lay.cbb lay.wb lay.wb (Equiv.refl (Fin n)) (fun _ => rfl) hB) h).neg

/-- `DN = Ω₀ (D L G⁻¹ + L D(G⁻¹))`. -/
theorem trDN_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hK : PMat.Encloses rb.Lb rb.bK rb.P n W.rho phaseNat Fin.val (ptK (α := α) W rb.toT mm) FL)
    (hB : PMat.Encloses rb.Lb rb.bB rb.P n W.rho Fin.val Fin.val (ptB Binv W cfg rb.toT eps) FG)
    (hDL : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val
      (nodeMat (α := α) rb.Lb rm.DL) FDL)
    {FDGi : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    (hDGi : PMat.Encloses rb.Lb rb.bR rb.P n W.rho Fin.val Fin.val (trDGi (α := α) rb rm) FDGi)
    (h : trStDN n Binv W cfg rb mm rm eps = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trDN (α := α) n rb rm)
      (fun θ => omegaZeroMatrix n * (FDL θ * FG θ + FL θ * FDGi θ)) :=
  (trStage_encloses hW lay nrm phaseNat_lt_add (fun j => j.isLt) nrm.hDN
    ((hDL.mul lay.cbb lay.wb lay.wb (Equiv.refl (Fin n)) (fun _ => rfl) hB).add
      (hK.mul lay.cbb lay.wb lay.wb (Equiv.refl (Fin n)) (fun _ => rfl) hDGi)) h).omega

/-- `X_N = A N - DN`. -/
theorem trXNm_encloses (hW : checkWeight W sw Nw = true) (lay : TRLay n rb)
    (nrm : TRNorm n W box s rb)
    (hA : PMat.Encloses rb.Lb rb.bA rb.P n W.rho phaseNat phaseNat (ptA (α := α) n W rb.toT tm) FA)
    (hN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trN (α := α) n rb rm) FN)
    (hDN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trDN (α := α) n rb rm) FDN)
    (h : trStXN (α := α) n W rb tm rm = true) :
    PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (nodeMat (α := α) rb.Lb rm.XN)
      (fun θ => FA θ * FN θ + -FDN θ) := by
  have h1 := hA.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN
  have h2 := (hDN.neg.shift lay.cbu lay.wb lay.wu (pow_unit_rep lay.wu lay.su rb.P)).cast lay.eu
    rfl rfl
  exact trStage_encloses hW lay nrm phaseNat_lt_add (fun j => j.isLt) nrm.hXN (h1.add h2) h

/-- `T = Nᵀ (Ω₀ X_N)` on the window. -/
theorem trT_encloses (lay : TRLay n rb)
    (hN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trN (α := α) n rb rm) FN)
    (hXN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val
      (nodeMat (α := α) rb.Lb rm.XN) FXN) :
    PMat.Encloses rb.Lw (rb.aT n) (2 * rb.P) n W.rho Fin.val Fin.val (trT (α := α) n rb rm)
      (fun θ => (FN θ)ᵀ * (omegaZeroMatrix n * FXN θ)) :=
  (hN.tr.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm
    hXN.omega).cast rfl rfl (two_mul rb.P).symm

/-- `Y = DH N` on the window. -/
theorem trY_encloses (lay : TRLay n rb) {FD1 : (Fin n → ℂ) → Matrix Unit (Fin n ⊕ Fin n) ℂ}
    (hD1 : PMat.Encloses rb.Lb rb.bA rb.P n W.rho (fun _ : Unit => 0) phaseNat
      (ptD1 (α := α) W rb.toT tm) FD1)
    (hN : PMat.Encloses rb.Lb rb.bR rb.P n W.rho phaseNat Fin.val (trN (α := α) n rb rm) FN) :
    PMat.Encloses rb.Lw (rb.aY n) (2 * rb.P) n W.rho (fun _ : Unit => 0) Fin.val
      (trY (α := α) n W rb tm rm) (fun θ => FD1 θ * FN θ) :=
  (hD1.mul lay.cbb lay.wb lay.wb finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN).cast rfl rfl
    (two_mul rb.P).symm

end Chain

end KAM.CertificateSharp.Packed
