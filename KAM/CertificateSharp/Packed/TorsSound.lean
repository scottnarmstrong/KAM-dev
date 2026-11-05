/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsChain
public import KAM.Certificate.Sound.Torsion

/-!
# The packed torsion stage: soundness

* `ptAvg_entry`: every entry of the average of the frozen bordered torsion is within `ptRad` of
  the exact centre `ptCentre` (the zero-key slot of the packed `T` and `Y`, the box centre of the
  frequency column, `0` in the corner);
* `ptDef_eq`: the entries of `I - S C` are exactly `ptDef`;
* `torsPacked_sound`: a passing core with passing boundary entries gives the conclusion of the
  landed `torsionAvgCheck_sound` for the frozen `extendedTorsionAverage`;
* `checkTorsionPacked_sound`: **the conclusion of the landed `checkTorsion_sound_of`**, under its
  hypotheses.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

/-- A complex rational. -/
def qC (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)

theorem norm_qC_le (z : ℚ × ℚ) : ‖qC z‖ ≤ (qAbs1 z : ℝ) := by
  unfold qC qAbs1
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  push_cast
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

theorem torusAverage_const_c {n : ℕ} (c : ℂ) : torusAverage (fun _ : Fin n → ℝ => c) = c := by
  rw [torusAverage, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    volume_unitCube, ENNReal.toReal_one, one_smul]

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

omit [LawfulCertArith α] in
theorem ptEntries_spec {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {tb : PTorsBook} {tm : PTorsMemo} {ms : List (CertModel α)}
    (h : ptEntries n K W cfg pe tb tm ms = true) :
    (∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe tb tm r j l = true) ∧
      (∀ a < n + n, ∀ b < n + n, ptAOk n W cfg pe tb tm ms a b = true) ∧
      ∀ a < n + n, ptD1Ok n W cfg pe tb tm ms a = true := by
  simp only [ptEntries, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

omit [LawfulCertArith α] in
theorem pgEntries_of_check {K : CertEmbedding α} {Binv : List (List (CertPoly α))}
    {W : CertWeight} {cfg : ModelConfig α} {pe : PiEnclosure α} {bk : PGramBook}
    {mm : PGramMemo} {σ : ℚ} {δβ : α × α}
    (h : gramPackedCheck n K Binv W cfg pe bk mm σ = some δβ) :
    pgEntries n K W cfg pe bk mm = true := by
  unfold gramPackedCheck at h
  split_ifs at h with he
  exact he

/-- A decoded witness entry is the complex rational `ptSq`. -/
theorem ccEntry_toC_eq {cfg : ModelConfig α} {tb : PTorsBook} {S : List (List (CC α))}
    (hS : ptSOk n cfg tb S = true) {i l : ℕ} (hi : i < n + 1) (hl : l < n + 1) :
    (ccEntry S i l).toC = qC (ptSq cfg tb S i l) := by
  simp only [ptSOk, List.all_eq_true, List.mem_range] at hS
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hS i hi l hl)
  rw [certMantPair_sound hz]
  unfold ptSq qC
  rw [hz]
  push_cast
  ring

omit [LawfulCertArith α] in
/-- The entries of `I - S C` are exactly `ptDef`. -/
theorem ptDef_eq {Binv : List (List (CertPoly α))} {W : CertWeight} {cfg : ModelConfig α}
    {box : FreqBox} {s : ℚ} {tb : PTorsBook} {mm : PGramMemo} {tm : PTorsMemo} {eps : α}
    (S : List (List (CC α))) (i j : ℕ) :
    qC (ptDef n Binv W cfg box s tb mm tm eps S i j) =
      (if i = j then (1 : ℂ) else 0) - ∑ l ∈ Finset.range (n + 1),
        qC (ptSq cfg tb S i l) * qC (ptCentre n Binv W cfg box s tb mm tm eps l j) := by
  have hI : ∀ x y u v : ℂ, (x + Complex.I * y) * (u + Complex.I * v) =
      (x * u - y * v) + Complex.I * (x * v + y * u) := by
    intro x y u v
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold ptDef qC
  simp only [hI, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  split_ifs <;> push_cast <;> ring

/-- **The averaged torsion bound from a passing core**: the conclusion of the landed
`torsionAvgCheck_sound` at the frozen bordered torsion. -/
theorem torsPacked_sound (hn : 1 ≤ n) {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) {tb : PTorsBook} {tm : PTorsMemo} (hP : tb.P = bk.P)
    (hent : ptEntries n K W cfg pe tb tm ms = true) (box : FreqBox) (s : ℚ)
    (S : List (List (CC α))) (σTμ : ℚ)
    (hcore : torsPackedCore n Binv W cfg box s tb mm tm eps S σTμ = true) {ω : Fin n → ℝ}
    (hω : FreqEncloses n box ω) :
    IsUnit (KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω))⁻¹ i j‖ ≤
        σTμ := by
  -- the Gram facts
  obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  have hρ : (0 : ℝ) < W.rho := CertWeight.rho_pos hW
  -- the guards and the boundary
  simp only [torsPackedCore, Bool.and_eq_true] at hcore
  obtain ⟨⟨⟨hlay, hnrm⟩, hpk⟩, hfin⟩ := hcore
  have lay := ptLayOk_spec hlay
  have nrm := ptNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  obtain ⟨eD2, eA, eD1⟩ := ptEntries_spec hent
  -- the base packed models
  have hK := ptK_encloses hW hpe K (pgEntries_of_check hG) hP lay.w1 pk.pK nrm.nK
  have hB := ptB_encloses (eps := eps) hW lay.wB pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2 := ptD2_encloses hW hpe K lay.w1 eD2 pk.pD nrm.nD
  have hF := fun l : Fin n => ptF_encloses (α := α) lay.wU0 lay.sU0 (s := s) hω l
    (nrm.fF l.val l.isLt) W.rho
  have hDL := ptDL_encloses hW K lay hD2 hF nrm.nDL
  have hA := ptA_encloses hW hpe hD hnv hKD hms lay.wA eA pk.pA nrm.nA
  have hD1 := ptD1_encloses hW hpe hD hnv hKD hms lay.wA eD1 pk.pD1 nrm.nA
  -- the chain
  have hN := ptN_encloses hW lay nrm hK hB
  have hDG := ptDG_encloses hW lay nrm hK hDL
  have hC := ptC_encloses hW lay nrm hB hDG
  have hDGi := ptDGi_encloses hW lay nrm hC hB
  have hDN := ptDN_encloses lay hK hB hDL hDGi
  have hXN := ptXN_encloses hW lay nrm hA hN hDN
  have hT := ptT_encloses lay hN hXN
  have hY := ptY_encloses lay hD1 hN
  -- the entries of the average
  set A := KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)
  set ι := torsionIdx n
  set Cm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y =>
    qC (ptCentre n Binv W cfg box s tb mm tm eps (ι x) (ι y))
  have hH : DifferentiableOn ℂ e.eval D := (e.contDiffOn_eval hD hnv).differentiableOn (by simp)
  have hcont := fun a b => continuousOn_extendedTorsion (ω := (s : ℝ) • ω) hD hH
    (K.differentiable_eval n) hKD hGu a b
  have hdig : ∀ (L : PackLayout) (e' : ℕ) (x : PC),
      qC (ptDigit n L e' x) = ((slotAt L.width (zslot n L) x.re : ℂ) +
        Complex.I * (slotAt L.width (zslot n L) x.im : ℂ)) / 2 ^ e' := by
    intro L e' x
    unfold qC ptDigit
    push_cast
    ring
  have hent' : ∀ x y,
      ‖A x y - Cm x y‖ ≤ val (ptRad n Binv W cfg box s tb mm tm eps (ι x) (ι y)) := by
    intro x y
    have hA' : A x y = torusAverage (fun v : Fin n → ℝ =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) (fun i => (v i : ℂ)) x y) := rfl
    rw [hA']
    rcases x with i | _ <;> rcases y with j | _
    · -- the torsion block
      have hTij := (hT i j).congr (g := fun θ =>
          KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j))
        fun θ hθ => by
          show _ = torsion e.eval (K.eval n) ((s : ℝ) • ω) θ i j
          rw [torsion_eq_models (K.differentiable_eval n) hGu _ hθ]
      have := PEnc.average lay.wT lay.dimsT lay.sT nrm.fT hρ (hcont _ _) hTij
      simp only [Cm, ι, torsionIdx, Sum.elim_inl, ptCentre, ptRad, i.isLt, j.isLt, ↓reduceIte,
        hdig]
      exact this
    · -- the frequency column
      simp only [Cm, ι, torsionIdx, Sum.elim_inl, Sum.elim_inr, ptCentre, ptRad, i.isLt,
        lt_irrefl, ↓reduceIte]
      show ‖torusAverage (fun _ : Fin n → ℝ => ((((s : ℝ) • ω) i : ℝ) : ℂ)) - _‖ ≤ _
      rw [torusAverage_const_c]
      refine le_trans ?_ (LawfulCertArith.ofRatUp_ge _)
      have hb : |ω i - ((box.getD i.val (0, 0)).1 : ℝ)| ≤ ((box.getD i.val (0, 0)).2 : ℝ) := hω i
      unfold qC
      have e1 : ((((s : ℝ) • ω) i : ℝ) : ℂ) - (((s * (box.getD i.val (0, 0)).1 : ℚ) : ℂ) +
          Complex.I * ((0 : ℚ) : ℂ)) =
          (((s : ℝ) * (ω i - ((box.getD i.val (0, 0)).1 : ℝ)) : ℝ) : ℂ) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      push_cast
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    · -- the last row
      have hYj := (hY () j).congr (g := fun θ =>
          KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inr ()) (Sum.inl j))
        fun θ _ => by
          show _ = fderiv ℂ e.eval (K.eval n θ) (normalFrame (K.eval n) θ j)
          rw [fderiv_apply_normalFrame]
          beta_reduce
          rw [Matrix.mul_apply]
          simp only [normalMat, Matrix.mul_assoc, Matrix.of_apply]
      have := PEnc.average lay.wAN lay.dimsAN lay.sAN nrm.fY hρ (hcont _ _) hYj
      simp only [Cm, ι, torsionIdx, Sum.elim_inl, Sum.elim_inr, ptCentre, ptRad, j.isLt,
        lt_irrefl, ↓reduceIte, hdig]
      exact this
    · -- the corner
      simp only [Cm, ι, torsionIdx, Sum.elim_inr, ptCentre, ptRad, lt_irrefl, ↓reduceIte]
      show ‖torusAverage (fun _ : Fin n → ℝ => (0 : ℂ)) - _‖ ≤ _
      rw [torusAverage_const_c, LawfulCertArith.val_ofInt]
      simp [qC]
  -- the final test
  simp only [ptFinal, Bool.and_eq_true] at hfin
  obtain ⟨⟨-, hSok⟩, hb⟩ := hfin
  obtain ⟨hd, hr, hr0, hbr, hδ1, hδ0, hfin⟩ := avgBoundsOk_spec hb
  set a := maxCandidate (ptDRows n Binv W cfg box s tb mm tm eps S)
  set b := maxCandidate (avgInvRows n S)
  set r := maxCandidate (ptRRows n Binv W cfg box s tb mm tm eps)
  let Sm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y => (ccEntry S (ι x) (ι y)).toC
  have hrow : ∀ x : Fin n ⊕ Unit, ∃ i : Fin (n + 1), i.val = ι x :=
    fun x => ⟨⟨ι x, torsionIdx_lt n x⟩, rfl⟩
  -- the radius matrix
  have hR : ‖A - Cm‖ ≤ val r := by
    rw [norm_le_iff_forall_rowSum hr0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (ptRad n Binv W cfg box s tb mm tm eps (ι x) j))]
    exact Finset.sum_le_sum fun y _ => by rw [Matrix.sub_apply]; exact hent' x y
  -- the witness
  have hb0 : 0 ≤ val b := by
    refine le_trans ?_ (hbr _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    exact sumUp_nonneg (fun _ => CC.normUp_nonneg _) _
  have hS : ‖Sm‖ ≤ val b := by
    rw [norm_le_iff_forall_rowSum hb0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hbr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (ccEntry S (ι x) j).normUp)]
    exact Finset.sum_le_sum fun y _ => CC.norm_le_normUp _
  -- the centre defect, exact
  have hSm : ∀ x l, Sm x l = qC (ptSq cfg tb S (ι x) (ι l)) := fun x l =>
    ccEntry_toC_eq hSok (torsionIdx_lt n x) (torsionIdx_lt n l)
  have ha0 : 0 ≤ val a := by
    refine le_trans ?_ (hd _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    refine le_trans ?_ (LawfulCertArith.ofRatUp_ge _)
    push_cast
    exact Finset.sum_nonneg fun j _ => by unfold qAbs1; positivity
  have hDf : ‖1 - Sm * Cm‖ ≤ val a := by
    rw [norm_le_iff_forall_rowSum ha0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hd _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((LawfulCertArith.ofRatUp_ge _).trans hrw)
    rw [hi]
    push_cast
    rw [Finset.sum_range (fun j =>
      ((qAbs1 (ptDef n Binv W cfg box s tb mm tm eps S (ι x) j) : ℚ) : ℝ)), ← sum_torsionIdx n
      (fun j => ((qAbs1 (ptDef n Binv W cfg box s tb mm tm eps S (ι x) j) : ℚ) : ℝ))]
    refine Finset.sum_le_sum fun y _ => ?_
    have he : (1 - Sm * Cm) x y = qC (ptDef n Binv W cfg box s tb mm tm eps S (ι x) (ι y)) := by
      rw [ptDef_eq, Finset.sum_range (fun l => qC (ptSq cfg tb S (ι x) l) *
          qC (ptCentre n Binv W cfg box s tb mm tm eps l (ι y))),
        ← sum_torsionIdx n (fun l => qC (ptSq cfg tb S (ι x) l) *
          qC (ptCentre n Binv W cfg box s tb mm tm eps l (ι y))),
        Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
      congr 1
      · by_cases hxy : x = y
        · simp [hxy]
        · have hne : ι x ≠ ι y := (torsionIdx_injective n).ne hxy
          simp [hxy, hne]
      · exact Finset.sum_congr rfl fun l _ => by rw [hSm]
    rw [he]
    exact norm_qC_le _
  -- the defect of `S` against the average
  have hE : ‖1 - Sm * A‖ ≤ val (upAdd a (upMul b r)) := by
    have e1 : 1 - Sm * A = (1 - Sm * Cm) + Sm * (Cm - A) := by
      rw [Matrix.mul_sub]
      abel
    have hm := LawfulCertArith.upMul_ge b r hb0 hr0
    have hu := LawfulCertArith.upAdd_ge a (upMul b r)
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖Sm * (Cm - A)‖ ≤ val b * val r := by
      refine (Matrix.linfty_opNorm_mul _ _).trans ?_
      rw [norm_sub_rev]
      exact mul_le_mul hS hR (norm_nonneg _) hb0
    linarith
  obtain ⟨hU, hInv, -⟩ := matrix_inv_of_approx_inverse hE hδ1 hS
  refine ⟨hU, fun i => (rowSum_le_norm _ i).trans (hInv.trans ?_)⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith


/-- **Soundness of the packed torsion sub-check**: the conclusion of the landed
`checkTorsion_sound_of`, under its hypotheses (the conclusions of the Hamiltonian-bounds and
embedding contracts). -/
theorem checkTorsionPacked_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {tb : PTorsBook} {tm : PTorsMemo}
    (h : checkTorsionPacked bk mm tb tm c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  unfold checkTorsionPacked at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps ms heps hcomp
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hP, hent⟩, hcore⟩ := h
      have hms : SlotsEnclose n c.ham c.emb c.weight.rho ms := by
        have := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgLow S.hpe _ hcomp
        exact ⟨this.1, this.2⟩
      have := torsPacked_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD c.gramInv c.cfgLow
        S.hpe hG heps hms hP hent c.freqBox c.params.s c.torsInv _ hcore hω
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [LawfulCertArith α] in
/-- The packed torsion check from its parts (for proofs split across declarations): the packed
Gram check, the landed composition, the boundary entries and the core. -/
theorem checkTorsionPacked_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {tb : PTorsBook} {tm : PTorsMemo} {δβ : α × α} {eps : α} {ms : List (CertModel α)}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hcomp : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some ms) (hP : tb.P = bk.P)
    (hent : ptEntries n c.emb c.weight c.cfgLow c.piEnc tb tm ms = true)
    (hcore : torsPackedCore n c.gramInv c.weight c.cfgLow c.freqBox c.params.s tb mm tm eps
      c.torsInv (c.params.σT - c.params.μ) = true) :
    checkTorsionPacked bk mm tb tm c = true := by
  unfold checkTorsionPacked
  rw [hG]
  dsimp only
  rw [heps, hcomp]
  dsimp only
  rw [hP, hent, hcore]
  simp

end Sound

end KAM.CertificateSharp.Packed
