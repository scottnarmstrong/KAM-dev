/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.GramBase
public import KAM.CertificateSharp.Packed.JetLeaf

/-!
# The packed Gram stage on a truncated `DK` memo

The landed boundary check `pgEntryOk` requires the memo to be the **exact** mantissas of the landed
`DK` model. So the memo's layout `L1`, and with it every product window of the Gram and torsion
stages, must hold the embedding's whole Fourier support. A certificate truncated at a tiny size
(MAG: 10⁻²⁶, a box of 223 × 131 keys) then forces windows of 10⁵ slots.

Here the memo is checked against the landed model **truncated to the box of `L1`**: the landed
`jBoxTrunc` (`JetLeaf.lean`) drops the terms without a slot on `L1` into the radius, at their
weighted sup bound (`CertPoly.supNormUp`), and `jBoxTrunc_encloses` keeps the enclosure. The radius
of every memo entry therefore covers the dropped tail, and the packed core runs on a small box.

* `dkModelT`, `pgEntryOkT`, `pgEntriesT`: the truncated boundary;
* `gramPackedCheckT`: the truncated boundary, then the landed core `gramPackedCore` (unchanged);
* `pgDnT_bound`, `gramPackedCheckT_sound`: the landed `pgDn_bound` and `gramPackedCheck_sound` with
  the truncated models; the same conclusion;
* `checkGramPackedT`, `checkGramPackedT_sound`: the base checker's Gram sub-check, with the inverse
  witness `Bw` an argument (a witness truncated to the same box; the conclusion does not mention
  it).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix.Norms.Operator

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
  (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (bk : PGramBook)

/-- The landed `DK` model `(r, a)` truncated to the box of `L` (the dropped terms in the radius). -/
def dkModelT (L : PackLayout) (r a : ℕ) : CertModel α := jBoxTrunc W L (dkModel n K W pe r a)

/-- **One truncated boundary entry**: the truncated `DK` model `(r, a)` has degree `0`, its
mantissas are the memo's, and its radius is below the memo's bound. -/
def pgEntryOkT (mm : PGramMemo) (r a : ℕ) : Bool :=
  (dkModelT n K W pe bk.L1 r a).deg == 0 &&
    decide ((dkModelT n K W pe bk.L1 r a).poly.toMants cfg.toMant bk.P =
      some (mm.reAt r a, mm.imAt r a)) &&
    ble (dkModelT n K W pe bk.L1 r a).rad (ofRatUp (mm.radAt r a))

/-- Every truncated boundary entry. -/
def pgEntriesT (mm : PGramMemo) : Bool :=
  (List.range (2 * n)).all fun r => (List.range n).all fun a => pgEntryOkT n K W cfg pe bk mm r a

/-- **The packed Gram check on a truncated memo**: the truncated boundary, then the landed core. -/
def gramPackedCheckT (mm : PGramMemo) (σBμ : ℚ) : Option (α × α) :=
  if pgEntriesT n K W cfg pe bk mm then gramPackedCore n Binv W cfg bk mm σBμ else none

theorem pgEntriesT_of {mm : PGramMemo}
    (h : ∀ r < 2 * n, ∀ a < n, pgEntryOkT n K W cfg pe bk mm r a = true) :
    pgEntriesT n K W cfg pe bk mm = true := by
  simp only [pgEntriesT, List.all_eq_true, List.mem_range]
  exact h

/-- The check from its truncated boundary and its core. -/
theorem gramPackedCheckT_eq_core {mm : PGramMemo} (h : pgEntriesT n K W cfg pe bk mm = true)
    (σBμ : ℚ) :
    gramPackedCheckT n K Binv W cfg pe bk mm σBμ = gramPackedCore n Binv W cfg bk mm σBμ := by
  simp [gramPackedCheckT, h]

end Defs

/-! ### Soundness -/

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

/-- The truncated `DK` model encloses the `DK` entry (`jBoxTrunc_encloses`). -/
theorem dkModelT_encloses {n : ℕ} (K : CertEmbedding α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (L : PackLayout) {r : ℕ} (hr : r < 2 * n) (a : Fin n) :
    (dkModelT n K W pe L r a.val).Encloses n W.rho (dkFun n K r a) :=
  jBoxTrunc_encloses hW L (dkModel_encloses K hW hpe hr a)

omit [LawfulCertArith α] in
theorem pgEntriesT_spec {n : ℕ} {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {bk : PGramBook} {mm : PGramMemo}
    (h : pgEntriesT n K W cfg pe bk mm = true) {r a : ℕ} (hr : r < 2 * n) (ha : a < n) :
    (dkModelT n K W pe bk.L1 r a).deg = 0 ∧
      (dkModelT n K W pe bk.L1 r a).poly.toMants cfg.toMant bk.P =
        some (mm.reAt r a, mm.imAt r a) ∧
      ble (dkModelT n K W pe bk.L1 r a).rad (ofRatUp (mm.radAt r a)) = true := by
  simp only [pgEntriesT, List.all_eq_true, List.mem_range] at h
  have := h r hr a ha
  simp only [pgEntryOkT, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

omit [LawfulCertArith α] in
theorem pgEntriesT_of_check {n : ℕ} {K : CertEmbedding α} {Binv : List (List (CertPoly α))}
    {W : CertWeight} {cfg : ModelConfig α} {pe : PiEnclosure α} {bk : PGramBook}
    {mm : PGramMemo} {σ : ℚ} {δβ : α × α}
    (h : gramPackedCheckT n K Binv W cfg pe bk mm σ = some δβ) :
    pgEntriesT n K W cfg pe bk mm = true := by
  unfold gramPackedCheckT at h
  split_ifs at h with he
  exact he

/-- **The defect entry bound** of the packed Gram check on a truncated memo (`pgDn_bound` with
the truncated `DK` models). -/
theorem pgDnT_bound {n : ℕ} (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo}
    (he : pgEntriesT n K W cfg pe bk mm = true) (hg : pgGuard n Binv W cfg bk mm = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) (i j : Fin n) :
    ‖(1 - polyMatrix n Binv θ * gramMatrix (K.eval n) θ) i j‖ ≤
      val (pgDn n Binv W cfg bk mm i.val j.val) := by
  obtain ⟨hw1, hwB, hc11, hcB2, hnK, hnB, hnD, hp0, hK, hB⟩ := pgGuard_spec hg
  have hw2 : layoutWf bk.L2 = true := win_wf hc11 hw1 hw1
  have hρ : (0 : ℝ) < W.rho := CertWeight.rho_pos hW
  set Pp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun r a θ => (dkModelT n K W pe bk.L1 r a).poly.eval n θ
  set Bp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun i k θ => (gramInvPoly Binv i k).eval n θ
  set Gp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun k j θ =>
    ∑ r ∈ Finset.range (2 * n), Pp r k θ * Pp r j θ
  -- representations
  have hKr : ∀ r < 2 * n, ∀ a < n, PCRep bk.L1 bk.bK (pgK bk mm r a) n
      (fun θ => Pp r a θ * 2 ^ bk.P) := fun r hr a ha =>
    PCRep.ofMants (pgEntriesT_spec he hr ha).2.1 hw1 (hK r hr a ha).1 (hK r hr a ha).2
  have hBr : ∀ i < n, ∀ k < n, PCRep bk.LB bk.bB (pgB Binv cfg bk i k) n
      (fun θ => Bp i k θ * 2 ^ bk.P) := fun i hi k hk => PCRep.ofPoly hwB (hB i hi k hk) n
  have hGr : ∀ k < n, ∀ j < n, PCRep bk.L2 (bk.bG n) (pgG n bk mm k j) n
      (fun θ => Gp k j θ * 2 ^ (2 * bk.P)) := by
    intro k hk j hj
    have := PCRep.sumN (L := bk.L2) (A := fun _ => mulLoad bk.L1 bk.L1 bk.bK bk.bK)
      (f := fun r => pcMul (pgK bk mm r k) (pgK bk mm r j))
      (F := fun r θ => Pp r k θ * 2 ^ bk.P * (Pp r j θ * 2 ^ bk.P)) (2 * n)
      (fun r hr => PCRep.mul hc11 hw1 hw1 (hKr r hr k hk) (hKr r hr j hj))
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at this
    refine this.congr fun θ => ?_
    simp only [Gp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hEr : ∀ i < n, ∀ j < n, PCRep bk.L3 (bk.bE n) (pgE n Binv cfg bk mm i j) n
      (fun θ => (∑ k ∈ Finset.range n, Bp i k θ * Gp k j θ) * 2 ^ (3 * bk.P)) := by
    intro i hi j hj
    have := PCRep.sumN (L := bk.L3) (A := fun _ => mulLoad bk.LB bk.L2 bk.bB (bk.bG n))
      (f := fun k => pcMul (pgB Binv cfg bk i k) (pgG n bk mm k j))
      (F := fun k θ => Bp i k θ * 2 ^ bk.P * (Gp k j θ * 2 ^ (2 * bk.P))) n
      (fun k hk => PCRep.mul hcB2 hwB hw2 (hBr i hi k hk) (hGr k hk j hj))
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at this
    refine this.congr fun θ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨p0, hp0'⟩ := Option.isSome_iff_exists.mp hp0
  have hw3 : layoutWf bk.L3 = true := by
    simp only [normOk, Bool.and_eq_true] at hnD
    exact hnD.1.1.1.1.1.1.1.1
  have hDr : PCRep bk.L3 (bk.bD n) (pgD n Binv cfg bk mm i.val j.val) n
      (fun θ => ((if i.val = j.val then (1 : ℂ) else 0) -
        ∑ k ∈ Finset.range n, Bp i.val k θ * Gp k j.val θ) * 2 ^ (3 * bk.P)) := by
    have hu := PCRep.unitSub hw3 hp0' (if i.val = j.val then 2 ^ (3 * bk.P) else 0)
      (hEr i.val i.isLt j.val j.isLt)
    have hpg : pgP0 n bk = p0 := by simp [pgP0, hp0']
    unfold pgD
    rw [hpg]
    refine (hu.mono ?_).congr fun θ => ?_
    · unfold PGramBook.bD
      split_ifs <;> simp
    · split_ifs <;> push_cast <;> ring
  -- the three sup bounds
  have hPn : ∀ r < 2 * n, ∀ a < n, ‖Pp r a θ‖ ≤ val (pgKn W bk mm r a : α) :=
    fun r hr a ha => norm_le_ofRatUp (hKr r hr a ha) hnK hW hθ bk.P rfl
  have hBn : ∀ i < n, ∀ k < n, ‖Bp i k θ‖ ≤ val (pgBn Binv W cfg bk i k) :=
    fun i hi k hk => norm_le_ofRatUp (hBr i hi k hk) hnB hW hθ bk.P rfl
  have hDn : ‖(if i.val = j.val then (1 : ℂ) else 0) -
      ∑ k ∈ Finset.range n, Bp i.val k θ * Gp k j.val θ‖ ≤
      val (ofRatUp ((pcNorm W bk.q bk.lD bk.L3 (pgD n Binv cfg bk mm i.val j.val) : ℚ) /
        2 ^ (3 * bk.P + 2 * bk.q)) : α) :=
    norm_le_ofRatUp hDr hnD hW hθ (3 * bk.P) rfl
  -- the entries' enclosures
  have hEnc : ∀ r < 2 * n, ∀ a : Fin n,
      ‖dkFun n K r a θ - Pp r a.val θ‖ ≤ val (pgKr (α := α) mm r a.val) ∧
        0 ≤ val (pgKr (α := α) mm r a.val) := by
    intro r hr a
    obtain ⟨hd, -, hrad⟩ := pgEntriesT_spec he hr a.isLt
    have ek := dkModelT_encloses K hW hpe bk.L1 hr a
    have h1 := encloses_deg0 ek hd hθ
    have h2 := LawfulCertArith.ble_sound _ _ hrad
    exact ⟨h1.trans h2, (ek.rad_nonneg hρ).trans h2⟩
  -- the radius of `G`
  have hGerr : ∀ k : Fin n, ‖Gp k.val j.val θ - gramMatrix (K.eval n) θ k j‖ ≤
      val (pgGr (α := α) n W bk mm k.val j.val) := by
    intro k
    rw [gramMatrix_eq_dkFun, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    unfold pgGr
    refine le_trans ?_ (sumUp_ge _ _)
    rw [list_sum_map_range_eq]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr' := Finset.mem_range.mp hr
    obtain ⟨bk1, rk0⟩ := hEnc r hr' k
    obtain ⟨bj1, rj0⟩ := hEnc r hr' j
    have nk := hPn r hr' k.val k.isLt
    have nj := hPn r hr' j.val j.isLt
    have nk0 : 0 ≤ val (pgKn W bk mm r k.val : α) := (norm_nonneg _).trans nk
    have nj0 : 0 ≤ val (pgKn W bk mm r j.val : α) := (norm_nonneg _).trans nj
    have m1 := LawfulCertArith.upMul_ge _ _ nk0 rj0
    have m2 := LawfulCertArith.upMul_ge _ _ nj0 rk0
    have m3 := LawfulCertArith.upMul_ge _ _ rk0 rj0
    have a1 := LawfulCertArith.upAdd_ge (upMul (pgKn W bk mm r k.val : α)
      (pgKr (α := α) mm r j.val)) (upMul (pgKn W bk mm r j.val : α) (pgKr (α := α) mm r k.val))
    have a2 := LawfulCertArith.upAdd_ge (upAdd (upMul (pgKn W bk mm r k.val : α)
      (pgKr (α := α) mm r j.val)) (upMul (pgKn W bk mm r j.val : α) (pgKr (α := α) mm r k.val)))
      (upMul (pgKr (α := α) mm r k.val) (pgKr (α := α) mm r j.val))
    set fk := dkFun n K r k θ
    set fj := dkFun n K r j θ
    set pk := Pp r k.val θ
    set pj := Pp r j.val θ
    have hid : pk * pj - fk * fj = pk * (pj - fj) + (pk - fk) * (pj - (pj - fj)) := by ring
    have e1 : ‖pk - fk‖ ≤ val (pgKr (α := α) mm r k.val) := by rw [norm_sub_rev]; exact bk1
    have e2 : ‖pj - fj‖ ≤ val (pgKr (α := α) mm r j.val) := by rw [norm_sub_rev]; exact bj1
    calc ‖pk * pj - fk * fj‖ ≤ ‖pk‖ * ‖pj - fj‖ + ‖pk - fk‖ * (‖pj‖ + ‖pj - fj‖) := by
          rw [hid]
          refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ?_)
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _)
            (norm_nonneg _))
      _ ≤ val (pgKn W bk mm r k.val : α) * val (pgKr (α := α) mm r j.val) +
          val (pgKr (α := α) mm r k.val) * (val (pgKn W bk mm r j.val : α) +
            val (pgKr (α := α) mm r j.val)) := by
          gcongr
      _ ≤ _ := by nlinarith
  -- the entry
  have hentry : (1 - polyMatrix n Binv θ * gramMatrix (K.eval n) θ) i j =
      ((if i.val = j.val then (1 : ℂ) else 0) - ∑ k ∈ Finset.range n, Bp i.val k θ * Gp k j.val θ) +
        ∑ k : Fin n, Bp i.val k.val θ * (Gp k.val j.val θ - gramMatrix (K.eval n) θ k j) := by
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
    simp only [polyMatrix_apply, Bp, mul_sub, Finset.sum_sub_distrib]
    rw [← Fin.sum_univ_eq_sum_range (fun k => (gramInvPoly Binv i.val k).eval n θ * Gp k j.val θ)]
    simp only [Fin.ext_iff]
    ring
  rw [hentry]
  unfold pgDn
  refine (norm_add_le _ _).trans (le_trans ?_ (LawfulCertArith.upAdd_ge _ _))
  refine add_le_add hDn ?_
  refine (norm_sum_le _ _).trans (le_trans ?_ (sumUp_ge _ _))
  rw [list_sum_map_range_eq, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul]
  have hb := hBn i.val i.isLt k.val k.isLt
  have hgk := hGerr k
  have hb0 : 0 ≤ val (pgBn Binv W cfg bk i.val k.val) := (norm_nonneg _).trans hb
  have hg0 : 0 ≤ val (pgGr (α := α) n W bk mm k.val j.val) := (norm_nonneg _).trans hgk
  exact (mul_le_mul hb hgk (norm_nonneg _) hb0).trans (LawfulCertArith.upMul_ge _ _ hb0 hg0)

/-- **Packed Gram check on a truncated memo**: the conclusion of the landed `gramCheck_sound`
(`gramPackedCheck_sound`, with `pgDnT_bound`). -/
theorem gramPackedCheckT_sound {n : ℕ} (hn : 1 ≤ n) (K : CertEmbedding α)
    (Binv : List (List (CertPoly α))) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (bk : PGramBook) (mm : PGramMemo) (σBμ : ℚ) {δβ : α × α}
    (h : gramPackedCheckT n K Binv W cfg pe bk mm σBμ = some δβ) :
    val δβ.1 < 1 ∧ ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det ∧
      (∀ i, ∑ j, ‖(gramMatrix (K.eval n) θ)⁻¹ i j‖ ≤ σBμ) ∧
      ‖(gramMatrix (K.eval n) θ)⁻¹ - polyMatrix n Binv θ‖ ≤
        val δβ.1 * val δβ.2 / (1 - val δβ.1) := by
  unfold gramPackedCheckT at h
  split_ifs at h with he
  unfold gramPackedCore at h
  split_ifs at h with hsh hok
  obtain rfl := (Option.some.inj h).symm
  simp only [Bool.and_eq_true] at hsh
  obtain ⟨-, hg⟩ := hsh
  obtain ⟨hd, hb, hδ1, hδ0, hfin⟩ := gramBoundsOk_spec hok
  set δ := maxCandidate (pgDRows n Binv W cfg bk mm)
  set β := maxCandidate (pgBRows n Binv W cfg bk)
  refine ⟨hδ1, fun θ hθ => ?_⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hE : ‖1 - polyMatrix n Binv θ * gramMatrix (K.eval n) θ‖ ≤ val δ := by
    rw [norm_le_iff_forall_rowSum hδ0]
    intro i
    have hrow := hd _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrow)
    rw [Fin.sum_univ_def]
    exact List.sum_le_sum fun j _ => pgDnT_bound K Binv hW cfg hpe he hg hθ i j
  obtain ⟨-, hwB, -, -, -, hnB, -, -, -, hBo⟩ := pgGuard_spec hg
  have hBr : ∀ i k : Fin n, ‖polyMatrix n Binv θ i k‖ ≤ val (pgBn Binv W cfg bk i.val k.val) := by
    intro i k
    rw [polyMatrix_apply]
    exact norm_le_ofRatUp (PCRep.ofPoly hwB (hBo i.val i.isLt k.val k.isLt) n) hnB hW hθ bk.P rfl
  have hβ0 : 0 ≤ val β := by
    refine le_trans ?_ (hb _ ((List.mem_ofFn' _ _).mpr ⟨⟨0, hn⟩, rfl⟩))
    exact sumUp_nonneg (fun k => (norm_nonneg _).trans (hBr ⟨0, hn⟩ k)) _
  have hB : ‖polyMatrix n Binv θ‖ ≤ val β := by
    rw [norm_le_iff_forall_rowSum hβ0]
    intro i
    refine le_trans ?_ ((sumUp_ge _ _).trans (hb _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)))
    rw [Fin.sum_univ_def]
    exact List.sum_le_sum fun k _ => hBr i k
  obtain ⟨hU, hInv, hDiff⟩ := matrix_inv_of_approx_inverse hE hδ1 hB
  refine ⟨hU, fun i => (rowSum_le_norm _ i).trans (hInv.trans ?_), hDiff⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Sound

/-! ### The base checker's Gram sub-check -/

section Base

variable {n : ℕ} {α : Type} [CertArith α]

/-- The packed Gram check on a truncated memo at the certificate's data, with bound `σB - μ`; the
inverse witness `Bw` is an argument. -/
def checkGramPackedT (Bw : List (List (CertPoly α))) (bk : PGramBook) (mm : PGramMemo)
    (c : TorusCertificate n α) : Bool :=
  (gramPackedCheckT n c.emb Bw c.weight c.cfgLow c.piEnc bk mm (c.params.σB - c.params.μ)).isSome

/-- **Soundness of the truncated Gram sub-check**: the conclusion of the landed
`checkGramPacked_sound`. -/
theorem checkGramPackedT_sound [LawfulCertArith α] {Bw : List (List (CertPoly α))}
    {bk : PGramBook} {mm : PGramMemo} {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkGramPackedT Bw bk mm c = true) :
    ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ := by
  have hS := checkStatic_sound hs
  intro θ hθ
  unfold checkGramPackedT at h
  obtain ⟨δβ, hδβ⟩ := Option.isSome_iff_exists.mp h
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [hS.hrho]; exact hθ
  obtain ⟨hu, hb, -⟩ :=
    (gramPackedCheckT_sound (by have := hS.hn; omega) c.emb Bw hS.hW c.cfgLow hS.hpe bk mm _
      hδβ).2 θ hθ'
  exact ⟨hu, fun i => by have := hb i; push_cast at this; exact this⟩

end Base

end KAM.CertificateSharp.Packed
