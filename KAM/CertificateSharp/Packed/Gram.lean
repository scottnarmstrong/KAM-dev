/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Complex
public import KAM.Certificate.Gram

/-!
# The packed Gram stage

The landed Gram check (`gramCheck`, `KAM/Certificate/Gram.lean`) certifies that `G = DKᵀ DK` is
invertible on the strip, with an approximate inverse `B`, through `‖1 - B G‖ ≤ δ < 1`. Its kernel
cost is dominated by the `2n·n·n + n³` model products (each a sharded, advice-checked packed product
with a
per-slot decode) and the per-coefficient sums and norms.

`gramPackedCheck` certifies **the same proposition** (`gramPackedCheck_sound` has the conclusion of
the landed `gramCheck_sound`) with packed arithmetic:

* **boundary**: every entry of `DK` is the landed model `dkAngleModel`/`dkActionModel` (degree `0`),
  and every entry of `B` is the landed polynomial; their mantissas are packed once (`pcOfPoly`);
* **exact products, no rounding**: `G_kj = Σ_r DK_rk DK_rj` and `(B G)_ij = Σ_k B_ik G_kj` are
  computed exactly as packed integers on window layouts (`pcMul`, `pcSumN`); then
  `δ_ij - (B G)_ij` (`pcUnitSub`);
* **norms**: packed weighted norms of the `DK` entries, of `B` and of the defects (`pcNorm`);
* **radii** (backend, upward): the `DK` models' radii propagate through `G` (cross terms) and `B G`;
* the landed final test `gramBoundsOk` on the row sums.

Every guard is decidable from metadata (`PGramBook`: layouts, load bounds, norm precision); the
soundness theorem assumes nothing else.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix.Norms.Operator

/-- The untrusted metadata of a packed Gram check. -/
structure PGramBook where
  /-- mantissa scale of the boundary -/
  P : ℕ
  /-- layout of every `DK` entry -/
  L1 : PackLayout
  /-- layout of every entry of the inverse witness `B` -/
  LB : PackLayout
  /-- load bounds of the `DK` and `B` mantissas -/
  bK : ℕ
  bB : ℕ
  /-- norm precision -/
  q : ℕ
  /-- norm offset exponents of the `DK` entries, of `B` and of the defects -/
  lK : ℕ
  lB : ℕ
  lD : ℕ

/-- The window of the `G` entries. -/
def PGramBook.L2 (bk : PGramBook) : PackLayout := win bk.L1 bk.L1

/-- The window of the `B G` entries. -/
def PGramBook.L3 (bk : PGramBook) : PackLayout := win bk.LB bk.L2

/-- Load bounds of `G`, `B G` and the defects. -/
def PGramBook.bG (bk : PGramBook) (n : ℕ) : ℕ := 2 * n * mulLoad bk.L1 bk.L1 bk.bK bk.bK

def PGramBook.bE (bk : PGramBook) (n : ℕ) : ℕ := n * mulLoad bk.LB bk.L2 bk.bB (bk.bG n)

def PGramBook.bD (bk : PGramBook) (n : ℕ) : ℕ := 2 ^ (3 * bk.P) + bk.bE n

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
  (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (bk : PGramBook)

/-- The landed model of the `DK` entry `(r, a)`: angle rows `r < n`, then action rows. -/
def dkModel (r a : ℕ) : CertModel α :=
  if r < n then dkAngleModel n K W pe r a else dkActionModel n K W pe (r - n) a

/-- The memoized boundary of the `DK` entries (untrusted, backend-free): the mantissas of every
entry's polynomial at scale `2^P` (real and imaginary parts) and an upper bound of its radius. Each
entry is checked against the landed model by `pgEntryOk`, one entry per declaration if needed. -/
structure PGramMemo where
  re : List (List (List (CertKey × ℤ)))
  im : List (List (List (CertKey × ℤ)))
  rad : List (List ℚ)

def PGramMemo.reAt (mm : PGramMemo) (r a : ℕ) : List (CertKey × ℤ) := (mm.re.getD r []).getD a []

def PGramMemo.imAt (mm : PGramMemo) (r a : ℕ) : List (CertKey × ℤ) := (mm.im.getD r []).getD a []

def PGramMemo.radAt (mm : PGramMemo) (r a : ℕ) : ℚ := (mm.rad.getD r []).getD a 0

/-- **One boundary entry**: the landed `DK` model `(r, a)` has degree `0`, its mantissas are the
memo's, and its radius is below the memo's bound. -/
def pgEntryOk (mm : PGramMemo) (r a : ℕ) : Bool :=
  (dkModel n K W pe r a).deg == 0 &&
    decide ((dkModel n K W pe r a).poly.toMants cfg.toMant bk.P =
      some (mm.reAt r a, mm.imAt r a)) &&
    ble (dkModel n K W pe r a).rad (ofRatUp (mm.radAt r a))

/-- Every boundary entry. -/
def pgEntries (mm : PGramMemo) : Bool :=
  (List.range (2 * n)).all fun r => (List.range n).all fun a => pgEntryOk n K W cfg pe bk mm r a

variable (mm : PGramMemo)

/-- Packed `DK` entry (from the memo's mantissas). -/
def pgK (r a : ℕ) : PC := ⟨packOf bk.L1 (mm.reAt r a), packOf bk.L1 (mm.imAt r a)⟩

/-- Packed entry of `B`. -/
def pgB (i k : ℕ) : PC := pcOfPoly cfg.toMant bk.P bk.LB (gramInvPoly Binv i k)

/-- Packed exact `G_kj = Σ_r DK_rk DK_rj` (scale `2^(2P)`). -/
def pgG (k j : ℕ) : PC := pcSumN (fun r => pcMul (pgK bk mm r k) (pgK bk mm r j)) (2 * n)

/-- Packed exact `(B G)_ij` (scale `2^(3P)`). -/
def pgE (i j : ℕ) : PC :=
  pcSumN (fun k => pcMul (pgB Binv cfg bk i k) (pgG n bk mm k j)) n

/-- The slot of the zero key in the window of `B G`. -/
def pgP0 : ℕ := (bk.L3.slot (List.replicate n 0)).getD 0

/-- Packed defect `δ_ij - (B G)_ij` (scale `2^(3P)`). -/
def pgD (i j : ℕ) : PC :=
  pcUnitSub bk.L3.width (pgP0 n bk) (if i = j then 2 ^ (3 * bk.P) else 0)
    (pgE n Binv cfg bk mm i j)

/-- Upper bound of `sup |DK_ra|` from the packed norm. -/
def pgKn (r a : ℕ) : α :=
  ofRatUp ((pcNorm W bk.q bk.lK bk.L1 (pgK bk mm r a) : ℚ) / 2 ^ (bk.P + 2 * bk.q))

/-- The radius bound of the `DK` entry `(r, a)`. -/
def pgKr (r a : ℕ) : α := ofRatUp (mm.radAt r a)

/-- Radius of `G_kj`: the cross terms of the `DK` radii. -/
def pgGr (k j : ℕ) : α :=
  sumUp (fun r : ℕ => upAdd (upAdd (upMul (pgKn W bk mm r k) (pgKr (α := α) mm r j))
      (upMul (pgKn W bk mm r j) (pgKr (α := α) mm r k)))
      (upMul (pgKr (α := α) mm r k) (pgKr (α := α) mm r j))) (List.range (2 * n))

/-- Upper bound of `sup |B_ik|`. -/
def pgBn (i k : ℕ) : α :=
  ofRatUp ((pcNorm W bk.q bk.lB bk.LB (pgB Binv cfg bk i k) : ℚ) / 2 ^ (bk.P + 2 * bk.q))

/-- Upper bound of `sup |(1 - B G)_ij|`. -/
def pgDn (i j : ℕ) : α :=
  upAdd (ofRatUp ((pcNorm W bk.q bk.lD bk.L3 (pgD n Binv cfg bk mm i j) : ℚ) /
      2 ^ (3 * bk.P + 2 * bk.q)))
    (sumUp (fun k : ℕ => upMul (pgBn Binv W cfg bk i k) (pgGr (α := α) n W bk mm k j))
      (List.range n))

/-- Row sums of the defect bounds. -/
def pgDRows : List α :=
  List.ofFn fun i : Fin n => sumUp (fun j : Fin n => pgDn n Binv W cfg bk mm i.val j.val)
    (List.finRange n)

/-- Row sums of the bounds of `B`. -/
def pgBRows : List α :=
  List.ofFn fun i : Fin n => sumUp (fun k : Fin n => pgBn Binv W cfg bk i.val k.val)
    (List.finRange n)

/-- **The guard of the core** (decidable: metadata, the memo's packing, the boundary of `B`). -/
def pgGuard : Bool :=
  layoutWf bk.L1 && layoutWf bk.LB && PackLayout.compat n bk.L1 bk.L1 &&
    PackLayout.compat n bk.LB bk.L2 && normOk W bk.q bk.lK bk.bK bk.L1 &&
    normOk W bk.q bk.lB bk.bB bk.LB && normOk W bk.q bk.lD (bk.bD n) bk.L3 &&
    (bk.L3.slot (List.replicate n 0)).isSome &&
    ((List.range (2 * n)).all fun r => (List.range n).all fun a =>
      packRepOk bk.L1 (mm.reAt r a) bk.bK && packRepOk bk.L1 (mm.imAt r a) bk.bK) &&
    ((List.range n).all fun i => (List.range n).all fun k =>
      pcOfPolyOk cfg.toMant bk.P bk.LB bk.bB (gramInvPoly Binv i k))

/-- **The core of the packed Gram check** (everything but the boundary entries): the landed final
test on packed row sums. Returns `(δ, β)`. -/
def gramPackedCore (σBμ : ℚ) : Option (α × α) :=
  if gramInvShapeOk n Binv && pgGuard n Binv W cfg bk mm then
    if gramBoundsOk (pgDRows n Binv W cfg bk mm) (pgBRows n Binv W cfg bk)
        (maxCandidate (pgDRows n Binv W cfg bk mm)) (maxCandidate (pgBRows n Binv W cfg bk))
        σBμ then
      some (maxCandidate (pgDRows n Binv W cfg bk mm), maxCandidate (pgBRows n Binv W cfg bk))
    else none
  else none

/-- **The packed Gram check**: the boundary entries, then the core. -/
def gramPackedCheck (σBμ : ℚ) : Option (α × α) :=
  if pgEntries n K W cfg pe bk mm then gramPackedCore n Binv W cfg bk mm σBμ else none

theorem pgEntries_of {mm : PGramMemo}
    (h : ∀ r < 2 * n, ∀ a < n, pgEntryOk n K W cfg pe bk mm r a = true) :
    pgEntries n K W cfg pe bk mm = true := by
  simp only [pgEntries, List.all_eq_true, List.mem_range]
  exact h

/-- The check from its boundary entries and its core (for proofs split across declarations). -/
theorem gramPackedCheck_eq_core {mm : PGramMemo} (h : pgEntries n K W cfg pe bk mm = true)
    (σBμ : ℚ) :
    gramPackedCheck n K Binv W cfg pe bk mm σBμ = gramPackedCore n Binv W cfg bk mm σBμ := by
  simp [gramPackedCheck, h]

end Defs

/-! ### Soundness -/

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

/-- The `DK` entry `(r, a)` as a function: angle rows `r < n`, then action rows. -/
def dkFun (n : ℕ) (K : CertEmbedding α) (r : ℕ) (a : Fin n) (θ : Fin n → ℂ) : ℂ :=
  if h : r < n then (fderiv ℂ (K.eval n) θ (Pi.single a 1)).1 ⟨r, h⟩
  else if h' : r - n < n then (fderiv ℂ (K.eval n) θ (Pi.single a 1)).2 ⟨r - n, h'⟩ else 0

theorem dkModel_encloses {n : ℕ} (K : CertEmbedding α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    {r : ℕ} (hr : r < 2 * n) (a : Fin n) :
    (dkModel n K W pe r a.val).Encloses n W.rho (dkFun n K r a) := by
  unfold dkModel
  by_cases h : r < n
  · rw [ite_eq_left h]
    refine (dkAngleModel_encloses hW hpe K ⟨r, h⟩ a).of_eq_fun fun θ => ?_
    simp [dkFun, h]
  · rw [ite_eq_right h]
    have h' : r - n < n := by omega
    refine (dkActionModel_encloses hW hpe K ⟨r - n, h'⟩ a).of_eq_fun fun θ => ?_
    simp [dkFun, h, h']

omit [LawfulCertArith α] in
/-- The Gram entry as a sum over the `2n` rows of `DK`. -/
theorem gramMatrix_eq_dkFun {n : ℕ} (K : CertEmbedding α) (θ : Fin n → ℂ) (k j : Fin n) :
    gramMatrix (K.eval n) θ k j =
      ∑ r ∈ Finset.range (2 * n), dkFun n K r k θ * dkFun n K r j θ := by
  rw [two_mul, Finset.sum_range_add]
  simp only [gramMatrix, dotℂ, Finset.sum_add_distrib]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun r => dkFun n K r k θ * dkFun n K r j θ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dkFun, i.isLt]
  · rw [← Fin.sum_univ_eq_sum_range (fun r => dkFun n K (n + r) k θ * dkFun n K (n + r) j θ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dkFun, i.isLt]

omit [LawfulCertArith α] in
/-- At degree `0` an enclosure is a plain sup bound. -/
theorem encloses_deg0 {n : ℕ} {ρ : ℝ} {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (h : m.Encloses n ρ f) (hd : m.deg = 0) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    ‖f θ - m.poly.eval n θ‖ ≤ val m.rad := by
  have := h θ hθ
  rwa [hd, zpow_zero, zpow_zero, one_mul, one_mul] at this

/-- The packed norm, scaled, is below its upward rational conversion. -/
theorem norm_le_ofRatUp {n : ℕ} {L : PackLayout} {A : ℕ} {x : PC} {F : (Fin n → ℂ) → ℂ}
    (hx : PCRep L A x n F) {W : CertWeight} {q l : ℕ} (hok : normOk W q l A L = true) {s N : ℕ}
    (hW : checkWeight W s N = true) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) (e : ℕ)
    {g : ℂ} (hg : F θ = g * 2 ^ e) :
    ‖g‖ ≤ val (ofRatUp ((pcNorm W q l L x : ℚ) / 2 ^ (e + 2 * q)) : α) := by
  have h1 := hx.norm_le hok hW hθ
  rw [hg, norm_mul, norm_pow, Complex.norm_ofNat] at h1
  refine le_trans ?_ (LawfulCertArith.ofRatUp_ge _)
  push_cast
  rw [pow_add, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at h1
  calc ‖g‖ * (2 ^ e * 2 ^ (2 * q)) = ‖g‖ * 2 ^ e * 2 ^ (2 * q) := by ring
    _ ≤ _ := h1

omit [LawfulCertArith α] in
theorem pgGuard_spec {n : ℕ} {Binv : List (List (CertPoly α))} {W : CertWeight}
    {cfg : ModelConfig α} {bk : PGramBook} {mm : PGramMemo}
    (h : pgGuard n Binv W cfg bk mm = true) :
    layoutWf bk.L1 = true ∧ layoutWf bk.LB = true ∧ PackLayout.compat n bk.L1 bk.L1 = true ∧
      PackLayout.compat n bk.LB bk.L2 = true ∧ normOk W bk.q bk.lK bk.bK bk.L1 = true ∧
      normOk W bk.q bk.lB bk.bB bk.LB = true ∧ normOk W bk.q bk.lD (bk.bD n) bk.L3 = true ∧
      (bk.L3.slot (List.replicate n 0)).isSome = true ∧
      (∀ r < 2 * n, ∀ a < n, packRepOk bk.L1 (mm.reAt r a) bk.bK = true ∧
        packRepOk bk.L1 (mm.imAt r a) bk.bK = true) ∧
      (∀ i < n, ∀ k < n, pcOfPolyOk cfg.toMant bk.P bk.LB bk.bB (gramInvPoly Binv i k) = true) := by
  simp only [pgGuard, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun r hr a ha => h9 r hr a ha, h10⟩

omit [LawfulCertArith α] in
theorem pgEntries_spec {n : ℕ} {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {bk : PGramBook} {mm : PGramMemo}
    (h : pgEntries n K W cfg pe bk mm = true) {r a : ℕ} (hr : r < 2 * n) (ha : a < n) :
    (dkModel n K W pe r a).deg = 0 ∧
      (dkModel n K W pe r a).poly.toMants cfg.toMant bk.P = some (mm.reAt r a, mm.imAt r a) ∧
      ble (dkModel n K W pe r a).rad (ofRatUp (mm.radAt r a)) = true := by
  simp only [pgEntries, List.all_eq_true, List.mem_range] at h
  have := h r hr a ha
  simp only [pgEntryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- The memo's packed `DK` entry denotes `2^P` times the landed model's polynomial. -/
theorem PCRep.ofMants {n : ℕ} {p : CertPoly α} {dec : ℕ → α → Option ℤ} {P : ℕ}
    {x y : List (CertKey × ℤ)} (hm : p.toMants dec P = some (x, y)) {L : PackLayout} {B : ℕ}
    (hw : layoutWf L = true) (hx : packRepOk L x B = true) (hy : packRepOk L y B = true) :
    PCRep L B ⟨packOf L x, packOf L y⟩ n (fun θ => p.eval n θ * 2 ^ P) := by
  obtain ⟨d1, s1, e1⟩ := srep_of_packRepOk hw hx
  obtain ⟨d2, s2, e2⟩ := srep_of_packRepOk hw hy
  refine ⟨d1, d2, s1, s2, fun θ => ?_⟩
  beta_reduce
  rw [CertPoly.toMants_sound hm θ, e1 n θ, e2 n θ]
  field_simp

/-- **The defect entry bound** of the packed Gram check. -/
theorem pgDn_bound {n : ℕ} (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo}
    (he : pgEntries n K W cfg pe bk mm = true) (hg : pgGuard n Binv W cfg bk mm = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) (i j : Fin n) :
    ‖(1 - polyMatrix n Binv θ * gramMatrix (K.eval n) θ) i j‖ ≤
      val (pgDn n Binv W cfg bk mm i.val j.val) := by
  obtain ⟨hw1, hwB, hc11, hcB2, hnK, hnB, hnD, hp0, hK, hB⟩ := pgGuard_spec hg
  have hw2 : layoutWf bk.L2 = true := win_wf hc11 hw1 hw1
  have hρ : (0 : ℝ) < W.rho := CertWeight.rho_pos hW
  set Pp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun r a θ => (dkModel n K W pe r a).poly.eval n θ
  set Bp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun i k θ => (gramInvPoly Binv i k).eval n θ
  set Gp : ℕ → ℕ → (Fin n → ℂ) → ℂ := fun k j θ =>
    ∑ r ∈ Finset.range (2 * n), Pp r k θ * Pp r j θ
  -- representations
  have hKr : ∀ r < 2 * n, ∀ a < n, PCRep bk.L1 bk.bK (pgK bk mm r a) n
      (fun θ => Pp r a θ * 2 ^ bk.P) := fun r hr a ha =>
    PCRep.ofMants (pgEntries_spec he hr ha).2.1 hw1 (hK r hr a ha).1 (hK r hr a ha).2
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
    obtain ⟨hd, -, hrad⟩ := pgEntries_spec he hr a.isLt
    have ek := dkModel_encloses K hW hpe hr a
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

/-- **Packed Gram check contract**: the conclusion of the landed `gramCheck_sound`. -/
theorem gramPackedCheck_sound {n : ℕ} (hn : 1 ≤ n) (K : CertEmbedding α)
    (Binv : List (List (CertPoly α))) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (bk : PGramBook) (mm : PGramMemo) (σBμ : ℚ) {δβ : α × α}
    (h : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) :
    val δβ.1 < 1 ∧ ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det ∧
      (∀ i, ∑ j, ‖(gramMatrix (K.eval n) θ)⁻¹ i j‖ ≤ σBμ) ∧
      ‖(gramMatrix (K.eval n) θ)⁻¹ - polyMatrix n Binv θ‖ ≤
        val δβ.1 * val δβ.2 / (1 - val δβ.1) := by
  unfold gramPackedCheck at h
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
    exact List.sum_le_sum fun j _ => pgDn_bound K Binv hW cfg hpe he hg hθ i j
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

end KAM.CertificateSharp.Packed
