/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Gram
public import KAM.Certificate.Torsion.Models

/-!
# Packed models and packed model matrices

A **packed model** `PEnc L A e x r nb n ρ f`: the packed complex array `x` (layout `L`, every slot
within `A`) denotes `2^e` times a trigonometric polynomial `F`, with `‖f - F/2^e‖ ≤ r` and
`‖F/2^e‖ ≤ nb` on the strip `T_ρ`. Products are exact (`pcMul`, scales add), the radius of a
product is `‖a‖ s + r ‖b‖ + r s` (`pmulRad`), sums add radii, and the norm bound of an entry can be
recomputed from its packed weighted norm (`pnorm`, `PEnc.renorm`).

A **packed model matrix** `PMat` holds entries, radii and norm bounds as functions of the row and
column; `PMat.Encloses` is entrywise `PEnc` through index maps (as the landed
`ModelMatrix.EntryEncloses`), with the operations of the landed torsion models: products
(`PMat.mul`), sums, negation, transposition, `Ω₀` (`PMat.omega`), a change of window and scale by
an exact power of two at the zero key (`PMat.shift`), and `PMat.renorm`.

The boundary: a landed degree-`0` model whose mantissas and radius bound are a memo entry
(`memoOk`) is a packed model of its function (`PEnc.ofMemo`); a backend polynomial with a radius
is one too (`PEnc.ofPCRep`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix

section Defs

variable {α : Type} [CertArith α]

/-- Packed complex negation. -/
def pcNeg (x : PC) : PC := ⟨-x.re, -x.im⟩

/-- The constant `c` at the slot `p` of a layout. -/
def pcUnit (w p : ℕ) (c : ℤ) : PC := ⟨c * 2 ^ (w * p), 0⟩

/-- The upward bound of `sup |F/2^e|` from the packed weighted norm. -/
def pnorm (W : CertWeight) (q l : ℕ) (L : PackLayout) (e : ℕ) (x : PC) : α :=
  ofRatUp ((pcNorm W q l L x : ℚ) / 2 ^ (e + 2 * q))

/-- The radius of a product `a b` from the norm bounds `na`, `nb` and the radii `r`, `s`. -/
def pmulRad (na r nb s : α) : α := upAdd (upAdd (upMul na s) (upMul r nb)) (upMul r s)

/-- A packed model matrix: entries, radii and norm bounds. -/
structure PMat (α : Type) where
  x : ℕ → ℕ → PC
  r : ℕ → ℕ → α
  nb : ℕ → ℕ → α

/-- The product of packed model matrices (inner dimension `m`). -/
def PMat.mul (m : ℕ) (A B : PMat α) : PMat α where
  x i j := pcSumN (fun k => pcMul (A.x i k) (B.x k j)) m
  r i j := sumUp (fun k => pmulRad (A.nb i k) (A.r i k) (B.nb k j) (B.r k j)) (List.range m)
  nb i j := sumUp (fun k => upMul (A.nb i k) (B.nb k j)) (List.range m)

/-- The entrywise sum. -/
def PMat.add (A B : PMat α) : PMat α :=
  ⟨fun i j => pcAdd (A.x i j) (B.x i j), fun i j => upAdd (A.r i j) (B.r i j),
    fun i j => upAdd (A.nb i j) (B.nb i j)⟩

/-- The entrywise negation. -/
def PMat.neg (A : PMat α) : PMat α := ⟨fun i j => pcNeg (A.x i j), A.r, A.nb⟩

/-- The transpose. -/
def PMat.tr (A : PMat α) : PMat α := ⟨fun i j => A.x j i, fun i j => A.r j i, fun i j => A.nb j i⟩

/-- `Ω₀` on the rows: row `i < n` is minus row `n + i`, row `n + i` is row `i`. -/
def PMat.omega (n : ℕ) (A : PMat α) : PMat α :=
  ⟨fun i j => if i < n then pcNeg (A.x (n + i) j) else A.x (i - n) j,
    fun i j => if i < n then A.r (n + i) j else A.r (i - n) j,
    fun i j => if i < n then A.nb (n + i) j else A.nb (i - n) j⟩

/-- Every entry times the packed array `u` (a change of window and scale when `u` is a power of
two at the zero key). -/
def PMat.shift (u : PC) (A : PMat α) : PMat α := ⟨fun i j => pcMul (A.x i j) u, A.r, A.nb⟩

/-- The norm bounds recomputed from the packed weighted norms. -/
def PMat.renorm (W : CertWeight) (q l : ℕ) (L : PackLayout) (e : ℕ) (A : PMat α) : PMat α :=
  ⟨A.x, A.r, fun i j => pnorm W q l L e (A.x i j)⟩

/-- One memo entry: the mantissas of the real and imaginary parts and an upper bound of the
radius. -/
abbrev MemoEntry := List (CertKey × ℤ) × List (CertKey × ℤ) × ℚ

/-- The landed model `m` has degree `0`, the memo's mantissas at scale `2^P`, and a radius below
the memo's bound. -/
def memoOk (dec : ℕ → α → Option ℤ) (P : ℕ) (m : CertModel α) (t : MemoEntry) : Bool :=
  m.deg == 0 && decide (m.poly.toMants dec P = some (t.1, t.2.1)) && ble m.rad (ofRatUp t.2.2)

/-- The packed array of a memo entry. -/
def memoPC (L : PackLayout) (t : MemoEntry) : PC := ⟨packOf L t.1, packOf L t.2.1⟩

/-- Both parts of a memo entry pack on `L` within `B`. -/
def memoPackOk (L : PackLayout) (B : ℕ) (t : MemoEntry) : Bool :=
  packRepOk L t.1 B && packRepOk L t.2.1 B

end Defs

/-! ### Packed models -/

section Sound

variable {α : Type} [CertArith α]

/-- `x` packs `2^e` times a polynomial `F` (layout `L`, load `A`) with `‖f - F/2^e‖ ≤ r` and
`‖F/2^e‖ ≤ nb` on `T_ρ`. -/
def PEnc (L : PackLayout) (A e : ℕ) (x : PC) (r nb : α) (n : ℕ) (ρ : ℝ)
    (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ F : (Fin n → ℂ) → ℂ, PCRep L A x n F ∧ ∀ θ ∈ complexStrip n ρ,
    ‖f θ - F θ / 2 ^ e‖ ≤ val r ∧ ‖F θ / 2 ^ e‖ ≤ val nb

/-- Entrywise packed models of a matrix function through index maps. -/
def PMat.Encloses (L : PackLayout) (A e n : ℕ) (ρ : ℝ) {ι κ : Type*} (ri : ι → ℕ) (ci : κ → ℕ)
    (M : PMat α) (F : (Fin n → ℂ) → Matrix ι κ ℂ) : Prop :=
  ∀ i j, PEnc L A e (M.x (ri i) (ci j)) (M.r (ri i) (ci j)) (M.nb (ri i) (ci j)) n ρ
    (fun θ => F θ i j)

variable {L La Lb Lu : PackLayout} {A B e ea eb : ℕ} {x y u : PC} {n : ℕ} {ρ : ℝ}
  {f g : (Fin n → ℂ) → ℂ}

theorem PCRep.neg {F : (Fin n → ℂ) → ℂ} (hx : PCRep L A x n F) :
    PCRep L A (pcNeg x) n (fun θ => -F θ) := by
  obtain ⟨dr, di, hr, hi, hF⟩ := hx
  obtain ⟨nr, tr⟩ := hr.neg
  obtain ⟨ni, ti⟩ := hi.neg
  refine ⟨dr.map Neg.neg, di.map Neg.neg, by simpa [pcNeg] using nr, by simpa [pcNeg] using ni,
    fun θ => ?_⟩
  show -F θ = _
  rw [tr, ti, hF]
  ring

/-- The constant `c` at the slot of the zero key. -/
theorem PCRep.unit (hw : layoutWf L = true) {p : ℕ} (hp : L.slot (List.replicate n 0) = some p)
    (c : ℤ) : PCRep L c.natAbs (pcUnit L.width p c) n (fun _ => (c : ℂ)) := by
  obtain ⟨hkey, hbox⟩ := keyOf_slot hw hp
  obtain ⟨u1, su⟩ := srep_unit (PackLayout.slot_lt_denseLen hp) hbox c
  have hk0 : certKeyFun n (keyOf L p) = 0 := by
    rw [hkey]
    funext j
    simp [certKeyFun, List.getD_eq_getElem?_getD]
  refine ⟨zunit L p c, zzero L, u1, (srep_zero L).mono (Nat.zero_le _), fun θ => ?_⟩
  rw [su, hk0, character_zero, slotSum_zero]
  ring

theorem PEnc.congr {x : PC} {r nb : α} (h : PEnc L A e x r nb n ρ f)
    (hfg : ∀ θ ∈ complexStrip n ρ, f θ = g θ) : PEnc L A e x r nb n ρ g := by
  obtain ⟨F, hF, hb⟩ := h
  exact ⟨F, hF, fun θ hθ => by rw [← hfg θ hθ]; exact hb θ hθ⟩

theorem PEnc.mono {x : PC} {r nb : α} (h : PEnc L A e x r nb n ρ f) {A' : ℕ} (hA : A ≤ A') :
    PEnc L A' e x r nb n ρ f := by
  obtain ⟨F, hF, hb⟩ := h
  exact ⟨F, hF.mono hA, hb⟩

theorem PEnc.nonneg {x : PC} {r nb : α} (h : PEnc L A e x r nb n ρ f) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) : 0 ≤ val r ∧ 0 ≤ val nb := by
  obtain ⟨F, -, hb⟩ := h
  exact ⟨(norm_nonneg _).trans (hb θ hθ).1, (norm_nonneg _).trans (hb θ hθ).2⟩

variable [LawfulCertArith α]

/-- **Product** of packed models (exact, window layout, scales add). -/
theorem PEnc.mul {m : ℕ} (hc : PackLayout.compat m La Lb = true) (hwa : layoutWf La = true)
    (hwb : layoutWf Lb = true) {r na s nb : α} (hx : PEnc La A ea x r na n ρ f)
    (hy : PEnc Lb B eb y s nb n ρ g) :
    PEnc (win La Lb) (mulLoad La Lb A B) (ea + eb) (pcMul x y) (pmulRad na r nb s) (upMul na nb)
      n ρ (fun θ => f θ * g θ) := by
  obtain ⟨F, hF, hFb⟩ := hx
  obtain ⟨G, hG, hGb⟩ := hy
  refine ⟨_, PCRep.mul hc hwa hwb hF hG, fun θ hθ => ?_⟩
  obtain ⟨h1, h2⟩ := hFb θ hθ
  obtain ⟨h3, h4⟩ := hGb θ hθ
  have hna : 0 ≤ val na := (norm_nonneg _).trans h2
  have hnb : 0 ≤ val nb := (norm_nonneg _).trans h4
  have hr : 0 ≤ val r := (norm_nonneg _).trans h1
  have hs : 0 ≤ val s := (norm_nonneg _).trans h3
  have he : F θ * G θ / 2 ^ (ea + eb) = F θ / 2 ^ ea * (G θ / 2 ^ eb) := by
    rw [pow_add]
    field_simp
  beta_reduce
  rw [he]
  set p := F θ / 2 ^ ea
  set q := G θ / 2 ^ eb
  refine ⟨?_, ?_⟩
  · have hid : f θ * g θ - p * q = p * (g θ - q) + (f θ - p) * g θ := by ring
    have hg : ‖g θ‖ ≤ val nb + val s := by
      have := norm_add_le (g θ - q) q
      rw [sub_add_cancel] at this
      linarith
    have m1 := LawfulCertArith.upMul_ge na s hna hs
    have m2 := LawfulCertArith.upMul_ge r nb hr hnb
    have m3 := LawfulCertArith.upMul_ge r s hr hs
    have a1 := LawfulCertArith.upAdd_ge (upMul na s) (upMul r nb)
    have a2 := LawfulCertArith.upAdd_ge (upAdd (upMul na s) (upMul r nb)) (upMul r s)
    have hb : ‖f θ * g θ - p * q‖ ≤ val na * val s + val r * (val nb + val s) := by
      rw [hid]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul h2 h3 (norm_nonneg _) hna
      · rw [norm_mul]
        exact mul_le_mul h1 hg (norm_nonneg _) hr
    unfold pmulRad
    have : val r * (val nb + val s) = val r * val nb + val r * val s := by ring
    linarith
  · rw [norm_mul]
    exact (mul_le_mul h2 h4 (norm_nonneg _) hna).trans (LawfulCertArith.upMul_ge _ _ hna hnb)

/-- **Sum** of packed models on one layout and scale. -/
theorem PEnc.add {r na s nb : α} (hx : PEnc L A e x r na n ρ f) (hy : PEnc L B e y s nb n ρ g) :
    PEnc L (A + B) e (pcAdd x y) (upAdd r s) (upAdd na nb) n ρ (fun θ => f θ + g θ) := by
  obtain ⟨F, hF, hFb⟩ := hx
  obtain ⟨G, hG, hGb⟩ := hy
  refine ⟨_, hF.add hG, fun θ hθ => ?_⟩
  obtain ⟨h1, h2⟩ := hFb θ hθ
  obtain ⟨h3, h4⟩ := hGb θ hθ
  beta_reduce
  have e1 : f θ + g θ - (F θ + G θ) / 2 ^ e = (f θ - F θ / 2 ^ e) + (g θ - G θ / 2 ^ e) := by
    ring
  have e2 : (F θ + G θ) / 2 ^ e = F θ / 2 ^ e + G θ / 2 ^ e := by ring
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact (norm_add_le _ _).trans ((add_le_add h1 h3).trans (LawfulCertArith.upAdd_ge _ _))
  · rw [e2]
    exact (norm_add_le _ _).trans ((add_le_add h2 h4).trans (LawfulCertArith.upAdd_ge _ _))

omit [LawfulCertArith α] in
/-- **Negation** of a packed model. -/
theorem PEnc.neg {r nb : α} (hx : PEnc L A e x r nb n ρ f) :
    PEnc L A e (pcNeg x) r nb n ρ (fun θ => -f θ) := by
  obtain ⟨F, hF, hb⟩ := hx
  refine ⟨_, hF.neg, fun θ hθ => ?_⟩
  obtain ⟨h1, h2⟩ := hb θ hθ
  beta_reduce
  refine ⟨?_, ?_⟩
  · rw [show -f θ - -F θ / 2 ^ e = -(f θ - F θ / 2 ^ e) by ring, norm_neg]
    exact h1
  · rw [neg_div, norm_neg]
    exact h2

/-- **Sums** of packed models over `k < m`. -/
theorem PEnc.sumN {Ak : ℕ → ℕ} {xk : ℕ → PC} {rk nk : ℕ → α} {fk : ℕ → (Fin n → ℂ) → ℂ}
    (m : ℕ) (h : ∀ k < m, PEnc L (Ak k) e (xk k) (rk k) (nk k) n ρ (fk k)) :
    PEnc L ((List.range m).map Ak).sum e (pcSumN xk m) (sumUp rk (List.range m))
      (sumUp nk (List.range m)) n ρ (fun θ => ∑ k ∈ Finset.range m, fk k θ) := by
  choose! F hF hb using h
  refine ⟨_, PCRep.sumN m hF, fun θ hθ => ?_⟩
  beta_reduce
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk =>
      (hb k (Finset.mem_range.mp hk) θ hθ).1).trans ?_)
    rw [← list_sum_map_range_eq]
    exact sumUp_ge _ _
  · rw [Finset.sum_div]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk =>
      (hb k (Finset.mem_range.mp hk) θ hθ).2).trans ?_)
    rw [← list_sum_map_range_eq]
    exact sumUp_ge _ _

omit [LawfulCertArith α] in
/-- **Shift** by an exact power of two at the zero key: a change of window and scale. -/
theorem PEnc.shift {m : ℕ} (hc : PackLayout.compat m La Lu = true) (hwa : layoutWf La = true)
    (hwu : layoutWf Lu = true) {c k : ℕ} {r nb : α} (hx : PEnc La A e x r nb n ρ f)
    (hu : PCRep Lu c u n (fun _ => (2 : ℂ) ^ k)) :
    PEnc (win La Lu) (mulLoad La Lu A c) (e + k) (pcMul x u) r nb n ρ f := by
  obtain ⟨F, hF, hb⟩ := hx
  refine ⟨_, PCRep.mul hc hwa hwu hF hu, fun θ hθ => ?_⟩
  have : F θ * 2 ^ k / 2 ^ (e + k) = F θ / 2 ^ e := by
    rw [pow_add]
    field_simp
  rw [this]
  exact hb θ hθ

/-- **Norm bound** from the packed weighted norm. -/
theorem PEnc.renorm {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {q l : ℕ}
    (hok : normOk W q l A L = true) {r nb : α} (hx : PEnc L A e x r nb n W.rho f) :
    PEnc L A e x r (pnorm W q l L e x) n W.rho f := by
  obtain ⟨F, hF, hb⟩ := hx
  refine ⟨F, hF, fun θ hθ => ⟨(hb θ hθ).1, ?_⟩⟩
  exact norm_le_ofRatUp hF hok hW hθ e (by field_simp)

/-- **Boundary**: a packed polynomial within `r` of `f`. -/
theorem PEnc.ofPCRep {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {q l : ℕ}
    (hok : normOk W q l A L = true) {p : (Fin n → ℂ) → ℂ}
    (hx : PCRep L A x n (fun θ => p θ * 2 ^ e)) {r : α}
    (hp : ∀ θ ∈ complexStrip n W.rho, ‖f θ - p θ‖ ≤ val r) :
    PEnc L A e x r (pnorm W q l L e x) n W.rho f := by
  refine ⟨_, hx, fun θ hθ => ⟨?_, norm_le_ofRatUp hx hok hW hθ e (by field_simp)⟩⟩
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ two_ne_zero)]
  exact hp θ hθ

/-- **Boundary**: a landed degree-`0` model matching a memo entry. -/
theorem PEnc.ofMemo {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {q l : ℕ}
    (hok : normOk W q l A L = true) (hw : layoutWf L = true) {dec : ℕ → α → Option ℤ} {P : ℕ}
    {m : CertModel α} {t : MemoEntry} (hm : m.Encloses n W.rho f) (ht : memoOk dec P m t = true)
    (hp : memoPackOk L A t = true) :
    PEnc L A P (memoPC L t) (ofRatUp t.2.2 : α) (pnorm W q l L P (memoPC L t) : α) n W.rho f :=
    by
  simp only [memoOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  simp only [memoPackOk, Bool.and_eq_true] at hp
  obtain ⟨⟨hd, hmt⟩, hrad⟩ := ht
  refine PEnc.ofPCRep hW hok (PCRep.ofMants hmt hw hp.1 hp.2) fun θ hθ => ?_
  exact (encloses_deg0 hm hd hθ).trans (LawfulCertArith.ble_sound _ _ hrad)

/-! ### Packed model matrices -/

variable {ι κ μ : Type*} {ri : ι → ℕ} {ci : κ → ℕ}

/-- **Product** of packed model matrices (inner index `μ ≃ Fin m`). -/
theorem PMat.Encloses.mul [Fintype μ] {m' : ℕ} (hc : PackLayout.compat m' La Lb = true)
    (hwa : layoutWf La = true) (hwb : layoutWf Lb = true) {m : ℕ} {mi : μ → ℕ} (eq : Fin m ≃ μ)
    (he : ∀ k, mi (eq k) = k.val) {M N : PMat α} {FA : (Fin n → ℂ) → Matrix ι μ ℂ}
    {FB : (Fin n → ℂ) → Matrix μ κ ℂ} (hA : PMat.Encloses La A ea n ρ ri mi M FA)
    (hB : PMat.Encloses Lb B eb n ρ mi ci N FB) :
    PMat.Encloses (win La Lb) (m * mulLoad La Lb A B) (ea + eb) n ρ ri ci (M.mul m N)
      (fun θ => FA θ * FB θ) := by
  intro i j
  set C := mulLoad La Lb A B
  let fk : ℕ → (Fin n → ℂ) → ℂ := fun k θ =>
    if hk : k < m then FA θ i (eq ⟨k, hk⟩) * FB θ (eq ⟨k, hk⟩) j else 0
  have hk : ∀ k < m, PEnc (win La Lb) C (ea + eb) (pcMul (M.x (ri i) k) (N.x k (ci j)))
      (pmulRad (M.nb (ri i) k) (M.r (ri i) k) (N.nb k (ci j)) (N.r k (ci j)))
      (upMul (M.nb (ri i) k) (N.nb k (ci j))) n ρ (fk k) := by
    intro k hkm
    have h1 := hA i (eq ⟨k, hkm⟩)
    have h2 := hB (eq ⟨k, hkm⟩) j
    rw [he] at h1 h2
    refine (PEnc.mul hc hwa hwb h1 h2).congr fun θ _ => ?_
    simp only [fk, hkm, ↓reduceDIte]
  have hs := PEnc.sumN (L := win La Lb) (Ak := fun _ => C)
    (xk := fun k => pcMul (M.x (ri i) k) (N.x k (ci j)))
    (rk := fun k => pmulRad (M.nb (ri i) k) (M.r (ri i) k) (N.nb k (ci j)) (N.r k (ci j)))
    (nk := fun k => upMul (M.nb (ri i) k) (N.nb k (ci j))) (fk := fk) m hk
  have hload : ((List.range m).map fun _ : ℕ => C).sum = m * C := by simp
  rw [hload] at hs
  unfold PMat.mul
  dsimp only
  refine hs.congr fun θ _ => ?_
  have hsum : ∑ k ∈ Finset.range m, fk k θ = ∑ k : Fin m, FA θ i (eq k) * FB θ (eq k) j := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => fk k θ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [fk, k.isLt, ↓reduceDIte]
  rw [hsum, Matrix.mul_apply]
  exact eq.sum_comp (fun k => FA θ i k * FB θ k j)

/-- **Sum** of packed model matrices. -/
theorem PMat.Encloses.add {M N : PMat α} {FA FB : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses L A e n ρ ri ci M FA) (hB : PMat.Encloses L B e n ρ ri ci N FB) :
    PMat.Encloses L (A + B) e n ρ ri ci (M.add N) (fun θ => FA θ + FB θ) :=
  fun i j => ((hA i j).add (hB i j)).congr fun θ _ => by simp [Matrix.add_apply]

omit [LawfulCertArith α] in
/-- **Negation** of a packed model matrix. -/
theorem PMat.Encloses.neg {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses L A e n ρ ri ci M F) :
    PMat.Encloses L A e n ρ ri ci M.neg (fun θ => -F θ) :=
  fun i j => (hA i j).neg.congr fun θ _ => by simp [Matrix.neg_apply]

omit [LawfulCertArith α] in
/-- **Transpose** of a packed model matrix. -/
theorem PMat.Encloses.tr {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses L A e n ρ ri ci M F) :
    PMat.Encloses L A e n ρ ci ri M.tr (fun θ => (F θ)ᵀ) :=
  fun j i => hA i j

omit [LawfulCertArith α] in
/-- **`Ω₀`** on the rows of a packed model matrix. -/
theorem PMat.Encloses.omega [Fintype κ] {M : PMat α}
    {F : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) κ ℂ}
    (hA : PMat.Encloses L A e n ρ phaseNat ci M F) :
    PMat.Encloses L A e n ρ phaseNat ci (M.omega n) (fun θ => omegaZeroMatrix n * F θ) := by
  rintro (i | i) j
  · have h := (hA (Sum.inr i) j).neg
    simp only [phaseNat] at h ⊢
    simp only [PMat.omega, i.isLt, ↓reduceIte]
    exact h.congr fun θ _ => by rw [omegaZeroMatrix_mul_apply_inl]
  · have h := hA (Sum.inl i) j
    have hn : ¬(n + i.val < n) := by omega
    simp only [phaseNat] at h ⊢
    simp only [PMat.omega, hn, ↓reduceIte, Nat.add_sub_cancel_left]
    exact h.congr fun θ _ => by rw [omegaZeroMatrix_mul_apply_inr]

omit [LawfulCertArith α] in
/-- **Shift** of a packed model matrix by an exact power of two at the zero key. -/
theorem PMat.Encloses.shift {m : ℕ} (hc : PackLayout.compat m La Lu = true)
    (hwa : layoutWf La = true) (hwu : layoutWf Lu = true) {c k : ℕ}
    (hu : PCRep Lu c u n (fun _ => (2 : ℂ) ^ k)) {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses La A e n ρ ri ci M F) :
    PMat.Encloses (win La Lu) (mulLoad La Lu A c) (e + k) n ρ ri ci (M.shift u) F :=
  fun i j => (hA i j).shift hc hwa hwu hu

/-- **Norm bounds** of a packed model matrix from the packed weighted norms. -/
theorem PMat.Encloses.renorm {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {q l : ℕ} (hok : normOk W q l A L = true) {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses L A e n W.rho ri ci M F) :
    PMat.Encloses L A e n W.rho ri ci (M.renorm W q l L e) F :=
  fun i j => (hA i j).renorm hW hok

omit [LawfulCertArith α] in
theorem PMat.Encloses.mono {M : PMat α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : PMat.Encloses L A e n ρ ri ci M F) {A' : ℕ} (hA' : A ≤ A') :
    PMat.Encloses L A' e n ρ ri ci M F :=
  fun i j => (hA i j).mono hA'

end Sound

end KAM.CertificateSharp.Packed
