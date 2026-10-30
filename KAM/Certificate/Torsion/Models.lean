/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Frame
public import KAM.Certificate.Torsion.Average
public import KAM.Certificate.Expr.Compose
public import KAM.Certificate.Expr.Diff
public import KAM.Certificate.Freq
public import KAM.Certificate.Model.Inv

/-!
# The models of the bordered torsion

`torsionModels` builds the entrywise models of the LITERAL frozen
`extendedTorsion e.eval (K.eval n) (s ω)` on `T_ρ`, valid for every `ω` in the frequency box
from matrices of models (`modelMatMul`, `modelMatAdd`,
`modelMatNeg`, `modelMatTranspose`, `modelMatOmega`):

* `L = DK` (`dkModels`, the Gram check's `DK` entries) and `D_{sω} L = Σ_l (sω)_l ∂_l L`
  (`dkwModels`, second derivatives `CertModel.ofDeriv2`, the frequency balls `freqModel`);
* `G⁻¹` as the Gram witness `B` with the certified radius `δβ/(1 - δ)` (`gramInvModels`,
  `gramInvRadius`, `1/(1 - δ)` through `recipOneSubUp`);
* `N = Ω₀ (L G⁻¹)`, `DG = D L ᵀ L + Lᵀ D L`, `D(G⁻¹) = -(G⁻¹ DG G⁻¹)`,
  `DN = Ω₀ (D L G⁻¹ + L D(G⁻¹))` (`fderiv_normalMat_apply`);
* `DX_H ∘ K` from the jet slots `∂_{a.swap} ∂_b H` composed with `K` (`Slp.compose`, sign
  `hamSign a`), `X_N = (DX_H ∘ K) N - DN`, the block `Nᵀ (Ω₀ X_N)`;
* the border column `(s ω)_a` (`freqModel`), the last row `(∂_a H ∘ K) N` and the corner `0`.

Product keys `[4, t, i, j, k]` (`t = 0, …, 10`). Contract: `torsionModels_sound`. This module
also re-exports the averaging check (`Torsion/Average`: `torsionAvgCheck`, its contracts).
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

section Defs

variable {α : Type} [CertArith α]

/-- A list matrix from an entry function (`r` rows, `c` columns). -/
def buildMat (r c : ℕ) (f : ℕ → ℕ → CertModel α) : ModelMatrix α :=
  (List.range r).map fun i => (List.range c).map fun j => f i j

/-- Exact negation of a model. -/
def CertModel.negM (a : CertModel α) : CertModel α := ⟨a.deg, a.poly.negP, a.rad⟩

/-- The product `A B` of model matrices (`r × m` times `m × c`): every entry is a balanced sum
of products at the keys `key ++ [i, j, k]`, re-expressed at degree `0`. -/
def modelMatMul (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (key : ProductKey)
    (r m c : ℕ) (A B : ModelMatrix α) : ModelMatrix α :=
  buildMat r c fun i j => CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m =>
    CertModel.mul W cfg (key ++ [i, j, k.val]) (modelMatrixEntry A i k.val)
      (modelMatrixEntry B k.val j)))

/-- The entrywise sum of model matrices. -/
def modelMatAdd (W : CertWeight) (pe : PiEnclosure α) (r c : ℕ) (A B : ModelMatrix α) :
    ModelMatrix α :=
  buildMat r c fun i j => CertModel.addMixed W pe (modelMatrixEntry A i j) (modelMatrixEntry B i j)

/-- The entrywise negation of a model matrix. -/
def modelMatNeg (r c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat r c fun i j => (modelMatrixEntry A i j).negM

/-- The transpose of an `r × c` model matrix. -/
def modelMatTranspose (r c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat c r fun i j => modelMatrixEntry A j i

/-- `Ω₀` applied to the rows of a `2n × c` model matrix: row `i < n` is minus row `n + i`, row
`n + i` is row `i`. -/
def modelMatOmega (n c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat (n + n) c fun i j =>
    if i < n then (modelMatrixEntry A (n + i) j).negM else modelMatrixEntry A (i - n) j

/-- The model of a constant `x` with `|x - c| ≤ r` (rational centre and radius). -/
def ballModel (n : ℕ) (c r : ℚ) : CertModel α :=
  ⟨0, (constModel n c 0 0 : CertModel α).poly,
    upAdd (constModel n c 0 0 : CertModel α).rad (ofRatUp r)⟩

/-- The model of the coordinate `l` of `s ω`, for every `ω` in the box. -/
def freqModel (n : ℕ) (box : FreqBox) (s : ℚ) (l : ℕ) : CertModel α :=
  ballModel n (s * (box.getD l (0, 0)).1) (|s| * (box.getD l (0, 0)).2)

/-- `L = DK` (`2n × n`): the angle rows, then the action rows. -/
def dkModels (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) :
    ModelMatrix α :=
  buildMat (n + n) n fun i j =>
    if i < n then dkAngleModel n K W pe i j else dkActionModel n K W pe (i - n) j

/-- The second partial `∂_l L_{ij}` at degree `0`. -/
def d2kModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (i j l : ℕ) : CertModel α :=
  if i < n then
    CertModel.toDeg W pe 0 (CertModel.ofDeriv2 W j l (K.angleDeg.getD i 0)
      (realCompPoly n K.angle[i]?))
  else
    CertModel.toDeg W pe 0 (CertModel.ofDeriv2 W j l (K.actionDeg.getD (i - n) 0)
      (realCompPoly n K.action[i - n]?))

/-- `D_{sω} L = Σ_l (sω)_l ∂_l L` (`2n × n`) for every `ω` in the box (scalar products: the
frequency factor is a constant model). -/
def dkwModels (n : ℕ) (K : CertEmbedding α) (box : FreqBox) (s : ℚ) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) : ModelMatrix α :=
  buildMat (n + n) n fun i j => CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun l : Fin n =>
    CertModel.mul W cfg [4, 10, i, j, l.val] (freqModel n box s l.val)
      (d2kModel n K W pe i j l.val)))

/-- The radius `δβ/(1 - δ)` of `G⁻¹ - B`, rounded upward (`none` unless `0 ≤ δ < 1`, `0 ≤ β`). -/
def gramInvRadius (δβ : α × α) : Option α :=
  if ble (ofInt 0) δβ.1 && ble (ofInt 0) δβ.2 && blt δβ.1 (ofInt 1) then
    (recipOneSubUp δβ.1).map fun t => upMul (upMul δβ.1 δβ.2) t
  else none

/-- `G⁻¹` (`n × n`): the witness `B` with the certified radius `eps`. -/
def gramInvModels (n : ℕ) (B : List (List (CertPoly α))) (eps : α) : ModelMatrix α :=
  buildMat n n fun k j => ⟨0, gramInvPoly B k j, eps⟩

/-- The jet slots read by the torsion: `∂_a H` (`a < 2n`), then `∂_a ∂_b H` (row-major,
`a, b < 2n`). -/
def torsionSlots (n : ℕ) (J : HamJet) : List ℕ :=
  (List.range (n + n)).map (fun a => J.d1.getD a 0) ++
    List.ofFn fun q : Fin ((n + n) * (n + n)) =>
      (J.d2.getD (q.val / (n + n)) []).getD (q.val % (n + n)) 0

/-- The phase index of the swapped coordinate: `a ↦ a + n` (`a < n`), `a ↦ a - n` otherwise. -/
def swapNat (n a : ℕ) : ℕ := if a < n then a + n else a - n

/-- `DX_H ∘ K` (`2n × 2n`): entry `(a, b)` is `± ∂_{a'} ∂_b H ∘ K` with `a' = swapNat n a`,
sign `+` for `a < n` (`hamSign`). -/
def dxhModels (n : ℕ) (ms : List (CertModel α)) : ModelMatrix α :=
  buildMat (n + n) (n + n) fun a b =>
    if a < n then ms.getD (n + n + (n + n) * swapNat n a + b) zeroModel
    else (ms.getD (n + n + (n + n) * swapNat n a + b) zeroModel).negM

/-- The row `∂_a H ∘ K` (`1 × 2n`). -/
def d1Models (n : ℕ) (ms : List (CertModel α)) : ModelMatrix α :=
  buildMat 1 (n + n) fun _ a => ms.getD a zeroModel

/-- Entrywise models of `extendedTorsion H K (s ω)` on `T_ρ` for EVERY `ω` in the box: the block
`torsion` from `DX_H ∘ K` (jet `d2` composed with `K`), the normal frame `N = Ω₀ DK B` with the
Gram witness `B` and the certified radius `δβ/(1 - δ)`, `DN[sω] = Ω₀ (D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])`
with `D(G⁻¹)[sω] = -G⁻¹ (DG[sω]) G⁻¹`; the border column `s ω` from the box (ball); the last row
`DH(K) N` (jet `d1` composed with `K`). -/
def torsionModels {α : Type} [CertArith α] (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (δβ : α × α) (box : FreqBox) (s : ℚ)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) : Option (ModelMatrix α) :=
  match gramInvRadius δβ, Slp.compose n e.jet.prog K wit W cfg pe (torsionSlots n e.jet) with
  | some eps, some ms =>
    let L := dkModels n K W pe
    let Gi := gramInvModels n Binv eps
    let DL := dkwModels n K box s W cfg pe
    let N := modelMatOmega n n (modelMatMul W cfg pe [4, 0] (n + n) n n L Gi)
    let DG := modelMatAdd W pe n n
      (modelMatMul W cfg pe [4, 1] n (n + n) n (modelMatTranspose (n + n) n DL) L)
      (modelMatMul W cfg pe [4, 2] n (n + n) n (modelMatTranspose (n + n) n L) DL)
    let DGi := modelMatNeg n n
      (modelMatMul W cfg pe [4, 4] n n n (modelMatMul W cfg pe [4, 3] n n n Gi DG) Gi)
    let DN := modelMatOmega n n (modelMatAdd W pe (n + n) n
      (modelMatMul W cfg pe [4, 5] (n + n) n n DL Gi)
      (modelMatMul W cfg pe [4, 6] (n + n) n n L DGi))
    let XN := modelMatAdd W pe (n + n) n
      (modelMatMul W cfg pe [4, 7] (n + n) (n + n) n (dxhModels n ms) N) (modelMatNeg (n + n) n DN)
    let Tb := modelMatMul W cfg pe [4, 8] n (n + n) n (modelMatTranspose (n + n) n N)
      (modelMatOmega n n XN)
    let Y := modelMatMul W cfg pe [4, 9] 1 (n + n) n (d1Models n ms) N
    some (buildMat (n + 1) (n + 1) fun i j =>
      if i < n then (if j < n then modelMatrixEntry Tb i j else freqModel n box s i)
      else (if j < n then modelMatrixEntry Y 0 j else zeroModel))
  | _, _ => none

end Defs

/-! ### Model matrices: entries and enclosures -/

section Generic

variable {α : Type} [CertArith α]

theorem buildMat_entry {r c : ℕ} (f : ℕ → ℕ → CertModel α) {i j : ℕ} (hi : i < r) (hj : j < c) :
    modelMatrixEntry (buildMat r c f) i j = f i j := by
  simp [modelMatrixEntry, buildMat, hi, hj]

omit [CertArith α] in
theorem buildMat_lookup {r c : ℕ} (f : ℕ → ℕ → CertModel α) {i j : ℕ} (hi : i < r)
    (hj : j < c) : ((buildMat r c f)[i]?.bind fun row => row[j]?) = some (f i j) := by
  simp [buildMat, hi, hj]

omit [CertArith α] in
theorem buildMat_hasShape (k : ℕ) (f : ℕ → ℕ → CertModel α) :
    ModelMatrix.HasShape k (buildMat k k f) := by
  refine ⟨by simp [buildMat], fun row hrow => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Entrywise enclosure of a matrix-valued function through `modelMatrixEntry` (row and column
index maps `ri`, `ci`). -/
def ModelMatrix.EntryEncloses (n : ℕ) (ρ : ℝ) {ι κ : Type*} (ri : ι → ℕ) (ci : κ → ℕ)
    (M : ModelMatrix α) (F : (Fin n → ℂ) → Matrix ι κ ℂ) : Prop :=
  ∀ i j, (modelMatrixEntry M (ri i) (ci j)).Encloses n ρ (fun θ => F θ i j)

theorem phaseNat_finSumFinEquiv_symm {n : ℕ} (k : Fin (n + n)) :
    phaseNat (finSumFinEquiv.symm k) = k.val := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective k
  rw [Equiv.symm_apply_apply]
  rcases x with x | x <;> simp [phaseNat, add_comm]

theorem phaseNat_lt_add {n : ℕ} (a : Fin n ⊕ Fin n) : phaseNat a < n + n := by
  rcases a with a | a <;> simp only [phaseNat] <;> omega

variable [LawfulCertArith α]

omit [LawfulCertArith α] in
theorem CertModel.Encloses.of_eqOn {n : ℕ} {ρ : ℝ} {m : CertModel α} {f g : (Fin n → ℂ) → ℂ}
    (h : m.Encloses n ρ f) (hfg : ∀ θ ∈ complexStrip n ρ, f θ = g θ) : m.Encloses n ρ g :=
  fun θ hθ => by rw [← hfg θ hθ]; exact h θ hθ

theorem CertModel.Encloses.negM {n : ℕ} {ρ : ℝ} {a : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (h : a.Encloses n ρ f) : a.negM.Encloses n ρ (fun θ => -f θ) := by
  intro θ hθ
  have := h θ hθ
  simp only [CertModel.negM, CertPoly.eval_negP]
  rw [show -f θ - (2 * (Real.pi : ℂ)) ^ a.deg * -a.poly.eval n θ =
    -(f θ - (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.eval n θ) by ring, norm_neg]
  exact this

variable {n : ℕ} {W : CertWeight} {s N : ℕ} {pe : PiEnclosure α} {ι κ μ : Type*}
  {ri : ι → ℕ} {ci : κ → ℕ}

theorem ModelMatrix.EntryEncloses.modelMul [Fintype μ] (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) (hpe : checkPiEnclosure pe = true) (key : ProductKey) {r m c : ℕ}
    (hri : ∀ i, ri i < r) (hci : ∀ j, ci j < c) {mi : μ → ℕ} (e : Fin m ≃ μ)
    (he : ∀ k, mi (e k) = k.val) {A B : ModelMatrix α} {FA : (Fin n → ℂ) → Matrix ι μ ℂ}
    {FB : (Fin n → ℂ) → Matrix μ κ ℂ} (hA : A.EntryEncloses n W.rho ri mi FA)
    (hB : B.EntryEncloses n W.rho mi ci FB) :
    (modelMatMul W cfg pe key r m c A B).EntryEncloses n W.rho ri ci
      (fun θ => FA θ * FB θ) := by
  intro i j
  rw [modelMatMul, buildMat_entry _ (hri i) (hci j)]
  let L : EnclosedList α n := List.ofFn fun k : Fin m =>
    (CertModel.mul W cfg (key ++ [ri i, ci j, k.val]) (modelMatrixEntry A (ri i) k.val)
      (modelMatrixEntry B k.val (ci j)), fun θ => FA θ i (e k) * FB θ (e k) j)
  have hL : ∀ p ∈ L, p.1.Encloses n W.rho p.2 := by
    intro p hp
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hp
    have h1 := hA i (e k)
    have h2 := hB (e k) j
    rw [he] at h1 h2
    exact CertModel.Encloses.mul hW cfg _ h1 h2
  have := (modelSum_encloses hW hpe L hL).toDeg hW hpe 0
  have hfst : L.map Prod.fst = List.ofFn fun k : Fin m =>
      CertModel.mul W cfg (key ++ [ri i, ci j, k.val]) (modelMatrixEntry A (ri i) k.val)
        (modelMatrixEntry B k.val (ci j)) := by
    simp only [L, List.map_ofFn]
    rfl
  rw [hfst] at this
  refine this.of_eq_fun fun θ => ?_
  simp only [L, List.map_ofFn, List.sum_ofFn, Function.comp_def, Matrix.mul_apply]
  exact e.sum_comp (fun k => FA θ i k * FB θ k j)

theorem ModelMatrix.EntryEncloses.modelAdd (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) {r c : ℕ} (hri : ∀ i, ri i < r) (hci : ∀ j, ci j < c)
    {A B : ModelMatrix α} {FA FB : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : A.EntryEncloses n W.rho ri ci FA) (hB : B.EntryEncloses n W.rho ri ci FB) :
    (modelMatAdd W pe r c A B).EntryEncloses n W.rho ri ci (fun θ => FA θ + FB θ) := by
  intro i j
  rw [modelMatAdd, buildMat_entry _ (hri i) (hci j)]
  exact ((hA i j).addMixed hW hpe (hB i j)).of_eq_fun fun θ => by simp [Matrix.add_apply]

theorem ModelMatrix.EntryEncloses.modelNeg {ρ : ℝ} {r c : ℕ} (hri : ∀ i, ri i < r)
    (hci : ∀ j, ci j < c) {A : ModelMatrix α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : A.EntryEncloses n ρ ri ci F) :
    (modelMatNeg r c A).EntryEncloses n ρ ri ci (fun θ => -F θ) := by
  intro i j
  rw [modelMatNeg, buildMat_entry _ (hri i) (hci j)]
  exact (hA i j).negM.of_eq_fun fun θ => by simp

omit [LawfulCertArith α] in
theorem ModelMatrix.EntryEncloses.modelTranspose {ρ : ℝ} {r c : ℕ} (hri : ∀ i, ri i < r)
    (hci : ∀ j, ci j < c) {A : ModelMatrix α} {F : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hA : A.EntryEncloses n ρ ri ci F) :
    (modelMatTranspose r c A).EntryEncloses n ρ ci ri (fun θ => (F θ)ᵀ) := by
  intro j i
  rw [modelMatTranspose, buildMat_entry _ (hci j) (hri i)]
  exact hA i j

theorem ModelMatrix.EntryEncloses.modelOmega {ρ : ℝ} [Fintype κ] {c : ℕ} (hci : ∀ j, ci j < c)
    {A : ModelMatrix α} {F : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) κ ℂ}
    (hA : A.EntryEncloses n ρ phaseNat ci F) :
    (modelMatOmega n c A).EntryEncloses n ρ phaseNat ci (fun θ => omegaZeroMatrix n * F θ) := by
  rintro (i | i) j
  · rw [modelMatOmega, buildMat_entry _ (phaseNat_lt_add _) (hci j)]
    simp only [phaseNat, i.isLt, ↓reduceIte]
    exact (hA (Sum.inr i) j).negM.of_eq_fun fun θ => by rw [omegaZeroMatrix_mul_apply_inl]
  · rw [modelMatOmega, buildMat_entry _ (phaseNat_lt_add _) (hci j)]
    have : ¬(n + i.val < n) := by omega
    simp only [phaseNat, this, ↓reduceIte, Nat.add_sub_cancel_left]
    exact (hA (Sum.inl i) j).of_eq_fun fun θ => by rw [omegaZeroMatrix_mul_apply_inr]

end Generic

/-! ### The base models -/

section Base

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {s N : ℕ}
  {pe : PiEnclosure α}

theorem dkModels_encloses (hW : checkWeight W s N = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) :
    (dkModels n K W pe).EntryEncloses n W.rho phaseNat Fin.val (tangentMat (K.eval n)) := by
  rintro (i | i) j
  · rw [dkModels, buildMat_entry _ (phaseNat_lt_add _) j.isLt]
    simp only [phaseNat, i.isLt, ↓reduceIte]
    exact (dkAngleModel_encloses hW hpe K i j).of_eq_fun fun θ => by
      rw [tangentMat_apply, sumVec_apply, Sum.elim_inl]
  · rw [dkModels, buildMat_entry _ (phaseNat_lt_add _) j.isLt]
    have : ¬(n + i.val < n) := by omega
    simp only [phaseNat, this, ↓reduceIte, Nat.add_sub_cancel_left]
    exact (dkActionModel_encloses hW hpe K i j).of_eq_fun fun θ => by
      rw [tangentMat_apply, sumVec_apply, Sum.elim_inr]

omit [LawfulCertArith α] in
theorem gramInvModels_encloses {ρ : ℝ} (B : List (List (CertPoly α))) {eps : α}
    {F : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ θ ∈ complexStrip n ρ, ‖F θ - polyMatrix n B θ‖ ≤ val eps) :
    (gramInvModels n B eps).EntryEncloses n ρ Fin.val Fin.val F := by
  intro k j θ hθ
  rw [gramInvModels, buildMat_entry _ k.isLt j.isLt]
  have := (norm_entry_le (F θ - polyMatrix n B θ) k j).trans (h θ hθ)
  rw [Matrix.sub_apply, polyMatrix_apply] at this
  simpa using this

theorem gramInvRadius_spec {δβ : α × α} {eps : α} (h : gramInvRadius δβ = some eps) :
    val δβ.1 * val δβ.2 / (1 - val δβ.1) ≤ val eps := by
  unfold gramInvRadius at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, h2⟩ := hc
  have hδ0 := LawfulCertArith.ble_sound _ _ h0
  have hβ0 := LawfulCertArith.ble_sound _ _ h1
  have hδ1 := LawfulCertArith.blt_sound _ _ h2
  rw [LawfulCertArith.val_ofInt, Int.cast_zero] at hδ0 hβ0
  rw [LawfulCertArith.val_ofInt, Int.cast_one] at hδ1
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  have hti := recipOneSubUp_ge ht hδ0 hδ1
  have hpos : 0 < 1 - val δβ.1 := by linarith
  have ht0 : 0 ≤ val t := le_trans (by positivity) hti
  have hm1 := LawfulCertArith.upMul_ge δβ.1 δβ.2 hδ0 hβ0
  have hm0 : 0 ≤ val (upMul δβ.1 δβ.2) := le_trans (mul_nonneg hδ0 hβ0) hm1
  have hm2 := LawfulCertArith.upMul_ge (upMul δβ.1 δβ.2) t hm0 ht0
  calc val δβ.1 * val δβ.2 / (1 - val δβ.1) = val δβ.1 * val δβ.2 * (1 / (1 - val δβ.1)) := by
        ring
    _ ≤ val (upMul δβ.1 δβ.2) * val t := mul_le_mul hm1 hti (by positivity) hm0
    _ ≤ _ := hm2

theorem freqModel_encloses {ρ : ℝ} {box : FreqBox} {ω : Fin n → ℝ} (hω : FreqEncloses n box ω)
    (sc : ℚ) (l : Fin n) :
    (freqModel n box sc l.val : CertModel α).Encloses n ρ
      (fun _ => ((((sc : ℝ) • ω) l : ℝ) : ℂ)) := by
  intro θ hθ
  set c := (box.getD l.val (0, 0)).1
  set r := (box.getD l.val (0, 0)).2
  have hc := constModel_encloses (α := α) n ρ (sc * c) 0 0 θ hθ
  have hdeg : (constModel n (sc * c) 0 0 : CertModel α).deg = 0 := rfl
  rw [hdeg] at hc
  simp only [slpConstVal, zpow_zero, mul_one, one_mul, Rat.cast_zero, zero_mul, add_zero]
    at hc
  have hb := hω l
  have hr := LawfulCertArith.ofRatUp_ge (α := α) (|sc| * r)
  have hu := LawfulCertArith.upAdd_ge (constModel n (sc * c) 0 0 : CertModel α).rad
    (ofRatUp (|sc| * r))
  simp only [freqModel, ballModel, zpow_zero, one_mul]
  have hx : ‖(((((sc : ℝ) • ω) l : ℝ) : ℂ)) - ((sc * c : ℚ) : ℂ)‖ ≤ ((|sc| * r : ℚ) : ℝ) := by
    rw [show ((((sc : ℝ) • ω) l : ℝ) : ℂ) - ((sc * c : ℚ) : ℂ) =
      (((sc : ℝ) * (ω l - (c : ℝ)) : ℝ) : ℂ) by push_cast; simp; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  calc _ ≤ ‖(((((sc : ℝ) • ω) l : ℝ) : ℂ)) - ((sc * c : ℚ) : ℂ)‖ +
        ‖((sc * c : ℚ) : ℂ) - (constModel n (sc * c) 0 0 : CertModel α).poly.eval n θ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

theorem d2kModel_encloses (hW : checkWeight W s N = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) (x : Fin n ⊕ Fin n) (j l : Fin n) :
    (d2kModel n K W pe (phaseNat x) j.val l.val).Encloses n W.rho
      (fun θ => fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1)) := by
  rcases x with i | i
  · simp only [d2kModel, phaseNat, i.isLt, ↓reduceIte]
    exact ((CertModel.Encloses.ofDeriv2 hW j l _ _).toDeg hW hpe 0).of_eq_fun
      fun θ => (fderiv_tangentMat_eval_inl K θ i j l).symm
  · have : ¬(n + i.val < n) := by omega
    simp only [d2kModel, phaseNat, this, ↓reduceIte, Nat.add_sub_cancel_left]
    exact ((CertModel.Encloses.ofDeriv2 hW j l _ _).toDeg hW hpe 0).of_eq_fun
      fun θ => (fderiv_tangentMat_eval_inr K θ i j l).symm

theorem dkwModels_encloses (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    (hpe : checkPiEnclosure pe = true) (K : CertEmbedding α) {box : FreqBox} {ω : Fin n → ℝ}
    (hω : FreqEncloses n box ω) (sc : ℚ) :
    (dkwModels n K box sc W cfg pe).EntryEncloses n W.rho phaseNat Fin.val
      (fun θ => fderiv ℂ (tangentMat (K.eval n)) θ (fun l => ((((sc : ℝ) • ω) l : ℝ) : ℂ))) := by
  intro x j
  rw [dkwModels, buildMat_entry _ (phaseNat_lt_add _) j.isLt]
  let L : EnclosedList α n := List.ofFn fun l : Fin n =>
    (CertModel.mul W cfg [4, 10, phaseNat x, j.val, l.val] (freqModel n box sc l.val)
      (d2kModel n K W pe (phaseNat x) j.val l.val),
     fun θ => ((((sc : ℝ) • ω) l : ℝ) : ℂ) *
      fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1))
  have hL : ∀ p ∈ L, p.1.Encloses n W.rho p.2 := by
    intro p hp
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hp
    exact CertModel.Encloses.mul hW cfg _ (freqModel_encloses hω sc l)
      (d2kModel_encloses hW hpe K x j l)
  have := (modelSum_encloses hW hpe L hL).toDeg hW hpe 0
  have hfst : L.map Prod.fst = List.ofFn fun l : Fin n =>
      CertModel.mul W cfg [4, 10, phaseNat x, j.val, l.val] (freqModel n box sc l.val)
        (d2kModel n K W pe (phaseNat x) j.val l.val) := by
    simp only [L, List.map_ofFn]
    rfl
  rw [hfst] at this
  refine this.of_eqOn fun θ hθ => ?_
  have hLd := differentiableOn_tangentMat (r := W.rho) (K.differentiable_eval n).differentiableOn
  beta_reduce
  rw [fderiv_tangentMat_eq_sum_partials
    (hLd.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ))]
  simp only [L, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-! #### The jet slots -/

theorem torsionSlots_length (J : HamJet) :
    (torsionSlots n J).length = n + n + (n + n) * (n + n) := by
  simp [torsionSlots]

theorem torsionSlots_getD_d1 (J : HamJet) {a : ℕ} (ha : a < n + n) :
    (torsionSlots n J).getD a 0 = J.d1.getD a 0 := by
  rw [torsionSlots, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ha)]
  simp [ha]

theorem torsionSlots_getD_d2 (J : HamJet) {a b : ℕ} (ha : a < n + n) (hb : b < n + n) :
    (torsionSlots n J).getD (n + n + (n + n) * a + b) 0 = (J.d2.getD a []).getD b 0 := by
  have hq : (n + n) * a + b < (n + n) * (n + n) := by nlinarith
  rw [torsionSlots, add_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left, List.getElem?_ofFn, hq]
  have hpos : 0 < n + n := by omega
  rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  simp

theorem swapNat_phaseNat (a : Fin n ⊕ Fin n) : swapNat n (phaseNat a) = phaseNat a.swap := by
  rcases a with a | a
  · simp [swapNat, phaseNat, add_comm]
  · have : ¬(n + a.val < n) := by omega
    simp [swapNat, phaseNat, this]

omit [LawfulCertArith α] in
/-- The composed jet slots enclose the derivatives of `H` along `K` (the contract of
`Slp.compose`, read through `torsionSlots`). -/
def SlotsEnclose (n : ℕ) (e : HamExpr n) (K : CertEmbedding α) (ρ : ℝ)
    (ms : List (CertModel α)) : Prop :=
  ms.length = (torsionSlots n e.jet).length ∧ ∀ idx (h : idx < ms.length), ms[idx].Encloses n ρ
    (fun θ => e.jet.prog.val n (K.eval n θ) ((torsionSlots n e.jet).getD idx 0))

theorem dxhModels_encloses {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {ρ : ℝ}
    (hKD : ∀ θ ∈ complexStrip n ρ, K.eval n θ ∈ D) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K ρ ms) :
    (dxhModels n ms).EntryEncloses n ρ phaseNat phaseNat (linMat e.eval (K.eval n)) := by
  have hslot : ∀ a b : Fin n ⊕ Fin n,
      (ms.getD (n + n + (n + n) * swapNat n (phaseNat a) + phaseNat b) zeroModel).Encloses n ρ
        (fun θ => iteratedFDeriv ℂ 2 e.eval (K.eval n θ) ![phaseBasis a.swap, phaseBasis b]) := by
    intro a b
    have ha := phaseNat_lt_add a.swap
    have hb := phaseNat_lt_add b
    rw [swapNat_phaseNat]
    have hq : n + n + (n + n) * phaseNat a.swap + phaseNat b < ms.length := by
      rw [hms.1, torsionSlots_length]; nlinarith
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    refine (hms.2 _ hq).of_eqOn fun θ hθ => ?_
    rw [torsionSlots_getD_d2 _ ha hb]
    exact e.jet_d2 hD hnv (hKD θ hθ) a.swap b
  intro a b
  rw [dxhModels, buildMat_entry _ (phaseNat_lt_add a) (phaseNat_lt_add b)]
  have hlin : ∀ θ ∈ complexStrip n ρ, linMat e.eval (K.eval n) θ a b = hamSign a *
      iteratedFDeriv ℂ 2 e.eval (K.eval n θ) ![phaseBasis a.swap, phaseBasis b] := fun θ hθ =>
    linMat_apply_eq (((e.contDiffOn_eval hD hnv).contDiffAt
      (hD.mem_nhds (hKD θ hθ))).of_le le_top) a b
  rcases a with i | i
  · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
    simp only [hlt, ↓reduceIte]
    exact (hslot (Sum.inl i) b).of_eqOn fun θ hθ => by rw [hlin θ hθ]; simp [hamSign]
  · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
    simp only [hlt, ↓reduceIte]
    exact (hslot (Sum.inr i) b).negM.of_eqOn fun θ hθ => by rw [hlin θ hθ]; simp [hamSign]

omit [LawfulCertArith α] in
theorem d1Models_encloses {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {ρ : ℝ}
    (hKD : ∀ θ ∈ complexStrip n ρ, K.eval n θ ∈ D) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K ρ ms) :
    (d1Models n ms).EntryEncloses n ρ (fun _ : Unit => 0) phaseNat
      (fun θ => Matrix.of fun _ a => fderiv ℂ e.eval (K.eval n θ) (phaseBasis a)) := by
  intro _ a
  rw [d1Models, buildMat_entry _ Nat.one_pos (phaseNat_lt_add a)]
  have ha := phaseNat_lt_add a
  have hq : phaseNat a < ms.length := by
    rw [hms.1, torsionSlots_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  refine (hms.2 _ hq).of_eqOn fun θ hθ => ?_
  rw [torsionSlots_getD_d1 _ ha, e.jet_d1 hD hnv (hKD θ hθ) a]
  rfl

end Base

/-! ### The producer contract -/

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- The torsion block of the frozen bordered torsion in the matrix form computed by the models:
`T = Nᵀ (Ω₀ X_N)`, `N = Ω₀ (L G⁻¹)`, `X_N = A N + -(Ω₀ (D L G⁻¹ + L D(G⁻¹)))`. -/
theorem torsion_eq_models {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ} (hK : Differentiable ℂ K)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) (ω : Fin n → ℝ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    torsion H K ω θ = (omegaZeroMatrix n * (tangentMat K θ * (gramMatrix K θ)⁻¹))ᵀ *
      (omegaZeroMatrix n * (linMat H K θ * (omegaZeroMatrix n * (tangentMat K θ *
        (gramMatrix K θ)⁻¹)) + -(omegaZeroMatrix n *
          (fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) * (gramMatrix K θ)⁻¹ +
            tangentMat K θ * -((gramMatrix K θ)⁻¹ *
              ((fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)))ᵀ * tangentMat K θ +
                (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ))) *
              (gramMatrix K θ)⁻¹))))) := by
  have hN := differentiableOn_normalMat (r := ρ) hK.differentiableOn hG
  rw [torsion_eq_mat H K ω (hN.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)),
    normalFieldMat, fderiv_normalMat_apply hK hG hθ, Matrix.mul_assoc, sub_eq_add_neg]
  simp only [normalMat, Matrix.mul_assoc]

/-- **Torsion producer contract.** Validated weight and `π`, a successful Gram
certificate (its `(δ, β)` passed on), successful construction, a frequency in the box, and `K`
mapping the strip into an open set where `e` has no vanishing denominator give the enclosure
of the LITERAL frozen `extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)`, and its continuity. -/
theorem torsionModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (cfg : ModelConfig α)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {σBμ : ℚ} {δβ : α × α}
    (hG : gramCheck n K Binv W cfg pe σBμ = some δβ) (box : FreqBox) (s : ℚ)
    {T : ModelMatrix α} (hT : torsionModels n e K wit Binv δβ box s W cfg pe = some T)
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) :
    ModelMatrix.HasShape (n + 1) T ∧ T.Encloses n (torsionIdx n) W.rho
        (KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)) ∧
      ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ a b)
        (complexStrip n W.rho) := by
  obtain ⟨-, hGs⟩ := gramCheck_sound hn K Binv hW cfg hpe σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  have hK := K.differentiable_eval n
  have hH : DifferentiableOn ℂ e.eval D := (e.contDiffOn_eval hD hnv).differentiableOn (by simp)
  unfold torsionModels at hT
  split at hT
  · rename_i eps ms heps hcomp
    dsimp only at hT
    obtain rfl := (Option.some.inj hT).symm
    have hms : SlotsEnclose n e K W.rho ms := by
      have := Slp.compose_sound e.jet.prog K wit hW cfg hpe _ hcomp
      exact ⟨this.1, this.2⟩
    -- the base models
    have hfin : ∀ j : Fin n, j.val < n := fun j => j.isLt
    have hL := dkModels_encloses (n := n) hW hpe K
    have hGi : (gramInvModels n Binv eps).EntryEncloses n W.rho Fin.val Fin.val
        (fun θ => (gramMatrix (K.eval n) θ)⁻¹) :=
      gramInvModels_encloses Binv fun θ hθ => (hGs θ hθ).2.2.trans (gramInvRadius_spec heps)
    have hDL := dkwModels_encloses hW cfg hpe K hω s
    have hA := dxhModels_encloses hD hnv hKD hms
    have hD1 := d1Models_encloses hD hnv hKD hms
    -- the products
    have he1 : ∀ k : Fin n, (Equiv.refl (Fin n) k).val = k.val := fun _ => rfl
    have hN := (hL.modelMul hW cfg hpe [4, 0] phaseNat_lt_add hfin (Equiv.refl _) he1
      hGi).modelOmega hfin
    have hDG := ((hDL.modelTranspose phaseNat_lt_add hfin).modelMul hW cfg hpe [4, 1] hfin
      hfin finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hL).modelAdd hW hpe hfin hfin
      ((hL.modelTranspose phaseNat_lt_add hfin).modelMul hW cfg hpe [4, 2] hfin hfin
        finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hDL)
    have hDGi := ((hGi.modelMul hW cfg hpe [4, 3] hfin hfin (Equiv.refl _) he1
      hDG).modelMul hW cfg hpe [4, 4] hfin hfin (Equiv.refl _) he1 hGi).modelNeg hfin hfin
    have hDN := ((hDL.modelMul hW cfg hpe [4, 5] phaseNat_lt_add hfin (Equiv.refl _) he1
      hGi).modelAdd hW hpe phaseNat_lt_add hfin
      (hL.modelMul hW cfg hpe [4, 6] phaseNat_lt_add hfin (Equiv.refl _) he1
        hDGi)).modelOmega hfin
    have hXN := (hA.modelMul hW cfg hpe [4, 7] phaseNat_lt_add hfin finSumFinEquiv.symm
      phaseNat_finSumFinEquiv_symm hN).modelAdd hW hpe phaseNat_lt_add hfin
      (hDN.modelNeg phaseNat_lt_add hfin)
    have hTb := (hN.modelTranspose phaseNat_lt_add hfin).modelMul hW cfg hpe [4, 8] hfin hfin
      finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm (hXN.modelOmega hfin)
    have hY := hD1.modelMul hW cfg hpe [4, 9] (r := 1) (fun _ => Nat.one_pos) hfin
      finSumFinEquiv.symm phaseNat_finSumFinEquiv_symm hN
    refine ⟨buildMat_hasShape _ _, ?_,
      fun a b => continuousOn_extendedTorsion hD hH hK hKD hGu _ a b⟩
    intro a b
    refine ⟨_, buildMat_lookup _ (torsionIdx_lt n a) (torsionIdx_lt n b), ?_⟩
    rcases a with i | _ <;> rcases b with j | _
    · simp only [torsionIdx, Sum.elim_inl, i.isLt, j.isLt, ↓reduceIte]
      refine (hTb i j).of_eqOn fun θ hθ => ?_
      show _ = torsion e.eval (K.eval n) ((s : ℝ) • ω) θ i j
      rw [torsion_eq_models hK hGu _ hθ]
    · simp only [torsionIdx, Sum.elim_inl, Sum.elim_inr, i.isLt, lt_irrefl, ↓reduceIte]
      exact freqModel_encloses hω s i
    · simp only [torsionIdx, Sum.elim_inl, Sum.elim_inr, j.isLt, lt_irrefl, ↓reduceIte]
      refine (hY () j).of_eqOn fun θ hθ => ?_
      show _ = fderiv ℂ e.eval (K.eval n θ) (normalFrame (K.eval n) θ j)
      rw [fderiv_apply_normalFrame]
      beta_reduce
      rw [Matrix.mul_apply]
      simp only [normalMat, Matrix.mul_assoc, Matrix.of_apply]
    · simp only [torsionIdx, Sum.elim_inr, lt_irrefl, ↓reduceIte]
      exact zeroModel_encloses n _
  · simp at hT

end Sound

end KAM.Certificate

end
