/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Linear
public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Fixed
public import KAM.Certificate.Freq
public import KAM.Certificate.DiophantineTransfer
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The shear of two degrees of freedom on certificate data

The linear symplectic unimodular change of variables of the lunar client
`shearMap ((Q₀, Q₁), (P₀, P₁)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))` (angle block
`S = [[1, 1], [0, 1]]`, action block `S⁻ᵀ`), with its continuous linear equivalence `shearCLE`
(`shearCLE_isSymplectic`), and the angle change `A = S⁻¹` (`angleCLE`,
`A (θ₀, θ₁) = (θ₀ - θ₁, θ₁)`).
`invarianceError_shear` is `invarianceError_comp` at this pair.

On the certificate's data the change of variables is computed exactly:
* `hamShear`: the expression of `H ∘ shearMap` (`eval_hamShear`): modes `k ↦ shearKey k =
  (k₀, k₀ + k₁)`, the action `P₁ ↦ P₁ - P₀`;
* `polyShear` (keys `k ↦ shearKey k`): `(polyShear P)(φ) = P(S φ)` (`eval_polyShear`), and
  `polyAdd` (the key-sorted merge `addTerms` of the half lists, `CertFixed` mantissas added
  exactly): `eval_polyAdd`;
* `embShear`: for an embedding of the form `⟨[d₀, d₁], [U, 0], [e, e], [P₀, P₁]⟩`, the data of
  `shearMap⁻¹ ∘ K ∘ S` (`eval_embShear`);
* `shearBox`: the box of `(ω₀ - ω₁, ω₁)` (`freqEncloses_shear`), and the Diophantine transfer
  `isDiophantine_shear` (constant `γ / 2^τ`);
* `norm_shearMap_le`, `norm_shearMapInv_le` (both `≤ 2`), `shearAngle_mem_complexStrip`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Linear

open KAM KAM.Certificate

/-! ### The linear maps -/

/-- The angle block `S (θ₀, θ₁) = (θ₀ + θ₁, θ₁)` of `shearMap`. -/
def shearAngle (θ : Fin 2 → ℂ) : Fin 2 → ℂ := ![θ 0 + θ 1, θ 1]

/-- Its inverse `A (θ₀, θ₁) = (θ₀ - θ₁, θ₁)`. -/
def shearAngleInv (θ : Fin 2 → ℂ) : Fin 2 → ℂ := ![θ 0 - θ 1, θ 1]

/-- The change of variables `((Q₀, Q₁), (P₀, P₁)) ↦ ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))` (the lunar
client's `soRotMap`). -/
def shearMap (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (shearAngle z.1, ![z.2 0, z.2 1 - z.2 0])

/-- Its inverse `((q, φ), (p, J)) ↦ ((q - φ, φ), (p, p + J))`. -/
def shearMapInv (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (shearAngleInv z.1, ![z.2 0, z.2 0 + z.2 1])

/-- `shearMap` as a continuous linear equivalence. -/
def shearCLE : ((Fin 2 → ℂ) × (Fin 2 → ℂ)) ≃L[ℂ] ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := shearMap
      invFun := shearMapInv
      map_add' := fun u v => by
        refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [shearMap, shearAngle] <;> ring
      map_smul' := fun c u => by
        refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [shearMap, shearAngle] <;> ring
      left_inv := fun z => by
        refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
          simp [shearMap, shearMapInv, shearAngle, shearAngleInv]
      right_inv := fun z => by
        refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
          simp [shearMap, shearMapInv, shearAngle, shearAngleInv] }

/-- The angle change `A = S⁻¹` as a continuous linear equivalence (`A.symm = S`). -/
def angleCLE : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := shearAngleInv
      invFun := shearAngle
      map_add' := fun u v => by ext i; fin_cases i <;> simp [shearAngleInv]; ring
      map_smul' := fun c u => by ext i; fin_cases i <;> simp [shearAngleInv]; ring
      left_inv := fun z => by ext i; fin_cases i <;> simp [shearAngle, shearAngleInv]
      right_inv := fun z => by ext i; fin_cases i <;> simp [shearAngle, shearAngleInv] }

@[simp] theorem coe_shearCLE : ⇑shearCLE = shearMap := rfl

@[simp] theorem coe_shearCLE_symm : ⇑shearCLE.symm = shearMapInv := rfl

@[simp] theorem coe_angleCLE : ⇑angleCLE = shearAngleInv := rfl

@[simp] theorem coe_angleCLE_symm : ⇑angleCLE.symm = shearAngle := rfl

/-- `shearMap` preserves the symplectic pairing (`Sᵀ S⁻ᵀ = I`). -/
theorem shearMap_isSymplectic : IsSymplectic shearMap := by
  intro u v
  simp only [symplecticPairing, Fin.sum_univ_two, shearMap, shearAngle]
  simp
  ring

theorem shearCLE_isSymplectic : IsSymplectic shearCLE := by
  rw [coe_shearCLE]; exact shearMap_isSymplectic

/-- **The invariance error in the sheared variables**:
`E(H ∘ shearMap, shearMap⁻¹ ∘ K ∘ S, (ω₀ - ω₁, ω₁))(θ) = shearMap⁻¹ E(H, K, ω)(S θ)`. -/
theorem invarianceError_shear (H : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (ω : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    invarianceError (H ∘ shearMap) (shearMapInv ∘ K ∘ shearAngle) ![ω 0 - ω 1, ω 1] θ =
      shearMapInv (invarianceError H K ω (shearAngle θ)) := by
  have hω : (fun i => ((![ω 0 - ω 1, ω 1] : Fin 2 → ℝ) i : ℂ)) =
      angleCLE fun i => (ω i : ℂ) := by
    ext i; fin_cases i <;> simp [shearAngleInv]
  have h := invarianceError_comp shearCLE_isSymplectic angleCLE H K hω θ
  simp only [coe_shearCLE, coe_shearCLE_symm, coe_angleCLE_symm] at h
  exact h

/-- The same identity read backwards: a torus `K'` of `H ∘ shearMap` at `(ω₀ - ω₁, ω₁)` gives
the torus `shearMap ∘ K' ∘ A` of `H` at `ω`. -/
theorem invarianceError_shear_symm (H : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (K' : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (ω : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    invarianceError H (shearMap ∘ K' ∘ shearAngleInv) ω θ =
      shearMap (invarianceError (H ∘ shearMap) K' ![ω 0 - ω 1, ω 1] (shearAngleInv θ)) := by
  have hω : (fun i => ((![ω 0 - ω 1, ω 1] : Fin 2 → ℝ) i : ℂ)) =
      angleCLE fun i => (ω i : ℂ) := by
    ext i; fin_cases i <;> simp [shearAngleInv]
  have h := invarianceError_comp_symm shearCLE_isSymplectic angleCLE H K' hω θ
  simp only [coe_shearCLE, coe_angleCLE] at h
  exact h

/-! ### Keys and Hamiltonian expressions -/

/-- The sheared Fourier index `k ↦ Sᵀ k = (k₀, k₀ + k₁)`: `shearKey k · θ = k · S θ`. -/
def shearKey (k : CertKey) : CertKey := [k.getD 0 0, k.getD 0 0 + k.getD 1 0]

theorem sum_shearKey (k : CertKey) (θ : Fin 2 → ℂ) :
    ∑ j, (certKeyFun 2 (shearKey k) j : ℂ) * θ j =
      ∑ j, (certKeyFun 2 k j : ℂ) * shearAngle θ j := by
  simp [Fin.sum_univ_two, certKeyFun, shearKey, shearAngle]
  ring

theorem character_shearKey (k : CertKey) (θ : Fin 2 → ℂ) :
    character (certKeyFun 2 (shearKey k)) θ = character (certKeyFun 2 k) (shearAngle θ) := by
  simp only [character, sum_shearKey]

theorem character_neg_shearKey (k : CertKey) (θ : Fin 2 → ℂ) :
    character (-certKeyFun 2 (shearKey k)) θ = character (-certKeyFun 2 k) (shearAngle θ) := by
  have h := sum_shearKey k θ
  simp only [character, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, h]

/-- The expression of `H ∘ shearMap`: modes `k ↦ shearKey k`, the action `P₁ ↦ P₁ - P₀`. -/
def hamShear : HamExpr 2 → HamExpr 2
  | .action j => if j.val = 0 then .action j else .add (.action j) (.mul (.const (-1)) (.action 0))
  | .cosMode k => .cosMode (shearKey k)
  | .sinMode k => .sinMode (shearKey k)
  | .add a b => .add (hamShear a) (hamShear b)
  | .mul a b => .mul (hamShear a) (hamShear b)
  | .div a b => .div (hamShear a) (hamShear b)
  | .pow a m => .pow (hamShear a) m
  | .exp a => .exp (hamShear a)
  | .sin a => .sin (hamShear a)
  | .cos a => .cos (hamShear a)
  | .sqrt a => .sqrt (hamShear a)
  | .const q => .const q
  | .pi => .pi

theorem modePhase_shearKey (k : CertKey) (θ : Fin 2 → ℂ) :
    modePhase 2 (shearKey k) θ = modePhase 2 k (shearAngle θ) := by
  simp only [modePhase, sum_shearKey]

/-- **The sheared expression denotes `H ∘ shearMap`.** -/
theorem eval_hamShear (e : HamExpr 2) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (hamShear e).eval z = e.eval (shearMap z) := by
  induction e with
  | const q => rfl
  | pi => rfl
  | action j =>
    fin_cases j
    · rfl
    · simp [hamShear, HamExpr.eval, shearMap]
      ring
  | cosMode k => simp only [hamShear, HamExpr.eval, modePhase_shearKey, shearMap]
  | sinMode k => simp only [hamShear, HamExpr.eval, modePhase_shearKey, shearMap]
  | add a b iha ihb => simp only [hamShear, HamExpr.eval, iha, ihb]
  | mul a b iha ihb => simp only [hamShear, HamExpr.eval, iha, ihb]
  | div a b iha ihb => simp only [hamShear, HamExpr.eval, iha, ihb]
  | pow a m ih => simp only [hamShear, HamExpr.eval, ih]
  | exp a ih => simp only [hamShear, HamExpr.eval, ih]
  | sin a ih => simp only [hamShear, HamExpr.eval, ih]
  | cos a ih => simp only [hamShear, HamExpr.eval, ih]
  | sqrt a ih => simp only [hamShear, HamExpr.eval, ih]

/-! ### Fourier data -/

section Poly

variable {α : Type} [CertArith α]

/-- Relabel the keys of a term list by `shearKey`. -/
def shearTerms (l : List (CertKey × CC α)) : List (CertKey × CC α) :=
  l.map fun t => (shearKey t.1, t.2)

/-- The sheared real data `θ ↦ P(S θ)`. -/
def polyShear (P : CertRealPoly α) : CertRealPoly α := ⟨P.zero, shearTerms P.half⟩

theorem eval_polyShear (P : CertRealPoly α) (θ : Fin 2 → ℂ) :
    (polyShear P).eval 2 θ = P.eval 2 (shearAngle θ) := by
  simp only [CertRealPoly.eval, polyShear, shearTerms, List.map_map, Function.comp_def,
    character_shearKey, character_neg_shearKey]

/-- The sheared complex data `θ ↦ P(S θ)` (character witnesses). -/
theorem eval_shearTerms (P : CertPoly α) (θ : Fin 2 → ℂ) :
    (CertPoly.mk (shearTerms P.terms)).eval 2 θ = P.eval 2 (shearAngle θ) := by
  simp only [CertPoly.eval, shearTerms, List.map_map, Function.comp_def, character_shearKey]

/-- The half-lattice sum of a term list (the non-constant part of `CertRealPoly.eval`). -/
def halfSum (n : ℕ) (l : List (CertKey × CC α)) (θ : Fin n → ℂ) : ℂ :=
  (l.map fun t => t.2.toC * character (certKeyFun n t.1) θ +
    (starRingEnd ℂ) t.2.toC * character (-certKeyFun n t.1) θ).sum

theorem CertRealPoly.eval_eq_halfSum (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ) :
    P.eval n θ = (CertArith.val P.zero : ℂ) + halfSum n P.half θ := rfl

end Poly

section Fixed

variable {P : ℕ}

/-- Exact addition of fixed-point complex numbers (mantissas add). -/
def ccAdd (a b : CC (CertFixed P)) : CC (CertFixed P) := ⟨⟨a.re.m + b.re.m⟩, ⟨a.im.m + b.im.m⟩⟩

theorem val_fixed_add (a b : ℤ) :
    CertArith.val (⟨a + b⟩ : CertFixed P) = CertArith.val (⟨a⟩ : CertFixed P) +
      CertArith.val (⟨b⟩ : CertFixed P) := by
  change ((a + b : ℤ) : ℝ) / 2 ^ P = (a : ℝ) / 2 ^ P + (b : ℝ) / 2 ^ P
  push_cast
  ring

theorem val_fixed_zero : CertArith.val (⟨0⟩ : CertFixed P) = 0 := by
  change ((0 : ℤ) : ℝ) / 2 ^ P = 0
  simp

theorem toC_ccAdd (a b : CC (CertFixed P)) : (ccAdd a b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [ccAdd, CC.toC, val_fixed_add]

/-- The lexicographic order of two-component keys (it only fixes the output order). -/
def keyLt2 (a b : CertKey) : Bool :=
  decide (a.getD 0 0 < b.getD 0 0) || (decide (a.getD 0 0 = b.getD 0 0) &&
    decide (a.getD 1 0 < b.getD 1 0))

/-- Insert a term into a key-sorted list, adding mantissas at an equal key. -/
def insertAddTerm (t : CertKey × CC (CertFixed P)) :
    List (CertKey × CC (CertFixed P)) → List (CertKey × CC (CertFixed P))
  | [] => [t]
  | a :: as =>
    if a.1 = t.1 then (a.1, ccAdd a.2 t.2) :: as
    else if keyLt2 t.1 a.1 then t :: a :: as else a :: insertAddTerm t as

/-- The merge of two key-sorted term lists, adding the mantissas of equal keys. -/
def addTerms (l₁ l₂ : List (CertKey × CC (CertFixed P))) : List (CertKey × CC (CertFixed P)) :=
  l₂.foldl (fun acc t => insertAddTerm t acc) l₁

theorem halfSum_insertAddTerm (n : ℕ) (t : CertKey × CC (CertFixed P))
    (l : List (CertKey × CC (CertFixed P))) (θ : Fin n → ℂ) :
    halfSum n (insertAddTerm t l) θ = halfSum n l θ + halfSum n [t] θ := by
  induction l with
  | nil => simp [insertAddTerm, halfSum]
  | cons a as ih =>
    simp only [insertAddTerm]
    split_ifs with h1 h2
    · simp only [halfSum, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, toC_ccAdd,
        map_add, h1]
      ring
    · simp only [halfSum, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
      ring
    · simp only [halfSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem halfSum_addTerms (n : ℕ) (l₁ l₂ : List (CertKey × CC (CertFixed P)))
    (θ : Fin n → ℂ) : halfSum n (addTerms l₁ l₂) θ = halfSum n l₁ θ + halfSum n l₂ θ := by
  induction l₂ generalizing l₁ with
  | nil => simp [addTerms, halfSum]
  | cons t ts ih =>
    have h : addTerms l₁ (t :: ts) = addTerms (insertAddTerm t l₁) ts := rfl
    rw [h, ih, halfSum_insertAddTerm]
    simp only [halfSum, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    ring

/-- The sum of two real data (fixed point, exact). -/
def polyAdd (A B : CertRealPoly (CertFixed P)) : CertRealPoly (CertFixed P) :=
  ⟨⟨A.zero.m + B.zero.m⟩, addTerms A.half B.half⟩

theorem eval_polyAdd (n : ℕ) (A B : CertRealPoly (CertFixed P)) (θ : Fin n → ℂ) :
    (polyAdd A B).eval n θ = A.eval n θ + B.eval n θ := by
  simp only [CertRealPoly.eval_eq_halfSum, polyAdd, halfSum_addTerms, val_fixed_add]
  push_cast
  ring

/-- The embedding of the forced form `⟨[d₀, d₁], [U, 0], [e, e], [P₀, P₁]⟩` (angle `1` not
displaced, both actions at degree `e`). -/
def embForced (d₀ d₁ e : ℤ) (U P₀ P₁ : CertRealPoly (CertFixed P)) : CertEmbedding (CertFixed P) :=
  ⟨[d₀, d₁], [U, ⟨⟨0⟩, []⟩], [e, e], [P₀, P₁]⟩

/-- Its sheared data: angle `polyShear U`, actions `polyShear P₀` and
`polyShear P₀ + polyShear P₁`. -/
def embShear (d₀ d₁ e : ℤ) (U P₀ P₁ : CertRealPoly (CertFixed P)) : CertEmbedding (CertFixed P) :=
  embForced d₀ d₁ e (polyShear U) (polyShear P₀) (polyAdd (polyShear P₀) (polyShear P₁))

/-- **The sheared embedding denotes `shearMap⁻¹ ∘ K ∘ S`.** -/
theorem eval_embShear (d₀ d₁ e : ℤ) (U P₀ P₁ : CertRealPoly (CertFixed P)) (θ : Fin 2 → ℂ) :
    (embShear d₀ d₁ e U P₀ P₁).eval 2 θ =
      shearMapInv ((embForced d₀ d₁ e U P₀ P₁).eval 2 (shearAngle θ)) := by
  have hz : ∀ φ, CertRealPoly.eval 2 (⟨⟨0⟩, []⟩ : CertRealPoly (CertFixed P)) φ = 0 := fun φ => by
    simp [CertRealPoly.eval_eq_halfSum, halfSum, val_fixed_zero]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
    simp [embShear, embForced, CertEmbedding.eval, shearMapInv, shearAngleInv, eval_polyShear,
      eval_polyAdd, hz] <;> simp [shearAngle] <;> ring

end Fixed

/-! ### The reference vector -/

/-- The box of `(ω₀ - ω₁, ω₁)`: centre `(c₀ - c₁, c₁)`, radius `(r₀ + r₁, r₁)`. -/
def shearBox (box : FreqBox) : FreqBox :=
  [((box.getD 0 (0, 0)).1 - (box.getD 1 (0, 0)).1, (box.getD 0 (0, 0)).2 + (box.getD 1 (0, 0)).2),
    box.getD 1 (0, 0)]

theorem freqEncloses_shear {box : FreqBox} {ω : Fin 2 → ℝ} (h : FreqEncloses 2 box ω) :
    FreqEncloses 2 (shearBox box) ![ω 0 - ω 1, ω 1] := by
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  intro i
  fin_cases i
  · simp only [shearBox, Fin.zero_eta, List.getD_cons_zero, Matrix.cons_val_zero]
    push_cast
    calc |ω 0 - ω 1 - (((box.getD 0 (0, 0)).1 : ℝ) - ((box.getD 1 (0, 0)).1 : ℝ))|
        = |(ω 0 - ((box.getD 0 (0, 0)).1 : ℝ)) - (ω 1 - ((box.getD 1 (0, 0)).1 : ℝ))| := by
          ring_nf
      _ ≤ |ω 0 - ((box.getD 0 (0, 0)).1 : ℝ)| + |ω 1 - ((box.getD 1 (0, 0)).1 : ℝ)| :=
          abs_sub _ _
      _ ≤ _ := add_le_add h0 h1
  · simpa [shearBox] using h1

/-- **Diophantine transfer along the shear**: `(ω₀ - ω₁, ω₁)` is `(γ / 2^τ, τ)`-Diophantine if `ω`
is `(γ, τ)`-Diophantine (`k · (ω₀ - ω₁, ω₁) = (k₀, k₁ - k₀) · ω`, `|(k₀, k₁ - k₀)|₁ ≤ 2 |k|₁`). -/
theorem isDiophantine_shear {γ τ : ℝ} {ω : Fin 2 → ℝ} (h : IsDiophantine γ τ ω) (hγ : 0 ≤ γ)
    (hτ : 0 ≤ τ) : IsDiophantine (γ / 2 ^ τ) τ ![ω 0 - ω 1, ω 1] := by
  refine isDiophantine_of_index_map h hγ hτ two_pos (fun k => ![k 0, k 1 - k 0]) ?_ ?_ ?_
  · intro k hk h0
    apply hk
    have a := congrFun h0 0
    have b := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at a b
    ext i
    fin_cases i <;> simp <;> omega
  · intro k
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring
  · intro k
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    have h1 := abs_sub (k 1 : ℝ) (k 0 : ℝ)
    have := abs_nonneg (k 0 : ℝ)
    have := abs_nonneg (k 1 : ℝ)
    linarith

/-! ### Norms and strips -/

/-- `‖shearMap⁻¹ v‖ ≤ 2 ‖v‖` (sup norms). -/
theorem norm_shearMapInv_le (v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ‖shearMapInv v‖ ≤ 2 * ‖v‖ := by
  have h1 : ∀ i, ‖v.1 i‖ ≤ ‖v‖ := fun i => (norm_le_pi_norm v.1 i).trans (norm_fst_le v)
  have h2 : ∀ i, ‖v.2 i‖ ≤ ‖v‖ := fun i => (norm_le_pi_norm v.2 i).trans (norm_snd_le v)
  have h0 : 0 ≤ ‖v‖ := norm_nonneg v
  refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_,
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_⟩ <;> fin_cases i
  · simpa [shearMapInv, shearAngleInv, two_mul] using
      (norm_sub_le (v.1 0) (v.1 1)).trans (add_le_add (h1 0) (h1 1))
  · simpa [shearMapInv, shearAngleInv] using (h1 1).trans (by linarith)
  · simpa [shearMapInv] using (h2 0).trans (by linarith)
  · simpa [shearMapInv, two_mul] using
      (norm_add_le (v.2 0) (v.2 1)).trans (add_le_add (h2 0) (h2 1))

/-- `‖shearMap v‖ ≤ 2 ‖v‖` (sup norms). -/
theorem norm_shearMap_le (v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ‖shearMap v‖ ≤ 2 * ‖v‖ := by
  have h1 : ∀ i, ‖v.1 i‖ ≤ ‖v‖ := fun i => (norm_le_pi_norm v.1 i).trans (norm_fst_le v)
  have h2 : ∀ i, ‖v.2 i‖ ≤ ‖v‖ := fun i => (norm_le_pi_norm v.2 i).trans (norm_snd_le v)
  have h0 : 0 ≤ ‖v‖ := norm_nonneg v
  refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_,
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_⟩ <;> fin_cases i
  · simpa [shearMap, shearAngle, two_mul] using
      (norm_add_le (v.1 0) (v.1 1)).trans (add_le_add (h1 0) (h1 1))
  · simpa [shearMap, shearAngle] using (h1 1).trans (by linarith)
  · simpa [shearMap] using (h2 0).trans (by linarith)
  · simpa [shearMap, two_mul] using
      (norm_sub_le (v.2 1) (v.2 0)).trans (add_le_add (h2 1) (h2 0))

/-- `S` maps the strip of width `ρ / 2` into the strip of width `ρ`. -/
theorem shearAngle_mem_complexStrip {ρ : ℝ} {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (ρ / 2)) :
    shearAngle θ ∈ complexStrip 2 ρ := by
  intro i
  have h0 := hθ 0
  have h1 := hθ 1
  fin_cases i
  · simp only [shearAngle, Fin.zero_eta, Matrix.cons_val_zero, Complex.add_im]
    exact (abs_add_le _ _).trans_lt (by linarith)
  · simp only [shearAngle, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have : 0 ≤ |(θ 0).im| := abs_nonneg _
    linarith

end KAM.CertificateSharp.Linear

end
