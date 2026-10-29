/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffBuild

/-!
# Jet nodes: first and second derivative tables of a program slot

A jet node `SlpNode` is a slot `v` of a program together with the tables `d1 i` and `d2 i j`
(`i, j < 2n`, folded slots) of its first and second directional derivatives along the coordinate
directions `dirVec n i`. `SlpNode.Sound` says that, on an open set `S`, the node of a program `s`
computes the function `f` and its derivative tables (`jetDeriv`). We build nodes for the seven
operations of the straight-line program (constants, actions, characters, sums, products, `exp`,
`inv`) and prove each sound from the second-order rules below. The tables of order three extend
this record by one more field (SO-EXPR part B2).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-! ### Second-order rules -/

theorem JetSmoothOn.neg {S : Set Ph} {f : Ph → ℂ} (hf : JetSmoothOn S f) :
    JetSmoothOn S (fun z => -f z) := ContDiffOn.neg hf

theorem jetDeriv_neg {S : Set Ph} (hS : IsOpen S) (u : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (fun z => -f z)) (fun z => -jetDeriv u f z) S := by
  intro z hz
  have h1 := hf.differentiableAt hS hz
  have e : fderiv ℂ (fun z => -f z) z = -fderiv ℂ f z := h1.hasFDerivAt.neg.fderiv
  simp only [jetDeriv]
  rw [e]
  rfl

theorem jetDeriv2_mul {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => f z * g z)))
      (fun z => (jetDeriv u (jetDeriv v f) z * g z + jetDeriv v f z * jetDeriv u g z) +
        (jetDeriv u f z * jetDeriv v g z + f z * jetDeriv u (jetDeriv v g) z)) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_mul hS v hf hg) hz,
    jetDeriv_add hS u ((hf.jetDeriv hS v).mul hg) (hf.mul (hg.jetDeriv hS v)) hz]
  beta_reduce
  rw [jetDeriv_mul hS u (hf.jetDeriv hS v) hg hz, jetDeriv_mul hS u hf (hg.jetDeriv hS v) hz]

theorem jetDeriv2_add {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f g : Ph → ℂ}
    (hf : JetSmoothOn S f) (hg : JetSmoothOn S g) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => f z + g z)))
      (fun z => jetDeriv u (jetDeriv v f) z + jetDeriv u (jetDeriv v g) z) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_add hS v hf hg) hz]
  beta_reduce
  rw [jetDeriv_add hS u (hf.jetDeriv hS v) (hg.jetDeriv hS v) hz]

theorem jetDeriv2_cexp {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => Complex.exp (f z))))
      (fun z => Complex.exp (f z) * (jetDeriv u f z * jetDeriv v f z) +
        Complex.exp (f z) * jetDeriv u (jetDeriv v f) z) S := by
  intro z hz
  rw [jetDeriv_congr hS u (jetDeriv_cexp hS v hf) hz,
    jetDeriv_mul hS u hf.cexp (hf.jetDeriv hS v) hz]
  beta_reduce
  rw [jetDeriv_cexp hS u hf hz]
  ring

theorem jetDeriv2_inv {S : Set Ph} (hS : IsOpen S) (u v : Ph) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (h0 : ∀ z ∈ S, f z ≠ 0) :
    Set.EqOn (jetDeriv u (jetDeriv v (fun z => (f z)⁻¹)))
      (fun z => 2 * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) * (jetDeriv u f z * jetDeriv v f z) +
        (-1) * ((f z)⁻¹ * (f z)⁻¹) * jetDeriv u (jetDeriv v f) z) S := by
  intro z hz
  have hw := hf.inv h0
  have hww := hw.mul hw
  have hnww := hww.neg
  rw [jetDeriv_congr hS u (jetDeriv_inv hS v hf h0) hz]
  have hm : JetSmoothOn S (fun z => -((f z)⁻¹ * (f z)⁻¹)) := hnww
  rw [jetDeriv_mul hS u hm (hf.jetDeriv hS v) hz]
  beta_reduce
  rw [jetDeriv_neg hS u hww hz]
  beta_reduce
  rw [jetDeriv_mul hS u hw hw hz]
  beta_reduce
  rw [jetDeriv_inv hS u hf h0 hz]
  ring

theorem jetDeriv_modePhase (k : CertKey) (u : Ph) :
    jetDeriv u (fun z => modePhase n k z.1) = fun _ => modePhase n k u.1 := by
  let Λ : Ph →L[ℂ] ℂ := ∑ i, (2 * (Real.pi : ℂ) * (certKeyFun n k i : ℂ)) •
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ)))
  have hΛ : ∀ w : Ph, Λ w = modePhase n k w.1 := by
    intro w
    simp only [Λ, modePhase, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  have e : (fun z : Ph => modePhase n k z.1) = ⇑Λ := funext fun z => (hΛ z).symm
  funext z
  rw [e]
  simp only [jetDeriv, ContinuousLinearMap.fderiv]
  exact hΛ u

theorem jetSmoothOn_modePhase (S : Set Ph) (k : CertKey) :
    JetSmoothOn S (fun z => modePhase n k z.1) :=
  (((contDiff_modePhase n k).comp contDiff_fst).of_le le_top).contDiffOn

theorem jetDeriv_char (k : CertKey) (u : Ph) :
    jetDeriv u (fun z => Complex.exp (Complex.I * modePhase n k z.1)) =
      fun z => (Complex.I * modePhase n k u.1) *
        Complex.exp (Complex.I * modePhase n k z.1) := by
  have hf : JetSmoothOn Set.univ (fun z : Ph => Complex.I * modePhase n k z.1) :=
    (JetSmoothOn.const _ _).mul (jetSmoothOn_modePhase _ k)
  funext z
  rw [jetDeriv_cexp isOpen_univ u hf (Set.mem_univ z)]
  have := jetDeriv_mul isOpen_univ u (JetSmoothOn.const Set.univ Complex.I)
    (jetSmoothOn_modePhase Set.univ k) (Set.mem_univ z)
  rw [jetDeriv_const, jetDeriv_modePhase] at this
  simp only [zero_mul, zero_add] at this
  beta_reduce
  rw [this]
  ring

theorem jetDeriv2_char (k : CertKey) (u v : Ph) :
    jetDeriv u (jetDeriv v (fun z => Complex.exp (Complex.I * modePhase n k z.1))) =
      fun z => (Complex.I * modePhase n k u.1) * ((Complex.I * modePhase n k v.1) *
        Complex.exp (Complex.I * modePhase n k z.1)) := by
  have hF : JetSmoothOn Set.univ (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)) :=
    ((JetSmoothOn.const _ _).mul (jetSmoothOn_modePhase _ k)).cexp
  rw [jetDeriv_char k v]
  funext z
  have := jetDeriv_mul isOpen_univ u (JetSmoothOn.const Set.univ (Complex.I *
    modePhase n k v.1)) hF (Set.mem_univ z)
  rw [jetDeriv_const, jetDeriv_char] at this
  simp only [zero_mul, zero_add] at this
  rw [this]
  ring

theorem modePhase_dirVec (k : CertKey) (i : ℕ) :
    Complex.I * modePhase n k (dirVec n i).1 =
      if i < n then slpConstVal 0 (k.getD i 0) 1 else 0 := by
  by_cases h : i < n
  · simp only [dirVec, h, dite_true, ite_true]
    simp only [modePhase, slpConstVal]
    rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp [certKeyFun]
      ring
    · intro b _ hb
      have : b.val ≠ i := fun e => hb (Fin.ext e)
      simp [hb]
    · simp
  · have h0 : (dirVec n i).1 = 0 := by
      simp only [dirVec, h, dite_false]
      split_ifs <;> rfl
    simp [h, h0, modePhase]

/-! ### Jet nodes -/

/-- A jet node: the value slot and the tables of first and second directional derivatives. -/
structure SlpNode where
  v : ℕ
  d1 : List (Option ℕ)
  d2 : List (List (Option ℕ))

/-- The slot of the derivative in direction `i`. -/
def SlpNode.get1 (J : SlpNode) (i : ℕ) : Option ℕ := J.d1.getD i none

/-- The slot of the second derivative in directions `i`, `j`. -/
def SlpNode.get2 (J : SlpNode) (i j : ℕ) : Option ℕ := (J.d2.getD i []).getD j none

/-- On `S`, the node `J` of the program `s` computes `f` (everywhere) and its derivatives. -/
structure SlpNode.Sound (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (s : List SlpOp) (J : SlpNode) : Prop where
  v_lt : J.v < s.length
  val : ∀ z, (Slp.vals n z s).getD J.v 0 = f z
  d1 : ∀ i < 2 * n, Realizes n S s (J.get1 i) (jetDeriv (dirVec n i) f)
  d2 : ∀ i < 2 * n, ∀ j < 2 * n, Realizes n S s (J.get2 i j)
    (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) f))

theorem SlpNode.Sound.mono {S : Set Ph} {f : Ph → ℂ} {s s' : List SlpOp} {J : SlpNode}
    (h : J.Sound n S f s) (hs : s <+: s') : J.Sound n S f s' where
  v_lt := h.v_lt.trans_le hs.length_le
  val z := by
    obtain ⟨t, rfl⟩ := hs
    rw [Slp.val_append n z s t h.v_lt]
    exact h.val z
  d1 i hi := (h.d1 i hi).mono hs
  d2 i hi j hj := (h.d2 i hi j hj).mono hs

theorem SlpNode.Sound.realizes_v {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {J : SlpNode}
    (h : J.Sound n S f s) : Realizes n S s (some J.v) f :=
  ⟨h.v_lt, fun z _ => h.val z⟩

/-- Finish a node: build the two tables from the given entry computations. -/
def slpFinish (n : ℕ) (v : ℕ) (c1 : ℕ → SlpComp) (c2 : ℕ → ℕ → SlpComp) (s : List SlpOp) :
    List SlpOp × SlpNode :=
  let r1 := slpTab1 n c1 s
  let r2 := slpTab2 n c2 r1.1
  (r2.1, ⟨v, r1.2, r2.2⟩)

theorem slpFinish_sound {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {v : ℕ}
    (hv : v < s.length) (hval : ∀ z, (Slp.vals n z s).getD v 0 = f z)
    (c1 : ℕ → SlpComp) (c2 : ℕ → ℕ → SlpComp)
    (h1 : ∀ i < 2 * n, SlpEnt n S s (c1 i) (jetDeriv (dirVec n i) f))
    (h2 : ∀ i < 2 * n, ∀ j < 2 * n,
      SlpEnt n S s (c2 i j) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) f))) :
    s <+: (slpFinish n v c1 c2 s).1 ∧ (slpFinish n v c1 c2 s).2.Sound n S f
      (slpFinish n v c1 c2 s).1 := by
  obtain ⟨p1, t1⟩ := slpTab1_spec c1 _ h1 (List.prefix_refl s)
  obtain ⟨p2, t2⟩ := slpTab2_spec c2 _ h2 p1
  refine ⟨p1.trans p2, ?_⟩
  refine ⟨hv.trans_le (p1.trans p2).length_le, fun z => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨t, ht⟩ := p1.trans p2
    simp only [slpFinish]
    rw [← ht, Slp.val_append n z s t hv]
    exact hval z
  · exact (t1 i hi).mono p2
  · exact t2 i hi j hj

end KAM.Certificate

end
