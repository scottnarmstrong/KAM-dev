/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffBuild
public import KAM.Certificate.Expr.DiffCalculus3

/-!
# Jet nodes: derivative tables of a program slot, to order three

A jet node `SlpNode` is a slot `v` of a program together with the tables `d1 i`, `d2 i j` and
`d3 i j k` (`i, j, k < 2n`, folded slots) of its first, second and third directional derivatives
along the coordinate directions `dirVec n i`. `SlpNode.Sound` says that, on an open set `S`, the
node of a program `s` computes the function `f` and its derivative tables (`jetDeriv`). We build
nodes for the seven operations of the straight-line program (constants, actions, characters, sums,
products, `exp`, `inv`) and prove each sound from the second- and third-order rules of
`KAM.Certificate.Expr.DiffCalculus3`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

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

theorem jetDeriv3_char (k : CertKey) (u v w : Ph) :
    jetDeriv u (jetDeriv v (jetDeriv w (fun z => Complex.exp (Complex.I * modePhase n k z.1)))) =
      fun z => (Complex.I * modePhase n k u.1) * ((Complex.I * modePhase n k v.1) *
        ((Complex.I * modePhase n k w.1) * Complex.exp (Complex.I * modePhase n k z.1))) := by
  have hC : JetSmoothOn Set.univ
      (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)) :=
    ((JetSmoothOn.const _ _).mul (jetSmoothOn_modePhase _ k)).cexp
  have hcv := (JetSmoothOn.const Set.univ (Complex.I * modePhase n k v.1)).mul hC
  rw [jetDeriv_char k w]
  have h1 : jetDeriv v (fun z : Ph => (Complex.I * modePhase n k w.1) *
      Complex.exp (Complex.I * modePhase n k z.1)) = fun z => (Complex.I * modePhase n k w.1) *
      ((Complex.I * modePhase n k v.1) * Complex.exp (Complex.I * modePhase n k z.1)) := by
    funext y
    rw [jetDeriv_cmul isOpen_univ v _ hC (Set.mem_univ y), jetDeriv_char]
  rw [h1]
  funext z
  rw [jetDeriv_cmul isOpen_univ u _ hcv (Set.mem_univ z)]
  beta_reduce
  rw [jetDeriv_cmul isOpen_univ u _ hC (Set.mem_univ z), jetDeriv_char]
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

/-- A jet node: the value slot and the tables of first, second and third directional
derivatives. -/
structure SlpNode where
  v : ℕ
  d1 : List (Option ℕ)
  d2 : List (List (Option ℕ))
  d3 : List (List (List (Option ℕ)))

/-- The slot of the derivative in direction `i`. -/
def SlpNode.get1 (J : SlpNode) (i : ℕ) : Option ℕ := J.d1.getD i none

/-- The slot of the second derivative in directions `i`, `j`. -/
def SlpNode.get2 (J : SlpNode) (i j : ℕ) : Option ℕ := (J.d2.getD i []).getD j none

/-- The slot of the third derivative in directions `i`, `j`, `k`. -/
def SlpNode.get3 (J : SlpNode) (i j k : ℕ) : Option ℕ :=
  (((J.d3.getD i []).getD j []).getD k none)

/-- On `S`, the node `J` of the program `s` computes `f` (everywhere) and its derivatives. -/
structure SlpNode.Sound (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (s : List SlpOp) (J : SlpNode) : Prop where
  v_lt : J.v < s.length
  val : ∀ z, (Slp.vals n z s).getD J.v 0 = f z
  d1 : ∀ i < 2 * n, Realizes n S s (J.get1 i) (jetDeriv (dirVec n i) f)
  d2 : ∀ i < 2 * n, ∀ j < 2 * n, Realizes n S s (J.get2 i j)
    (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) f))
  d3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, Realizes n S s (J.get3 i j k)
    (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k) f)))

theorem SlpNode.Sound.mono {S : Set Ph} {f : Ph → ℂ} {s s' : List SlpOp} {J : SlpNode}
    (h : J.Sound n S f s) (hs : s <+: s') : J.Sound n S f s' where
  v_lt := h.v_lt.trans_le hs.length_le
  val z := by
    obtain ⟨t, rfl⟩ := hs
    rw [Slp.val_append n z s t h.v_lt]
    exact h.val z
  d1 i hi := (h.d1 i hi).mono hs
  d2 i hi j hj := (h.d2 i hi j hj).mono hs
  d3 i hi j hj k hk := (h.d3 i hi j hj k hk).mono hs

theorem SlpNode.Sound.realizes_v {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {J : SlpNode}
    (h : J.Sound n S f s) : Realizes n S s (some J.v) f :=
  ⟨h.v_lt, fun z _ => h.val z⟩

/-- Finish a node: build the three tables from the given entry computations. -/
def slpFinish (n : ℕ) (v : ℕ) (c1 : ℕ → SlpComp) (c2 : ℕ → ℕ → SlpComp)
    (c3 : ℕ → ℕ → ℕ → SlpComp) (s : List SlpOp) : List SlpOp × SlpNode :=
  let r1 := slpTab1 n c1 s
  let r2 := slpTab2 n c2 r1.1
  let r3 := slpTab3 n c3 r2.1
  (r3.1, ⟨v, r1.2, r2.2, r3.2⟩)

theorem slpFinish_sound {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {v : ℕ}
    (hv : v < s.length) (hval : ∀ z, (Slp.vals n z s).getD v 0 = f z)
    (c1 : ℕ → SlpComp) (c2 : ℕ → ℕ → SlpComp) (c3 : ℕ → ℕ → ℕ → SlpComp)
    (h1 : ∀ i < 2 * n, SlpEnt n S s (c1 i) (jetDeriv (dirVec n i) f))
    (h2 : ∀ i < 2 * n, ∀ j < 2 * n,
      SlpEnt n S s (c2 i j) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) f)))
    (h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S s (c3 i j k)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k) f)))) :
    s <+: (slpFinish n v c1 c2 c3 s).1 ∧ (slpFinish n v c1 c2 c3 s).2.Sound n S f
      (slpFinish n v c1 c2 c3 s).1 := by
  obtain ⟨p1, t1⟩ := slpTab1_spec c1 _ h1 (List.prefix_refl s)
  obtain ⟨p2, t2⟩ := slpTab2_spec c2 _ h2 p1
  obtain ⟨p3, t3⟩ := slpTab3_spec c3 _ h3 (p1.trans p2)
  refine ⟨(p1.trans p2).trans p3, ?_⟩
  refine ⟨hv.trans_le ((p1.trans p2).trans p3).length_le, fun z => ?_, fun i hi => ?_,
    fun i hi j hj => ?_, fun i hi j hj k hk => ?_⟩
  · obtain ⟨t, ht⟩ := (p1.trans p2).trans p3
    simp only [slpFinish]
    rw [← ht, Slp.val_append n z s t hv]
    exact hval z
  · exact (t1 i hi).mono (p2.trans p3)
  · exact (t2 i hi j hj).mono p3
  · exact t3 i hi j hj k hk

/-! ### Constants, actions, characters -/

/-- The node of a constant. -/
def slpConstNode (n : ℕ) (s : List SlpOp) (re im : ℚ) (deg : ℤ) : List SlpOp × SlpNode :=
  slpFinish n s.length (fun _ => slpPure none) (fun _ _ => slpPure none)
    (fun _ _ _ => slpPure none) (s ++ [.const re im deg])

theorem slpConstNode_sound (S : Set Ph) (s : List SlpOp) (re im : ℚ) (deg : ℤ) :
    s <+: (slpConstNode n s re im deg).1 ∧ (slpConstNode n s re im deg).2.Sound n S
      (fun _ => slpConstVal re im deg) (slpConstNode n s re im deg).1 := by
  have hv : s.length < (s ++ [SlpOp.const re im deg]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.const re im deg])).getD s.length 0 =
      slpConstVal re im deg := fun z => by rw [Slp.val_snoc_self]; rfl
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.const re im deg]) (slpPure none)
      (jetDeriv (dirVec n i) (fun _ => slpConstVal re im deg)) := fun i _ => by
    rw [jetDeriv_const]; exact SlpEnt.pure (Realizes.none S _)
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S (s ++ [.const re im deg]) (slpPure none)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun _ => slpConstVal re im deg))) :=
    fun i _ j _ => by
    rw [jetDeriv_const, jetDeriv_const]; exact SlpEnt.pure (Realizes.none S _)
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S (s ++ [.const re im deg])
      (slpPure none) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j)
        (jetDeriv (dirVec n k) (fun _ => slpConstVal re im deg)))) :=
    fun i _ j _ k _ => by
    rw [jetDeriv_const, jetDeriv_const, jetDeriv_const]; exact SlpEnt.pure (Realizes.none S _)
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨(List.prefix_append _ _).trans p, h⟩

theorem jetDeriv_action (j : Fin n) (u : Ph) :
    jetDeriv u (fun z : Ph => z.2 j) = fun _ => u.2 j := by
  have e : (fun z : Ph => z.2 j) = ⇑((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin n => ℂ) j).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))) :=
    rfl
  funext z
  rw [e]
  simp [jetDeriv, ContinuousLinearMap.fderiv]

theorem dirVec_snd (i : ℕ) (j : Fin n) :
    (dirVec n i).2 j = if i = n + j.val then 1 else 0 := by
  by_cases h1 : i < n
  · have : i ≠ n + j.val := by omega
    simp [dirVec, h1, this]
  · by_cases h2 : i - n < n
    · simp only [dirVec, h1, h2, dite_true, dite_false, Pi.single_apply]
      by_cases hj : j = ⟨i - n, h2⟩
      · have hv : j.val = i - n := congrArg Fin.val hj
        have : i = n + j.val := by omega
        simp only [eq_true hj, eq_true this, ite_true]
      · have : i ≠ n + j.val := fun e => hj (Fin.ext (by show j.val = i - n; omega))
        simp only [eq_false hj, eq_false this, ite_false]
    · have : i ≠ n + j.val := by have := j.isLt; omega
      simp [dirVec, h1, h2, this]

/-- The node of the action coordinate `j`. -/
def slpActionNode (n : ℕ) (s : List SlpOp) (j : ℕ) : List SlpOp × SlpNode :=
  slpFinish n s.length (fun i s' => if i = n + j then slpEmit s' (.const 1 0 0) else (s', none))
    (fun _ _ => slpPure none) (fun _ _ _ => slpPure none) (s ++ [.action j])

theorem slpActionNode_sound (S : Set Ph) (s : List SlpOp) (j : Fin n) :
    s <+: (slpActionNode n s j.val).1 ∧ (slpActionNode n s j.val).2.Sound n S
      (fun z : Ph => z.2 j) (slpActionNode n s j.val).1 := by
  have hv : s.length < (s ++ [SlpOp.action j.val]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.action j.val])).getD s.length 0 = z.2 j :=
    fun z => by rw [Slp.val_snoc_self]; simp [SlpOp.step]
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.action j.val])
      (fun s' => if i = n + j.val then slpEmit s' (.const 1 0 0) else (s', none))
      (jetDeriv (dirVec n i) (fun z : Ph => z.2 j)) := by
    intro i _ s' hs'
    rw [jetDeriv_action]
    by_cases h : i = n + j.val
    · simp only [h, ite_true]
      refine ⟨slpEmit_prefix _ _, slpEmit_realizes _ _ _ fun z _ => ?_⟩
      simp [SlpOp.step, slpConstVal, dirVec_snd]
    · simp only [h, ite_false]
      refine ⟨List.prefix_refl _, trivial, fun z _ => ?_⟩
      simp [slpOv, dirVec_snd, h]
  have h2 : ∀ i < 2 * n, ∀ j' < 2 * n, SlpEnt n S (s ++ [.action j.val]) (slpPure none)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j') (fun z : Ph => z.2 j))) :=
    fun i _ j' _ => by
    rw [jetDeriv_action, jetDeriv_const]; exact SlpEnt.pure (Realizes.none S _)
  have h3 : ∀ i < 2 * n, ∀ j' < 2 * n, ∀ k < 2 * n, SlpEnt n S (s ++ [.action j.val])
      (slpPure none) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j')
        (jetDeriv (dirVec n k) (fun z : Ph => z.2 j)))) :=
    fun i _ j' _ k _ => by
    rw [jetDeriv_action, jetDeriv_const, jetDeriv_const]; exact SlpEnt.pure (Realizes.none S _)
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨(List.prefix_append _ _).trans p, h⟩

/-- The node of the character `e^{2πi k·θ}`. -/
def slpCharNode (n : ℕ) (s : List SlpOp) (k : CertKey) : List SlpOp × SlpNode :=
  slpFinish n s.length
    (fun i => if i < n then slpCScale 0 ((k.getD i 0 : ℤ) : ℚ) 1 (slpPure (some s.length))
      else slpPure none)
    (fun i j => if i < n ∧ j < n then
      slpCScale (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ))) 0 2
        (slpPure (some s.length)) else slpPure none)
    (fun i j l => if i < n ∧ j < n ∧ l < n then
      slpCScale 0 (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ) * ((k.getD l 0 : ℤ) : ℚ))) 3
        (slpPure (some s.length)) else slpPure none)
    (s ++ [.char k])

theorem slpCharNode_sound (S : Set Ph) (s : List SlpOp) (k : CertKey) :
    s <+: (slpCharNode n s k).1 ∧ (slpCharNode n s k).2.Sound n S
      (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)) (slpCharNode n s k).1 := by
  have hv : s.length < (s ++ [SlpOp.char k]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.char k])).getD s.length 0 =
      Complex.exp (Complex.I * modePhase n k z.1) :=
    fun z => by rw [Slp.val_snoc_self]; rfl
  have hvr : Realizes n S (s ++ [.char k]) (some s.length)
      (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)) :=
    ⟨by simp [SlotOk], fun z _ => by simpa [slpOv] using hval z⟩
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.char k])
      (if i < n then slpCScale 0 ((k.getD i 0 : ℤ) : ℚ) 1 (slpPure (some s.length))
        else slpPure none)
      (jetDeriv (dirVec n i) (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1))) := by
    intro i _
    rw [jetDeriv_char, modePhase_dirVec]
    by_cases h : i < n
    · simp only [h, ite_true]
      exact (SlpEnt.pure hvr).scale _ _ _
    · simp only [h, ite_false, zero_mul]
      exact SlpEnt.pure (Realizes.none S _)
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S (s ++ [.char k])
      (if i < n ∧ j < n then
        slpCScale (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ))) 0 2
          (slpPure (some s.length)) else slpPure none)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j)
        (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)))) := by
    intro i _ j _
    rw [jetDeriv2_char, modePhase_dirVec, modePhase_dirVec]
    by_cases h : i < n ∧ j < n
    · simp only [h, and_self, ite_true]
      refine ((SlpEnt.pure hvr).scale _ _ _).congr fun z _ => ?_
      simp only [slpConstVal]
      push_cast
      simp [zpow_ofNat]
      ring_nf
      simp [Complex.I_sq]
    · simp only [h, ite_false]
      have : ¬ i < n ∨ ¬ j < n := by tauto
      refine (SlpEnt.pure (Realizes.none S _)).congr fun z _ => ?_
      rcases this with h' | h' <;> simp [h']
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ l < 2 * n, SlpEnt n S (s ++ [.char k])
      (if i < n ∧ j < n ∧ l < n then
        slpCScale 0 (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ) *
          ((k.getD l 0 : ℤ) : ℚ))) 3 (slpPure (some s.length)) else slpPure none)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n l)
        (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1))))) := by
    intro i _ j _ l _
    rw [jetDeriv3_char, modePhase_dirVec, modePhase_dirVec, modePhase_dirVec]
    by_cases h : i < n ∧ j < n ∧ l < n
    · simp only [h, and_self, ite_true]
      refine ((SlpEnt.pure hvr).scale _ _ _).congr fun z _ => ?_
      simp only [slpConstVal]
      push_cast
      simp [zpow_ofNat]
      ring_nf
      simp
    · simp only [h, ite_false]
      refine (SlpEnt.pure (Realizes.none S _)).congr fun z _ => ?_
      by_cases h1 : i < n <;> by_cases h2 : j < n <;> by_cases h3 : l < n <;> simp_all
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨(List.prefix_append _ _).trans p, h⟩

/-! ### Sums, products, `exp`, `inv` -/

/-- The slot of the sum `f_{ij} f_k + f_j f_{ik} + f_i f_{jk}` of the node `A`. -/
def slpCross (A : SlpNode) (i j k : ℕ) : SlpComp :=
  slpCAdd (slpCAdd (slpCMul (slpPure (A.get2 i j)) (slpPure (A.get1 k)))
    (slpCMul (slpPure (A.get1 j)) (slpPure (A.get2 i k))))
    (slpCMul (slpPure (A.get1 i)) (slpPure (A.get2 j k)))

theorem slpCross_ent {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {A : SlpNode}
    (hA : A.Sound n S f s) {i j k : ℕ} (hi : i < 2 * n) (hj : j < 2 * n) (hk : k < 2 * n) :
    SlpEnt n S s (slpCross A i j k)
      (fun z => (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) f) z * jetDeriv (dirVec n k) f z +
        jetDeriv (dirVec n j) f z * jetDeriv (dirVec n i) (jetDeriv (dirVec n k) f) z) +
        jetDeriv (dirVec n i) f z * jetDeriv (dirVec n j) (jetDeriv (dirVec n k) f) z) :=
  (((SlpEnt.pure (hA.d2 i hi j hj)).mul (SlpEnt.pure (hA.d1 k hk))).add
    ((SlpEnt.pure (hA.d1 j hj)).mul (SlpEnt.pure (hA.d2 i hi k hk)))).add
    ((SlpEnt.pure (hA.d1 i hi)).mul (SlpEnt.pure (hA.d2 j hj k hk)))

/-- The node of a sum. -/
def slpAddNode (n : ℕ) (s : List SlpOp) (A B : SlpNode) : List SlpOp × SlpNode :=
  slpFinish n s.length (fun i => slpCAdd (slpPure (A.get1 i)) (slpPure (B.get1 i)))
    (fun i j => slpCAdd (slpPure (A.get2 i j)) (slpPure (B.get2 i j)))
    (fun i j k => slpCAdd (slpPure (A.get3 i j k)) (slpPure (B.get3 i j k)))
    (s ++ [.add A.v B.v])

theorem slpAddNode_sound {S : Set Ph} (hS : IsOpen S) {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) {s : List SlpOp} {A B : SlpNode} (hA : A.Sound n S f s)
    (hB : B.Sound n S g s) :
    s <+: (slpAddNode n s A B).1 ∧ (slpAddNode n s A B).2.Sound n S (fun z => f z + g z)
      (slpAddNode n s A B).1 := by
  have hp : s <+: s ++ [SlpOp.add A.v B.v] := List.prefix_append _ _
  have hA' := hA.mono hp
  have hB' := hB.mono hp
  have hv : s.length < (s ++ [SlpOp.add A.v B.v]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.add A.v B.v])).getD s.length 0 = f z + g z :=
    fun z => by rw [Slp.val_snoc_self]; simp only [SlpOp.step]; rw [hA.val z, hB.val z]
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.add A.v B.v])
      (slpCAdd (slpPure (A.get1 i)) (slpPure (B.get1 i)))
      (jetDeriv (dirVec n i) (fun z => f z + g z)) := fun i hi =>
    ((SlpEnt.pure (hA'.d1 i hi)).add (SlpEnt.pure (hB'.d1 i hi))).congr
      (jetDeriv_add hS _ hf hg).symm
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S (s ++ [.add A.v B.v])
      (slpCAdd (slpPure (A.get2 i j)) (slpPure (B.get2 i j)))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun z => f z + g z))) := fun i hi j hj =>
    ((SlpEnt.pure (hA'.d2 i hi j hj)).add (SlpEnt.pure (hB'.d2 i hi j hj))).congr
      (jetDeriv2_add hS _ _ hf hg).symm
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S (s ++ [.add A.v B.v])
      (slpCAdd (slpPure (A.get3 i j k)) (slpPure (B.get3 i j k)))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k)
        (fun z => f z + g z)))) := fun i hi j hj k hk =>
    ((SlpEnt.pure (hA'.d3 i hi j hj k hk)).add (SlpEnt.pure (hB'.d3 i hi j hj k hk))).congr
      (jetDeriv3_add hS _ _ _ hf hg).symm
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨hp.trans p, h⟩

/-- The third derivative entry of a product (Leibniz rule). -/
def slpMulD3 (A B : SlpNode) (i j k : ℕ) : SlpComp :=
  slpCAdd
    (slpCAdd (slpCAdd (slpCMul (slpPure (A.get3 i j k)) (slpPure (some B.v)))
      (slpCMul (slpPure (A.get2 j k)) (slpPure (B.get1 i))))
      (slpCAdd (slpCMul (slpPure (A.get2 i k)) (slpPure (B.get1 j)))
      (slpCMul (slpPure (A.get1 k)) (slpPure (B.get2 i j)))))
    (slpCAdd (slpCAdd (slpCMul (slpPure (A.get2 i j)) (slpPure (B.get1 k)))
      (slpCMul (slpPure (A.get1 j)) (slpPure (B.get2 i k))))
      (slpCAdd (slpCMul (slpPure (A.get1 i)) (slpPure (B.get2 j k)))
      (slpCMul (slpPure (some A.v)) (slpPure (B.get3 i j k)))))

/-- The node of a product. -/
def slpMulNode (n : ℕ) (s : List SlpOp) (A B : SlpNode) : List SlpOp × SlpNode :=
  slpFinish n s.length
    (fun i => slpCAdd (slpCMul (slpPure (A.get1 i)) (slpPure (some B.v)))
      (slpCMul (slpPure (some A.v)) (slpPure (B.get1 i))))
    (fun i j => slpCAdd
      (slpCAdd (slpCMul (slpPure (A.get2 i j)) (slpPure (some B.v)))
        (slpCMul (slpPure (A.get1 j)) (slpPure (B.get1 i))))
      (slpCAdd (slpCMul (slpPure (A.get1 i)) (slpPure (B.get1 j)))
        (slpCMul (slpPure (some A.v)) (slpPure (B.get2 i j)))))
    (slpMulD3 A B) (s ++ [.mul A.v B.v])

theorem slpMulNode_sound {S : Set Ph} (hS : IsOpen S) {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) {s : List SlpOp} {A B : SlpNode} (hA : A.Sound n S f s)
    (hB : B.Sound n S g s) :
    s <+: (slpMulNode n s A B).1 ∧ (slpMulNode n s A B).2.Sound n S (fun z => f z * g z)
      (slpMulNode n s A B).1 := by
  have hp : s <+: s ++ [SlpOp.mul A.v B.v] := List.prefix_append _ _
  have hA' := hA.mono hp
  have hB' := hB.mono hp
  have hv : s.length < (s ++ [SlpOp.mul A.v B.v]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.mul A.v B.v])).getD s.length 0 = f z * g z :=
    fun z => by rw [Slp.val_snoc_self]; simp only [SlpOp.step]; rw [hA.val z, hB.val z]
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.mul A.v B.v])
      (slpCAdd (slpCMul (slpPure (A.get1 i)) (slpPure (some B.v)))
        (slpCMul (slpPure (some A.v)) (slpPure (B.get1 i))))
      (jetDeriv (dirVec n i) (fun z => f z * g z)) := fun i hi =>
    (((SlpEnt.pure (hA'.d1 i hi)).mul (SlpEnt.pure hB'.realizes_v)).add
      ((SlpEnt.pure hA'.realizes_v).mul (SlpEnt.pure (hB'.d1 i hi)))).congr
      (jetDeriv_mul hS _ hf hg).symm
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S (s ++ [.mul A.v B.v])
      (slpCAdd
        (slpCAdd (slpCMul (slpPure (A.get2 i j)) (slpPure (some B.v)))
          (slpCMul (slpPure (A.get1 j)) (slpPure (B.get1 i))))
        (slpCAdd (slpCMul (slpPure (A.get1 i)) (slpPure (B.get1 j)))
          (slpCMul (slpPure (some A.v)) (slpPure (B.get2 i j)))))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun z => f z * g z))) := fun i hi j hj =>
    ((((SlpEnt.pure (hA'.d2 i hi j hj)).mul (SlpEnt.pure hB'.realizes_v)).add
      ((SlpEnt.pure (hA'.d1 j hj)).mul (SlpEnt.pure (hB'.d1 i hi)))).add
      (((SlpEnt.pure (hA'.d1 i hi)).mul (SlpEnt.pure (hB'.d1 j hj))).add
      ((SlpEnt.pure hA'.realizes_v).mul (SlpEnt.pure (hB'.d2 i hi j hj))))).congr
      (jetDeriv2_mul hS _ _ hf hg).symm
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S (s ++ [.mul A.v B.v])
      (slpMulD3 A B i j k) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k)
        (fun z => f z * g z)))) := fun i hi j hj k hk => by
    unfold slpMulD3
    exact (((((SlpEnt.pure (hA'.d3 i hi j hj k hk)).mul (SlpEnt.pure hB'.realizes_v)).add
      ((SlpEnt.pure (hA'.d2 j hj k hk)).mul (SlpEnt.pure (hB'.d1 i hi)))).add
      (((SlpEnt.pure (hA'.d2 i hi k hk)).mul (SlpEnt.pure (hB'.d1 j hj))).add
      ((SlpEnt.pure (hA'.d1 k hk)).mul (SlpEnt.pure (hB'.d2 i hi j hj))))).add
      ((((SlpEnt.pure (hA'.d2 i hi j hj)).mul (SlpEnt.pure (hB'.d1 k hk))).add
      ((SlpEnt.pure (hA'.d1 j hj)).mul (SlpEnt.pure (hB'.d2 i hi k hk)))).add
      (((SlpEnt.pure (hA'.d1 i hi)).mul (SlpEnt.pure (hB'.d2 j hj k hk))).add
      ((SlpEnt.pure hA'.realizes_v).mul (SlpEnt.pure (hB'.d3 i hi j hj k hk)))))).congr
      (jetDeriv3_mul hS _ _ _ hf hg).symm
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨hp.trans p, h⟩

/-- The third derivative entry of `exp` (`E` is the slot of the exponential). -/
def slpExpD3 (E : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpComp :=
  slpCMul (slpPure E) (slpCAdd
    (slpCMul (slpPure (A.get1 i)) (slpCMul (slpPure (A.get1 j)) (slpPure (A.get1 k))))
    (slpCAdd (slpCross A i j k) (slpPure (A.get3 i j k))))

/-- The node of `exp`. -/
def slpExpNode (n : ℕ) (s : List SlpOp) (A : SlpNode) : List SlpOp × SlpNode :=
  slpFinish n s.length
    (fun i => slpCMul (slpPure (some s.length)) (slpPure (A.get1 i)))
    (fun i j => slpCAdd
      (slpCMul (slpPure (some s.length)) (slpCMul (slpPure (A.get1 i)) (slpPure (A.get1 j))))
      (slpCMul (slpPure (some s.length)) (slpPure (A.get2 i j))))
    (slpExpD3 (some s.length) A) (s ++ [.exp A.v])

theorem slpExpNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) :
    s <+: (slpExpNode n s A).1 ∧
      (slpExpNode n s A).2.Sound n S (fun z => Complex.exp (f z)) (slpExpNode n s A).1 := by
  have hp : s <+: s ++ [SlpOp.exp A.v] := List.prefix_append _ _
  have hA' := hA.mono hp
  have hv : s.length < (s ++ [SlpOp.exp A.v]).length := by simp
  have hval : ∀ z : Ph, (Slp.vals n z (s ++ [.exp A.v])).getD s.length 0 =
      Complex.exp (f z) := fun z => by rw [Slp.val_snoc_self]; simp only [SlpOp.step]; rw [hA.val z]
  have hE : Realizes n S (s ++ [.exp A.v]) (some s.length) (fun z => Complex.exp (f z)) :=
    ⟨by simp [SlotOk], fun z _ => by simpa [slpOv] using hval z⟩
  have h1 : ∀ i < 2 * n, SlpEnt n S (s ++ [.exp A.v])
      (slpCMul (slpPure (some s.length)) (slpPure (A.get1 i)))
      (jetDeriv (dirVec n i) (fun z => Complex.exp (f z))) := fun i hi =>
    ((SlpEnt.pure hE).mul (SlpEnt.pure (hA'.d1 i hi))).congr (jetDeriv_cexp hS _ hf).symm
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S (s ++ [.exp A.v])
      (slpCAdd
        (slpCMul (slpPure (some s.length)) (slpCMul (slpPure (A.get1 i)) (slpPure (A.get1 j))))
        (slpCMul (slpPure (some s.length)) (slpPure (A.get2 i j))))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun z => Complex.exp (f z)))) :=
    fun i hi j hj =>
    (((SlpEnt.pure hE).mul ((SlpEnt.pure (hA'.d1 i hi)).mul (SlpEnt.pure (hA'.d1 j hj)))).add
      ((SlpEnt.pure hE).mul (SlpEnt.pure (hA'.d2 i hi j hj)))).congr
      (jetDeriv2_cexp hS _ _ hf).symm
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S (s ++ [.exp A.v])
      (slpExpD3 (some s.length) A i j k) (jetDeriv (dirVec n i) (jetDeriv (dirVec n j)
        (jetDeriv (dirVec n k) (fun z => Complex.exp (f z))))) := fun i hi j hj k hk => by
    unfold slpExpD3
    exact ((SlpEnt.pure hE).mul (((SlpEnt.pure (hA'.d1 i hi)).mul
      ((SlpEnt.pure (hA'.d1 j hj)).mul (SlpEnt.pure (hA'.d1 k hk)))).add
      ((slpCross_ent hA' hi hj hk).add (SlpEnt.pure (hA'.d3 i hi j hj k hk))))).congr
      (jetDeriv3_cexp hS _ _ _ hf).symm
  obtain ⟨p, h⟩ := slpFinish_sound hv hval _ _ _ h1 h2 h3
  exact ⟨hp.trans p, h⟩

/-- The third derivative entry of `x⁻¹` from the slots `w²`, `w³`, `w⁴` (`w = x⁻¹`). -/
def slpInvD3 (w2 w3 w4 : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpComp :=
  slpCAdd (slpCScale (-6) 0 0 (slpCMul (slpPure w4) (slpCMul (slpPure (A.get1 i))
    (slpCMul (slpPure (A.get1 j)) (slpPure (A.get1 k))))))
    (slpCAdd (slpCScale 2 0 0 (slpCMul (slpPure w3) (slpCross A i j k)))
      (slpCScale (-1) 0 0 (slpCMul (slpPure w2) (slpPure (A.get3 i j k)))))

/-- The derivative tables of `x⁻¹` from the slots `w²`, `w³` and `w⁴` (`w = x⁻¹`). -/
def slpInvTail (n : ℕ) (v : ℕ) (A : SlpNode) (w2 w3 w4 : Option ℕ) (s : List SlpOp) :
    List SlpOp × SlpNode :=
  slpFinish n v
    (fun i => slpCScale (-1) 0 0 (slpCMul (slpPure w2) (slpPure (A.get1 i))))
    (fun i j => slpCAdd
      (slpCScale 2 0 0 (slpCMul (slpPure w3) (slpCMul (slpPure (A.get1 i))
        (slpPure (A.get1 j)))))
      (slpCScale (-1) 0 0 (slpCMul (slpPure w2) (slpPure (A.get2 i j)))))
    (slpInvD3 w2 w3 w4 A) s

theorem slpConstVal_rat (q : ℚ) : slpConstVal q 0 0 = (q : ℂ) := by
  simp [slpConstVal]

theorem slpInvTail_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (h0 : ∀ z ∈ S, f z ≠ 0) {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s)
    {v : ℕ} (hv : v < s.length) (hval : ∀ z, (Slp.vals n z s).getD v 0 = (f z)⁻¹)
    {w2 w3 w4 : Option ℕ} (hw2 : Realizes n S s w2 (fun z => (f z)⁻¹ * (f z)⁻¹))
    (hw3 : Realizes n S s w3 (fun z => (f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)))
    (hw4 : Realizes n S s w4 (fun z => (f z)⁻¹ * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)))) :
    s <+: (slpInvTail n v A w2 w3 w4 s).1 ∧
      (slpInvTail n v A w2 w3 w4 s).2.Sound n S (fun z => (f z)⁻¹)
        (slpInvTail n v A w2 w3 w4 s).1 := by
  have h1 : ∀ i < 2 * n, SlpEnt n S s
      (slpCScale (-1) 0 0 (slpCMul (slpPure w2) (slpPure (A.get1 i))))
      (jetDeriv (dirVec n i) (fun z => (f z)⁻¹)) := by
    intro i hi
    refine (((SlpEnt.pure hw2).mul (SlpEnt.pure (hA.d1 i hi))).scale (-1) 0 0).congr ?_
    intro z hz
    rw [jetDeriv_inv hS _ hf h0 hz]
    beta_reduce
    rw [slpConstVal_rat]
    push_cast
    ring
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S s
      (slpCAdd
        (slpCScale 2 0 0 (slpCMul (slpPure w3) (slpCMul (slpPure (A.get1 i))
          (slpPure (A.get1 j)))))
        (slpCScale (-1) 0 0 (slpCMul (slpPure w2) (slpPure (A.get2 i j)))))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun z => (f z)⁻¹))) := by
    intro i hi j hj
    refine ((((SlpEnt.pure hw3).mul ((SlpEnt.pure (hA.d1 i hi)).mul
      (SlpEnt.pure (hA.d1 j hj)))).scale 2 0 0).add
      (((SlpEnt.pure hw2).mul (SlpEnt.pure (hA.d2 i hi j hj))).scale (-1) 0 0)).congr ?_
    intro z hz
    rw [jetDeriv2_inv hS _ _ hf h0 hz]
    beta_reduce
    rw [slpConstVal_rat, slpConstVal_rat]
    push_cast
    ring
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S s (slpInvD3 w2 w3 w4 A i j k)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k)
        (fun z => (f z)⁻¹)))) := by
    intro i hi j hj k hk
    unfold slpInvD3
    refine ((((SlpEnt.pure hw4).mul ((SlpEnt.pure (hA.d1 i hi)).mul
      ((SlpEnt.pure (hA.d1 j hj)).mul (SlpEnt.pure (hA.d1 k hk))))).scale (-6) 0 0).add
      ((((SlpEnt.pure hw3).mul (slpCross_ent hA hi hj hk)).scale 2 0 0).add
      (((SlpEnt.pure hw2).mul (SlpEnt.pure (hA.d3 i hi j hj k hk))).scale (-1) 0 0))).congr ?_
    intro z hz
    rw [jetDeriv3_inv hS _ _ _ hf h0 hz]
    beta_reduce
    rw [slpConstVal_rat, slpConstVal_rat, slpConstVal_rat]
    push_cast
    ring
  exact slpFinish_sound hv hval _ _ _ h1 h2 h3

/-- The program of the node of `x ↦ x⁻¹` before its tables: the operations `w = x⁻¹`, `w²`, `w³`,
`w⁴` and the slots of `w²`, `w³`, `w⁴`. -/
def slpInvPre (s : List SlpOp) (A : SlpNode) :
    List SlpOp × Option ℕ × Option ℕ × Option ℕ :=
  let r1 := slpEmit s (.inv A.v)
  let r2 := slpMulO r1.1 r1.2 r1.2
  let r3 := slpMulO r2.1 r1.2 r2.2
  let r4 := slpMulO r3.1 r1.2 r3.2
  (r4.1, r2.2, r3.2, r4.2)

/-- The node of `x ↦ x⁻¹`: the slots `w = x⁻¹`, `w²`, `w³`, `w⁴` follow the operand. -/
def slpInvNode (n : ℕ) (s : List SlpOp) (A : SlpNode) : List SlpOp × SlpNode :=
  slpInvTail n s.length A (slpInvPre s A).2.1 (slpInvPre s A).2.2.1 (slpInvPre s A).2.2.2
    (slpInvPre s A).1

theorem slpInvPre_spec {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {A : SlpNode}
    (hA : A.Sound n S f s) :
    s <+: (slpInvPre s A).1 ∧ s.length < (slpInvPre s A).1.length ∧
      (∀ z, (Slp.vals n z (slpInvPre s A).1).getD s.length 0 = (f z)⁻¹) ∧
      Realizes n S (slpInvPre s A).1 (slpInvPre s A).2.1 (fun z => (f z)⁻¹ * (f z)⁻¹) ∧
      Realizes n S (slpInvPre s A).1 (slpInvPre s A).2.2.1
        (fun z => (f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹)) ∧
      Realizes n S (slpInvPre s A).1 (slpInvPre s A).2.2.2
        (fun z => (f z)⁻¹ * ((f z)⁻¹ * ((f z)⁻¹ * (f z)⁻¹))) := by
  have hp1 : s <+: (slpEmit s (.inv A.v)).1 := slpEmit_prefix _ _
  have hw : Realizes n S (slpEmit s (.inv A.v)).1 (slpEmit s (.inv A.v)).2
      (fun z => (f z)⁻¹) :=
    slpEmit_realizes _ _ _ fun z _ => by simp only [SlpOp.step]; rw [hA.val z]
  obtain ⟨p2, hw2⟩ := slpMulO_spec hw hw
  obtain ⟨p3, hw3⟩ := slpMulO_spec (hw.mono p2) hw2
  obtain ⟨p4, hw4⟩ := slpMulO_spec (hw.mono (p2.trans p3)) hw3
  have hvlt : s.length < (slpEmit s (.inv A.v)).1.length := by simp [slpEmit]
  refine ⟨hp1.trans (p2.trans (p3.trans p4)),
    hvlt.trans_le (p2.trans (p3.trans p4)).length_le, fun z => ?_,
    (hw2.mono p3).mono p4, hw3.mono p4, hw4⟩
  obtain ⟨t, ht⟩ := p2.trans (p3.trans p4)
  show (Slp.vals n z (slpMulO _ _ _).1).getD s.length 0 = _
  rw [← ht, Slp.val_append n z _ t hvlt]
  show (Slp.vals n z (s ++ [SlpOp.inv A.v])).getD s.length 0 = _
  rw [Slp.val_snoc_self]
  simp only [SlpOp.step]
  rw [hA.val z]

theorem slpInvNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (h0 : ∀ z ∈ S, f z ≠ 0) {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) :
    s <+: (slpInvNode n s A).1 ∧
      (slpInvNode n s A).2.Sound n S (fun z => (f z)⁻¹) (slpInvNode n s A).1 := by
  obtain ⟨hp, hvlt, hval, hw2, hw3, hw4⟩ := slpInvPre_spec hA
  obtain ⟨p, h⟩ := slpInvTail_sound hS hf h0 (hA.mono hp) hvlt hval hw2 hw3 hw4
  exact ⟨hp.trans p, h⟩

end KAM.Certificate

end
