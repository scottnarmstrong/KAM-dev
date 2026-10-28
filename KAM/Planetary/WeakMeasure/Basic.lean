/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Interfaces.Norms

/-!
# Weak-measure conventions and amounts (P11A-W0)

Carriers, Euclidean gauges `p11dg`/`p11op`, thickenings, jet bounds, the amount `index_def` and the
least positive index `p11Index`, the patch/hypothesis structures of the sublevel and Diophantine
estimates, and the boundedness/attainment facts (design note N3) that make every supremum and
infimum meaningful before use: no junk value of `sSup`/`sInf` is ever used downstream.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary
abbrev P11Vec (n : ℕ) := Fin n → ℝ
abbrev P11CVec (n : ℕ) := Fin n → ℂ
abbrev P11Phase (n : ℕ) := P11CVec n × P11CVec n
abbrev P11Family (n : ℕ) := P11Phase n × P11CVec n
/-- Explicit Euclidean lengths; retain the existing max norm instances. -/
abbrev p11euclid {n : ℕ} (x : P11Vec n) := KAM.Nekhoroshev.euclid x
def p11dot {m : ℕ} (c w : P11Vec m) : ℝ := ∑ i, c i * w i
def p11dotZ {m : ℕ} (k : Fin m → ℤ) (w : P11Vec m) : ℝ :=
  ∑ i, (k i : ℝ) * w i
def p11dotC {m : ℕ} (k : Fin m → ℤ) (w : P11CVec m) : ℂ :=
  ∑ i, (k i : ℂ) * w i
/-- Closed Euclidean thickening, not max-norm Metric.cthickening. -/
def p11thick {n : ℕ} (K : Set (P11Vec n)) (v : ℝ) : Set (P11Vec n) :=
  {y | ∃ x ∈ K, p11euclid (y - x) ≤ v}
/-- Order zero is evaluated on the unique empty tuple. -/
def p11dg {n m : ℕ} (f : P11Vec n → P11Vec m) (j : ℕ) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ a : P11Vec n, p11euclid a = 1 ∧
    v = p11euclid (iteratedFDeriv ℝ j f y (fun _ => a))}
def p11op {n m : ℕ} (f : P11Vec n → P11Vec m) (j : ℕ) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ a : Fin j → P11Vec n, (∀ i, p11euclid (a i) ≤ 1) ∧
    v = p11euclid (iteratedFDeriv ℝ j f y a)}
def p11scalar {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m)
    (c : P11Vec m) (y : P11Vec n) : P11Vec 1 :=
  fun _ => (p11dot c (w y)) ^ rho
def p11maxJet {n m : ℕ} (mu : ℕ) (f : P11Vec n → P11Vec m) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ j ≤ mu, v = p11dg f j y}
/-- index-def: precisely the scalar-family amount, rho=1 or rho=2. -/
def index_def {n m : ℕ} (rho mu : ℕ) (w : P11Vec n → P11Vec m)
    (K : Set (P11Vec n)) : ℝ :=
  sInf {v | ∃ c : P11Vec m, p11euclid c = 1 ∧
    ∃ y ∈ K, v = p11maxJet mu (p11scalar rho w c) y}
def p11JetBound {n m : ℕ} (diag : Bool) (mu : ℕ) (A : Set (P11Vec n))
    (f : P11Vec n → P11Vec m) (M : ℝ) : Prop :=
  ∀ j ≤ mu, ∀ y ∈ A, (if diag then p11dg f j y else p11op f j y) ≤ M
def p11eta (rho mu : ℕ) (M theta : ℝ) : ℝ :=
  if rho = 1 then theta else (2 : ℝ)^mu * theta * (2*M + theta)
/-- Common source geometry of S1-S3 and D1-D4. -/
structure P11Patch (n : ℕ) where
  K : Set (P11Vec n)
  V : Set (P11Vec n)
  v : ℝ
  n_pos : 1 ≤ n
  nonempty : K.Nonempty
  compact : IsCompact K
  openV : IsOpen V
  diameter_pos : 0 < Metric.diam K
  v_pos : 0 < v
  thick_sub : p11thick K v ⊆ V
/-- All fields are S1-S3, with regularity on the open V. -/
structure P11SublevelHyp {n : ℕ} (P : P11Patch n) (mu : ℕ)
    (g gt : P11Vec n → ℝ) (beta M : ℝ) : Prop where
  mu_pos : 1 ≤ mu
  beta_pos : 0 < beta
  size_ge : beta ≤ M
  g_smooth : ContDiffOn ℝ (mu+1) g P.V
  gt_smooth : ContDiffOn ℝ mu gt P.V
  finite_type : ∀ y ∈ P.K, beta ≤ p11maxJet mu (fun (x : P11Vec n) (_ : Fin 1) => g x) y
  size : ∀ j, 1 ≤ j → j ≤ mu+1 → ∀ y ∈ p11thick P.K P.v,
    p11op (fun (x : P11Vec n) (_ : Fin 1) => g x) j y ≤ M
  close : p11JetBound true mu (p11thick P.K P.v)
    (fun (x : P11Vec n) (_ : Fin 1) => gt x - g x) (beta/2)
def p11Csub (n mu : ℕ) (d v ratio : ℝ) : ℝ :=
  (2 : ℝ)^(n+2) * mu * (Real.sqrt n * d)^(n-1) * ratio *
    (1+(4+v⁻¹)*Real.sqrt n*d)
/-- The source's R-nondegeneracy; this is an interface to Part 10, not a new frozen object. -/
def p11RNondegenerate {n m : ℕ} (V : Set (P11Vec n)) (w : P11Vec n → P11Vec m) : Prop :=
  ∀ c : P11Vec m, c ≠ 0 → ∃ y ∈ V, p11dot c (w y) ≠ 0
/-- The mode-dependent maps live over the original patch, even when retained sets shrink. -/
def p11Good {n m : ℕ} (K : Set (P11Vec n))
    (wt : (Fin m → ℤ) → P11Vec n → P11Vec m) (psi : (Fin m → ℤ) → ℝ) :=
  {y ∈ K | ∀ k, k ≠ 0 → psi k ≤ |p11dotZ k (wt k y)|}
structure P11DioHyp {n m : ℕ} (P : P11Patch n) (rho mu : ℕ)
    (w : P11Vec n → P11Vec m) (wt : (Fin m → ℤ) → P11Vec n → P11Vec m)
    (beta M : ℝ) : Prop where
  m_pos : 1 ≤ m
  mu_pos : 1 ≤ mu
  convention : rho=1 ∨ rho=2
  beta_pos : 0 < beta
  size_ge : beta ≤ M
  regular : ContDiffOn ℝ (mu+1) w P.V
  perturbed_regular : ∀ k, k ≠ 0 → ContDiffOn ℝ mu (wt k) P.V
  amount : beta ≤ index_def rho mu w P.K
  size : ∀ c, p11euclid c=1 → ∀ j, 1 ≤ j → j ≤ mu+1 →
    ∀ y ∈ p11thick P.K P.v, p11op (p11scalar rho w c) j y ≤ M
  close : ∀ k, k ≠ 0 → ∀ c, p11euclid c=1 →
    p11JetBound true mu (p11thick P.K P.v)
      (p11scalar rho (wt k) c-p11scalar rho w c) (beta/2)
/-- The least positive index is meaningful only after rank_compact gives nonempty candidates. -/
def p11Index {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) : ℕ :=
  sInf {mu | 1 ≤ mu ∧ 0 < index_def rho mu w K}
def p11Amount {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) : ℝ :=
  index_def rho (p11Index rho w K) w K
section Attainment

variable {n m : ℕ}

theorem p11euclid_continuous : Continuous (fun x : P11Vec n => p11euclid x) := by
  unfold p11euclid KAM.Nekhoroshev.euclid
  fun_prop

theorem p11euclid_nonneg (x : P11Vec n) : 0 ≤ p11euclid x := Real.sqrt_nonneg _

theorem p11euclid_zero : p11euclid (0 : P11Vec n) = 0 := by
  simp [p11euclid, KAM.Nekhoroshev.euclid]

theorem p11sphere_isCompact : IsCompact {a : P11Vec n | p11euclid a = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq p11euclid_continuous continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : P11Vec n)) (r := 1)).subset fun a ha => ?_
    rw [mem_closedBall_zero_iff]
    exact (KAM.Nekhoroshev.norm_le_euclid a).1.trans ha.le

theorem p11ball_isCompact : IsCompact {a : P11Vec n | p11euclid a ≤ 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_le p11euclid_continuous continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : P11Vec n)) (r := 1)).subset fun a ha => ?_
    rw [mem_closedBall_zero_iff]
    exact (KAM.Nekhoroshev.norm_le_euclid a).1.trans ha

theorem p11sphere_nonempty (hn : 1 ≤ n) : {a : P11Vec n | p11euclid a = 1}.Nonempty := by
  refine ⟨fun i => if i = ⟨0, hn⟩ then 1 else 0, ?_⟩
  simp only [mem_ofPred_eq, p11euclid, KAM.Nekhoroshev.euclid]
  rw [Real.sqrt_eq_one, Finset.sum_eq_single ⟨0, hn⟩] <;> simp +contextual

/-- The tuple set of `p11op` is compact. -/
theorem p11tuple_isCompact (j : ℕ) :
    IsCompact {a : Fin j → P11Vec n | ∀ i, p11euclid (a i) ≤ 1} := by
  have : {a : Fin j → P11Vec n | ∀ i, p11euclid (a i) ≤ 1} =
      Set.pi univ (fun _ => {a : P11Vec n | p11euclid a ≤ 1}) := by
    ext a; simp
  rw [this]
  exact isCompact_univ_pi fun _ => p11ball_isCompact

theorem p11tuple_nonempty (j : ℕ) :
    {a : Fin j → P11Vec n | ∀ i, p11euclid (a i) ≤ 1}.Nonempty :=
  ⟨0, fun i => by simp [p11euclid_zero]⟩

variable (f : P11Vec n → P11Vec m) (j : ℕ) (y : P11Vec n)

private theorem p11dg_set_compact :
    IsCompact {v | ∃ a : P11Vec n, p11euclid a = 1 ∧
      v = p11euclid (iteratedFDeriv ℝ j f y (fun _ => a))} := by
  have hc : Continuous fun a : P11Vec n =>
      p11euclid (iteratedFDeriv ℝ j f y (fun _ => a)) :=
    p11euclid_continuous.comp ((iteratedFDeriv ℝ j f y).cont.comp (by fun_prop))
  have := p11sphere_isCompact.image hc
  convert this using 1
  ext v; simp [eq_comm]

theorem p11dg_nonneg : 0 ≤ p11dg f j y := by
  unfold p11dg
  exact Real.sSup_nonneg fun _ ⟨_, _, hv⟩ => hv ▸ p11euclid_nonneg _

theorem le_p11dg (a : P11Vec n) (ha : p11euclid a = 1) :
    p11euclid (iteratedFDeriv ℝ j f y (fun _ => a)) ≤ p11dg f j y :=
  le_csSup (p11dg_set_compact f j y).bddAbove ⟨a, ha, rfl⟩

theorem p11dg_attained (hn : 1 ≤ n) : ∃ a : P11Vec n, p11euclid a = 1 ∧
    p11dg f j y = p11euclid (iteratedFDeriv ℝ j f y (fun _ => a)) := by
  obtain ⟨a, ha⟩ := p11sphere_nonempty hn
  obtain ⟨b, hb, hv⟩ := (p11dg_set_compact f j y).sSup_mem ⟨_, a, ha, rfl⟩
  exact ⟨b, hb, hv⟩

private theorem p11op_set_compact :
    IsCompact {v | ∃ a : Fin j → P11Vec n, (∀ i, p11euclid (a i) ≤ 1) ∧
      v = p11euclid (iteratedFDeriv ℝ j f y a)} := by
  have hc : Continuous fun a : Fin j → P11Vec n => p11euclid (iteratedFDeriv ℝ j f y a) :=
    p11euclid_continuous.comp (iteratedFDeriv ℝ j f y).cont
  have := (p11tuple_isCompact (n := n) j).image hc
  convert this using 1
  ext v; simp [eq_comm]

theorem p11op_nonneg : 0 ≤ p11op f j y := by
  unfold p11op
  exact Real.sSup_nonneg fun _ ⟨_, _, hv⟩ => hv ▸ p11euclid_nonneg _

theorem le_p11op (a : Fin j → P11Vec n) (ha : ∀ i, p11euclid (a i) ≤ 1) :
    p11euclid (iteratedFDeriv ℝ j f y a) ≤ p11op f j y :=
  le_csSup (p11op_set_compact f j y).bddAbove ⟨a, ha, rfl⟩

theorem p11op_attained : ∃ a : Fin j → P11Vec n, (∀ i, p11euclid (a i) ≤ 1) ∧
    p11op f j y = p11euclid (iteratedFDeriv ℝ j f y a) := by
  obtain ⟨b, hb, hv⟩ := (p11op_set_compact f j y).sSup_mem
    ⟨_, 0, fun i => by simp [p11euclid_zero], rfl⟩
  exact ⟨b, hb, hv⟩

/-- The diagonal gauge is dominated by the operator gauge (unit vectors repeated). -/
theorem p11dg_le_p11op (hn : 1 ≤ n) : p11dg f j y ≤ p11op f j y := by
  obtain ⟨a, ha, h⟩ := p11dg_attained f j y hn
  rw [h]
  exact le_p11op f j y _ fun _ => ha.le

theorem p11maxJet_set_finite (mu : ℕ) : {v | ∃ j ≤ mu, v = p11dg f j y}.Finite := by
  have : {v | ∃ j ≤ mu, v = p11dg f j y} = (fun j => p11dg f j y) '' Set.Iic mu := by
    ext v; simp [eq_comm]
  rw [this]
  exact (Set.finite_Iic mu).image _

theorem le_p11maxJet (mu : ℕ) {j : ℕ} (hj : j ≤ mu) : p11dg f j y ≤ p11maxJet mu f y :=
  le_csSup (p11maxJet_set_finite f y mu).bddAbove ⟨j, hj, rfl⟩

theorem p11maxJet_attained (mu : ℕ) : ∃ j ≤ mu, p11maxJet mu f y = p11dg f j y := by
  obtain ⟨j, hj, e⟩ := (p11maxJet_set_finite f y mu).isCompact.sSup_mem ⟨_, 0, Nat.zero_le _, rfl⟩
  exact ⟨j, hj, e⟩

theorem p11maxJet_nonneg (mu : ℕ) : 0 ≤ p11maxJet mu f y := by
  obtain ⟨j, -, h⟩ := p11maxJet_attained f y mu
  rw [h]; exact p11dg_nonneg f j y

end Attainment

section Amount

variable {n m : ℕ}

theorem index_def_set_nonempty (hm : 1 ≤ m) (rho mu : ℕ) (w : P11Vec n → P11Vec m)
    {K : Set (P11Vec n)} (hK : K.Nonempty) :
    {v | ∃ c : P11Vec m, p11euclid c = 1 ∧
      ∃ y ∈ K, v = p11maxJet mu (p11scalar rho w c) y}.Nonempty := by
  obtain ⟨c, hc⟩ := p11sphere_nonempty hm
  obtain ⟨y, hy⟩ := hK
  exact ⟨_, c, hc, y, hy, rfl⟩

theorem index_def_set_bddBelow (rho mu : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) :
    BddBelow {v | ∃ c : P11Vec m, p11euclid c = 1 ∧
      ∃ y ∈ K, v = p11maxJet mu (p11scalar rho w c) y} :=
  ⟨0, fun _ ⟨_, _, _, _, hv⟩ => hv ▸ p11maxJet_nonneg _ _ _⟩

theorem index_def_nonneg (rho mu : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) :
    0 ≤ index_def rho mu w K := by
  unfold index_def
  exact Real.sInf_nonneg fun _ ⟨_, _, _, _, hv⟩ => hv ▸ p11maxJet_nonneg _ _ _

theorem index_def_le (rho mu : ℕ) (w : P11Vec n → P11Vec m) {K : Set (P11Vec n)}
    {c : P11Vec m} (hc : p11euclid c = 1) {y : P11Vec n} (hy : y ∈ K) :
    index_def rho mu w K ≤ p11maxJet mu (p11scalar rho w c) y :=
  csInf_le (index_def_set_bddBelow rho mu w K) ⟨c, hc, y, hy, rfl⟩

/-- Greatest-lower-bound property, with the nonemptiness gate explicit. -/
theorem le_index_def (hm : 1 ≤ m) (rho mu : ℕ) (w : P11Vec n → P11Vec m)
    {K : Set (P11Vec n)} (hK : K.Nonempty) {b : ℝ}
    (hb : ∀ c : P11Vec m, p11euclid c = 1 → ∀ y ∈ K,
      b ≤ p11maxJet mu (p11scalar rho w c) y) : b ≤ index_def rho mu w K :=
  le_csInf (index_def_set_nonempty hm rho mu w hK) fun _ ⟨c, hc, y, hy, hv⟩ =>
    hv ▸ hb c hc y hy

theorem p11Index_spec {rho : ℕ} {w : P11Vec n → P11Vec m} {K : Set (P11Vec n)}
    (h : ∃ mu : ℕ, 1 ≤ mu ∧ 0 < index_def rho mu w K) :
    1 ≤ p11Index rho w K ∧ 0 < index_def rho (p11Index rho w K) w K :=
  Nat.sInf_mem (s := {mu | 1 ≤ mu ∧ 0 < index_def rho mu w K}) h

theorem p11Index_le {rho mu : ℕ} {w : P11Vec n → P11Vec m} {K : Set (P11Vec n)}
    (h1 : 1 ≤ mu) (h : 0 < index_def rho mu w K) : p11Index rho w K ≤ mu :=
  Nat.sInf_le (s := {mu | 1 ≤ mu ∧ 0 < index_def rho mu w K}) ⟨h1, h⟩

theorem p11Amount_pos {rho : ℕ} {w : P11Vec n → P11Vec m} {K : Set (P11Vec n)}
    (h : ∃ mu : ℕ, 1 ≤ mu ∧ 0 < index_def rho mu w K) : 0 < p11Amount rho w K :=
  (p11Index_spec h).2

end Amount

section Joint

open scoped Pointwise

variable {n m : ℕ}

private theorem p11slice_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : P11Vec m × P11Vec n → E} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hG : ContDiffOn ℝ j G (univ ×ˢ V)) (c : P11Vec m) {y : P11Vec n} (hy : y ∈ V) :
    iteratedFDeriv ℝ j (fun y => G (c, y)) y =
      (iteratedFDeriv ℝ j G (c, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)) := by
  have hso : IsOpen (univ ×ˢ V : Set (P11Vec m × P11Vec n)) := isOpen_univ.prod hV
  set a : P11Vec m × P11Vec n := (c, 0) with ha
  set t : Set (P11Vec m × P11Vec n) := (fun z => z + a) ⁻¹' (univ ×ˢ V) with ht
  have hto : IsOpen t := hso.preimage (continuous_id.add continuous_const)
  have hfc : ContDiffOn ℝ j (fun z => G (z + a)) t :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hin : ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n) y ∈ t := by
    simp [ht, ha, hy]
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)) hfc hto.uniqueDiffOn
    (hto.preimage (ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)).continuous).uniqueDiffOn
    hin (i := j) le_rfl
  have hfun : ((fun z => G (z + a)) ∘ ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)) =
      fun y => G (c, y) := by
    funext y; simp [ha]
  have hvadd : a +ᵥ t = univ ×ˢ V := by
    ext z
    simp only [mem_vadd_set, vadd_eq_add, ht, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [add_comm]  at hx
    · intro hz; exact ⟨z - a, by simpa using hz, by simp⟩
  rw [hfun] at h1
  rw [iteratedFDerivWithin_comp_add_right, hvadd] at h1
  have hop : IsOpen (ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n) ⁻¹' t) :=
    hto.preimage (ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)).continuous
  rw [iteratedFDerivWithin_of_isOpen _ hop hin,
    iteratedFDerivWithin_of_isOpen _ hso (by simpa [ha] using hy)] at h1
  have hin2 : (ContinuousLinearMap.inr ℝ (P11Vec m) (P11Vec n)) y + a = (c, y) := by simp [ha]
  rw [hin2] at h1
  exact h1

private def p11jointFamily (rho : ℕ) (w : P11Vec n → P11Vec m) (p : P11Vec m × P11Vec n) :
    P11Vec 1 := p11scalar rho w p.1 p.2

private theorem p11joint_contDiffOn {rho mu : ℕ} {w : P11Vec n → P11Vec m} {V : Set (P11Vec n)}
    (hw : ContDiffOn ℝ mu w V) :
    ContDiffOn ℝ mu (p11jointFamily rho w) (univ ×ˢ V) := by
  refine contDiffOn_pi.2 fun _ => ?_
  have hd : ContDiffOn ℝ mu (fun p : P11Vec m × P11Vec n => p11dot p.1 (w p.2))
      (univ ×ˢ V) := by
    unfold p11dot
    refine ContDiffOn.sum fun i _ => ContDiffOn.mul ?_ ?_
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).contDiff.comp
        contDiff_fst).contDiffOn
    · exact (contDiffOn_pi.1 hw i).comp contDiffOn_snd fun p hp => hp.2
  exact hd.pow rho

/-- The unit-direction jet value is jointly continuous in `(c, y, a)`. -/
private theorem p11joint_term_continuousOn {rho mu : ℕ} {w : P11Vec n → P11Vec m}
    {V : Set (P11Vec n)} (hV : IsOpen V) (hw : ContDiffOn ℝ mu w V) {j : ℕ} (hj : j ≤ mu) :
    ContinuousOn (fun q : (P11Vec m × P11Vec n) × P11Vec n =>
      p11euclid (iteratedFDeriv ℝ j (p11scalar rho w q.1.1) q.1.2 (fun _ => q.2)))
      ((univ ×ˢ V) ×ˢ univ) := by
  have hG := (p11joint_contDiffOn (rho := rho) hw).of_le (m := j) (by exact_mod_cast hj)
  have hso : IsOpen (univ ×ˢ V : Set (P11Vec m × P11Vec n)) := isOpen_univ.prod hV
  have hc : ContinuousOn (iteratedFDeriv ℝ j (p11jointFamily rho w)) (univ ×ˢ V) :=
    (hG.continuousOn_iteratedFDerivWithin le_rfl hso.uniqueDiffOn).congr
      fun x hx => (iteratedFDerivWithin_of_isOpen j hso hx).symm
  have hev : ContinuousOn (fun q : (P11Vec m × P11Vec n) × P11Vec n =>
      iteratedFDeriv ℝ j (p11jointFamily rho w) q.1 (fun _ => (0, q.2)))
      ((univ ×ˢ V) ×ˢ univ) := by
    refine ContinuousOn.eval (hc.comp continuousOn_fst fun q hq => hq.1) ?_
    fun_prop
  refine p11euclid_continuous.comp_continuousOn (hev.congr fun q hq => ?_)
  have := p11slice_iteratedFDeriv hV hG q.1.1 hq.1.2
  change _ = (iteratedFDeriv ℝ j (p11jointFamily rho w) q.1) _
  have e : p11scalar rho w q.1.1 = fun y => p11jointFamily rho w (q.1.1, y) := rfl
  rw [e, this]
  rfl

private theorem p11sphere_sSup_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    (T : X → P11Vec n → ℝ) (hT : ContinuousOn (fun q : X × P11Vec n => T q.1 q.2) (S ×ˢ univ)) :
    ContinuousOn (fun x => sSup (T x '' {a : P11Vec n | p11euclid a = 1})) S := by
  have hcont : Continuous (fun x : S => sSup (T x.1 '' {a : P11Vec n | p11euclid a = 1})) :=
    p11sphere_isCompact.continuous_sSup (f := fun (x : S) (a : P11Vec n) => T x.1 a)
      (hT.comp_continuous (continuous_subtype_val.prodMap continuous_id) fun x => ⟨x.1.2, trivial⟩)
  exact continuousOn_iff_continuous_domRestrict.2 hcont

private theorem p11joint_dg_continuousOn {rho mu : ℕ} {w : P11Vec n → P11Vec m}
    {V : Set (P11Vec n)} (hV : IsOpen V) (hw : ContDiffOn ℝ mu w V) {j : ℕ} (hj : j ≤ mu) :
    ContinuousOn (fun p : P11Vec m × P11Vec n => p11dg (p11scalar rho w p.1) j p.2)
      (univ ×ˢ V) := by
  have h := p11sphere_sSup_continuousOn (S := univ ×ˢ V)
    (fun (p : P11Vec m × P11Vec n) (a : P11Vec n) =>
      p11euclid (iteratedFDeriv ℝ j (p11scalar rho w p.1) p.2 (fun _ => a)))
    (p11joint_term_continuousOn hV hw hj)
  refine h.congr fun p _ => ?_
  simp only [p11dg]
  congr 1
  ext v; simp [eq_comm]

private theorem p11sSup_range_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    (d : ℕ → X → ℝ) (mu : ℕ) (hd : ∀ j ≤ mu, ContinuousOn (d j) S) :
    ContinuousOn (fun x => sSup {v | ∃ j ≤ mu, v = d j x}) S := by
  induction mu with
  | zero =>
    refine (hd 0 (Nat.zero_le _)).congr fun x _ => ?_
    have : {v | ∃ j ≤ 0, v = d j x} = {d 0 x} := by ext v; simp
    rw [this, csSup_singleton]
  | succ k ih =>
    have hih := ih fun j hj => hd j (hj.trans (Nat.le_succ _))
    refine (continuous_max.comp_continuousOn
      (hih.prodMk (hd (k + 1) le_rfl))).congr fun x _ => ?_
    have : {v | ∃ j ≤ k + 1, v = d j x} = insert (d (k + 1) x) {v | ∃ j ≤ k, v = d j x} := by
      ext v
      simp only [mem_ofPred_eq, mem_insert_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rcases Nat.lt_or_ge j (k + 1) with h | h
        · exact Or.inr ⟨j, Nat.lt_succ_iff.1 h, rfl⟩
        · exact Or.inl (by rw [le_antisymm hj h])
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨k + 1, le_rfl, rfl⟩
        · exact ⟨j, hj.trans (Nat.le_succ _), rfl⟩
    rw [this, csSup_insert]
    · exact max_comm _ _
    · exact (Set.finite_Iic k |>.image (fun j => d j x)).bddAbove.mono (by
        intro v ⟨j, hj, hv⟩; exact ⟨j, hj, hv.symm⟩)
    · exact ⟨d 0 x, 0, Nat.zero_le _, rfl⟩

/-- The finite maximum over orders is jointly continuous in `(c, y)` on `ℝ^m × V`. -/
theorem p11maxJet_joint_continuousOn {rho mu : ℕ} {w : P11Vec n → P11Vec m}
    {V : Set (P11Vec n)} (hV : IsOpen V) (hw : ContDiffOn ℝ mu w V) :
    ContinuousOn (fun p : P11Vec m × P11Vec n => p11maxJet mu (p11scalar rho w p.1) p.2)
      (univ ×ˢ V) := by
  have h := p11sSup_range_continuousOn (X := P11Vec m × P11Vec n) (S := univ ×ˢ V)
    (fun j p => p11dg (p11scalar rho w p.1) j p.2) mu
    fun _ hj => p11joint_dg_continuousOn (rho := rho) hV hw hj
  exact h

/-- The index-def parameter set: unit coefficients times the patch. -/
theorem index_def_params_isCompact {K : Set (P11Vec n)} (hK : IsCompact K) :
    IsCompact ({c : P11Vec m | p11euclid c = 1} ×ˢ K) :=
  p11sphere_isCompact.prod hK

theorem index_def_params_nonempty (hm : 1 ≤ m) {K : Set (P11Vec n)} (hK : K.Nonempty) :
    ({c : P11Vec m | p11euclid c = 1} ×ˢ K).Nonempty :=
  (p11sphere_nonempty hm).prod hK

/-- The infimum in `index_def` is a minimum: an actual minimizing `(c, y)` exists. -/
theorem index_def_attained (hm : 1 ≤ m) (rho mu : ℕ) {w : P11Vec n → P11Vec m}
    {V K : Set (P11Vec n)} (hV : IsOpen V) (hw : ContDiffOn ℝ mu w V) (hKc : IsCompact K)
    (hKV : K ⊆ V) (hK : K.Nonempty) :
    ∃ c : P11Vec m, p11euclid c = 1 ∧ ∃ y ∈ K,
      index_def rho mu w K = p11maxJet mu (p11scalar rho w c) y := by
  have hsub : ({c : P11Vec m | p11euclid c = 1} ×ˢ K) ⊆ univ ×ˢ V :=
    fun p hp => ⟨trivial, hKV hp.2⟩
  have hcont : ContinuousOn
      (fun p : P11Vec m × P11Vec n => p11maxJet mu (p11scalar rho w p.1) p.2)
      ({c : P11Vec m | p11euclid c = 1} ×ˢ K) :=
    (p11maxJet_joint_continuousOn (rho := rho) hV hw).mono hsub
  have hc0 := index_def_params_isCompact (m := m) hKc
  have hne := index_def_params_nonempty hm hK
  obtain ⟨p, hp, hmin⟩ := hc0.exists_isMinOn hne hcont
  have hc : p11euclid p.1 = 1 := (Set.mem_prod.1 hp).1
  have hy : p.2 ∈ K := (Set.mem_prod.1 hp).2
  refine ⟨p.1, hc, p.2, hy, ?_⟩
  unfold index_def
  refine IsLeast.csInf_eq ⟨⟨p.1, hc, p.2, hy, rfl⟩, ?_⟩
  intro v hv
  obtain ⟨c', hc', y', hy', hv'⟩ := hv
  have hmem : (c', y') ∈ {c : P11Vec m | p11euclid c = 1} ×ˢ K := Set.mem_prod.2 ⟨hc', hy'⟩
  have h2 := isMinOn_iff.1 hmin _ hmem
  rw [hv']
  exact h2

end Joint

end KAM.Planetary
