/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Stability of the amount and size bound for the scalar families (P11A-W1)

`stability` and `M_bound`: iterated Leibniz formulas (diagonal, via the line `t ↦ y + t a`, and the
operator-norm form on `EuclideanSpace`, used only as an internal bridge) and Cauchy-Schwarz.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Euclid

variable {n m : ℕ}

/-- The identification of `P11Vec n` with `EuclideanSpace` (internal bridge only). -/
def p11toE : P11Vec n ≃L[ℝ] EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm

theorem p11euclid_eq_norm (x : P11Vec n) : p11euclid x = ‖p11toE x‖ := by
  simp [p11toE, p11euclid, KAM.Nekhoroshev.euclid, EuclideanSpace.norm_eq]

theorem p11euclid_add_le (x y : P11Vec n) : p11euclid (x + y) ≤ p11euclid x + p11euclid y := by
  simp only [p11euclid_eq_norm, map_add]
  exact norm_add_le _ _

theorem p11euclid_sub_le (x y : P11Vec n) : p11euclid (x - y) ≤ p11euclid x + p11euclid y := by
  simp only [p11euclid_eq_norm, map_sub]
  exact (norm_sub_le _ _)

theorem p11euclid_one (r : ℝ) : p11euclid (fun _ : Fin 1 => r) = |r| := by
  simp [p11euclid, KAM.Nekhoroshev.euclid, Real.sqrt_sq_eq_abs]

theorem abs_p11dot_le (c v : P11Vec m) : |p11dot c v| ≤ p11euclid c * p11euclid v := by
  simp only [p11euclid_eq_norm]
  have := abs_real_inner_le_norm (p11toE c) (p11toE v)
  convert this using 2
  simp [p11dot, p11toE, PiLp.inner_apply, mul_comm]

end Euclid

section Jets

variable {n m : ℕ}

/-- The coefficient functional `v ↦ p11dot c v` as a continuous linear map. -/
def p11lin (c : P11Vec m) : P11Vec m →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i

theorem p11lin_apply (c v : P11Vec m) : p11lin c v = p11dot c v := by
  simp [p11lin, p11dot]

/-- Embedding of scalars as `P11Vec 1`. -/
def p11const : ℝ →L[ℝ] P11Vec 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

theorem p11const_apply (r : ℝ) : p11const r = fun _ => r := rfl

theorem iteratedFDeriv_dot {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) (c : P11Vec m) (a : Fin j → P11Vec n) :
    iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y a = p11dot c (iteratedFDeriv ℝ j w y a) := by
  have := (p11lin c).iteratedFDeriv_comp_left hw (i := j) le_rfl
  have h2 : (fun x => p11dot c (w x)) = (p11lin c) ∘ w := by
    funext x; simp [p11lin_apply]
  rw [h2, this]
  simp [p11lin_apply]

theorem abs_iteratedFDeriv_dot_le {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) (c : P11Vec m) (a : Fin j → P11Vec n) :
    |iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y a| ≤
      p11euclid c * p11euclid (iteratedFDeriv ℝ j w y a) := by
  rw [iteratedFDeriv_dot hw]
  exact abs_p11dot_le _ _

theorem p11euclid_iteratedFDeriv_scalar {g : P11Vec n → ℝ} {y : P11Vec n} {j : ℕ}
    (hg : ContDiffAt ℝ j g y) (a : Fin j → P11Vec n) :
    p11euclid (iteratedFDeriv ℝ j (fun x => (fun _ : Fin 1 => g x)) y a) =
      |iteratedFDeriv ℝ j g y a| := by
  have h := p11const.iteratedFDeriv_comp_left hg (i := j) le_rfl
  have h2 : (fun x => (fun _ : Fin 1 => g x)) = p11const ∘ g := by
    funext x; rfl
  rw [h2, h]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact p11euclid_one _

/-- Diagonal gauge of a scalar function (as a `P11Vec 1`-valued one) from unit-direction bounds. -/
theorem p11dg_scalar_le {g : P11Vec n → ℝ} {y : P11Vec n} {j : ℕ}
    (hg : ContDiffAt ℝ j g y) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a : P11Vec n, p11euclid a = 1 → |iteratedFDeriv ℝ j g y (fun _ => a)| ≤ B) :
    p11dg (fun x => (fun _ : Fin 1 => g x)) j y ≤ B := by
  unfold p11dg
  refine Real.sSup_le ?_ hB
  rintro v ⟨a, ha, rfl⟩
  rw [p11euclid_iteratedFDeriv_scalar hg]
  exact h a ha

theorem abs_jet_dot_le_of_p11dg {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) {c : P11Vec m} (hc : p11euclid c = 1) {B : ℝ}
    (hB : p11dg w j y ≤ B) (a : P11Vec n) (ha : p11euclid a = 1) :
    |iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y (fun _ => a)| ≤ B := by
  refine (abs_iteratedFDeriv_dot_le hw c _).trans ?_
  rw [hc, one_mul]
  exact (le_p11dg w j y a ha).trans hB

end Jets

section Leibniz

variable {n : ℕ}

private theorem p11line_isOpen {V : Set (P11Vec n)} (hV : IsOpen V) (y a : P11Vec n) :
    IsOpen ((ContinuousLinearMap.toSpanSingleton ℝ a) ⁻¹' ((fun z => y + z) ⁻¹' V)) :=
  (hV.preimage (continuous_const.add continuous_id)).preimage (ContinuousLinearMap.continuous _)

/-- The `j`-th derivative of `f` along the line `t ↦ y + t a` is the diagonal jet. -/
theorem p11line_iteratedDeriv {f : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) {y : P11Vec n} (hy : y ∈ V) (a : P11Vec n) :
    iteratedDeriv j (fun t : ℝ => f (y + t • a)) 0 = iteratedFDeriv ℝ j f y (fun _ => a) := by
  set g := ContinuousLinearMap.toSpanSingleton ℝ a with hg
  set V' : Set (P11Vec n) := (fun z => y + z) ⁻¹' V with hV'
  have hV'o : IsOpen V' := hV.preimage (continuous_const.add continuous_id)
  have hf' : ContDiffOn ℝ j (fun z => f (y + z)) V' :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have h0 : g 0 ∈ V' := by simpa [hV'] using hy
  have h1 := g.iteratedFDerivWithin_comp_right hf' hV'o.uniqueDiffOn
    (p11line_isOpen hV y a).uniqueDiffOn h0 (i := j) le_rfl
  have h0' : (0 : ℝ) ∈ (ContinuousLinearMap.toSpanSingleton ℝ a) ⁻¹' V' := by
    simpa [hg, hV'] using hy
  rw [iteratedFDerivWithin_of_isOpen _ (p11line_isOpen hV y a) h0',
    iteratedFDerivWithin_of_isOpen _ hV'o h0] at h1
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have e : (fun t : ℝ => f (y + t • a)) = (fun z => f (y + z)) ∘ g := by
    funext t; simp [hg]
  rw [e, h1, iteratedFDeriv_comp_add_left]
  simp [hg]

theorem p11line_contDiffAt {f : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) {y : P11Vec n} (hy : y ∈ V) (a : P11Vec n) :
    ContDiffAt ℝ j (fun t : ℝ => f (y + t • a)) 0 := by
  have h1 : ContDiffAt ℝ j f (y + (0 : ℝ) • a) := by
    simpa using hf.contDiffAt (hV.mem_nhds hy)
  exact h1.comp (0 : ℝ) (by fun_prop)

/-- Iterated Leibniz formula for equal arguments (`bpP:p11a:f-leib`, diagonal form). -/
theorem p11leibniz_diag {f h : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) (hh : ContDiffOn ℝ j h V) {y : P11Vec n} (hy : y ∈ V)
    (a : P11Vec n) :
    iteratedFDeriv ℝ j (fun x => f x * h x) y (fun _ => a) =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        iteratedFDeriv ℝ i f y (fun _ => a) * iteratedFDeriv ℝ (j - i) h y (fun _ => a) := by
  have hfh : ContDiffOn ℝ j (fun x => f x * h x) V := hf.mul hh
  rw [← p11line_iteratedDeriv hV hfh hy a]
  have e : (fun t : ℝ => f (y + t • a) * h (y + t • a)) =
      (fun t : ℝ => f (y + t • a)) * (fun t : ℝ => h (y + t • a)) := rfl
  rw [e, iteratedDeriv_mul (p11line_contDiffAt hV hf hy a) (p11line_contDiffAt hV hh hy a)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [p11line_iteratedDeriv hV (hf.of_le (by exact_mod_cast hi')) hy a,
    p11line_iteratedDeriv hV (hh.of_le (by exact_mod_cast Nat.sub_le j i)) hy a]

end Leibniz

section Stability

variable {n m : ℕ}

theorem p11eta_nonneg {rho mu : ℕ} {M theta : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ theta) :
    0 ≤ p11eta rho mu M theta := by
  unfold p11eta
  split_ifs
  · exact ht
  · positivity

theorem contDiffOn_p11dot {w : P11Vec n → P11Vec m} {V : Set (P11Vec n)} {mu : ℕ}
    (hw : ContDiffOn ℝ mu w V) (c : P11Vec m) : ContDiffOn ℝ mu (fun x => p11dot c (w x)) V := by
  have := (p11lin c).contDiff.comp_contDiffOn hw
  simpa [Function.comp_def, p11lin_apply] using this

/-- Difference of the scalar families, in the `P11Vec 1`-valued form. -/
theorem p11scalar_sub_eq {rho : ℕ} (hp : rho = 1 ∨ rho = 2) (w wt : P11Vec n → P11Vec m)
    (c : P11Vec m) :
    p11scalar rho wt c - p11scalar rho w c = fun x _ =>
      if rho = 1 then p11dot c ((wt - w) x)
      else p11dot c ((wt - w) x) * (p11dot c ((wt - w) x) + 2 * p11dot c (w x)) := by
  have hd : ∀ x, p11dot c (wt x) = p11dot c ((wt - w) x) + p11dot c (w x) := by
    intro x
    simp [p11dot, mul_sub]
  funext x i
  rcases hp with rfl | rfl
  · simp [p11scalar, hd]
  · simp [p11scalar, hd]; ring

/-- First conclusion of `stability`: the jet bound for the error families. -/
theorem stability_jet {V A : Set (P11Vec n)} (hV : IsOpen V) (hAV : A ⊆ V)
    {rho mu : ℕ} (hp : rho = 1 ∨ rho = 2) {w wt : P11Vec n → P11Vec m}
    (hw : ContDiffOn ℝ mu w V) (hwt : ContDiffOn ℝ mu wt V)
    {M theta : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ theta)
    (hb : p11JetBound true mu A w M) (he : p11JetBound true mu A (wt - w) theta)
    {c : P11Vec m} (hc : p11euclid c = 1) :
    p11JetBound true mu A (p11scalar rho wt c - p11scalar rho w c) (p11eta rho mu M theta) := by
  intro j hj y hy
  have hyV := hAV hy
  have hdiff : ContDiffOn ℝ mu (wt - w) V := hwt.sub hw
  have hs := contDiffOn_p11dot hdiff c
  have htt := contDiffOn_p11dot hw c
  have hat : ∀ {k : ℕ}, k ≤ mu → ∀ {g : P11Vec n → ℝ}, ContDiffOn ℝ mu g V → ContDiffAt ℝ k g y :=
    fun hk g hg => (hg.of_le (by exact_mod_cast hk)).contDiffAt (hV.mem_nhds hyV)
  have hat' : ∀ {k : ℕ}, k ≤ mu → ∀ {g : P11Vec n → P11Vec m}, ContDiffOn ℝ mu g V →
      ContDiffAt ℝ k g y :=
    fun hk g hg => (hg.of_le (by exact_mod_cast hk)).contDiffAt (hV.mem_nhds hyV)
  have hsb : ∀ k ≤ mu, ∀ a : P11Vec n, p11euclid a = 1 →
      |iteratedFDeriv ℝ k (fun x => p11dot c ((wt - w) x)) y (fun _ => a)| ≤ theta :=
    fun k hk a ha => abs_jet_dot_le_of_p11dg (hat' hk hdiff) hc (he k hk y hy) a ha
  have htb : ∀ k ≤ mu, ∀ a : P11Vec n, p11euclid a = 1 →
      |iteratedFDeriv ℝ k (fun x => p11dot c (w x)) y (fun _ => a)| ≤ M :=
    fun k hk a ha => abs_jet_dot_le_of_p11dg (hat' hk hw) hc (hb k hk y hy) a ha
  rw [p11scalar_sub_eq hp]
  have hη := p11eta_nonneg (rho := rho) (mu := mu) hM ht
  rcases hp with rfl | rfl
  · simp only [ite_true]
    refine p11dg_scalar_le (hat hj hs) (by simpa [p11eta] using ht) fun a ha => ?_
    simpa [p11eta] using hsb j hj a ha
  · simp only [p11eta, show (2 : ℕ) ≠ 1 by norm_num]
    simp only [p11eta, show (2 : ℕ) ≠ 1 by norm_num] at hη
    set s : P11Vec n → ℝ := fun x => p11dot c ((wt - w) x) with hsdef
    set t : P11Vec n → ℝ := fun x => p11dot c (w x) with htdef
    have hh : ContDiffOn ℝ mu (fun x => s x + 2 * t x) V := hs.add (contDiffOn_const.mul htt)
    refine p11dg_scalar_le (hat hj (hs.mul hh)) hη fun a ha => ?_
    rw [p11leibniz_diag hV (hs.of_le (by exact_mod_cast hj)) (hh.of_le (by exact_mod_cast hj)) hyV]
    have hhb : ∀ k ≤ mu, |iteratedFDeriv ℝ k (fun x => s x + 2 * t x) y (fun _ => a)| ≤
        theta + 2 * M := by
      intro k hk
      have e : (fun x => s x + 2 * t x) = s + (2 : ℝ) • t := by
        funext x; simp
      rw [e, iteratedFDeriv_add_apply (hat hk hs)
        (show ContDiffAt ℝ k ((2 : ℝ) • t) y from (hat hk htt).const_smul (2 : ℝ)),
        iteratedFDeriv_const_smul_apply (hat hk htt)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add (hsb k hk a ha) ?_)
      rw [abs_mul]
      have := htb k hk a ha
      norm_num
      linarith
    calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (theta * (theta + 2 * M)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [abs_mul, abs_mul, Nat.abs_cast]
          have h1 := hsb i (hi'.trans hj) a ha
          have h2 := hhb (j - i) ((Nat.sub_le _ _).trans hj)
          have := mul_le_mul h1 h2 (abs_nonneg _) ht
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 ^ j * (theta * (theta + 2 * M)) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]; push_cast; rfl
      _ ≤ 2 ^ mu * theta * (2 * M + theta) := by
          have : (2 : ℝ) ^ j ≤ 2 ^ mu := pow_le_pow_right₀ (by norm_num) hj
          have h0 : 0 ≤ theta * (theta + 2 * M) := by positivity
          nlinarith

theorem contDiffOn_p11scalar {w : P11Vec n → P11Vec m} {V : Set (P11Vec n)} {mu : ℕ}
    (hw : ContDiffOn ℝ mu w V) (rho : ℕ) (c : P11Vec m) :
    ContDiffOn ℝ mu (p11scalar rho w c) V :=
  contDiffOn_pi.2 fun _ => (contDiffOn_p11dot hw c).pow rho

/-- Triangle inequality for the diagonal gauge. -/
theorem p11dg_le_add {f g : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hf : ContDiffAt ℝ j f y) (hg : ContDiffAt ℝ j g y) :
    p11dg f j y ≤ p11dg g j y + p11dg (g - f) j y := by
  have hgf : ContDiffAt ℝ j (g - f) y := hg.sub hf
  have e : g - (g - f) = f := by funext x; simp
  have h := iteratedFDeriv_sub_apply hg hgf
  rw [e] at h
  unfold p11dg
  refine Real.sSup_le ?_ (add_nonneg (p11dg_nonneg _ _ _) (p11dg_nonneg _ _ _))
  rintro v ⟨a, ha, rfl⟩
  rw [h]
  simp only [sub_apply]
  exact (p11euclid_sub_le _ _).trans (add_le_add (le_p11dg g j y a ha) (le_p11dg _ j y a ha))

theorem p11maxJet_le_add {f g : P11Vec n → P11Vec m} {y : P11Vec n} {mu : ℕ} {eta : ℝ}
    (hf : ∀ j ≤ mu, ContDiffAt ℝ j f y) (hg : ∀ j ≤ mu, ContDiffAt ℝ j g y)
    (h : ∀ j ≤ mu, p11dg (g - f) j y ≤ eta) :
    p11maxJet mu f y ≤ p11maxJet mu g y + eta := by
  obtain ⟨j, hj, e⟩ := p11maxJet_attained f y mu
  rw [e]
  exact (p11dg_le_add (hf j hj) (hg j hj)).trans (add_le_add (le_p11maxJet g y mu hj) (h j hj))

/-- `bpP:p11a:stability`. -/
theorem stability {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V A K : Set (P11Vec n)} (hV : IsOpen V) (hAV : A ⊆ V)
    (hKA : K ⊆ A) (hK : IsCompact K) (hne : K.Nonempty)
    {rho mu : ℕ} (hp : rho=1 ∨ rho=2) {w wt : P11Vec n → P11Vec m}
    (hw : ContDiffOn ℝ mu w V) (hwt : ContDiffOn ℝ mu wt V)
    {M theta : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ theta)
    (hb : p11JetBound true mu A w M) (he : p11JetBound true mu A (wt-w) theta) :
    (∀ c, p11euclid c=1 → p11JetBound true mu A
      (p11scalar rho wt c-p11scalar rho w c) (p11eta rho mu M theta)) ∧
    index_def rho mu w K - p11eta rho mu M theta ≤ index_def rho mu wt K := by
  have h1 : ∀ c, p11euclid c=1 → p11JetBound true mu A
      (p11scalar rho wt c-p11scalar rho w c) (p11eta rho mu M theta) :=
    fun c hc => stability_jet hV hAV hp hw hwt hM ht hb he hc
  refine ⟨h1, ?_⟩
  refine le_index_def hm rho mu wt hne fun c hc y hy => ?_
  have hyV := hAV (hKA hy)
  have hat : ∀ {g : P11Vec n → P11Vec 1}, ContDiffOn ℝ mu g V → ∀ j ≤ mu, ContDiffAt ℝ j g y :=
    fun hg j hj => (hg.of_le (by exact_mod_cast hj)).contDiffAt (hV.mem_nhds hyV)
  have := p11maxJet_le_add (f := p11scalar rho w c) (g := p11scalar rho wt c)
    (hat (contDiffOn_p11scalar hw rho c)) (hat (contDiffOn_p11scalar hwt rho c))
    (eta := p11eta rho mu M theta) (y := y) (mu := mu) ?_
  · have h2 := index_def_le rho mu w hc hy
    linarith
  · exact fun j hj => h1 c hc j hj y (hKA hy)

end Stability

section OperatorBound

variable {n m : ℕ}

theorem p11euclid_symm (b : EuclideanSpace ℝ (Fin n)) : p11euclid (p11toE.symm b) = ‖b‖ := by
  rw [p11euclid_eq_norm]; simp

theorem opNorm_le_of_unit {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ b : Fin k → E, (∀ i, ‖b i‖ ≤ 1) → ‖f b‖ ≤ B) : ‖f‖ ≤ B := by
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun b => ?_
  by_cases h0 : ∃ i, b i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [f.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hB (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at h0
    have hpos : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (h0 i)
    set b' : Fin k → E := fun i => (‖b i‖)⁻¹ • b i with hb'
    have hb1 : ∀ i, ‖b' i‖ ≤ 1 := fun i => by
      simp [hb', norm_smul, (hpos i).ne']
    have hbb : b = fun i => ‖b i‖ • b' i := by
      funext i; simp [hb', smul_smul, (hpos i).ne']
    have : f b = (∏ i, ‖b i‖) • f b' := by
      conv_lhs => rw [hbb]
      exact f.map_smul_univ _ _
    rw [this, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (h b' hb1) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem iteratedFDeriv_comp_fromE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P11Vec n → F) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (f ∘ p11toE.symm) x =
      (iteratedFDeriv ℝ j f (p11toE.symm x)).compContinuousLinearMap
        fun _ => (p11toE (n := n)).symm.toContinuousLinearMap := by
  have := p11toE.symm.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (mem_univ (p11toE.symm x)) j
  simpa [iteratedFDerivWithin_univ] using this

theorem norm_comp_dot_le {w : P11Vec n → P11Vec m} {y : P11Vec n} {k : ℕ}
    {c : P11Vec m} (hc : p11euclid c = 1) {M : ℝ} (hM : 0 ≤ M) (hw : ContDiffAt ℝ k w y)
    (hop : p11op w k y ≤ M) :
    ‖iteratedFDeriv ℝ k ((fun x => p11dot c (w x)) ∘ p11toE.symm) (p11toE y)‖ ≤ M := by
  rw [iteratedFDeriv_comp_fromE]
  refine opNorm_le_of_unit _ hM fun b hb => ?_
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, Real.norm_eq_abs]
  refine (abs_iteratedFDeriv_dot_le hw c _).trans ?_
  rw [hc, one_mul]
  exact (le_p11op w k y _ fun i => by rw [p11euclid_symm]; exact hb i).trans hop

theorem p11op_scalar_le {g : P11Vec n → ℝ} {y : P11Vec n} {j : ℕ} (hg : ContDiffAt ℝ j g y)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ‖iteratedFDeriv ℝ j (g ∘ p11toE.symm) (p11toE y)‖ ≤ B) :
    p11op (fun x => (fun _ : Fin 1 => g x)) j y ≤ B := by
  unfold p11op
  refine Real.sSup_le ?_ hB
  rintro v ⟨a, ha, rfl⟩
  rw [p11euclid_iteratedFDeriv_scalar hg]
  have e : iteratedFDeriv ℝ j g y a =
      iteratedFDeriv ℝ j (g ∘ p11toE.symm) (p11toE y) (fun i => p11toE (a i)) := by
    rw [iteratedFDeriv_comp_fromE]
    simp
  rw [e, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have hp : ∏ i, ‖p11toE (a i)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => by
      rw [← p11euclid_eq_norm]; exact ha i
  calc _ ≤ B * ∏ i, ‖p11toE (a i)‖ :=
        mul_le_mul_of_nonneg_right h (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ ≤ B := by nlinarith

end OperatorBound

end KAM.Planetary
