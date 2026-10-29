/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.ChartScaling

/-!
# Amount transfer helpers (P11A-P8c, `bpP:p11:amount`)

Parametric exported helpers for the steps of `bpP:p11:amount` (they are not the signed `amount`):

* `amount_norm` (`stepP:p11:am-norm`): `beta_{2,mu}(diag(1, eps) w, K) ≥ eps^2 beta_{2,mu}(w, K)`.
* `amount_dir` (`stepP:p11:am-dir`): the stability transfer in the action variable `J`.
* `amount_scale` (`stepP:p11:am-scale`): the `eps^nu` rescaling of the `J`-derivatives in the
  directions `(a, 0)`, giving `eps^mu b ≤` the full tensor norm at `(r, rho')`.
* `amount_transfer`: the combination, `(1/2) eps^(mu+2) beta_J ≤ index_def 2 mu (diag(1, eps) w) K`.

The prepared conclusions the signed `amount` consumes enter only as hypotheses of the shape
produced by `bpP:p11:prepared` (c) and `bpP:p11:holo-chart` (a).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Diag

variable {n : ℕ}

/-- The diagonal matrix `diag(1_n, eps 1_n)` applied to a `2n`-vector. -/
def p11DiagVec (eps : ℝ) (v : P11Vec (n+n)) : P11Vec (n+n) :=
  Fin.append (fun i : Fin n => v (Fin.castAdd n i)) (fun i : Fin n => eps * v (Fin.natAdd n i))

theorem p11dot_diagVec (eps : ℝ) (c v : P11Vec (n+n)) :
    p11dot c (p11DiagVec eps v) = p11dot (p11DiagVec eps c) v := by
  simp only [p11dot, p11DiagVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem p11euclid_sq {m : ℕ} (x : P11Vec m) : p11euclid x ^ 2 = ∑ i, x i ^ 2 := by
  simp only [p11euclid, KAM.Nekhoroshev.euclid, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem p11euclid_diagVec_sq (eps : ℝ) (c : P11Vec (n+n)) :
    p11euclid (p11DiagVec eps c) ^ 2 =
      (∑ i : Fin n, c (Fin.castAdd n i) ^ 2) + eps ^ 2 * ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 := by
  rw [p11euclid_sq]
  simp only [p11DiagVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right, mul_pow,
    Finset.mul_sum]

theorem p11euclid_diagVec_bounds {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) {c : P11Vec (n+n)}
    (hc : p11euclid c = 1) :
    eps ^ 2 ≤ p11euclid (p11DiagVec eps c) ^ 2 := by
  have h1 : (∑ i : Fin n, c (Fin.castAdd n i) ^ 2) + ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 = 1 := by
    have := p11euclid_sq c
    rw [hc, Fin.sum_univ_add] at this
    linarith
  have hB : 0 ≤ ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : 0 ≤ ∑ i : Fin n, c (Fin.castAdd n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [p11euclid_diagVec_sq]
  have : eps ^ 2 ≤ 1 := pow_le_one₀ he0.le he1
  nlinarith

theorem p11dot_smul_left {m : ℕ} (t : ℝ) (c v : P11Vec m) : p11dot (t • c) v = t * p11dot c v := by
  simp only [p11dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Scalar multiples can only increase the maximal jet by the factor, at points of smoothness. -/
theorem p11maxJet_smul_ge {d : ℕ} (hd : 1 ≤ d) {G : P11Vec d → P11Vec 1} {y : P11Vec d} {mu : ℕ}
    (hG : ∀ j ≤ mu, ContDiffAt ℝ j G y) {t : ℝ} (ht : 0 ≤ t) :
    t * p11maxJet mu G y ≤ p11maxJet mu (t • G) y := by
  obtain ⟨j, hj, e⟩ := p11maxJet_attained G y mu
  rw [e]
  obtain ⟨a, ha, h⟩ := p11dg_attained G j y hd
  have := le_p11dg (t • G) j y a ha
  rw [iteratedFDeriv_const_smul_apply (hG j hj)] at this
  have h2 : t * p11dg G j y ≤ p11dg (t • G) j y := by
    rw [h]
    simpa [p11_euclid_smul, abs_of_nonneg ht] using this
  exact h2.trans (le_p11maxJet (t • G) y mu hj)

/-- `stepP:p11:am-norm`: `g_2[D w](c, .) = |Dc|^2 g_2[w](c-hat, .)` with `eps ≤ |Dc| ≤ 1`, hence
`beta_{2,mu}(D w, K) ≥ eps^2 beta_{2,mu}(w, K)`. -/
theorem amount_norm {d n mu : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {V K : Set (P11Vec d)}
    (hV : IsOpen V) (hKV : K ⊆ V) (hne : K.Nonempty) {w : P11Vec d → P11Vec (n+n)}
    (hw : ContDiffOn ℝ mu w V) {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) :
    eps ^ 2 * index_def 2 mu w K ≤ index_def 2 mu (fun y => p11DiagVec eps (w y)) K := by
  refine le_index_def (by omega) 2 mu _ hne fun c hc y hy => ?_
  set s := p11euclid (p11DiagVec eps c) with hs
  have hs2 : eps ^ 2 ≤ s ^ 2 := p11euclid_diagVec_bounds he0 he1 hc
  have hs0 : 0 < s := by
    rcases (p11euclid_nonneg (p11DiagVec eps c)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hs] at h
      rw [← h] at hs2
      nlinarith [sq_pos_of_pos he0]
  set c' : P11Vec (n+n) := s⁻¹ • p11DiagVec eps c with hc'
  have hc'1 : p11euclid c' = 1 := by
    rw [hc', p11_euclid_smul, abs_of_pos (inv_pos.2 hs0), ← hs, inv_mul_cancel₀ hs0.ne']
  have hfun : p11scalar 2 (fun y => p11DiagVec eps (w y)) c = (s ^ 2) • p11scalar 2 w c' := by
    funext y i
    simp only [p11scalar, p11dot_diagVec, hc', p11dot_smul_left, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hat : ∀ j ≤ mu, ContDiffAt ℝ j (p11scalar 2 w c') y := fun j hj =>
    ((contDiffOn_p11scalar hw 2 c').of_le (by exact_mod_cast hj)).contDiffAt
      (hV.mem_nhds (hKV hy))
  have h1 := index_def_le 2 mu w hc'1 hy
  have h2 := p11maxJet_smul_ge hd hat (sq_nonneg s)
  rw [hfun]
  have hnn := index_def_nonneg 2 mu w K
  calc eps ^ 2 * index_def 2 mu w K ≤ s ^ 2 * index_def 2 mu w K :=
        mul_le_mul_of_nonneg_right hs2 hnn
    _ ≤ s ^ 2 * p11maxJet mu (p11scalar 2 w c') y :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    _ ≤ _ := h2

end Diag

section Sets

variable {n m : ℕ}

theorem index_def_anti (hm : 1 ≤ m) (rho mu : ℕ) (w : P11Vec n → P11Vec m) {K K' : Set (P11Vec n)}
    (hKK : K ⊆ K') (hne : K.Nonempty) : index_def rho mu w K' ≤ index_def rho mu w K :=
  le_index_def hm rho mu w hne fun _ hc _ hy => index_def_le rho mu w hc (hKK hy)

/-- The amount over `K` depends only on the germ of `w` along `K`. -/
theorem index_def_congr {U K : Set (P11Vec n)} (hU : IsOpen U) (hKU : K ⊆ U)
    {w w' : P11Vec n → P11Vec m} (h : ∀ y ∈ U, w y = w' y) (rho mu : ℕ) :
    index_def rho mu w K = index_def rho mu w' K := by
  have key : ∀ c : P11Vec m, ∀ y ∈ K,
      p11maxJet mu (p11scalar rho w c) y = p11maxJet mu (p11scalar rho w' c) y := by
    intro c y hy
    have hev : p11scalar rho w c =ᶠ[nhds y] p11scalar rho w' c := by
      filter_upwards [hU.mem_nhds (hKU hy)] with z hz
      have hz' : w z = w' z := h z hz
      show p11scalar rho w c z = p11scalar rho w' c z
      unfold p11scalar
      rw [hz']
    have e : ∀ j, iteratedFDeriv ℝ j (p11scalar rho w c) y =
        iteratedFDeriv ℝ j (p11scalar rho w' c) y := fun j =>
      (Filter.EventuallyEq.iteratedFDeriv ℝ hev j).self_of_nhds
    simp only [p11maxJet, p11dg, e]
  unfold index_def
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c, hc, y, hy, key c y hy⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c, hc, y, hy, (key c y hy).symm⟩

end Sets

section Dir

/-- `stepP:p11:am-dir`: directional stability in the action variable `J` (the `n`-dimensional
amount of `psi_eps` on `A`), from `bpP:p11a:stability`. -/
theorem amount_dir {n mu : ℕ} (hn : 1 ≤ n) {V A : Set (P11Vec n)} (hV : IsOpen V) (hAV : A ⊆ V)
    (hA : IsCompact A) (hne : A.Nonempty) {psi psiE : P11Vec n → P11Vec (n+n)}
    (hpsi : ContDiffOn ℝ mu psi V) (hpsiE : ContDiffOn ℝ mu psiE V) {L1 theta betaJ : ℝ}
    (hL : 0 ≤ L1) (ht : 0 ≤ theta) (hb : p11JetBound true mu A psi L1)
    (he : p11JetBound true mu A (psiE - psi) theta) (hbeta : betaJ ≤ index_def 2 mu psi A)
    (hsmall : (2 : ℝ) ^ mu * theta * (2 * L1 + theta) ≤ betaJ / 2) :
    betaJ / 2 ≤ index_def 2 mu psiE A := by
  have := (stability hn (by omega) hV hAV subset_rfl hA hne (Or.inr rfl) hpsi hpsiE hL ht hb he).2
  have he2 : p11eta 2 mu L1 theta = (2 : ℝ) ^ mu * theta * (2 * L1 + theta) := by
    simp [p11eta]
  rw [he2] at this
  linarith

end Dir

section Slice

variable {n : ℕ}

/-- The inclusion `r ↦ (r, 0)` of the action block. -/
def p11Inl (n : ℕ) : P11Vec n →L[ℝ] P11Vec (n+n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun r => Fin.append r (0 : P11Vec n)
      map_add' := fun x y => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp only [Fin.append_left, Fin.append_right, Pi.add_apply, add_zero, Pi.zero_apply]
      map_smul' := fun t x => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, mul_zero,
            RingHom.id_apply, Pi.zero_apply] }

@[simp] theorem p11Inl_apply (r : P11Vec n) : p11Inl n r = Fin.append r (0 : P11Vec n) := rfl

theorem p11_append_eq (r rho : P11Vec n) :
    Fin.append r rho = Fin.append (0 : P11Vec n) rho + p11Inl n r := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [p11Inl_apply, Fin.append_left, Fin.append_right, Pi.add_apply, add_zero, zero_add,
      Pi.zero_apply]

theorem p11euclid_inl (a : P11Vec n) : p11euclid (p11Inl n a) = p11euclid a := by
  refine (sq_eq_sq₀ (p11euclid_nonneg _) (p11euclid_nonneg _)).1 ?_
  rw [p11euclid_sq, p11euclid_sq, Fin.sum_univ_add]
  simp only [p11Inl_apply, Fin.append_left, Fin.append_right, Pi.zero_apply, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]

/-- Derivatives of the slice `x ↦ G (x, rho)` are the derivatives of `G` in the directions
`(a, 0)`. -/
theorem p11_iteratedFDeriv_slice {m k j : ℕ} {U : Set (P11Vec (n+n))} (hU : IsOpen U)
    {G : P11Vec (n+n) → P11Vec m} (hG : ContDiffOn ℝ k G U) (rho : P11Vec n) (hj : j ≤ k)
    {r : P11Vec n} (hr : Fin.append r rho ∈ U) (a : Fin j → P11Vec n) :
    iteratedFDeriv ℝ j (fun x => G (Fin.append x rho)) r a =
      iteratedFDeriv ℝ j G (Fin.append r rho) (fun i => p11Inl n (a i)) := by
  set a0 : P11Vec (n+n) := Fin.append (0 : P11Vec n) rho with ha0
  set L := p11Inl n with hL
  set V' : Set (P11Vec (n+n)) := (fun z => a0 + z) ⁻¹' U with hV'
  have hV'o : IsOpen V' := hU.preimage (continuous_const.add continuous_id)
  set g : P11Vec (n+n) → P11Vec m := fun z => G (a0 + z) with hg
  have hgd : ContDiffOn ℝ k g V' :=
    hG.comp (contDiffOn_const.add contDiffOn_id) (fun z hz => hz)
  have hLo : IsOpen ((L : P11Vec n → P11Vec (n+n)) ⁻¹' V') := hV'o.preimage L.continuous
  have hmem : L r ∈ V' := by
    show a0 + L r ∈ U
    rwa [← p11_append_eq]
  have h1 := L.iteratedFDerivWithin_comp_right hgd hV'o.uniqueDiffOn hLo.uniqueDiffOn hmem
    (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hLo (by simpa using hmem),
    iteratedFDerivWithin_of_isOpen j hV'o hmem] at h1
  have h2 : (fun x => G (Fin.append x rho)) = g ∘ L := by
    funext x
    simp only [hg, Function.comp_apply]
    congr 1
    exact p11_append_eq x rho
  rw [h2, h1]
  have h3 : iteratedFDeriv ℝ j g (L r) = iteratedFDeriv ℝ j G (Fin.append r rho) := by
    rw [hg, iteratedFDeriv_comp_add_left, p11_append_eq r rho]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, h3]

theorem p11dg_slice_le (hn : 1 ≤ n) {m k j : ℕ} {U : Set (P11Vec (n+n))} (hU : IsOpen U)
    {G : P11Vec (n+n) → P11Vec m} (hG : ContDiffOn ℝ k G U) (rho : P11Vec n) (hj : j ≤ k)
    {r : P11Vec n} (hr : Fin.append r rho ∈ U) :
    p11dg (fun x => G (Fin.append x rho)) j r ≤ p11dg G j (Fin.append r rho) := by
  obtain ⟨a, ha, h⟩ := p11dg_attained (fun x => G (Fin.append x rho)) j r hn
  rw [h, p11_iteratedFDeriv_slice hU hG rho hj hr (fun _ => a)]
  exact le_p11dg G j _ (p11Inl n a) (by rw [p11euclid_inl, ha])

/-- The chart `J ↦ (eps^{-1}(J - J0), rho)` is smooth on an open neighbourhood of the image of
`R`, on which the frozen-`rho` slice of `W` is `C^mu`. -/
theorem p11_slice_chart {mu : ℕ} {U : Set (P11Vec (n+n))} (hU : IsOpen U)
    {W : P11Vec (n+n) → P11Vec (n+n)} (hW : ContDiffOn ℝ mu W U) (J0 : P11Vec n) {eps : ℝ}
    (he0 : 0 < eps) {R : Set (P11Vec n)} (rho : P11Vec n) (hRU : ∀ r ∈ R, Fin.append r rho ∈ U) :
    ∃ V : Set (P11Vec n), IsOpen V ∧ (fun r => J0 + eps • r) '' R ⊆ V ∧
      ContDiffOn ℝ mu (fun J => W (Fin.append (eps⁻¹ • (J - J0)) rho)) V := by
  set a0 : P11Vec (n+n) := Fin.append (0 : P11Vec n) rho with ha0
  have haff : (fun J : P11Vec n => (Fin.append (eps⁻¹ • (J - J0)) rho : P11Vec (n+n))) =
      fun J => a0 + p11Inl n (eps⁻¹ • (J - J0)) := funext fun J => p11_append_eq _ _
  have hcd : ContDiff ℝ mu
      (fun J : P11Vec n => (Fin.append (eps⁻¹ • (J - J0)) rho : P11Vec (n+n))) := by
    rw [haff]
    exact contDiff_const.add ((p11Inl n).contDiff.comp
      ((contDiff_id.sub contDiff_const).const_smul eps⁻¹))
  refine ⟨(fun J : P11Vec n => (Fin.append (eps⁻¹ • (J - J0)) rho : P11Vec (n+n))) ⁻¹' U,
    hU.preimage hcd.continuous, ?_, hW.comp hcd.contDiffOn (fun J hJ => hJ)⟩
  rintro _ ⟨r, hr, rfl⟩
  show Fin.append (eps⁻¹ • (J0 + eps • r - J0)) rho ∈ U
  have : eps⁻¹ • (J0 + eps • r - J0) = r := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he0.ne', one_smul]
  rw [this]
  exact hRU r hr

end Slice

section Scale

/-- `stepP:p11:am-scale`: the `eps^nu` rescaling of the `J`-derivatives. A lower bound `b` on the
`n`-dimensional amount of the frozen-`rho` slice `psi_eps` over `A = J0 + eps R` gives
`eps^mu b ≤` the full tensor norm of `g_2[W](c, .)` at every `(r, rho)`, `r ∈ R`. -/
theorem amount_scale {n mu : ℕ} (hn : 1 ≤ n) {U : Set (P11Vec (n+n))} (hU : IsOpen U)
    {W : P11Vec (n+n) → P11Vec (n+n)} (hW : ContDiffOn ℝ mu W U) (J0 : P11Vec n)
    {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) {R : Set (P11Vec n)} (hR : IsCompact R)
    (hRne : R.Nonempty) (rho : P11Vec n) (hRU : ∀ r ∈ R, Fin.append r rho ∈ U) {b : ℝ}
    (hb : b ≤ index_def 2 mu (fun J => W (Fin.append (eps⁻¹ • (J - J0)) rho))
      ((fun r => J0 + eps • r) '' R)) :
    ∀ c : P11Vec (n+n), p11euclid c = 1 → ∀ r ∈ R,
      eps ^ mu * b ≤ p11maxJet mu (p11scalar 2 W c) (Fin.append r rho) := by
  intro c hc r hr
  obtain ⟨V, hV, hAV, hpsiE⟩ := p11_slice_chart hU hW J0 he0 rho hRU
  have hA : IsCompact ((fun r : P11Vec n => J0 + eps • r) '' R) :=
    hR.image (continuous_const.add (continuous_const_smul eps))
  have hcs := chart_scaling (rho := 2) (by omega : 1 ≤ n) (by omega : 1 ≤ n + n) hA
    (hRne.image _) hV hAV hpsiE J0 he0
  have hphi : (fun y : P11Vec n => (fun J => W (Fin.append (eps⁻¹ • (J - J0)) rho))
      (J0 + eps • y)) = fun y => W (Fin.append y rho) := by
    funext y
    have : eps⁻¹ • (J0 + eps • y - J0) = y := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he0.ne', one_smul]
    simp only [this]
  rw [hphi, min_eq_right (pow_le_one₀ he0.le he1)] at hcs
  have h1 : index_def 2 mu (fun y => W (Fin.append y rho))
      ((fun y : P11Vec n => J0 + eps • y) ⁻¹' ((fun r => J0 + eps • r) '' R)) ≤
      p11maxJet mu (p11scalar 2 (fun y => W (Fin.append y rho)) c) r :=
    index_def_le 2 mu _ hc ⟨r, hr, rfl⟩
  have hGd : ContDiffOn ℝ mu (p11scalar 2 W c) U := contDiffOn_p11scalar hW 2 c
  have h2 : p11maxJet mu (p11scalar 2 (fun y => W (Fin.append y rho)) c) r ≤
      p11maxJet mu (p11scalar 2 W c) (Fin.append r rho) := by
    obtain ⟨j, hj, e⟩ := p11maxJet_attained
      (p11scalar 2 (fun y => W (Fin.append y rho)) c) r mu
    rw [e]
    exact (p11dg_slice_le hn hU hGd rho (by exact_mod_cast hj) (hRU r hr)).trans
      (le_p11maxJet _ _ mu hj)
  have h3 : eps ^ mu * b ≤ eps ^ mu *
      index_def 2 mu (fun J => W (Fin.append (eps⁻¹ • (J - J0)) rho))
      ((fun r => J0 + eps • r) '' R) := mul_le_mul_of_nonneg_left hb (pow_nonneg he0.le _)
  linarith

end Scale

section Transfer

/-- Combination of `am-dir`, `am-scale`, `am-norm`: the amount of `diag(1, eps) W` on `K` is at
least `(1/2) eps^(mu+2) beta_J`. The prepared closeness `he` (from `bpP:p11:prepared` (c)), the
size bound `hb` (`bpP:p11:holo-chart` (a)) and the unscaled amount `hbeta` (`bpP:p11:norm-dict`)
enter as hypotheses. -/
theorem amount_transfer {n mu : ℕ} (hn : 1 ≤ n) {U : Set (P11Vec (n+n))} (hU : IsOpen U)
    {W : P11Vec (n+n) → P11Vec (n+n)} (hW : ContDiffOn ℝ mu W U) (J0 : P11Vec n)
    {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) {R Rho : Set (P11Vec n)} (hR : IsCompact R)
    (hRne : R.Nonempty) (hRU : ∀ r ∈ R, ∀ rho ∈ Rho, Fin.append r rho ∈ U)
    {Vn : Set (P11Vec n)} (hVn : IsOpen Vn)
    (hAVn : (fun r => J0 + eps • r) '' R ⊆ Vn) {varpi : P11Vec n → P11Vec (n+n)}
    (hvarpi : ContDiffOn ℝ mu varpi Vn) {L1 theta betaJ : ℝ} (hL : 0 ≤ L1) (ht : 0 ≤ theta)
    (hb : p11JetBound true mu ((fun r => J0 + eps • r) '' R) varpi L1)
    (he : ∀ rho ∈ Rho, p11JetBound true mu ((fun r => J0 + eps • r) '' R)
      ((fun J => W (Fin.append (eps⁻¹ • (J - J0)) rho)) - varpi) theta)
    (hbeta : betaJ ≤ index_def 2 mu varpi ((fun r => J0 + eps • r) '' R))
    (hsmall : (2 : ℝ) ^ mu * theta * (2 * L1 + theta) ≤ betaJ / 2)
    {K : Set (P11Vec (n+n))} (hKne : K.Nonempty)
    (hK : ∀ y ∈ K, (fun i : Fin n => y (Fin.castAdd n i)) ∈ R ∧
      (fun i : Fin n => y (Fin.natAdd n i)) ∈ Rho) :
    (1 / 2 : ℝ) * eps ^ (mu + 2) * betaJ ≤
      index_def 2 mu (fun y => p11DiagVec eps (W y)) K := by
  have hA : IsCompact ((fun r : P11Vec n => J0 + eps • r) '' R) :=
    hR.image (continuous_const.add (continuous_const_smul eps))
  have hy : ∀ y ∈ K, Fin.append (fun i : Fin n => y (Fin.castAdd n i))
      (fun i : Fin n => y (Fin.natAdd n i)) = y := fun y _ => Fin.append_castAdd_natAdd
  have hKU : K ⊆ U := fun y hyK => by
    have := hRU _ (hK y hyK).1 _ (hK y hyK).2
    rwa [hy y hyK] at this
  have h1 : eps ^ mu * (betaJ / 2) ≤ index_def 2 mu W K := by
    refine le_index_def (by omega) 2 mu W hKne fun c hc y hyK => ?_
    obtain ⟨hr, hrho⟩ := hK y hyK
    obtain ⟨V, hV, hAV, hpsiE⟩ := p11_slice_chart hU hW J0 he0 _ (fun r hr' => hRU r hr' _ hrho)
    have hdir := amount_dir hn (hV.inter hVn) (fun x hx => ⟨hAV hx, hAVn hx⟩) hA (hRne.image _)
      (hvarpi.mono Set.inter_subset_right) (hpsiE.mono Set.inter_subset_left) hL ht hb
      (he _ hrho) hbeta hsmall
    have := amount_scale hn hU hW J0 he0 he1 hR hRne _ (fun r hr' => hRU r hr' _ hrho) hdir c hc
      _ hr
    rwa [hy y hyK] at this
  have h2 := amount_norm (by omega) hn hU hKU hKne hW he0 he1
  calc (1 / 2 : ℝ) * eps ^ (mu + 2) * betaJ = eps ^ 2 * (eps ^ mu * (betaJ / 2)) := by ring
    _ ≤ eps ^ 2 * index_def 2 mu W K := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ _ := h2

end Transfer

end KAM.Planetary

end
