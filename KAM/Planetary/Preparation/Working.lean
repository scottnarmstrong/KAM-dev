/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Basic
public import KAM.Planetary.Preparation.ForwardTube
public import KAM.Planetary.WeakMeasure.ChartScaling
public import KAM.Planetary.WeakMeasure.Stability
public import KAM.Planetary.Newtonian.Models

/-!
# Preparation working data (P11A-P1, `bpP:p11:sec-A#data`, `bpP:p11:norm-dict`)

The physical data `P11Physical`, the tube radius `p11Zeta`, the packaged forward tube
`forward_tube` and `p11PhysicalDelta` (one-line consequences of `forward_tube_core`), the literal
secular Hessian `p11SecularMatrix`, the Part 10 patch output `P11PatchData` with its specification
`P11PatchSpec`, and `norm_dict`: the `2π`-rescaling `J = 2π Λ` preserves analyticity,
R-nondegeneracy and the squared amount up to the factor `(2π)^(-(2+μ))`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

structure P11Physical (n : ℕ) where
  G : ℝ
  m0 : ℝ
  m : P11Vec n
  a : P11Vec n
  eta : ℝ
  n_ge : 2 ≤ n
  G_pos : 0 < G
  m0_pos : 0 < m0
  m_pos : ∀ i, 0 < m i
  a_pos : ∀ i, 0 < a i
  ordered : StrictMono a
  eta_pos : 0 < eta

def p11Zeta {n : ℕ} (D : P11Physical n) : ℝ :=
  min D.eta ((sInf ({x | ∃ i, x=D.a i} ∪ {x | ∃ i j, i ≠ j ∧ x=|D.a i-D.a j|}))/6)

theorem p11_zeta_pos {n : ℕ} (D : P11Physical n) : 0 < p11Zeta D := by
  have hfin : ({x | ∃ i, x = D.a i} ∪ {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}).Finite := by
    refine Set.Finite.union ((Set.finite_range D.a).subset ?_) ?_
    · rintro x ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    have : {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|} ⊆
        Set.range (fun p : Fin n × Fin n => |D.a p.1 - D.a p.2|) := by
      rintro x ⟨i, j, -, rfl⟩
      exact ⟨(i, j), rfl⟩
    exact (Set.finite_range _).subset this
  have hne : ({x | ∃ i, x = D.a i} ∪ {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}).Nonempty :=
    ⟨D.a ⟨0, by have := D.n_ge; omega⟩, Or.inl ⟨_, rfl⟩⟩
  have hmem := Set.Nonempty.csInf_mem hne hfin
  have hpos : 0 < sInf ({x | ∃ i, x = D.a i} ∪ {x | ∃ i j : Fin n, i ≠ j ∧ x = |D.a i - D.a j|}) := by
    rcases hmem with ⟨i, hi⟩ | ⟨i, j, hij, hx⟩
    · rw [hi]; exact D.a_pos i
    · rw [hx]
      exact abs_pos.2 (sub_ne_zero.2 fun h => hij (D.ordered.injective h))
  exact lt_min D.eta_pos (by positivity)

/-- Forward tube uses existing product chart and one-planet Gamma, for arbitrary n. -/
theorem forward_tube {n : ℕ} (D : P11Physical n) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ i, delta ≤ D.m i*Real.sqrt (D.G*D.m0*D.a i)/4) ∧
      ∀ w : Phase (n+n),
        (∀ i : Fin n, |w.2 (Fin.castAdd n i)-D.m i*Real.sqrt (D.G*D.m0*D.a i)| ≤ delta) →
        (∀ i, poincareGamma (planetBlock w i) ≤ delta) →
        w ∈ poincareProdDom n ∧
        ‖poincareProd D.m (D.G*D.m0) w-
          circularPoint D.G D.m0 D.m D.a (fun i => w.1 (Fin.castAdd n i)/(2*Real.pi))‖ < zeta :=
  forward_tube_core D.G_pos D.m0_pos D.m_pos D.a_pos hzeta

def p11PhysicalDelta {n : ℕ} (D : P11Physical n) : ℝ :=
  (forward_tube D (p11_zeta_pos D)).choose

/-- Literal secular Hessian, connected to Part 8 Q_h by an equality proved at its port. -/
def p11SecularMatrix {n : ℕ} (D : P11Physical n) (L : P11Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1/2 : ℝ) * iteratedFDeriv ℝ 2
    (fun xi : P11Vec n => secularAverage
      (fun (_ : ℝ) z => fFix D.G D.m (poincareProd D.m (D.G*D.m0) z)) 0 L 0 xi)
    0 ![Pi.single i 1,Pi.single j 1]

/-- Part 10 patch output, tied to the actual frozen secular average and physical frequencies. -/
structure P11PatchData (n : ℕ) where
  K : Set (P11Vec n)
  V : Set (P11Vec n)
  varpi : P11Vec n → P11Vec (n+n)
  sigma : P11Vec n → P11Vec n
  mu : ℕ
  beta : ℝ

def P11PatchSpec {n : ℕ} (D : P11Physical n) (A : P11PatchData n) : Prop :=
  (∀ J ∈ A.V, StrictMono (A.sigma J) ∧
    (p11SecularMatrix D ((2*Real.pi)⁻¹ • J)).charpoly=
      ∏ i, (Polynomial.X-Polynomial.C (A.sigma J i))) ∧
  (∀ J ∈ A.V, A.varpi J=Fin.append
    (fun i : Fin n => (D.G*D.m0)^2*D.m i^3/((J i/(2*Real.pi))^3*(2*Real.pi)))
    (fun i : Fin n => 2*A.sigma J i/(2*Real.pi))) ∧
  IsOpen A.V ∧ IsPreconnected A.V ∧ IsCompact A.K ∧ A.K.Nonempty ∧ A.K ⊆ A.V ∧
    0 < volume A.K ∧ volume (A.K \ interior A.K)=0 ∧
    1 ≤ A.mu ∧ 0 < A.beta ∧ AnalyticOnNhd ℝ A.varpi A.V ∧
    p11RNondegenerate A.V A.varpi ∧ A.beta ≤ index_def 2 A.mu A.varpi A.K ∧
    ∀ J ∈ A.K, ∀ i : Fin n,
      |J i/(2*Real.pi)-D.m i*Real.sqrt (D.G*D.m0*D.a i)| < p11PhysicalDelta D/8

section NormDict

variable {n m : ℕ}

private theorem nd_scalar_eq (r : ℝ) (w : P11Vec n → P11Vec m) (c : P11Vec m) :
    p11scalar 2 (fun J => r • w (r • J)) c =
      fun y => (r ^ 2) • (p11scalar 2 w c (0 + r • y)) := by
  funext y i
  have h : ∑ k, c k * (r * w (r • y) k) = r * ∑ k, c k * w (r • y) k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [p11scalar, p11dot, Pi.smul_apply, smul_eq_mul, zero_add, h]
  ring

private theorem nd_p11dg_smul (hn : 1 ≤ n) {G : P11Vec n → P11Vec 1} {y : P11Vec n} {j : ℕ}
    (hG : ContDiffAt ℝ j G y) {t : ℝ} (ht : 0 ≤ t) :
    t * p11dg G j y ≤ p11dg (t • G) j y := by
  obtain ⟨a, ha, h⟩ := p11dg_attained G j y hn
  have := le_p11dg (t • G) j y a ha
  rw [iteratedFDeriv_const_smul_apply hG] at this
  rw [h]
  simpa [smul_apply, p11_euclid_smul, abs_of_nonneg ht] using this

private theorem nd_rnd {V K : Set (P11Vec n)} (hV : IsOpen V) (hsub : K ⊆ V)
    (hne : K.Nonempty) {w : P11Vec n → P11Vec m} {mu : ℕ}
    (hpos : 0 < index_def 2 mu w K) : p11RNondegenerate V w := by
  intro c hc
  by_contra h
  push Not at h
  have hce : 0 < p11euclid c := by
    refine lt_of_le_of_ne (p11euclid_nonneg c) fun h0 => hc ?_
    have h1 : ∑ i, c i ^ 2 = 0 := by
      have := congrArg (· ^ 2) h0.symm
      simp only [p11euclid, KAM.Nekhoroshev.euclid, zero_pow two_ne_zero] at this
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at this
      simpa using this
    funext i
    exact (pow_eq_zero_iff two_ne_zero).1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (c i)).1 h1 i (Finset.mem_univ i))
  set c' : P11Vec m := (p11euclid c)⁻¹ • c with hc'
  have hc'1 : p11euclid c' = 1 := by
    rw [hc', p11_euclid_smul, abs_of_pos (inv_pos.2 hce), inv_mul_cancel₀ hce.ne']
  obtain ⟨y0, hy0⟩ := hne
  have hle := index_def_le 2 mu w hc'1 hy0
  have hzero : p11scalar 2 w c' =ᶠ[nhds y0] 0 := by
    filter_upwards [hV.mem_nhds (hsub hy0)] with y hy
    funext i
    have : p11dot c' (w y) = 0 := by
      simp only [hc', p11dot, Pi.smul_apply, smul_eq_mul]
      have := h y hy
      simp only [p11dot] at this
      rw [show ∑ k, (p11euclid c)⁻¹ * c k * w y k = (p11euclid c)⁻¹ * ∑ k, c k * w y k by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, this, mul_zero]
    simp [p11scalar, this]
  obtain ⟨j, -, hj⟩ := p11maxJet_attained (f := p11scalar 2 w c') (y := y0) mu
  have hdg : p11dg (p11scalar 2 w c') j y0 ≤ 0 := by
    refine Real.sSup_nonpos fun v hv' => ?_
    obtain ⟨a, -, hv⟩ := hv'
    rw [hv, (Filter.EventuallyEq.iteratedFDeriv ℝ hzero j).self_of_nhds]
    simp [p11euclid_zero]
  linarith

/-- norm-dict retains the exact scalar and input dilation factor. -/
theorem norm_dict {n m mu : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V K : Set (P11Vec n)} (hV : IsOpen V) (hK : IsCompact K)
    (hne : K.Nonempty) (hsub : K ⊆ V) {w : P11Vec n → P11Vec m}
    (hw : AnalyticOnNhd ℝ w V) {beta : ℝ} (hb : 0 < beta)
    (ham : beta ≤ index_def 2 mu w K) :
    let wJ := fun J : P11Vec n => (2*Real.pi)⁻¹ • w ((2*Real.pi)⁻¹ • J)
    AnalyticOnNhd ℝ wJ ((fun J => (2*Real.pi) • J) '' V) ∧
    p11RNondegenerate ((fun J => (2*Real.pi) • J) '' V) wJ ∧
    (2*Real.pi)^(-(2+(mu : ℝ)))*beta ≤
      index_def 2 mu wJ ((fun J => (2*Real.pi) • J) '' K) := by
  intro wJ
  set r : ℝ := (2*Real.pi)⁻¹ with hrdef
  have hpi := Real.pi_gt_three
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ∀ y : P11Vec n, r • ((2*Real.pi) • y) = y := fun y => by
    rw [smul_smul, hrdef, inv_mul_cancel₀ (by positivity), one_smul]
  have hinv' : ∀ J : P11Vec n, (2*Real.pi) • (r • J) = J := fun J => by
    rw [smul_smul, hrdef, mul_inv_cancel₀ (by positivity), one_smul]
  have hmem : ∀ J ∈ (fun J => (2*Real.pi) • J) '' V, r • J ∈ V := by
    rintro J ⟨y, hy, rfl⟩
    rwa [hinv]
  have hcd : ContDiffOn ℝ mu w V := hw.contDiffOn hV.uniqueDiffOn
  refine ⟨?_, ?_, ?_⟩
  · intro J hJ
    have hwa : AnalyticAt ℝ w (r • J) := hw _ (hmem J hJ)
    have hl : AnalyticAt ℝ (fun x : P11Vec n => r • x) J := by fun_prop
    exact AnalyticAt.fun_const_smul (c := r)
      (AnalyticAt.comp (g := w) (f := fun x : P11Vec n => r • x) hwa hl)
  · intro c hc
    obtain ⟨y, hy, hcy⟩ := nd_rnd hV hsub hne (hb.trans_le ham) c hc
    refine ⟨(2*Real.pi) • y, ⟨y, hy, rfl⟩, ?_⟩
    have : wJ ((2*Real.pi) • y) = r • w y := by
      show r • w (r • ((2*Real.pi) • y)) = r • w y
      rw [hinv]
    rw [this]
    have h : p11dot c (r • w y) = r * p11dot c (w y) := by
      simp only [p11dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h]
    exact mul_ne_zero hr.ne' hcy
  · have himg : (fun J => (2*Real.pi) • J) '' K = (fun y : P11Vec n => 0 + r • y) ⁻¹' K := by
      ext J
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [hinv] using hy
      · intro hJ
        exact ⟨r • J, by simpa using hJ, hinv' J⟩
    have hne' : ((fun J => (2*Real.pi) • J) '' K).Nonempty := hne.image _
    have hfac : (2*Real.pi)^(-(2+(mu : ℝ))) = r ^ 2 * r ^ mu := by
      rw [Real.rpow_neg (by positivity),
        show (2+(mu : ℝ)) = ((2+mu : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← pow_add, hrdef, inv_pow]
    rw [hfac, himg]
    refine le_index_def hm 2 mu wJ (himg ▸ hne') fun c hc J hJ => ?_
    have hJK : 0 + r • J ∈ K := hJ
    set F := p11scalar 2 w c with hF
    have hFd : ContDiffOn ℝ mu F V := contDiffOn_p11scalar hcd 2 c
    obtain ⟨j, hj, hjeq⟩ := p11maxJet_attained (f := F) (y := 0 + r • J) mu
    have h1 : index_def 2 mu w K ≤ p11maxJet mu F (0 + r • J) := index_def_le 2 mu w hc hJK
    have h2 := (chart_scaling_jets hn hV hFd 0 hr j hj J (hsub hJK)).1
    have hcda : ContDiffAt ℝ j (fun x => F (0 + r • x)) J := by
      have := (hFd.contDiffAt (hV.mem_nhds (hsub hJK))).of_le
        (show ((j : ℕ) : WithTop ℕ∞) ≤ (mu : WithTop ℕ∞) by exact_mod_cast hj)
      exact this.comp J (show ContDiffAt ℝ (j : WithTop ℕ∞) (fun x : P11Vec n => 0 + r • x) J by fun_prop)
    have h3 := nd_p11dg_smul hn hcda (sq_nonneg r)
    have h4 : (r ^ 2) • (fun x => F (0 + r • x)) = p11scalar 2 wJ c := (nd_scalar_eq r w c).symm
    rw [h4] at h3
    have h5 : p11dg (p11scalar 2 wJ c) j J ≤ p11maxJet mu (p11scalar 2 wJ c) J :=
      le_p11maxJet (f := p11scalar 2 wJ c) (y := J) mu hj
    have h6 : r ^ mu ≤ r ^ j := pow_le_pow_of_le_one hr.le hr1 hj
    have h7 : beta ≤ p11dg F j (0 + r • J) := by rw [← hjeq]; linarith
    rw [h2] at h3
    calc r ^ 2 * r ^ mu * beta ≤ r ^ 2 * (r ^ j * p11dg F j (0 + r • J)) := by
          have : r ^ mu * beta ≤ r ^ j * p11dg F j (0 + r • J) :=
            mul_le_mul h6 h7 hb.le (by positivity)
          nlinarith [sq_nonneg r]
      _ ≤ _ := h3.trans h5

end NormDict

end KAM.Planetary

end
