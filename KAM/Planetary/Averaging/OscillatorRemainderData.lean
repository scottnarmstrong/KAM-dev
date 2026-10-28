/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Lie
public import KAM.Planetary.Averaging.OscillatorSeriesAlgebra
public import KAM.Planetary.Averaging.OscillatorStep
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Parts 2-3: the data of the oscillator remainder (`stepP:p2:oi-transfer`)

`oscRemIntegrand` and `osc_remainder_decomposition`: the new remainder `fp` of one oscillator step
is the integral of the explicit family `v t = {g + (1 - t) ξ + t T, φ}` along the exact flow plus
`(f - T) ∘ Ψ`; each `v t` is in the oscillator class with the weighted bound `B`, and `v`, `D v`
are jointly continuous. The local homological equation `{H₀, φ} = ξ - T` is recovered from
`homological_param`, and `taylor_poschel` (at phase dimension `n + m`) gives the identity.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13g.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Literal integrand obtained from taylor_poschel and the homological identity. -/
def oscRemIntegrand {n m : ℕ} (K : ℝ) (φ g f : CHam (n + m))
    (t : ℝ) : CHam (n + m) :=
  poissonBracket (fun z => g z + ((1 - t : ℝ) : ℂ) *
    coeff (oscFunction f) (oscPack z).2 0 + (t : ℂ) * oscTruncate K f z) φ

section Helpers

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S : ℝ}

theorem osc_bound_mono {u : CHam (n + m)} {E E' : ℝ} (h : oscBound D r rp rq S u E)
    (hE : E ≤ E') : oscBound D r rp rq S u E' :=
  fun x hx => ⟨(h x hx).1, (h x hx).2.trans hE⟩

theorem osc_bound_nonneg {u : CHam (n + m)} {E : ℝ} (h : oscBound D r rp rq S u E)
    {x : Fin (n + (m + m)) → ℂ} (hx : x ∈ oscParams (m := m) D r rp rq) : 0 ≤ E :=
  nonneg_of_wsum h hx

theorem osc_class_const_mul (c : ℂ) {u : CHam (n + m)} (hu : oscClass D r rp rq S u) :
    oscClass D r rp rq S (fun z => c * u z) :=
  ⟨hu.1.const_mul c, fun j z hz => by simp only [hu.2 j z hz]⟩

theorem osc_bound_add_sum (hS : 0 < S) {u : CHam (n + m)} {A : ℝ} (hu : oscClass D r rp rq S u)
    (hA : oscBound D r rp rq S u A) {J : ℕ} {v : Fin J → CHam (n + m)} {b : Fin J → ℝ}
    (hv : ∀ j, oscClass D r rp rq S (v j)) (hb : ∀ j, oscBound D r rp rq S (v j) (b j)) :
    oscBound D r rp rq S (fun z => u z + ∑ j, v j z) (A + ∑ j, b j) := by
  induction J generalizing u A with
  | zero => simpa using hA
  | succ J ih =>
    have e : (fun z : CPhase (n + m) => u z + ∑ j, v j z) =
        fun z => (fun z => u z + v 0 z) z + ∑ j : Fin J, v j.succ z := by
      funext z; rw [Fin.sum_univ_succ]; ring
    rw [e, Fin.sum_univ_succ, ← add_assoc]
    exact ih (hu.add (hv 0)) (osc_bound_add hS hu (hv 0) hA (hb 0))
      (fun j => hv j.succ) fun j => hb j.succ

end Helpers

section Hom

variable {n m : ℕ} {D : Set (Fin n → ℝ)}

/-- The frequency part `w ↦ firstBlock w.2` as a continuous linear map. -/
def oscActionL (n m : ℕ) : CPhase (n + m) →L[ℂ] (Fin n → ℂ) :=
  (ContinuousLinearMap.pi fun i : Fin n =>
    (ContinuousLinearMap.proj (Fin.castAdd m i) : (Fin (n + m) → ℂ) →L[ℂ] ℂ)).comp
    (ContinuousLinearMap.snd ℂ (Fin (n + m) → ℂ) (Fin (n + m) → ℂ))

theorem oscActionL_apply (w : CPhase (n + m)) : oscActionL n m w = firstBlock (b := m) w.2 := rfl

theorem fderiv_oscH0 {h : (Fin n → ℂ) → ℂ} {z : CPhase (n + m)}
    (hd : DifferentiableAt ℂ h (firstBlock (b := m) z.2)) (v : CPhase (n + m)) :
    fderiv ℂ (fun w : CPhase (n + m) => h (firstBlock (b := m) w.2)) z v =
      fderiv ℂ h (firstBlock (b := m) z.2) (firstBlock (b := m) v.2) := by
  have h1 : HasFDerivAt (fun w : CPhase (n + m) => oscActionL n m w) (oscActionL n m) z :=
    (oscActionL n m).hasFDerivAt
  have h2 := (hd.hasFDerivAt).comp z h1
  exact congrArg (fun L => L v) h2.fderiv

theorem firstBlock_zero_fun : firstBlock (b := m) (0 : Fin (n + m) → ℂ) = 0 := rfl

theorem firstBlock_single_cast (j : Fin n) :
    firstBlock (b := m) (Pi.single (Fin.castAdd m j) (1 : ℂ) : Fin (n + m) → ℂ) =
      Pi.single j 1 := by
  funext i
  simp [firstBlock, Pi.single_apply, Fin.ext_iff]

theorem firstBlock_single_nat (k : Fin m) :
    firstBlock (b := m) (Pi.single (Fin.natAdd n k) (1 : ℂ) : Fin (n + m) → ℂ) = 0 := by
  funext i
  have := i.2
  simp [firstBlock, Pi.single_apply, Fin.ext_iff]
  omega

/-- The local homological equation `{H₀, φ} = ξ - T` on the original domain, recovered from
`homological_param` at each flat parameter. -/
theorem osc_hom_bracket {r rp rq S K α δ : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}
    (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ) :
    ∀ z ∈ oscDom (m := m) D r rp rq S,
      poissonBracket (fun w : CPhase (n + m) => h (firstBlock (b := m) w.2)) (oscGen K h f) z =
        oscZero f z - oscTruncate K f z := by
  intro z hz
  obtain ⟨hzS, hx⟩ := (show oscPack z ∈ KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq from hz)
  obtain ⟨c1, c2⟩ := oscGen_class_bound hS hK hα hh hdiv hf hδ
  set x := (oscPack z).2 with hxdef
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_oscParams (m := m) D r rp rq) x hx
  have hF := hf.flat
  have hc : InClass ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) :=
    hF.inClass hball le_rfl
  have hb : WBound ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) δ := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact hδ I (hball hI)
  have hω : DifferentiableOn ℂ (oscFreq n m h)
      (polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) ε) := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact (differentiableAt_oscFreq hh (hball hI).1).differentiableWithinAt
  have hdir : ∀ I ∈ polyNbhd ({x} : Set (Fin (n + (m + m)) → ℂ)) ε, ∀ k ∈ zBall n K \ {0},
      α / 1 ≤ ‖dotC k (oscFreq n m h I)‖ := by
    intro I hI k hk
    rw [polyNbhd_singleton] at hI
    rw [div_one]
    exact hdiv _ (hball hI).1 k hk
  obtain ⟨c1', -, -, c4, -, c6, -, -, -, -⟩ :=
    homological_param (ω := oscFreq n m h) (q := 1) le_rfl hα hS hK hω hdir hc hb
  have e0 : ({0} : Set (Fin n → ℤ)) ∩ zBall n K = {0} :=
    Set.inter_eq_left.2 (by
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      simpa [zBall, KAM.Fourier.modeSize] using hK)
  have hy : oscPack z ∈ Dom n ({x} : Set (Fin (n + (m + m)) → ℂ)) ε S :=
    ⟨hzS, by rw [polyNbhd_singleton]; exact mem_ball_self hε⟩
  have hEq := c4 _ hy
  rw [c6 _ hy, e0, ← modeAverage_eq_projMode] at hEq
  have hGd : DifferentiableAt ℂ (homGenParam K {0} (oscFreq n m h) (oscFunction f))
      (oscPack z) := by
    refine c1'.differentiableOn.differentiableAt ?_
    exact (KAM.isOpen_complexStrip n S |>.prod (isOpen_polyNbhd _ _)).mem_nhds hy
  have hφe : oscGen K h f =
      (homGenParam K {0} (oscFreq n m h) (oscFunction f)) ∘ oscPackL (m := m) := by
    funext w
    have := oscFunction_oscGen K h f (oscPack w)
    simp only [oscFunction, Function.comp, s_osc_data] at this
    exact this
  have hder : ∀ i : Fin n, fderiv ℂ (oscGen K h f) z (Pi.single (Fin.castAdd m i) 1, 0) =
      fderiv ℂ (homGenParam K {0} (oscFreq n m h) (oscFunction f)) (oscPack z)
        (Pi.single i 1, 0) := by
    intro i
    rw [hφe]
    have h2 : HasFDerivAt ((homGenParam K {0} (oscFreq n m h) (oscFunction f)) ∘
        ⇑(oscPackL (m := m)))
        ((fderiv ℂ (homGenParam K {0} (oscFreq n m h) (oscFunction f)) (oscPack z)).comp
          (oscPackL (m := m))) z :=
      (hGd.hasFDerivAt).comp z (oscPackL (m := m)).hasFDerivAt
    rw [h2.fderiv]
    exact congrArg _ (oscPack_theta i)
  have hI : firstBlock (b := m) z.2 ∈ KAM.actionNbhd D r := (mem_oscDom_iff.1 hz).2.1
  have hhd : DifferentiableAt ℂ h (firstBlock (b := m) z.2) :=
    hh.differentiableAt ((isOpen_actionNbhd D r).mem_nhds hI)
  have hfb : firstBlock (b := m + m) (oscPack z).2 = firstBlock (b := m) z.2 := by
    funext i; simp [oscPack, firstBlock, Fin.append_left]
  have hfr : ∀ i : Fin n, oscFreq n m h (oscPack z).2 i =
      fderiv ℂ h (firstBlock (b := m) z.2) (Pi.single i 1) := by
    intro i
    simp only [oscFreq, freq, hfb]
  simp only [hfr] at hEq
  unfold poissonBracket
  simp only [fderiv_oscH0 hhd]
  rw [Fin.sum_univ_add]
  simp only [firstBlock_zero_fun, map_zero, zero_mul, zero_sub, Finset.sum_neg_distrib,
    firstBlock_single_cast, firstBlock_single_nat, hder, Finset.sum_const_zero, neg_zero]
  have hc : ∀ x : Fin n,
      (fderiv ℂ (homGenParam K {0} (oscFreq n m h) (oscFunction f)) (oscPack z))
        (Pi.single x 1, 0) * (fderiv ℂ h (firstBlock (b := m) z.2)) (Pi.single x 1) =
      (fderiv ℂ h (firstBlock (b := m) z.2)) (Pi.single x 1) *
        (fderiv ℂ (homGenParam K {0} (oscFreq n m h) (oscFunction f)) (oscPack z))
          (Pi.single x 1, 0) := fun x => mul_comm _ _
  simp only [hc] at hEq
  have hξ : modeAverage (oscFunction f) (oscPack z) = oscZero f z := rfl
  have hT : truncate K (oscFunction f) (oscPack z) = oscTruncate K f z := rfl
  rw [hξ, hT] at hEq
  linear_combination (-1 : ℂ) * hEq

end Hom

section Lin

variable {N : ℕ}

/-- Linearity of the bracket in the first slot, at a point of differentiability. -/
theorem pb_lin3 {a b c φ : CPhase N → ℂ} {s t : ℂ} {z : CPhase N}
    (ha : DifferentiableAt ℂ a z) (hb : DifferentiableAt ℂ b z) (hc : DifferentiableAt ℂ c z) :
    poissonBracket (fun w => a w + s * b w + t * c w) φ z =
      poissonBracket a φ z + s * poissonBracket b φ z + t * poissonBracket c φ z := by
  simp only [poissonBracket_eq_fderiv_field]
  rw [fderiv_fun_add (ha.fun_add (hb.const_mul s)) (hc.const_mul t),
    fderiv_fun_add ha (hb.const_mul s), fderiv_const_mul hb, fderiv_const_mul hc]
  simp

theorem pb_sum {J : ℕ} {u : Fin J → CPhase N → ℂ} {φ : CPhase N → ℂ} {z : CPhase N}
    (hd : ∀ j, DifferentiableAt ℂ (u j) z) :
    poissonBracket (fun w => ∑ j, u j w) φ z = ∑ j, poissonBracket (u j) φ z := by
  simp only [poissonBracket_eq_fderiv_field]
  rw [fderiv_fun_sum (fun j _ => hd j)]
  simp

theorem pb_congr_eventually {u u' φ : CPhase N → ℂ} {z : CPhase N}
    (h : u =ᶠ[nhds z] u') : poissonBracket u φ z = poissonBracket u' φ z := by
  simp only [poissonBracket_eq_fderiv_field, h.fderiv_eq]

end Lin

section Numerics

theorem osc_W_le (m : ℕ) {a s ap aq M : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hap : 0 ≤ ap)
    (haq : 0 ≤ aq) (haM : a ≤ M) (hsM : s ≤ M) (hapM : ap ≤ M) (haqM : aq ≤ M) :
    (1 / exp 1) * (a + s) + m * (aq + ap) ≤ 2 * (1 + m) * M := by
  have e : 1 / exp 1 ≤ 1 := by
    rw [div_le_one (exp_pos 1)]; exact one_le_exp zero_le_one
  have h1 : (1 / exp 1) * (a + s) ≤ 1 * (a + s) :=
    mul_le_mul_of_nonneg_right e (add_nonneg ha hs)
  have h2 : (m : ℝ) * (aq + ap) ≤ m * (2 * M) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
  nlinarith

theorem osc_bracket_bound_le (m : ℕ) {W Mx A Φ d : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (hΦ : 0 ≤ Φ)
    (hW : W ≤ 2 * (1 + m) * Mx) : W / d * A * Φ ≤ 2 * (1 + m) * Φ / d * (Mx * A) := by
  have e1 : W / d * A * Φ = (W * (A * Φ)) / d := by ring
  have e2 : 2 * (1 + (m : ℝ)) * Φ / d * (Mx * A) = (2 * (1 + m) * Mx * (A * Φ)) / d := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hW (mul_nonneg hA hΦ)) hd.le

end Numerics

section Main

set_option linter.unusedVariables false in
theorem osc_remainder_decomposition {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
    let φ := oscGen K h f
    let O := oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    let v := oscRemIntegrand K φ g f
    let B := 2 * (1 + (m : ℝ)) * (δ / (2 * π * α)) / d * (Rsum + δ)
    (∀ t ∈ Icc (0 : ℝ) 1,
      oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) ∧
      oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) B) ∧
    ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2) (Icc 0 1 ×ˢ O) ∧
    ContinuousOn (fun p : ℝ × CPhase (n + m) => fderiv ℂ (v p.1) p.2) (Icc 0 1 ×ˢ O) ∧
    ∀ z ∈ V, fp z =
      (∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) O t z)) +
        f (Ψ z) - oscTruncate K f (Ψ z) := by
  intro Ψ g gp fp d Rsum φ O U u V v B
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hπ := Real.pi_pos
  have hS : 0 < S := by linarith
  have hS' : 0 < S - σ := by linarith
  have hd : 0 < d := lt_min (mul_pos h1 h7) (mul_pos h3 h5)
  have H := osc_flowHyp hα hK ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hh hdiv hf hδ hδpos hsmall
  obtain ⟨c1, c2⟩ := oscGen_class_bound hS hK hα hh hdiv hf hδ
  obtain ⟨z1, z2⟩ := oscZero_class_bound hS hK hα hh hdiv hf hδ
  obtain ⟨t1, t2, -⟩ := osc_truncation_tail hf hδ h7 (by linarith : σ < S) hK
  set Φ := δ / (2 * π * α) with hΦdef
  have hΦ : 0 ≤ Φ := div_nonneg hδpos (by positivity)
  have hgcl : ∀ j, oscClass D r rp rq S (gj j) := fun j =>
    (hg j).1.mono (hg j).2.2.1 (hg j).2.2.2.1 (hg j).2.2.2.2.1 (hg j).2.2.2.2.2
  have hgsum : oscClass D r rp rq S g := oscClass.sum hgcl
  have hOr : O ⊆ oscDom (m := m) D r rp rq S :=
    oscDom_mono (by linarith) (by linarith) (by linarith) (by linarith)
  have hOopen : IsOpen O := isOpen_oscDom _ _ _ _ _
  have hdiffAt : ∀ F : CHam (n + m), oscClass D r rp rq S F → ∀ z ∈ O, DifferentiableAt ℂ F z :=
    fun F hF z hz => hF.1.differentiableAt ((isOpen_oscDom _ _ _ _ _).mem_nhds (hOr hz))
  -- brackets with the generator
  have hbrG : ∀ j, oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket (gj j) φ) ∧
      oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket (gj j) φ)
        (((1 / exp 1) * (ρ / (rj j - r + ρ) + σ / (Sj j - S + σ)) +
          m * (ρq / (rqj j - rq + ρq) + ρp / (rpj j - rp + ρp))) / d * Mj j * Φ) := fun j =>
    osc_bracket hn hm (hg j).1 c1 (hg j).2.1 c2 ⟨h1, by linarith⟩ ⟨h3, by linarith⟩
      ⟨h5, by linarith⟩ ⟨h7, by linarith⟩
      ⟨by linarith [(hg j).2.2.1], by linarith [(hg j).2.2.2.1], by linarith [(hg j).2.2.2.2.1],
        by linarith [(hg j).2.2.2.2.2]⟩
  have hbr0 : ∀ F : CHam (n + m), oscClass D r rp rq S F → oscBound D r rp rq S F δ →
      oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket F φ) ∧
      oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket F φ)
        (2 * (1 + (m : ℝ)) * Φ / d * (1 * δ)) := by
    intro F hF hFb
    obtain ⟨a1, a2⟩ := osc_bracket hn hm hF c1 hFb c2 ⟨h1, by linarith⟩ ⟨h3, by linarith⟩
      ⟨h5, by linarith⟩ ⟨h7, by linarith⟩ ⟨by linarith, by linarith, by linarith, by linarith⟩
    refine ⟨a1, osc_bound_mono a2 (osc_bracket_bound_le m hd hδpos hΦ ?_)⟩
    have e1 : ρ / (r - r + ρ) = 1 := by rw [sub_self, zero_add, div_self h1.ne']
    have e2 : σ / (S - S + σ) = 1 := by rw [sub_self, zero_add, div_self h7.ne']
    have e3 : ρp / (rp - rp + ρp) = 1 := by rw [sub_self, zero_add, div_self h3.ne']
    have e4 : ρq / (rq - rq + ρq) = 1 := by rw [sub_self, zero_add, div_self h5.ne']
    rw [e1, e2, e3, e4]
    exact osc_W_le m zero_le_one zero_le_one zero_le_one zero_le_one le_rfl le_rfl le_rfl le_rfl
  obtain ⟨hQc, hQb⟩ := hbr0 _ z1 z2
  obtain ⟨hRc, hRb⟩ := hbr0 _ t1 t2
  -- pointwise decomposition of `v t` on `O`
  have hveq : ∀ t : ℝ, ∀ z ∈ O, v t z =
      (((1 - t : ℝ) : ℂ) * poissonBracket (oscZero f) φ z +
        (t : ℂ) * poissonBracket (oscTruncate K f) φ z) + ∑ j, poissonBracket (gj j) φ z := by
    intro t z hz
    have hg' : ∀ j, DifferentiableAt ℂ (gj j) z := fun j => hdiffAt _ (hgcl j) z hz
    have e := pb_lin3 (a := g) (b := oscZero f) (c := oscTruncate K f) (φ := φ)
      (s := ((1 - t : ℝ) : ℂ)) (t := (t : ℂ)) (hdiffAt g hgsum z hz) (hdiffAt _ z1 z hz)
      (hdiffAt _ t1 z hz)
    have e' : poissonBracket g φ z = ∑ j, poissonBracket (gj j) φ z := pb_sum hg'
    show poissonBracket (fun z => g z + ((1 - t : ℝ) : ℂ) *
      coeff (oscFunction f) (oscPack z).2 0 + (t : ℂ) * oscTruncate K f z) φ z = _
    rw [show (fun z => g z + ((1 - t : ℝ) : ℂ) * coeff (oscFunction f) (oscPack z).2 0 +
      (t : ℂ) * oscTruncate K f z) = fun w => g w + ((1 - t : ℝ) : ℂ) * oscZero f w +
        (t : ℂ) * oscTruncate K f w from rfl, e, e']
    ring
  have hU1 : ∀ t : ℝ, oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (fun z =>
      ((1 - t : ℝ) : ℂ) * poissonBracket (oscZero f) φ z +
        (t : ℂ) * poissonBracket (oscTruncate K f) φ z) := fun t =>
    (osc_class_const_mul _ hQc).add (osc_class_const_mul _ hRc)
  refine ⟨fun t ht => ?_, ?_, ?_, ?_⟩
  · have hcl : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (fun z =>
        (((1 - t : ℝ) : ℂ) * poissonBracket (oscZero f) φ z +
          (t : ℂ) * poissonBracket (oscTruncate K f) φ z) +
          ∑ j, poissonBracket (gj j) φ z) :=
      (hU1 t).add (oscClass.sum fun j => (hbrG j).1)
    refine ⟨hcl.congr fun z hz => (hveq t z hz).symm, ?_⟩
    by_cases hne : (oscParams (m := m) D (r - ρ) (rp - ρp) (rq - ρq)).Nonempty
    swap
    · intro x hx; exact absurd ⟨x, hx⟩ hne
    obtain ⟨x0, hx0⟩ := hne
    have hMj : ∀ j, 0 ≤ Mj j := fun j => osc_bound_nonneg (hg j).2.1
      (oscParams_mono (by linarith [(hg j).2.2.1]) (by linarith [(hg j).2.2.2.1])
        (by linarith [(hg j).2.2.2.2.1]) hx0)
    have hbU := osc_bound_add hS' (osc_class_const_mul ((1 - t : ℝ) : ℂ) hQc)
      (osc_class_const_mul (t : ℂ) hRc) (osc_bound_const_mul ((1 - t : ℝ) : ℂ) hQb)
      (osc_bound_const_mul (t : ℂ) hRb)
    have hbS := osc_bound_add_sum hS' (hU1 t) hbU (fun j => (hbrG j).1) fun j => (hbrG j).2
    refine oscBound.congr hS' (fun z hz => (hveq t z hz).symm) (osc_bound_mono hbS ?_)
    have n1 : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    have n2 : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [n1, n2]
    have hsumle : ∑ j, ((1 / exp 1) * (ρ / (rj j - r + ρ) + σ / (Sj j - S + σ)) +
          m * (ρq / (rqj j - rq + ρq) + ρp / (rpj j - rp + ρp))) / d * Mj j * Φ ≤
        2 * (1 + (m : ℝ)) * Φ / d * Rsum := by
      rw [show Rsum = ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
        (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j from rfl, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => osc_bracket_bound_le m hd (hMj j) hΦ ?_
      have a1 : 0 ≤ rj j - r + ρ := by linarith [(hg j).2.2.1]
      have a2 : 0 ≤ Sj j - S + σ := by linarith [(hg j).2.2.2.2.2]
      have a3 : 0 ≤ rpj j - rp + ρp := by linarith [(hg j).2.2.2.1]
      have a4 : 0 ≤ rqj j - rq + ρq := by linarith [(hg j).2.2.2.2.1]
      exact osc_W_le m (div_nonneg h1.le a1) (div_nonneg h7.le a2) (div_nonneg h3.le a3)
        (div_nonneg h5.le a4) ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_right _ _).trans (le_max_left _ _)) ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))
    have hB : B = 2 * (1 + (m : ℝ)) * Φ / d * Rsum + 2 * (1 + (m : ℝ)) * Φ / d * (1 * δ) := by
      show 2 * (1 + (m : ℝ)) * Φ / d * (Rsum + δ) = _
      ring
    rw [hB]
    nlinarith [hsumle]
  all_goals sorry

end Main




end KAM.Planetary

end
