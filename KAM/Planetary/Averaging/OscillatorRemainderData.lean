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


end KAM.Planetary

end
