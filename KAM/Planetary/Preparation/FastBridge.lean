/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.Averaging.OscillatorFinite
public import KAM.Planetary.Preparation.FastDivisor

/-!
# Fast averaging: the oscillator dictionary (P11A-P5, `stepP:p11:af-apply`)

The working carrier `p11WorkingDom` is the oscillator domain `oscDom {J0}` with `m = n`, the
secular position `x` playing the oscillator coordinate `q` and the momentum `y` playing `p`
(frozen order `((θ,x),(J,y))`). This module records that dictionary: domains, the flat parameter,
and the weighted-norm conversion of the spectator parameters.
-/

@[expose] public noncomputable section
open Set Metric
namespace KAM.Planetary

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

theorem oscDom_eq_workingDom (J0 : P11Vec n) (r rz S : ℝ) :
    oscDom (m := n) {J0} r rz rz S = p11WorkingDom n J0 S r rz := by
  ext z
  simp only [oscDom, oscParams, p11WorkingDom, mem_preimage, mem_prod, mem_ofPred_eq,
    oscPack, KAM.actionNbhd, mem_singleton_iff, exists_eq_left]
  have h1 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      firstBlock (b := n + n) (Fin.append a (Fin.append b c)) = a := fun a b c => by
    funext i; simp [firstBlock]
  have h2 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      firstBlock (b := n) (lastBlock (a := n) (Fin.append a (Fin.append b c))) = b :=
    fun a b c => by
    funext i; simp [firstBlock, lastBlock]
  have h3 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      lastBlock (a := n) (lastBlock (a := n) (Fin.append a (Fin.append b c))) = c := fun a b c => by
    funext i; simp [lastBlock]
  have h4 : KAM.realInclusion n J0 = fun i => (J0 i : ℂ) := by funext i; simp
  rw [h1, h2, h3, h4]
  have e1 : ∀ v : Fin (n + n) → ℂ, firstBlock (b := n) v = fun i => v (Fin.castAdd n i) :=
    fun v => rfl
  have e2 : ∀ v : Fin (n + n) → ℂ, lastBlock (a := n) v = fun i => v (Fin.natAdd n i) :=
    fun v => rfl
  rw [e1, e1, e2, e2]
  tauto

/-- The flat oscillator parameter `(J, p, q) = (J, y, x)`. -/
def p11Flat (J y x : P11CVec n) : Fin (n + (n + n)) → ℂ := Fin.append J (Fin.append y x)

theorem firstBlock_p11Flat (J y x : P11CVec n) : firstBlock (b := n + n) (p11Flat J y x) = J := by
  funext i; simp [firstBlock, p11Flat]

theorem p_p11Flat (J y x : P11CVec n) :
    firstBlock (b := n) (lastBlock (a := n) (p11Flat J y x)) = y := by
  funext i; simp [firstBlock, lastBlock, p11Flat]

theorem q_p11Flat (J y x : P11CVec n) :
    lastBlock (a := n) (lastBlock (a := n) (p11Flat J y x)) = x := by
  funext i; simp [lastBlock, p11Flat]

theorem oscUnpack_flat (θ J y x : P11CVec n) :
    oscUnpack (θ, p11Flat J y x) = (Fin.append θ x, Fin.append J y) := by
  simp only [oscUnpack, firstBlock_p11Flat, p_p11Flat, q_p11Flat]

theorem oscPack_eq (z : CPhase (n + n)) :
    oscPack z = (firstBlock (b := n) z.1,
      p11Flat (firstBlock (b := n) z.2) (lastBlock (a := n) z.2) (lastBlock (a := n) z.1)) := rfl

theorem realInclusion₂_append (a b c d : Fin n → ℝ) :
    KAM.realInclusion₂ (n + n) (Fin.append a b, Fin.append c d) =
      (Fin.append (KAM.realInclusion n a) (KAM.realInclusion n b),
        Fin.append (KAM.realInclusion n c) (KAM.realInclusion n d)) := by
  ext i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem oscFunction_flat (f : CHam (n + n)) (θ J y x : P11CVec n) :
    oscFunction f (θ, p11Flat J y x) = f (Fin.append θ x, Fin.append J y) := by
  simp only [oscFunction, Function.comp, oscUnpack, firstBlock_p11Flat, p_p11Flat, q_p11Flat]

theorem coeff_zero_flat (F : P11Phase (n + n) → ℂ) (eps : ℝ) (J y x : P11CVec n) :
    coeff (oscFunction (fun w : CPhase (n + n) => (eps : ℂ) * F w)) (p11Flat J y x) 0 =
      eps * p11FastMean F J (x, y) := by
  unfold coeff KAM.torusCoeffW p11FastMean
  simp only [oscFunction_flat, neg_zero, KAM.character_zero, one_smul]
  unfold KAM.torusAverage
  rw [← MeasureTheory.integral_const_mul]
  rfl

theorem spectator_coeff (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (k : Fin n → ℤ) :
    coeff (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) J k =
      coeff (oscFunction fs) (p11Flat J z.2 z.1) k := by
  unfold coeff
  simp only [oscFunction_flat]

/-- Weighted spectator conversion: the bound for the flat oscillator parameter `(J, y, x)` is the
bound of the function with the secular pair `z = (x, y)` frozen. -/
theorem spectator_wsummable (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (S : ℝ) :
    WSummable (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) S J ↔
      WSummable (oscFunction fs) S (p11Flat J z.2 z.1) := by
  unfold WSummable
  simp only [spectator_coeff]

theorem spectator_wsum_eq (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (S : ℝ) :
    wsum (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) S J =
      wsum (oscFunction fs) S (p11Flat J z.2 z.1) := by
  unfold wsum
  simp only [spectator_coeff]

/-- `bpN:p4:sup-weighted` (b) for the oscillator carrier. -/
theorem oscBound_of_sup {D : Set (Fin n → ℝ)} {m : ℕ} {r rp rq σ σ' M : ℝ} {g : CHam (n + m)}
    (hσ : 0 < σ) (hσ' : 0 < σ') (hcl : oscClass D r rp rq (σ + σ') g)
    (hM : ∀ z ∈ oscDom (m := m) D r rp rq (σ + σ'), ‖g z‖ ≤ M) :
    oscBound D r rp rq σ g (coth (Real.pi * σ') ^ n * M) := by
  refine oscBound_of_flat (G := oscFunction g) hσ (fun y _ => rfl) fun x hx => ?_
  have hfc := hcl.flat
  have hmem : ∀ θ ∈ KAM.complexStrip n (σ + σ'), (θ, x) ∈ KAM.complexStrip n (σ + σ') ×ˢ
      oscParams (m := m) D r rp rq := fun θ hθ => ⟨hθ, hx⟩
  have hd : DifferentiableOn ℂ (fun θ : Fin n → ℂ => oscFunction g (θ, x))
      (KAM.complexStrip n (σ + σ')) :=
    hfc.1.comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn hmem
  obtain ⟨h1, h2⟩ := KAM.summableWeighted_torusCoeffW (ρ := σ + σ') (δ := σ') hσ' (by linarith) hd
    (fun i θ hθ => hfc.2 i (θ, x) (hmem θ hθ))
    (fun θ hθ => hM _ (oscUnpack_mem_oscDom.2 (hmem θ hθ)) |>.trans_eq' (by
      simp [oscFunction, Function.comp]))
  have he : σ + σ' - σ' = σ := by ring
  rw [he] at h1 h2
  exact ⟨h1, h2⟩

theorem p11WorkingDom_mono {J0 : P11Vec n} {s s' r r' rz rz' : ℝ} (hs : s ≤ s') (hr : r ≤ r')
    (hrz : rz ≤ rz') : p11WorkingDom n J0 s r rz ⊆ p11WorkingDom n J0 s' r' rz' := by
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨fun i => (h1 i).trans_le hs, h2.trans_le hr, h3.trans_le hrz, h4.trans_le hrz⟩

theorem actionNbhd_sub_ball (J0 : P11Vec n) {s r : ℝ} (h : s ≤ r) :
    KAM.actionNbhd {J0} s ⊆ Metric.ball (KAM.realInclusion n J0) r := by
  rintro I ⟨J, hJ, hI⟩
  have hJ0 : J = J0 := hJ
  subst hJ0
  have : KAM.realInclusion n J = fun i => (J i : ℂ) := by funext i; simp
  rw [mem_ball, dist_eq_norm, this]
  exact hI.trans_le h

theorem coth_pos {x : ℝ} (hx : 0 < x) : 0 < coth x := by
  unfold coth
  exact div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.2 hx)

/-- `stepP:p11:af-apply`: the hypotheses of `osc_averaging` for the fast Hamiltonian
`h̃ + ε F` (`D = {J₀}`, `r = s₁`, `rp = rq = r_z`, `s̄ = 0`, `s = σ_F`, `E = ε M_F`).  The
reality of `h̃` at real points is a source premise of `osc_averaging`; it is the explicit
hypothesis `hh`. -/
theorem oscHyp_fast {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    (hh : ∀ J : P11Vec n,
      KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n C.J0) (2 * C.rC) →
      (C.h (KAM.realInclusion n J)).im = 0)
    {eps K α s1 : ℝ} (heps : 0 < eps) (hs1 : 0 < s1) (hs1r : s1 ≤ C.rC) (hK : 0 < K)
    (hα : 0 < α) (hbud : 6 ≤ 2 * Real.pi * K * C.sigma)
    (hsK : K * C.L * s1 ≤ C.gamma * K ^ (-C.tau) / 4)
    (hαK : α ≤ 3 / 4 * C.gamma * K ^ (-C.tau))
    (hsmall : 2 ^ 12 * (1 + (n : ℝ)) * K * (eps * C.MF) * C.sigma ≤
      α * min (s1 * C.sigma) (C.rz ^ 2)) :
    OscHyp (m := n) {C.J0} s1 C.rz C.rz 0 C.sigma K α (eps * C.MF) C.h
      (fun z => (eps : ℂ) * C.F z) := by
  have hC' := hC
  obtain ⟨-, -, -, -, hhd, -, -, -, -, -, -, hrC0, hrC1, -, hσ0, hσ1, hrz0, hrz1, hMF, hL1, -, -,
    hFd, hFb, hFp, hFr, -⟩ := hC
  have hn : 1 ≤ n := by have := D.n_ge; omega
  have hsubW : ∀ S, S ≤ 2 * C.sigma → p11WorkingDom n C.J0 S s1 C.rz ⊆
      p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz :=
    fun S hS => p11WorkingDom_mono hS (by linarith) le_rfl
  have hcoth := coth_pos (x := Real.pi * C.sigma) (by positivity)
  have hcls : oscClass (m := n) {C.J0} s1 C.rz C.rz (C.sigma + C.sigma)
      (fun z => (eps : ℂ) * C.F z) := by
    rw [oscClass, oscDom_eq_workingDom]
    have hsub' : p11WorkingDom n C.J0 (C.sigma + C.sigma) s1 C.rz ⊆
        p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz :=
      p11WorkingDom_mono (by linarith) (by linarith) le_rfl
    refine ⟨(differentiableOn_const _).mul (hFd.mono hsub'), fun j z hz => ?_⟩
    simp only [hFp z (hsub' hz) j]
  refine ⟨hn, hn, ⟨hs1, hrz0, hrz0, hσ0, hK, hα⟩, le_rfl, mul_nonneg heps.le (by linarith), hbud,
    (hhd.mono ((actionNbhd_sub_ball C.J0 (by linarith)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I hI
    exact hh I (actionNbhd_sub_ball C.J0 (by linarith) hI)
  · exact hcls.mono le_rfl le_rfl le_rfl (by linarith)
  · have hM : ∀ z ∈ oscDom (m := n) {C.J0} s1 C.rz C.rz (C.sigma + C.sigma),
        ‖(eps : ℂ) * C.F z‖ ≤ eps * C.MF / coth (Real.pi * C.sigma) ^ n := by
      intro z hz
      rw [oscDom_eq_workingDom] at hz
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg heps.le, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hFb z (hsubW _ (by linarith) hz)) heps.le
    have := oscBound_of_sup (σ := C.sigma) (σ' := C.sigma) hσ0 hσ0 hcls hM
    rw [mul_div_cancel₀ _ (pow_pos hcoth n).ne'] at this
    rwa [zero_add]
  · intro x hx
    rw [zero_add, oscDom_eq_workingDom] at hx
    have := hFr x (hsubW _ (by linarith) hx)
    show ((eps : ℂ) * C.F (KAM.realInclusion₂ (n + n) x)).im = 0
    rw [Complex.mul_im, this]
    simp
  · exact fast_divisor hC' hs1r hK hsK hαK
  · rw [show C.rz * C.rz = C.rz ^ 2 by ring]
    exact hsmall

end KAM.Planetary

end
