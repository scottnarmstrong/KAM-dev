/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Choice
public import KAM.Nekhoroshev.Interfaces.ConstantsAnalytic
public import KAM.Nekhoroshev.Interfaces.QuasiConvex
public import KAM.Nekhoroshev.Interfaces.HoloReal
public import KAM.Nekhoroshev.Interfaces.Setting
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Canonical.Setting

/-!
# Part 10 assembly: the hypotheses check (`bpN:p10:hypotheses-check`)

The concrete conversion lemmas `hc_tubes`, `hc_h`, `hc_qc`, `hc_f`, `hc_exc`, `hc_time`, the
locality of the total frozen field `head_field_locality`, and their conjunction
`hypotheses_check`. Everything is in the period-one, geometric-width normalization (no `2π`
rescaling of time or of the orbit).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- hc-tubes: V is the existing max-norm polyNbhd, U is its real preimage. -/
theorem hc_tubes (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 ⊆ KAM.actionNbhd (actionBall n p.R) p.s ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      I ∈ actionBall n (5 * p.R / 8) ∧ I ∈ actionBall n p.R ∧ I ∈ realActionDomain n p.R p.s) ∧
    (centralSet n p.R).Nonempty ∧
    (∀ I ∈ actionBall n (p.R / 2), KAM.realInclusion n I ∈ centralSet n p.R) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hsub, hreal⟩ := const_tubes hn1 p hp
  have hR := hp.hR
  refine ⟨hsub, fun I hI => ?_, ⟨KAM.realInclusion n 0, 0, ?_, rfl⟩, fun I hI => ⟨I, ?_, rfl⟩⟩
  · have h1 := hreal I hI
    have h2 : I ∈ actionBall n p.R := by
      simp only [actionBall, mem_ball, dist_zero_right]
      linarith
    refine ⟨?_, h2, ball_subset_realActionDomain hR hp.hs h2⟩
    simpa [actionBall] using h1
  · simp only [mem_ofPred_eq, norm_zero]
    linarith
  · simp only [actionBall, mem_ball, dist_zero_right] at hI
    exact hI.le

/-- hc-h: Euclidean operator estimate, without installing a second norm instance. -/
theorem hc_h (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    DifferentiableOn ℂ h (KAM.Weighted.polyNbhd (centralSet n p.R) p.r0) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      (h (KAM.realInclusion n I)).im = 0) ∧
    ∀ I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0, ∀ x : Fin n → ℂ,
      euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ p.B * euclid x := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨htube, hreal, -, -⟩ := hc_tubes hn p hp
  obtain ⟨hAI, hHB, -, -, -⟩ := hh
  refine ⟨hAI.1.mono htube, fun I hI => hAI.2.2.2.1 I (hreal I hI).2.2, fun I hI x => ?_⟩
  have h1 := ((hessian_convert hp.hR hp.hs hAI hHB).1 I (htube hI)).2.2 x
  have hB : (n : ℝ) * p.Mc ≤ p.B := by
    have := p.q_pos hn1 hp
    change (n : ℝ) * p.Mc ≤ qcB n p.m p.Mc
    unfold qcB
    unfold HeadParams.q at this
    linarith
  refine h1.trans ?_
  have hx : 0 ≤ euclid x := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right hB hx

/-- hc-qc in the period-one normalization consumed by Part 9. -/
theorem hc_qc (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      ∀ ξ : Fin n → ℝ, |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ →
        p.mu * euclid ξ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I ξ ξ := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hreal, -, -⟩ := hc_tubes hn p hp
  obtain ⟨hAI, hHB, hmin, hQC, -⟩ := hh
  intro I hI ξ hξ
  exact (qc_convert hn1 hp.hR hp.hs hp.hm hp.hMc hp.hω hAI hHB hQC hmin I
    (hreal I hI).2.1).2.1 ξ hξ

/-- hc-f: class, reality and an actual summable weighted bound. -/
theorem hc_f (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hf : IsAnalyticPerturbation p.R p.s ε f) :
    KAM.Weighted.InClass (centralSet n p.R) p.r0 p.s1 f ∧
    KAM.Canonical.RealOn (KAM.Weighted.Dom n (centralSet n p.R) p.r0 p.s1) f ∧
    KAM.Weighted.WBound (centralSet n p.R) p.r0 p.s1 f (p.epsPrime ε) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨htube, hreal, -, -⟩ := hc_tubes hn p hp
  obtain ⟨-, hdiff, -, hper, hrealf, -⟩ := id hf
  have hsub : KAM.Weighted.Dom n (centralSet n p.R) p.r0 p.s1 ⊆ complexDomain n p.R p.s := by
    rintro ⟨θ, I⟩ ⟨hθ, hI⟩
    exact ⟨complexStrip_mono (by unfold HeadParams.s1; linarith [hp.hs]) hθ, htube hI⟩
  refine ⟨⟨hdiff.mono hsub, fun j z hz => ?_⟩, ?_, (const_perturbation hn1 p hp hf).1⟩
  · have := hper z (hsub hz) (Pi.single j 1)
    convert this using 3
    ext i
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  · intro x hx
    exact hrealf x.1 x.2 (hreal x.2 hx.2).2.2

/-- hc-exc: strict exclusion, retaining the frozen frequency lower bound on B(0,R). -/
theorem hc_exc (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I₀ ∈ actionBall n (p.R / 2),
      p.mu * p.r0 / 8 < p.wmin ∧ p.wmin ≤ euclid (KAM.frequencyMap h I₀) := by
  have hn1 : 1 ≤ n := by omega
  intro I₀ hI₀
  have hmu := p.mu_pos hn1 hp
  have hIR : I₀ ∈ actionBall n p.R := by
    simp only [actionBall, mem_ball, dist_zero_right] at hI₀ ⊢
    linarith [hp.hR]
  refine ⟨?_, (hh.2.2.1 I₀ hIR).trans (norm_le_euclid _).1⟩
  have h1 : p.mu * p.r0 ≤ 4 * p.wmin := by
    have := mul_le_mul_of_nonneg_left p.r0_le_wmin_div hmu.le
    rwa [mul_div_cancel₀ _ hmu.ne'] at this
  linarith [hp.hω]

/-- hc-time: pointwise input for upstream omega0; no new definition of that maximum. -/
theorem hc_time (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I₀ ∈ actionBall n (p.R / 2), ∀ I : Fin n → ℝ, euclid (I - I₀) ≤ p.R0 →
      euclid (KAM.frequencyMap h I) ≤ Real.sqrt n * p.M := by
  have hn1 : 1 ≤ n := by omega
  intro I₀ hI₀ I hI
  have hsize := (const_size hn1 p hp).2.2.2
  have hnorm : ‖I - I₀‖ ≤ p.r0 / p.A := (norm_le_euclid (I - I₀)).1.trans hI
  have hI₀' : ‖I₀‖ < p.R / 2 := by simpa [actionBall] using hI₀
  have hIR : I ∈ realActionDomain n p.R p.s := by
    refine ball_subset_realActionDomain hp.hR hp.hs ?_
    simp only [actionBall, mem_ball, dist_zero_right]
    calc ‖I‖ = ‖(I - I₀) + I₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖I - I₀‖ + ‖I₀‖ := norm_add_le _ _
      _ < p.R := by linarith [hp.hR, hsize.1, hsize.2]
  exact (partials hh.2.2.2.2 hIR).2.2.1

/-- Locality of the total frozen field. Hlocal is any extension of the same Hamiltonian on W. -/
theorem head_field_locality (p : HeadParams n)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Hlocal : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (heq : EqOn Hlocal (KAM.realHamiltonian h f)
      (univ ×ˢ (KAM.realInclusion n ⁻¹' KAM.Weighted.polyNbhd (centralSet n p.R) p.r0))) :
    EqOn (KAM.hamiltonianVectorField Hlocal) (KAM.hamiltonianVectorField (KAM.realHamiltonian h f))
      (univ ×ˢ (KAM.realInclusion n ⁻¹' KAM.Weighted.polyNbhd (centralSet n p.R) p.r0)) := by
  have hopen : IsOpen (univ ×ˢ (KAM.realInclusion n ⁻¹'
      KAM.Weighted.polyNbhd (centralSet n p.R) p.r0) : Set ((Fin n → ℝ) × (Fin n → ℝ))) :=
    isOpen_univ.prod ((KAM.Weighted.isOpen_polyNbhd _ _).preimage (KAM.realInclusion n).continuous)
  intro z hz
  have hfd := (heq.eventuallyEq_of_mem (hopen.mem_nhds hz)).fderiv_eq (𝕜 := ℝ)
  simp only [KAM.hamiltonianVectorField, hfd]

/-- hypotheses-check: all concrete Part 9 analytic clauses; no guessed upstream setting carrier. -/
theorem hypotheses_check (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    Data n p.R p.s ε h f ∧
    DifferentiableOn ℂ h (KAM.Weighted.polyNbhd (centralSet n p.R) p.r0) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      (h (KAM.realInclusion n I)).im = 0) ∧
    (∀ I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0, ∀ x : Fin n → ℂ,
      euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ p.B * euclid x) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      ∀ ξ : Fin n → ℝ, |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ →
        p.mu * euclid ξ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I ξ ξ) ∧
    KAM.Weighted.InClass (centralSet n p.R) p.r0 p.s1 f ∧
    KAM.Canonical.RealOn (KAM.Weighted.Dom n (centralSet n p.R) p.r0 p.s1) f ∧
    KAM.Weighted.WBound (centralSet n p.R) p.r0 p.s1 f (p.epsPrime ε) ∧
    0 < p.epsPrime ε ∧ p.epsPrime ε ≤ p.eps1 := by
  obtain ⟨h1, h2, h3⟩ := hc_h hn p hp hh
  obtain ⟨f1, f2, f3⟩ := hc_f hn p hp hf
  obtain ⟨-, -, -, hd⟩ := cp_dict hn p hp ε
  obtain ⟨d1, d2⟩ := hd hε hε0
  exact ⟨⟨hp.hR, hp.hs, hh.1, hf⟩, h1, h2, h3, hc_qc hn p hp hh, f1, f2, f3, d1, d2⟩

end KAM.Nekhoroshev

end
