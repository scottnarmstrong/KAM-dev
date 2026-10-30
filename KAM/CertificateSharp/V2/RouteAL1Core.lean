/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Run
public import KAM.CertificateSharp.V2.RouteAL1FactsSound
public import KAM.CertificateSharp.V2.RouteAL1Gamma
public import KAM.CertificateSharp.V2.RouteARefined

/-!
# The numerical test of route A with the ℓ¹ entry (package C6L1)

The run is C6's refined run of route A (`RefinedWit`: `X⋆`, the schedule, the caps, the claimed
bounds on `H` and the frame, the certified small-divisor sites) on the strip `ρ' = L.W1.rho < ρ`
of the ℓ¹ data, with the entry record `E` (`KAM.Sharp2.Examples.EntryQ`):

* `L1Wit`, `L1Wit.num`: the witness and the rational numbers of the run;
* `entryOk`: the entry record against the ℓ¹ claim, `ηᴺ`, `ηᴸ` by Wiener products
  (`a_N e ≥ |Lᵀ Ω₀|₁ |E|₁`, `a_L e ≥ |Nᵀ Ω₀|₁ |E|₁`), the torsion strip, the frame caps, and
  `Γ_∞(sω*, δ₀) ≤ G₀`, `Γ_∞(sω*, ρ') ≤ G_ρ` (`gamOk`, clock boxes, `n = 2`, `τ = 1`);
* `finalL1`, `finalL1_sound`: the smallness and the displacement, through `c2L1`, `c3L1`;
* `refHyp_of_le`: C6's `refHyp_of` on a narrower strip;
* `entryHyp_of`: the entry hypotheses `EntryHypA` from `L1Facts`, `FrameFacts` and `entryOk`.

`V2/RouteAL1.lean` assembles `l1Core` and its soundness through `iso_g1_branch_AL1`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith KAM.Sharp2.L1 Matrix
  KAM.CertificateSharp.V2 KAM.Sharp KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp.Engine
open KAM.Sharp2.Examples (EntryQ)

/-- The witness of route A with the ℓ¹ entry. -/
structure L1Wit where
  /-- C6's refined witness (run, claimed bounds, sites). -/
  base : RefinedWit
  /-- The claimed ℓ¹ bounds and their strips. -/
  L : L1Claim
  /-- The entry record (with `ei ≥ e⁻¹`). -/
  E : EntryQ
  /-- `Γ_∞` at `δ₀`. -/
  g0 : FibWit
  /-- `Γ_∞` at `ρ'`. -/
  gρ : FibWit

/-- The rational numbers of the run: C6's refined run on the strip `ρ'` of the ℓ¹ data. -/
def L1Wit.num (w : L1Wit) (n : ℕ) (p : CertParams) (box : FreqBox) : NumQ :=
  { w.base.num n p box with ρ := w.L.W1.rho }

/-- The entry record against the ℓ¹ claim and the box. -/
def entryOk (n : ℕ) (Q : NumQ) (p : CertParams) (box : FreqBox) (w : L1Wit) : Bool :=
  decide (n = 2) && decide (p.tau = 1) &&
    decide (w.L.aLt * w.L.aE ≤ w.E.aN * p.err) && decide (w.L.aNt * w.L.aE ≤ w.E.aL * p.err) &&
    decide (w.L.t1 ≤ w.E.t1) && decide (w.base.R.bT ≤ w.E.tR) &&
    decide (Q.ρ - Q.δ 0 ≤ w.L.WT.rho) &&
    (match w.E.frame with
      | some f => decide (w.L.nuK ≤ f.1) && decide (w.L.nuN ≤ f.2)
      | none => true) &&
    gamOk box w.base.κ p.γ p.s (Q.δ 0) w.E.G0 w.g0 && gamOk box w.base.κ p.γ p.s Q.ρ w.E.Gρ w.gρ

/-- The final comparisons on the strip `Q.ρ`. -/
def finalL1 (Q : NumQ) (E : EntryQ) (p : CertParams) (box : FreqBox) (Xs : ℚ) : Bool :=
  decide (p.err < Xs * p.γ ^ 4 * Q.δ0 ^ (4 * p.tau)) &&
    decide (max (c2L1 Q E Xs) (c3L1 Q E Xs) * p.err ≤ p.disp * (p.γ ^ 2 * Q.ρ ^ (2 * p.tau))) &&
    decide (p.disp < (p.σω - p.s) * freqNormLo box)

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **`finalL1` gives the inputs of the branch** on the strip `Q.ρ`. -/
theorem finalL1_sound {c : TorusCertificate n α} {Q : NumQ} {E : EntryQ} {Xs : ℚ}
    (hs : checkStatic c = true) (hQ : Q.toNum.Wf) (hτ : Q.τ = c.params.tau) (hτ1 : 1 ≤ Q.τ)
    (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) (hXs : 0 < Xs)
    (h : finalL1 Q E c.params c.freqBox Xs = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    (c.params.err : ℝ) / ((c.params.γ : ℝ) ^ 4 *
        delta0 3 Q.toNum.ρ Q.toNum.ρinf ^ (2 * (2 * Q.toNum.τ))) < Xs ∧
      KAM.Iso.Sharp2.L1.c2IL1 Q.toNum E.toA Xs * c.params.err /
        ((c.params.γ : ℝ) ^ 2 * Q.toNum.ρ ^ (2 * Q.toNum.τ)) ≤ c.params.disp ∧
      KAM.Iso.Sharp2.L1.c3IL1 Q.toNum E.toA Xs * c.params.err /
        ((c.params.γ : ℝ) ^ 2 * Q.toNum.ρ ^ (2 * Q.toNum.τ)) ≤ c.params.disp ∧
      (c.params.disp : ℝ) < ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
  have S := checkStatic_sound hs
  simp only [finalL1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hρ0 : (0 : ℝ) < Q.ρ := hQ.ρinf_pos.trans hQ.ρinf_lt
  have hd0 : 0 < (Q.δ0 : ℝ) := by
    rw [← NumQ.cast_δ0]; exact delta0_pos (by norm_num) hQ.ρinf_lt
  have hτQ : Q.toNum.τ = (c.params.tau : ℝ) := by show ((Q.τ : ℕ) : ℝ) = _; rw [hτ]
  have e2 : (2 * (c.params.tau : ℝ)) = ((2 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have hb := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at hb
  have hg : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (Q.ρ : ℝ) ^ (2 * c.params.tau) :=
    mul_pos (pow_pos S.hγ 2) (pow_pos hρ0 _)
  have hρpow : Q.toNum.ρ ^ (2 * Q.toNum.τ) = (Q.ρ : ℝ) ^ (2 * c.params.tau) := by
    rw [hτQ, e2, Real.rpow_natCast]; rfl
  have hclose : ∀ {C B : ℝ}, C ≤ B → B * c.params.err ≤
      c.params.disp * ((c.params.γ : ℝ) ^ 2 * (Q.ρ : ℝ) ^ (2 * c.params.tau)) →
      C * c.params.err / ((c.params.γ : ℝ) ^ 2 * (Q.ρ : ℝ) ^ (2 * c.params.tau)) ≤
        c.params.disp := fun {C B} hC hB => by
    rw [div_le_iff₀ hg]
    exact (mul_le_mul_of_nonneg_right hC S.he0).trans hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e4 : 2 * (2 * (c.params.tau : ℝ)) = ((4 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
    have hX4 : (0 : ℝ) < (c.params.γ : ℝ) ^ 4 * (Q.δ0 : ℝ) ^ (4 * c.params.tau) :=
      mul_pos (pow_pos S.hγ 4) (pow_pos hd0 _)
    have hh := (Rat.cast_lt (K := ℝ)).mpr h1
    push_cast at hh
    show (c.params.err : ℝ) / ((c.params.γ : ℝ) ^ 4 *
      delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (2 * (2 * Q.toNum.τ))) < Xs
    rw [NumQ.cast_δ0, hτQ, e4, Real.rpow_natCast, div_lt_iff₀ hX4]
    calc (c.params.err : ℝ) < Xs * (c.params.γ : ℝ) ^ 4 * (Q.δ0 : ℝ) ^ (4 * c.params.tau) := hh
      _ = _ := by ring
  · rw [hρpow]
    exact hclose ((c2_le hQ hτ1 hE hei hXs).trans (le_max_left _ _)) hb
  · rw [hρpow]
    exact hclose ((c3_le hQ hτ1 hE hei hXs).trans (le_max_right _ _)) hb
  · have hlen : c.freqBox.length = n := by
      simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hs
      exact hs.1
    have hle := freqNormLo_le_norm hlen hω
    have h3' := (Rat.cast_lt (K := ℝ)).mpr h3
    push_cast at h3'
    have hp : (0 : ℝ) ≤ (c.params.σω : ℝ) - c.params.s := by linarith [S.hsσ]
    exact h3'.trans_le (mul_le_mul_of_nonneg_left hle hp)

omit [LawfulCertArith α] in
/-- C6's `refHyp_of` on a strip `N.ρ ≤ ρ`. -/
theorem refHyp_of_le {N : NumA} {c : TorusCertificate N.n α} {R : RefClaim}
    {ωstar : Fin N.n → ℝ} (hn : 1 ≤ N.n) (hρ : N.ρ ≤ c.params.rho) (hδ : 0 ≤ N.δ 0)
    (hρ0 : (0 : ℝ) < c.params.rho) (hM1 : N.M1 = R.dx) (hM2 : N.M2 = R.d2x)
    (hMh2 : N.Mh2 = R.d2h) (hH : HamFacts c R) (hF : FrameFacts c R ωstar) :
    RefHypIA N R.init R.dh c.D c.H c.K ((c.params.s : ℝ) • ωstar) := by
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n c.params.rho := fun i => by simpa using hρ0
  have j0 : Fin N.n := ⟨0, hn⟩
  have hbL : (0 : ℝ) ≤ R.bL :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bL 0 h00 j0)
  have hbN : (0 : ℝ) ≤ R.bN :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bN 0 h00 (Sum.inl j0))
  have hbNt : (0 : ℝ) ≤ R.bNt :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bNt 0 h00 j0)
  have hbT : (0 : ℝ) ≤ R.bT :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bT 0 h00 j0)
  have hs : ∀ θ ∈ complexStrip N.n N.ρ, θ ∈ complexStrip N.n c.params.rho :=
    fun θ hθ i => (hθ i).trans_le hρ
  refine
    { dX := fun z hz => hM1 ▸ hH.dx z hz
      d2X := fun z hz => hM2 ▸ hH.d2x z hz
      dH := hH.dh
      d2H := fun z hz => hMh2 ▸ hH.d2h z hz
      tangentT := fun θ hθ => (norm_le_iff_forall_rowSum hbL).2 fun j => hF.bL θ (hs θ hθ) j
      normal := fun θ hθ => (norm_le_iff_forall_rowSum hbN).2 fun r => hF.bN θ (hs θ hθ) r
      normalT := fun θ hθ => (norm_le_iff_forall_rowSum hbNt).2 fun j => hF.bNt θ (hs θ hθ) j
      tors := fun θ hθ => (norm_le_iff_forall_rowSum hbT).2 fun i => ?_ }
  have hθ' : θ ∈ complexStrip N.n c.params.rho :=
    hs θ (fun i => (hθ i).trans_le (by linarith))
  exact hF.bT θ hθ' i

omit [CertArith α] [LawfulCertArith α] in
/-- `Γ_∞(sω*, δ) ≤ G` from `gamOk`, in dimension `2`. -/
theorem gam_of {c : TorusCertificate n α} (hn : n = 2) (hτ : c.params.tau = 1) {κ δ G : ℚ}
    {w : FibWit} (h : gamOk c.freqBox κ c.params.γ c.params.s δ G w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) :
    smallDivisorSup ((c.params.s : ℝ) • ωstar) (δ : ℝ) ≤ (G : ℝ) := by
  subst hn
  rw [hτ, Nat.cast_one] at hdio
  exact gamOk_sound h hω hdio

/-- **The entry hypotheses from the ℓ¹ facts.** -/
theorem entryHyp_of {c : TorusCertificate n α} {w : L1Wit} {ωstar : Fin n → ℝ}
    (B : BaseFacts c ωstar) (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hF : FrameFacts c w.base.R ωstar) (hL : L1Facts c w.L ωstar)
    (h : entryOk n (w.num n c.params c.freqBox) c.params c.freqBox w = true) :
    EntryHypA (w.num n c.params c.freqBox).toNum w.E.toA c.H c.K ((c.params.s : ℝ) • ωstar)
      c.params.err := by
  set Q := w.num n c.params c.freqBox with hQd
  have S := checkStatic_sound B.hs
  simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn2, hτ1⟩, haN⟩, haL⟩, ht1⟩, htR⟩, hWT⟩, hfr⟩, hg0⟩, hgρ⟩ := h
  have hρQ : Q.toNum.ρ = (w.L.W1.rho : ℝ) := rfl
  have hρ' : (0 : ℝ) < w.L.W1.rho := hL.rho1.1
  have hle : (w.L.W1.rho : ℝ) ≤ c.params.rho := hL.rho1.2.le
  have hsub : complexStrip n (w.L.W1.rho : ℝ) ⊆ complexStrip n c.params.rho :=
    fun θ hθ i => (hθ i).trans_le hle
  have hK : Differentiable ℂ c.K := CertEmbedding.differentiable_eval n c.emb
  have hKp : ∀ r, IsPrimaryOnStrip c.K r := fun r => CertEmbedding.isPrimaryOnStrip n c.emb r
  have hKD : ∀ θ ∈ complexStrip n c.params.rho, c.K θ ∈ c.D := fun θ hθ =>
    B.hEm.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hGu : ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det := fun θ hθ =>
    (B.hG θ hθ).1
  have hSt := standingAt B hdio
  have hEd : DifferentiableOn ℂ (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar))
      (complexStrip n c.params.rho) :=
    KAM.Apost.FrameAux.differentiableOn_invarianceError hSt hK.differentiableOn hKD
  have hEp : IsPeriodicOn (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar)) c.params.rho :=
    KAM.Apost.periodic_invarianceError hSt hKD (hKp _)
  have hvd : DifferentiableOn ℂ
      (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ))
      (complexStrip n (w.L.W1.rho : ℝ)) := by
    exact (sumVecIso n).differentiable.comp_differentiableOn (hEd.mono hsub)
  have hvp : IsPeriodicOn
      (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ))
      (w.L.W1.rho : ℝ) := fun l z hz => by
    show sumVec n _ = sumVec n _
    rw [hEp l z (hsub hz)]
  have hLtd : DifferentiableOn ℂ (fun θ => (tangentMat c.K θ)ᵀ * omegaZeroMatrix n)
      (complexStrip n (w.L.W1.rho : ℝ)) :=
    (differentiableOn_tangentMat hK.differentiableOn).matrix_transpose.matrix_mul
      (differentiableOn_const _)
  have hLtp : IsPeriodicOn (fun θ => (tangentMat c.K θ)ᵀ * omegaZeroMatrix n)
      (w.L.W1.rho : ℝ) := fun l z hz => by
    simp only [KAM.Apost.periodic_tangentMat (hKp _) l z hz]
  have hNd : DifferentiableOn ℂ (normalMat c.K) (complexStrip n (w.L.W1.rho : ℝ)) :=
    (differentiableOn_normalMat hK.differentiableOn hGu).mono hsub
  have hNtd : DifferentiableOn ℂ (fun θ => (normalMat c.K θ)ᵀ * omegaZeroMatrix n)
      (complexStrip n (w.L.W1.rho : ℝ)) :=
    hNd.matrix_transpose.matrix_mul (differentiableOn_const _)
  have hNtp : IsPeriodicOn (fun θ => (normalMat c.K θ)ᵀ * omegaZeroMatrix n)
      (w.L.W1.rho : ℝ) := fun l z hz => by
    simp only [KAM.Apost.periodic_normalMat (hKp _) l z hz]
  have herr : (0 : ℝ) ≤ c.params.err := S.he0
  -- `ηᴺ`
  have hηN := L1Mat.mulVec hρ' hLtd hLtp hvd hvp hL.lt hL.err
  have haN' : ((w.L.aLt : ℚ) : ℝ) * w.L.aE ≤ (w.E.aN : ℝ) * c.params.err := by
    exact_mod_cast haN
  -- `ηᴸ`
  have hηL0 := L1Mat.mulVec hρ' hNtd hNtp hvd hvp hL.nt hL.err
  have hgd : DifferentiableOn ℂ (fun θ => ((normalMat c.K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ))
      (complexStrip n (w.L.W1.rho : ℝ)) := hNtd.matrix_mulVec hvd
  have hzero := L1Vec.const (n := n) (r := (w.L.W1.rho : ℝ)) hρ'.le (0 : Fin n → ℂ)
  have hηL := L1Vec.sub hρ' (differentiableOn_const _) hgd hzero hηL0
  have haL' : ((w.L.aNt : ℚ) : ℝ) * w.L.aE ≤ (w.E.aL : ℝ) * c.params.err := by
    exact_mod_cast haL
  -- the torsion strip
  have hWT' : Q.toNum.ρ - Q.toNum.δ 0 ≤ (w.L.WT.rho : ℝ) := by
    rw [NumQ.cast_δ, hρQ]
    have := (Rat.cast_le (K := ℝ)).mpr hWT
    push_cast at this
    exact this
  refine
    { l1EtaN := (hηN.le (by simpa [EntryQ.toA] using haN')).congr_real fun x => rfl
      l1EtaL := ?_
      l1Torsion := (hL.tors.mono hWT').le (by simpa [EntryQ.toA] using
        (show ((w.L.t1 : ℚ) : ℝ) ≤ w.E.t1 by exact_mod_cast ht1))
      realTorsion := fun x => ?_
      gam0 := ?_
      gamρ := ?_
      frame := ?_ }
  · refine (hηL.le ?_).congr_real fun x => ?_
    · simp only [norm_zero, zero_add]
      simpa [EntryQ.toA] using haL'
    · funext i
      show (0 : ℂ) - _ = -_
      rw [zero_sub]
      rfl
  · have hx : (fun i => ((x i : ℝ) : ℂ)) ∈ complexStrip n c.params.rho :=
      KAM.ofReal_mem_complexStrip (S.hρinf.trans S.hρinfρ) x
    have hj0 : (0 : Fin n → ℂ) ∈ complexStrip n c.params.rho := fun i => by
      simpa using S.hρinf.trans S.hρinfρ
    have hn1 : 1 ≤ n := by have := S.hn; omega
    have hbT : (0 : ℝ) ≤ w.base.R.bT :=
      (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bT 0 hj0 ⟨0, hn1⟩)
    have h1 : ‖torsion c.H c.K ((c.params.s : ℝ) • ωstar) (fun i => ((x i : ℝ) : ℂ))‖ ≤
        w.base.R.bT := (norm_le_iff_forall_rowSum hbT).2 fun i => hF.bT _ hx i
    have h2 : ((w.base.R.bT : ℚ) : ℝ) ≤ w.E.tR := by exact_mod_cast htR
    exact h1.trans h2
  · rw [NumQ.cast_δ]
    exact gam_of hn2 hτ1 hg0 hω hdio
  · exact gam_of hn2 hτ1 hgρ hω hdio
  · intro F hF'
    rcases hfe : w.E.frame with _ | f
    · simp [EntryQ.toA, hfe] at hF'
    · simp only [EntryQ.toA, hfe, Option.map_some, Option.some.injEq] at hF'
      subst hF'
      rw [hfe] at hfr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr
      exact ⟨hL.nuK.le (show ((w.L.nuK : ℚ) : ℝ) ≤ (f.1 : ℝ) by exact_mod_cast hfr.1),
        hL.nuN.le (show ((w.L.nuN : ℚ) : ℝ) ≤ (f.2 : ℝ) by exact_mod_cast hfr.2)⟩

end KAM.CertificateSharp.V2.L1

end
