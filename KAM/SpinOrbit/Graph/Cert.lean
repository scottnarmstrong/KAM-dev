/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Rot
public import KAM.Certificate.Soundness
public import KAM.Certificate.Positivity
public import KAM.Certificate.Torsion.Models
public import KAM.Strip.Cauchy

/-!
# Graph certificates and the barrier from a passing certificate

`SoGraphCert` adds to a torus certificate a monotonicity margin for `∂_{θ₀}` of the angle
component `(.1 0)` and the range `[pLo, pHi]` of the action component `(.2 0)` on the real torus,
each with a paid SOS residual (`checkRealLowerBound`). `checkSoGraph` checks them on the
certificate's own embedding `K` together with the strict margin `mono > disp/ρ∞`.

The transfer to the black box's exact torus `K∞` (`soGraph_deriv_transfer`, then
`soGraph_exactTorus`): `K∞ - K` is holomorphic on `T_{ρ∞}` with sup at most `disp`, so Cauchy
bounds its real `∂_{θ₀}` by `disp/ρ∞`, and the values move by at most `disp`.
Then `soBarrier_of_exact_torus` (original frame) and `soBarrier_of_exact_rotTorus` (rotated frame)
give the barrier with the band widened by `disp`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate CertArith

/-- Graph data checked on top of a passing torus certificate: a monotonicity margin `mono` for
`∂_{θ₀}` of the angle component `(.1 0)` (checked with the strict margin `mono > disp/ρ∞`), the
range `[pLo, pHi]` of the action component `(.2 0)` on the real torus, and the SOS witnesses
with their certified centres. Frame-free: in the original frame `(.1 0) = q`, in the rotated
frame `(.1 0) = Q₀ = q - φ` (same monotonicity in `θ₀`); in both `(.2 0) = p`. -/
structure SoGraphCert (α : Type) where
  base : TorusCertificate 2 α
  mono : ℚ
  mono₀ : ℚ
  pLo : ℚ
  pLo₀ : ℚ
  pHi : ℚ
  pHi₀ : ℚ
  sosMono : CertPoly α
  sosLo : CertPoly α
  sosHi : CertPoly α

variable {α : Type} [CertArith α]

/-- The degree-`0` model of `∂_{θ₀} K_{.1 0}` (entry `(0, 0)` of the `DK` models). -/
def soGraphMonoModel (g : SoGraphCert α) : CertModel α :=
  CertModel.toDeg g.base.weight g.base.piEnc 0
    (modelMatrixEntry (dkModels 2 g.base.emb g.base.weight g.base.piEnc) 0 0)

/-- The degree-`0` model of the action component `K_{.2 0} = (2π)^{dA₀} A₀`. -/
def soGraphActionModel (g : SoGraphCert α) : CertModel α :=
  CertModel.toDeg g.base.weight g.base.piEnc 0
    (realCompModel 2 (g.base.emb.actionDeg.getD 0 0) g.base.emb.action[0]?)

/-- **The graph check**: the strict margin `disp < mono ρ∞`, the SOS lower bound `mono` of
`Re ∂_{θ₀} K_{.1 0}` and the SOS range `[pLo, pHi]` of `Re K_{.2 0}` on the real torus. -/
def checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool :=
  decide (g.base.params.disp < g.mono * g.base.params.rhoInf) &&
    checkRealLowerBound g.base.weight g.base.cfgLow (soGraphMonoModel g) g.mono₀ g.mono
      g.sosMono &&
    checkRealLowerBound g.base.weight g.base.cfgLow (soGraphActionModel g) g.pLo₀ g.pLo
      g.sosLo &&
    checkRealLowerBound g.base.weight g.base.cfgLow (soGraphActionModel g).negM (-g.pHi₀)
      (-g.pHi) g.sosHi

open SoGraph

theorem norm_fst_apply_sub_le (u v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ‖u.1 0 - v.1 0‖ ≤ ‖u - v‖ := by
  simpa using (norm_le_pi_norm (u - v).1 0).trans (norm_fst_le (u - v))

theorem norm_snd_apply_sub_le (u v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ‖u.2 0 - v.2 0‖ ≤ ‖u - v‖ := by
  simpa using (norm_le_pi_norm (u - v).2 0).trans (norm_snd_le (u - v))

theorem realPt_one_zero : realPt 1 0 = Pi.single 0 1 := by
  funext i; fin_cases i <;> simp [realPt]

/-- **Cauchy transfer**: if `‖K∞ - K‖ ≤ d` on `T_ρ`, the real `∂_{θ₀}` of `(.1 0)` moves by at
most `d/ρ` (stated as `|Δ| ρ ≤ d`). -/
theorem soGraph_deriv_transfer {Kinf K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {ρ d : ℝ}
    (hρ : 0 < ρ) (hKinf : DifferentiableOn ℂ Kinf (complexStrip 2 ρ)) (hK : Differentiable ℂ K)
    (hd : ∀ θ ∈ complexStrip 2 ρ, ‖Kinf θ - K θ‖ ≤ d) (x y : ℝ) :
    |((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re -
      ((fderiv ℂ K (realPt x y) (realPt 1 0)).1 0).re| * ρ ≤ d := by
  set D := |((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re -
      ((fderiv ℂ K (realPt x y) (realPt 1 0)).1 0).re| with hD
  have hf : DifferentiableOn ℂ (fun θ => Kinf θ - K θ) (complexStrip 2 ρ) :=
    hKinf.sub hK.differentiableOn
  have hδ : ∀ δ, 0 < δ → δ < ρ → D * δ ≤ d := by
    intro δ hδ0 hδρ
    have hz : realPt x y ∈ complexStrip 2 (ρ - δ) := realPt_mem (by linarith) x y
    have hzρ : realPt x y ∈ complexStrip 2 ρ := realPt_mem hρ x y
    have hC := norm_coordinate_fderiv_le_of_mem_complexStrip hf hd hδ0 hz 0
    have hdiff : fderiv ℂ (fun θ => Kinf θ - K θ) (realPt x y) =
        fderiv ℂ Kinf (realPt x y) - fderiv ℂ K (realPt x y) :=
      fderiv_sub ((hKinf.differentiableAt
        ((isOpen_complexStrip 2 ρ).mem_nhds hzρ))) (hK _)
    rw [hdiff, ← realPt_one_zero] at hC
    have h1 : D ≤ ‖(fderiv ℂ Kinf (realPt x y) - fderiv ℂ K (realPt x y)) (realPt 1 0)‖ := by
      rw [hD, ← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans ?_
      exact norm_fst_apply_sub_le (fderiv ℂ Kinf (realPt x y) (realPt 1 0))
        (fderiv ℂ K (realPt x y) (realPt 1 0))
    have := h1.trans hC
    rwa [le_div_iff₀ hδ0] at this
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd _ (realPt_mem hρ 0 0))
  by_contra hlt
  push Not at hlt
  have hD0 : 0 < D := by
    by_contra h; push Not at h; nlinarith [abs_nonneg D]
  have hq : d / D < ρ := by rwa [div_lt_iff₀ hD0, mul_comm]
  have hpos : 0 ≤ d / D := div_nonneg hd0 hD0.le
  have h := hδ ((d / D + ρ) / 2) (by linarith) (by linarith)
  have : d < D * ((d / D + ρ) / 2) := by
    have : D * (d / D) = d := mul_div_cancel₀ d hD0.ne'
    nlinarith
  linarith

variable {α : Type} [CertArith α] [LawfulCertArith α]

/-- What a passing `checkSoGraph` gives on the certificate's own embedding `K`, on the reals:
the strict margin, `∂_{θ₀} K_{.1 0} ≥ mono` and `K_{.2 0} ∈ [pLo, pHi]`. -/
theorem checkSoGraph_sound {g : SoGraphCert α}
    (hW : checkWeight g.base.weight g.base.expHalvings g.base.expOrder = true)
    (hpe : checkPiEnclosure g.base.piEnc = true) (hg : checkSoGraph g = true) :
    (g.base.params.disp : ℝ) < g.mono * g.base.params.rhoInf ∧
      (∀ x y : ℝ, (g.mono : ℝ) ≤ ((fderiv ℂ g.base.K (realPt x y) (realPt 1 0)).1 0).re) ∧
      (∀ x y : ℝ, (g.pLo : ℝ) ≤ ((g.base.K (realPt x y)).2 0).re) ∧
      (∀ x y : ℝ, ((g.base.K (realPt x y)).2 0).re ≤ g.pHi) := by
  simp only [checkSoGraph, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hm, hmono⟩, hlo⟩, hhi⟩ := hg
  have hM : (soGraphMonoModel g).Encloses 2 g.base.weight.rho
      fun θ => (fderiv ℂ g.base.K θ (Pi.single 0 1)).1 0 :=
    ((dkModels_encloses (n := 2) hW hpe g.base.emb (.inl 0) 0).toDeg hW hpe 0).of_eq_fun
      fun θ => by rw [KAM.Torus.tangentMat_apply, KAM.Torus.sumVec_apply, Sum.elim_inl]; rfl
  have hA : (soGraphActionModel g).Encloses 2 g.base.weight.rho
      fun θ => (g.base.K θ).2 0 :=
    (realCompModel_encloses 2 _ _ _).toDeg hW hpe 0
  refine ⟨by exact_mod_cast hm, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [realPt_one_zero]
    exact checkRealLowerBound_sound hW _ hM hmono ![x, y]
  · exact checkRealLowerBound_sound hW _ hA hlo ![x, y]
  · have h := checkRealLowerBound_sound hW _ hA.negM hhi ![x, y]
    have e : (fun i => ((![x, y] i : ℝ) : ℂ)) = realPt x y := rfl
    rw [e, Complex.neg_re] at h
    push_cast at h
    linarith

/-- The black box output (`CertifiedTorus`, from either certifier) plus a passing graph check and
the static check: an exact torus `K∞` on `T_{ρ∞}`, invariant for `c.H` at `s∞ ω*` (`s∞ ω*`
Diophantine), with `∂_{θ₀} K∞_{.1 0} ≥ mono - disp/ρ∞ > 0` and
`K∞_{.2 0} ∈ [pLo - disp, pHi + disp]` on the reals. -/
theorem soGraph_exactTorus_of_certified {g : SoGraphCert α} (hs : checkStatic g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hT : CertifiedTorus g.base ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      DifferentiableOn ℂ Kinf (complexStrip 2 g.base.params.rhoInf) ∧
      IsPrimaryOnStrip Kinf g.base.params.rhoInf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 g.base.params.rhoInf,
        invarianceError g.base.H Kinf (sinf • ωstar) θ = 0) ∧
      IsDiophantine (sinf * g.base.params.γ) (g.base.params.tau : ℝ) (sinf • ωstar) ∧
      0 < sinf * (g.base.params.γ : ℝ) ∧
      0 < (g.mono : ℝ) - g.base.params.disp / g.base.params.rhoInf ∧
      (∀ x y : ℝ, (g.mono : ℝ) - g.base.params.disp / g.base.params.rhoInf ≤
        ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re) ∧
      (∀ x y : ℝ, (g.pLo : ℝ) - g.base.params.disp ≤ ((Kinf (realPt x y)).2 0).re) ∧
      (∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ (g.pHi : ℝ) + g.base.params.disp) := by
  have S := checkStatic_sound hs
  obtain ⟨hm, hmono, hlo, hhi⟩ := checkSoGraph_sound S.hW S.hpe hg
  obtain ⟨Kinf, sinf, hs1, -, hholo, hprim, hreal, hinv, -, -, -, hdisp, -⟩ := hT
  have hρ : (0 : ℝ) < g.base.params.rhoInf := S.hρinf
  have hsinf : 0 < sinf := by linarith
  have hK : Differentiable ℂ g.base.K := CertEmbedding.differentiable_eval 2 g.base.emb
  set d : ℝ := (g.base.params.disp : ℝ)
  have hpt : ∀ x y : ℝ, ‖Kinf (realPt x y) - g.base.K (realPt x y)‖ ≤ d :=
    fun x y => hdisp _ (realPt_mem hρ x y)
  refine ⟨Kinf, sinf, hholo, hprim, hreal, hinv, isDiophantine_smul_scale hsinf hdio,
    mul_pos hsinf (by exact_mod_cast S.hγ), ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [sub_pos, div_lt_iff₀ hρ]; exact hm
  · have h := soGraph_deriv_transfer hρ hholo hK hdisp x y
    have h' : |((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re -
        ((fderiv ℂ g.base.K (realPt x y) (realPt 1 0)).1 0).re| ≤ d / g.base.params.rhoInf := by
      rwa [le_div_iff₀ hρ]
    have := hmono x y
    have := (abs_le.1 h').1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hlo x y
    have := (abs_le.1 h).1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hhi x y
    have := (abs_le.1 h).2
    linarith

omit [LawfulCertArith α] in
/-- The static check is the first conjunct of `checkTorusCertificate`. -/
theorem checkStatic_of_checkTorusCertificate {c : TorusCertificate 2 α}
    (hc : checkTorusCertificate c = true) : checkStatic c = true := by
  simp only [checkTorusCertificate, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1.1

/-- The black box plus a passing graph check: an exact torus `K∞` on `T_{ρ∞}`, invariant for
`c.H` at `s∞ ω*` (`s∞ ω*` Diophantine), with `∂_{θ₀} K∞_{.1 0} ≥ mono - disp/ρ∞ > 0` and
`K∞_{.2 0} ∈ [pLo - disp, pHi + disp]` on the reals. -/
theorem soGraph_exactTorus {g : SoGraphCert α} (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      DifferentiableOn ℂ Kinf (complexStrip 2 g.base.params.rhoInf) ∧
      IsPrimaryOnStrip Kinf g.base.params.rhoInf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 g.base.params.rhoInf,
        invarianceError g.base.H Kinf (sinf • ωstar) θ = 0) ∧
      IsDiophantine (sinf * g.base.params.γ) (g.base.params.tau : ℝ) (sinf • ωstar) ∧
      0 < sinf * (g.base.params.γ : ℝ) ∧
      0 < (g.mono : ℝ) - g.base.params.disp / g.base.params.rhoInf ∧
      (∀ x y : ℝ, (g.mono : ℝ) - g.base.params.disp / g.base.params.rhoInf ≤
        ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re) ∧
      (∀ x y : ℝ, (g.pLo : ℝ) - g.base.params.disp ≤ ((Kinf (realPt x y)).2 0).re) ∧
      (∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ (g.pHi : ℝ) + g.base.params.disp) :=
  soGraph_exactTorus_of_certified (checkStatic_of_checkTorusCertificate hc) hg
    (checkTorusCertificate_sound hc hω hdio) hdio

/-- The barrier from a passing ORIGINAL-frame certificate (valid, not on the
headline route). The band is widened by `disp`. -/
theorem soBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    (hham : g.base.ham = soHamExpr) (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) := by
  obtain ⟨Kinf, sinf, hholo, hprim, hreal, hinv, hdio', hγ, hm, hmono, hlo, hhi⟩ :=
    soGraph_exactTorus hc hg hω hdio
  have hH : g.base.H = soHC := by
    rw [TorusCertificate.H, hham]; exact funext soHamExpr_eval
  rw [hH] at hinv
  have hρ : (0 : ℝ) < g.base.params.rhoInf := by
    have hs : checkStatic g.base = true := by
      simp only [checkTorusCertificate, Bool.and_eq_true] at hc
      exact hc.1.1.1.1.1.1.1
    exact (checkStatic_sound hs).hρinf
  exact soBarrier_of_exact_torus hρ hholo hprim hreal hinv hγ hdio' hm hmono hlo hhi

/-- The barrier from the black box output (`CertifiedTorus`, from either certifier), the static
check and a passing graph check, in the ROTATED frame: graph transfer (`checkSoGraph`, Cauchy on
`T_{ρ∞}`, frame-free), then `soBarrier_of_exact_rotTorus`. The band is widened by `disp`. -/
theorem soRotBarrier_of_certified {α : Type} [CertArith α] [LawfulCertArith α]
    (g : SoGraphCert α) {c : ℚ} (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c)
    (hs : checkStatic g.base = true) (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ}
    (hT : CertifiedTorus g.base ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) := by
  obtain ⟨Kinf, sinf, hholo, hprim, hreal, hinv, hdio', hγ, hm, hmono, hlo, hhi⟩ :=
    soGraph_exactTorus_of_certified hs hg hT hdio
  have hH : g.base.H = (soRotHamExprScaled c).eval := by rw [TorusCertificate.H, hham]
  rw [hH] at hinv
  exact soBarrier_of_exact_rotTorus hc0 (checkStatic_sound hs).hρinf hholo hprim hreal hinv hγ
    hdio' hm hmono hlo hhi

/-- **The barrier from a passing ROTATED-frame certificate**: black box
(`checkTorusCertificate_sound`), then `soRotBarrier_of_certified`. The band is widened by
`disp`. -/
theorem soRotBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    {c : ℚ} (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c)
    (hc : checkTorusCertificate g.base = true) (hg : checkSoGraph g = true)
    {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  soRotBarrier_of_certified g hc0 hham (checkStatic_of_checkTorusCertificate hc) hg
    (checkTorusCertificate_sound hc hω hdio) hdio

end KAM.SpinOrbit
