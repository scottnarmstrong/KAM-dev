/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Ham
public import KAM.Magnetic.Params
public import KAM.SpinOrbit.Graph.CertV2
public import KAM.Application.ClockGraphCheck
public import KAM.Frozen.Magnetic.Defs.MagAlpha

/-!
# The magnetic torus and its graph from a passing v2 certificate

`magnetic_torus_of_V2`: a passing v2 certificate (`checkTorusCertificateV2 routeAV2`) of the
magnetic Hamiltonian `magHamExpr` at the parameters `magParams err disp`, a passing graph check
`checkSoGraph`, the frequency box around `ω* = algFreq 2 magCoeffs √5 = κ (α, 1)`, the Diophantine
property of `ω*` and the band inequalities `8/25 ≤ pLo - disp`, `pHi + disp ≤ 39/100` give

* the analytic, doubly one-periodic graph `P` with `8/25 ≤ P ≤ 39/100`;
* the analytic primary torus `K` of `magHamC` on the strip of width `3/1000000` at the frequency
  `(α, 1)`, energy zero, with the clock `(K θ).1 1 = θ 1` and `(K θ).2 0 = P (Re (K θ).1 0) (θ 1)`
  on real angles (the first five conjuncts of `KAM.Magnetic.magnetic_barrier`, verbatim);
* a global field line inside the graph through every graph point.

Route: the v2 black box `checkTorusCertificateV2_sound` gives `CertifiedTorus`; the clock-triangular
graph adapter `CertifiedTorus.exists_clockGraph` (clock `J` of slope `1`, free diagonal from the
first two conjuncts of `checkSoGraph`) gives the exact torus `K∞`, `s∞ κ = 1` and the analytic
graph of `k = Re ∘ K∞ ∘ ι`; the range transfer is `soGraph_exactTorus_of_certified`'s, at the
named `K∞`. `K` is `K∞` shifted by the clock phase in the second angle (`shiftTorus`); the field
lines are the torus orbits projected by `magProj` (`magProj_hamiltonianVectorField`).
This is a conditional helper over certificate data, not a source result.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

open Set Function
open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.Application
open KAM.SpinOrbit KAM.SpinOrbit.SoGraph

/-! ### Real shifts of a torus -/

section Shift

variable {n : ℕ}

/-- The torus `K∞` shifted by the real vector `v`: `θ ↦ K∞ (θ - v)`. -/
def shiftTorus (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (v : Fin n → ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => Kinf (θ - realInclusion n v)

variable {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

theorem sub_realInclusion_mem_complexStrip {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ)
    (v : Fin n → ℝ) : θ - realInclusion n v ∈ complexStrip n ρ := fun i => by
  simpa [realInclusion_eq_ofReal] using hθ i

theorem differentiableOn_shiftTorus (hK : DifferentiableOn ℂ Kinf (complexStrip n ρ))
    (v : Fin n → ℝ) : DifferentiableOn ℂ (shiftTorus Kinf v) (complexStrip n ρ) :=
  hK.comp (differentiableOn_id.sub_const _) fun _ hθ => sub_realInclusion_mem_complexStrip hθ v

theorem isPrimaryOnStrip_shiftTorus (hp : IsPrimaryOnStrip Kinf ρ) (v : Fin n → ℝ) :
    IsPrimaryOnStrip (shiftTorus Kinf v) ρ := by
  intro θ hθ k
  simp only [shiftTorus]
  rw [add_sub_right_comm]
  exact hp _ (sub_realInclusion_mem_complexStrip hθ v) k

theorem shiftTorus_ofReal (v θ : Fin n → ℝ) :
    shiftTorus Kinf v (fun i => (θ i : ℂ)) = Kinf (realInclusion n (θ - v)) := by
  simp only [shiftTorus, map_sub]
  rfl

theorem isRealOnReals_shiftTorus (hr : IsRealOnReals Kinf) (v : Fin n → ℝ) :
    IsRealOnReals (shiftTorus Kinf v) := by
  intro θ
  rw [shiftTorus_ofReal]
  exact hr (θ - v)

theorem fderiv_shiftTorus (v : Fin n → ℝ) (θ : Fin n → ℂ) :
    fderiv ℂ (shiftTorus Kinf v) θ = fderiv ℂ Kinf (θ - realInclusion n v) := by
  show fderiv ℂ (fun θ => Kinf (θ - realInclusion n v)) θ = _
  simp only [sub_eq_add_neg]
  exact fderiv_comp_add_right (f := Kinf) (x := θ) (-realInclusion n v)

theorem invarianceError_shiftTorus (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ)
    (v : Fin n → ℝ) (θ : Fin n → ℂ) :
    invarianceError h (shiftTorus Kinf v) ω θ = invarianceError h Kinf ω (θ - realInclusion n v) := by
  simp only [invarianceError, fderiv_shiftTorus]
  rfl

end Shift

/-! ### The frequency -/

private theorem magTorus_algFreq_eq :
    algFreq 2 magCoeffs (Real.sqrt 5) = (magKappa : ℝ) • ![magAlpha, 1] := by
  funext i
  fin_cases i
  · simp [algFreq, magCoeffs, magAlpha, Finset.sum_range_succ]
    ring
  · simp [algFreq, magCoeffs]

/-! ### The main theorem -/

/-- **The magnetic torus and graph from a passing v2 certificate** (conditional helper over the
certificate data `g`, `w`, `err`, `disp`; the hypotheses are the data conclusions, the Diophantine
property of `ω*` and two rational band inequalities). The first five conjuncts are those of
`KAM.Magnetic.magnetic_barrier`; the last gives a global field line inside the graph through every
graph point. -/
theorem magnetic_torus_of_V2 (g : SoGraphCert MagBackend) (w : routeAV2.Wit) (err disp : ℚ)
    (hham : g.base.ham = magHamExpr) (hpar : g.base.params = magParams err disp)
    (hc : checkTorusCertificateV2 routeAV2 g.base w = true) (hg : checkSoGraph g = true)
    (hω : FreqEncloses 2 g.base.freqBox (algFreq 2 magCoeffs (Real.sqrt 5)))
    (hdio : IsDiophantine ((magKappa : ℝ) / 10) 1 (algFreq 2 magCoeffs (Real.sqrt 5)))
    (hlo : 8 / 25 ≤ g.pLo - disp) (hhi : g.pHi + disp ≤ 39 / 100) :
    ∃ P : ℝ → ℝ → ℝ,
      AnalyticOnNhd ℝ (fun x : ℝ × ℝ => P x.1 x.2) Set.univ ∧
      (∀ q φ, P (q + 1) φ = P q φ) ∧ (∀ q φ, P q (φ + 1) = P q φ) ∧
      (∀ q φ, 8 / 25 ≤ P q φ ∧ P q φ ≤ 39 / 100) ∧
      (∃ K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
        DifferentiableOn ℂ K (complexStrip 2 (3 / 1000000)) ∧
        IsPrimaryOnStrip K (3 / 1000000) ∧ IsRealOnReals K ∧
        (∀ θ ∈ complexStrip 2 (3 / 1000000), invarianceError magHamC K ![magAlpha, 1] θ = 0) ∧
        (∀ θ ∈ complexStrip 2 (3 / 1000000), magHamC (K θ) = 0) ∧
        ∀ θ : Fin 2 → ℝ,
          (K (fun i => (θ i : ℂ))).1 1 = θ 1 ∧
          (K (fun i => (θ i : ℂ))).2 0 = (P ((K (fun i => (θ i : ℂ))).1 0).re (θ 1) : ℂ)) ∧
      ∀ q φ, ∃ z : ℝ → ℝ × ℝ × ℝ, z 0 = (q, P q φ, φ) ∧
        (∀ t, HasDerivAt z (magField (z t)) t) ∧ ∀ t, (z t).2.1 = P (z t).1 (z t).2.2 := by
  set ωstar := algFreq 2 magCoeffs (Real.sqrt 5) with hωdef
  have hfreq : ωstar = (magKappa : ℝ) • ![magAlpha, 1] := magTorus_algFreq_eq
  -- the parameters
  have hγ' : ((g.base.params.γ : ℚ) : ℝ) = (magKappa : ℝ) / 10 := by
    rw [hpar]; simp [magParams]
  have hτ : (g.base.params.tau : ℝ) = 1 := by rw [hpar]; simp [magParams]
  have hρ : ((g.base.params.rhoInf : ℚ) : ℝ) = 3 / 1000000 := by
    rw [hpar]; simp only [magParams]; push_cast; ring
  have hE0 : ((g.base.params.E0 : ℚ) : ℝ) = 0 := by rw [hpar]; simp [magParams]
  have hdispq : ((g.base.params.disp : ℚ) : ℝ) = disp := by rw [hpar]; rfl
  have hdio' : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar := by
    rw [hγ', hτ]; exact hdio
  -- the black box and the base checks
  have hT := checkTorusCertificateV2_sound routeAV2 hc hω hdio'
  have hbase : landedBase.check g.base = true := by
    simp only [checkTorusCertificateV2, checkV2With, Bool.and_eq_true] at hc
    exact hc.1
  have hs : checkStatic g.base = true := checkStatic_of_checkTorusCertificateV2 hc
  have S := checkStatic_sound hs
  have hh : checkHamBounds g.base = true := by
    simp only [landedBase, Bool.and_eq_true] at hbase
    exact hbase.1.1.1.1.1.2
  have hH : g.base.H = magHamC := by rw [TorusCertificate.H, hham, magHamExpr_eval]
  have hRH := isRealHolo_of_checkHamBounds hs hh
  have hclock : ∀ l, l ≠ (0 : Fin 2) → ∀ z ∈ g.base.D,
      fderiv ℂ g.base.H z (phaseBasis (.inr l)) = ((1 : ℝ) : ℂ) := by
    intro l hl z _
    have hl1 : l = 1 := by
      fin_cases l
      · exact absurd rfl hl
      · rfl
    subst hl1
    rw [hH, magHamC_clock, Complex.ofReal_one]
  have hgc : checkClockGraph g.base 0 g.mono g.mono₀ g.sosMono = true := by
    simp only [checkSoGraph, Bool.and_eq_true] at hg
    simp only [checkClockGraph, Bool.and_eq_true]
    exact ⟨hg.1.1.1, hg.1.1.2⟩
  obtain ⟨hmono, hmargin⟩ := checkClockGraph_sound hs hgc
  obtain ⟨Kinf, sinf, hTA, hk, hsl, cc, hgraph⟩ :=
    hT.exists_clockGraph hs hRH one_pos hclock S.hγ hdio' hmono hmargin
  -- the frequency `s∞ ω* = (α, 1)`
  have hsκ : sinf * (magKappa : ℝ) = 1 := by
    have h := hsl 1 (by decide)
    rwa [hfreq, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_one] at h
  have hsω : sinf • ωstar = ![magAlpha, 1] := by
    rw [hfreq, smul_smul, hsκ, one_smul]
  -- the exact torus
  obtain ⟨-, -, hd, hp, hr, hinv, hEn, -, -, hdisp', -⟩ := hTA
  have hρpos : (0 : ℝ) < g.base.params.rhoInf := S.hρinf
  obtain ⟨-, -, hlo', hhi'⟩ := checkSoGraph_sound S.hW S.hpe hg
  have hbnd : ∀ x : Fin 2 → ℝ, (8 / 25 : ℝ) ≤ ((Kinf (realInclusion 2 x)).2 0).re ∧
      ((Kinf (realInclusion 2 x)).2 0).re ≤ 39 / 100 := by
    intro x
    have e : realInclusion 2 x = realPt (x 0) (x 1) := by
      funext i; fin_cases i <;> rfl
    have h := (Complex.abs_re_le_norm _).trans ((norm_snd_apply_sub_le (Kinf (realInclusion 2 x))
      (g.base.K (realInclusion 2 x))).trans (hdisp' _ (realInclusion_mem_complexStrip hρpos x)))
    rw [Complex.sub_re, hdispq] at h
    have h1 := hlo' (x 0) (x 1)
    have h2 := hhi' (x 0) (x 1)
    rw [← e] at h1 h2
    have hlo'' : (8 / 25 : ℝ) ≤ g.pLo - disp := by
      have h := (Rat.cast_le (K := ℝ)).2 hlo
      push_cast at h
      linarith
    have hhi'' : (g.pHi : ℝ) + disp ≤ 39 / 100 := by
      have h := (Rat.cast_le (K := ℝ)).2 hhi
      push_cast at h
      linarith
    constructor <;> linarith [(abs_le.1 h).1, (abs_le.1 h).2]
  rw [hρ] at hd hp hinv hEn
  rw [hH, hsω] at hinv
  rw [hH, hE0] at hEn
  rw [hH, hsω, realHam_magHamC] at hk
  -- the real torus and its graph
  set k := realRestriction Kinf with hkdef
  have hkι : ∀ x, Kinf (realInclusion 2 x) = realInclusion₂ 2 (k x) := isRealOnReals_iff.mp hr
  have hk2 : ∀ x, (k x).2 0 = ((Kinf (realInclusion 2 x)).2 0).re := fun x => by
    simp [hkdef, realRestriction]
  have hG := hgraph.toIsAnalyticAngleGraph
  have hcl1 : ∀ θ, torusAngle k θ 1 = θ 1 + cc 1 := fun θ =>
    hgraph.triangular.clock θ 1 (by decide)
  have heta : ∀ u : Fin 2 → ℝ, u = ![u 0, u 1] := fun u => by
    funext i; fin_cases i <;> rfl
  set P : ℝ → ℝ → ℝ := fun q φ => torusGraph k ![q, φ] 0 with hP
  refine ⟨P, ?_, fun q φ => ?_, fun q φ => ?_, fun q φ => ?_, ?_, fun q φ => ?_⟩
  · -- analytic
    intro x _
    have hL : AnalyticAt ℝ (fun x : ℝ × ℝ => (![x.1, x.2] : Fin 2 → ℝ)) x := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · exact analyticAt_fst
      · exact analyticAt_snd
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt _).comp
      ((hG.analytic_graph _ (mem_univ _)).comp hL)
  · -- periodic in `q`
    have e : (![q + 1, φ] : Fin 2 → ℝ) =
        ![q, φ] + fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ) := by
      funext i; fin_cases i <;> simp
    simp only [hP, e, hG.graph_add_int]
  · -- periodic in `φ`
    have e : (![q, φ + 1] : Fin 2 → ℝ) =
        ![q, φ] + fun i => (((![0, 1] : Fin 2 → ℤ) i : ℤ) : ℝ) := by
      funext i; fin_cases i <;> simp
    simp only [hP, e, hG.graph_add_int]
  · -- the band
    have e : P q φ = (k (invFun (torusAngle k) ![q, φ])).2 0 := by
      simp only [hP, hG.k_invFun]
    rw [e, hk2]
    exact hbnd _
  · -- the complex torus
    set v : Fin 2 → ℝ := Pi.single 1 (cc 1) with hv
    refine ⟨shiftTorus Kinf v, differentiableOn_shiftTorus hd v, isPrimaryOnStrip_shiftTorus hp v,
      isRealOnReals_shiftTorus hr v, fun θ hθ => ?_, fun θ hθ => ?_, fun θ => ?_⟩
    · rw [invarianceError_shiftTorus]
      exact hinv _ (sub_realInclusion_mem_complexStrip hθ v)
    · simpa [shiftTorus] using hEn _ (sub_realInclusion_mem_complexStrip hθ v)
    · have hA : torusAngle k (θ - v) = ![(k (θ - v)).1 0, θ 1] := by
        rw [heta (torusAngle k (θ - v)), hcl1]
        simp [hv, torusAngle]
      rw [shiftTorus_ofReal, hkι, realInclusion₂_apply]
      simp only [realInclusion_eq_ofReal, Complex.ofReal_re]
      refine ⟨?_, ?_⟩
      · have h := congrFun hA 1
        simp only [torusAngle, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
        rw [h]
      · have h := congrArg (fun y => y.2 0) (hG.eq_graph (θ - v))
        simp only at h
        rw [h, hA]
  · -- the field lines inside the graph
    set θ₀ := invFun (torusAngle k) ![q, φ] with hθ₀
    refine ⟨fun t => magProj (k (θ₀ + t • ![magAlpha, 1])), ?_, fun t => ?_, fun t => ?_⟩
    · simp only [zero_smul, add_zero, magProj_apply, hθ₀, hG.k_invFun, hP]
      simp
    · have h := magProj.hasFDerivAt.comp_hasDerivAt t (hk.flow θ₀ t)
      rw [← realHam_magHamC, magProj_hamiltonianVectorField] at h
      exact h
    · set θ := θ₀ + t • ![magAlpha, 1]
      have h := congrArg (fun y => y.2 0) (hG.eq_graph θ)
      simp only at h
      simp only [magProj_apply, hP]
      rw [h, heta (torusAngle k θ)]
      rfl

end KAM.Magnetic

end
