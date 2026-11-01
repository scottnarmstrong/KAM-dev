/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleQt
public import KAM.Wave.KamStep.ActionAngleDomain
public import KAM.Wave.KamStep.Class
public import KAM.Wave.Birkhoff.QuartMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `P_ξ` is a smoothing Hamiltonian (blueprint-W `bpW:w5:action-angle` (v))

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (v), step `a-field`.

`aaXP ξ w = X_{Q̃}(w) + D𝒜_ξ(w)⁻¹ (X_{G^{nor}} + X_K)(𝒜_ξ w)` (`p+1`-representatives; the inverse is
`aaDerInv a (p+1)`). Main results:

* `hasFDerivAt_comp_aaMap`: the chain rule `D(G ∘ 𝒜_ξ)(w) W = ϖ_{p+1,p}(D𝒜_ξ(w)⁻¹ X_G(𝒜_ξ w), W)`
  for `G` with `DG(w') v = Ω(ι X_G(w'), v)` (step `a-field`, via `aaDer_symp` with `(q,q') = (p+1,p)`);
* `aaP_isSmoothing_of` (helper on an arbitrary open `V` on which `𝒜_ξ` is defined and maps into
  `B_{ρ₁}`) and the source-facing **`aaP_isSmoothing`** (`a = p = 1`, `P_ξ ∈ 𝒮_{p+1}(D(s,r))` under
  the hypotheses of (ii) and `c_A(t+r²) < ρ₁²`), with field `aaXP`;
* `aaPfun_real` (`P_ξ` real at real points for real `ξ`), `aaPfun_add_tau` (periodicity).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-! ### Holomorphy of `w ↦ D𝒜_ξ(w)⁻¹ F(w)` -/

theorem aaDerInv_eq (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) :
    aaDerInv a q ξ w V =
      ((fun i => (V (false, modeIdx i) * aaE w true i - V (true, modeIdx i) * aaE w false i) /
          (4 * Real.pi * I * aaS ξ w i * ellWeight a q (modeIdx i))),
        (fun i => aaS ξ w i * (V (true, modeIdx i) * aaE w false i +
          V (false, modeIdx i) * aaE w true i) / ellWeight a q (modeIdx i)),
        aaUnshift (birkZinv V).1, aaUnshift (birkZinv V).2) := by
  refine Prod.ext (funext fun i => aaDerInv_theta a q ξ w V i)
    (Prod.ext (funext fun i => aaDerInv_y a q ξ w V i) (Prod.ext rfl rfl))

theorem differentiableAt_aaS {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2}
    (h : 0 < (ξ i + w.2.1 i).re) : DifferentiableAt ℂ (fun w : KamPhase => aaS ξ w i) w :=
  (hasFDerivAt_aaS h).differentiableAt

theorem differentiableAt_aaE (w : KamPhase) (b : Bool) (i : Fin 2) :
    DifferentiableAt ℂ (fun w : KamPhase => aaE w b i) w :=
  (hasFDerivAt_aaE w b i).differentiableAt

/-- `w ↦ D𝒜_ξ(w)⁻¹ F(w)` is holomorphic where `F` is. -/
theorem differentiableAt_aaDerInv_apply (a q : ℝ) {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) {F : KamPhase → BirkSpace} (hF : DifferentiableAt ℂ F w) :
    DifferentiableAt ℂ (fun w => aaDerInv a q ξ w (F w)) w := by
  simp_rw [aaDerInv_eq]
  have hev : ∀ l : BirkIdx, DifferentiableAt ℂ (fun w => F w l) w := fun l =>
    (aaEv l).differentiableAt.comp w hF
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  refine DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ ?_))
  · refine differentiableAt_pi.2 fun i => ?_
    have hs := differentiableAt_aaS (hw i)
    have hs0 := aaS_ne_zero (hw i)
    have hE1 := differentiableAt_aaE w true i
    have hE2 := differentiableAt_aaE w false i
    have h1 := hev (false, modeIdx i)
    have h2 := hev (true, modeIdx i)
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    have hden : 4 * (Real.pi : ℂ) * I * aaS ξ w i * (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi)
        Complex.I_ne_zero) hs0) hω
    fun_prop (disch := assumption)
  · refine differentiableAt_pi.2 fun i => ?_
    have hs := differentiableAt_aaS (hw i)
    have hE1 := differentiableAt_aaE w true i
    have hE2 := differentiableAt_aaE w false i
    have h1 := hev (false, modeIdx i)
    have h2 := hev (true, modeIdx i)
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    fun_prop (disch := assumption)
  · exact (aaUnshift.comp ((ContinuousLinearMap.fst ℂ _ _).comp birkZinv)).differentiableAt.comp
      w hF
  · exact (aaUnshift.comp ((ContinuousLinearMap.snd ℂ _ _).comp birkZinv)).differentiableAt.comp
      w hF

/-! ### The chain rule for `G ∘ 𝒜_ξ` -/

/-- **Step `a-field`**: if `DG(𝒜_ξ w) v = Ω(ι X, v)` for all `v` (`X ∈ 𝔚^{p+1}`), then
`D(G ∘ 𝒜_ξ)(w) W = ϖ_{p+1,p}(D𝒜_ξ(w)⁻¹ X, W)`. -/
theorem hasFDerivAt_comp_aaMap {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {ξ : Fin 2 → ℂ}
    {w : KamPhase} (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) {G : BirkSpace → ℂ}
    {DG : BirkSpace →L[ℂ] ℂ} (hG : HasFDerivAt G DG (aaMap a p ξ w)) {X : BirkSpace}
    (hX : ∀ v, DG v = birkOmegaPlus a p ha hp X v) :
    HasFDerivAt (fun w => G (aaMap a p ξ w)) (DG.comp (aaDer a p ξ w)) w ∧
      ∀ W, DG.comp (aaDer a p ξ w) W =
        stepSymp (q := p + 1) (q' := p) ha (by linarith) (aaDerInv a (p + 1) ξ w X) W := by
  refine ⟨hG.comp w (hasFDerivAt_aaMap a p hw), fun W => ?_⟩
  rw [ContinuousLinearMap.comp_apply, hX, birkOmegaPlus_eq_birkOmegaMix]
  conv_lhs => rw [← aaDer_aaDerInv a (p + 1) hw X]
  exact aaDer_symp ha (by linarith) hw _ _

/-! ### The field of `P_ξ` -/

variable (m : ℝ) (hm : 0 < m)

/-- **The field `X_{P_ξ}`** (`bpW:w5:action-angle` (v)), `p+1`-representatives:
`X_{Q̃} + D𝒜_ξ⁻¹ (X_{G^{nor}} + X_K) ∘ 𝒜_ξ`. -/
def aaXP {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase) : KamPhase :=
  aaXQt m hm ha (p := p) (by linarith) w + aaDerInv a (p + 1) ξ w
    (birkHamNorX m hm ha hp (aaMap a p ξ w) + aaXKext m hm ha hp (aaMap a p ξ w))

variable {m hm}

section Smoothing

variable {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

theorem birkHamNor_classA :
    IsBirkClassA a p ha (by linarith) Set.univ (birkHamNor m hm ha hp) (birkHamNorX m hm ha hp) :=
  birkQuart_isClassA m hm ha hp (birkCoefNor_isCoef m hm)

theorem aaKext_analyticOnNhd : AnalyticOnNhd ℂ (aaKext m hm ha hp) (birkBall1 m p) :=
  birkK_analyticOnNhd (aaKext m hm ha hp) (aaKext_isExtension m hm ha hp)

theorem aaXKext_analyticOnNhd : AnalyticOnNhd ℂ (aaXKext m hm ha hp) (birkBall1 m p) :=
  birkXK_analyticOnNhd (aaXKext m hm ha hp) (aaXKext_isExtension m hm ha hp)

theorem aaKext_field {w' : BirkSpace} (hw' : w' ∈ birkBall1 m p) (v : BirkSpace) :
    fderiv ℂ (aaKext m hm ha hp) w' v =
      birkOmegaPlus a p ha (by linarith) (aaXKext m hm ha hp w') v := by
  rw [birkK_field (aaKext m hm ha hp) (aaKext_isExtension m hm ha hp) ⟨w', hw'⟩ v]
  simp [aaXKext, hw']

theorem differentiableAt_aaXQt (w : KamPhase) :
    DifferentiableAt ℂ (aaXQt m hm ha (by linarith : 0 ≤ p)) w := by
  have hS : DifferentiableAt ℂ (aaSfun m hm ha (by linarith : 0 ≤ p)) w :=
    (hasFDerivAt_aaSfun ha (by linarith) w).differentiableAt
  have hY : ∀ i : Fin 2, DifferentiableAt ℂ (fun w : KamPhase => w.2.1 i) w := fun i =>
    ((ContinuousLinearMap.proj i).comp aaPrY).differentiableAt
  have hB : DifferentiableAt ℂ (fun w : KamPhase => aaBdot m hm w.2.1) w := by
    unfold aaBdot
    fun_prop
  unfold aaXQt
  refine DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk (differentiableAt_const _)
    (DifferentiableAt.prodMk ?_ ?_))
  · refine differentiableAt_pi.2 fun i => ?_
    fun_prop
  · exact hB.smul ((aaDiagE m hm).differentiableAt.comp w aaPrV.differentiableAt)
  · exact (hB.smul ((aaDiagE m hm).differentiableAt.comp w aaPrU.differentiableAt)).neg

/-- Helper (`P_ξ ∈ 𝒮_{p+1}(V)`) on any open `V` on which `𝒜_ξ` is defined (`Re(ξ_i + y_i) > 0`) and
maps into `B_{ρ₁}`; the source-facing statement is `aaP_isSmoothing`. -/
theorem aaP_isSmoothing_of (ξ : Fin 2 → ℂ) {V : Set KamPhase} (hV : IsOpen V)
    (hVd : ∀ w ∈ V, (∀ i, 0 < (ξ i + w.2.1 i).re) ∧ aaMap a p ξ w ∈ birkBall1 m p) :
    IsSmoothing (p := p) (pb := p + 1) ha (by linarith) V (aaPfun m hm ha hp ξ)
      (aaXP m hm ha hp ξ) := by
  have hp0 : 0 ≤ p := by linarith
  have hball := isOpen_birkBall1 m p
  -- derivatives of the three pieces at `w ∈ V`
  have hder : ∀ w ∈ V, HasFDerivAt (aaPfun m hm ha hp ξ)
      (fderiv ℂ (aaQt m hm a p) w +
        (fderiv ℂ (birkHamNor m hm ha hp) (aaMap a p ξ w)).comp (aaDer a p ξ w) +
        (fderiv ℂ (aaKext m hm ha hp) (aaMap a p ξ w)).comp (aaDer a p ξ w)) w := by
    intro w hw
    obtain ⟨hpos, hB⟩ := hVd w hw
    have h1 := (aaQt_hasFDerivAt (m := m) (hm := hm) ha hp0 w).1
    have hGd : DifferentiableAt ℂ (birkHamNor m hm ha hp) (aaMap a p ξ w) :=
      ((birkHamNor_classA ha hp).analytic _ trivial).differentiableAt
    have hKd : DifferentiableAt ℂ (aaKext m hm ha hp) (aaMap a p ξ w) :=
      (aaKext_analyticOnNhd ha hp _ hB).differentiableAt
    have h2 := hGd.hasFDerivAt.comp w (hasFDerivAt_aaMap a p hpos)
    have h3 := hKd.hasFDerivAt.comp w (hasFDerivAt_aaMap a p hpos)
    exact (h1.add h2).add h3
  refine ⟨fun w hw => (hder w hw).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro w hw
    obtain ⟨hpos, hB⟩ := hVd w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold aaXP
    refine (differentiableAt_aaXQt ha hp w).add (differentiableAt_aaDerInv_apply a (p + 1) hpos ?_)
    have hmap : DifferentiableAt ℂ (aaMap a p ξ) w := (hasFDerivAt_aaMap a p hpos).differentiableAt
    exact (((birkHamNor_classA ha hp).analytic_field _ trivial).differentiableAt.comp w hmap).add
      ((aaXKext_analyticOnNhd ha hp _ hB).differentiableAt.comp w hmap)
  · intro w hw W
    obtain ⟨hpos, hB⟩ := hVd w hw
    rw [(hder w hw).fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      (aaQt_hasFDerivAt (m := m) (hm := hm) ha hp0 w).2 W]
    have hGd : DifferentiableAt ℂ (birkHamNor m hm ha hp) (aaMap a p ξ w) :=
      ((birkHamNor_classA ha hp).analytic _ trivial).differentiableAt
    have hKd : DifferentiableAt ℂ (aaKext m hm ha hp) (aaMap a p ξ w) :=
      (aaKext_analyticOnNhd ha hp _ hB).differentiableAt
    have e2 := (hasFDerivAt_comp_aaMap ha hp0 hpos hGd.hasFDerivAt
      (X := birkHamNorX m hm ha hp (aaMap a p ξ w))
      (fun v => (birkHamNor_classA ha hp).field _ trivial v)).2 W
    have e3 := (hasFDerivAt_comp_aaMap ha hp0 hpos hKd.hasFDerivAt
      (X := aaXKext m hm ha hp (aaMap a p ξ w)) (fun v => aaKext_field ha hp hB v)).2 W
    rw [e2, e3, aaXP, stepSymp_add_left, map_add, stepSymp_add_left, add_assoc]

/-- **`P_ξ ∈ 𝒮_{p+1}(D(s,r))`** (`bpW:w5:action-angle` (v), `a = p = 1`), on the domain of (ii)
with `𝒜_ξ(D(s,r)) ⊂ B_{ρ₁}`: holomorphic with field `aaXP` (values in `𝒫^{p+1}`). -/
theorem aaP_isSmoothing {s r t : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r) (ht : 0 < t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ t)
    (hre : ∀ i, 2 * r ^ 2 ≤ (ξ i).re) :
    IsSmoothing (p := 1) (pb := 1 + 1) (zero_le_one' ℝ) (by norm_num) (kamDomain s r)
      (aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ξ)
      (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ξ) :=
  aaP_isSmoothing_of (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ξ (kamDomain_isOpen s r) fun w hw =>
    ⟨fun i => lt_trans (by positivity) ((aaMap_domain hs hr ht ξ hξ hre hw).1 i),
      aaMap_mem_birkBall1 m hm hs hr ht hρ₁ ξ hξ hre hw⟩

/-! ### Reality and periodicity -/

theorem aaQt_congr {w w' : KamPhase} (h : w.2 = w'.2) : aaQt m hm a p w = aaQt m hm a p w' := by
  unfold aaQt aaZZ
  simp only [stepZ_apply', stepZb_apply', h]

/-- `P_ξ` is `1`-periodic in each `θ_i`. -/
theorem aaPfun_add_tau (ξ : Fin 2 → ℂ) (w : KamPhase) (k : Fin 2) :
    aaPfun m hm ha hp ξ (w + stepTau k) = aaPfun m hm ha hp ξ w := by
  unfold aaPfun
  rw [aaMap_add_tau, aaQt_congr (show (w + stepTau k).2 = w.2 by simp [stepTau])]

theorem im_eq_zero_of_conj {z : ℂ} (h : starRingEnd ℂ z = z) : z.im = 0 :=
  Complex.conj_eq_iff_im.1 h

/-- `P_ξ` is real at real points for real `ξ` (where `𝒜_ξ(w) ∈ B_{ρ₁}`). -/
theorem aaPfun_real (ξ : Fin 2 → ℝ) (w : KamPhase) (hw : StepReal w)
    (hpos : ∀ i, 0 < ξ i + (w.2.1 i).re)
    (hB : aaMap a p (fun i => (ξ i : ℂ)) w ∈ birkBall1 m p) :
    (aaPfun m hm ha hp (fun i => (ξ i : ℂ)) w).im = 0 := by
  have hrho := aaMap_real a p ξ w hw hpos
  have hQ : starRingEnd ℂ (aaQt m hm a p w) = aaQt m hm a p w := by
    have hy : ∀ i, starRingEnd ℂ (w.2.1 i) = w.2.1 i := fun i => Complex.conj_eq_iff_im.2 (hw.2.1 i)
    have hu : ∀ j, starRingEnd ℂ (w.2.2.1 j) = w.2.2.1 j :=
      fun j => Complex.conj_eq_iff_im.2 (hw.2.2.1 j)
    have hv : ∀ j, starRingEnd ℂ (w.2.2.2 j) = w.2.2.2 j :=
      fun j => Complex.conj_eq_iff_im.2 (hw.2.2.2 j)
    unfold aaQt aaZZ aaBdot
    simp only [map_add, map_mul, map_sum, map_div₀, Complex.conj_tsum, Complex.conj_ofReal, hy,
      stepZ_apply', stepZb_apply', map_sub, hu, hv, Complex.conj_I, map_pow,
      map_ofNat, map_one]
    congr 1
    refine tsum_congr fun j => ?_
    ring
  have hG : starRingEnd ℂ (birkHamNor m hm ha hp (aaMap a p (fun i => (ξ i : ℂ)) w)) =
      birkHamNor m hm ha hp (aaMap a p (fun i => (ξ i : ℂ)) w) := by
    have := (birkHamNor_classA (m := m) (hm := hm) ha hp).real
      (aaMap a p (fun i => (ξ i : ℂ)) w) trivial
    rw [hrho] at this
    exact this.symm
  have hK : starRingEnd ℂ (aaKext m hm ha hp (aaMap a p (fun i => (ξ i : ℂ)) w)) =
      aaKext m hm ha hp (aaMap a p (fun i => (ξ i : ℂ)) w) := by
    have := birkK_rho (m := m) (hm := hm) (ha := ha) (hp := hp)
      ⟨aaMap a p (fun i => (ξ i : ℂ)) w, hB⟩
    simp only [hrho] at this
    simp only [aaKext, hB, dite_true]
    exact this.symm
  unfold aaPfun
  exact im_eq_zero_of_conj (by rw [map_add, map_add, hQ, hG, hK])

end Smoothing

end KAM.Wave

end
