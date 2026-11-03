/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain.Domain
public import KAM.EffectiveStability.OscillatorStep.Drift

/-!
# Chains of normalization steps: the action-bracket bound (track B, B2-MULTI)

`driftAbstract_le` is the abstract form of the Cauchy argument of `stepDrift_le`: a function equal
near `x` to `P + Re G ∘ ι` with `P` polynomial and `G` holomorphic and bounded by `M` on a
`δc`-polydisc has action bracket at most the polynomial bracket bound plus `2 r_j M / δc`.
`chainDrift_le` specializes to `R = H ∘ Ψ - Nact ∘ I` of a chain.
-/

@[expose] public noncomputable section

open Set KAM.Canonical Filter
open scoped Topology

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ}

/-- Abstract drift bound: polynomial part by `cartSupBound`, holomorphic part by Cauchy. -/
theorem driftAbstract_le {R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {P : CartPoly} (hP : CartFits n P)
    {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hxU : KAM.realInclusion₂ n x ∈ U)
    (hev : R =ᶠ[𝓝 x] fun y => cartEval P y + (G (KAM.realInclusion₂ n y)).re)
    {δc M : ℝ} (hδc : 0 < δc) (hsub : cpolydisc (KAM.realInclusion₂ n x) δc ⊆ U)
    (hM : ∀ w ∈ cpolydisc (KAM.realInclusion₂ n x) δc, ‖G w‖ ≤ M)
    (rl : List ℚ) (r η : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hxr : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i) (j : Fin n)
    (hdrift : ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * M / δc) :
    |x.1 j * fderiv ℝ R x (0, Pi.single j 1) - x.2 j * fderiv ℝ R x (Pi.single j 1, 0)| ≤
      η j := by
  have hdP : DifferentiableAt ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => cartEval P y) x :=
    ((contDiff_eval (𝕜 := ℝ) P 1).differentiable one_ne_zero).differentiableAt
  have hdRe := differentiableAt_realPart hU hG hxU
  have hfd : ∀ v, fderiv ℝ R x v =
      fderiv ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => cartEval P y) x v +
        fderiv ℝ (fun y => (G (KAM.realInclusion₂ n y)).re) x v := by
    intro v
    rw [hev.fderiv_eq, fderiv_fun_add hdP hdRe]
    rfl
  rw [hfd, hfd, fderiv_eval_p, fderiv_eval_q]
  have hpoly := CartPoly.abs_actionBracket_le_supBound P hP j rl x
    (fun i => by rw [hrl]; exact (hxr i).1) (fun i => by rw [hrl]; exact (hxr i).2)
  have hcau := abs_actionBracket_le_of_cauchy hU hG hxU hδc hsub hM j
  have hM0 : 0 ≤ M / δc := by
    refine div_nonneg (le_trans (norm_nonneg _) (hM (KAM.realInclusion₂ n x) ?_)) hδc.le
    intro i
    simp [hδc.le]
  have hxj : |x.1 j| + |x.2 j| ≤ 2 * r j := by linarith [(hxr j).1, (hxr j).2]
  have hcau' : (|x.1 j| + |x.2 j|) * (M / δc) ≤ 2 * r j * M / δc := by
    calc _ ≤ 2 * r j * (M / δc) := mul_le_mul_of_nonneg_right hxj hM0
      _ = _ := by ring
  have e : x.1 j * (cartEval (cartDp j P) x + fderiv ℝ (fun y => (G
        (KAM.realInclusion₂ n y)).re) x (0, Pi.single j 1)) -
      x.2 j * (cartEval (cartDq j P) x + fderiv ℝ (fun y => (G
        (KAM.realInclusion₂ n y)).re) x (Pi.single j 1, 0)) =
      (x.1 j * cartEval (cartDp j P) x - x.2 j * cartEval (cartDq j P) x) +
      (x.1 j * fderiv ℝ (fun y => (G (KAM.realInclusion₂ n y)).re) x (0, Pi.single j 1) -
        x.2 j * fderiv ℝ (fun y => (G (KAM.realInclusion₂ n y)).re) x
          (Pi.single j 1, 0)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith

theorem oscBound_of_cpolydisc {r : Fin n → ℝ} {δc : ℝ} {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hxr : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i) {w : (Fin n → ℂ) × (Fin n → ℂ)}
    (hw : w ∈ cpolydisc (KAM.realInclusion₂ n x) δc) : OscBound r δc w := by
  intro i
  obtain ⟨h1, h2⟩ := hw i
  have e1 : ‖w.1 i‖ ≤ ‖(KAM.realInclusion₂ n x).1 i‖ + ‖w.1 i - (KAM.realInclusion₂ n x).1 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).1 i) (w.1 i - (KAM.realInclusion₂ n x).1 i)
  have e2 : ‖w.2 i‖ ≤ ‖(KAM.realInclusion₂ n x).2 i‖ + ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).2 i) (w.2 i - (KAM.realInclusion₂ n x).2 i)
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
    Real.norm_eq_abs] at e1 e2 h1 h2
  constructor <;> linarith [(hxr i).1, (hxr i).2]

/-- **Chain drift bound** at a real point `x` of the closed oscillator domain. -/
theorem chainDrift_le {H Nact P : CartPoly} (hH : CartFits n H) (hN : CartFits n Nact)
    (hP : CartFits n P) (hA : cartActOnly Nact = true) {l : List OscStep}
    (hok : OscChainOK n Nact P l H) {r : Fin n → ℝ} {δc : ℝ} (hdom : OscDomOK n r δc l)
    (hδc : 0 < δc) (rl : List ℚ) (b η : Fin n → ℝ) {εb : ℝ}
    (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i) (hr0 : ∀ i, 0 ≤ r i)
    (hb : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hεb : 0 < εb)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ j, KAM.Planetary.oscillatorAction x.2 x.1 j ≤ b j)
    (j : Fin n) :
    |x.1 j * fderiv ℝ (fun w => cartEval H (oscChainMap l w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) x (0, Pi.single j 1) -
      x.2 j * fderiv ℝ (fun w => cartEval H (oscChainMap l w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) x (Pi.single j 1, 0)| ≤ η j := by
  have hl := hok.stepsOK
  obtain ⟨hUo, -⟩ := oscChainDom_isOpen_and_differentiableOn hl
  have hxr : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i := fun i =>
    CartPoly.abs_le_of_oscillatorAction_le x b r i (hx i) (by linarith [hb i]) (hr0 i)
  have hxbox : x ∈ oscBox r 0 := by
    intro i
    have hi := hx i
    simp only [KAM.Planetary.oscillatorAction] at hi
    have hbi := hb i
    constructor
    · exact abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (x.2 i)]) (hr0 i) |>.trans_eq (by ring)
    · exact abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (x.1 i)]) (hr0 i) |>.trans_eq (by ring)
  have hxB : OscBound r δc (KAM.realInclusion₂ n x) := by
    intro i
    simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
      Real.norm_eq_abs]
    constructor <;> linarith [(hxr i).1, (hxr i).2]
  have hxU : KAM.realInclusion₂ n x ∈ oscChainDom l :=
    (oscChainTheta_oscBound hl hdom hxB).1
  have hev : (fun w => cartEval H (oscChainMap l w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) =ᶠ[𝓝 x]
      fun y => cartEval P y + (oscChainRem l H (KAM.realInclusion₂ n y)).re := by
    filter_upwards [(isOpen_oscBox r 0).mem_nhds hxbox] with y hy
    rw [oscChain_identity hN hA hok hdom hy]
    ring
  refine driftAbstract_le hP hUo (differentiableOn_oscChainRem hl H) hxU hev hδc
    (fun w hw => (oscChainTheta_oscBound hl hdom (oscBound_of_cpolydisc hxr hw)).1)
    (fun w hw => norm_oscChainRem_le hH hok hdom (oscBound_of_cpolydisc hxr hw)) rl r η hrl hxr
    j (hdrift j)

end KAM.EffectiveStability
