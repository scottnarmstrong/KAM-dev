/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain.Remainder
public import KAM.EffectiveStability.OscillatorStep
public import KAM.EffectiveStability.ChartChain

/-!
# Chains of normalization steps: the real chart (track B, B2-MULTI)

The composed real chart `oscChainMap l = Φ₁ ∘ ⋯ ∘ Φ_m` (time-one real flows) with its inverse
`oscChainInv l` (reversed composition of time `-1` flows). Each step is a canonical chart from the
open box `oscBox r (∑_{inner} ε δ)` onto the next box (`oscStep_isCanonicalChart`); the chain is a
canonical chart on `oscBox r 0` (`oscChain_isCanonical`), complexifies to `oscChainTheta`
(`oscChainMap_realInclusion`), and satisfies the telescoped Lie identity
`Q (Ψ w) = Nact(I w) + P w + Re (oscChainRem l Q (ι w))` (`oscChain_identity`).
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ}

/-- The open real box `|q_i|, |p_i| < r i + c`. -/
def oscBox (r : Fin n → ℝ) (c : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {y | ∀ i, |y.1 i| < r i + c ∧ |y.2 i| < r i + c}

theorem isOpen_oscBox (r : Fin n → ℝ) (c : ℝ) : IsOpen (oscBox r c) := by
  have : oscBox r c = ⋂ i, ({y : (Fin n → ℝ) × (Fin n → ℝ) | |y.1 i| < r i + c} ∩
      {y | |y.2 i| < r i + c}) := by
    ext y; simp [oscBox]
  rw [this]
  exact isOpen_iInter_of_finite fun i => IsOpen.inter
    (isOpen_lt (((continuous_apply i).comp continuous_fst).abs) continuous_const)
    (isOpen_lt (((continuous_apply i).comp continuous_snd).abs) continuous_const)

theorem oscBox_congr (r : Fin n → ℝ) {c c' : ℝ} (h : c = c') : oscBox r c = oscBox r c' := by
  rw [h]

/-- The composite real chart `Φ₁ ∘ ⋯ ∘ Φ_m`. -/
def oscChainMap : List OscStep → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | s :: l => stepChart s.gen (s.ρ : ℝ) ∘ oscChainMap l

/-- The composite inverse `Φ_m⁻¹ ∘ ⋯ ∘ Φ₁⁻¹` (time `-1` flows). -/
def oscChainInv : List OscStep → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | s :: l => oscChainInv l ∘ stepChartInv s.gen (s.ρ : ℝ)

/-- The chain of `ChartStep`s of a chain, over the boxes `oscBox r (inner displacement)`. -/
def oscChartSteps (r : Fin n → ℝ) : List OscStep → List (ChartStep n)
  | [] => []
  | s :: l => ⟨stepChart s.gen (s.ρ : ℝ), stepChartInv s.gen (s.ρ : ℝ), oscBox r (oscTail l : ℝ),
      oscBox r (oscTail (s :: l) : ℝ)⟩ :: oscChartSteps r l

theorem chartChainMap_oscChartSteps (r : Fin n → ℝ) :
    ∀ l : List OscStep, chartChainMap (oscChartSteps r l) = oscChainMap l
  | [] => rfl
  | s :: l => by
    simp only [oscChartSteps, chartChainMap, oscChainMap, chartChainMap_oscChartSteps r l]

theorem chartChainInv_oscChartSteps (r : Fin n → ℝ) :
    ∀ l : List OscStep, chartChainInv (oscChartSteps r l) = oscChainInv l
  | [] => rfl
  | s :: l => by
    simp only [oscChartSteps, chartChainInv, oscChainInv, chartChainInv_oscChartSteps r l]

theorem chartChainTarget_oscChartSteps (r : Fin n → ℝ) (l : List OscStep) :
    chartChainTarget (oscBox r 0) (oscChartSteps r l) = oscBox r (oscTail l : ℝ) := by
  cases l <;> simp [chartChainTarget, oscChartSteps, oscTail]

theorem norm_realInclusion₂_sub_coord (a b : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    ‖(KAM.realInclusion₂ n a - KAM.realInclusion₂ n b).1 i‖ = |a.1 i - b.1 i| ∧
      ‖(KAM.realInclusion₂ n a - KAM.realInclusion₂ n b).2 i‖ = |a.2 i - b.2 i| := by
  simp [KAM.realInclusion₂_apply, KAM.realInclusion_apply, ← Complex.ofReal_sub]

section Step

variable {s : OscStep}

private theorem oscStep_gen_real (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    (cartEval s.gen (KAM.realInclusion₂ n x)).im = 0 := cartEval_realInclusion₂_im s.gen x

theorem oscBox_subset_realInterior (hs : OscStepOK n s) {r : Fin n → ℝ} {c : ℝ}
    (hdom : ∀ i, r i + c + (s.δ : ℝ) < (s.ρ : ℝ)) :
    oscBox r c ⊆ realInterior (gaugeScalar (s.δ : ℝ) hs.delta_posℝ) (cpolyOpen (s.ρ : ℝ)) 1 :=
  fun _ hx => mem_realInterior_cpolyOpen hs.delta_posℝ (r := fun i => r i + c) hdom
    (fun i => ⟨(hx i).1.le, (hx i).2.le⟩)

/-- One step is a canonical chart from `oscBox r c` into `oscBox r (c + ε δ)`. -/
theorem oscStep_isCanonicalChart (hs : OscStepOK n s) {r : Fin n → ℝ} {c : ℝ}
    (hdom : ∀ i, r i + c + (s.δ : ℝ) < (s.ρ : ℝ)) :
    IsCanonicalChart (stepChart s.gen (s.ρ : ℝ)) (stepChartInv s.gen (s.ρ : ℝ)) (oscBox r c)
      (oscBox r (c + (s.ε : ℝ) * (s.δ : ℝ))) := by
  have hδ := hs.delta_posℝ
  have hS := hs.smallField hδ
  have hφ := differentiableOn_cartEval (n := n) s.gen (cpolyOpen (s.ρ : ℝ))
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cpolyOpen (s.ρ : ℝ) →
      (cartEval s.gen (KAM.realInclusion₂ n x)).im = 0 := fun x _ => oscStep_gen_real x
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hbx := oscBox_subset_realInterior hs hdom
  have hbx2 : oscBox r c ⊆ realInterior (gaugeScalar (s.δ : ℝ) hδ) (cpolyOpen (s.ρ : ℝ))
      (1 / 2) := hbx.trans (realInterior_mono (by norm_num))
  refine ⟨isOpen_oscBox r c, ?_, ?_, ?_, ?_⟩
  · exact ((contDiffOn_realFlow hS h1).of_le (WithTop.coe_le_coe.2 le_top)).mono hbx2
  · intro y hy
    have hdisp := norm_realFlow_sub_le (isOpen_cpolyOpen _) hφ hS hreal (hbx2 hy) h1
    rw [norm_gaugeScalar_apply, div_le_iff₀ hδ, abs_one, one_mul] at hdisp
    intro i
    have hc := norm_coord_le_prod (KAM.realInclusion₂ n (stepChart s.gen (s.ρ : ℝ) y) -
      KAM.realInclusion₂ n y) i
    rw [(norm_realInclusion₂_sub_coord _ _ i).1, (norm_realInclusion₂_sub_coord _ _ i).2] at hc
    have e1 := abs_sub_abs_le_abs_sub ((stepChart s.gen (s.ρ : ℝ) y).1 i) (y.1 i)
    have e2 := abs_sub_abs_le_abs_sub ((stepChart s.gen (s.ρ : ℝ) y).2 i) (y.2 i)
    have := hy i
    change ‖KAM.realInclusion₂ n (stepChart s.gen (s.ρ : ℝ) y) - KAM.realInclusion₂ n y‖ ≤ _
      at hdisp
    constructor <;> linarith [hc.1, hc.2]
  · intro w hw u v
    exact realFlow_symplectic hφ hS hreal h1 (hbx2 hw) u v
  · intro w hw
    exact realFlow_neg_realFlow_one hS.isOpen hφ hS hreal (hbx hw)

end Step

section Chain

variable {r : Fin n → ℝ} {δc : ℝ}

theorem oscChartSteps_ok {l : List OscStep} (hl : ∀ s ∈ l, OscStepOK n s)
    (hdom : OscDomOK n r δc l) :
    ChartChainOK (oscBox r 0) (oscChartSteps r l) := by
  induction l with
  | nil => exact isOpen_oscBox r 0
  | cons s l ih =>
    obtain ⟨h1, -, h3⟩ := hdom
    have hs := hl s (by simp)
    refine ⟨?_, ?_, ih (fun t ht => hl t (by simp [ht])) h3⟩
    · have := oscStep_isCanonicalChart hs (c := (oscTail l : ℝ)) h1
      have e : (oscTail (s :: l) : ℝ) = (oscTail l : ℝ) + (s.ε : ℝ) * (s.δ : ℝ) := by
        simp only [oscTail]; push_cast; ring
      rw [← e] at this
      exact this
    · rw [chartChainTarget_oscChartSteps]

/-- The composite real chart is canonical from `oscBox r 0` onto `oscBox r (∑ ε δ)`. -/
theorem oscChain_isCanonical {l : List OscStep} (hl : ∀ s ∈ l, OscStepOK n s)
    (hdom : OscDomOK n r δc l) :
    IsCanonicalChart (oscChainMap l) (oscChainInv l) (oscBox r 0) (oscBox r (oscTail l : ℝ)) := by
  have h := chartChain_isCanonical (oscBox r 0) _ (oscChartSteps_ok hl hdom)
  rw [chartChainMap_oscChartSteps, chartChainInv_oscChartSteps,
    chartChainTarget_oscChartSteps] at h
  exact h

theorem oscChainMap_realInclusion {l : List OscStep} (hl : ∀ s ∈ l, OscStepOK n s)
    (hdom : OscDomOK n r δc l) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ oscBox r 0) :
    KAM.realInclusion₂ n (oscChainMap l w) = oscChainTheta l (KAM.realInclusion₂ n w) := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨h1, -, h3⟩ := hdom
    have hl' : ∀ t ∈ l, OscStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl s (by simp)
    have hδ := hs.delta_posℝ
    have hS := hs.smallField hδ
    have hy : oscChainMap l w ∈ oscBox r (oscTail l : ℝ) :=
      (oscChain_isCanonical hl' h3).chart_maps hw
    have hy2 : oscChainMap l w ∈ realInterior (gaugeScalar (s.δ : ℝ) hδ) (cpolyOpen (s.ρ : ℝ))
        (1 / 2) := realInterior_mono (by norm_num) (oscBox_subset_realInterior hs h1 hy)
    have hφ := differentiableOn_cartEval (n := n) s.gen (cpolyOpen (s.ρ : ℝ))
    have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈
        cpolyOpen (s.ρ : ℝ) → (cartEval s.gen (KAM.realInclusion₂ n x)).im = 0 :=
      fun x _ => oscStep_gen_real x
    show KAM.realInclusion₂ n (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval s.gen w)
      (cpolyOpen (s.ρ : ℝ)) 1 (oscChainMap l w)) = oscStepFlow s (oscChainTheta l _)
    rw [realInclusion₂_realFlow (isOpen_cpolyOpen _) hφ hS hreal hy2 ⟨by norm_num, le_rfl⟩,
      ih hl' h3]
    rfl

/-- **Telescoped Lie identity** on the real box: `Q (Ψ w) = Nact(I w) + P w + Re (Rem_l (ι w))`. -/
theorem oscChain_identity {Nact P : CartPoly} (hN : CartFits n Nact)
    (hA : cartActOnly Nact = true) :
    ∀ {l : List OscStep} {Q : CartPoly}, OscChainOK n Nact P l Q → OscDomOK n r δc l →
      ∀ {w : (Fin n → ℝ) × (Fin n → ℝ)}, w ∈ oscBox r 0 →
      cartEval Q (oscChainMap l w) =
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ)) + cartEval P w +
        (oscChainRem l Q (KAM.realInclusion₂ n w)).re
  | [], Q, hok, _, w, _ => by
    have h := cartEval_eq_of_eqCheck (R := ℝ) hok w
    rw [cartEval_add, cartEval_actSubst_real Nact hN hA] at h
    simpa [oscChainMap, oscChainRem] using h
  | s :: l, Q, hok, hdom, w, hw => by
    obtain ⟨hs, hid, hrest⟩ := hok
    obtain ⟨h1, -, h3⟩ := hdom
    have hl' := OscChainOK.stepsOK hrest
    have hδ := hs.delta_posℝ
    have hS := hs.smallField hδ
    have hy : oscChainMap l w ∈ oscBox r (oscTail l : ℝ) :=
      (oscChain_isCanonical hl' h3).chart_maps hw
    have hy2 : oscChainMap l w ∈ realInterior (gaugeScalar (s.δ : ℝ) hδ) (cpolyOpen (s.ρ : ℝ))
        (1 / 2) := realInterior_mono (by norm_num) (oscBox_subset_realInterior hs h1 hy)
    have hrem := stepRem_realInclusion₂ (H := Q) hS s.order hy2
    have hth := oscChainMap_realInclusion hl' h3 hw
    have hLie := hid.cartEval_lieSum_eq (R := ℝ) (oscChainMap l w)
    have ih := oscChain_identity hN hA hrest h3 hw
    have hre : (stepRem s.gen Q (s.ρ : ℝ) s.order (oscChainTheta l (KAM.realInclusion₂ n w))).re =
        cartEval Q (stepChart s.gen (s.ρ : ℝ) (oscChainMap l w)) -
          cartEval (cartLieSum s.gen Q s.order) (oscChainMap l w) := by
      rw [← hth, hrem, Complex.ofReal_re]
      rfl
    show cartEval Q (stepChart s.gen (s.ρ : ℝ) (oscChainMap l w)) = _ +
      (stepRem s.gen Q (s.ρ : ℝ) s.order (oscChainTheta l (KAM.realInclusion₂ n w)) +
        oscChainRem l s.out (KAM.realInclusion₂ n w)).re
    rw [Complex.add_re, hre, hLie, ih]
    ring

end Chain

end KAM.EffectiveStability
