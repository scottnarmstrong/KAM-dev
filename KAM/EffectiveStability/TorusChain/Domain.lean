/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain.Remainder
public import KAM.EffectiveStability.TorusStep
public import KAM.EffectiveStability.ChartChain

/-!
# Chains of torus steps: the real chart (track B, B4-TMULTI)

The composed real chart `tchChainMap l = Φ₁ ∘ ⋯ ∘ Φ_m` (`torusChart` of each step) with its inverse
`tchChainInv l` (reversed composition of the time `-1` flows). Each step is a canonical chart from
the open cylinder `cyl c` into `cyl (c + ε ρ')` (`tchStep_isCanonicalChart`); the chain is a
canonical chart on `cyl (b + εb)` (`tchChain_isCanonical`), complexifies to `tchTheta`
(`tchChainMap_realInclusion`), satisfies the telescoped Lie identity
`Q (Ψ w) = Nact(J w) + P w + Re (tchRem l Q (ι w))` (`tchChain_identity`) and commutes with the
lattice angle shifts (`tchChainMap_angleShift`).
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- The composite real chart `Φ₁ ∘ ⋯ ∘ Φ_m`. -/
def tchChainMap : List TChStep → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | s :: l => torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) ∘ tchChainMap l

/-- The composite inverse `Φ_m⁻¹ ∘ ⋯ ∘ Φ₁⁻¹` (time `-1` flows). -/
def tchChainInv : List TChStep → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [] => id
  | s :: l => tchChainInv l ∘ torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ)

/-- The chain of `ChartStep`s of a chain over the cylinders `cyl (b + εb + inner action budget)`. -/
def tchChartSteps (b : Fin n → ℝ) (εb : ℝ) : List TChStep → List (ChartStep n)
  | [] => []
  | s :: l => ⟨torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ), torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ),
      cyl (fun j => b j + εb + (tchTailJ l : ℝ)),
      cyl (fun j => b j + εb + (tchTailJ (s :: l) : ℝ))⟩ :: tchChartSteps b εb l

theorem chartChainMap_tchChartSteps (b : Fin n → ℝ) (εb : ℝ) :
    ∀ l : List TChStep, chartChainMap (tchChartSteps b εb l) = tchChainMap l
  | [] => rfl
  | s :: l => by
    simp only [tchChartSteps, chartChainMap, tchChainMap, chartChainMap_tchChartSteps b εb l]

theorem chartChainInv_tchChartSteps (b : Fin n → ℝ) (εb : ℝ) :
    ∀ l : List TChStep, chartChainInv (tchChartSteps b εb l) = tchChainInv l
  | [] => rfl
  | s :: l => by
    simp only [tchChartSteps, chartChainInv, tchChainInv, chartChainInv_tchChartSteps b εb l]

theorem tchNorm_ric_sub (a b : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    ‖(KAM.realInclusion₂ n a - KAM.realInclusion₂ n b).1 i‖ = |a.1 i - b.1 i| ∧
      ‖(KAM.realInclusion₂ n a - KAM.realInclusion₂ n b).2 i‖ = |a.2 i - b.2 i| := by
  simp [KAM.realInclusion₂_apply, KAM.realInclusion_apply, ← Complex.ofReal_sub]

section Step

variable {s : TChStep}

private theorem tchStep_gen_real (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    (ftEvalC s.gen (KAM.realInclusion₂ n x)).im = 0 := ftEvalC_realInclusion₂_im s.gen x

theorem cyl_subset_realInterior_tch (hs : TChStepOK n s) {c : Fin n → ℝ}
    (hdom : ∀ i, c i + (s.ρ' : ℝ) ≤ (s.ρ : ℝ)) :
    cyl c ⊆ realInterior (scaleCLE (s.ρ' : ℝ) (s.σ' : ℝ) hs.ρ'_posℝ hs.σ'_posℝ)
      (cstripOpen (s.σ : ℝ) (s.ρ : ℝ)) 1 :=
  cyl_subset_realInterior_cstrip hs.ρ'_posℝ hs.σ'_posℝ hs.σ'_ltℝ hdom

/-- One step is a canonical chart from `cyl c` into `cyl c'` when `c + ε ρ' ≤ c'`. -/
theorem tchStep_isCanonicalChart (hs : TChStepOK n s) {c c' : Fin n → ℝ}
    (hdom : ∀ i, c i + (s.ρ' : ℝ) ≤ (s.ρ : ℝ)) (hcc : ∀ i, c i + (s.ε : ℝ) * (s.ρ' : ℝ) ≤ c' i) :
    IsCanonicalChart (torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ))
      (torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ)) (cyl c) (cyl c') := by
  have hS := hs.tchSmallField
  have hφ := (ftEvalC_differentiable (n := n) s.gen).differentiableOn
    (s := cstripOpen (s.σ : ℝ) (s.ρ : ℝ))
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ cstripOpen (s.σ : ℝ) (s.ρ : ℝ) →
      (ftEvalC s.gen (KAM.realInclusion₂ n x)).im = 0 := fun x _ => tchStep_gen_real x
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hbx := cyl_subset_realInterior_tch hs hdom
  have hbx2 := hbx.trans (realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num))
  refine ⟨isOpen_cyl c, ?_, ?_, ?_, ?_⟩
  · exact ((contDiffOn_realFlow hS h1).of_le (WithTop.coe_le_coe.2 le_top)).mono hbx2
  · intro y hy
    have hdisp := norm_realFlow_sub_le (isOpen_cstripOpen _ _) hφ hS hreal (hbx2 hy) h1
    rw [norm_scaleCLE, scaledNorm, abs_one, one_mul, max_le_iff, div_le_iff₀ hs.σ'_posℝ,
      div_le_iff₀ hs.ρ'_posℝ] at hdisp
    intro i
    have hc := (norm_le_pi_norm (KAM.realInclusion₂ n (torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) y) -
      KAM.realInclusion₂ n y).2 i).trans hdisp.2
    rw [(tchNorm_ric_sub _ _ i).2] at hc
    have e2 := abs_sub_abs_le_abs_sub ((torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) y).2 i) (y.2 i)
    have := hy i
    have := hcc i
    linarith
  · intro w hw u v
    exact realFlow_symplectic hφ hS hreal h1 (hbx2 hw) u v
  · intro w hw
    exact realFlow_neg_realFlow_one hS.isOpen hφ hS hreal (hbx hw)

end Step

section Chain

variable {b r : Fin n → ℝ} {εb δc : ℝ}

theorem chartChainTarget_tchChartSteps_subset (l : List TChStep) :
    chartChainTarget (cyl (fun j => b j + εb)) (tchChartSteps b εb l) ⊆
      cyl (fun j => b j + εb + (tchTailJ l : ℝ)) := by
  cases l with
  | nil => intro w hw i; simpa [tchTailJ] using hw i
  | cons s l => exact subset_rfl

theorem tchChartSteps_ok {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hdom : TChDomOK n b r εb δc l) :
    ChartChainOK (cyl (fun j => b j + εb)) (tchChartSteps b εb l) := by
  induction l with
  | nil => exact isOpen_cyl _
  | cons s l ih =>
    obtain ⟨h1, -, -, h4⟩ := hdom
    have hs := hl s (by simp)
    refine ⟨?_, chartChainTarget_tchChartSteps_subset l, ih (fun t ht => hl t (by simp [ht])) h4⟩
    exact tchStep_isCanonicalChart hs (c := fun j => b j + εb + (tchTailJ l : ℝ))
      (c' := fun j => b j + εb + (tchTailJ (s :: l) : ℝ)) (fun i => by simpa using h1 i)
      (fun i => by simp only [tchTailJ]; push_cast; linarith)

/-- The composite real chart is canonical from `cyl (b + εb)` into the cylinder enlarged by the
total action displacement. -/
theorem tchChain_isCanonical {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hdom : TChDomOK n b r εb δc l) :
    IsCanonicalChart (tchChainMap l) (tchChainInv l) (cyl (fun j => b j + εb))
      (cyl (fun j => b j + εb + (tchTailJ l : ℝ))) := by
  have h := chartChain_isCanonical (cyl (fun j => b j + εb)) _ (tchChartSteps_ok hl hdom)
  rw [chartChainMap_tchChartSteps, chartChainInv_tchChartSteps] at h
  exact h.mono_chart (isOpen_cyl _) subset_rfl (chartChainTarget_tchChartSteps_subset l)

theorem tchChainMap_realInclusion {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hdom : TChDomOK n b r εb δc l) {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : w ∈ cyl (fun j => b j + εb)) :
    KAM.realInclusion₂ n (tchChainMap l w) = tchTheta l (KAM.realInclusion₂ n w) := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨h1, -, -, h4⟩ := hdom
    have hl' : ∀ t ∈ l, TChStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl s (by simp)
    have hS := hs.tchSmallField
    have hy : tchChainMap l w ∈ cyl (fun j => b j + εb + (tchTailJ l : ℝ)) :=
      (tchChain_isCanonical hl' h4).chart_maps hw
    have hy2 := realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num)
      (cyl_subset_realInterior_tch hs (fun i => by simpa using h1 i) hy)
    have hφ := (ftEvalC_differentiable (n := n) s.gen).differentiableOn
      (s := cstripOpen (s.σ : ℝ) (s.ρ : ℝ))
    have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
        KAM.realInclusion₂ n x ∈ cstripOpen (s.σ : ℝ) (s.ρ : ℝ) →
        (ftEvalC s.gen (KAM.realInclusion₂ n x)).im = 0 :=
      fun x _ => ftEvalC_realInclusion₂_im s.gen x
    show KAM.realInclusion₂ n (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC s.gen w)
      (cstripOpen (s.σ : ℝ) (s.ρ : ℝ)) 1 (tchChainMap l w)) = tchStepFlow s (tchTheta l _)
    rw [realInclusion₂_realFlow (isOpen_cstripOpen _ _) hφ hS hreal hy2 ⟨by norm_num, le_rfl⟩,
      ih hl' h4]
    rfl

/-- **Telescoped Lie identity** on the real cylinder:
`Q (Ψ w) = Nact(0, J w) + P w + Re (Rem_l (ι w))`. -/
theorem tchChain_identity {Nact P : FTPoly} (hA : ftActOnly Nact = true) :
    ∀ {l : List TChStep} {Q : FTPoly}, TChChainOK n Nact P l Q → TChDomOK n b r εb δc l →
      ∀ {w : (Fin n → ℝ) × (Fin n → ℝ)}, w ∈ cyl (fun j => b j + εb) →
      ftEvalR Q (tchChainMap l w) =
        ftEvalR Nact ((0 : Fin n → ℝ), w.2) + ftEvalR P w +
        (tchRem l Q (KAM.realInclusion₂ n w)).re
  | [], Q, hok, _, w, _ => by
    have h := ftEvalR_eq_of_eqCheck hok w
    rw [ftEvalR_add, ftEvalR_actOnly hA w] at h
    simpa [tchChainMap, tchRem] using h
  | s :: l, Q, hok, hdom, w, hw => by
    obtain ⟨hs, hid, hrest⟩ := hok
    obtain ⟨h1, -, -, h4⟩ := hdom
    have hl' := TChChainOK.tchStepsOK hrest
    have hS := hs.tchSmallField
    have hy : tchChainMap l w ∈ cyl (fun j => b j + εb + (tchTailJ l : ℝ)) :=
      (tchChain_isCanonical hl' h4).chart_maps hw
    have hy2 := realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num)
      (cyl_subset_realInterior_tch hs (fun i => by simpa using h1 i) hy)
    have hrem := torusRem_realInclusion₂ (H := Q) hS s.order hy2
    have hth := tchChainMap_realInclusion hl' h4 hw
    have hLie := ftEvalR_eq_of_eqCheck hid (tchChainMap l w)
    have ih := tchChain_identity hA hrest h4 hw
    have hre : (torusRem s.gen Q (s.σ : ℝ) (s.ρ : ℝ) s.order
        (tchTheta l (KAM.realInclusion₂ n w))).re =
        ftEvalR Q (torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) (tchChainMap l w)) -
          ftEvalR (ftLieSum s.gen Q s.order) (tchChainMap l w) := by
      rw [← hth, hrem, Complex.ofReal_re]
      rfl
    show ftEvalR Q (torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) (tchChainMap l w)) = _ +
      (torusRem s.gen Q (s.σ : ℝ) (s.ρ : ℝ) s.order (tchTheta l (KAM.realInclusion₂ n w)) +
        tchRem l s.out (KAM.realInclusion₂ n w)).re
    rw [Complex.add_re, hre, hLie, ih]
    ring

/-- Lattice equivariance of the composite chart: every step's chart commutes with the integer
angle shifts, hence so does the chain. -/
theorem tchChainMap_angleShift {l : List TChStep} (hl : ∀ s ∈ l, TChStepOK n s)
    (hdom : TChDomOK n b r εb δc l) (m : Fin n → ℤ) {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : w ∈ cyl (fun j => b j + εb)) :
    tchChainMap l (w + KAM.ODE.angleShift m) = tchChainMap l w + KAM.ODE.angleShift m := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨h1, -, -, h4⟩ := hdom
    have hl' : ∀ t ∈ l, TChStepOK n t := fun t ht => hl t (by simp [ht])
    have hs := hl s (by simp)
    have hS := hs.tchSmallField
    have hy : tchChainMap l w ∈ cyl (fun j => b j + εb + (tchTailJ l : ℝ)) :=
      (tchChain_isCanonical hl' h4).chart_maps hw
    have hy2 := realInterior_mono (c := 1) (c' := 1 / 2) (by norm_num)
      (cyl_subset_realInterior_tch hs (fun i => by simpa using h1 i) hy)
    have hφ := (ftEvalC_differentiable (n := n) s.gen).differentiableOn
      (s := cstripOpen (s.σ : ℝ) (s.ρ : ℝ))
    have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
        KAM.realInclusion₂ n x ∈ cstripOpen (s.σ : ℝ) (s.ρ : ℝ) →
        (ftEvalC s.gen (KAM.realInclusion₂ n x)).im = 0 :=
      fun x _ => ftEvalC_realInclusion₂_im s.gen x
    show torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) (tchChainMap l (w + KAM.ODE.angleShift m)) =
      torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) (tchChainMap l w) + KAM.ODE.angleShift m
    rw [ih hl' h4]
    exact realFlow_angleShift_equivariant hφ hS hreal m
      (fun z _ => ftEvalC_add_period s.gen z m) hy2 ⟨by norm_num, le_rfl⟩

end Chain

end KAM.EffectiveStability
