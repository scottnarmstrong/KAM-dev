/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep.Drift
public import KAM.EffectiveStability.Torus

/-!
# One-generator Fourier–Taylor normalization ⇒ certified torus confinement (track B, B4-TSTEP)

`torusStep_confinement`: the soundness theorem of the torus checker for ONE generator `χ`. Every
premise is finite data (Fourier–Taylor polynomials with `ℚ` coefficients, radii lists) or a real
inequality between `ℚ`-computable majorants; no premise mentions the flow, the remainder, or
confinement.

* `hid`: the exact identity `∑_{j<L} (j!)⁻¹ ad_χ^j H = Nact(J) + P` (`ftEqCheck`), with `Nact` a
  polynomial in the actions only (`ftActOnly`);
* `hJ`, `hφ`: majorants `ftSupBound (∂_J χ) ≤ ε σ'` and `ftSupBound (∂_φ χ) ≤ ε ρ'` (small field
  of the generator on `cstripOpen σ ρ`), the strip check `1/(1-2 πub σ) ≤ λ`;
* domain inequalities (chart domain, Cauchy discs) and the drift inequality
  `ftAngleDriftBound P j πub b + B / (L! δc) ≤ η_j`, `B = ftSupBound (ftAdPow χ L H) πub λ ρ`.

The conclusion is that of `torus_confinement` for `V = univ`, the physical Hamiltonian
`ftEvalR H`, and the chart `Ψ = realFlow φ Ω 1` of the time-one map of the complexified generator.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set KAM.Canonical

variable {n : ℕ}

/-- The torus chart `Ψ`: the real time-one map of the flow of the complexified generator `χ` on
the open strip × polydisc `cstripOpen σ ρ`. -/
def torusChart (χ : FTPoly) (σ ρ : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) 1

/-- The inverse torus chart `Ψinv`: the real time-`(-1)` map. -/
def torusChartInv (χ : FTPoly) (σ ρ : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) (cstripOpen σ ρ) (-1)

/-- **One-step torus soundness** (track B, B4-TSTEP): a single exact finite Lie-sum identity plus
rational/real majorant inequalities certify torus confinement for the physical flow. -/
theorem torusStep_confinement {H χ Nact P : FTPoly}
    (hH : FTFits n H) (hχ : FTFits n χ) (hP : FTFits n P)
    (hA : ftActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : ftEqCheck (ftLieSum χ H L) (ftAdd Nact P) = true)
    {σ ρ σ' ρ' δc ε : ℝ} (hσ' : 0 < σ') (hρ' : 0 < ρ') (hδc : 0 < δc) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) {πub lam : ℚ} (hπ : Real.pi ≤ ((πub : ℚ) : ℝ))
    (hx : 2 * ((πub : ℚ) : ℝ) * σ < 1)
    (hlam : 1 / (1 - 2 * ((πub : ℚ) : ℝ) * σ) ≤ ((lam : ℚ) : ℝ))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hJ : ∀ i : Fin n, ((ftSupBound (ftDJ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * σ')
    (hφ : ∀ i : Fin n, ((ftSupBound (ftDφ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * ρ')
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (bl : List ℚ) (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i)
    (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hσσ' : σ' < σ) (hdom1 : ∀ i, b i + εb + ρ' ≤ ρ) (hσc : δc + σ' / 2 < σ)
    (hr3 : ∀ i, r i + δc + ρ' / 2 < ρ) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j πub bl : ℚ) : ℝ) +
      ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) / ((L.factorial : ℝ) * δc) ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = torusChart χ σ ρ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = torusChart χ σ ρ w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → torusChart χ σ ρ (torusChartInv χ σ ρ (z t)) = z t ∧
        ∀ j, |(torusChartInv χ σ ρ (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧
          |(torusChartInv χ σ ρ (z t)).2 j| ≤ a j + η j * T := by
  have hσ0 : 0 ≤ σ := by linarith
  have hlam0 : 0 < lam := by
    have h1 : 0 < 1 - 2 * ((πub : ℚ) : ℝ) * σ := by linarith
    have : (0 : ℝ) < ((lam : ℚ) : ℝ) := lt_of_lt_of_le (by positivity) hlam
    exact_mod_cast this
  have hstrip := strip_le_log_lam hπ hσ0 hx hlam
  have hS := smallField_of_ftBounds hχ hσ' hρ' hπ hlam0 hstrip ρl hρl hε0 hε hJ hφ
  have hφd := (ftEvalC_differentiable (n := n) χ).differentiableOn (s := cstripOpen σ ρ)
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cstripOpen σ ρ →
      (ftEvalC χ (KAM.realInclusion₂ n x)).im = 0 := fun x _ => ftEvalC_realInclusion₂_im χ x
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hDsub : cyl (fun j => b j + εb) ⊆
      realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) 1 :=
    cyl_subset_realInterior_cstrip hρ' hσ' hσσ' hdom1
  have hDsub2 : cyl (fun j => b j + εb) ⊆
      realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) :=
    hDsub.trans (realInterior_mono (by norm_num))
  have hΨ : ContDiffOn ℝ 2 (torusChart χ σ ρ) {w | ∀ j, |w.2 j| < b j + εb} :=
    ((contDiffOn_realFlow hS h1).of_le (WithTop.coe_le_coe.2 le_top)).mono hDsub2
  have hHΨ : ContDiffOn ℝ 2 (fun w => ftEvalR H (torusChart χ σ ρ w))
      {w | ∀ j, |w.2 j| < b j + εb} :=
    (ftEvalR_contDiff (n := n) H 2).comp_contDiffOn hΨ
  have hNd : Differentiable ℝ (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      ftEvalR Nact ((0 : Fin n → ℝ), w.2)) :=
    ((ftEvalR_contDiff (n := n) Nact 1).comp
      (contDiff_const.prodMk contDiff_snd)).differentiable one_ne_zero
  have hper : ∀ m : Fin n → ℤ, ∀ w ∈ cstripOpen (n := n) σ ρ,
      ftEvalC χ (w + ((fun i => (m i : ℂ)), 0)) = ftEvalC χ w :=
    fun m w _ => ftEvalC_add_period χ w m
  have hdomc : ∀ i, b i + ρ' < ρ := fun i => by linarith [hdom1 i]
  refine torus_confinement a b η εb T hεb hT hη hmargin univ isOpen_univ
    (fun w => ftEvalR H w) (ftEvalR_contDiff H 2).contDiffOn
    (torusChart χ σ ρ) (torusChartInv χ σ ρ) hΨ (fun _ _ => mem_univ _)
    (fun w hw u v => realFlow_symplectic hφd hS hreal h1 (hDsub2 hw) u v)
    (fun w hw => realFlow_neg_realFlow_one (isOpen_cstripOpen σ ρ) hφd hS hreal (hDsub hw))
    (fun J => ftEvalR Nact ((0 : Fin n → ℝ), J))
    (fun w => ftEvalR H (torusChart χ σ ρ w) - ftEvalR Nact ((0 : Fin n → ℝ), w.2))
    (hHΨ.differentiableOn (by norm_num) |>.sub hNd.differentiableOn)
    ?_ (fun w _ => by ring) ?_ w₀ hw₀
  · intro k w hw
    have hx' := hDsub2 hw
    have h2 : (w + ((fun i => (k i : ℝ)), (0 : Fin n → ℝ))).2 = w.2 := by simp
    have h3 : ftEvalR H (torusChart χ σ ρ (w + ((fun i => (k i : ℝ)), 0))) =
        ftEvalR H (torusChart χ σ ρ w) :=
      comp_realFlow_angleShift hφd hS hreal k (hper k) (fun y => ftEvalR H y)
        (fun y => ftEvalR_add_period H y k) hx' h1
    simp only [h2]
    rw [h3]
  · intro w hw j
    have hwI : w ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2) :=
      realInterior_mono (by norm_num)
        (cylClosed_subset_realInterior_cstrip hρ' hσ' hσσ' hdomc hw)
    exact torusDrift_le hχ hH hP hA hL hδc hid hS hπ hlam0 hstrip ρl hρl bl b r η hbl hbr hσc
      hr3 hdrift hw hwI j

end KAM.EffectiveStability
