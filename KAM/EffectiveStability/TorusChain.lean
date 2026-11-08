/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain.Drift
public import KAM.EffectiveStability.Torus

/-!
# `m`-generator Fourier–Taylor normalization ⇒ certified torus confinement (track B, B4-TMULTI)

`torusChain_confinement`: the soundness theorem of the torus checker for a FINITE LIST of
generators `χ₁, …, χ_m` (`TChStep`, outermost first), generalizing `torusStep_confinement`.
The chart is `Ψ = Φ₁ ∘ ⋯ ∘ Φ_m` (`tchChainMap`), each `Φ_k = torusChart` the real time-one flow of
`χ_k` on `cstripOpen σ_k ρ_k`; `Ψinv` is the reversed composition of time `-1` flows
(`tchChainInv`).

Premises (all finite data, exact `Bool` checks or inequalities between `ℚ`-computable
majorants; none mentions a flow, a remainder or confinement):

* `TChChainOK n Nact P l H`: per-step small-field majorants, strip checks and typing, the exact
  identities `ftEqCheck (ftLieSum χ_k Q_{k-1} L_k) Q_k = true` and
  `ftEqCheck Q_m (Nact + P) = true`;
* `TChDomOK n b r εb δc l`: the radius budget in which inner flows move angles by at most
  `∑ ε σ'` and actions by at most `∑ ε ρ'`;
* the drift inequality `ftAngleDriftBound P j + (∑_k B_k / L_k!) / δc ≤ η_j`.

The conclusion is that of `torus_confinement` for `V = univ` and the physical Hamiltonian
`ftEvalR H`. The pullback remainder is angle-periodic because each step chart is lattice
equivariant (`tchChainMap_angleShift`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

variable {n : ℕ}

/-- **`m`-generator torus soundness** (track B, B4-TMULTI): finitely many exact Lie-sum identities
plus rational/real majorant inequalities certify torus confinement for the physical flow. -/
theorem torusChain_confinement {H Nact P : FTPoly}
    (hH : FTFits n H) (hP : FTFits n P) (hA : ftActOnly Nact = true) {l : List TChStep}
    (hok : TChChainOK n Nact P l H) {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ)
    (hεb : 0 < εb) (hT : 0 ≤ T) (bl : List ℚ)
    (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i) (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hdom : TChDomOK n b r εb δc l) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j ftPiUB bl : ℚ) : ℝ) +
      (tchChainBound n l H : ℝ) / δc ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = tchChainMap l w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = tchChainMap l w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → tchChainMap l (tchChainInv l (z t)) = z t ∧
        ∀ j, |(tchChainInv l (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧
          |(tchChainInv l (z t)).2 j| ≤ a j + η j * T := by
  have hl := hok.tchStepsOK
  have hΨ : IsCanonicalChart (tchChainMap l) (tchChainInv l) (cyl (fun j => b j + εb)) univ :=
    (tchChain_isCanonical hl hdom).mono_chart (isOpen_cyl _) subset_rfl (subset_univ _)
  have hHΨ : ContDiffOn ℝ 2 (fun w => ftEvalR H (tchChainMap l w)) (cyl (fun j => b j + εb)) :=
    (ftEvalR_contDiff (n := n) H 2).comp_contDiffOn hΨ.chart_smooth
  have hNd : Differentiable ℝ (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      ftEvalR Nact ((0 : Fin n → ℝ), w.2)) :=
    ((ftEvalR_contDiff (n := n) Nact 1).comp
      (contDiff_const.prodMk contDiff_snd)).differentiable one_ne_zero
  refine torus_confinement a b η εb T hεb hT hη hmargin univ isOpen_univ
    (fun w => ftEvalR H w) (ftEvalR_contDiff H 2).contDiffOn
    (tchChainMap l) (tchChainInv l) hΨ.chart_smooth (fun _ _ => mem_univ _) hΨ.chart_symp
    hΨ.chart_leftInv (fun J => ftEvalR Nact ((0 : Fin n → ℝ), J))
    (fun w => ftEvalR H (tchChainMap l w) - ftEvalR Nact ((0 : Fin n → ℝ), w.2))
    (hHΨ.differentiableOn (by norm_num) |>.sub hNd.differentiableOn)
    ?_ (fun w _ => by ring) ?_ w₀ hw₀
  · intro k w hw
    have h2 : (w + ((fun i => (k i : ℝ)), (0 : Fin n → ℝ))).2 = w.2 := by simp
    have h3 : tchChainMap l (w + ((fun i => (k i : ℝ)), 0)) =
        tchChainMap l w + ((fun i => (k i : ℝ)), 0) :=
      tchChainMap_angleShift hl hdom k hw
    simp only [h2, h3]
    rw [ftEvalR_add_period H (tchChainMap l w) k]
  · intro w hw j
    exact tchChainDrift_le hH hP hA hok hdom hδc hεb bl η hbl hbr hdrift hw j

/-- The singleton chain's chart is the one-step torus chart. -/
theorem tchChainMap_singleton (s : TChStep) :
    tchChainMap (n := n) [s] = torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) := rfl

/-- The singleton chain's inverse is the one-step inverse torus chart. -/
theorem tchChainInv_singleton (s : TChStep) :
    tchChainInv (n := n) [s] = torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ) := rfl

/-- **One-step reduction**: the chain theorem for a one-element list, stated for the one-step
chart `torusChart` (data `s`: step checks, the Lie identity to `s.out`, and
`s.out = Nact + P` as an exact check). -/
theorem torusStep_of_chain {H Nact P : FTPoly} (hH : FTFits n H) (hP : FTFits n P)
    (hA : ftActOnly Nact = true) {s : TChStep}
    (hs : TChStepOK n s) (hid : ftEqCheck (ftLieSum s.gen H s.order) s.out = true)
    (hfin : ftEqCheck s.out (ftAdd Nact P) = true)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ)
    (hεb : 0 < εb) (hT : 0 ≤ T) (bl : List ℚ)
    (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i) (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hdom1 : ∀ i, b i + εb + (s.ρ' : ℝ) ≤ (s.ρ : ℝ))
    (hσc : δc + (s.σ' : ℝ) / 2 < (s.σ : ℝ))
    (hr3 : ∀ i, r i + δc + (s.ρ' : ℝ) / 2 < (s.ρ : ℝ)) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j ftPiUB bl : ℚ) : ℝ) +
      ((ftSupBound (ftAdPow s.gen s.order H) ftPiUB s.lam (List.replicate n s.ρ) /
        (s.order.factorial : ℚ) : ℚ) : ℝ) / δc ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ) w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → torusChart s.gen (s.σ : ℝ) (s.ρ : ℝ)
          (torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ) (z t)) = z t ∧
        ∀ j, |(torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ) (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧
          |(torusChartInv s.gen (s.σ : ℝ) (s.ρ : ℝ) (z t)).2 j| ≤ a j + η j * T := by
  have hok : TChChainOK n Nact P [s] H := ⟨hs, hid, hfin⟩
  have hdom : TChDomOK n b r εb δc [s] :=
    ⟨fun i => by simpa [tchTailJ] using hdom1 i, by simpa [tchTailA] using hσc,
      fun i => by simpa [tchTailJ] using hr3 i, trivial⟩
  exact torusChain_confinement hH hP hA hok hδc a b η εb T hεb hT bl hbl r hbr hdom hη
    (fun j => by simpa [tchChainBound] using hdrift j) hmargin w₀ hw₀

end KAM.EffectiveStability
