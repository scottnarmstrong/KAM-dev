/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainQuart

/-!
# The combined quartic field `X_Ḡ + X_{G^{nor}}` (blueprint-W `bpW:w3:transport-tori-weak`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-MAIN, blueprint label `bpW:w3:transport-tori-weak` (Step
`stepW:w3:wk-reg`: `‖X_Ḡ(w) + X_{G^{nor}}(w)‖ ≤ C_*‖w‖³` by `bpW:w3:quartic` applied to
`𝔊̄ + 𝔊^{nor}`, whose coefficient sets are disjoint).

* `birkGradML_add`, `birkQuartX_add`: the gradient and the field are additive in the coefficient;
* `birkBarNorSet = 𝒯 ∩ paired ∪ 𝒯ᶜ`, `birkCoefBarNor = 𝔤 · 1_{birkBarNorSet}`, with
  `birkCoefBarNor = c̄ + c^{nor}` (`birkCoefBarNor_eq`, disjoint supports);
* `birkHamBarX_add_birkHamNorX`: `X_Ḡ + X_{G^{nor}} = X_{Ḡ + G^{nor}}`;
* `norm_birkHamBarX_add_birkHamNorX_le`: `‖X_Ḡ(w) + X_{G^{nor}}(w)‖₊ ≤ C_* ‖w‖³`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c₁ c₂ c₃ : (Fin 4 → BirkIdx) → ℂ}

include ha hp in
/-- The quartic gradient `∇𝔓` is additive in the coefficient. -/
theorem birkGradML_add (hc₁ : ∀ x, ‖c₁ x‖ ≤ |birkG m hm x|) (hc₂ : ∀ x, ‖c₂ x‖ ≤ |birkG m hm x|)
    (hc₃ : ∀ x, ‖c₃ x‖ ≤ |birkG m hm x|) (h : ∀ x, c₃ x = c₁ x + c₂ x) (w : Fin 3 → BirkSpace) :
    birkGradML m hm ha hp hc₃ w = birkGradML m hm ha hp hc₁ w + birkGradML m hm ha hp hc₂ w := by
  ext l
  show birkGradSeq a p c₃ w l = birkGradSeq a p c₁ w l + birkGradSeq a p c₂ w l
  unfold birkGradSeq birkGradCoord birkGradSum
  rw [← mul_add, ← mul_add, ← Summable.tsum_add
    (summable_birkGradTerm m hm ha hp hc₁ l w)
    (summable_birkGradTerm m hm ha hp hc₂ l w)]
  congr 2
  refine tsum_congr fun y => ?_
  simp only [birkGradTerm, h, add_mul]

include ha hp in
/-- The quartic field `X_P` is additive in the coefficient. -/
theorem birkQuartX_add (hc₁ : IsBirkQuartCoef m hm c₁) (hc₂ : IsBirkQuartCoef m hm c₂)
    (hc₃ : IsBirkQuartCoef m hm c₃) (h : ∀ x, c₃ x = c₁ x + c₂ x) (w : BirkSpace) :
    birkQuartX m hm ha hp hc₃ w = birkQuartX m hm ha hp hc₁ w + birkQuartX m hm ha hp hc₂ w := by
  unfold birkQuartX birkDiagField
  rw [birkGradML_add m hm ha hp hc₁.bound hc₂.bound hc₃.bound h, smul_add]

end

/-- The coefficient set `(𝒯 ∩ paired) ∪ 𝒯ᶜ` of `Ḡ + G^{nor}`. -/
def birkBarNorSet : Set (Fin 4 → BirkIdx) := birkBarSet ∪ birkNormalSet

/-- The coefficient `𝔤 · 1_{(𝒯 ∩ paired) ∪ 𝒯ᶜ}` of `Ḡ + G^{nor}`. -/
def birkCoefBarNor : (Fin 4 → BirkIdx) → ℂ := birkQuartCoefOn m hm birkBarNorSet

theorem birkCoefBarNor_isCoef : IsBirkQuartCoef m hm (birkCoefBarNor m hm) :=
  isBirkQuartCoef_on m hm birkBarNorSet
    (fun σ x hx => hx.elim (fun h => Or.inl (birkBarSet_perm σ x h))
      (fun h => Or.inr fun t => h (σ t)))
    (fun x hx => hx.elim (fun h => Or.inl (birkBarSet_neg x h)) (fun h => Or.inr fun t => h t))

/-- The coefficient sets of `Ḡ` and `G^{nor}` are disjoint. -/
theorem birkBarSet_disjoint_birkNormalSet : Disjoint birkBarSet birkNormalSet := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨t, ht⟩, -⟩ hn
  have := hn t
  omega

/-- `c̄ + c^{nor} = 𝔤 · 1_{(𝒯 ∩ paired) ∪ 𝒯ᶜ}` (disjoint supports). -/
theorem birkCoefBarNor_eq (x : Fin 4 → BirkIdx) :
    birkCoefBarNor m hm x = birkCoefBar m hm x + birkCoefNor m hm x := by
  classical
  unfold birkCoefBarNor birkCoefBar birkCoefNor birkQuartCoefOn birkBarNorSet
  by_cases hb : x ∈ birkBarSet
  · have hn : x ∉ birkNormalSet := Set.disjoint_left.1 birkBarSet_disjoint_birkNormalSet hb
    simp [hb, hn]
  · by_cases hn : x ∈ birkNormalSet
    · simp [hb, hn]
    · simp [hb, hn]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- `X_Ḡ + X_{G^{nor}}` is the field of the single quartic form `Ḡ + G^{nor}` with coefficient
`birkCoefBarNor`. -/
theorem birkHamBarX_add_birkHamNorX (w : BirkSpace) :
    birkHamBarX m hm ha hp w + birkHamNorX m hm ha hp w =
      birkQuartX m hm ha hp (birkCoefBarNor_isCoef m hm) w :=
  (birkQuartX_add m hm ha hp (birkCoefBar_isCoef m hm) (birkCoefNor_isCoef m hm)
    (birkCoefBarNor_isCoef m hm) (birkCoefBarNor_eq m hm) w).symm

include ha hp in
/-- (`bpW:w3:transport-tori-weak`, Step `stepW:w3:wk-reg`) `‖X_Ḡ(w) + X_{G^{nor}}(w)‖₊ ≤ C_*‖w‖³`
(`bpW:w3:quartic` for the single coefficient family `c̄ + c^{nor}` with disjoint supports). -/
theorem norm_birkHamBarX_add_birkHamNorX_le (w : BirkSpace) :
    ‖birkHamBarX m hm ha hp w + birkHamNorX m hm ha hp w‖ ≤ waveCubicConst p * ‖w‖ ^ 3 := by
  rw [birkHamBarX_add_birkHamNorX]
  exact norm_birkQuartX_le m hm ha hp _ w

end

end KAM.Wave

end
