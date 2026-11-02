/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainRealTori

/-!
# Real-coordinate identities (blueprint-W `bpW:w3:main` (ii), `bpW:w3:gamma-real` (iv))

Package W3-MAIN, blueprint labels `bpW:w3:main`, `bpW:w3:gamma-real`.

* `birkKExt_real_fderiv`: `D K^ℝ(x) h = ω_ℝ(Π ι X_K(𝒵x), h)`; in coefficients
  (`birkKExt_real_gradient`): `X_K^ℝ = (∂_p K^ℝ, -∂_q K^ℝ)`, i.e.
  `D K^ℝ(x) h = Σ_j [(X_K^ℝ)^q_j h^p_j - (X_K^ℝ)^p_j h^q_j]`;
* `birkGbarR`, `birkHamBar_birkZR`: `Ḡ(𝒵x) = ½ ⟨A I, I⟩ + ⟨B I, Z⟩`, `I_j = (q_j² + p_j²)/2`;
* `birkLambda_birkZR`, `birkH_gammaR_aux`: `H(Γ^ℝ x) = Λ(x) + Ḡ(x) + G^{nor}(x) + K(𝒵x)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
/-- (`bpW:w3:main` (ii)) `D K^ℝ(x) h = ω_ℝ(X_K^ℝ(x), h)` with `X_K^ℝ = Π ι X_K(𝒵 x)` the real
restriction of the field (read at weight `p`), `ω_ℝ = Σ dq ∧ dp`. -/
theorem birkKExt_real_fderiv (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) (h : BirkReal) :
    fderiv ℝ (fun y : BirkReal => (birkKExt m hm ha hp (birkZR y)).re) x h =
      birkOmegaR a p
        (birkPi (birkEmbed a (p + 1) p (by linarith) (birkXKExt m hm ha hp (birkZR x)))) h := by
  have hcls := birkKExt_isClassA (ha := ha) (hm := hm) (hp := hp)
  have hw := birkZR_dom (hm := hm) (hp := hp) x hx
  have hKd : DifferentiableAt ℂ (birkKExt m hm ha hp) (birkZR x) :=
    (hcls.analytic _ hw).differentiableAt
  have hd : HasFDerivAt (fun y : BirkReal => (birkKExt m hm ha hp (birkZR y)).re)
      (Complex.reCLM.comp (((fderiv ℂ (birkKExt m hm ha hp) (birkZR x)).restrictScalars ℝ).comp
        birkZR)) x :=
    Complex.reCLM.hasFDerivAt.comp x
      ((hKd.hasFDerivAt.restrictScalars ℝ).comp x birkZR.hasFDerivAt)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply]
  rw [hcls.field _ hw, birkOmegaPlus_eq]
  have hρ : birkRho (birkEmbed a (p + 1) p (by linarith) (birkXKExt m hm ha hp (birkZR x))) =
      birkEmbed a (p + 1) p (by linarith) (birkXKExt m hm ha hp (birkZR x)) := by
    rw [birkRho_birkEmbed, ← hcls.field_rho hw, birkRho_birkZR]
  have hz := birkZR_birkPi _ hρ
  conv_lhs => rw [← hz]
  rw [birkOmega_birkZR ha (by linarith), Complex.ofReal_re]

/-- The coefficients of `Π ι y` at weight `p` are those of `Π y` at weight `p + 1`. -/
theorem coeffW_birkPi_embed_fst (y : BirkSpace) (j : ℕ+) (hr : p ≤ p + 1) :
    coeffW (K := ℝ) a p (birkPi (birkEmbed a (p + 1) p hr y)).1 j =
      coeffW (K := ℝ) a (p + 1) (birkPi y).1 j := by
  rw [coeffW_birkPi_fst, coeffW_birkPi_fst, birkCoord_birkEmbed, birkCoord_birkEmbed]

theorem coeffW_birkPi_embed_snd (y : BirkSpace) (j : ℕ+) (hr : p ≤ p + 1) :
    coeffW (K := ℝ) a p (birkPi (birkEmbed a (p + 1) p hr y)).2 j =
      coeffW (K := ℝ) a (p + 1) (birkPi y).2 j := by
  rw [coeffW_birkPi_snd, coeffW_birkPi_snd, birkCoord_birkEmbed, birkCoord_birkEmbed]

include hm hp in
/-- (`bpW:w3:main` (ii)) `X_K^ℝ = (∂_p K^ℝ, -∂_q K^ℝ)`, as the identity of differentials
`D K^ℝ(x) h = Σ_j [(X_K^ℝ)^q_j h^p_j - (X_K^ℝ)^p_j h^q_j]` where `(X_K^ℝ)^q, (X_K^ℝ)^p` are the
actual coefficients (weight `p + 1`) of `Π X_K(𝒵x)` and `h^q, h^p` those of `h` (weight `p`):
`∂_{p_j} K^ℝ = (X_K^ℝ)^q_j`, `∂_{q_j} K^ℝ = -(X_K^ℝ)^p_j`. -/
theorem birkKExt_real_gradient (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) (h : BirkReal) :
    fderiv ℝ (fun y : BirkReal => (birkKExt m hm ha hp (birkZR y)).re) x h =
      ∑' j : ℕ+, (coeffW (K := ℝ) a (p + 1) (birkPi (birkXKExt m hm ha hp (birkZR x))).1 j *
          coeffW (K := ℝ) a p h.2 j -
        coeffW (K := ℝ) a (p + 1) (birkPi (birkXKExt m hm ha hp (birkZR x))).2 j *
          coeffW (K := ℝ) a p h.1 j) := by
  rw [birkKExt_real_fderiv (ha := ha) (hm := hm) (hp := hp) x hx h, birkOmegaR]
  refine tsum_congr fun j => ?_
  rw [coeffW_birkPi_embed_fst, coeffW_birkPi_embed_snd]

/-- The action `I_j = (q_j² + p_j²)/2` of a real point (actual coefficients at weight `(a,p)`). -/
def birkActionR (a p : ℝ) (x : BirkReal) (j : ℕ+) : ℝ :=
  (coeffW (K := ℝ) a p x.1 j ^ 2 + coeffW (K := ℝ) a p x.2 j ^ 2) / 2

/-- `Ḡ` on real points: `½ Σ_{i,i'∈J} A_{ii'} I_i I_{i'} + Σ_{i∈J} Σ_{j≥3} B_{ji} I_i I_j`. -/
def birkGbarR (m : ℝ) (hm : 0 < m) (a p : ℝ) (x : BirkReal) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 2, ∑ i' : Fin 2, actionA m hm i i' *
      (birkActionR a p x (modeIdx i) * birkActionR a p x (modeIdx i')) +
    ∑ i : Fin 2, ∑' j : ℕ+, (if 3 ≤ (j : ℕ) then
      birkActionB m hm j i * (birkActionR a p x (modeIdx i) * birkActionR a p x j) else 0)

theorem birkAction_birkZR (x : BirkReal) (j : ℕ+) :
    birkAction a p (birkZR x) j = ((birkActionR a p x j : ℝ) : ℂ) := by
  rw [birkAction, birkZR_apply, birkCoord_mul_birkZ]
  simp [birkActionR]

include hm hp in
/-- (`bpW:w3:gamma-real` (iv)) On real points `Ḡ(𝒵 x) = ½ ⟨A I, I⟩ + ⟨B I, Z⟩`,
`I_j = (q_j² + p_j²)/2`. -/
theorem birkHamBar_birkZR (x : BirkReal) :
    birkHamBar m hm ha hp (birkZR x) = ((birkGbarR m hm a p x : ℝ) : ℂ) := by
  unfold birkHamBar
  rw [birkQuartP_bar m hm ha hp (birkZR x)]
  simp only [birkAction_birkZR, birkGbarR]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => tsum_congr fun j => ?_
  split_ifs <;> simp

include hm hp in
/-- (`bpW:w3:gamma-real` (iv)) `Λ(𝒵 x) = Σ_j λ_j I_j` on real points. -/
theorem birkLambda_birkZR (x : BirkReal) :
    birkLambda m hm ha hp (birkZR x) = ((∑' j : ℕ+, lam m hm j * birkActionR a p x j : ℝ) : ℂ) := by
  rw [birkZR_apply, birkLambda_birkZ, Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  simp [birkActionR]

include hm hp in
/-- (`bpW:w3:gamma-real` (iv)) For real `x` in the ball, with `y = Γ^ℝ x`:
`(Λ + G)(𝒵 y) = Λ(𝒵 x) + Ḡ(𝒵 x) + G^{nor}(𝒵 x) + K(𝒵 x)` (the real form of
`H(Γ^ℝ x) = Λ(x) + Ḡ(x) + G^{nor}(x) + K(𝒵x)`, `H = Λ + G`), with `Λ`, `Ḡ` as in
`birkLambda_birkZR`, `birkHamBar_birkZR`. -/
theorem birkH_gammaR_aux (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) :
    birkLambda m hm ha hp (birkZR (birkGammaRExt m hm ha hp x)) +
        birkHamG m hm ha hp (birkZR (birkGammaRExt m hm ha hp x)) =
      ((∑' j : ℕ+, lam m hm j * birkActionR a p x j : ℝ) : ℂ) +
        ((birkGbarR m hm a p x : ℝ) : ℂ) + birkHamNor m hm ha hp (birkZR x) +
        birkKExt m hm ha hp (birkZR x) := by
  have hw160 := birkZR_dom (hm := hm) (hp := hp) x hx
  have hfix := birkGamma_one_fixed (ha := ha) (hm := hm) (hp := hp) (birkZR x)
    (birkRho_birkZR x) hw160
  have hz : birkZR (birkGammaRExt m hm ha hp x) = birkGamma m hm ha hp 1 (birkZR x) :=
    birkZR_birkPi _ hfix
  rw [hz, ← birkLambda_birkZR (ha := ha) (hm := hm) (hp := hp), ← birkHamBar_birkZR
    (ha := ha) (hm := hm) (hp := hp)]
  unfold birkKExt
  ring

end KAM.Wave

end
