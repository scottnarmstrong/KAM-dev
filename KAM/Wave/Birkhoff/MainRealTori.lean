/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainRealK
public import KAM.Wave.Birkhoff.QuartIdent
public import KAM.Wave.Cubic.TriProps

/-!
# Real transport in `(Q,P)`-coefficient form (blueprint-W `bpW:w3:transport-tori`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-MAIN, blueprint label `bpW:w3:transport-tori`.

For a real torus `Ψ` (`ϱ Ψ = Ψ`), `(Q,P) = 𝒵⁻¹ Γ ∘ Ψ = Π Γ ∘ Ψ`
(`birkTransportQP`) satisfies the coefficient system of `bpW:w0:coeffsys` along `ν`:
`D_ν Q_j = λ_j P_j`, `D_ν P_j = -λ_j Q_j - 𝒢(Q)_j` with `𝒢 = waveCubic`
(`birk_transport_tori_real`), for `a > 0`.  The coefficients are `coeffW a p` of the weighted
coordinates.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

/-- `(Q,P) = 𝒵⁻¹ Γ ∘ Ψ` (the real coordinates of the transported torus point `Γ(ι Ψ θ)`). -/
def birkTransportQP (m : ℝ) (hm : 0 < m) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    (Ψ : (Fin 2 → ℝ) → BirkSpace) (θ : Fin 2 → ℝ) : BirkReal :=
  birkPi (birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)))

/-- The coefficients of `Π y` are the real parts of `(w_j ± w_{-j})/(√2, i√2)`. -/
theorem coeffW_birkPi_fst (a p : ℝ) (y : BirkSpace) (j : ℕ+) :
    coeffW (K := ℝ) a p (birkPi y).1 j =
      ((birkCoord a p y (true, j) + birkCoord a p y (false, j)) / birkSqrt2).re := by
  have : (birkPi y).1 = reLp (birkZinv y).1 := rfl
  rw [this, coeffW_reLp]
  congr 1
  simp only [coeffW_apply, birkZinv_fst_apply, birkCoord]
  field_simp

theorem coeffW_birkPi_snd (a p : ℝ) (y : BirkSpace) (j : ℕ+) :
    coeffW (K := ℝ) a p (birkPi y).2 j =
      ((birkCoord a p y (true, j) - birkCoord a p y (false, j)) /
        (Complex.I * birkSqrt2)).re := by
  have : (birkPi y).2 = reLp (birkZinv y).2 := rfl
  rw [this, coeffW_reLp]
  congr 1
  simp only [coeffW_apply, birkZinv_snd_apply, birkCoord]
  have := birkSqrt2_ne
  have := Complex.I_ne_zero
  field_simp

/-- The two coordinates `(w_j ± w_{-j})` of the derivative, at a real point `u = 𝒵 x`. -/
theorem birkTransport_coeff_aux (x : BirkReal) (z : BirkSpace) (hz :
    birkEmbed a (p + 1) p (by linarith) z = birkZR x) (j : ℕ+) :
    (coeffW (K := ℝ) a p
        (birkPi (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZR x)))).1 j =
      lam m hm j * coeffW (K := ℝ) a p x.2 j) ∧
    (coeffW (K := ℝ) a p
        (birkPi (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZR x)))).2 j =
      -(lam m hm j * coeffW (K := ℝ) a p x.1 j) -
        (waveTriSeq (K := ℝ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1)) j) := by
  have hc : ∀ l, birkCoord a p (birkXLam m hm z) l =
      -Complex.I * birkSgn l * (lam m hm l.2 : ℂ) * birkCoord a p (birkZR x) l := fun l => by
    rw [birkCoord_birkXLam, ← hz, birkCoord_birkEmbed]
  have hg : ∀ l, birkCoord a p (birkEmbed a (p + 1) p (by linarith)
      (birkQuartX m hm ha hp (birkCoefAll_isCoef m hm) (birkZR x))) l =
      -Complex.I * birkSgn l * (birkSqrt2 / 2) *
        ((waveTriSeq (K := ℝ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1) l.2 : ℝ)
          : ℂ) := fun l => by
    rw [birkCoord_birkEmbed, birkZR_apply, birkCoord_birkQuartX_birkZ m hm ha hp]
    have hcw : coeffW (K := ℂ) a p (complexifyLp x.1) =
        fun j => ((coeffW (K := ℝ) a p x.1 j : ℝ) : ℂ) := funext (coeffW_complexifyLp a p x.1)
    simp only [birkReal_apply]
    rw [hcw, waveTriSeq_ofReal]
  have h2 := birkSqrt2_sq
  have h3 := birkSqrt2_ne
  have hI := Complex.I_sq
  have hI0 := Complex.I_ne_zero
  have e1 : birkCoord a p (birkZR x) (true, j) =
      (((coeffW (K := ℝ) a p x.1 j : ℝ) : ℂ) + Complex.I * ((coeffW (K := ℝ) a p x.2 j : ℝ) : ℂ))
        / birkSqrt2 := by
    rw [birkZR_apply, birkCoord_birkZ_true]; simp
  have e2 : birkCoord a p (birkZR x) (false, j) =
      (((coeffW (K := ℝ) a p x.1 j : ℝ) : ℂ) - Complex.I * ((coeffW (K := ℝ) a p x.2 j : ℝ) : ℂ))
        / birkSqrt2 := by
    rw [birkZR_apply, birkCoord_birkZ_false]; simp
  constructor
  · rw [coeffW_birkPi_fst]
    simp only [birkCoord_add, hc, hg, e1, e2, birkSgn, ite_true,
      Bool.false_eq_true, ite_false]
    generalize lam m hm j = L
    generalize coeffW (K := ℝ) a p x.1 j = q
    generalize coeffW (K := ℝ) a p x.2 j = pp
    generalize waveTriSeq (K := ℝ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1) j = T
    have : ((-Complex.I * 1 * (L : ℂ) * (((q : ℂ) + Complex.I * pp) / birkSqrt2) +
        -Complex.I * 1 * (birkSqrt2 / 2) * T +
        (-Complex.I * -1 * L * (((q : ℂ) - Complex.I * pp) / birkSqrt2) +
          -Complex.I * -1 * (birkSqrt2 / 2) * T)) / birkSqrt2) = (((L * pp : ℝ)) : ℂ) := by
      push_cast
      field_simp
      linear_combination (-4 * (L : ℂ) * pp) * hI + (-2 * (L : ℂ) * pp) * h2
    rw [this, Complex.ofReal_re]
  · rw [coeffW_birkPi_snd]
    simp only [birkCoord_add, hc, hg, e1, e2, birkSgn, ite_true,
      Bool.false_eq_true, ite_false]
    generalize lam m hm j = L
    generalize coeffW (K := ℝ) a p x.1 j = q
    generalize coeffW (K := ℝ) a p x.2 j = pp
    generalize waveTriSeq (K := ℝ) m hm (coeffW a p x.1) (coeffW a p x.1) (coeffW a p x.1) j = T
    have : ((-Complex.I * 1 * (L : ℂ) * (((q : ℂ) + Complex.I * pp) / birkSqrt2) +
        -Complex.I * 1 * (birkSqrt2 / 2) * T -
        (-Complex.I * -1 * L * (((q : ℂ) - Complex.I * pp) / birkSqrt2) +
          -Complex.I * -1 * (birkSqrt2 / 2) * T)) / (Complex.I * birkSqrt2)) =
        (((-(L * q) - T : ℝ)) : ℂ) := by
      push_cast
      field_simp
      linear_combination (2 * (L : ℂ) * q) * h2
    rw [this, Complex.ofReal_re]

theorem waveCubic_coeffW_eq_waveTriSeq (hapos : 0 < a) (hp : 1 / 2 ≤ p)
    (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    waveCubic m hm (coeffW (K := ℝ) a p y) j =
      waveTriSeq (K := ℝ) m hm (coeffW a p y) (coeffW a p y) (coeffW a p y) j := by
  have h := congrFun (waveCubic_coeffW_eq_coeffW_triML m hm hp hapos y) j
  rw [h, coeffW_waveTriML]

include hm hp in
/-- (`bpW:w3:transport-tori`, real form) For real `Ψ` (`ϱ Ψ = Ψ`) and `a > 0`:
`(Q,P) = 𝒵⁻¹ Γ ∘ Ψ` satisfies `𝒵 (Q,P) = Γ ∘ Ψ` and the coefficient system
`D_ν Q_j = λ_j P_j`, `D_ν P_j = -λ_j Q_j - 𝒢(Q)_j` (coefficients `coeffW a p`). -/
theorem birk_transport_tori_real (hapos : 0 < a) (ν : Fin 2 → ℝ) (Ψ : (Fin 2 → ℝ) → BirkSpace)
    (hρ : ∀ θ, birkRho (Ψ θ) = Ψ θ)
    (hΨ : ∀ θ, 160 * birkCF m p * ‖birkEmbed a (p + 1) p (by linarith) (Ψ θ)‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt
      (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν)))
      (birkXLam m hm (Ψ θ) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamBarX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkHamNorX m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ))) +
        birkEmbed a (p + 1) p (by linarith)
          (birkXK m hm hapos.le hp (birkEmbed a (p + 1) p (by linarith) (Ψ θ)))) 0)
    (θ : Fin 2 → ℝ) :
    birkZR (birkTransportQP m hm hapos.le hp Ψ θ) =
        birkGamma m hm hapos.le hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)) ∧
      ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkTransportQP m hm hapos.le hp Ψ (θ + t • ν)).1 j)
          (lam m hm j * coeffW (K := ℝ) a p (birkTransportQP m hm hapos.le hp Ψ θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeffW (K := ℝ) a p
            (birkTransportQP m hm hapos.le hp Ψ (θ + t • ν)).2 j)
          (-(lam m hm j * coeffW (K := ℝ) a p (birkTransportQP m hm hapos.le hp Ψ θ).1 j) -
            waveCubic m hm (coeffW (K := ℝ) a p (birkTransportQP m hm hapos.le hp Ψ θ).1) j) 0 := by
  obtain ⟨z, hz, hd⟩ := birk_transport_tori (ha := hapos.le) (hm := hm) (hp := hp) ν Ψ hΨ hder θ
  set u := birkGamma m hm hapos.le hp 1 (birkEmbed a (p + 1) p (by linarith) (Ψ θ)) with hu
  have hρu : birkRho u = u := by
    refine birkGamma_one_fixed (ha := hapos.le) (hm := hm) (hp := hp) _ ?_ (hΨ θ)
    rw [birkRho_birkEmbed, hρ]
  have hx : birkZR (birkTransportQP m hm hapos.le hp Ψ θ) = u := birkZR_birkPi u hρu
  refine ⟨hx, fun j => ?_⟩
  have haux := birkTransport_coeff_aux (m := m) (hm := hm) (a := a) (p := p) (ha := hapos.le)
    (hp := hp) (birkTransportQP m hm hapos.le hp Ψ θ) z (hz.trans hx.symm) j
  rw [hx] at haux
  have hd' : HasDerivAt (fun t : ℝ => birkGamma m hm hapos.le hp 1
        (birkEmbed a (p + 1) p (by linarith) (Ψ (θ + t • ν))))
      (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
        (birkQuartX m hm hapos.le hp (birkCoefAll_isCoef m hm) u)) 0 := hd
  have hcub := waveCubic_coeffW_eq_waveTriSeq (m := m) (hm := hm) hapos hp
    (birkTransportQP m hm hapos.le hp Ψ θ).1 j
  constructor
  · have L1 := ((coeffWCLM (K := ℝ) a p j).comp
      ((ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).comp
        birkPi)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd'
    convert L1 using 1
    · funext t; simp [birkTransportQP]
    · simpa using haux.1.symm
  · have L1 := ((coeffWCLM (K := ℝ) a p j).comp
      ((ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).comp
        birkPi)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd'
    convert L1 using 1
    · funext t; simp [birkTransportQP]
    · rw [hcub]
      simpa using haux.2.symm

end KAM.Wave

end
