/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Step
public import KAM.Sharp.ConstantsArith
public import KAM.Sharp.Engine.Limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The fixed-frequency scheme of the sharp theorem

Blueprint `bp:p2s:fixed-scheme`. `fixedScheme` is the abstract Newton scheme of
`KAM.Sharp.Engine` whose states are tori `K`, with `Adm r β ε m K` the admissibility of `K` with the
bounds `(m 0, m 1, m 2)` in place of `(σ_K, σ_B, σ_T)`, and whose step is
`K ↦ newtonMap h K ω (r - 2δ)`. `fixedScheme_isNewton` proves (N1), (N2) from
`KAM.Sharp.step_spec`; `engine_hyps` turns `𝔠_* e/(γ⁴ δ₀^{2a}) ≤ 1` into the arithmetic hypotheses
(I1)–(I4) of the engine.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {κ cR M σK σB σT γb μ : ℝ}
variable {τ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

/-- The fixed-frequency scheme (`bp:p2s:fixed-scheme`). -/
def fixedScheme (n : ℕ) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (ω : Fin n → ℝ) : Engine.Scheme n 3 ((Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) where
  tor := fun K => K
  par := fun _ => 0
  Adm := fun r β ε m K => Admissible (m 0) (m 1) (m 2) 𝔅 h ω r β ε K
  step := fun r δ K => newtonMap h K ω (r - 2 * δ)

/-- The constants of the fixed-frequency scheme (caps `σ - μ/2`). -/
def fixedConsts (n : ℕ) (κ cR M σK σB σT γb μ : ℝ) : Engine.Consts 3 where
  lam := 3
  a := 2 * κ
  CE := cE n cR M σK σB σT γb
  CD := cDK n cR M σK σB σT γb
  Cp := 0
  cstep := cStep n κ cR M σK σB σT γb
  cap := ![σK - μ / 2, σB - μ / 2, σT - μ / 2]
  rate := ![rateD n cR M σK σB σT γb, rateB n cR M σK σB σT γb, rateT n cR M σK σB σT γb]
  j := ![1, 1, 1]

/-- The engine's `δ₀` for `λ = 3` is `delta0s`. -/
theorem delta0_fixed_eq (ρ ρinf : ℝ) :
    Engine.delta0 (fixedConsts n κ cR M σK σB σT γb μ).lam ρ ρinf = delta0s ρ ρinf := rfl

/-- Positivity of the constants that the scheme needs. -/
theorem fixed_consts_pos (hC : CohData n τ κ cR) (hP : Params n τ M σK σB σT) (hγb : 0 < γb) :
    0 < cDK n cR M σK σB σT γb ∧ 0 < cE n cR M σK σB σT γb ∧ 0 < rateD n cR M σK σB σT γb ∧
      0 < rateB n cR M σK σB σT γb ∧ 0 < rateT n cR M σK σB σT γb := by
  obtain ⟨h1, h2, h3, h4, -⟩ := consts_pos (n := n) (κ := κ) (μ := 1) (by have := hP.two_le; omega)
    hC.cR_pos hP.M_pos hP.σK_pos hP.σB_pos hP.σT_pos hγb one_pos
  have hn0 : 0 < n := by have := hP.two_le; omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · unfold rateD; positivity
  · unfold rateB; positivity
  · unfold rateT vthh; have := hP.σT_pos; positivity

theorem fixedConsts_j (i : Fin 3) : ((fixedConsts n κ cR M σK σB σT γb μ).j i : ℝ) = 1 := by
  fin_cases i <;> simp [fixedConsts]

theorem norm_le_add_of_sub_le {E : Type*} [NormedAddCommGroup E] {a b : E} {c : ℝ}
    (hh : ‖a - b‖ ≤ c) : ‖a‖ ≤ ‖b‖ + c :=
  (norm_le_norm_add_norm_sub' a b).trans (by linarith)

/-- Blueprint `bp:p2s:fixed-scheme`. -/
theorem fixedScheme_isNewton (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hγb : γ ≤ γb) (hμ : 0 ≤ μ) :
    (fixedScheme n h 𝔅 ω).IsNewton (fixedConsts n κ cR M σK σB σT γb μ) γ := by
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  obtain ⟨hDK, hE, hrD, hrB, hrT⟩ := fixed_consts_pos hC hS.toParams hγb0
  have hrate : ∀ i, 0 ≤ (fixedConsts n κ cR M σK σB σT γb μ).rate i := by
    intro i; fin_cases i
    · exact hrD.le
    · exact hrB.le
    · exact hrT.le
  refine
    { lam_pos := by show (0 : ℝ) < 3; norm_num
      two_le_a := by show (2 : ℝ) ≤ 2 * κ; linarith [hC.one_le_kappa]
      CE_nonneg := hE.le
      CD_nonneg := hDK.le
      Cp_nonneg := le_refl _
      rate_nonneg := hrate
      j_le_one := by intro i; fin_cases i <;> simp [fixedConsts]
      adm := ?_
      step := ?_ }
  · intro r β ε m x hx
    have hx' : Admissible (m 0) (m 1) (m 2) 𝔅 h ω r β ε x := hx
    exact ⟨hx'.ε_nonneg, hx'.holo, hx'.primary, hx'.real⟩
  · intro r β ε δ m x hx hδ hδ1 h3 hst hβ hcap
    have hx' : Admissible (m 0) (m 1) (m 2) 𝔅 h ω r β ε x := hx
    have h3' : 3 * δ < r := h3
    have hst' : cStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1 := hst
    have hβ' : 2 * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤ β := hβ
    have hε0 := hx'.ε_nonneg
    have hpw : ∀ q : ℝ, 0 ≤ q → 0 ≤ q * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := fun q hq => by
      have : 0 < δ ^ (2 * κ + 1) := Real.rpow_pos_of_pos hδ _
      positivity
    have hc0 : m 0 + rateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σK - μ / 2 := by
      simpa [fixedConsts] using hcap 0
    have hc1 : m 1 + rateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σB - μ / 2 := by
      simpa [fixedConsts] using hcap 1
    have hc2 : m 2 + rateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σT - μ / 2 := by
      simpa [fixedConsts] using hcap 2
    have hm0 : m 0 ≤ σK := by linarith [hpw _ hrD.le]
    have hm1 : m 1 ≤ σB := by linarith [hpw _ hrB.le]
    have hm2 : m 2 ≤ σT := by linarith [hpw _ hrT.le]
    have hK : Admissible σK σB σT 𝔅 h ω r β ε x :=
      { hx' with
        deriv_le := fun θ hθ => (hx'.deriv_le θ hθ).trans hm0
        gram := fun θ hθ => ⟨(hx'.gram θ hθ).1, (hx'.gram θ hθ).2.trans hm1⟩
        twist := ⟨hx'.twist.1, hx'.twist.2.trans hm2⟩ }
    obtain ⟨⟨hhol, hprim, hreal⟩, ⟨hclose, hball⟩, herr, hεle, hdiff, hTu, hTd⟩ :=
      step_spec hC hS hγb hK hδ hδ1 h3' hst' hβ'
    have hsub : ∀ {a b : ℝ}, a ≤ b → complexStrip n a ⊆ complexStrip n b :=
      fun hab => Triangular.strip_mono hab
    have h32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
      hsub (by linarith)
    have h3r : complexStrip n (r - 3 * δ) ⊆ complexStrip n r := hsub (by linarith)
    have hd0 : 0 ≤ cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
      have : 0 < δ ^ (2 * κ) := Real.rpow_pos_of_pos hδ _
      positivity
    have hK' : Admissible (m 0 + rateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)))
        (m 1 + rateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)))
        (m 2 + rateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) 𝔅 h ω (r - 3 * δ)
        (β - cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)))
        (cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))))
        (newtonMap h x ω (r - 2 * δ)) :=
      { r_pos := by linarith
        β_pos := by linarith [hx'.β_pos]
        ε_nonneg := by
          have : 0 < δ ^ (2 * (2 * κ)) := Real.rpow_pos_of_pos hδ _
          have := hE.le
          positivity
        ε_le_one := hεle.trans hx'.ε_le_one
        holo := hhol.mono h32
        primary := fun θ hθ k => hprim θ (h32 hθ) k
        real := hreal
        ball_sub := fun θ hθ => hball θ (h32 hθ)
        deriv_le := fun θ hθ => by
          have h1 := norm_le_add_of_sub_le (hdiff θ hθ).1
          have h2 := hx'.deriv_le θ (h3r hθ)
          linarith
        gram := fun θ hθ => ⟨(hdiff θ hθ).2.1, by
          have h1 := norm_le_add_of_sub_le (hdiff θ hθ).2.2
          have h2 := (hx'.gram θ (h3r hθ)).2
          linarith⟩
        twist := ⟨hTu, by
          have h1 := norm_le_add_of_sub_le hTd
          have h2 := hx'.twist.2
          linarith⟩
        error_le := fun θ hθ => herr θ (h32 hθ) }
    have e0 : (fun i => m i + (fixedConsts n κ cR M σK σB σT γb μ).rate i * ε /
        (γ ^ 2 * δ ^ ((fixedConsts n κ cR M σK σB σT γb μ).a +
          ((fixedConsts n κ cR M σK σB σT γb μ).j i : ℝ)))) 0 =
        m 0 + rateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [fixedConsts]
    have e1 : (fun i => m i + (fixedConsts n κ cR M σK σB σT γb μ).rate i * ε /
        (γ ^ 2 * δ ^ ((fixedConsts n κ cR M σK σB σT γb μ).a +
          ((fixedConsts n κ cR M σK σB σT γb μ).j i : ℝ)))) 1 =
        m 1 + rateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [fixedConsts]
    have e2 : (fun i => m i + (fixedConsts n κ cR M σK σB σT γb μ).rate i * ε /
        (γ ^ 2 * δ ^ ((fixedConsts n κ cR M σK σB σT γb μ).a +
          ((fixedConsts n κ cR M σK σB σT γb μ).j i : ℝ)))) 2 =
        m 2 + rateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [fixedConsts]
    refine ⟨?_, fun θ hθ => ⟨hclose θ (h32 hθ), ?_⟩, ?_⟩
    · show Admissible _ _ _ 𝔅 h ω _ _ _ _
      rw [e0, e1, e2]
      exact hK'
    · have := (hdiff θ hθ).1
      have e : (rateD n cR M σK σB σT γb) * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) =
          n * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ := by
        rw [StepSharp.div_delta_eq hγ hδ]; unfold rateD; ring
      exact e ▸ this
    · simp [fixedScheme, fixedConsts]

/-- The ball and cap conditions from `𝔠_* e/(γ⁴ δ₀^{2a}) ≤ 1`: for `q ≥ 0` with `4γ̄² q ≤ 𝔠_sum`,
`q e/(γ² δ₀^{a+j}) ≤ μ/4` for `a = 2κ`, `j ∈ {0, 1}`. -/
theorem fixed_arith {D e : ℝ} (hκ : 1 ≤ κ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hD0 : 0 < D)
    (hD1 : D ≤ 1) (hμ : 0 < μ) (he : 0 ≤ e)
    (hsm : cStar n κ cR M σK σB σT γb μ * e / (γ ^ 4 * D ^ (2 * (2 * κ))) ≤ 1) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : 4 * γb ^ 2 * q ≤ cSum n cR M σK σB σT γb) :
    q * e / (γ ^ 2 * D ^ (2 * κ + 1)) ≤ μ / 4 ∧ q * e / (γ ^ 2 * D ^ (2 * κ)) ≤ μ / 4 := by
  obtain ⟨-, -, ⟨-, -, a1, a2⟩, -⟩ := absorb (κ := κ) (γb := γb) hκ hγ hγb hD0 hD1 he
  have hD : 0 < γ ^ 4 * D ^ (2 * (2 * κ)) := by positivity
  generalize hXd : e / (γ ^ 4 * D ^ (2 * (2 * κ))) = X at a1 a2
  have hX0 : 0 ≤ X := by rw [← hXd]; positivity
  have hCX : cStar n κ cR M σK σB σT γb μ * X ≤ 1 := by
    rw [← hXd]; rwa [mul_div_assoc] at hsm
  have hcs : cSum n cR M σK σB σT γb ≤ cStar n κ cR M σK σB σT γb μ * μ :=
    (div_le_iff₀ hμ).1 ((le_max_right _ _).trans (le_max_right _ _))
  have key : ∀ y : ℝ, y ≤ γb ^ 2 * X → q * e / (γ ^ 2 * D ^ (2 * κ + 1)) ≤ 0 ∨ True →
      q * y ≤ μ / 4 := by
    intro y hy _
    have h1 : q * y ≤ q * (γb ^ 2 * X) := mul_le_mul_of_nonneg_left hy hq0
    have h2 : (4 * γb ^ 2 * q) * X ≤ (cStar n κ cR M σK σB σT γb μ * μ) * X :=
      mul_le_mul_of_nonneg_right (hq.trans hcs) hX0
    have h3 : μ * (cStar n κ cR M σK σB σT γb μ * X) ≤ μ * 1 :=
      mul_le_mul_of_nonneg_left hCX hμ.le
    nlinarith
  constructor
  · rw [mul_div_assoc]; exact key _ a1 (Or.inr trivial)
  · rw [mul_div_assoc]; exact key _ a2 (Or.inr trivial)

/-- Step `step:p2s:g1-hyp`: the engine hypotheses from `𝔠_* e/(γ⁴ δ₀^{2a}) ≤ 1`. -/
theorem engine_hyps (hC : CohData n τ κ cR) (hP : Params n τ M σK σB σT) {ρ ρinf γ e : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hμ : 0 < μ) (he : 0 ≤ e)
    (hsm : cStar n κ cR M σK σB σT γb μ * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1) :
    (2 : ℝ) ^ (2 * (fixedConsts n κ cR M σK σB σT γb μ).a) *
        (fixedConsts n κ cR M σK σB σT γb μ).CE * e /
        (γ ^ 4 * Engine.delta0 (fixedConsts n κ cR M σK σB σT γb μ).lam ρ ρinf ^
          (2 * (fixedConsts n κ cR M σK σB σT γb μ).a)) ≤ 1 ∧
    (fixedConsts n κ cR M σK σB σT γb μ).cstep * e /
        (γ ^ 4 * Engine.delta0 (fixedConsts n κ cR M σK σB σT γb μ).lam ρ ρinf ^
          (2 * (fixedConsts n κ cR M σK σB σT γb μ).a)) ≤ 1 ∧
    2 * (fixedConsts n κ cR M σK σB σT γb μ).CD * e /
        (γ ^ 2 * Engine.delta0 (fixedConsts n κ cR M σK σB σT γb μ).lam ρ ρinf ^
          (fixedConsts n κ cR M σK σB σT γb μ).a) ≤ μ / 4 ∧
    ∀ i, ![σK - μ, σB - μ, σT - μ] i + 2 * (fixedConsts n κ cR M σK σB σT γb μ).rate i * e /
        (γ ^ 2 * Engine.delta0 (fixedConsts n κ cR M σK σB σT γb μ).lam ρ ρinf ^
          ((fixedConsts n κ cR M σK σB σT γb μ).a + (fixedConsts n κ cR M σK σB σT γb μ).j i)) ≤
      (fixedConsts n κ cR M σK σB σT γb μ).cap i := by
  have _ := hρinf
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD0 : 0 < delta0s ρ ρinf := Engine.delta0_pos hlam hρ
  have hD1 : delta0s ρ ρinf ≤ 1 := Engine.delta0_le_one _ _ _
  have hD : 0 < γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ)) := by positivity
  obtain ⟨hDK, hE, hrD, hrB, hrT⟩ := fixed_consts_pos hC hP hγb0
  have hn1 : 1 ≤ n := by have := hP.two_le; omega
  obtain ⟨-, -, -, -, -, hSum, -⟩ := consts_pos (n := n) (κ := κ) (μ := μ) hn1 hC.cR_pos hP.M_pos
    hP.σK_pos hP.σB_pos hP.σT_pos hγb0 hμ
  have hmax : ∀ x, x ≤ max (2 * cDK n cR M σK σB σT γb) (max (rateD n cR M σK σB σT γb)
      (max (rateB n cR M σK σB σT γb) (rateT n cR M σK σB σT γb))) →
      4 * γb ^ 2 * x ≤ cSum n cR M σK σB σT γb := fun x hx => by
    unfold cSum
    have := pow_pos hγb0 2
    nlinarith
  have hcs1 : (2 : ℝ) ^ (2 * (2 * κ)) * cE n cR M σK σB σT γb ≤ cStar n κ cR M σK σB σT γb μ :=
    le_max_left _ _
  have hcs2 : cStep n κ cR M σK σB σT γb ≤ cStar n κ cR M σK σB σT γb μ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX : 0 ≤ e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) := by positivity
  have hCX : cStar n κ cR M σK σB σT γb μ * (e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ)))) ≤ 1 := by
    rwa [← mul_div_assoc]
  have hmx : ∀ c : ℝ, c ≤ cStar n κ cR M σK σB σT γb μ →
      c * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1 := fun c hc => by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right hc hX).trans hCX
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hmx _ hcs1
  · exact hmx _ hcs2
  · have := (fixed_arith (n := n) (cR := cR) (M := M) (σK := σK) (σB := σB) (σT := σT)
      hC.one_le_kappa hγ hγb hD0 hD1 hμ he hsm (q := 2 * cDK n cR M σK σB σT γb)
      (by positivity) (hmax _ (le_max_left _ _))).2
    exact this
  · intro i
    have hj := fixedConsts_j (n := n) (κ := κ) (cR := cR) (M := M) (σK := σK) (σB := σB)
      (σT := σT) (γb := γb) (μ := μ) i
    have hq : ∀ q : ℝ, 0 ≤ q → q ≤ max (2 * cDK n cR M σK σB σT γb)
        (max (rateD n cR M σK σB σT γb) (max (rateB n cR M σK σB σT γb)
          (rateT n cR M σK σB σT γb))) → 2 * q * e /
        (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) ≤ μ / 2 := fun q hq0 hqm => by
      have := (fixed_arith (n := n) (cR := cR) (M := M) (σK := σK) (σB := σB) (σT := σT)
        hC.one_le_kappa hγ hγb hD0 hD1 hμ he hsm hq0 (hmax _ hqm)).1
      have e2 : 2 * q * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) =
          2 * (q * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1))) := by ring
      linarith
    show ![σK - μ, σB - μ, σT - μ] i + 2 * (fixedConsts n κ cR M σK σB σT γb μ).rate i * e /
        (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + ((fixedConsts n κ cR M σK σB σT γb μ).j i : ℝ))) ≤
      (fixedConsts n κ cR M σK σB σT γb μ).cap i
    rw [hj]
    fin_cases i
    · have h0 := hq _ hrD.le ((le_max_left _ _).trans (le_max_right _ _))
      show σK - μ + 2 * rateD n cR M σK σB σT γb * e /
        (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) ≤ σK - μ / 2
      linarith
    · have h0 := hq _ hrB.le (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
      show σB - μ + 2 * rateB n cR M σK σB σT γb * e /
        (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) ≤ σB - μ / 2
      linarith
    · have h0 := hq _ hrT.le
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      show σT - μ + 2 * rateT n cR M σK σB σT γb * e /
        (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) ≤ σT - μ / 2
      linarith

end KAM.Sharp

end
