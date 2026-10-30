/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Step
public import KAM.Iso.Sharp.ConstantsArith
public import KAM.Iso.Apost.Limit
public import KAM.Sharp.Scheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The isoenergetic scheme of the sharp theorem

Blueprint `bpI:p2s:scheme`. `isoScheme` is the abstract Newton scheme of `KAM.Sharp.Engine` whose
states are pairs `(K, s)` (torus and ray scalar), with parameter `p(K, s) = s |ω*|`, four bounds
`(m₁, m₂, m₃, m₄)` (the last one the used part of the ray margin `ν`), and step
`(K, s) ↦ (K̄, s̄)` of `bpI:p2:correction`, `bpI:p2:newton-error`.

* `isoScheme_isNewton`: (N1), (N2) from `KAM.Iso.Sharp.iso_step_spec`; the ray part of the new
  admissibility is `KAM.Iso.Apost.ray` (b) with the fourth cap (step `stepI:p2s:sc-s`).
* `iso_engine_hyps`: the arithmetic hypotheses (I1)–(I4) of the engine from
  `ĉ_* e/(γ⁴δ₀^{2a}) ≤ 1` (step `stepI:p2s:g1-eng`; the fourth rate uses the branch `4γ̄²C_Δω/ν`).
* `iso_energy_limit` (Lemma `bpI:p2:energy-limit` for the engine iterates): the energy averages of
  the iterates converge to `E₀` (they are within `ε_s` of it) and to the energy average of the limit
  (`KAM.Iso.Apost.tendsto_energyAverage_of_uniform`, the iterates staying within `μ/4` of `K`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb μ ν : ℝ}
variable {τ σω : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- The state of the isoenergetic scheme: a torus and the ray scalar `s`. -/
abbrev IsoState (n : ℕ) : Type := ((Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) × ℝ

/-- The isoenergetic scheme (`bpI:p2s:scheme`). -/
def isoScheme (n : ℕ) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (ωstar : Fin n → ℝ) (E₀ σω ν : ℝ) : Engine.Scheme n 4 (IsoState n) where
  tor := fun x => x.1
  par := fun x => x.2 * ‖ωstar‖
  Adm := fun r β ε m x => IsoAdmissible (m 0) (m 1) (m 2) D H ωstar E₀ r β ε x.2 x.1 ∧
    ν - m 3 ≤ rayMargin σω ωstar x.2
  step := fun r δ x => (isoNewtonMap H x.1 ωstar E₀ x.2 (r - 2 * δ), isoNewS H x.1 ωstar E₀ x.2)

/-- The constants of the isoenergetic scheme (caps `σ - μ/2` and `ν/2`). -/
def isoConsts (n : ℕ) (κ cR M σK σB σT γb μ ν : ℝ) : Engine.Consts 4 where
  lam := 3
  a := 2 * κ
  CE := iCE n cR M σK σB σT γb
  CD := iCDK n cR M σK σB σT γb
  Cp := iCDw n cR M σK σB σT γb
  cstep := iCStep n κ cR M σK σB σT γb
  cap := ![σK - μ / 2, σB - μ / 2, σT - μ / 2, ν / 2]
  rate := ![iRateD n cR M σK σB σT γb, iRateB n cR M σK σB σT γb, iRateT n cR M σK σB σT γb,
    iCDw n cR M σK σB σT γb]
  j := ![1, 1, 1, 0]

/-- The admissibility of the scheme, unfolded. -/
theorem isoScheme_adm_iff {E₀ r β ε : ℝ} {m : Fin 4 → ℝ} {x : IsoState n} :
    (isoScheme n H D ωstar E₀ σω ν).Adm r β ε m x ↔
      IsoAdmissible (m 0) (m 1) (m 2) D H ωstar E₀ r β ε x.2 x.1 ∧
        ν - m 3 ≤ rayMargin σω ωstar x.2 := Iff.rfl

/-- Positivity of the constants that the scheme needs. -/
theorem iso_scheme_consts_pos (hC : CohData n τ κ cR) (hP : Params n τ M σK σB σT)
    (hγb : 0 < γb) :
    0 < iCDK n cR M σK σB σT γb ∧ 0 < iCDw n cR M σK σB σT γb ∧ 0 < iCE n cR M σK σB σT γb ∧
      0 < iRateD n cR M σK σB σT γb ∧ 0 < iRateB n cR M σK σB σT γb ∧
      0 < iRateT n cR M σK σB σT γb := by
  have hn1 : 1 ≤ n := by have := hP.two_le; omega
  obtain ⟨h1, h2, h3, h4, -⟩ := iso_consts_pos (n := n) (κ := κ) (μ := 1) (ν := 1) hn1 hC.cR_pos
    hP.M_pos hP.σK_pos hP.σB_pos hP.σT_pos hγb one_pos one_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hσK := hP.σK_pos
  have hσB := hP.σB_pos
  have hσT := hP.σT_pos
  have hG : 0 < cGram n σK := by unfold cGram vth; positivity
  have hB : 0 < cB n σK σB := by unfold cB vthh; positivity
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · unfold iRateD; positivity
  · unfold iRateB; positivity
  · unfold iRateT vthh; positivity

/-- Blueprint `bpI:p2s:scheme`. -/
theorem isoScheme_isNewton (hC : CohData n τ κ cR)
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) (hγb : γ ≤ γb) (hμ : 0 ≤ μ) (E₀ : ℝ) :
    (isoScheme n H D ωstar E₀ σω ν).IsNewton (isoConsts n κ cR M σK σB σT γb μ ν) γ := by
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  obtain ⟨hDK, hDw, hE, hrD, hrB, hrT⟩ := iso_scheme_consts_pos hC hS.toParams hγb0
  have hrate : ∀ i, 0 ≤ (isoConsts n κ cR M σK σB σT γb μ ν).rate i := by
    intro i; fin_cases i
    · exact hrD.le
    · exact hrB.le
    · exact hrT.le
    · exact hDw.le
  refine
    { lam_pos := by show (0 : ℝ) < 3; norm_num
      two_le_a := by show (2 : ℝ) ≤ 2 * κ; linarith [hC.one_le_kappa]
      CE_nonneg := hE.le
      CD_nonneg := hDK.le
      Cp_nonneg := hDw.le
      rate_nonneg := hrate
      j_le_one := by intro i; fin_cases i <;> simp [isoConsts]
      adm := ?_
      step := ?_ }
  · intro r β ε m x hx
    obtain ⟨hx', -⟩ := isoScheme_adm_iff.1 hx
    exact ⟨hx'.ε_nonneg, hx'.holo, hx'.primary, hx'.real⟩
  · intro r β ε δ m x hx hδ hδ1 h3 hst hβ hcap
    obtain ⟨hx', hray⟩ := isoScheme_adm_iff.1 hx
    have h3' : 3 * δ < r := h3
    have hst' : iCStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1 := hst
    have hβ' : 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤ β := hβ
    have hε0 := hx'.ε_nonneg
    have hpw : ∀ q : ℝ, 0 ≤ q → 0 ≤ q * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := fun q hq => by
      have : 0 < δ ^ (2 * κ + 1) := Real.rpow_pos_of_pos hδ _
      positivity
    have hc0 : m 0 + iRateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σK - μ / 2 := by
      simpa [isoConsts] using hcap 0
    have hc1 : m 1 + iRateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σB - μ / 2 := by
      simpa [isoConsts] using hcap 1
    have hc2 : m 2 + iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ σT - μ / 2 := by
      simpa [isoConsts] using hcap 2
    have hc3 : m 3 + iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ≤ ν / 2 := by
      simpa [isoConsts] using hcap 3
    have hm0 : m 0 ≤ σK := by linarith [hpw _ hrD.le]
    have hm1 : m 1 ≤ σB := by linarith [hpw _ hrB.le]
    have hm2 : m 2 ≤ σT := by linarith [hpw _ hrT.le]
    have hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε x.2 x.1 :=
      { hx' with
        deriv_le := fun θ hθ => (hx'.deriv_le θ hθ).trans hm0
        gram := fun θ hθ => ⟨(hx'.gram θ hθ).1, (hx'.gram θ hθ).2.trans hm1⟩
        twist := ⟨hx'.twist.1, hx'.twist.2.trans hm2⟩ }
    obtain ⟨⟨hhol, hprim, hreal⟩, ⟨hclose, hball, hsd⟩, ⟨herr, hen, hεle⟩, hdiff, hTu, hTd⟩ :=
      iso_step_spec hC hS hγb hK hδ hδ1 h3' hst' hβ'
    -- step `sc-s`: the ray
    have hsd' : ‖isoNewS H x.1 ωstar E₀ x.2 • ωstar - x.2 • ωstar‖ ≤
        iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact hsd
    have hlt : iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < ν - m 3 := by
      linarith [hS.ν_pos]
    obtain ⟨hs1', -, hray'⟩ := (KAM.Iso.Apost.ray (σω := σω) hS.dio).2.2.2.2.2 x.2
      (isoNewS H x.1 ωstar E₀ x.2) (ν - m 3) _ hray hsd' hlt
    -- step `sc-n2`: the new admissibility
    have h32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
      Triangular.strip_mono (by linarith)
    have h3r : complexStrip n (r - 3 * δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
    have hd0 : 0 ≤ iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
      have : 0 < δ ^ (2 * κ) := Real.rpow_pos_of_pos hδ _
      positivity
    have hK' : IsoAdmissible
        (m 0 + iRateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)))
        (m 1 + iRateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)))
        (m 2 + iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) D H ωstar E₀ (r - 3 * δ)
        (β - iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)))
        (iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))))
        (isoNewS H x.1 ωstar E₀ x.2) (isoNewtonMap H x.1 ωstar E₀ x.2 (r - 2 * δ)) :=
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
        error_le := fun θ hθ => herr θ (h32 hθ)
        s_gt := hs1'
        twist := ⟨hTu, by
          have h1 := norm_le_add_of_sub_le hTd
          have h2 := hx'.twist.2
          linarith⟩
        energy_le := hen }
    have e0 : (fun i => m i + (isoConsts n κ cR M σK σB σT γb μ ν).rate i * ε /
        (γ ^ 2 * δ ^ ((isoConsts n κ cR M σK σB σT γb μ ν).a +
          ((isoConsts n κ cR M σK σB σT γb μ ν).j i : ℝ)))) 0 =
        m 0 + iRateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [isoConsts]
    have e1 : (fun i => m i + (isoConsts n κ cR M σK σB σT γb μ ν).rate i * ε /
        (γ ^ 2 * δ ^ ((isoConsts n κ cR M σK σB σT γb μ ν).a +
          ((isoConsts n κ cR M σK σB σT γb μ ν).j i : ℝ)))) 1 =
        m 1 + iRateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [isoConsts]
    have e2 : (fun i => m i + (isoConsts n κ cR M σK σB σT γb μ ν).rate i * ε /
        (γ ^ 2 * δ ^ ((isoConsts n κ cR M σK σB σT γb μ ν).a +
          ((isoConsts n κ cR M σK σB σT γb μ ν).j i : ℝ)))) 2 =
        m 2 + iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      simp [isoConsts]
    have e3 : (fun i => m i + (isoConsts n κ cR M σK σB σT γb μ ν).rate i * ε /
        (γ ^ 2 * δ ^ ((isoConsts n κ cR M σK σB σT γb μ ν).a +
          ((isoConsts n κ cR M σK σB σT γb μ ν).j i : ℝ)))) 3 =
        m 3 + iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
      simp [isoConsts]
    refine ⟨?_, fun θ hθ => ⟨hclose θ (h32 hθ), ?_⟩, ?_⟩
    · show IsoAdmissible _ _ _ D H ωstar E₀ _ _ _ (isoNewS H x.1 ωstar E₀ x.2)
          (isoNewtonMap H x.1 ωstar E₀ x.2 (r - 2 * δ)) ∧
        ν - _ ≤ rayMargin σω ωstar (isoNewS H x.1 ωstar E₀ x.2)
      rw [e0, e1, e2, e3]
      exact ⟨hK', by linarith⟩
    · have := (hdiff θ hθ).1
      have e : iRateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) =
          n * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ := by
        rw [StepSharp.div_delta_eq hγ hδ]; unfold iRateD; ring
      exact e ▸ this
    · show |isoNewS H x.1 ωstar E₀ x.2 * ‖ωstar‖ - x.2 * ‖ωstar‖| ≤
        iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))
      rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact hsd

/-- The budget of the engine hypotheses: if `c X ≤ 1` and `4γ̄² q ≤ c B`, then `q y ≤ B/4` for
every `y ≤ γ̄² X`. -/
theorem iso_budget {X y q c B : ℝ} (hX0 : 0 ≤ X) (hcX : c * X ≤ 1) (hB : 0 ≤ B) (hq0 : 0 ≤ q)
    (hy : y ≤ γb ^ 2 * X) (h4 : 4 * γb ^ 2 * q ≤ c * B) : q * y ≤ B / 4 :=
  calc q * y ≤ q * (γb ^ 2 * X) := mul_le_mul_of_nonneg_left hy hq0
    _ = 4 * γb ^ 2 * q * X / 4 := by ring
    _ ≤ c * B * X / 4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hX0)
        (by norm_num)
    _ = B * (c * X) / 4 := by ring
    _ ≤ B * 1 / 4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcX hB) (by norm_num)
    _ = B / 4 := by ring

/-- Step `stepI:p2s:g1-eng`: the engine hypotheses (I1)–(I4) from `ĉ_* e/(γ⁴ δ₀^{2a}) ≤ 1`. -/
theorem iso_engine_hyps (hC : CohData n τ κ cR) (hP : Params n τ M σK σB σT) {ρ ρinf γ e : ℝ}
    (hρ : ρinf < ρ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hμ : 0 < μ) (hν : 0 < ν) (he : 0 ≤ e)
    (hsm : iCStar n κ cR M σK σB σT γb μ ν * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1) :
    (2 : ℝ) ^ (2 * (isoConsts n κ cR M σK σB σT γb μ ν).a) *
        (isoConsts n κ cR M σK σB σT γb μ ν).CE * e /
        (γ ^ 4 * Engine.delta0 (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf ^
          (2 * (isoConsts n κ cR M σK σB σT γb μ ν).a)) ≤ 1 ∧
    (isoConsts n κ cR M σK σB σT γb μ ν).cstep * e /
        (γ ^ 4 * Engine.delta0 (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf ^
          (2 * (isoConsts n κ cR M σK σB σT γb μ ν).a)) ≤ 1 ∧
    2 * (isoConsts n κ cR M σK σB σT γb μ ν).CD * e /
        (γ ^ 2 * Engine.delta0 (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf ^
          (isoConsts n κ cR M σK σB σT γb μ ν).a) ≤ μ / 4 ∧
    ∀ i, ![σK - μ, σB - μ, σT - μ, 0] i + 2 * (isoConsts n κ cR M σK σB σT γb μ ν).rate i * e /
        (γ ^ 2 * Engine.delta0 (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf ^
          ((isoConsts n κ cR M σK σB σT γb μ ν).a + (isoConsts n κ cR M σK σB σT γb μ ν).j i)) ≤
      (isoConsts n κ cR M σK σB σT γb μ ν).cap i := by
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hD0 : 0 < delta0s ρ ρinf := Engine.delta0_pos (by norm_num : (0 : ℝ) < 3) hρ
  have hD1 : delta0s ρ ρinf ≤ 1 := Engine.delta0_le_one _ _ _
  have hn1 : 1 ≤ n := by have := hP.two_le; omega
  obtain ⟨hDK, hDw, -, -, -, -, -⟩ := iso_consts_pos (n := n) (κ := κ) hn1 hC.cR_pos hP.M_pos
    hP.σK_pos hP.σB_pos hP.σT_pos hγb0 hμ hν
  obtain ⟨-, -, -, hrD, hrB, hrT⟩ := iso_scheme_consts_pos (κ := κ) hC hP hγb0
  obtain ⟨-, -, ⟨-, -, a1, a2⟩, -⟩ := absorb (κ := κ) (γb := γb) hC.one_le_kappa hγ hγb hD0 hD1 he
  have hX0 : 0 ≤ e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) := by positivity
  have hCX : iCStar n κ cR M σK σB σT γb μ ν * (e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ)))) ≤
      1 := by rwa [← mul_div_assoc]
  have hmx : ∀ c : ℝ, c ≤ iCStar n κ cR M σK σB σT γb μ ν →
      c * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1 := fun c hc => by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right hc hX0).trans hCX
  -- the four branches of `ĉ_*`
  have hb1 : (2 : ℝ) ^ (2 * (2 * κ)) * iCE n cR M σK σB σT γb ≤ iCStar n κ cR M σK σB σT γb μ ν :=
    le_max_left _ _
  have hb2 : iCStep n κ cR M σK σB σT γb ≤ iCStar n κ cR M σK σB σT γb μ ν :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hb3 : iCSum n cR M σK σB σT γb ≤ iCStar n κ cR M σK σB σT γb μ ν * μ :=
    (div_le_iff₀ hμ).1 ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb4 : 4 * γb ^ 2 * iCDw n cR M σK σB σT γb ≤ iCStar n κ cR M σK σB σT γb μ ν * ν :=
    (div_le_iff₀ hν).1 ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hsum : ∀ q, q ≤ max (2 * iCDK n cR M σK σB σT γb) (max (iRateD n cR M σK σB σT γb)
      (max (iRateB n cR M σK σB σT γb) (iRateT n cR M σK σB σT γb))) →
      4 * γb ^ 2 * q ≤ iCStar n κ cR M σK σB σT γb μ ν * μ := fun q hq =>
    (mul_le_mul_of_nonneg_left hq (by positivity)).trans hb3
  -- the rates `ϱ_D, ϱ_B, ϱ_𝖳` (exponent `a + 1`)
  have hrate : ∀ q, 0 ≤ q → q ≤ max (2 * iCDK n cR M σK σB σT γb) (max (iRateD n cR M σK σB σT γb)
      (max (iRateB n cR M σK σB σT γb) (iRateT n cR M σK σB σT γb))) →
      2 * q * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) ≤ μ / 2 := fun q hq0 hq => by
    have := iso_budget hX0 hCX hμ.le hq0 a1 (hsum q hq)
    have e2 : 2 * q * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)) =
        2 * (q * (e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + 1)))) := by ring
    linarith
  refine ⟨hmx _ hb1, hmx _ hb2, ?_, ?_⟩
  · -- (I3): the ball budget
    show 2 * iCDK n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) ≤ μ / 4
    have := iso_budget hX0 hCX hμ.le (by positivity) a2 (hsum _ (le_max_left _ _))
    have e2 : 2 * iCDK n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) =
        2 * iCDK n cR M σK σB σT γb * (e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ))) := by ring
    linarith
  · -- (I4): the four caps
    intro i
    fin_cases i
    · show σK - μ + 2 * iRateD n cR M σK σB σT γb * e /
          (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + ((1 : ℕ) : ℝ))) ≤ σK - μ / 2
      rw [Nat.cast_one]
      linarith [hrate _ hrD.le ((le_max_left _ _).trans (le_max_right _ _))]
    · show σB - μ + 2 * iRateB n cR M σK σB σT γb * e /
          (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + ((1 : ℕ) : ℝ))) ≤ σB - μ / 2
      rw [Nat.cast_one]
      linarith [hrate _ hrB.le
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))]
    · show σT - μ + 2 * iRateT n cR M σK σB σT γb * e /
          (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + ((1 : ℕ) : ℝ))) ≤ σT - μ / 2
      rw [Nat.cast_one]
      linarith [hrate _ hrT.le
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))]
    · show 0 + 2 * iCDw n cR M σK σB σT γb * e /
          (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ + ((0 : ℕ) : ℝ))) ≤ ν / 2
      rw [Nat.cast_zero, add_zero, zero_add]
      have := iso_budget hX0 hCX hν.le hDw.le a2 hb4
      have e2 : 2 * iCDw n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) =
          2 * (iCDw n cR M σK σB σT γb * (e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)))) := by ring
      linarith

/-- The iterates stay within `D_s = ∑_{t<s} d_t` of the initial torus on `T_{ρ∞}`. -/
theorem iso_iter_close {E₀ ρ ρinf e : ℝ} {x₀ : IsoState n}
    (hit : ∀ s : ℕ, ∀ θ ∈ complexStrip n ρinf,
      ‖((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ (s + 1)).1 θ -
          ((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1 θ‖ ≤
        (isoConsts n κ cR M σK σB σT γb μ ν).d ρ ρinf γ e s) (s : ℕ) :
    ∀ θ ∈ complexStrip n ρinf,
      ‖((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1 θ - x₀.1 θ‖ ≤
        (isoConsts n κ cR M σK σB σT γb μ ν).sumD ρ ρinf γ e s := by
  induction s with
  | zero =>
    intro θ _
    simp [Engine.Consts.sumD, Engine.Scheme.iter]
  | succ s ih =>
    intro θ hθ
    rw [show (isoConsts n κ cR M σK σB σT γb μ ν).sumD ρ ρinf γ e (s + 1) =
      (isoConsts n κ cR M σK σB σT γb μ ν).sumD ρ ρinf γ e s +
        (isoConsts n κ cR M σK σB σT γb μ ν).d ρ ρinf γ e s from Finset.sum_range_succ _ _]
    calc _ ≤ ‖((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ (s + 1)).1 θ -
            ((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1 θ‖ +
          ‖((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1 θ - x₀.1 θ‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith [hit s θ hθ, ih θ hθ]

/-- Lemma `bpI:p2:energy-limit` for the engine iterates. -/
theorem iso_energy_limit (hC : CohData n τ κ cR)
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) (hγb : γ ≤ γb) {E₀ ρ ρinf e : ℝ}
    {x₀ : IsoState n} {m₀ : Fin 4 → ℝ} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    (h0 : (isoScheme n H D ωstar E₀ σω ν).Adm ρ μ e m₀ x₀)
    (hM0 : ∀ i, m₀ i ≤ ![σK - μ, σB - μ, σT - μ, 0] i)
    (hsm : iCStar n κ cR M σK σB σT γb μ ν * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1) :
    KAM.Iso.energyAverage H ((isoScheme n H D ωstar E₀ σω ν).limTor 3 ρ ρinf x₀) = (E₀ : ℂ) := by
  have hγ := hS.gamma_pos
  have hP := hS.toParams
  have hN := isoScheme_isNewton (κ := κ) (cR := cR) (μ := μ) hC hS hγb hμ.le E₀
  have he : 0 ≤ e := (hN.adm h0).1
  obtain ⟨hEh, hst, hbl, hcap0⟩ := iso_engine_hyps (κ := κ) hC hP (ρinf := ρinf) hρ hγ hγb hμ
    hS.ν_pos he hsm
  have hcap : ∀ i, m₀ i + 2 * (isoConsts n κ cR M σK σB σT γb μ ν).rate i * e /
      (γ ^ 2 * Engine.delta0 (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf ^
        ((isoConsts n κ cR M σK σB σT γb μ ν).a + (isoConsts n κ cR M σK σB σT γb μ ν).j i)) ≤
      (isoConsts n κ cR M σK σB σT γb μ ν).cap i := fun i =>
    (add_le_add (hM0 i) le_rfl).trans (hcap0 i)
  have hit := Engine.Scheme.iterate hN hρinf hρ hγ h0 hEh hst hbl hcap
  obtain ⟨hconv, -, hholoL, -, -, hclose, -, -, hεz⟩ :=
    Engine.Scheme.limit hN hρinf hρ hγ h0 hEh hst hbl hcap
  have hsch := Engine.schedule (lam := (isoConsts n κ cR M σK σB σT γb μ ν).lam) hN.lam_pos
    hρinf hρ
  have hsub : ∀ s, complexStrip n ρinf ⊆
      complexStrip n (Engine.rSeq (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf s) :=
    fun s => Triangular.strip_mono (hsch.2.2.2.2.1 s).le
  have hsubρ : complexStrip n ρinf ⊆ complexStrip n ρ := Triangular.strip_mono hρ.le
  obtain ⟨h0', -⟩ := isoScheme_adm_iff.1 h0
  have hAdm := fun s => (isoScheme_adm_iff.1 (hit s).1).1
  have hKs := iso_iter_close (fun s θ hθ =>
    ((hit s).2.2.2.1 θ (hsub (s + 1) hθ)).1)
  have hT := tendsto_energyAverage_of_uniform hρinf hP.M_pos.le hS.isOpen hS.holo
    (fun z hz => (hS.bounds z hz).1) hμ (K := x₀.1)
    (Ks := fun s => ((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1)
    (fun θ hθ => h0'.ball_sub θ (hsubρ hθ))
    (fun s θ hθ => (hKs s θ hθ).trans ((hit s).2.1.trans hbl))
    (fun θ hθ => (hclose θ hθ).trans hbl) (fun s => (hAdm s).holo.mono (hsub s)) hholoL hconv
  have hE0 : Tendsto (fun s => KAM.Iso.energyAverage H
      ((isoScheme n H D ωstar E₀ σω ν).iter 3 ρ ρinf x₀ s).1) atTop (𝓝 (E₀ : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun s => (hAdm s).energy_le) hεz
  exact tendsto_nhds_unique hT hE0

end KAM.Iso.Sharp

end
