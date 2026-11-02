/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellInv
public import KAM.Wave.Iteration.Tori
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: the shell tori in Birkhoff coordinates (blueprint `bpW:w8:shell-data`, `bpW:w8:shell-iter`,
`bpW:w8:w6-general`, `bpW:w8:torus-shape`)

Blueprint labels `bpW:w8:shell-data` (iii), (iv), `bpW:w8:shell-iter`,
`bpW:w8:w6-general` (tori), `bpW:w8:torus-shape` (milestone W8).

* `w8HW hm n`: the hypotheses of Lemma `bpW:w6:prep-step` for shell `n` and the initial
  perturbation `P = w6InP` of Proposition `bpW:w5:initial` (W5's `H_in = N_ξ + P_ξ`), from
  `bpW:w8:shell-data` (iii), (iv) and W6-TORI's `w6PrepHyp_initial`;
* `w8tori` (local macro): Theorem `bpW:w6:tori` (i)–(v) for the shell iteration (Lemma
  `bpW:w8:w6-general`, Step `stepW:w8:g-tori`), with `e_tor = e^{(n)}_tor`;
* `w8Psi hm n ξ θ = Ψ̃^{(n)}_ξ(θ) = 𝒜_ξ(Φ^{(n)}_P(Φ^{(n)}_*(θ)))` for real `θ`;
* the angle and action errors on real `θ`: the phase `w8Phase` (`θ + X(θ)`), the angle error
  `w8Xang` (`X`), the action error `w8Yact` (`y`);
* Lemma `bpW:w8:torus-shape`: `w8_torusShape_bounds` ((i)), `w8_torusShape_real` and
  `w8_torusShape_coord` ((ii)), `w8Xang_periodic` and `w8Psi_periodic` ((iii)),
  `w8_torusShape_deriv` and `w8Xang_lipschitz` ((iv)), `w8Psi_ball` ((v)).
-/

@[expose] public noncomputable section

open Set Real Complex Metric

namespace KAM.Wave

open KAM

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- (`bpW:w8:shell-data` (iii), Step `stepW:w8:sd-init`) On `Π_n`: `ξ_i ≥ 2r_n²` and
`|ξ| ≤ t_n` (the hypotheses of `bpW:w5:action-angle` (ii) used by `bpW:w6:tori`). -/
theorem w8_shellPi_bounds (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8Pi 𝔱 n) :
    (∀ i, 2 * w8rn 𝔱 n ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ w8tn 𝔱 n := by
  obtain ⟨-, -, -, hPar, -, -⟩ := w8_shellData_init hm n
  have hα := w8alpha_pos (w8T0_pos hm (w8Upstream m hm)) n
  obtain ⟨h1, h2⟩ := hPar (aaOfReal ξ) ⟨ξ, hξ, by
    rw [show aaOfReal ξ - (fun i => (ξ i : ℂ)) = 0 from sub_self _, norm_zero]
    unfold w8rhoXi; positivity⟩
  refine ⟨fun i => by simpa using h1 i, ?_⟩
  have e := norm_aaOfReal_sub ξ 0
  have e2 : aaOfReal ξ - aaOfReal 0 = aaOfReal ξ := by ext i; simp
  rw [e2, sub_zero] at e
  rw [← e]
  exact h2

/-- `c_A(t_n + r_n²) < ρ₁²` (`bpW:w8:shell-data` (iv), Remark `bpW:w6:to-w8`). -/
theorem w8_shellRho1 (n : ℕ) : aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) < birkRho1 m 1 ^ 2 :=
  (w8_shellData_prep hm n).2.2.2.2.2.2.2

/-- **The shell prep-step bundle of the source** (blueprint `bpW:w8:shell-data` (iii), (iv)): the
hypotheses of Lemma `bpW:w6:prep-step` for shell `n` (`Π_n`, `α_n`, `r_n`, `ε^♯_n`) hold for the
initial perturbation `P = w6InP` of Proposition `bpW:w5:initial`. -/
theorem w8HW (n : ℕ) : W8ShellPrep m hm n (w6InP m hm) (w6InX m hm) := by
  obtain ⟨-, ht, hρξ, hPar, hρ₁, hin⟩ := w8_shellData_init hm n
  obtain ⟨hmeas, hsub, hα, hα0, hr, hε, hεγ, -⟩ := w8_shellData_prep hm n
  exact w6PrepHyp_initial hmeas hsub hα hα0 hr ht hρξ hPar hρ₁ hε hεγ hin

/-- The torus of shell `n` in KAM coordinates, `Φ^{(n)}_P ∘ Φ^{(n)}_*`, for the source. -/
abbrev w8TK (n : ℕ) (z : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) : KamPhase :=
  w8ShellTorusKam (w8HW hm n) z ξ

/-- `Ψ̃^{(n)}_ξ(θ) = 𝒜_ξ(Φ^{(n)}_P(Φ^{(n)}_*(θ)))` at real `θ` (blueprint `bpW:w8:shell-iter`). -/
def w8Psi (n : ℕ) (ξ θ : Fin 2 → ℝ) : BirkSpace :=
  (w8HW hm n).w6TorusBk (w8Eps0W m hm n) (aaOfReal θ) ξ

/-- The data of Theorem `bpW:w6:tori` for shell `n`: `ε_{0,n} ∈ [ε^♭_{0,n}, γ₁ α̌_n]`, `t_n > 0`,
the action-angle hypotheses on `Π_n` and `c_A(t_n + r_n²) < ρ₁²`. -/
theorem w8_toriData (n : ℕ) :
    w6EpsFlat (w8alpha 𝔱 n) (w8epsSharp m hm 𝔱 n) ≤ w8Eps0W m hm n ∧
      w8Eps0W m hm n ≤ w6Gamma1 m hm * alphaCheck (w8alpha 𝔱 n) ∧ 0 < w8tn 𝔱 n ∧
      (∀ ξ ∈ w8Pi 𝔱 n, (∀ i, 2 * w8rn 𝔱 n ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ w8tn 𝔱 n) ∧
      aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) < birkRho1 m 1 ^ 2 :=
  ⟨(w8_epsFlat_shell hm n).2.1, (w8_epsFlat_shell hm n).2.2,
    w8tn_pos (w8T0_pos hm (w8Upstream m hm)) n, fun _ hξ => w8_shellPi_bounds hm n hξ,
    w8_shellRho1 hm n⟩

/-- Theorem `bpW:w6:tori` (i)–(v) for the shell iteration (blueprint `bpW:w8:w6-general`, Step
`stepW:w8:g-tori`), with `e_tor = e^{(n)}_tor`: W6's `w6Tori` at the data `w8_toriData`. -/
local macro "w8tori" hm:term:max n:term:max : term =>
  `((w8HW $hm $n).w6Tori (w8_toriData $hm $n).1 (w8_toriData $hm $n).2.1
    (w8_toriData $hm $n).2.2.1 (w8_toriData $hm $n).2.2.2.1 (w8_toriData $hm $n).2.2.2.2)

/-- The phase `θ + X(θ)` of a shell torus at real `θ` (real part). -/
def w8Phase (n : ℕ) (ξ θ : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => ((w8TK hm n (aaOfReal θ) ξ).1 i).re

/-- The action error `y(θ)` of a shell torus at real `θ` (real part). -/
def w8Yact (n : ℕ) (ξ θ : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => ((w8TK hm n (aaOfReal θ) ξ).2.1 i).re

/-- The angle error `X(θ)` of a shell torus at real `θ`. -/
def w8Xang (n : ℕ) (ξ θ : Fin 2 → ℝ) : Fin 2 → ℝ := w8Phase hm n ξ θ - θ

/-- The angle error `X(z) = Φ_P Φ_*(z)_θ - z` on the complex strip. -/
def w8XC (n : ℕ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) : Fin 2 → ℂ := (w8TK hm n z ξ).1 - z

theorem w8_strip_half_sub (n : ℕ) :
    complexStrip 2 (w6S0 / 2) ⊆ complexStrip 2 (w8ShellSeqData m hm n).sInfty :=
  w6_strip_half_subset _ rfl

theorem w8TK_differentiableOn (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) :
    DifferentiableOn ℂ (fun z => w8TK hm n z ξ) (complexStrip 2 (w6S0 / 2)) :=
  (((w8ShellToriKam (w8HW hm n)).1 ξ hξ).1).mono (w8_strip_half_sub hm n)

/-- (`bpW:w6:tori` (iv)) The representation `Φ_P Φ_*(z) = ιz + ιV` with the bounds of `V`. -/
theorem w8TK_close (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) {z : Fin 2 → ℂ}
    (hz : z ∈ complexStrip 2 (w6S0 / 2)) :
    ‖w8XC hm n ξ z‖ ≤ w8ShellEtor m hm n ∧
      ‖(w8TK hm n z ξ).2.1‖ ≤ w8rn 𝔱 n ^ 2 * w8ShellEtor m hm n := by
  obtain ⟨V, hV, h1, h2, -, -, -⟩ := (w8tori hm n).2.2.2.2.1 ξ hξ z hz
  have e1 : w8XC hm n ξ z = V.1 := by
    unfold w8XC
    change ((w8HW hm n).w6TorusKam (w8Eps0W m hm n) z ξ).1 - z = V.1
    rw [hV]
    simp [w6TorusPt, w6Iota, kamHomEmbed_apply]
  have e2 : (w8TK hm n z ξ).2.1 = V.2.1 := by
    change ((w8HW hm n).w6TorusKam (w8Eps0W m hm n) z ξ).2.1 = V.2.1
    rw [hV]
    simp [w6TorusPt, w6Iota, kamHomEmbed_apply]
  exact ⟨e1 ▸ h1, e2 ▸ h2⟩

/-- Reality at real `θ` (`bpW:w6:tori` (i)): `Φ_P Φ_*(θ)` is a real point. -/
theorem w8TK_real (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    (w8TK hm n (aaOfReal θ) ξ).1 = aaOfReal (w8Phase hm n ξ θ) ∧
      (w8TK hm n (aaOfReal θ) ξ).2.1 = aaOfReal (w8Yact hm n ξ θ) := by
  obtain ⟨h1, h2, -, -⟩ := ((w8ShellToriKam (w8HW hm n)).1 ξ hξ).2.2 θ
  refine ⟨funext fun i => Complex.ext (by simp [w8Phase]) (by simpa [w8Phase] using h1 i),
    funext fun i => Complex.ext (by simp [w8Yact]) (by simpa [w8Yact] using h2 i)⟩

theorem w8XC_real (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) : w8XC hm n ξ (aaOfReal θ) = aaOfReal (w8Xang hm n ξ θ) := by
  unfold w8XC
  rw [(w8TK_real hm n hξ θ).1]
  ext i
  simp [w8Xang, aaOfReal]

/-- **Torus shape (i)** (blueprint `bpW:w8:torus-shape` (i), at real `θ`): `|X| ≤ e`,
`|y| ≤ r_n² e`, `‖Ψ̂‖ ≤ r_n e`, `e = e^{(n)}_tor`. -/
theorem w8_torusShape_bounds (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    ‖w8Xang hm n ξ θ‖ ≤ w8ShellEtor m hm n ∧
      ‖w8Yact hm n ξ θ‖ ≤ w8rn 𝔱 n ^ 2 * w8ShellEtor m hm n ∧
      ‖birkNormalPart (w8Psi hm n ξ θ)‖ ≤ w8rn 𝔱 n * w8ShellEtor m hm n := by
  have hz := w6_real_mem_strip_half θ
  obtain ⟨h1, h2⟩ := w8TK_close hm n hξ hz
  obtain ⟨-, -, -, -, -, -, h3⟩ := (w8tori hm n).2.2.2.2.1 ξ hξ _ hz
  have e0 : ∀ v : Fin 2 → ℝ, ‖aaOfReal v‖ = ‖v‖ := fun v => by
    have e := norm_aaOfReal_sub v 0
    have e2 : aaOfReal v - aaOfReal 0 = aaOfReal v := by ext i; simp
    rwa [e2, sub_zero] at e
  rw [w8XC_real hm n hξ, e0] at h1
  rw [(w8TK_real hm n hξ θ).2, e0] at h2
  exact ⟨h1, h2, h3⟩

/-- The shell constants: `e^{(n)}_tor ≥ 0`, `e^{(n)}_tor ≤ 7/256`, `r_n² ≤ α_n/4`, `r_n ≤ 1`,
`α_n ≤ t_n ≤ 1`, `t_n > 0`. -/
theorem w8_shell_consts (n : ℕ) :
    0 ≤ w8ShellEtor m hm n ∧ w8ShellEtor m hm n ≤ 7 / 256 ∧
      w8rn 𝔱 n ^ 2 ≤ w8alpha 𝔱 n / 4 ∧ w8rn 𝔱 n ≤ 1 ∧ w8alpha 𝔱 n ≤ w8tn 𝔱 n ∧
      w8tn 𝔱 n ≤ 1 ∧ 0 < w8tn 𝔱 n ∧ 0 < w8alpha 𝔱 n ∧ 0 < w8rn 𝔱 n := by
  set u := w8Upstream m hm
  have hT := w8T0_pos hm u
  obtain ⟨⟨h1, -, -⟩, ⟨-, hαt⟩, hr1, hr2, -, -, -, -⟩ := w8_shellData_sizes hm u n
  obtain ⟨he1, he2, he3, -, -⟩ := w8_etor hm n
  have ht1 : w8tn 𝔱 n ≤ 1 := (w8tn_facts hm u n).2.2.2.1
  have he0 : 0 ≤ w8ShellEtor m hm n := by
    rw [w8ShellEtor_eq]
    have hc : 0 < alphaCheck (w8alpha 𝔱 n) := Real.rpow_pos_of_pos (w8alpha_pos hT n) _
    have := (w8_shellData_prep hm n).2.2.2.2.2.1
    have := (w8_epsFlat_shell hm n)
    have : 0 < w8Eps0W m hm n := this.1.trans_le this.2.1
    have : 0 < w8alphaHat 𝔱 n := Real.rpow_pos_of_pos (w8alpha_pos hT n) _
    have := w6CFn_pos
    have := w6CF_pos
    have := w6SigmaP_pos
    have := w6Sigma0_pos
    positivity
  exact ⟨he0, he1.trans (he2 ▸ he3), hr2, hr1, hαt, ht1, h1, w8alpha_pos hT n,
    Real.rpow_pos_of_pos h1 _⟩

/-- **Torus shape (ii), reality and positivity** (blueprint `bpW:w8:torus-shape` (ii)): for real
`θ`, `ξ_i + y_i(θ) ≥ (3/4) α_n > 0`. -/
theorem w8_torusShape_real (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (i : Fin 2) : 3 / 4 * w8alpha 𝔱 n ≤ ξ i + w8Yact hm n ξ θ i := by
  obtain ⟨he0, he1, hr2, -, -, -, -, hα, -⟩ := w8_shell_consts hm n
  have hξP : ξ ∈ w8Pi 𝔱 n := w8ShellGamma_subset_Pi (w8HW hm n) hξ
  have hc := (w8Pi_coord hξP i).1
  have hy := (w8_torusShape_bounds hm n hξ θ).2.1
  have hyi : |w8Yact hm n ξ θ i| ≤ w8rn 𝔱 n ^ 2 * w8ShellEtor m hm n :=
    (norm_le_pi_norm (w8Yact hm n ξ θ) i).trans hy
  have : w8rn 𝔱 n ^ 2 * w8ShellEtor m hm n ≤ w8alpha 𝔱 n / 4 := by
    have hrr := sq_nonneg (w8rn 𝔱 n)
    nlinarith
  linarith [(abs_le.1 hyi).1]

/-- **Torus shape (ii), coordinates** (blueprint `bpW:w8:torus-shape` (ii)): for real `θ`,
`Ψ̃_{±i}(θ) = √(ξ_i + y_i(θ)) e^{∓2πi(θ_i + X_i(θ))}` with the positive square root. -/
theorem w8_torusShape_coord (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (b : Bool) (i : Fin 2) :
    birkCoord 1 1 (w8Psi hm n ξ θ) (b, modeIdx i) =
      ((Real.sqrt (ξ i + w8Yact hm n ξ θ i) : ℝ) : ℂ) *
        cexp (-(birkSgn (b, modeIdx i)) * (2 * π * I * ((w8Phase hm n ξ θ i : ℝ) : ℂ))) := by
  have hpos := w8_torusShape_real hm n hξ θ i
  have hα := (w8_shell_consts hm n).2.2.2.2.2.2.2.1
  unfold w8Psi W6PrepHyp.w6TorusBk
  rw [birkCoord_aaMap_tan]
  unfold aaTanCoord
  have e := w8TK_real hm n hξ θ
  change aaSqrt ((ξ i : ℂ) + (w8TK hm n (aaOfReal θ) ξ).2.1 i) *
    cexp (-(birkSgn (b, modeIdx i)) * (2 * π * I * (w8TK hm n (aaOfReal θ) ξ).1 i)) = _
  rw [e.1, e.2]
  simp only [aaOfReal]
  rw [← Complex.ofReal_add, aaSqrt_ofReal (by linarith)]

/-- **Torus shape (iii)** (blueprint `bpW:w8:torus-shape` (iii)): `X(θ + k) = X(θ)` for real `θ`,
`k ∈ ℤ²`; also `Φ_P Φ_*(z + k)_θ = Φ_P Φ_*(z)_θ + k` on the strip. -/
theorem w8XC_periodic (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) :
    ∀ i : Fin 2, ∀ k : ℤ, ∀ z ∈ complexStrip 2 (w6S0 / 2),
      z + k • _root_.Pi.single i (1 : ℂ) ∈ complexStrip 2 (w6S0 / 2) ∧
        w8XC hm n ξ (z + k • _root_.Pi.single i (1 : ℂ)) = w8XC hm n ξ z := fun i =>
  w6_periodic_zsmul (f := w8XC hm n ξ) (fun z hz => w6_strip_sub_single hz i) fun z hz => by
    have h := ((w8ShellToriKam (w8HW hm n)).1 ξ hξ).2.1 z (w8_strip_half_sub hm n hz) i
    unfold w8XC
    change (w8ShellTorusKam (w8HW hm n) (z + _root_.Pi.single i 1) ξ).1 -
      (z + _root_.Pi.single i 1) = (w8ShellTorusKam (w8HW hm n) z ξ).1 - z
    rw [h]
    simp [stepTau]

theorem w8_aaOfReal_add_int (θ : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    aaOfReal (θ + fun i => (k i : ℝ)) =
      aaOfReal θ + k 0 • _root_.Pi.single 0 (1 : ℂ) + k 1 • _root_.Pi.single 1 (1 : ℂ) := by
  ext i; fin_cases i <;> simp [aaOfReal]

theorem w8Xang_periodic (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    w8Xang hm n ξ (θ + fun i => (k i : ℝ)) = w8Xang hm n ξ θ := by
  have hz := w6_real_mem_strip_half θ
  obtain ⟨m0, e0⟩ := w8XC_periodic hm n hξ 0 (k 0) _ hz
  have e1 := (w8XC_periodic hm n hξ 1 (k 1) _ m0).2
  have h : w8XC hm n ξ (aaOfReal (θ + fun i => (k i : ℝ))) = w8XC hm n ξ (aaOfReal θ) := by
    rw [w8_aaOfReal_add_int, e1, e0]
  rw [w8XC_real hm n hξ, w8XC_real hm n hξ] at h
  funext i
  have := congrFun h i
  simpa [aaOfReal] using this

/-- `Ψ̃^{(n)}_ξ` is `ℤ²`-periodic on `ℝ²` (`bpW:w6:tori` (i)). -/
theorem w8Psi_periodic (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    w8Psi hm n ξ (θ + fun i => (k i : ℝ)) = w8Psi hm n ξ θ := by
  obtain ⟨-, -, hper, -, -⟩ := (w8tori hm n).1 ξ hξ
  have hp : ∀ i : Fin 2, ∀ k : ℤ, ∀ z ∈ complexStrip 2 (w6S0 / 2),
      z + k • _root_.Pi.single i (1 : ℂ) ∈ complexStrip 2 (w6S0 / 2) ∧
        (w8HW hm n).w6TorusBk (w8Eps0W m hm n) (z + k • _root_.Pi.single i (1 : ℂ)) ξ =
          (w8HW hm n).w6TorusBk (w8Eps0W m hm n) z ξ := fun i =>
    w6_periodic_zsmul (f := fun z => (w8HW hm n).w6TorusBk (w8Eps0W m hm n) z ξ)
      (fun z hz => w6_strip_sub_single hz i) fun z hz => hper z hz i
  have hz := w6_real_mem_strip_half θ
  obtain ⟨m0, e0⟩ := hp 0 (k 0) _ hz
  unfold w8Psi
  rw [w8_aaOfReal_add_int, (hp 1 (k 1) _ m0).2, e0]

/-- **Torus shape (iv)** (blueprint `bpW:w8:torus-shape` (iv), Step `stepW:w8:ts-cauchy`): at real
`θ`, `‖DX(θ)‖ ≤ 128e/7 ≤ 1/2` (Cauchy on `B(θ, s_0/2) ⊆ T_{s_0/2}`, W1 `bpW:w1:cauchy`). -/
theorem w8_torusShape_deriv (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    ‖fderiv ℂ (w8XC hm n ξ) (aaOfReal θ)‖ ≤ 128 * w8ShellEtor m hm n / 7 ∧
      128 * w8ShellEtor m hm n / 7 ≤ 1 / 2 := by
  obtain ⟨he0, he1, -⟩ := w8_shell_consts hm n
  have hs : (0 : ℝ) < w6S0 / 2 := by rw [w6S0_val]; norm_num
  have hdiff : DifferentiableOn ℂ (w8XC hm n ξ) (complexStrip 2 (w6S0 / 2)) :=
    (w8TK_differentiableOn hm n hξ).fst.sub differentiableOn_id
  have hball : ball (aaOfReal θ) (w6S0 / 2) ⊆ complexStrip 2 (w6S0 / 2) := fun z hz i => by
    have h1 := (norm_le_pi_norm (z - aaOfReal θ) i).trans_lt (mem_ball_iff_norm.1 hz)
    have h2 := Complex.abs_im_le_norm (z i - aaOfReal θ i)
    simp only [aaOfReal, Complex.sub_im, Complex.ofReal_im, sub_zero, _root_.Pi.sub_apply] at h2 h1
    linarith
  have h := norm_fderiv_le_div_of_ball_subset hs he0 hdiff
    (fun z hz => (w8TK_close hm n hξ hz).1) hball
  refine ⟨h.trans (le_of_eq ?_), by linarith⟩
  rw [w6S0_val]; ring

/-- **Torus shape (iv), Lipschitz** (blueprint `bpW:w8:torus-shape` (iv)):
`|X(θ) - X(θ')| ≤ |θ - θ'|/2` for real `θ, θ'`. -/
theorem w8Xang_lipschitz (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ θ' : Fin 2 → ℝ) : ‖w8Xang hm n ξ θ - w8Xang hm n ξ θ'‖ ≤ 1 / 2 * ‖θ - θ'‖ := by
  obtain ⟨he0, he1, -⟩ := w8_shell_consts hm n
  have hs : (0 : ℝ) < w6S0 / 2 := by rw [w6S0_val]; norm_num
  have hdiff : DifferentiableOn ℂ (w8XC hm n ξ) (complexStrip 2 (w6S0 / 2)) :=
    (w8TK_differentiableOn hm n hξ).fst.sub differentiableOn_id
  have hconv : Convex ℝ (range aaOfReal) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b - - -
    exact ⟨a • x + b • y, by ext i; simp [aaOfReal]⟩
  have hCV : ∀ z ∈ range aaOfReal, ball z (w6S0 / 2) ⊆ complexStrip 2 (w6S0 / 2) := by
    rintro _ ⟨x, rfl⟩ z hz i
    have h1 := (norm_le_pi_norm (z - aaOfReal x) i).trans_lt (mem_ball_iff_norm.1 hz)
    have h2 := Complex.abs_im_le_norm (z i - aaOfReal x i)
    simp only [aaOfReal, Complex.sub_im, Complex.ofReal_im, sub_zero, _root_.Pi.sub_apply] at h2 h1
    linarith
  have h := lipschitz_of_margin hs he0 (isOpen_complexStrip 2 _) hdiff
    (fun z hz => (w8TK_close hm n hξ hz).1) hconv hCV (aaOfReal θ) ⟨θ, rfl⟩ (aaOfReal θ')
    ⟨θ', rfl⟩
  rw [w8XC_real hm n hξ, w8XC_real hm n hξ, norm_aaOfReal_sub, norm_aaOfReal_sub] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [w6S0_val]
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **Torus shape (v)** (blueprint `bpW:w8:torus-shape` (v), Step `stepW:w8:ts-ball`), with
the reality of `Ψ̃` (`bpW:w6:tori` (i)): `‖Ψ̃(θ)‖² < c_A(t_n + r_n²) = ρ_n² ≤ 2c_A t_n < r₁²`,
`Ψ̃(θ) ∈ B_{ρ₁}`, `ϱΨ̃(θ) = Ψ̃(θ)`, `𝒵⁻¹Ψ̃(θ) ∈ B^E_{r₁}` is real and `𝒵 𝒵⁻¹ Ψ̃(θ) = Ψ̃(θ)`. -/
theorem w8Psi_ball (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    ‖w8Psi hm n ξ θ‖ ^ 2 < aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) ∧
      aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) ≤ 2 * aaCA * w8tn 𝔱 n ∧
      2 * aaCA * w8tn 𝔱 n < birkRho1 m 1 ^ 2 / 2 ∧
      w8Psi hm n ξ θ ∈ birkBall1 m 1 ∧ birkRho (w8Psi hm n ξ θ) = w8Psi hm n ξ θ ∧
      birkPi (w8Psi hm n ξ θ) ∈ birkRealBall1 m 1 ∧
      birkZR (birkPi (w8Psi hm n ξ θ)) = w8Psi hm n ξ θ := by
  set H := w8HW hm n
  obtain ⟨-, hB, -, hreal, -⟩ := (w8tori hm n).1 ξ hξ
  obtain ⟨-, -, hr2, -, hαt, -, ht, -, hr⟩ := w8_shell_consts hm n
  obtain ⟨⟨-, -, -⟩, -, -, -, -, -, -, hρ2⟩ := w8_shellData_sizes hm (w8Upstream m hm) n
  have hz := w6_real_mem_strip_half θ
  have hw := ((w8ShellToriKam H).2.2.1 _ (w8_strip_half_sub hm n hz) ξ hξ).1
  have hη := H.prepStepHyp.hη
  have hη0 := H.prepStepHyp.hη0
  have hsub : kamDomain (w6S - 4 * w6SigmaP)
      (2 * w6EtaP (w8alpha 𝔱 n) (w8epsSharp m hm 𝔱 n) * w8rn 𝔱 n) ⊆
      kamDomain (1 / 8) (w8rn 𝔱 n) :=
    kamDomain_mono (by rw [w6SigmaP_val]; unfold w6S; norm_num) (by positivity) (by nlinarith)
  have hξP : ξ ∈ w8Pi 𝔱 n := w8ShellGamma_subset_Pi H hξ
  obtain ⟨hre0, hnorm0⟩ := w8_shellPi_bounds hm n hξP
  have hnorm : ‖aaOfReal ξ‖ ≤ w8tn 𝔱 n := by
    have e := norm_aaOfReal_sub ξ 0
    have e2 : aaOfReal ξ - aaOfReal 0 = aaOfReal ξ := by ext i; simp
    rw [e2, sub_zero] at e
    rw [e]; exact hnorm0
  have hre : ∀ i, 2 * w8rn 𝔱 n ^ 2 ≤ (aaOfReal ξ i).re := fun i => by simpa using hre0 i
  have hdom := (aaMap_domain le_rfl hr ht (aaOfReal ξ) hnorm hre (hsub hw)).2
  have hrt : w8rn 𝔱 n ^ 2 ≤ w8tn 𝔱 n := by
    have := (w8_shell_consts hm n).2.2.2.2.2.2.2.1; linarith
  have hcA : (0 : ℝ) < aaCA := by unfold aaCA; norm_num
  have h1 : aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) ≤ 2 * aaCA * w8tn 𝔱 n := by nlinarith
  have h2 : 2 * aaCA * w8tn 𝔱 n < birkRho1 m 1 ^ 2 / 2 := hρ2
  have hρsq := birkRho1_sq (m := m) (hm := hm) (p := 1) (hp := by norm_num)
  have hCF := birkCF_pos m hm (p := 1) (by norm_num)
  have hPsi : ‖w8Psi hm n ξ θ‖ ^ 2 < aaCA * (w8tn 𝔱 n + w8rn 𝔱 n ^ 2) := hdom
  refine ⟨hPsi, h1, h2, hB _ hz, hreal θ, ?_, birkZR_birkPi _ (hreal θ)⟩
  show 320 * birkCF m 1 * ‖birkPi (w8Psi hm n ξ θ)‖ ^ 2 < 1
  have hpi := norm_birkPi_le (w8Psi hm n ξ θ)
  have hsq : ‖birkPi (w8Psi hm n ξ θ)‖ ^ 2 ≤ ‖w8Psi hm n ξ θ‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hpi 2
  have : 320 * birkCF m 1 * (birkRho1 m 1 ^ 2 / 2) = 1 := by
    rw [hρsq]; field_simp; norm_num
  nlinarith

end KAM.Wave

end
