/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellTorus
public import KAM.Wave.Assembly.InjAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: each shell torus is an analytic torus embedding (blueprint `bpW:w8:Kshell`,
`bpW:w8:shell-embedding`)

Blueprint labels `bpW:w8:Kshell`, `bpW:w8:shell-embedding` (milestone W8).

* `w8AA ξ = 𝒜_ξ` (W5's `aaMap 1 1 ξ`, `bpW:w5:action-angle`) and
  `w8Kshell w8AA (w8HW hm n) ξ = w8KOfBirk m hm (w8Psi hm n ξ)` (`w8Kshell_eq`), i.e.
  `K^{(n)}_ξ(θ) = τ_E Γ^ℝ(𝒵⁻¹ Ψ̃^{(n)}_ξ(θ))` (Definition `bpW:w8:Kshell`, `τ_E = id`);
* `w8_phase_int_of_eq`: equal tangential coordinates of the shape of `bpW:w8:torus-shape` (ii)
  have phases differing by an integer (Step `stepW:w8:se-inj`, `bpW:w8:ext-exp`);
* **`w8_shellEmbedding`** (Lemma `bpW:w8:shell-embedding`): `IsAnalyticTorusEmbedding K^{(n)}_ξ`.

Step `stepW:w8:se-der` (injective derivative) is proved through the left inverse of `Γ^ℝ`
(W3 Corollary `bpW:w3:gamma-real` (iii): `𝒵⁻¹Γ_{-1}𝒵Γ^ℝ = id`): with `x = 𝒵⁻¹Ψ̃`,
`x = G ∘ K` for the differentiable `G = 𝒵⁻¹ ∘ Γ_{-1} ∘ 𝒵`, so `DK(θ)h = 0` gives `Dx(θ)h = 0`, hence
`DΨ̃(θ)h = 0` (`Ψ̃ = 𝒵x`); this replaces the blueprint's appeal to the invertibility of `DΓ`
(Theorem `bpW:w3:flow` (iii)) and its commutation with `ϱ`, and gives the same conclusion.
The `+i` component then forces `h_i + DX_i(θ)h = 0`, and `‖DX(θ)‖ ≤ 1/2` gives `h = 0`.
-/

@[expose] public noncomputable section

open Set Real Complex Metric

namespace KAM.Wave

open KAM

/-- `A ξ = 𝒜_ξ`, W5's action–angle map at `a = p = 1` (`bpW:w5:action-angle`). -/
def w8AA (ξ : Fin 2 → ℝ) (w : KamPhase) : BirkSpace := aaMap 1 1 (aaOfReal ξ) w

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

local macro "w8tori" hm:term:max n:term:max : term =>
  `((w8HW $hm $n).w6Tori (w8_toriData $hm $n).1 (w8_toriData $hm $n).2.1
    (w8_toriData $hm $n).2.2.1 (w8_toriData $hm $n).2.2.2.1 (w8_toriData $hm $n).2.2.2.2)

/-- **Shell embeddings** (blueprint `bpW:w8:Kshell`): `K^{(n)}_ξ = w8KOfBirk m hm Ψ̃^{(n)}_ξ`. -/
theorem w8Kshell_eq (n : ℕ) (ξ : Fin 2 → ℝ) :
    w8Kshell w8AA (w8HW hm n) ξ = w8KOfBirk m hm (w8Psi hm n ξ) := rfl

theorem w8_birkPi_eq_reWave (w : BirkSpace) : birkPi w = reWave (birkZinv w) := rfl

/-- Step `stepW:w8:se-inj` (`bpW:w8:ext-exp`): if `a e^{-2πiφ} = a' e^{-2πiφ'}` with `a, a' > 0`
real, then `φ - φ' ∈ ℤ` (and `a = a'`). -/
theorem w8_phase_int_of_eq {a a' φ φ' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (h : (a : ℂ) * cexp (-(2 * π * I * φ)) = (a' : ℂ) * cexp (-(2 * π * I * φ'))) :
    ∃ k : ℤ, φ - φ' = k := by
  have hnorm : ∀ x : ℝ, ‖cexp (-(2 * π * I * x))‖ = 1 := fun x => by
    have : -(2 * π * I * x) = ((-(2 * π * x) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]; exact (w8ext_norm_exp_I _).1
  have haa : a = a' := by
    have := congrArg norm h
    rwa [norm_mul, norm_mul, hnorm, hnorm, mul_one, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos ha'] at this
  subst haa
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2 := mul_left_cancel₀ hne h
  have h3 : cexp (-(2 * π * I * (φ - φ'))) = 1 := by
    have : -(2 * π * I * ((φ : ℂ) - φ')) = -(2 * π * I * φ) - -(2 * π * I * φ') := by ring
    rw [this, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := (w8ext_exp_eq_one_iff _).1 h3
  refine ⟨-n, ?_⟩
  have hpi : (2 * π * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h4 : ((φ - φ' : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination (-1 : ℂ) * hn
  exact_mod_cast h4

theorem w8_exp_cancel (A W z : ℂ) : A * cexp (-z) * W * cexp z = A * W := by
  rw [mul_assoc A, mul_comm (cexp (-z)) W, ← mul_assoc, mul_assoc, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, mul_one]

/-- The `+i` tangential coordinate (`b = true`) of `Ψ̃` at real `θ`:
`√(ξ_i + y_i) e^{-2πi(θ_i + X_i)}`. -/
theorem w8_coord_true (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (i : Fin 2) :
    birkCoord 1 1 (w8Psi hm n ξ θ) (true, modeIdx i) =
      ((Real.sqrt (ξ i + w8Yact hm n ξ θ i) : ℝ) : ℂ) *
        cexp (-(2 * π * I * ((θ i + w8Xang hm n ξ θ i : ℝ) : ℂ))) := by
  rw [w8_torusShape_coord hm n hξ θ true i]
  simp [birkSgn, w8Xang]

theorem w8_sqrt_pos (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (i : Fin 2) : 0 < Real.sqrt (ξ i + w8Yact hm n ξ θ i) := by
  have h := w8_torusShape_real hm n hξ θ i
  have hα := (w8_shell_consts hm n).2.2.2.2.2.2.2.1
  exact Real.sqrt_pos.2 (by linarith)

/-- Step `stepW:w8:se-an`: `K^{(n)}_ξ` is real analytic on `ℝ²` (`bpW:w6:tori` (v)). -/
theorem w8Kshell_analytic (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) :
    AnalyticOnNhd ℝ (w8KOfBirk m hm (w8Psi hm n ξ)) univ := by
  have hA := (w8tori hm n).2.2.2.2.2 ξ hξ
  refine hA.congr isOpen_univ fun θ _ => ?_
  obtain ⟨-, -, -, -, hρ, hb, -⟩ := w8Psi_ball hm n hξ θ
  rw [w8KOfBirk_eq_gamma hρ hb, w8_birkPi_eq_reWave]
  rfl

/-- Step `stepW:w8:se-inj`: `K^{(n)}_ξ(θ) = K^{(n)}_ξ(θ')` implies `θ - θ' ∈ ℤ²`. -/
theorem w8Kshell_injMod (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    {θ θ' : Fin 2 → ℝ} (h : w8KOfBirk m hm (w8Psi hm n ξ) θ = w8KOfBirk m hm (w8Psi hm n ξ) θ') :
    ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) := by
  obtain ⟨-, -, -, -, -, hb, hr⟩ := w8Psi_ball hm n hξ θ
  obtain ⟨-, -, -, -, -, hb', hr'⟩ := w8Psi_ball hm n hξ θ'
  have hΨ := w8KOfBirk_eq_of_eq hb hb' hr hr' h
  have hk : ∀ i, ∃ k : ℤ, (θ i + w8Xang hm n ξ θ i) - (θ' i + w8Xang hm n ξ θ' i) = k :=
      fun i => by
    have e := congrArg (fun w => birkCoord 1 1 w (true, modeIdx i)) hΨ
    simp only [w8_coord_true hm n hξ] at e
    exact w8_phase_int_of_eq (w8_sqrt_pos hm n hξ θ i) (w8_sqrt_pos hm n hξ θ' i) e
  choose k hk using hk
  refine ⟨k, w8_injMod_of_phase (w8Xang_periodic hm n hξ) (w8Xang_lipschitz hm n hξ) ?_⟩
  funext i
  have := hk i
  simp only [_root_.Pi.sub_apply, _root_.Pi.add_apply]
  linarith

/-- `G = 𝒵⁻¹ ∘ Γ_{-1} ∘ 𝒵` is a left inverse of `K^{(n)}_ξ` on `𝒵⁻¹Ψ̃`: `G(K(θ)) = 𝒵⁻¹Ψ̃(θ)`
(W3 Corollary `bpW:w3:gamma-real` (iii)). -/
theorem w8Kshell_leftInv (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    birkPi (birkGamma m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) (-1)
      (birkZR (w8KOfBirk m hm (w8Psi hm n ξ) θ))) = birkPi (w8Psi hm n ξ θ) := by
  obtain ⟨-, -, -, -, -, hb, -⟩ := w8Psi_ball hm n hξ θ
  rw [w8KOfBirk_of_mem hb]
  exact birkGammaR_inv (hm := hm) ⟨_, hb⟩

/-- The left inverse `G` is differentiable at `K(θ)` (`|K(θ)|` small). -/
theorem w8Kshell_leftInv_hasFDerivAt (n : ℕ) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) (θ : Fin 2 → ℝ) :
    ∃ L : WaveSpace →L[ℝ] BirkReal, HasFDerivAt (fun y : WaveSpace =>
      birkPi (birkGamma m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) (-1) (birkZR y)))
      L (w8KOfBirk m hm (w8Psi hm n ξ) θ) := by
  obtain ⟨hn2, h1, h2, -, -, hb, -⟩ := w8Psi_ball hm n hξ θ
  set x : BirkReal := birkPi (w8Psi hm n ξ θ)
  have hK : ‖w8KOfBirk m hm (w8Psi hm n ξ) θ‖ ≤ 10 / 9 * Real.sqrt 2 * ‖x‖ := by
    rw [w8KOfBirk_of_mem hb]
    obtain ⟨-, -, -, h⟩ := birkGammaR_sub (hm := hm) (ha := zero_le_one) (hp := by norm_num) ⟨x, hb⟩
    exact h
  have hx : ‖x‖ ^ 2 < birkRho1 m 1 ^ 2 / 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_birkPi_le (w8Psi hm n ξ θ)) 2
    linarith
  have hρsq := birkRho1_sq (m := m) (hm := hm) (p := 1) (hp := by norm_num)
  have hCF := birkCF_pos m hm (p := 1) (by norm_num)
  set w := birkZR (w8KOfBirk m hm (w8Psi hm n ξ) θ)
  have hw : ‖w‖ ≤ Real.sqrt 2 * (10 / 9 * Real.sqrt 2 * ‖x‖) :=
    (norm_birkZR_le _).trans (mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _))
  have hs2 : Real.sqrt 2 * (10 / 9 * Real.sqrt 2 * ‖x‖) = 20 / 9 * ‖x‖ := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linear_combination (10 / 9 * ‖x‖) * this
  rw [hs2] at hw
  have hw2 : ‖w‖ ^ 2 ≤ (20 / 9) ^ 2 * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hw40 : 40 * birkCF m 1 * ‖w‖ ^ 2 < 1 := by
    have e : 40 * birkCF m 1 * ((20 / 9) ^ 2 * (birkRho1 m 1 ^ 2 / 2)) < 1 := by
      rw [hρsq]; field_simp; norm_num
    have : 40 * birkCF m 1 * ‖w‖ ^ 2 ≤ 40 * birkCF m 1 * ((20 / 9) ^ 2 * (birkRho1 m 1 ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (hw2.trans (by nlinarith)) (by positivity)
    linarith
  have hG := birkGamma_hasFDerivAt (m := m) (hm := hm) (ha := zero_le_one)
    (hp := (by norm_num : (1 / 2 : ℝ) ≤ 1)) (-1) w (by norm_num) hw40
  exact ⟨_, birkPi.hasFDerivAt.comp _ (hG.comp _ birkZR.hasFDerivAt)⟩

/-- Step `stepW:w8:se-der`: `DK^{(n)}_ξ(θ)` is injective. -/
theorem w8Kshell_fderiv_injective (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) : Function.Injective (fderiv ℝ (w8KOfBirk m hm (w8Psi hm n ξ)) θ) := by
  set K := w8KOfBirk m hm (w8Psi hm n ξ)
  set x : (Fin 2 → ℝ) → BirkReal := fun θ' => birkPi (w8Psi hm n ξ θ')
  have hKd : HasFDerivAt K (fderiv ℝ K θ) θ :=
    ((w8Kshell_analytic hm n hξ θ (mem_univ _)).differentiableAt).hasFDerivAt
  obtain ⟨L, hG⟩ := w8Kshell_leftInv_hasFDerivAt hm n hξ θ
  have hx : HasFDerivAt x (L.comp (fderiv ℝ K θ)) θ := by
    have := hG.comp θ hKd
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ' => ?_)
    exact (w8Kshell_leftInv hm n hξ θ').symm
  -- the kernel is trivial
  suffices hker : ∀ h, fderiv ℝ K θ h = 0 → h = 0 by
    intro h h' e
    have := hker (h - h') (by rw [map_sub, e, sub_self])
    exact sub_eq_zero.1 this
  intro h h0
  have hl : HasDerivAt (fun s : ℝ => θ + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add θ
  -- the coordinate `Ψ̃(θ + sh)_{(true, i)}` has derivative `0` at `s = 0`
  have hc : ∀ i : Fin 2, HasDerivAt
      (fun s : ℝ => w8Psi hm n ξ (θ + s • h) (true, modeIdx i)) 0 0 := fun i => by
    set E : BirkSpace →L[ℝ] ℂ :=
      (lp.evalCLM ℂ (fun _ : BirkIdx => ℂ) 2 (true, modeIdx i)).restrictScalars ℝ
    have h1 := (E.comp birkZR).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
      (hx.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)) rfl
    simp only [ContinuousLinearMap.comp_apply, h0, map_zero] at h1
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply, x, E, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars']
    rw [(w8Psi_ball hm n hξ (θ + s • h)).2.2.2.2.2.2]
    rfl
  -- the complex phase along the line
  set F : (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun z => (w8TK hm n z ξ).1
  have hz := w6_real_mem_strip_half θ
  have hFd : HasFDerivAt F (fderiv ℂ F (aaOfReal θ)) (aaOfReal θ) :=
    ((w8TK_differentiableOn hm n hξ).fst.differentiableAt
      ((isOpen_complexStrip 2 _).mem_nhds hz)).hasFDerivAt
  have hlC : HasDerivAt (fun s : ℝ => aaOfReal (θ + s • h)) (aaOfReal h) 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (θ i)).ofReal_comp
    simpa [aaOfReal, mul_comm] using this
  have hφ : HasDerivAt (fun s : ℝ => F (aaOfReal (θ + s • h)))
      (fderiv ℂ F (aaOfReal θ) (aaOfReal h)) 0 :=
    (hFd.restrictScalars ℝ).comp_hasDerivAt_of_eq (x := (0 : ℝ)) hlC (by simp)
  have hXd : fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) =
      fderiv ℂ F (aaOfReal θ) - ContinuousLinearMap.id ℂ _ :=
    (hFd.sub (hasFDerivAt_id _)).fderiv
  have hDX := (w8_torusShape_deriv hm n hξ θ)
  -- the real part of `d_i = h_i + DX_i(θ)h` vanishes
  have hre : ∀ i : Fin 2, h i + (fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i).re = 0 :=
      fun i => by
    have hφi : HasDerivAt (fun s : ℝ => F (aaOfReal (θ + s • h)) i)
        (fderiv ℂ F (aaOfReal θ) (aaOfReal h) i) 0 := hasDerivAt_pi.1 hφ i
    set d := fderiv ℂ F (aaOfReal θ) (aaOfReal h) i
    have he := ((hφi.const_mul (2 * π * I)).cexp)
    have hg := (hc i).mul he
    set wl : ℂ := (RCLike.ofReal (ellWeight 1 1 (modeIdx i)) : ℂ)
    -- `g(s) = Ψ̃(θ+sh)_{(true,i)} e^{2πiφ(s)} = w_l √(ξ_i + y_i)` is real
    have hreal : ∀ s : ℝ, (w8Psi hm n ξ (θ + s • h) (true, modeIdx i) *
        cexp (2 * π * I * F (aaOfReal (θ + s • h)) i)).im = 0 := fun s => by
      have e1 := birkCoord_mul_weight 1 1 (w8Psi hm n ξ (θ + s • h)) (true, modeIdx i)
      rw [← e1, w8_coord_true hm n hξ]
      have e2 : F (aaOfReal (θ + s • h)) i = ((θ + s • h) i + w8Xang hm n ξ (θ + s • h) i : ℝ) := by
        show (w8TK hm n (aaOfReal (θ + s • h)) ξ).1 i = _
        rw [(w8TK_real hm n hξ _).1]
        simp [w8Xang, aaOfReal]
      rw [e2, w8_exp_cancel]
      simp [Complex.mul_im]
    have hgim : (0 * cexp (2 * π * I * F (aaOfReal (θ + (0 : ℝ) • h)) i) +
        w8Psi hm n ξ (θ + (0 : ℝ) • h) (true, modeIdx i) *
          (cexp (2 * π * I * F (aaOfReal (θ + (0 : ℝ) • h)) i) * (2 * π * I * d))).im = 0 := by
      have him := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hg
      have hconst : HasDerivAt (fun s : ℝ => (Complex.imCLM ∘ fun s =>
          w8Psi hm n ξ (θ + s • h) (true, modeIdx i) *
            cexp (2 * π * I * F (aaOfReal (θ + s • h)) i)) s) 0 0 := by
        simp only [Function.comp_apply, Complex.imCLM_apply, hreal]
        exact hasDerivAt_const _ _
      exact him.unique hconst
    -- `g(0) = w_l √(ξ_i + y_i(θ)) > 0`
    have hg0 := hreal 0
    set g0 := w8Psi hm n ξ (θ + (0 : ℝ) • h) (true, modeIdx i) *
      cexp (2 * π * I * F (aaOfReal (θ + (0 : ℝ) • h)) i)
    have hg0re : 0 < g0.re := by
      have e1 := birkCoord_mul_weight 1 1 (w8Psi hm n ξ (θ + (0 : ℝ) • h)) (true, modeIdx i)
      have e2 : F (aaOfReal (θ + (0 : ℝ) • h)) i =
          ((θ + (0 : ℝ) • h) i + w8Xang hm n ξ (θ + (0 : ℝ) • h) i : ℝ) := by
        show (w8TK hm n (aaOfReal (θ + (0 : ℝ) • h)) ξ).1 i = _
        rw [(w8TK_real hm n hξ _).1]
        simp [w8Xang, aaOfReal]
      simp only [g0]
      rw [← e1, w8_coord_true hm n hξ, e2, w8_exp_cancel]
      have hw := ellWeight_pos 1 1 (modeIdx i)
      have hs := w8_sqrt_pos hm n hξ θ i
      simp [Complex.mul_re]
      exact mul_pos hs hw
    have e : (0 * cexp (2 * π * I * F (aaOfReal (θ + (0 : ℝ) • h)) i) +
        w8Psi hm n ξ (θ + (0 : ℝ) • h) (true, modeIdx i) *
          (cexp (2 * π * I * F (aaOfReal (θ + (0 : ℝ) • h)) i) * (2 * π * I * d))) =
        g0 * (2 * π * I * d) := by simp only [g0]; ring
    rw [e] at hgim
    have hd : d = aaOfReal h i + fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i := by
      rw [hXd]; simp [d]
    have him2 : (g0 * (2 * π * I * d)).im = 2 * π * (g0.re * d.re + g0.im * 0) - 0 := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, hg0]
      norm_num
      ring
    rw [him2] at hgim
    have hdre : d.re = 0 := by
      have hπ := Real.pi_pos
      have : g0.re * d.re = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact h'
    rw [hd, Complex.add_re] at hdre
    simpa [aaOfReal] using hdre
  -- `|h| ≤ |DX(θ) h| ≤ |h|/2`
  have hle : ‖h‖ ≤ 1 / 2 * ‖h‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have := hre i
    have h1 : |h i| = |(fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i).re| := by
      rw [show h i = -(fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i).re by linarith,
        abs_neg]
    rw [Real.norm_eq_abs, h1]
    have e0 : ‖aaOfReal h‖ = ‖h‖ := by
      have e := norm_aaOfReal_sub h 0
      have e2 : aaOfReal h - aaOfReal 0 = aaOfReal h := by ext i; simp
      rwa [e2, sub_zero] at e
    calc |(fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i).re|
        ≤ ‖fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h) i‖ := Complex.abs_re_le_norm _
      _ ≤ ‖fderiv ℂ (w8XC hm n ξ) (aaOfReal θ) (aaOfReal h)‖ := norm_le_pi_norm _ i
      _ ≤ ‖fderiv ℂ (w8XC hm n ξ) (aaOfReal θ)‖ * ‖aaOfReal h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / 2 * ‖h‖ := by
          rw [e0]
          exact mul_le_mul_of_nonneg_right (hDX.1.trans hDX.2) (norm_nonneg _)
  exact norm_eq_zero.1 (le_antisymm (by linarith [norm_nonneg h]) (norm_nonneg h))

/-- **Each shell torus is an analytic torus embedding** (blueprint `bpW:w8:shell-embedding`): for
`ξ ∈ Γ_n`, `IsAnalyticTorusEmbedding K^{(n)}_ξ`. -/
theorem w8_shellEmbedding (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) :
    IsAnalyticTorusEmbedding (w8Kshell w8AA (w8HW hm n) ξ) := by
  rw [w8Kshell_eq]
  exact ⟨fun k θ => w8KOfBirk_periodic (w8Psi_periodic hm n hξ θ k),
    w8Kshell_analytic hm n hξ, fun θ θ' h => w8Kshell_injMod hm n hξ h,
    w8Kshell_fderiv_injective hm n hξ⟩

end KAM.Wave

end
