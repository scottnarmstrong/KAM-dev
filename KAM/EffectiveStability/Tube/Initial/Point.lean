/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.Domain
public import KAM.EffectiveStability.Tube.Ecc.Sound
public import KAM.EffectiveStability.Tube.Poly.Center

/-!
# The tube chart at a rational point (T2-CONF, N5c)

Helpers for the initial box `Q` of the tube checker
(`KAM/EffectiveStability/Tube/Check/TubeChart.lean`):

* `abs_fderiv_tubeCenter_le`: `|∂_{φ_b} B_l| ≤ lipSum_b(l)` for the tube centre
  `B = tubeCenter modes Ibar` (the `β` of the checker).
* `exp_tubeChart_angle`: the reduced angles of the chart at `x` are those of the unit complex
  numbers `ζ_a/|ζ_a|`, `ζ_a = z_a · conj z_2`, `z_j = p_j - i q_j`, `(q, p) = Vᵀ x`.
* `norm_div_norm_sub_le`: a rational test (`unitOK`) that `‖ζ/|ζ| - P‖ ≤ ε` for a unit `P`.
* `abs_tubeU_le_of_point`: **the enclosure of `u(z)`** at a point whose rotated coordinates are
  rational, through rational circle points `P_a = circPt s_a t_a` and the exact fixed-point centre
  of N6 (`pointMu`, a rational).
* `abs_obs_sub_le_of_face`: the centre bound `|f_j(u(z), φ(z)) - c̃_j| ≤ ε_j + μ_j` from the face
  bound and `|u(z)| ≤ μ ≤ ρ`.
-/

@[expose] public section

open Complex Matrix

namespace KAM.EffectiveStability.Tube

/-! ### The derivative of the tube centre -/

theorem hasFDerivAt_tubeCenter (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (φ : Fin 2 → ℝ) :
    HasFDerivAt (fun φ => tubeCenter modes Ibar k φ)
      ((modes.map fun x => (((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) *
        Real.sin (x.1 * φ 0 + x.2.1 * φ 1)) • phaseCLM x.1 x.2.1).sum) φ := by
  unfold tubeCenter
  refine (hasFDerivAt_const _ φ).add ?_ |>.congr_fderiv (zero_add _)
  induction modes with
  | nil => simpa using hasFDerivAt_const (0 : ℝ) φ
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h := ((hasFDerivAt_phase x.1 x.2.1 φ).cos).const_mul
      (-((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ))
    refine (h.add ih).congr_fderiv ?_
    rw [smul_smul]
    congr 2
    ring

/-- `|∂_{φ_b} B_l| ≤ Σ_m |m_l σ_m| |m_b|` (`lipSum₁` for `b = 0`, `lipSum₂` for `b = 1`). -/
theorem abs_fderiv_tubeCenter_le (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (φ : Fin 2 → ℝ)
    (b : Fin 2) (l : Fin 3) :
    |fderiv ℝ (fun φ k => tubeCenter modes Ibar k φ) φ (Pi.single b 1) l| ≤
      ((if b = 0 then lipSum₁ modes l else lipSum₂ modes l : ℚ) : ℝ) := by
  have hd : ∀ k, DifferentiableAt ℝ (fun φ => tubeCenter modes Ibar k φ) φ :=
    fun k => (hasFDerivAt_tubeCenter modes Ibar k φ).differentiableAt
  rw [fderiv_pi hd]
  simp only [ContinuousLinearMap.pi_apply]
  rw [(hasFDerivAt_tubeCenter modes Ibar l φ).fderiv, clm_list_sum_apply]
  have hb : ∀ x : ℤ × ℤ × ℚ, |phaseCLM x.1 x.2.1 (Pi.single b 1)| =
      ((if b = 0 then |(x.1 : ℚ)| else |(x.2.1 : ℚ)| : ℚ) : ℝ) := by
    intro x; fin_cases b <;> simp [phaseCLM]
  have key : ∀ (L : List (ℤ × ℤ × ℚ)),
      |(L.map fun x => ((((modeK x.1 x.2.1 l : ℤ) : ℝ) * (x.2.2 : ℝ) *
        Real.sin (x.1 * φ 0 + x.2.1 * φ 1)) • phaseCLM x.1 x.2.1) (Pi.single b 1)).sum| ≤
      (L.map fun x => (((|(modeK x.1 x.2.1 l : ℚ)| * |x.2.2| *
        (if b = 0 then |(x.1 : ℚ)| else |(x.2.1 : ℚ)|) : ℚ)) : ℝ)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans (add_le_add ?_ ih)
      rw [_root_.smul_apply, smul_eq_mul, abs_mul, abs_mul, abs_mul, hb x]
      push_cast
      have hs := Real.abs_sin_le_one (x.1 * φ 0 + x.2.1 * φ 1)
      have h0 : 0 ≤ |((modeK x.1 x.2.1 l : ℤ) : ℝ)| * |(x.2.2 : ℝ)| := by positivity
      have h1 : (0 : ℝ) ≤ ((if b = 0 then |(x.1 : ℚ)| else |(x.2.1 : ℚ)| : ℚ) : ℝ) := by
        split_ifs <;> simp
      calc |((modeK x.1 x.2.1 l : ℤ) : ℝ)| * |(x.2.2 : ℝ)| * |Real.sin (x.1 * φ 0 + x.2.1 * φ 1)| *
            ((if b = 0 then |(x.1 : ℚ)| else |(x.2.1 : ℚ)| : ℚ) : ℝ)
          ≤ |((modeK x.1 x.2.1 l : ℤ) : ℝ)| * |(x.2.2 : ℝ)| * 1 *
            ((if b = 0 then |(x.1 : ℚ)| else |(x.2.1 : ℚ)| : ℚ) : ℝ) := by gcongr
        _ = _ := by split_ifs <;> push_cast <;> ring
  refine (key modes).trans (le_of_eq ?_)
  rw [← cast_list_sum_map]
  congr 1
  fin_cases b
  · simp [lipSum₁, treeSumQ_eq]
  · simp [lipSum₂, treeSumQ_eq]

/-! ### Angles of the chart -/

/-- The complex mode `z_j = p_j - i q_j` of the rotated point `(q, p) = Vᵀ x`. -/
noncomputable def zMode (V : Matrix (Fin 3) (Fin 3) ℝ) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (j : Fin 3) :
    ℂ :=
  ⟨(rotMap Vᵀ x).2 j, -(rotMap Vᵀ x).1 j⟩

theorem zMode_ne_zero {V : Matrix (Fin 3) (Fin 3) ℝ} {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : x ∈ modesPos V) (j : Fin 3) : zMode V x j ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [zMode] at h1 h2
  have := hx j
  simp [modeSq, h1, h2] at this

theorem exp_arg_mul_I {z : ℂ} (hz : z ≠ 0) : Complex.exp (Complex.arg z * I) = z / (‖z‖ : ℂ) := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  field_simp
  rw [mul_comm]; exact h

/-- The reduced angles of the chart at `x` are those of `ζ_a = z_a conj z_2`. -/
theorem exp_tubeChart_angle (V : Matrix (Fin 3) (Fin 3) ℝ) (B : (Fin 2 → ℝ) → (Fin 3 → ℝ))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ modesPos V) (a : Fin 2) :
    Complex.exp ((tubeChart V B x).2 a * I) =
      zMode V x a.castSucc * (starRingEnd ℂ) (zMode V x 2) /
        (‖zMode V x a.castSucc * (starRingEnd ℂ) (zMode V x 2)‖ : ℂ) := by
  have hθ : ∀ j, Complex.exp ((polarInv (rotMap Vᵀ x)).2 j * I) =
      zMode V x j / (‖zMode V x j‖ : ℂ) := fun j => exp_arg_mul_I (zMode_ne_zero hx j)
  have hφ : (tubeChart V B x).2 a = (polarInv (rotMap Vᵀ x)).2 a.castSucc -
      (polarInv (rotMap Vᵀ x)).2 2 := by
    fin_cases a <;> rfl
  have h2 := zMode_ne_zero hx 2
  have hn2 : (‖zMode V x 2‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h2
  have hna : (‖zMode V x a.castSucc‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (zMode_ne_zero hx _)
  rw [hφ, Complex.ofReal_sub, sub_mul, Complex.exp_sub, hθ, hθ, norm_mul, norm_conj]
  have hc : zMode V x 2 * (starRingEnd ℂ) (zMode V x 2) = ((‖zMode V x 2‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  push_cast
  field_simp
  linear_combination (-zMode V x a.castSucc) * hc

/-! ### Rational circle points near a unit vector -/

/-- The rational test of `‖ζ/|ζ| - P‖ ≤ ε` for a unit `P` (`norm_div_norm_sub_le`). -/
def unitOK (ζ P : GQ) (ε : ℚ) : Bool :=
  decide (0 ≤ ε) && decide (0 ≤ 1 - ε * ε / 2) && decide (0 ≤ ζ.reDot P) &&
    decide ((1 - ε * ε / 2) * (1 - ε * ε / 2) * ζ.nsq ≤ ζ.reDot P * ζ.reDot P)

theorem norm_div_norm_sub_le {ζ P : ℂ} (hζ : ζ ≠ 0) (hP : ‖P‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : 0 ≤ 1 - ε * ε / 2) (hρ : 0 ≤ rdot ζ P)
    (h : (1 - ε * ε / 2) * (1 - ε * ε / 2) * Complex.normSq ζ ≤ rdot ζ P * rdot ζ P) :
    ‖ζ / (‖ζ‖ : ℂ) - P‖ ≤ ε := by
  set n := ‖ζ‖ with hn
  have hn0 : 0 < n := norm_pos_iff.mpr hζ
  set c := 1 - ε * ε / 2
  have hcn : c * n ≤ rdot ζ P := by
    have h1 : (c * n) * (c * n) ≤ rdot ζ P * rdot ζ P := by
      rw [Complex.normSq_eq_norm_sq] at h; nlinarith
    exact (mul_self_le_mul_self_iff (mul_nonneg hc hn0.le) hρ).mpr h1
  have hu : Complex.normSq (ζ / (n : ℂ) - P) = 2 - 2 * rdot ζ P / n := by
    have hP2 : Complex.normSq P = 1 := by rw [Complex.normSq_eq_norm_sq, hP]; norm_num
    have hz2 : Complex.normSq ζ = n ^ 2 := by rw [Complex.normSq_eq_norm_sq]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
    rw [Complex.normSq_apply] at hP2 hz2
    simp only [rdot]
    field_simp
    nlinarith [hP2, hz2]
  have h2 : Complex.normSq (ζ / (n : ℂ) - P) ≤ ε * ε := by
    rw [hu]
    have : c ≤ rdot ζ P / n := by rw [le_div_iff₀ hn0]; exact hcn
    have e : 2 * rdot ζ P / n = 2 * (rdot ζ P / n) := by ring
    rw [e]; simp only [c] at this; linarith
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg (ζ / (n : ℂ) - P)]

/-! ### The tube deviation at a rational point -/

/-- `ζ_a = z_a conj z_2` from rational rotated coordinates `(q, p)`, `z_j = p_j - i q_j`. -/
def pointZeta (q p : Fin 3 → ℚ) (a : Fin 2) : GQ :=
  GQ.mul ⟨p a.castSucc, -q a.castSucc⟩ (GQ.conj ⟨p 2, -q 2⟩)

/-- The exact fixed-point centre `B̃_k` at the rational circle points `circPt s_a t_a`. -/
def pointCenter (d : EccData) (s₁ s₂ : Bool) (t₁ t₂ : ℚ) (k : Fin 3) : ℚ :=
  d.Ibar k + (bSumZ d.fix (GZ.table (circG s₁ t₁) (circN t₁) d.M)
    (GZ.table (circG s₂ t₂) (circN t₂) d.M) k : ℚ) /
    (pow2 d.K * ((circN t₁ ^ d.M * circN t₂ ^ d.M : ℤ) : ℚ))

/-- The enclosure radius of `u_k` at the point: `|I_k - B̃_k| + ε₁ L₁ + ε₂ L₂ + τ`. -/
def pointMu (d : EccData) (q p : Fin 3 → ℚ) (s₁ s₂ : Bool) (t₁ t₂ ε₁ ε₂ : ℚ) (k : Fin 3) : ℚ :=
  |(q k * q k + p k * p k) / 2 - pointCenter d s₁ s₂ t₁ t₂ k| + ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k

theorem toC_pointZeta {V : Matrix (Fin 3) (Fin 3) ℝ} {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    {q p : Fin 3 → ℚ} (hq : ∀ j, (rotMap Vᵀ x).1 j = q j) (hp : ∀ j, (rotMap Vᵀ x).2 j = p j)
    (a : Fin 2) :
    GQ.toC (pointZeta q p a) = zMode V x a.castSucc * (starRingEnd ℂ) (zMode V x 2) := by
  rw [pointZeta, GQ.toC_mul, GQ.toC_conj]
  congr 1 <;> [skip; congr 1] <;> apply Complex.ext <;> simp [GQ.toC, zMode, hq, hp]

/-- **The enclosure of `u(z)`** at a point with rational rotated coordinates. -/
theorem abs_tubeU_le_of_point {d : EccData} (hg : globalOK d = true)
    {V : Matrix (Fin 3) (Fin 3) ℝ} {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ modesPos V)
    {q p : Fin 3 → ℚ} (hq : ∀ j, (rotMap Vᵀ x).1 j = q j) (hp : ∀ j, (rotMap Vᵀ x).2 j = p j)
    {s₁ s₂ : Bool} {t₁ t₂ ε₁ ε₂ : ℚ}
    (h₁ : unitOK (pointZeta q p 0) (circPt s₁ t₁) ε₁ = true)
    (h₂ : unitOK (pointZeta q p 1) (circPt s₂ t₂) ε₂ = true) (k : Fin 3) :
    |tubeU V (fun φ k => tubeCenter d.modes d.Ibar k φ) x k| ≤
      (pointMu d q p s₁ s₂ t₁ t₂ ε₁ ε₂ k : ℝ) := by
  obtain ⟨hfix, hM, hLk⟩ := globalOK_spec hg
  obtain ⟨hL₁, hL₂, hτ⟩ := hLk k
  set B : (Fin 2 → ℝ) → (Fin 3 → ℝ) := fun φ k => tubeCenter d.modes d.Ibar k φ
  -- the chart points and their rational approximations
  have hw : ∀ (a : Fin 2) (s : Bool) (t ε : ℚ), unitOK (pointZeta q p a) (circPt s t) ε = true →
      ‖Complex.exp ((tubeChart V B x).2 a * I) - GQ.toC (circPt s t)‖ ≤ ε ∧ 0 ≤ (ε : ℝ) := by
    intro a s t ε h
    simp only [unitOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hc⟩, hρ⟩, hh⟩ := h
    have hζ : GQ.toC (pointZeta q p a) ≠ 0 := by
      rw [toC_pointZeta hq hp]
      exact mul_ne_zero (zMode_ne_zero hx _) ((map_ne_zero _).mpr (zMode_ne_zero hx 2))
    rw [exp_tubeChart_angle V B hx a, ← toC_pointZeta hq hp]
    refine ⟨norm_div_norm_sub_le hζ (norm_toC_circPt s t) (by exact_mod_cast h0)
      (by exact_mod_cast hc) (by rw [rdot_toC]; exact_mod_cast hρ) ?_, by exact_mod_cast h0⟩
    rw [rdot_toC, ← GQ.nsq_eq]
    exact_mod_cast hh
  obtain ⟨hε₁, hε₁0⟩ := hw 0 s₁ t₁ ε₁ h₁
  obtain ⟨hε₂, hε₂0⟩ := hw 1 s₂ t₂ ε₂ h₂
  have hn : ∀ a : Fin 2, ‖Complex.exp ((tubeChart V B x).2 a * I)‖ = 1 :=
    fun a => norm_exp_mul_I _
  -- `B` at the chart angles
  have hB : B (tubeChart V B x).2 k = tubeCenterW d.modes d.Ibar k
      (Complex.exp ((tubeChart V B x).2 0 * I)) (Complex.exp ((tubeChart V B x).2 1 * I)) :=
    tubeCenter_eq_W d.modes d.Ibar k _
  have hc : (pointCenter d s₁ s₂ t₁ t₂ k : ℝ) = fixCenterW d.K d.fix d.Ibar k
      (GQ.toC (circPt s₁ t₁)) (GQ.toC (circPt s₂ t₂)) :=
    bSumZ_div_eq d.K d.M d.fix d.Ibar k hM s₁ s₂ t₁ t₂
  have hlip := abs_tubeCenterW_sub_le d.modes d.Ibar k (hn 0) (hn 1)
    (norm_toC_circPt s₁ t₁) (norm_toC_circPt s₂ t₂) hε₁ hε₂
  have hrnd := abs_tubeCenterW_sub_fix_le d.K d.modes d.Ibar k (norm_toC_circPt s₁ t₁)
    (norm_toC_circPt s₂ t₂)
  rw [← hfix] at hrnd
  have hL₁' : (lipSum₁ d.modes k : ℝ) ≤ d.L₁ k := by exact_mod_cast hL₁
  have hL₂' : (lipSum₂ d.modes k : ℝ) ≤ d.L₂ k := by exact_mod_cast hL₂
  have hτ' : (errSum d.K d.modes k : ℝ) ≤ d.tau k := by exact_mod_cast hτ
  have hI : modeSq V x k / 2 = (((q k * q k + p k * p k) / 2 : ℚ) : ℝ) := by
    simp only [modeSq, hq, hp]; push_cast; ring
  rw [tubeU_apply, hI, hB]
  unfold pointMu
  push_cast
  rw [hc] at *
  have := mul_le_mul_of_nonneg_left hL₁' hε₁0
  have := mul_le_mul_of_nonneg_left hL₂' hε₂0
  have e := abs_sub_le ((((q k * q k + p k * p k) / 2 : ℚ) : ℝ))
    (fixCenterW d.K d.fix d.Ibar k (GQ.toC (circPt s₁ t₁)) (GQ.toC (circPt s₂ t₂)))
    (tubeCenterW d.modes d.Ibar k (Complex.exp ((tubeChart V B x).2 0 * I))
      (Complex.exp ((tubeChart V B x).2 1 * I)))
  have e2 := abs_sub_le (tubeCenterW d.modes d.Ibar k (Complex.exp ((tubeChart V B x).2 0 * I))
      (Complex.exp ((tubeChart V B x).2 1 * I)))
    (tubeCenterW d.modes d.Ibar k (GQ.toC (circPt s₁ t₁)) (GQ.toC (circPt s₂ t₂)))
    (fixCenterW d.K d.fix d.Ibar k (GQ.toC (circPt s₁ t₁)) (GQ.toC (circPt s₂ t₂)))
  rw [abs_sub_comm] at e2
  push_cast at e
  linarith [abs_sub_comm (tubeCenterW d.modes d.Ibar k (GQ.toC (circPt s₁ t₁))
    (GQ.toC (circPt s₂ t₂))) (fixCenterW d.K d.fix d.Ibar k (GQ.toC (circPt s₁ t₁))
    (GQ.toC (circPt s₂ t₂)))]

/-! ### The observable at the centre point from the face bound -/

/-- From the face bound `|f(u, φ) - c̃ - u_j| ≤ ε` on the box `|u| ≤ ρ` and `|u(z)| ≤ μ ≤ ρ`:
`|f(tubeChart z) - c̃| ≤ ε + μ_j`. -/
theorem abs_obs_sub_le_of_face {V : Matrix (Fin 3) (Fin 3) ℝ} {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)}
    {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {ct ε ρ : ℝ} {μ : Fin 3 → ℝ}
    {z : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (j : Fin 3)
    (hface : ∀ u φ, (∀ l, |u l| ≤ ρ) → |f (u, φ) - ct - u j| ≤ ε)
    (hμ : ∀ l, |tubeU V B z l| ≤ μ l) (hμρ : ∀ l, μ l ≤ ρ) :
    |f (tubeChart V B z) - ct| ≤ ε + μ j := by
  have h := hface (tubeChart V B z).1 (tubeChart V B z).2 fun l => (hμ l).trans (hμρ l)
  have hu : |(tubeChart V B z).1 j| ≤ μ j := hμ j
  calc |f (tubeChart V B z) - ct| = |(f ((tubeChart V B z).1, (tubeChart V B z).2) - ct -
        (tubeChart V B z).1 j) + (tubeChart V B z).1 j| := by ring_nf
    _ ≤ ε + μ j := (abs_add_le _ _).trans (add_le_add h hu)

end KAM.EffectiveStability.Tube

end
