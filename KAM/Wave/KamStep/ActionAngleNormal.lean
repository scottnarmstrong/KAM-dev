/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleDeriv
public import KAM.Wave.KamStep.ActionAngleSymp
public import KAM.Wave.Birkhoff.MainBall
public import KAM.Wave.Birkhoff.MainQuart
public import KAM.Wave.Birkhoff.QuartBarAlg
public import KAM.Wave.Homological.Wave
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The action–angle substitution: the normal form (blueprint-W `bpW:w5:action-angle` (iv))

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (iv), step `a-nf`.

For `ξ ∈ ℂ²` (complexified parameters) and `w ∈ 𝒫` with `𝒜_ξ(w) ∈ B_{ρ₁}`:
`H' ∘ 𝒜_ξ = e(ξ) + N_ξ + P_ξ` (`aaMap_normalForm`), `H' = Λ + Ḡ + G^{nor} + K`, with
* `e(ξ) = ⟨λ_J, ξ⟩ + ½⟨Aξ, ξ⟩` (`aaEnergy`);
* `N_ξ = ⟨ω⁰(ξ), y⟩ + Σ_{j ≥ 1} Ω⁰_{j+2}(ξ) z_j \bar z_j` (`aaNfun`, defined on its convergence
  carrier `0 ≤ a`, `1/2 ≤ p`, where the normal series converges absolutely, `summable_aaNfun`),
  `ω⁰ = λ_J + Aξ` (`aaOmega0`),
  `Ω⁰_J = λ_J + 3⟨b,ξ⟩/(2πλ_J)` (`aaOmegaN0`), `z_j \bar z_j` the actual product (`aaZZ`);
  for real `ξ` these are W4's `waveFreqTan`, `waveFreqNor` (`aaOmega0_ofReal`, `aaOmegaN0_ofReal`),
  i.e. W7's `ω⁰`, `Ω⁰` (Definition `bpW:w7:omega0`);
* `P_ξ = Q̃ + G^{nor} ∘ 𝒜_ξ + K ∘ 𝒜_ξ` (`aaPfun`),
  `Q̃ = ½⟨Ay, y⟩ + Σ_j 3⟨b,y⟩/(2πλ_{j+2}) z_j \bar z_j` (`aaQt`, defined on its convergence carrier
  `0 ≤ a`, `0 ≤ p`; convergence `summable_aaQt`, ActionAngleQt); `K ∘ 𝒜_ξ` uses the extension
  `aaKext` of W3's `K` (defined on `B_{ρ₁}`) by `0`, which agrees with `K` on `B_{ρ₁}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

variable (m : ℝ) (hm : 0 < m)

/-- `⟨b, ξ⟩ = Σ_i ξ_i/λ_i` (complex `ξ`). -/
def aaBdot (ξ : Fin 2 → ℂ) : ℂ := ∑ i : Fin 2, ξ i / (lamTan m hm i : ℂ)

/-- `e(ξ) = ⟨λ_J, ξ⟩ + ½⟨Aξ, ξ⟩`. -/
def aaEnergy (ξ : Fin 2 → ℂ) : ℂ :=
  ∑ i : Fin 2, (lamTan m hm i : ℂ) * ξ i +
    1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) * (ξ i * ξ i')

/-- `ω⁰(ξ) = λ_J + Aξ` (Definition `bpW:w7:omega0`, complex `ξ`). -/
def aaOmega0 (ξ : Fin 2 → ℂ) (i : Fin 2) : ℂ :=
  (lamTan m hm i : ℂ) + ∑ i' : Fin 2, (actionA m hm i i' : ℂ) * ξ i'

/-- `Ω⁰_J(ξ) = λ_J + 3⟨b,ξ⟩/(2πλ_J)` (Definition `bpW:w7:omega0`, complex `ξ`). -/
def aaOmegaN0 (ξ : Fin 2 → ℂ) (J : ℕ+) : ℂ :=
  (lam m hm J : ℂ) + 3 / (2 * Real.pi * lam m hm J) * aaBdot m hm ξ

/-- `z_j \bar z_j` (actual coordinates, `z = (u + iv)/√2`). -/
def aaZZ (a p : ℝ) (w : KamPhase) (j : ℕ+) : ℂ := stepZ w j * stepZb w j / (homWt a p j : ℂ) ^ 2

/-- `N_ξ = ⟨ω⁰(ξ), y⟩ + Σ_j Ω⁰_{j+2}(ξ) z_j \bar z_j`, on its convergence carrier `0 ≤ a`,
`1/2 ≤ p` (the source weights are `a = p = 1`); the normal series converges absolutely there
(`summable_aaNfun`). -/
def aaNfun {a p : ℝ} (_ha : 0 ≤ a) (_hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase) : ℂ :=
  ∑ i : Fin 2, aaOmega0 m hm ξ i * w.2.1 i + ∑' j : ℕ+, aaOmegaN0 m hm ξ (j + 2) * aaZZ a p w j

/-- `Q̃ = ½⟨Ay, y⟩ + Σ_j 3⟨b,y⟩/(2πλ_{j+2}) z_j \bar z_j`, on its convergence carrier `0 ≤ a`,
`0 ≤ p` (the source weights are `a = p = 1`); the normal series converges absolutely there
(`summable_aaQt`). -/
def aaQt {a p : ℝ} (_ha : 0 ≤ a) (_hp : 0 ≤ p) (w : KamPhase) : ℂ :=
  1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) * (w.2.1 i * w.2.1 i') +
    ∑' j : ℕ+, 3 * aaBdot m hm w.2.1 / (2 * Real.pi * lam m hm (j + 2)) * aaZZ a p w j

section K

variable {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

open Classical in
/-- W3's `K` (defined on `B_{ρ₁}`), extended by `0`. -/
def aaKext (w' : BirkSpace) : ℂ :=
  if h : w' ∈ birkBall1 m p then birkK m hm ha hp ⟨w', h⟩ else 0

open Classical in
/-- W3's `X_K` (defined on `B_{ρ₁}`), extended by `0`. -/
def aaXKext (w' : BirkSpace) : BirkSpace :=
  if h : w' ∈ birkBall1 m p then birkXK m hm ha hp ⟨w', h⟩ else 0

theorem aaKext_isExtension : IsBirkExtension (birkK m hm ha hp) (aaKext m hm ha hp) := fun x => by
  simp [aaKext, x.2]

theorem aaXKext_isExtension : IsBirkExtension (birkXK m hm ha hp) (aaXKext m hm ha hp) :=
  fun x => by simp [aaXKext, x.2]

/-- `P_ξ = Q̃ + G^{nor} ∘ 𝒜_ξ + K ∘ 𝒜_ξ`. -/
def aaPfun (ξ : Fin 2 → ℂ) (w : KamPhase) : ℂ :=
  aaQt m hm ha (le_trans one_half_pos.le hp) w + birkHamNor m hm ha hp (aaMap a p ξ w) +
    aaKext m hm ha hp (aaMap a p ξ w)

end K

variable {m hm}

/-! ### Real parameters -/

theorem lamTan_eq_lam (i : Fin 2) : lamTan m hm i = lam m hm (modeIdx i) := rfl

theorem aaOmega0_ofReal (ξ : Fin 2 → ℝ) (i : Fin 2) :
    aaOmega0 m hm (fun i => (ξ i : ℂ)) i = (waveFreqTan m hm ξ i : ℂ) := by
  simp [aaOmega0, waveFreqTan]

theorem aaBdot_ofReal (ξ : Fin 2 → ℝ) : aaBdot m hm (fun i => (ξ i : ℂ)) = (waveB m hm ξ : ℂ) := by
  simp only [aaBdot, waveB]
  push_cast
  rfl

theorem aaOmegaN0_ofReal (ξ : Fin 2 → ℝ) (j : ℕ+) :
    aaOmegaN0 m hm (fun i => (ξ i : ℂ)) (j + 2) = (waveFreqNor m hm ξ j : ℂ) := by
  simp only [aaOmegaN0, aaBdot_ofReal, waveFreqNor, waveOmega]
  push_cast
  rfl

/-! ### The actions of `𝒜_ξ(w)` -/

theorem aa_one_le_lam (j : ℕ+) : 1 ≤ lam m hm j := by
  have h := one_le_lam_div_pnat hm j
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hj0 : (0 : ℝ) < j := by linarith
  rw [le_div_iff₀ hj0, one_mul] at h
  linarith

theorem stepZ_apply' (w : KamPhase) (j : ℕ+) :
    stepZ w j = (w.2.2.1 j + I * w.2.2.2 j) / birkSqrt2 := by
  obtain ⟨θ, y, u, v⟩ := w
  rw [stepZ_apply, div_eq_inv_mul]
  rfl

theorem stepZb_apply' (w : KamPhase) (j : ℕ+) :
    stepZb w j = (w.2.2.1 j - I * w.2.2.2 j) / birkSqrt2 := by
  obtain ⟨θ, y, u, v⟩ := w
  rw [stepZb_apply, div_eq_inv_mul]
  rfl

theorem birkAction_aaMap_tan (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) :
    birkAction a p (aaMap a p ξ w) (modeIdx i) = ξ i + w.2.1 i := by
  unfold birkAction
  rw [birkCoord_aaMap_tan, birkCoord_aaMap_tan, aaTanCoord_eq, aaTanCoord_eq]
  have hE := aaE_mul w i
  have hS := aaS_mul_self ξ w i
  linear_combination (aaS ξ w i * aaS ξ w i) * hE + hS

theorem birkAction_aaMap_nor (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (j : ℕ+) :
    birkAction a p (aaMap a p ξ w) (j + 2) = aaZZ a p w j := by
  unfold birkAction aaZZ
  simp only [birkCoord, aaMap_nor_true, aaMap_nor_false, stepZ_apply', stepZb_apply']
  have h : (RCLike.ofReal (ellWeight a p (j + 2)) : ℂ) = (homWt a p j : ℂ) := rfl
  rw [h]
  ring

/-! ### Summability of the normal sums -/

theorem norm_lam_aaZZ_le (a p : ℝ) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase)
    (j : ℕ+) :
    ‖(lam m hm (j + 2) : ℂ) * aaZZ a p w j‖ ≤ Real.sqrt (1 + m) *
      (‖aaMap a p ξ w (true, j + 2)‖ * ‖aaMap a p ξ w (false, j + 2)‖) := by
  have h := norm_birkLamTerm_le m hm ha hp (aaMap a p ξ w) (aaMap a p ξ w) (j + 2)
  rw [← birkAction_aaMap_nor a p ξ w j, birkAction, ← mul_assoc]
  rw [birk_lam_mul_coord]
  exact h

theorem summable_norm_lam_aaZZ (a p : ℝ) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (w : KamPhase) :
    Summable fun j : ℕ+ => ‖(lam m hm (j + 2) : ℂ) * aaZZ a p w j‖ := by
  have hs := ((birkHalf_summable (aaMap a p 0 w) (aaMap a p 0 w)).1.mul_left
    (Real.sqrt (1 + m))).comp_injective aaIdx_injective
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_lam_aaZZ_le a p ha hp 0 w j) hs

/-- A normal sum `Σ_j c_j z_j \bar z_j` with `|c_j| ≤ C λ_{j+2}` converges absolutely. -/
theorem summable_coef_aaZZ (a p : ℝ) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (w : KamPhase)
    {c : ℕ+ → ℂ} {C : ℝ} (hc : ∀ j, ‖c j‖ ≤ C * lam m hm (j + 2)) :
    Summable fun j : ℕ+ => c j * aaZZ a p w j := by
  refine Summable.of_norm_bounded ((summable_norm_lam_aaZZ (m := m) (hm := hm) a p ha hp w).mul_left
    C) (fun j => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lam_pnat_pos hm (j + 2)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)

theorem norm_three_div_le (J : ℕ+) : ‖(3 / (2 * Real.pi * lam m hm J) : ℂ)‖ ≤ 1 * lam m hm J := by
  have hl := aa_one_le_lam (m := m) (hm := hm) J
  have hpi := Real.pi_gt_three
  have hpos : 0 < 2 * Real.pi * lam m hm J := by positivity
  rw [show (3 / (2 * Real.pi * lam m hm J) : ℂ) = ((3 / (2 * Real.pi * lam m hm J) : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_le_iff₀ hpos]
  nlinarith

/-- `‖Ω⁰_J(ξ)‖ ≤ (1 + ‖⟨b,ξ⟩‖) λ_J`. -/
theorem norm_aaOmegaN0_le (ξ : Fin 2 → ℂ) (J : ℕ+) :
    ‖aaOmegaN0 m hm ξ J‖ ≤ (1 + ‖aaBdot m hm ξ‖) * lam m hm J := by
  have hl := (lam_pnat_pos hm J).le
  have h3 := norm_three_div_le (m := m) (hm := hm) J
  unfold aaOmegaN0
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (aaBdot m hm ξ))
  linarith

/-- (`bpW:w5:action-angle` (iv), well-definedness of `N_ξ`) On the carrier `0 ≤ a`, `1/2 ≤ p` of
`aaNfun`, its normal series `Σ_j Ω⁰_{j+2}(ξ) z_j \bar z_j` converges absolutely. -/
theorem summable_aaNfun {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase) :
    Summable fun j : ℕ+ => aaOmegaN0 m hm ξ (j + 2) * aaZZ a p w j :=
  summable_coef_aaZZ a p ha hp w fun j => norm_aaOmegaN0_le ξ (j + 2)

/-! ### The normal form -/

theorem tsum_ite_three (F : ℕ+ → ℂ) :
    ∑' J : ℕ+, (if 3 ≤ (J : ℕ) then F J else 0) = ∑' j : ℕ+, F (j + 2) := by
  have h3 : ∀ j : ℕ+, 3 ≤ ((j + 2 : ℕ+) : ℕ) := fun j => by
    rw [PNat.add_coe]; simp; exact j.pos
  have := Function.Injective.tsum_eq aaIdx_injective
    (f := fun J : ℕ+ => if 3 ≤ (J : ℕ) then F J else 0) (fun J hJ => by
      by_cases h : 3 ≤ (J : ℕ)
      · exact ⟨Nat.toPNat ((J : ℕ) - 2) (by omega), pnat_sub_two_add_two J h⟩
      · exact absurd (by simp [h]) hJ)
  rw [← this]
  exact tsum_congr fun j => by simp only [h3 j, ite_true]

theorem actionA_symm (i i' : Fin 2) : actionA m hm i i' = actionA m hm i' i := by
  unfold actionA
  by_cases h : i = i'
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]; ring

/-- **The normal form** (`bpW:w5:action-angle` (iv)): where `𝒜_ξ(w) ∈ B_{ρ₁}`,
`(Λ + Ḡ + G^{nor} + K)(𝒜_ξ w) = e(ξ) + N_ξ(w) + P_ξ(w)`. -/
theorem aaMap_normalForm {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase)
    (h : aaMap a p ξ w ∈ birkBall1 m p) :
    birkLambda m hm ha hp (aaMap a p ξ w) + birkHamBar m hm ha hp (aaMap a p ξ w) +
        birkHamNor m hm ha hp (aaMap a p ξ w) + birkK m hm ha hp ⟨aaMap a p ξ w, h⟩ =
      aaEnergy m hm ξ + aaNfun m hm ha hp ξ w + aaPfun m hm ha hp ξ w := by
  -- the two base sums
  set T := ∑' j : ℕ+, (lam m hm (j + 2) : ℂ) * aaZZ a p w j with hT
  set S := ∑' j : ℕ+, (3 / (2 * Real.pi * lam m hm (j + 2)) : ℂ) * aaZZ a p w j with hS
  have hsT : Summable fun j : ℕ+ => (lam m hm (j + 2) : ℂ) * aaZZ a p w j :=
    summable_coef_aaZZ a p ha hp w (C := 1) fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lam_pnat_pos hm _), one_mul]
  have hsS : Summable fun j : ℕ+ => (3 / (2 * Real.pi * lam m hm (j + 2)) : ℂ) * aaZZ a p w j :=
    summable_coef_aaZZ a p ha hp w (C := 1) fun j => norm_three_div_le _
  -- `Λ`
  have hΛ : birkLambda m hm ha hp (aaMap a p ξ w) =
      (lam m hm 1 : ℂ) * (ξ 0 + w.2.1 0) + (lam m hm 2 : ℂ) * (ξ 1 + w.2.1 1) + T := by
    rw [birkLambda_eq]
    have hterm : ∀ J : ℕ+, (lam m hm J : ℂ) * birkCoord a p (aaMap a p ξ w) (true, J) *
        birkCoord a p (aaMap a p ξ w) (false, J) =
          (lam m hm J : ℂ) * birkAction a p (aaMap a p ξ w) J := fun J => by
      rw [birkAction, mul_assoc]
    simp_rw [hterm]
    have hsum : Summable fun J : ℕ+ => (lam m hm J : ℂ) * birkAction a p (aaMap a p ξ w) J := by
      have := summable_birkLamTerm m hm ha hp (aaMap a p ξ w) (aaMap a p ξ w)
      refine this.congr fun J => ?_
      rw [birkLamTerm, ← birk_lam_mul_coord, birkAction, mul_assoc]
    rw [(aa_hasSum_pnat _ hsum).tsum_eq]
    have e1 : birkAction a p (aaMap a p ξ w) 1 = ξ 0 + w.2.1 0 := birkAction_aaMap_tan a p ξ w 0
    have e2 : birkAction a p (aaMap a p ξ w) 2 = ξ 1 + w.2.1 1 := birkAction_aaMap_tan a p ξ w 1
    rw [e1, e2, hT]
    congr 1
    exact tsum_congr fun j => by rw [birkAction_aaMap_nor]
  -- `Ḡ`
  have hG : birkHamBar m hm ha hp (aaMap a p ξ w) =
      1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        ((ξ i + w.2.1 i) * (ξ i' + w.2.1 i')) +
      ∑ i : Fin 2, (ξ i + w.2.1 i) / (lamTan m hm i : ℂ) * S := by
    rw [birkHamBar, birkQuartP_bar]
    congr 1
    · simp only [birkAction_aaMap_tan]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [tsum_ite_three, hS, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [birkAction_aaMap_tan, birkAction_aaMap_nor, birkActionB]
      have hl := (lam_pnat_pos hm (j + 2)).ne'
      have hli := (lam_pnat_pos hm (modeIdx i)).ne'
      have hpi := Real.pi_ne_zero
      rw [lamTan_eq_lam]
      push_cast
      field_simp
  -- `N_ξ` and `Q̃`
  have hN : aaNfun m hm ha hp ξ w = ∑ i : Fin 2, aaOmega0 m hm ξ i * w.2.1 i +
      (T + aaBdot m hm ξ * S) := by
    unfold aaNfun aaOmegaN0
    congr 1
    rw [hT, hS, ← tsum_mul_left, ← hsT.tsum_add (hsS.mul_left _)]
    exact tsum_congr fun j => by ring
  have hQ : aaQt m hm ha (le_trans one_half_pos.le hp) w =
      1 / 2 * ∑ i : Fin 2, ∑ i' : Fin 2, (actionA m hm i i' : ℂ) *
        (w.2.1 i * w.2.1 i') + aaBdot m hm w.2.1 * S := by
    unfold aaQt
    congr 1
    rw [hS, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hK : aaKext m hm ha hp (aaMap a p ξ w) = birkK m hm ha hp ⟨aaMap a p ξ w, h⟩ := by
    simp [aaKext, h]
  unfold aaPfun
  rw [hΛ, hG, hN, hQ, hK]
  simp only [aaEnergy, aaOmega0, aaBdot, Fin.sum_univ_two, lamTan_eq_lam]
  have h0 : modeIdx (0 : Fin 2) = 1 := rfl
  have h1 : modeIdx (1 : Fin 2) = 2 := rfl
  rw [h0, h1, actionA_symm 1 0]
  ring

end KAM.Wave

end
