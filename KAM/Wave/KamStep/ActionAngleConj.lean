/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngleField
public import KAM.Wave.KamStep.ActionAngleGbar
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The conjugacy identity (blueprint-W `bpW:w5:action-angle` (v), step `a-conj`)

Blueprint label `bpW:w5:action-angle` (v), step `a-conj`.

* `aaXN ξ w`: the field `X_{N_ξ}(w) = (ω⁰(ξ)/(2π), 0, Ω⁰ v, -Ω⁰ u)` of `N_ξ`, in
  `(p-1)`-representatives (the normal multiplier is `Ω⁰_{j+2}(ξ) ω_{a,p-1}(j+2)/ω_{a,p}(j+2) =
  Ω⁰_{j+2}(ξ)/(j+2)`, `aaXNcoef`);
* **`aaConjugacy`**: where `𝒜_ξ` is defined and `𝒜_ξ(w) ∈ B_{ρ₁}`,
  `X_{H'}(𝒜_ξ w) = D𝒜_ξ(w)(X_{N_ξ}(w) + X_{P_ξ}(w))` in `𝔚^{p-1}`, with
  `X_{H'} = X_Λ + X_Ḡ + X_{G^{nor}} + X_K` (`X_Λ(w')_l = -iλ'_l w'_l` on all of `𝔚`: W3's `birkXLam`
  read from weight `p` to weight `p-1`; the smoothing fields enter through `ι : 𝔚^{p+1} → 𝔚^{p-1}`,
  `X_{P_ξ}` through `ι : 𝒫^{p+1} → 𝒫^{p-1}`).

The proof compares the actual coordinates at every `l ∈ ℤ ∖ {0}` (the coordinate formulas of
`X_Ḡ` from `ActionAngleGbar`, `D𝒜 D𝒜⁻¹ = id`), instead of the blueprint's route through derivatives
and nondegeneracy of `Ω`; the identity proved is the same.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

variable (m : ℝ) (hm : 0 < m)

/-- `Ω⁰_{j+2}(ξ)/(j+2)`. -/
def aaXNcoef (ξ : Fin 2 → ℂ) (j : ℕ+) : ℂ := aaOmegaN0 m hm ξ (j + 2) * ((j : ℂ) + 2)⁻¹

variable {m hm}

theorem norm_aaXNcoef_le (ξ : Fin 2 → ℂ) (j : ℕ+) :
    ‖aaXNcoef m hm ξ j‖ ≤ Real.sqrt (1 + m) + ‖aaBdot m hm ξ‖ := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hJ : (3 : ℝ) ≤ (j : ℝ) + 2 := by linarith
  have hJ' : (((j + 2 : ℕ+) : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  have hl := aa_one_le_lam (m := m) (hm := hm) (j + 2)
  have hpi := Real.pi_pos
  have hlam : lam m hm (j + 2) ≤ Real.sqrt (1 + m) * ((j : ℝ) + 2) := by
    unfold lam
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (j : ℝ) + 2), ← Real.sqrt_mul (by linarith),
      hJ']
    have hJ2 : (1 : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by nlinarith
    exact Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hJ2 hm.le])
  unfold aaXNcoef aaOmegaN0
  rw [norm_mul, norm_inv, show ((j : ℂ) + 2) = (((j : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [mul_inv_le_iff₀ (by linarith)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lam_pnat_pos hm _)]
  have h3 : ‖(3 / (2 * Real.pi * lam m hm (j + 2)) : ℂ)‖ ≤ 1 := by
    have hpi3 := Real.pi_gt_three
    rw [show (3 / (2 * Real.pi * lam m hm (j + 2)) : ℂ) =
      ((3 / (2 * Real.pi * lam m hm (j + 2)) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith
  have hb := norm_nonneg (aaBdot m hm ξ)
  nlinarith [mul_le_mul_of_nonneg_right h3 hb]

variable (m hm)

/-- The diagonal operator `v ↦ (Ω⁰_{j+2}(ξ) v_j/(j+2))_j` (`p`- to `(p-1)`-representatives). -/
def aaXNdiag (ξ : Fin 2 → ℂ) : HomOp := weightedDiagCLM (aaXNcoef m hm ξ) (norm_aaXNcoef_le ξ)

/-- **The field `X_{N_ξ}(w) = (ω⁰(ξ)/(2π), 0, Ω⁰ v, -Ω⁰ u)`** in `(p-1)`-representatives. -/
def aaXN (ξ : Fin 2 → ℂ) (w : KamPhase) : KamPhase :=
  (fun i => (2 * Real.pi : ℂ)⁻¹ * aaOmega0 m hm ξ i, 0, aaXNdiag m hm ξ w.2.2.2,
    -aaXNdiag m hm ξ w.2.2.1)

variable {m hm}

/-! ### Coordinate lemmas -/

theorem birkSpace_ext_coord (a q : ℝ) {y y' : BirkSpace}
    (h : ∀ l, birkCoord a q y l = birkCoord a q y' l) : y = y' := by
  ext l
  have := h l
  simp only [birkCoord] at this
  exact (div_left_inj' (ellWeight_cast_ne_zero (K := ℂ) a q l.2)).1 this

theorem aaDerTanL_kamHomEmbed (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) {a q q' : ℝ}
    (h : q ≤ q') (W : KamPhase) :
    aaDerTanL ξ w b i (kamHomEmbed a q q' h W) = aaDerTanL ξ w b i W := by
  rw [aaDerTanL_apply, aaDerTanL_apply, kamHomEmbed_apply]

theorem aaDerTanL_aaDerInv (a q : ℝ) {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) (V : BirkSpace) (b : Bool) (i : Fin 2) :
    aaDerTanL ξ w b i (aaDerInv a q ξ w V) = birkCoord a q V (b, modeIdx i) := by
  have h := congrArg (fun y : BirkSpace => birkCoord a q y (b, modeIdx i)) (aaDer_aaDerInv a q hw V)
  rw [birkCoord_aaDer_tan] at h
  exact h

theorem aaGbarR_aaMap (a p : ℝ) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) (w : KamPhase)
    (i : Fin 2) :
    aaGbarR m hm ha hp (aaMap a p ξ w) i =
      aaSfun m hm ha (le_trans one_half_pos.le hp) w / (lamTan m hm i : ℂ) := by
  unfold aaGbarR
  rw [tsum_ite_three, ← aaSfun_eq ha (le_trans one_half_pos.le hp), div_eq_mul_inv,
    ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [birkAction_aaMap_nor, birkActionB, aaCoefC, lamTan_eq]
  have hl := (lam_pnat_pos hm (j + 2)).ne'
  have hli := (lam_pnat_pos hm (modeIdx i)).ne'
  have hpi := Real.pi_ne_zero
  push_cast
  field_simp

/-! ### The conjugacy identity -/

/-- **Conjugacy** (`bpW:w5:action-angle` (v)): `X_{H'}(𝒜_ξ w) = D𝒜_ξ(w)(X_{N_ξ}(w) + X_{P_ξ}(w))`
in `𝔚^{p-1}`, for `w` in the domain of `𝒜_ξ` with `𝒜_ξ(w) ∈ B_{ρ₁}`. -/
theorem aaConjugacy {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (ξ : Fin 2 → ℂ) {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) (hB : aaMap a p ξ w ∈ birkBall1 m p) :
    birkXLam m hm (aaMap a p ξ w) + birkEmbed a (p + 1) (p - 1) (by linarith)
        (birkHamBarX m hm ha hp (aaMap a p ξ w) + birkHamNorX m hm ha hp (aaMap a p ξ w) +
          birkXK m hm ha hp ⟨aaMap a p ξ w, hB⟩) =
      aaDer a (p - 1) ξ w (aaXN m hm ξ w +
        kamHomEmbed a (p - 1) (p + 1) (by linarith) (aaXP m hm ha hp ξ w)) := by
  have hp0 : 0 ≤ p := by linarith
  have hK : birkXK m hm ha hp ⟨aaMap a p ξ w, hB⟩ = aaXKext m hm ha hp (aaMap a p ξ w) := by
    simp [aaXKext, hB]
  rw [hK]
  set V := birkHamNorX m hm ha hp (aaMap a p ξ w) + aaXKext m hm ha hp (aaMap a p ξ w) with hV
  have hpp : p - 1 + 1 = p := by ring
  refine birkSpace_ext_coord a (p - 1) fun l => ?_
  obtain ⟨b, J⟩ := l
  rw [birkCoord_add, birkCoord_birkXLam, hpp, birkCoord_birkEmbed, add_assoc
    (birkHamBarX m hm ha hp (aaMap a p ξ w)), birkCoord_add, ← hV]
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · -- tangential coordinates
    rw [birkCoord_aaDer_tan, map_add (aaDerTanL ξ w b i), aaDerTanL_kamHomEmbed, aaXP,
      map_add (aaDerTanL ξ w b i), aaDerTanL_aaDerInv a (p + 1) hw, birkCoord_birkHamBarX_tan,
      aaGbarR_aaMap a p ha hp]
    simp only [aaDerTanL_apply, aaXN, aaXQt, Pi.zero_apply,
      zero_div, birkCoord_aaMap_tan, aaTanCoord_eq]
    have hI : ∀ i', birkAction a p (aaMap a p ξ w) (modeIdx i') = ξ i' + w.2.1 i' := fun i' =>
      birkAction_aaMap_tan a p ξ w i'
    simp_rw [hI]
    unfold aaOmega0
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
    rw [lamTan_eq]
    field_simp
    simp only [Fin.sum_univ_two]
    ring
  · -- normal coordinates
    have hsucc : ((homWt a p j : ℝ) : ℂ) = ((j : ℂ) + 2) * (homWt a (p - 1) j : ℂ) := by
      have := homWt_succ_eq a (p - 1) j
      rw [hpp] at this
      rw [this]; push_cast; ring
    have hsucc2 : ((homWt a (p + 1) j : ℝ) : ℂ) = ((j : ℂ) + 2) * (homWt a p j : ℂ) := by
      rw [homWt_succ_eq a p j]; push_cast; ring
    have hcoordp : ∀ bb : Bool, birkCoord a p (aaMap a p ξ w) (bb, j + 2) =
        aaMap a p ξ w (bb, j + 2) / (homWt a p j : ℂ) := fun bb => rfl
    have hcoordV : ∀ bb : Bool, birkCoord a (p + 1) V (bb, j + 2) =
        V (bb, j + 2) / (homWt a (p + 1) j : ℂ) := fun bb => rfl
    have hI : ∀ i', birkAction a p (aaMap a p ξ w) (modeIdx i') = ξ i' + w.2.1 i' := fun i' =>
      birkAction_aaMap_tan a p ξ w i'
    rw [birkCoord_birkHamBarX_nor, hcoordV]
    simp only [hI]
    set κ : ℂ := ((homWt a (p - 1) j / homWt a (p + 1) j : ℝ) : ℂ) with hκ
    set bd : ℂ := aaBdot m hm w.2.1 with hbd
    have hZU : (aaXN m hm ξ w + kamHomEmbed a (p - 1) (p + 1) (by linarith)
        (aaXP m hm ha hp ξ w)).2.2.1 j = aaXNcoef m hm ξ j * w.2.2.2 j +
          κ * (bd * aaCoefE m hm j * w.2.2.2 j +
            (V (true, j + 2) + V (false, j + 2)) / birkSqrt2) := by
      simp only [aaXN, aaXP, aaXQt, kamHomEmbed_apply, Prod.snd_add, Prod.fst_add, lp.coeFn_add,
        Pi.add_apply, homEmbed_gen, weightedDiagCLM_apply, aaXNdiag, aaDiagE, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul, homEmbedCoef_gen, map_add, ← hV, aaDerInv_u, ← hbd, ← hκ]
      ring
    have hZV : (aaXN m hm ξ w + kamHomEmbed a (p - 1) (p + 1) (by linarith)
        (aaXP m hm ha hp ξ w)).2.2.2 j = -(aaXNcoef m hm ξ j * w.2.2.1 j) +
          κ * (-(bd * aaCoefE m hm j * w.2.2.1 j) +
            (V (true, j + 2) - V (false, j + 2)) / (I * birkSqrt2)) := by
      simp only [aaXN, aaXP, aaXQt, kamHomEmbed_apply, Prod.snd_add, lp.coeFn_add,
        Pi.add_apply, homEmbed_gen, weightedDiagCLM_apply, aaXNdiag, aaDiagE, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul, homEmbedCoef_gen, map_add, ← hV, aaDerInv_v, ← hbd, ← hκ,
        lp.coeFn_neg, Pi.neg_apply, map_neg]
      ring
    have hκ' : κ = 1 / (((j : ℂ) + 2) * ((j : ℂ) + 2)) := by
      rw [hκ]
      have h0 : (homWt a (p - 1) j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos _ _ _).ne'
      have hj : ((j : ℂ) + 2) ≠ 0 := by
        have : (0 : ℝ) < (j : ℝ) + 2 := by positivity
        exact_mod_cast this.ne'
      push_cast
      rw [hsucc2, hsucc]
      field_simp
    have h0 : (homWt a (p - 1) j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (homWt_pos _ _ _).ne'
    have hj : ((j : ℂ) + 2) ≠ 0 := by
      have : (0 : ℝ) < (j : ℝ) + 2 := by positivity
      exact_mod_cast this.ne'
    have h2 := birkSqrt2_ne
    have hs2 := birkSqrt2_sq
    have hl : (lam m hm (j + 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (lam_pnat_pos hm _).ne'
    have hl0 : (lam m hm (modeIdx (0 : Fin 2)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (lam_pnat_pos hm _).ne'
    have hl1 : (lam m hm (modeIdx (1 : Fin 2)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (lam_pnat_pos hm _).ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    cases b
    · rw [birkCoord_aaDer_nor_false, hcoordp, aaMap_nor_false, hZU, hZV, hκ', hsucc2, hsucc]
      simp only [aaXNcoef, aaCoefE, aaCoefC, aaOmegaN0, birkSgn_false, birkActionB, hbd, aaBdot,
        Fin.sum_univ_two, lamTan_eq]
      push_cast
      field_simp
      ring_nf
      simp only [Complex.I_sq, hs2]
      ring
    · rw [birkCoord_aaDer_nor_true, hcoordp, aaMap_nor_true, hZU, hZV, hκ', hsucc2, hsucc]
      simp only [aaXNcoef, aaCoefE, aaCoefC, aaOmegaN0, birkSgn_true, birkActionB, hbd, aaBdot,
        Fin.sum_univ_two, lamTan_eq]
      push_cast
      field_simp
      ring_nf
      simp only [Complex.I_sq, hs2]
      ring

end KAM.Wave

end
