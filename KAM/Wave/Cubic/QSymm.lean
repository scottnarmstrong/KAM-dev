/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.QPair
public import KAM.Wave.Cubic.ReconComplex
public import KAM.Wave.Cubic.CubicDeriv

/-!
# Full symmetry of the quartic form `𝒬` (blueprint `bpW:w1:gradient-identity` (i))

The coefficient `c_{ijkl}` is symmetric under `k ↔ l` (`waveTriCoef_comm34`). The quadruple series
`Σ_{ijkl} c_{ijkl} q_i q'_j q''_k q'''_l` converges absolutely (`waveTri_quad_summable`; the
absolute values of the inner sums are the real `T` of the moduli, bounded by `waveTri_oneSided`),
so `⟨T(q,q',q''), q'''⟩₀ = ⟨T(q,q',q'''), q''⟩₀` (`waveTri_pairing_swap`). With the symmetry of `𝒯`
in its first three slots this gives symmetry of `𝒬` under every permutation of the four slots
(`waveQuartForm_perm`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ}

lemma waveQuartic_comm34 (i j k l : ℕ+) : waveQuartic i j k l = waveQuartic i j l k := by
  unfold waveQuartic
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

lemma waveTriCoef_comm34 (i j k l : ℕ+) : waveTriCoef m hm i j k l = waveTriCoef m hm i j l k := by
  unfold waveTriCoef
  rw [waveQuartic_comm34 i j k l]
  ring

/-- The quadruple term `c_{ijkl} q_i q'_j q''_k q'''_l`, indexed by `(l, (i, j, k))`. -/
def waveQuadTerm (q₁ q₂ q₃ q₄ : ℕ+ → K) (x : ℕ+ × ℕ+ × ℕ+ × ℕ+) : K :=
  (waveTriCoef m hm x.2.1 x.2.2.1 x.2.2.2 x.1 : K) *
    (q₁ x.2.1 * (q₂ x.2.2.1 * (q₃ x.2.2.2 * q₄ x.1)))

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- Absolute convergence of the quadruple series. -/
theorem waveTri_quad_summable {q₁ q₂ q₃ q₄ : ℕ+ → K} (h₁ : IsEll a p q₁) (h₂ : IsEll a p q₂)
    (h₃ : IsEll a p q₃) (h₄ : IsEll a p q₄) :
    Summable fun x => ‖waveQuadTerm m hm q₁ q₂ q₃ q₄ x‖ := by
  have hp0 : 0 ≤ p := by linarith
  -- the moduli of the inner sums, as a real trilinear sum
  set c' : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℝ := fun i j k l => |waveTriCoef m hm i j k l| with hc'
  have hc'b : ∀ i j k l : ℕ+, ‖c' i j k l‖ ≤ (1 / (2 * Real.pi)) *
      (((i : ℝ) * j * k * l) ^ (-(1 / 2 : ℝ))) * waveSelCount l (i, j, k) := fun i j k l => by
    have := waveTriCoef_bound (K := ℝ) m hm i j k l
    simpa [hc', RCLike.norm_ofReal] using this
  have hr := waveSel_oneSided (K := ℝ) ha hp (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)) hc'b
    (waveEll_iff_isEll a p _ |>.1 (waveEllK_real_norm h₁))
    (waveEll_iff_isEll a p _ |>.1 (waveEllK_real_norm h₂))
    (waveEll_iff_isEll a p _ |>.1 (waveEllK_real_norm h₃))
  set r : ℕ+ → ℝ := waveSelSum c' (fun j => ‖q₁ j‖) (fun j => ‖q₂ j‖) (fun j => ‖q₃ j‖) with hr_def
  have hrt : ∀ l, r l = ∑' t : ℕ+ × ℕ+ × ℕ+,
      ‖(waveTriCoef m hm t.1 t.2.1 t.2.2 l : K) * (q₁ t.1 * (q₂ t.2.1 * q₃ t.2.2))‖ := by
    intro l
    simp only [hr_def, waveSelSum, hc']
    refine tsum_congr fun t => ?_
    simp [norm_mul]
  have hr0 : ∀ l, 0 ≤ r l := fun l => by rw [hrt]; exact tsum_nonneg fun _ => norm_nonneg _
  have hrs : Summable fun l => (ellWeight a (p + 1) l * r l) ^ 2 := by
    have := (wave_isEll_iff_summable a (p + 1) r).1 hr.2.1
    simpa [Real.norm_eq_abs, abs_of_nonneg (hr0 _)] using this
  have h4s := (wave_isEll_iff_summable a p q₄).1 h₄
  have hprod : Summable fun l => r l * ‖q₄ l‖ := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hr0 l) (norm_nonneg _)) (fun l => ?_)
      ((hrs.add h4s).mul_left (1 / 2))
    have w1 := one_le_ellWeight ha (by linarith : 0 ≤ p + 1) l
    have w2 := one_le_ellWeight ha hp0 l
    have h1 : r l ≤ ellWeight a (p + 1) l * r l := le_mul_of_one_le_left (hr0 l) w1
    have h2 : ‖q₄ l‖ ≤ ellWeight a p l * ‖q₄ l‖ := le_mul_of_one_le_left (norm_nonneg _) w2
    nlinarith [sq_nonneg (ellWeight a (p + 1) l * r l - ellWeight a p l * ‖q₄ l‖),
      mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (by linarith) (hr0 l))]
  rw [summable_prod_of_nonneg (fun x => norm_nonneg _)]
  have hterm : ∀ (l : ℕ+) (t : ℕ+ × ℕ+ × ℕ+), ‖waveQuadTerm m hm q₁ q₂ q₃ q₄ (l, t)‖ =
      ‖(waveTriCoef m hm t.1 t.2.1 t.2.2 l : K) * (q₁ t.1 * (q₂ t.2.1 * q₃ t.2.2))‖ *
        ‖q₄ l‖ := by
    intro l t
    simp only [waveQuadTerm, ← norm_mul]
    congr 1; ring
  refine ⟨fun l => ?_, ?_⟩
  · simp only [hterm]
    exact ((waveTri_oneSided m hm ha hp h₁ h₂ h₃).1 l).mul_right _
  · simp only [hterm]
    simp only [tsum_mul_right, ← hrt]
    exact hprod

include ha hp in
theorem waveTri_pairing_eq_quad {q₁ q₂ q₃ q₄ : ℕ+ → K} (h₁ : IsEll a p q₁) (h₂ : IsEll a p q₂)
    (h₃ : IsEll a p q₃) (h₄ : IsEll a p q₄) :
    ∑' l, waveTriSeq m hm q₁ q₂ q₃ l * q₄ l = ∑' x, waveQuadTerm m hm q₁ q₂ q₃ q₄ x := by
  rw [(waveTri_quad_summable m hm ha hp h₁ h₂ h₃ h₄).of_norm.tsum_prod]
  refine tsum_congr fun l => ?_
  have : ∀ t : ℕ+ × ℕ+ × ℕ+, waveQuadTerm m hm q₁ q₂ q₃ q₄ (l, t) =
      (waveTriCoef m hm t.1 t.2.1 t.2.2 l : K) * (q₁ t.1 * (q₂ t.2.1 * q₃ t.2.2)) * q₄ l :=
    fun t => by simp only [waveQuadTerm]; ring
  simp only [this, tsum_mul_right]
  rfl

include ha hp in
/-- `⟨T(q,q',q''), q'''⟩₀ = ⟨T(q,q',q'''), q''⟩₀`. -/
theorem waveTri_pairing_swap {q₁ q₂ q₃ q₄ : ℕ+ → K} (h₁ : IsEll a p q₁) (h₂ : IsEll a p q₂)
    (h₃ : IsEll a p q₃) (h₄ : IsEll a p q₄) :
    ∑' l, waveTriSeq m hm q₁ q₂ q₃ l * q₄ l = ∑' l, waveTriSeq m hm q₁ q₂ q₄ l * q₃ l := by
  rw [waveTri_pairing_eq_quad m hm ha hp h₁ h₂ h₃ h₄,
    waveTri_pairing_eq_quad m hm ha hp h₁ h₂ h₄ h₃]
  let e : ℕ+ × ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1)
      invFun := fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1)
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun x => ?_
  simp only [waveQuadTerm, e, Equiv.coe_fn_mk]
  rw [waveTriCoef_comm34 m hm x.2.1 x.2.2.1 x.2.2.2 x.1]
  ring

/-- Swap of the last two slots of `𝒬`. -/
theorem waveQuartForm_swap34 (y₁ y₂ y₃ y₄ : lp (fun _ : ℕ+ => K) 2) :
    waveQuartForm (K := K) m hm ha hp ![y₁, y₂, y₃, y₄] =
      waveQuartForm (K := K) m hm ha hp ![y₁, y₂, y₄, y₃] := by
  rw [waveQuartForm_apply, waveQuartForm_apply]
  exact waveTri_pairing_swap m hm ha hp (isEll_coeffW a p y₁) (isEll_coeffW a p y₂)
    (isEll_coeffW a p y₃) (isEll_coeffW a p y₄)

include ha hp in
lemma waveQuartForm_vec4 (y₁ y₂ y₃ y₄ : lp (fun _ : ℕ+ => K) 2) :
    waveQuartForm (K := K) m hm ha hp ![y₁, y₂, y₃, y₄] =
      wavePair a p (waveTriML (K := K) m hm ha hp ![y₁, y₂, y₃]) y₄ := by
  rw [waveQuartForm_apply_vec]
  rfl

include ha hp in
/-- `bpW:w1:gradient-identity` (i): `𝒬` is symmetric under every permutation of its four slots. -/
theorem waveQuartForm_perm (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → lp (fun _ : ℕ+ => K) 2) :
    waveQuartForm (K := K) m hm ha hp (fun i => v (σ i)) = waveQuartForm (K := K) m hm ha hp v := by
  let S : Submonoid (Equiv.Perm (Fin 4)) :=
    { carrier := {σ | ∀ v : Fin 4 → lp (fun _ : ℕ+ => K) 2,
        waveQuartForm (K := K) m hm ha hp (fun i => v (σ i)) =
          waveQuartForm (K := K) m hm ha hp v}
      mul_mem' := fun {σ τ} hσ hτ v => by
        have := hτ (fun i => v (σ i))
        have h2 := hσ v
        simpa [Equiv.Perm.coe_mul, Function.comp_def] using this.trans h2
      one_mem' := fun v => rfl }
  have hvec : ∀ w : Fin 4 → lp (fun _ : ℕ+ => K) 2, w = ![w 0, w 1, w 2, w 3] := fun w => by
    ext i; fin_cases i <;> rfl
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ 3, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩ v
    show waveQuartForm (K := K) m hm ha hp (fun k => v (Equiv.swap i.castSucc i.succ k)) = _
    rw [hvec v]
    fin_cases i
    · have e : (fun k => ![v 0, v 1, v 2, v 3] (Equiv.swap (Fin.castSucc (0 : Fin 3))
          (Fin.succ (0 : Fin 3)) k)) = ![v 1, v 0, v 2, v 3] := by
        ext k; fin_cases k <;> simp [Equiv.swap_apply_def]
      refine (congrArg (waveQuartForm (K := K) m hm ha hp) e).trans ?_
      rw [waveQuartForm_vec4 m hm ha hp, waveQuartForm_vec4 m hm ha hp]
      rw [waveTriML_swap_left_mid (K := K) m hm ha hp (v 1) (v 0) (v 2)]
    · have e : (fun k => ![v 0, v 1, v 2, v 3] (Equiv.swap (Fin.castSucc (1 : Fin 3))
          (Fin.succ (1 : Fin 3)) k)) = ![v 0, v 2, v 1, v 3] := by
        ext k; fin_cases k <;> simp [Equiv.swap_apply_def]
      refine (congrArg (waveQuartForm (K := K) m hm ha hp) e).trans ?_
      rw [waveQuartForm_vec4 m hm ha hp, waveQuartForm_vec4 m hm ha hp]
      rw [waveTriML_swap_mid_right (K := K) m hm ha hp (v 0) (v 2) (v 1)]
    · have e : (fun k => ![v 0, v 1, v 2, v 3] (Equiv.swap (Fin.castSucc (2 : Fin 3))
          (Fin.succ (2 : Fin 3)) k)) = ![v 0, v 1, v 3, v 2] := by
        ext k; fin_cases k <;> simp [Equiv.swap_apply_def]
      refine (congrArg (waveQuartForm (K := K) m hm ha hp) e).trans ?_
      exact (waveQuartForm_swap34 m hm ha hp (v 0) (v 1) (v 2) (v 3)).symm
  exact (hS ▸ Submonoid.mem_top σ : σ ∈ S) v

end KAM.Wave

end
