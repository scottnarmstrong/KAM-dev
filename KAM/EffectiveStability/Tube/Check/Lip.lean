/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.Deriv

/-!
# Mean-value bounds for tube observables on a box (T2-CONF, N5b)

The SR-7 method for the initial box `Q = closedBall z r` (sup norm): a bound
`|dG(x) v| ≤ L ‖v‖` for `G = f ∘ tubeChart V B` from sup bounds of the partials of `f` and `B` and
per-mode bounds of the rotated point `w = Vᵀx = (q, p)`:

* `|q_j| + |p_j| ≤ A_j`, `0 < a_j ≤ q_j² + p_j²`, `Σ_k |V_kj| ≤ N_V`;
* `|∂_{φ_b} B_l| ≤ β_l`, `|∂_{u_l} f| ≤ Fu_l`, `|∂_{φ_b} f| ≤ Fφ_b`.

Then `L = chartLip N_V A a β Fu Fφ = N_V (Σ_l Fu_l (A_l + β_l (Θ₀ + Θ₁)) + Σ_b Fφ_b Θ_b)` with
`Θ_b = A_b / a_b + A_2 / a_2` (`abs_fderiv_comp_tubeChart_le`), and on the ball
`|G x - G z| ≤ L r` (`abs_sub_le_of_closedBall`).

`modeBounds_of_mem_closedBall` supplies `A`, `a` on the ball from the centre:
`A_j = |q*_j| + |p*_j| + 2 N_V r`, `a_j = q*_j² + p*_j² - 2 (|q*_j| + |p*_j|) N_V r`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Set Filter Topology Matrix Real

/-- The angle weight `Θ_b = A_b / a_b + A_2 / a_2` (bound of `|dφ_b| / ‖dw‖`). -/
def thetaW (A a : Fin 3 → ℝ) (b : Fin 2) : ℝ := A b.castSucc / a b.castSucc + A 2 / a 2

/-- The Lipschitz constant of a tube observable on a set where the bounds hold. -/
def chartLip (Nv : ℝ) (A a β Fu : Fin 3 → ℝ) (Fφ : Fin 2 → ℝ) : ℝ :=
  Nv * (∑ l, Fu l * (A l + β l * (thetaW A a 0 + thetaW A a 1)) + ∑ b, Fφ b * thetaW A a b)

theorem abs_fst_apply_le {n : ℕ} (v : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) : |v.1 j| ≤ ‖v‖ := by
  have := (norm_le_pi_norm v.1 j).trans (norm_fst_le v)
  rwa [Real.norm_eq_abs] at this

theorem abs_snd_apply_le {n : ℕ} (v : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) : |v.2 j| ≤ ‖v‖ := by
  have := (norm_le_pi_norm v.2 j).trans (norm_snd_le v)
  rwa [Real.norm_eq_abs] at this

/-- `‖Vᵀ v‖ ≤ N_V ‖v‖` in the sup norm, with `N_V` a bound of the column sums of `|V|`. -/
theorem norm_rotMap_transpose_le {V : Matrix (Fin 3) (Fin 3) ℝ} {Nv : ℝ}
    (hN : ∀ j, ∑ k, |V k j| ≤ Nv) (v : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    ‖rotMap Vᵀ v‖ ≤ Nv * ‖v‖ := by
  have hc : ∀ u : Fin 3 → ℝ, ‖u‖ ≤ ‖v‖ → ‖Vᵀ *ᵥ u‖ ≤ Nv * ‖v‖ := by
    intro u hu
    have hN0 : 0 ≤ Nv := le_trans (Finset.sum_nonneg fun k _ => abs_nonneg (V k 0)) (hN 0)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have e : (Vᵀ *ᵥ u) j = ∑ k, V k j * u k := rfl
    rw [e]
    calc |∑ k, V k j * u k| ≤ ∑ k, |V k j * u k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |V k j| * ‖v‖ := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          have := (norm_le_pi_norm u k).trans hu
          rw [Real.norm_eq_abs] at this
          exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (∑ k, |V k j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ Nv * ‖v‖ := mul_le_mul_of_nonneg_right (hN j) (norm_nonneg _)
  rw [Prod.norm_def]
  exact max_le (hc _ (norm_fst_le v)) (hc _ (norm_snd_le v))

theorem abs_polarInvD_fst_le {w dw : (Fin 3 → ℝ) × (Fin 3 → ℝ)} {j : Fin 3} {A : ℝ}
    (hA : |w.1 j| + |w.2 j| ≤ A) : |(polarInvD w dw).1 j| ≤ A * ‖dw‖ := by
  have h1 := abs_fst_apply_le dw j
  have h2 := abs_snd_apply_le dw j
  show |w.1 j * dw.1 j + w.2 j * dw.2 j| ≤ _
  calc |w.1 j * dw.1 j + w.2 j * dw.2 j| ≤ |w.1 j| * |dw.1 j| + |w.2 j| * |dw.2 j| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (|w.1 j| + |w.2 j|) * ‖dw‖ := by
        nlinarith [abs_nonneg (w.1 j), abs_nonneg (w.2 j)]
    _ ≤ A * ‖dw‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)

theorem abs_polarInvD_snd_le {w dw : (Fin 3 → ℝ) × (Fin 3 → ℝ)} {j : Fin 3} {A a : ℝ}
    (hA : |w.1 j| + |w.2 j| ≤ A) (ha : 0 < a) (haw : a ≤ w.1 j ^ 2 + w.2 j ^ 2) :
    |(polarInvD w dw).2 j| ≤ A / a * ‖dw‖ := by
  have h1 := abs_fst_apply_le dw j
  have h2 := abs_snd_apply_le dw j
  have hN : 0 < w.1 j ^ 2 + w.2 j ^ 2 := ha.trans_le haw
  have hA0 : 0 ≤ A := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hA
  show |(w.1 j * dw.2 j - w.2 j * dw.1 j) / (w.1 j ^ 2 + w.2 j ^ 2)| ≤ _
  have hnum : |w.1 j * dw.2 j - w.2 j * dw.1 j| ≤ A * ‖dw‖ := by
    calc |w.1 j * dw.2 j - w.2 j * dw.1 j| ≤ |w.1 j| * |dw.2 j| + |w.2 j| * |dw.1 j| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ (|w.1 j| + |w.2 j|) * ‖dw‖ := by
          nlinarith [abs_nonneg (w.1 j), abs_nonneg (w.2 j)]
      _ ≤ A * ‖dw‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  rw [abs_div, abs_of_pos hN, div_mul_eq_mul_div]
  calc |w.1 j * dw.2 j - w.2 j * dw.1 j| / (w.1 j ^ 2 + w.2 j ^ 2)
      ≤ A * ‖dw‖ / (w.1 j ^ 2 + w.2 j ^ 2) := div_le_div_of_nonneg_right hnum hN.le
    _ ≤ A * ‖dw‖ / a := div_le_div_of_nonneg_left (by positivity) ha haw

theorem clm_fin2_apply (B' : (Fin 2 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (b : Fin 2 → ℝ) (l : Fin 3) :
    B' b l = b 0 * B' (Pi.single 0 1) l + b 1 * B' (Pi.single 1 1) l := by
  have hb : b = b 0 • (Pi.single 0 1 : Fin 2 → ℝ) + b 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hb]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem thetaW_nonneg {A a : Fin 3 → ℝ} (hA : ∀ j, 0 ≤ A j) (ha : ∀ j, 0 < a j) (b : Fin 2) :
    0 ≤ thetaW A a b := by
  unfold thetaW
  have := hA b.castSucc; have := ha b.castSucc; have := hA 2; have := ha 2
  positivity

/-- **The chain-rule bound** for `G = f ∘ tubeChart V B` at `x` with all rotated modes nonzero. -/
theorem abs_fderiv_comp_tubeChart_le {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    (hBper : ShiftPeriodic B) (hfper : ObsPeriodic f) {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : x ∈ modesPos V) (hf : DifferentiableAt ℝ f (tubeChart V B x))
    (hB : DifferentiableAt ℝ B (tubeChart V B x).2)
    {Nv : ℝ} {A a β Fu : Fin 3 → ℝ} {Fφ : Fin 2 → ℝ} (hN : ∀ j, ∑ k, |V k j| ≤ Nv)
    (hA : ∀ j, |(rotMap Vᵀ x).1 j| + |(rotMap Vᵀ x).2 j| ≤ A j) (ha : ∀ j, 0 < a j)
    (haw : ∀ j, a j ≤ modeSq V x j)
    (hβ : ∀ (b : Fin 2) (l : Fin 3), |fderiv ℝ B (tubeChart V B x).2 (Pi.single b 1) l| ≤ β l)
    (hFu : ∀ l, |fderiv ℝ f (tubeChart V B x) (Pi.single l 1, 0)| ≤ Fu l)
    (hFφ : ∀ b, |fderiv ℝ f (tubeChart V B x) (0, Pi.single b 1)| ≤ Fφ b)
    (v : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    |fderiv ℝ (fun x => f (tubeChart V B x)) x v| ≤ chartLip Nv A a β Fu Fφ * ‖v‖ := by
  rw [fderiv_comp_tubeChart_apply hV hBper hfper hx hf hB v]
  set p := tubeChart V B x
  set B' := fderiv ℝ B p.2
  set d := polarInvD (rotMap Vᵀ x) (rotMap Vᵀ v)
  set D := ‖rotMap Vᵀ v‖
  have hA0 : ∀ j, 0 ≤ A j := fun j => (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hA j)
  have hβ0 : ∀ l, 0 ≤ β l := fun l => (abs_nonneg _).trans (hβ 0 l)
  have hFu0 : ∀ l, 0 ≤ Fu l := fun l => (abs_nonneg _).trans (hFu l)
  have hFφ0 : ∀ b, 0 ≤ Fφ b := fun b => (abs_nonneg _).trans (hFφ b)
  have hθ0 := thetaW_nonneg hA0 ha
  have hD0 : 0 ≤ D := norm_nonneg _
  have hd1 : ∀ l, |d.1 l| ≤ A l * D := fun l => abs_polarInvD_fst_le (hA l)
  have hd2 : ∀ k, |d.2 k| ≤ A k / a k * D := fun k => abs_polarInvD_snd_le (hA k) (ha k) (haw k)
  have hb : ∀ c : Fin 2, |phiOf d.2 c| ≤ thetaW A a c * D := by
    intro c
    have e : phiOf d.2 c = d.2 c.castSucc - d.2 2 := by fin_cases c <;> rfl
    rw [e, thetaW, add_mul]
    exact (abs_sub _ _).trans (add_le_add (hd2 _) (hd2 _))
  have hu : ∀ l, |(d.1 - B' (phiOf d.2)) l| ≤
      (A l + β l * (thetaW A a 0 + thetaW A a 1)) * D := by
    intro l
    rw [Pi.sub_apply, clm_fin2_apply]
    have h0 : |phiOf d.2 0 * B' (Pi.single 0 1) l| ≤ thetaW A a 0 * D * β l := by
      rw [abs_mul]; exact mul_le_mul (hb 0) (hβ 0 l) (abs_nonneg _) (mul_nonneg (hθ0 0) hD0)
    have h1 : |phiOf d.2 1 * B' (Pi.single 1 1) l| ≤ thetaW A a 1 * D * β l := by
      rw [abs_mul]; exact mul_le_mul (hb 1) (hβ 1 l) (abs_nonneg _) (mul_nonneg (hθ0 1) hD0)
    calc |d.1 l - (phiOf d.2 0 * B' (Pi.single 0 1) l + phiOf d.2 1 * B' (Pi.single 1 1) l)|
        ≤ |d.1 l| + (|phiOf d.2 0 * B' (Pi.single 0 1) l| +
            |phiOf d.2 1 * B' (Pi.single 1 1) l|) :=
          (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ A l * D + (thetaW A a 0 * D * β l + thetaW A a 1 * D * β l) :=
          add_le_add (hd1 l) (add_le_add h0 h1)
      _ = (A l + β l * (thetaW A a 0 + thetaW A a 1)) * D := by ring
  have hshift : shiftD B' d = (d.1 - B' (phiOf d.2), phiOf d.2) := rfl
  rw [hshift, clm_prod_apply_eq_sum]
  have hDv : D ≤ Nv * ‖v‖ := norm_rotMap_transpose_le hN v
  set S := ∑ l, Fu l * (A l + β l * (thetaW A a 0 + thetaW A a 1)) + ∑ b, Fφ b * thetaW A a b
  have hS0 : 0 ≤ S := add_nonneg
    (Finset.sum_nonneg fun l _ => mul_nonneg (hFu0 l)
      (add_nonneg (hA0 l) (mul_nonneg (hβ0 l) (add_nonneg (hθ0 0) (hθ0 1)))))
    (Finset.sum_nonneg fun b _ => mul_nonneg (hFφ0 b) (hθ0 b))
  calc |∑ l, (d.1 - B' (phiOf d.2)) l * fderiv ℝ f p (Pi.single l 1, 0) +
        ∑ c, phiOf d.2 c * fderiv ℝ f p (0, Pi.single c 1)|
      ≤ ∑ l, |(d.1 - B' (phiOf d.2)) l * fderiv ℝ f p (Pi.single l 1, 0)| +
          ∑ c, |phiOf d.2 c * fderiv ℝ f p (0, Pi.single c 1)| :=
        (abs_add_le _ _).trans
          (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ l, (A l + β l * (thetaW A a 0 + thetaW A a 1)) * D * Fu l +
          ∑ c, thetaW A a c * D * Fφ c := by
        refine add_le_add (Finset.sum_le_sum fun l _ => ?_) (Finset.sum_le_sum fun c _ => ?_)
        · rw [abs_mul]
          exact mul_le_mul (hu l) (hFu l) (abs_nonneg _) (mul_nonneg
            (add_nonneg (hA0 l) (mul_nonneg (hβ0 l) (add_nonneg (hθ0 0) (hθ0 1)))) hD0)
        · rw [abs_mul]; exact mul_le_mul (hb c) (hFφ c) (abs_nonneg _) (mul_nonneg (hθ0 c) hD0)
    _ = S * D := by
        simp only [S, add_mul, Finset.sum_mul]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ S * (Nv * ‖v‖) := mul_le_mul_of_nonneg_left hDv hS0
    _ = chartLip Nv A a β Fu Fφ * ‖v‖ := by simp only [chartLip, S]; ring

/-- **Mean-value inequality on a ball** (sup norm on phase space): a pointwise derivative bound
`|dG(y) v| ≤ L ‖v‖` on `closedBall z r` gives `|G x - G z| ≤ L r` there. -/
theorem abs_sub_le_of_closedBall {G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    {z x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} {r L : ℝ} (hL0 : 0 ≤ L)
    (hG : ∀ y ∈ Metric.closedBall z r, DifferentiableAt ℝ G y)
    (hL : ∀ y ∈ Metric.closedBall z r, ∀ v, |fderiv ℝ G y v| ≤ L * ‖v‖)
    (hx : x ∈ Metric.closedBall z r) : |G x - G z| ≤ L * r := by
  have hr : 0 ≤ r := Metric.nonempty_closedBall.1 ⟨x, hx⟩
  have h := (convex_closedBall z r).norm_image_sub_le_of_norm_fderiv_le hG
    (fun y hy => ContinuousLinearMap.opNorm_le_bound _ hL0 fun v => by
      rw [Real.norm_eq_abs]; exact hL y hy v)
    (Metric.mem_closedBall_self hr) hx
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hx) hL0)

/-- **Per-mode bounds on the ball** from the centre `w* = Vᵀz`: with `ε = N_V r`,
`|q_j| + |p_j| ≤ |q*_j| + |p*_j| + 2ε` and `q*_j² + p*_j² - 2 (|q*_j| + |p*_j|) ε ≤ q_j² + p_j²`. -/
theorem modeBounds_of_mem_closedBall {V : Matrix (Fin 3) (Fin 3) ℝ} {Nv r : ℝ}
    (hN : ∀ j, ∑ k, |V k j| ≤ Nv) {z y : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hy : y ∈ Metric.closedBall z r) (j : Fin 3) :
    |(rotMap Vᵀ y).1 j| + |(rotMap Vᵀ y).2 j| ≤
        |(rotMap Vᵀ z).1 j| + |(rotMap Vᵀ z).2 j| + 2 * (Nv * r) ∧
      (rotMap Vᵀ z).1 j ^ 2 + (rotMap Vᵀ z).2 j ^ 2 -
          2 * (|(rotMap Vᵀ z).1 j| + |(rotMap Vᵀ z).2 j|) * (Nv * r) ≤ modeSq V y j := by
  have hN0 : 0 ≤ Nv := le_trans (Finset.sum_nonneg fun k _ => abs_nonneg (V k 0)) (hN 0)
  have hdiff : rotMap Vᵀ y - rotMap Vᵀ z = rotMap Vᵀ (y - z) := by
    rw [rotMap_eq_rotCLM, map_sub]
  have he : ‖rotMap Vᵀ y - rotMap Vᵀ z‖ ≤ Nv * r := by
    rw [hdiff]
    refine (norm_rotMap_transpose_le hN _).trans (mul_le_mul_of_nonneg_left ?_ hN0)
    rw [← dist_eq_norm]; exact hy
  set q := (rotMap Vᵀ y).1 j
  set p := (rotMap Vᵀ y).2 j
  set q' := (rotMap Vᵀ z).1 j
  set p' := (rotMap Vᵀ z).2 j
  have hq : |q - q'| ≤ Nv * r := (abs_fst_apply_le _ j).trans he
  have hp : |p - p'| ≤ Nv * r := (abs_snd_apply_le _ j).trans he
  have hq2 := abs_le.1 hq
  have hp2 := abs_le.1 hp
  refine ⟨?_, ?_⟩
  · have h1 : |q| ≤ |q'| + Nv * r := by
      have := abs_sub_abs_le_abs_sub q q'; linarith
    have h2 : |p| ≤ |p'| + Nv * r := by
      have := abs_sub_abs_le_abs_sub p p'; linarith
    linarith
  · show q' ^ 2 + p' ^ 2 - 2 * (|q'| + |p'|) * (Nv * r) ≤ q ^ 2 + p ^ 2
    have e1 : q' ^ 2 - 2 * |q'| * (Nv * r) ≤ q ^ 2 := by
      have : -(|q'| * (Nv * r)) ≤ q' * (q - q') := by
        have := abs_mul q' (q - q')
        have := neg_abs_le (q' * (q - q'))
        nlinarith [abs_nonneg q', abs_nonneg (q - q')]
      nlinarith [sq_nonneg (q - q')]
    have e2 : p' ^ 2 - 2 * |p'| * (Nv * r) ≤ p ^ 2 := by
      have : -(|p'| * (Nv * r)) ≤ p' * (p - p') := by
        have := abs_mul p' (p - p')
        have := neg_abs_le (p' * (p - p'))
        nlinarith [abs_nonneg p', abs_nonneg (p - p')]
      nlinarith [sq_nonneg (p - p')]
    linarith

end KAM.EffectiveStability.Tube

end
