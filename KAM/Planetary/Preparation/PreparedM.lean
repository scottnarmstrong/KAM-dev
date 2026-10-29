/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedFreq
public import KAM.Planetary.WeakMeasure.Stability

/-!
# The scalar bound `2^k M₁²`, `M*` and `M₀*` (P11A-P8b3, `stepP:p11:pr-d`)

Order-zero Euclidean control of the prepared frequency (the main terms `(ω, εΩ̃/(2π))` have
Euclidean size `≤ L`, the deviations are `≤ c ε ℓ^b`), operator bounds of the real slice of the
higher derivatives, and `M_bound` for the scalar family.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Pd

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Triangle inequality for the Euclidean length with a uniform sup-norm perturbation. -/
theorem p11_pd_euclid_add {N : ℕ} {x : Fin N → ℝ} {u : Fin N → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ c, |x c| ≤ ‖u c‖ + d) :
    KAM.Nekhoroshev.euclid x ≤ KAM.Nekhoroshev.euclid u + Real.sqrt N * d := by
  unfold KAM.Nekhoroshev.euclid
  set S : ℝ := ∑ i, ‖u i‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hcs : ∑ i, ‖u i‖ ≤ Real.sqrt N * Real.sqrt S := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ))
      (fun i => ‖u i‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h1
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le h1
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h2 : ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, (‖u i‖ + d) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  have h3 : ∑ i, (‖u i‖ + d) ^ 2 = S + 2 * d * ∑ i, ‖u i‖ + N * d ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, hSdef, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have h4 : (Real.sqrt S + Real.sqrt N * d) ^ 2 =
      S + 2 * d * (Real.sqrt N * Real.sqrt S) + N * d ^ 2 := by
    have := Real.sq_sqrt hS
    have h5 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith [this, h5]
  rw [h4]
  have : 2 * d * ∑ i, ‖u i‖ ≤ 2 * d * (Real.sqrt N * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  linarith

/-- The first partial of `C.h` is the frequency `ω`. -/
theorem p11_pd_omega_partial (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) (i : Fin n) :
    p11PartialVec (Pi.single i 1) (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J =
      fun _ => C.omega J i := by
  obtain ⟨-, -, -, -, hhd, hωh, -⟩ := id hC
  rw [p11PartialVec_single]
  show p11Step i (fun (J' : P11CVec n) (_ : Fin 1) => C.h J') J = _
  rw [p11_dev_step_const _ (hhd.differentiableAt (isOpen_ball.mem_nhds hJ))]
  funext x
  simp [hωh J hJ]

/-- Pure `J` deviation of a first partial from `ω`. -/
theorem p11_pd_dev_pure (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hFs : P11FastSpec C eps Fast) (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (i : Fin n) (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {k1 : ℝ}
    (hη : p11eta1 C eps ≤ 1)
    (hs1' : 4 * eps / p11s1 C eps ≤ 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1))
    (hs1small : 4 * eps / p11s1 C eps ≤ 1) (hl : 1 ≤ Real.log (1 / eps)) :
    ‖p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ) (0 : Fin n → ℕ)) (p11DevH A)
        (Fin.append J ρ) 0 - C.omega J i‖ ≤
      (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) +
        c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hd := p11_dev_J_bound hC hnu heps hεM hFs hA hzs h5 (Pi.single i 1) J ρ hJ hρ
  rw [p11_pd_omega_partial hC hJball i] at hd
  have h0 : ‖p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ) (0 : Fin n → ℕ))
      (p11DevH A) (Fin.append J ρ) 0 - C.omega J i‖ ≤ _ :=
    le_trans (by
      have := norm_le_pi_norm (p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ)
        (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) - fun _ => C.omega J i) 0
      simpa using this) hd
  refine h0.trans ?_
  have hαs : ∑ k, (Pi.single i 1 : Fin n → ℕ) k = 1 := by simp
  have hP0 : 0 ≤ ∏ k, (((Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ) :=
    Finset.prod_nonneg fun _ _ => by positivity
  have hPα : (∏ k, (((Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) ≤ 1 := by
    have := p11_resc_prod_le (Pi.single i 1 : Fin n → ℕ)
    rw [hαs] at this
    simpa using this
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have := hGη (KAM.realInclusion n C.J0) (by simp; positivity) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  have hRη : 0 ≤ C.MF + p11eta1 C eps := by linarith
  have t1 : eps * p11DevA C eps (Pi.single i 1) ≤
      (∏ k, (((Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) * (C.MF + p11eta1 C eps) *
        (4 * eps / p11s1 C eps) := by
    have := p11_num_a heps hs1 hP0 hRη hs1small _ 0 (by omega)
    simpa [p11DevA] using this
  have t1' : (∏ k, (((Pi.single i 1 : Fin n → ℕ) k).factorial : ℝ)) * (C.MF + p11eta1 C eps) *
        (4 * eps / p11s1 C eps) ≤
      (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) := by
    have h1 : C.MF + p11eta1 C eps ≤ C.MF + 1 := by linarith
    have h2 : 0 ≤ 4 * eps / p11s1 C eps := by positivity
    calc _ ≤ 1 * (C.MF + 1) * (4 * eps / p11s1 C eps) := by gcongr
      _ ≤ _ := by rw [one_mul]; gcongr
  have hl5 : 0 ≤ Real.log (1 / eps) ^ (5 * C.tau + 2) := Real.rpow_nonneg (by linarith) _
  have t2 : p11DevG C nu eps c (Pi.single i 1) 0 ≤
      c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by
    have := p11_num_g (Q := ∏ k, (((0 : Fin n → ℕ) k).factorial : ℝ)) heps h5 hP0
      (Finset.prod_nonneg fun _ _ => by positivity) hc0 hl5
      (∑ k, (Pi.single i 1 : Fin n → ℕ) k) (∑ k, (0 : Fin n → ℕ) k) 0 (by simp)
    simp only [pow_zero, one_mul] at this
    have h3 : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by positivity
    refine le_trans (le_of_eq ?_) (this.trans ?_)
    · simp [p11DevG]
    · simp only [Pi.zero_apply, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, mul_one,
        Finset.sum_const_zero, pow_zero]
      calc _ ≤ 1 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by gcongr
        _ = _ := one_mul _
  linarith

/-- Deviation of a `ρ̃`-index first partial from `ε Ω̃/(2π)`. -/
theorem p11_pd_dev_rho (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hA : P11SlowSpecOf C Fast nu eps c A) (hc0 : 0 ≤ c)
    (hzs : 3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (k : Fin n) (J ρ : P11CVec n) (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4) {k2 : ℝ}
    (hη0 : 0 ≤ p11eta1 C eps)
    (hη : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1))
    (hl : 1 ≤ Real.log (1 / eps)) :
    ‖p11PartialVec (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) + Pi.single (Fin.natAdd n k) 1)
        (p11DevH A) (Fin.append J ρ) 0 - (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k)‖ ≤
      c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1) +
        4 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hd := p11_dev_rho_bound hC hnu heps hεM hA hzs h5 k 0 0 J ρ hJ hρ
  have hz : (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) : Fin (n + n) → ℕ) = 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  have hJe : (fun i => (Fin.append J ρ : P11CVec (n + n)) (Fin.castAdd n i)) = J :=
    funext fun i => Fin.append_left J ρ i
  rw [hz, p11PartialVec_zero, hJe] at hd
  have h0 : ‖p11PartialVec (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) +
      Pi.single (Fin.natAdd n k) 1) (p11DevH A) (Fin.append J ρ) 0 -
      (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k)‖ ≤
      eps * p11DevZ C nu eps c 0 0 + p11DevG C nu eps c 0 (0 + Pi.single k 1) := by
    rw [hz]
    refine le_trans ?_ hd
    have h1 := norm_le_pi_norm (p11PartialVec (0 + Pi.single (Fin.natAdd n k) 1) (p11DevH A)
      (Fin.append J ρ) - (eps : ℂ) • fun (_ : Fin 1) =>
        (2 * Real.pi : ℂ)⁻¹ * C.Omega J k) 0
    simpa using h1
  refine h0.trans ?_
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := by
    refine Real.one_le_rpow hl ?_
    have hτ0 := (fast_consts hC).2.1
    linarith
  have hl5 : 0 ≤ Real.log (1 / eps) ^ (5 * C.tau + 2) := Real.rpow_nonneg (by linarith) _
  have hM0 : 0 ≤ c * (eps + p11eta1 C eps) := by positivity
  have tz : eps * p11DevZ C nu eps c 0 0 ≤
      c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1) := by
    have := p11_num_z_final (PQ := 1) (F := 1) heps hc0 hη0 hlx zero_le_one le_rfl hη
    simp only [p11DevZ, Pi.zero_apply, Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one,
      Finset.sum_const_zero, pow_zero, mul_one, div_one, one_mul] at this ⊢
    linarith
  have tg : p11DevG C nu eps c 0 (0 + Pi.single k 1 : Fin n → ℕ) ≤
      4 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by
    have hsum : ∑ i, (0 + Pi.single k 1 : Fin n → ℕ) i = 1 := by simp
    have hQ0 : 0 ≤ ∏ i, ((((0 + Pi.single k 1 : Fin n → ℕ)) i).factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => by positivity
    have hQ1 : (∏ i, ((((0 + Pi.single k 1 : Fin n → ℕ)) i).factorial : ℝ)) ≤ 1 := by
      have := p11_resc_prod_le (0 + Pi.single k 1 : Fin n → ℕ)
      rw [hsum] at this
      simpa using this
    have := p11_num_g (P := 1) (Q := ∏ i, ((((0 + Pi.single k 1 : Fin n → ℕ)) i).factorial : ℝ))
      heps h5 zero_le_one hQ0 hc0 hl5 0 1 0 (by simp)
    simp only [pow_zero, one_mul, pow_one] at this
    have h3 : 0 ≤ c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) := by positivity
    refine le_trans (le_of_eq ?_) (this.trans ?_)
    · simp [p11DevG]
    · calc _ ≤ 1 * 4 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by gcongr
        _ = _ := by ring
  linarith

/-- Order-one deviations of the partials of `h` from the main terms `(ω, ε Ω̃/(2π))`. -/
theorem p11_pd_dev0 (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      ∀ J ρ : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 →
        ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4 →
        (∀ i : Fin n, ‖p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ) (0 : Fin n → ℕ))
            (p11DevH A) (Fin.append J ρ) 0 - C.omega J i‖ ≤ K * (1 + c) * eps *
              Real.log (1 / eps) ^ (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1))) ∧
        ∀ k : Fin n, ‖p11PartialVec (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) +
            Pi.single (Fin.natAdd n k) 1) (p11DevH A) (Fin.append J ρ) 0 -
              (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k)‖ ≤ K * (1 + c) * eps *
              Real.log (1 / eps) ^ (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) := by
  obtain ⟨k1, hk1, hs1inv⟩ := p11_prin_s1_inv hC
  obtain ⟨k2, hk2, heta⟩ := p11_prin_eta1_le hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  refine ⟨(C.MF + 1) * 4 * k1 + k2 + 5, by positivity, ?_⟩
  intro Fast eps c A heps hεM hc0 hθ hzs h5 hFs hA J ρ hJ hρ
  generalize hK : (C.MF + 1) * 4 * k1 + k2 + 5 = K at hθ ⊢
  generalize hQe : 5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1) = Qe at hθ ⊢
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have hℓ0 : 0 ≤ Real.log (1 / eps) := by linarith
  have hKk : (C.MF + 1) * 4 * k1 + k2 + 5 = K := hK
  have hmu0 : (0 : ℝ) ≤ (p11PatchData D).mu := Nat.cast_nonneg _
  have hprod : 0 ≤ (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1) := by positivity
  have hQ1 : C.tau + 1 ≤ Qe := by rw [← hQe]; linarith
  have hQ2 : 2 * C.tau + 1 ≤ Qe := by rw [← hQe]; linarith
  have hQ3 : 5 * C.tau + 2 ≤ Qe := by rw [← hQe]; linarith
  have hlQ1 : Real.log (1 / eps) ^ (C.tau + 1) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ1
  have hlQ2 : Real.log (1 / eps) ^ (2 * C.tau + 1) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ2
  have hlQ3 : Real.log (1 / eps) ^ (5 * C.tau + 2) ≤ Real.log (1 / eps) ^ Qe :=
    p11_resc_rpow_le hl hQ3
  have hlx : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.one_le_rpow hl (by linarith)
  have he1 : eps ≤ 1 := by
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    nlinarith
  have hMF1 : 0 ≤ C.MF + 1 := by linarith
  have hKk2 : k2 ≤ K := by
    have : 0 ≤ (C.MF + 1) * 4 * k1 := by positivity
    linarith
  have hKk1 : 4 * k1 ≤ K := by
    have h1 : 4 * k1 ≤ (C.MF + 1) * 4 * k1 := by nlinarith
    linarith
  have hθ' : ∀ t : ℝ, 0 ≤ t → t ≤ K → ∀ x : ℝ, x ≤ Qe →
      t * eps * Real.log (1 / eps) ^ x ≤ 1 := by
    intro t ht htK x hx
    have h1 : Real.log (1 / eps) ^ x ≤ Real.log (1 / eps) ^ Qe := p11_resc_rpow_le hl hx
    have h3 : t * eps * Real.log (1 / eps) ^ x ≤ t * eps * Real.log (1 / eps) ^ Qe := by gcongr
    have htc : t ≤ K * (1 + c) := by nlinarith
    have h4 : t * eps * Real.log (1 / eps) ^ Qe ≤ K * (1 + c) * eps * Real.log (1 / eps) ^ Qe := by
      gcongr
    exact h3.trans (h4.trans hθ)
  have hη : p11eta1 C eps ≤ k2 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := heta heps hεM
  have hη1 : p11eta1 C eps ≤ 1 := hη.trans (hθ' k2 hk2.le hKk2 _ hQ2)
  have hη0 : 0 ≤ p11eta1 C eps := by
    obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGη, -⟩ := hFs
    have hr : 0 < C.rz / 2 := by positivity
    have hs1 := (slow_pos hC hnu heps hεM).2.1
    have := hGη (KAM.realInclusion n C.J0) (by simp; linarith only [hs1]) 0 (by simpa using hr)
    exact (norm_nonneg _).trans this
  have hs1' : 4 * eps / p11s1 C eps ≤ 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1) := by
    have h1 := hs1inv heps hεM
    rw [div_eq_mul_inv]
    calc 4 * eps * (p11s1 C eps)⁻¹ ≤ 4 * eps * (k1 * Real.log (1 / eps) ^ (C.tau + 1)) := by
          gcongr
      _ = 4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1) := by ring
  have hs1small : 4 * eps / p11s1 C eps ≤ 1 :=
    hs1'.trans (hθ' (4 * k1) (by positivity) hKk1 _ hQ1)
  have hl1 : 0 ≤ Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_nonneg hℓ0 _
  have hl2 : 0 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) := Real.rpow_nonneg hℓ0 _
  have hl5 : 0 ≤ Real.log (1 / eps) ^ (5 * C.tau + 2) := Real.rpow_nonneg hℓ0 _
  refine ⟨fun i => ?_, fun k => ?_⟩
  · have h := p11_pd_dev_pure hC hnu heps hεM hFs hA hc0 hzs h5 i J ρ hJ hρ hη1 hs1' hs1small hl
    refine le_trans ?_ (le_of_eq (zero_add _))
    refine p11_num_collect_pure (T3 := 0) (a := (C.MF + 1) * (4 * k1)) (F := 1) heps he1 hc0
      zero_le_one hl1 hl5 hlQ1 hlQ3 ?_ ?_ ?_
    · linarith
    · linarith [mul_nonneg hMF1 hk1.le]
    · have e1 : (C.MF + 1) * (4 * k1 * eps * Real.log (1 / eps) ^ (C.tau + 1)) =
          (C.MF + 1) * (4 * k1) * (eps * Real.log (1 / eps) ^ (C.tau + 1)) := by ring
      have e2 : c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2) =
          1 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by ring
      linarith
  · have h := p11_pd_dev_rho hC hnu heps hεM hA hc0 hzs h5 k J ρ hJ hρ hη0 hη hl
    refine le_trans ?_ (le_of_eq (zero_add _))
    refine p11_num_collect_rho (m := 0) (T3 := 0) (F := 1) (M := 4) (K := K) heps he1 hc0 zero_le_one
      hk2.le (by norm_num) hl2 hl5 hlQ2 hlQ3 ?_ ?_ le_rfl
    · have : 0 ≤ (C.MF + 1) * 4 * k1 := by positivity
      linarith
    · have e1 : c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1) =
          1 * (c * (1 + k2) * eps ^ 2 * Real.log (1 / eps) ^ (2 * C.tau + 1)) := by ring
      have e2 : 4 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) =
          1 * 4 * (c * eps ^ 2 * Real.log (1 / eps) ^ (5 * C.tau + 2)) := by ring
      linarith

/-- The rescaled point of `I ∈ actionNbhd box (3/4)` lies in the Cauchy region. -/
theorem p11_pd_point {nu eps : ℝ} (heps : 0 < eps) (h5 : 5 * eps ≤ p11s2 C nu eps)
    {I : P11CVec (n + n)} (hI : I ∈ KAM.actionNbhd (p11PreparedBox n) (3 / 4)) :
    ∃ J ρ : P11CVec n, (p11Rescale C.J0 eps (0, I)).2 = Fin.append J ρ ∧
      ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 ∧
      ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4 := by
  have hIn := p11_freq_smallV_norm hI
  obtain ⟨J, ρ, hJρ⟩ : ∃ (J ρ : P11CVec n), (p11Rescale C.J0 eps (0, I)).2 = Fin.append J ρ :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := (p11Rescale C.J0 eps (0, I)).2)).symm⟩
  have hdiff : (p11Rescale C.J0 eps (0, I)).2 - (Fin.append (KAM.realInclusion n C.J0)
      (fun _ => (2 * Real.pi * eps : ℂ)) : P11CVec (n + n)) = (eps : ℂ) • I := by
    rw [p11_freq_res_eq C.J0 eps I]; abel
  have hnorm : ‖(Fin.append J ρ : P11CVec (n + n)) - Fin.append (KAM.realInclusion n C.J0)
      (fun _ => (2 * Real.pi * eps : ℂ))‖ < 5 * eps / 4 := by
    rw [← hJρ, hdiff, norm_smul, Complex.norm_real, Real.norm_of_nonneg heps.le]
    nlinarith
  refine ⟨J, ρ, hJρ, ?_, ?_⟩
  · have h1 : ‖J - KAM.realInclusion n C.J0‖ ≤ ‖(Fin.append J ρ : P11CVec (n + n)) -
        Fin.append (KAM.realInclusion n C.J0) (fun _ => (2 * Real.pi * eps : ℂ))‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      have := norm_le_pi_norm ((Fin.append J ρ : P11CVec (n + n)) - Fin.append
        (KAM.realInclusion n C.J0) (fun _ => (2 * Real.pi * eps : ℂ))) (Fin.castAdd n i)
      simpa using this
    linarith
  · have h1 : ‖ρ - (fun _ => (2 * Real.pi * eps : ℂ))‖ ≤ ‖(Fin.append J ρ : P11CVec (n + n)) -
        Fin.append (KAM.realInclusion n C.J0) (fun _ => (2 * Real.pi * eps : ℂ))‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      have := norm_le_pi_norm ((Fin.append J ρ : P11CVec (n + n)) - Fin.append
        (KAM.realInclusion n C.J0) (fun _ => (2 * Real.pi * eps : ℂ))) (Fin.natAdd n i)
      simpa using this
    linarith

/-- The prepared frequency is holomorphic on `actionNbhd box 1`. -/
theorem p11_pd_freq_diff {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    {Q : P11PreparedData n} (heps : 0 < eps) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (hs2 : 0 ≤ p11s2 C nu eps) (hA : P11SlowSpecOf C Fast nu eps c A)
    (hN : ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
      (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) / (eps : ℂ)) :
    DifferentiableOn ℂ (p11PreparedFreq Q) (KAM.actionNbhd (p11PreparedBox n) 1) := by
  set U1 := KAM.actionNbhd (p11PreparedBox n) 1 with hU1
  have hU1o : IsOpen U1 := p11_freq_isOpen_actionNbhd _ _
  set Vh := p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) with hVh
  set b : P11CVec (n + n) := Fin.append (KAM.realInclusion n C.J0)
    (fun _ => (2 * Real.pi * eps : ℂ)) with hb
  have hres : ∀ I, (p11Rescale C.J0 eps (0, I)).2 = b + (eps : ℂ) • I := p11_freq_res_eq C.J0 eps
  have hsub := p11_freq_U1_sub (C := C) (nu := nu) heps h5
  have hHd := p11_freq_H_diff (C := C) hs2 heps.le hA
  have hmap : ∀ I ∈ U1, b + (eps : ℂ) • I ∈ Vh := fun I hI => by
    have := hsub hI
    simpa [hres] using this
  have hHaff : DifferentiableOn ℂ (fun I : P11CVec (n + n) => p11DevH A (b + (eps : ℂ) • I)) U1 :=
    hHd.comp (by fun_prop) hmap
  have hNd : DifferentiableOn ℂ Q.N U1 := by
    have h1 : DifferentiableOn ℂ (fun I : P11CVec (n + n) =>
        (eps : ℂ)⁻¹ * p11DevH A (b + (eps : ℂ) • I) 0) U1 :=
      (differentiableOn_const _).mul (differentiableOn_pi.1 hHaff 0)
    refine h1.congr fun I hI => ?_
    rw [hN I hI, hres I]
    have : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
    simp only [p11DevH]
    field_simp
  have hfd := (KAM.analyticOnNhd_of_differentiableOn hU1o hNd).fderiv
  exact differentiableOn_pi.2 fun i => hfd.differentiableOn.clm_apply (differentiableOn_const _)

/-- A point of the Euclidean `1/4`-thickening of the box has its real image in every
`r`-neighbourhood, `1/4 < r`. -/
theorem p11_pd_thick_mem {y : P11Vec (n + n)} {r : ℝ} (hr : 1 / 4 < r)
    (hy : y ∈ p11thick (p11PreparedBox n) (1 / 4)) :
    KAM.realInclusion (n + n) y ∈ KAM.actionNbhd (p11PreparedBox n) r := by
  obtain ⟨x, hx, hyx⟩ := hy
  refine ⟨x, hx, lt_of_le_of_lt ?_ hr⟩
  refine le_trans ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_) (le_refl _)
  have h1 : ‖y i - x i‖ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
  have h2 : ‖y - x‖ ≤ p11euclid (y - x) := (KAM.Nekhoroshev.norm_le_euclid (y - x)).1
  simp only [Pi.sub_apply, KAM.realInclusion_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact le_trans h1 (h2.trans hyx)

/-- Euclidean length is monotone in the coordinatewise norms. -/
theorem p11_pd_euclid_mono {N : ℕ} {u v : Fin N → ℂ} (h : ∀ c, ‖u c‖ ≤ ‖v c‖) :
    KAM.Nekhoroshev.euclid u ≤ KAM.Nekhoroshev.euclid v := by
  unfold KAM.Nekhoroshev.euclid
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (norm_nonneg _) (h c) 2)

theorem p11_pd_single_cast (i : Fin n) :
    (0 + Pi.single (Fin.castAdd n i) 1 : Fin (n + n) → ℕ) =
      Fin.append (Pi.single i 1 : Fin n → ℕ) (0 : Fin n → ℕ) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · by_cases h : a = i
    · subst h; simp
    · have : (Fin.castAdd n a : Fin (n + n)) ≠ Fin.castAdd n i := fun h' => h (Fin.castAdd_injective _ _ h')
      simp [h, this]
  · have : (Fin.natAdd n a : Fin (n + n)) ≠ Fin.castAdd n i := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
      have := i.isLt
      omega
    have h2 : ¬ a.addNat n = Fin.castAdd n i := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
      have := i.isLt
      omega
    simp [h2]

theorem p11_pd_single_nat (k : Fin n) :
    (0 + Pi.single (Fin.natAdd n k) 1 : Fin (n + n) → ℕ) =
      Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) + Pi.single (Fin.natAdd n k) 1 := by
  have hz : (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) : Fin (n + n) → ℕ) = 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [hz]

/-- Order-zero Euclidean bound `|ω̂|₂ ≤ 2L + 1` on the real slice of the thickened box. -/
theorem p11_pd_zero (hCF : P11SecularFullSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      ∀ y ∈ p11thick (p11PreparedBox n) (1 / 4),
        p11euclid (p11PreparedFreqR Q y) ≤ 2 * C.L + 1 := by
  have hC := hCF.1
  obtain ⟨K1, hK1, hdev⟩ := p11_pd_dev0 hC hnu
  obtain ⟨-, -, hL1, hrC0, -, -, -, -, -, hMF⟩ := fast_consts hC
  have hN0 : (0 : ℝ) ≤ ((n + n : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨((n + n : ℕ) + 1 : ℝ) * K1, by positivity, ?_⟩
  intro Fast eps c A Q heps hεM hc0 hθ hzs h5 hFs hA hN y hy
  obtain ⟨hK2, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK2
  have hs1r := p11s1_le C eps
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  generalize hX : (1 + c) * eps * Real.log (1 / eps) ^
    (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1)) = X
  have hX0 : 0 ≤ X := by
    rw [← hX]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log (1 / eps) by linarith)
      (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1))
    positivity
  have hθ1 : ((n + n : ℕ) + 1 : ℝ) * (K1 * X) ≤ 1 := by
    rw [← hX]; linarith
  have hKX : K1 * X ≤ 1 := by
    have h1 : K1 * X ≤ ((n + n : ℕ) + 1 : ℝ) * (K1 * X) := by
      have : 0 ≤ K1 * X := by positivity
      nlinarith
    linarith
  have hyI := p11_pd_thick_mem (r := 3 / 4) (by norm_num) hy
  have hU1 : KAM.realInclusion (n + n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 :=
    p11_pd_thick_mem (r := 1) (by norm_num) hy
  obtain ⟨J, ρ, hres, hJ, hρ⟩ := p11_pd_point heps h5 hyI
  have hJball : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball_iff_norm]; linarith
  have hW : ∀ c' : Fin (n + n), p11PreparedFreq Q (KAM.realInclusion (n + n) y) c' =
      p11PartialVec (0 + Pi.single c' 1) (p11DevH A) (Fin.append J ρ) 0 := by
    intro c'
    have := p11_freq_partial_eq heps h5 hs2.le hA hN hU1 (0 : Fin (n + n) → ℕ) c'
    rw [p11PartialVec_zero] at this
    rw [this]
    simp [hres]
  obtain ⟨hJdev, hρdev⟩ := hdev (c := c) heps hεM hc0
    (by rw [← hX] at hKX; linarith) hzs h5 hFs hA J ρ hJ hρ
  set mainv : P11CVec (n + n) := Fin.append (fun i => C.omega J i)
    (fun k => (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k)) with hmain
  have he1 : eps ≤ 1 := by
    have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    nlinarith
  have hmainE : KAM.Nekhoroshev.euclid mainv ≤ C.L := by
    refine le_trans (p11_pd_euclid_mono (v := Fin.append (C.omega J)
      ((2 * Real.pi : ℂ)⁻¹ • C.Omega J)) fun c' => ?_) (hCF.2 J hJball)
    refine Fin.addCases (fun i => ?_) (fun k => ?_) c'
    · simp [hmain]
    · simp only [hmain, Fin.append_right, Pi.smul_apply, smul_eq_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg heps.le]
      exact mul_le_of_le_one_left (by positivity) he1
  have hcomp : ∀ c' : Fin (n + n),
      |p11PreparedFreqR Q y c'| ≤ ‖mainv c'‖ + K1 * X := by
    intro c'
    have hre : |p11PreparedFreqR Q y c'| ≤ ‖p11PreparedFreq Q (KAM.realInclusion (n + n) y) c'‖ :=
      Complex.abs_re_le_norm _
    refine hre.trans ?_
    rw [hW c']
    refine Fin.addCases (fun i => ?_) (fun k => ?_) c'
    · rw [p11_pd_single_cast]
      have h1 : ‖p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ) (0 : Fin n → ℕ))
          (p11DevH A) (Fin.append J ρ) 0 - C.omega J i‖ ≤ K1 * X := by
        rw [← hX]; linarith [hJdev i]
      simp only [hmain, Fin.append_left]
      linarith [norm_le_norm_add_norm_sub' (p11PartialVec (Fin.append (Pi.single i 1 : Fin n → ℕ)
        (0 : Fin n → ℕ)) (p11DevH A) (Fin.append J ρ) 0) (C.omega J i)]
    · rw [p11_pd_single_nat]
      have h1 : ‖p11PartialVec (Fin.append (0 : Fin n → ℕ) (0 : Fin n → ℕ) +
          Pi.single (Fin.natAdd n k) 1) (p11DevH A) (Fin.append J ρ) 0 -
          (eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k)‖ ≤ K1 * X := by
        rw [← hX]; linarith [hρdev k]
      simp only [hmain, Fin.append_right]
      linarith [norm_le_norm_add_norm_sub' (p11PartialVec (Fin.append (0 : Fin n → ℕ)
        (0 : Fin n → ℕ) + Pi.single (Fin.natAdd n k) 1) (p11DevH A) (Fin.append J ρ) 0)
        ((eps : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * C.Omega J k))]
  have hadd := p11_pd_euclid_add (x := p11PreparedFreqR Q y) (u := mainv)
    (d := K1 * X) (by positivity) hcomp
  have hsq : Real.sqrt ((n + n : ℕ) : ℝ) ≤ ((n + n : ℕ) : ℝ) + 1 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h2 : Real.sqrt ((n + n : ℕ) : ℝ) * (K1 * X) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hsq (by positivity)) hθ1
  show KAM.Nekhoroshev.euclid (p11PreparedFreqR Q y) ≤ 2 * C.L + 1
  linarith

theorem p11_pd_prem {K K' c e l : ℝ} (hK : K' ≤ K) (h0 : 0 ≤ (1 + c) * e * l)
    (h : K * (1 + c) * e * l ≤ 1) : K' * (1 + c) * e * l ≤ 1 := by
  have h1 : K' * ((1 + c) * e * l) ≤ K * ((1 + c) * e * l) := mul_le_mul_of_nonneg_right hK h0
  linarith

theorem p11_pd_num {N K0 L K1 eps X : ℝ} {j mu : ℕ} (hN0 : 0 ≤ N) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (hK1 : 0 ≤ K1) (hX0 : 0 ≤ X) (hεX : eps ≤ X) (heps : 0 ≤ eps) (hj : j + 1 ≤ mu + 2)
    (hKX : ((N + 1) ^ (mu + 2) * (K0 + L) + K1 + 1) * X ≤ 1) :
    Real.sqrt N * (N ^ j * (eps * L + K0 * X)) ≤ 1 := by
  have hsq : Real.sqrt N ≤ N + 1 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hpw : N ^ j ≤ (N + 1) ^ j := pow_le_pow_left₀ hN0 (by linarith) j
  have hB0 : 0 ≤ eps * L + K0 * X := by positivity
  have hBle : eps * L + K0 * X ≤ (K0 + L) * X := by nlinarith
  have hFn' : Real.sqrt N * N ^ j ≤ (N + 1) ^ (mu + 2) := by
    calc _ ≤ (N + 1) * (N + 1) ^ j := mul_le_mul hsq hpw (by positivity) (by positivity)
      _ = (N + 1) ^ (j + 1) := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hj
  have h3 : Real.sqrt N * (N ^ j * (eps * L + K0 * X)) ≤ (N + 1) ^ (mu + 2) * ((K0 + L) * X) := by
    rw [← mul_assoc]
    exact mul_le_mul hFn' hBle hB0 (by positivity)
  have h4 : (N + 1) ^ (mu + 2) * ((K0 + L) * X) ≤ 1 := by
    have h5 : 0 ≤ ((N + 1) ^ (mu + 2) * (K0 + L)) * X := by positivity
    have h6 : 0 ≤ K1 * X := by positivity
    nlinarith
  linarith

/-- Operator bound of the real slice of the derivatives of order `1 ≤ j ≤ μ̄ + 1`. -/
theorem p11_pd_ord (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ (p11PatchData D).mu + 1 →
        ∀ y ∈ p11thick (p11PreparedBox n) (1 / 4),
          p11op (p11PreparedFreqR Q) j y ≤ 2 * C.L + 1 := by
  obtain ⟨K0, hK0, hpart⟩ := p11_freq_partial hC hnu
  obtain ⟨-, -, hL1, -, -, -, -, -, -, hMF⟩ := fast_consts hC
  have hN0 : (0 : ℝ) ≤ ((n + n : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨(((n + n : ℕ) : ℝ) + 1) ^ ((p11PatchData D).mu + 2) * (K0 + C.L) + K0 + 1,
    by positivity, ?_⟩
  intro Fast eps c A Q heps hεM hc0 hθ hzs h5 hFs hA hN j hj1 hj y hy
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have hlQ : 1 ≤ Real.log (1 / eps) ^
      (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1)) := by
    refine Real.one_le_rpow hl ?_
    have hτ0 := (fast_consts hC).2.1
    have : (0 : ℝ) ≤ (p11PatchData D).mu := Nat.cast_nonneg _
    nlinarith
  generalize hX : (1 + c) * eps * Real.log (1 / eps) ^
    (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1)) = X
  have hX0 : 0 ≤ X := by rw [← hX]; positivity
  have hεX : eps ≤ X := by
    rw [← hX]
    nlinarith [mul_nonneg heps.le hc0, mul_nonneg heps.le (sub_nonneg.2 hlQ)]
  have hKX : ((((n + n : ℕ) : ℝ) + 1) ^ ((p11PatchData D).mu + 2) * (K0 + C.L) + K0 + 1) * X ≤ 1 :=
    by rw [← hX]; exact le_trans (le_of_eq (by ring)) hθ
  have hK0X : K0 * X ≤ 1 := by
    have h1 : 0 ≤ (((n + n : ℕ) : ℝ) + 1) ^ ((p11PatchData D).mu + 2) * (K0 + C.L) := by
      positivity
    nlinarith
  have hyI := p11_pd_thick_mem (r := 3 / 4) (by norm_num) hy
  have hyU := p11_pd_thick_mem (r := 1) (by norm_num) hy
  have hWd := p11_pd_freq_diff (C := C) heps h5 (slow_pos hC hnu heps hεM).2.2.le hA hN (Q := Q)
  have hB : ∀ α : Fin (n + n) → ℕ, ∑ i, α i = j →
      ‖p11PartialVec α (p11PreparedFreq Q) (KAM.realInclusion (n + n) y)‖ ≤
        eps * C.L + K0 * X := by
    intro α hα
    have := hpart (Fast := Fast) (A := A) (Q := Q) heps hεM hc0
      (by rw [← hX] at hK0X; linarith) hzs h5 hFs hA hN _ hyI j hj α hα
    have hj0 : j ≠ 0 := by omega
    simp only [hj0, ↓reduceIte] at this
    refine this.trans (le_of_eq ?_)
    rw [← hX]; ring
  have h1 := p11op_re_le (p11_freq_isOpen_actionNbhd _ _) hWd hyU hB
  have h2 : p11op (p11PreparedFreqR Q) j y ≤
      Real.sqrt ((n + n : ℕ) : ℝ) * (((n + n : ℕ) : ℝ) ^ j * (eps * C.L + K0 * X)) := h1
  have h3 := p11_pd_num (N := ((n + n : ℕ) : ℝ)) (L := C.L) (K1 := 0) (j := j)
    (mu := (p11PatchData D).mu) hN0 hK0.le (by linarith) le_rfl hX0 hεX heps.le (by omega)
    (by nlinarith [mul_nonneg hK0.le hX0])
  linarith

theorem p11_pd_contdiff {Q : P11PreparedData n} {U : Set (P11CVec (n + n))} (hU : IsOpen U)
    (hW : DifferentiableOn ℂ (p11PreparedFreq Q) U) (r : ℕ) :
    ContDiffOn ℝ r (p11PreparedFreqR Q) (KAM.realInclusion (n + n) ⁻¹' U) := by
  have hcdC : ContDiffOn ℂ r (p11PreparedFreq Q) U :=
    (KAM.analyticOnNhd_of_differentiableOn hU hW).contDiffOn hU.uniqueDiffOn
  have hcomp := (hcdC.restrict_scalars ℝ).comp_continuousLinearMap (KAM.realInclusion (n + n))
  exact contDiffOn_pi.2 fun l => Complex.reCLM.contDiff.comp_contDiffOn ((contDiffOn_pi.1 hcomp) l)

/-- The operator jet bound `M₁ ≤ 2L + 1` of the real prepared frequency, orders `0..μ̄+1`. -/
theorem p11_pd_jet (hCF : P11SecularFullSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      p11JetBound false ((p11PatchData D).mu + 1) (p11thick (p11PreparedBox n) (1 / 4))
        (p11PreparedFreqR Q) (2 * C.L + 1) := by
  obtain ⟨K0, hK0, hord⟩ := p11_pd_ord hCF.1 hnu
  obtain ⟨K1, hK1, hzero⟩ := p11_pd_zero hCF hnu
  refine ⟨K0 + K1, by positivity, ?_⟩
  intro Fast eps c A Q heps hεM hc0 hθ hzs h5 hFs hA hN j hj y hy
  have hS : 0 ≤ (1 + c) * eps * Real.log (1 / eps) ^
      (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1)) := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log (1 / eps) by
      linarith [slow_log_ge_one hCF.1 heps hεM]) (5 * C.tau + 2 +
        (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1))
    positivity
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨a, -, ha⟩ := p11op_attained (n := n + n) (m := n + n) (p11PreparedFreqR Q) 0 y
    rw [ha]
    have := hzero heps hεM hc0 (p11_pd_prem (by linarith) hS hθ) hzs h5 hFs hA hN y hy
    simpa using this
  · exact hord heps hεM hc0 (p11_pd_prem (by linarith) hS hθ) hzs h5 hFs hA hN j hj0 hj y hy

/-- `stepP:p11:pr-d`: the scalar bound `2^k M₁²` (orders `1 ≤ j ≤ μ̄ + 1` and order zero), and the
diagonal bound `M₀*`, for the real prepared frequency on the `1/4`-thickened box. The only
extra premises are the numeric smallness (`ε ≤ ε₃`) conditions of the other prepared steps. -/
theorem p11_pr_d (hCF : P11SecularFullSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      (∀ direction : P11Vec (n + n), p11euclid direction = 1 →
        ∀ j, 1 ≤ j → j ≤ (p11PatchData D).mu + 1 →
          ∀ y ∈ p11thick (p11PreparedBox n) (1 / 4),
            p11op (p11scalar 2 (p11PreparedFreqR Q) direction) j y ≤
              (2 : ℝ) ^ ((p11PatchData D).mu + 1) * (2 * C.L + 1) ^ 2) ∧
      p11JetBound true (p11PatchData D).mu (p11thick (p11PreparedBox n) (1 / 4))
        (p11PreparedFreqR Q) (p11M0 n (p11PatchData D).mu C.L) ∧
      (∀ direction : P11Vec (n + n), p11euclid direction = 1 →
        ∀ y ∈ p11thick (p11PreparedBox n) (1 / 4),
          p11op (p11scalar 2 (p11PreparedFreqR Q) direction) 0 y ≤
            (2 : ℝ) ^ ((p11PatchData D).mu + 1) * (2 * C.L + 1) ^ 2) := by
  have hC := hCF.1
  obtain ⟨K, hK, hjet⟩ := p11_pd_jet hCF hnu
  obtain ⟨K1, hK1, hzero⟩ := p11_pd_zero hCF hnu
  have hn : 1 ≤ n + n := by have := D.n_ge; omega
  have hL1 := (fast_consts hC).2.2.1
  refine ⟨K + K1, by positivity, ?_⟩
  intro Fast eps c A Q heps hεM hc0 hθ hzs h5 hFs hA hN
  have hS : 0 ≤ (1 + c) * eps * Real.log (1 / eps) ^
      (5 * C.tau + 2 + (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1)) := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log (1 / eps) by
      linarith [slow_log_ge_one hC heps hεM]) (5 * C.tau + 2 +
        (C.tau + 1) * (((p11PatchData D).mu : ℝ) + 1))
    positivity
  have hjet' := hjet heps hεM hc0 (p11_pd_prem (by linarith) hS hθ) hzs h5 hFs hA hN
  have hzero' := hzero heps hεM hc0 (p11_pd_prem (by linarith) hS hθ) hzs h5 hFs hA hN
  have hU1o : IsOpen (KAM.actionNbhd (p11PreparedBox n) 1) := p11_freq_isOpen_actionNbhd _ _
  have hWd := p11_pd_freq_diff (C := C) heps h5 (slow_pos hC hnu heps hεM).2.2.le hA hN (Q := Q)
  have hVo : IsOpen (KAM.realInclusion (n + n) ⁻¹' KAM.actionNbhd (p11PreparedBox n) 1) :=
    hU1o.preimage (KAM.realInclusion (n + n)).continuous
  have hAV : p11thick (p11PreparedBox n) (1 / 4) ⊆
      KAM.realInclusion (n + n) ⁻¹' KAM.actionNbhd (p11PreparedBox n) 1 := fun y hy =>
    p11_pd_thick_mem (r := 1) (by norm_num) hy
  have hMb := M_bound hn hVo hAV (p11_pd_contdiff hU1o hWd _) (by linarith) hjet'
  refine ⟨fun d hd j hj1 hj y hy => ?_, fun j hj y hy => ?_, fun d hd y hy => ?_⟩
  · refine (hMb d hd j hj1 hj y hy).2.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
  · simp only [↓reduceIte]
    refine (p11dg_le_p11op _ j y hn).trans ((hjet' j (by omega) y hy).trans ?_)
    unfold p11M0
    have : (1 : ℝ) ≤ (2 * (n : ℝ) + 1) ^ ((p11PatchData D).mu + 1) :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
    nlinarith
  · obtain ⟨a, -, ha⟩ := p11op_attained (n := n + n) (m := 1)
      (p11scalar 2 (p11PreparedFreqR Q) d) 0 y
    rw [ha]
    simp only [iteratedFDeriv_zero_apply]
    have hdot := abs_p11dot_le d (p11PreparedFreqR Q y)
    have hdw : |p11dot d (p11PreparedFreqR Q y)| ≤ 2 * C.L + 1 := by
      rw [hd, one_mul] at hdot
      exact hdot.trans (hzero' y hy)
    have hval : p11euclid (p11scalar 2 (p11PreparedFreqR Q) d y) =
        |p11dot d (p11PreparedFreqR Q y)| ^ 2 := by
      unfold p11euclid KAM.Nekhoroshev.euclid p11scalar
      simp [← sq_abs]
    rw [hval]
    refine (pow_le_pow_left₀ (abs_nonneg _) hdw 2).trans ?_
    have : (1 : ℝ) ≤ 2 ^ ((p11PatchData D).mu + 1) := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg (2 * C.L + 1)]

end Pd

end KAM.Planetary

end
