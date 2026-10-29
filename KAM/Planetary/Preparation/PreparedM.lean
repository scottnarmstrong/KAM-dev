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

end Pd

end KAM.Planetary

end
