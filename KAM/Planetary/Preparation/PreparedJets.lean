/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Planetary.Preparation.PreparedCauchy
public import KAM.Planetary.Preparation.SlowSmall

/-!
# Jet inputs of the prepared frequency (P11A-P8b, `stepP:p11:pr-in`)

Helper lemmas, parametric in the slow datum `A` with `P11SlowSpecOf C Fast nu eps c A` (so they
apply to `p11SlowData D nu eps` through `P11SlowSpec`).  They are exported helpers, not the signed
`prepared` / `amount` (which are assembled in P8e).

* `p11_prin_g2_jet`, `p11_prin_g2_jet_log`: step pr-in (iii), the mixed Cauchy estimate for `g₂`
  with radii `s₂/4` in `J` and `ε/4` in `ρ̃`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section PrIn

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

private theorem p11Box_isOpen_aux {a b : ℕ} (c : P11CVec (a+b)) (r1 r2 : ℝ) :
    IsOpen (p11Box c r1 r2) := by
  rw [p11Box_eq]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

private theorem prin_prod_append (α γ : Fin n → ℕ) (f : ℕ → ℝ) :
    ∏ j : Fin (n+n), f (Fin.append α γ j) = (∏ i, f (α i)) * ∏ i, f (γ i) := by
  rw [Fin.prod_univ_add]; simp [Fin.append_left]

private theorem prin_poly_prod (α γ : Fin n → ℕ) (r1 r2 : ℝ) :
    ∏ j : Fin (n+n), p11BoxRad n n r1 r2 j ^ (Fin.append α γ j) =
      r1 ^ (∑ i, α i) * r2 ^ (∑ i, γ i) := by
  rw [Fin.prod_univ_add]
  simp [p11BoxRad, Fin.append_left, Finset.prod_pow_eq_pow_sum]

/-- Step pr-in (iii), sharp form: the mixed Cauchy estimate for `g₂` on the polydisc of radii
`s₂/4` (in `J`) and `ε/4` (in `ρ̃`). -/
theorem p11_prin_g2_jet {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hs2 : 0 < p11s2 C nu eps) (heps : 0 < eps) (hc : P11SlowSpecOf C Fast nu eps c A)
    (α γ : Fin n → ℕ) (J ρ : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4)
    (hρ : ‖ρ - (fun _ => (2*Real.pi*eps : ℂ))‖ < 5*eps/4) :
    ‖p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n+n)) (_ : Fin 1) => A.g2 I)
        (Fin.append J ρ)‖ ≤
      (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
        (c*eps^3*Real.log (1/eps)^(5*C.tau+2)) /
        ((p11s2 C nu eps/4) ^ (∑ i, α i) * (eps/4) ^ (∑ i, γ i)) := by
  obtain ⟨-, -, -, -, -, -, -, hdg, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbg, -, -⟩ := hc
  have hπ := Real.pi_gt_three
  have hUo := p11Box_isOpen_aux (Fin.append (KAM.realInclusion n C.J0)
    (fun _ : Fin n => (2*Real.pi*eps : ℂ))) (p11s2 C nu eps/2) (Real.pi*eps/2)
  have hR : ∀ j, 0 < p11BoxRad n n (p11s2 C nu eps/4) (eps/4) j := fun j => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11BoxRad] <;> positivity
  have hcl : {y : P11CVec (n+n) | ∀ j, ‖y j - Fin.append J ρ j‖ ≤
      p11BoxRad n n (p11s2 C nu eps/4) (eps/4) j} ⊆
      p11Box (Fin.append (KAM.realInclusion n C.J0) (fun _ : Fin n => (2*Real.pi*eps : ℂ)))
        (p11s2 C nu eps/2) (Real.pi*eps/2) := by
    intro y hy
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := hy (Fin.castAdd n i)
      simp only [p11BoxRad, Fin.append_left] at h1 ⊢
      have h2 : ‖J i - KAM.realInclusion n C.J0 i‖ < p11s2 C nu eps/4 :=
        lt_of_le_of_lt (by simpa using norm_le_pi_norm (J - KAM.realInclusion n C.J0) i) hJ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.castAdd n i)) (J i)
        (KAM.realInclusion n C.J0 i)
      linarith
    · have h1 := hy (Fin.natAdd n i)
      simp only [p11BoxRad, Fin.append_right] at h1 ⊢
      have h2 : ‖ρ i - (2*Real.pi*eps : ℂ)‖ < 5*eps/4 :=
        lt_of_le_of_lt (norm_le_pi_norm (ρ - fun _ : Fin n => (2*Real.pi*eps : ℂ)) i) hρ
      have := norm_sub_le_norm_sub_add_norm_sub (y (Fin.natAdd n i)) (ρ i) (2*Real.pi*eps : ℂ)
      nlinarith
  have hg : DifferentiableOn ℂ (fun (I : P11CVec (n+n)) (_ : Fin 1) => A.g2 I)
      (p11Box (Fin.append (KAM.realInclusion n C.J0) (fun _ : Fin n => (2*Real.pi*eps : ℂ)))
        (p11s2 C nu eps/2) (Real.pi*eps/2)) :=
    differentiableOn_pi.2 fun _ => hdg
  have hM : ∀ w ∈ p11Box (Fin.append (KAM.realInclusion n C.J0)
      (fun _ : Fin n => (2*Real.pi*eps : ℂ))) (p11s2 C nu eps/2) (Real.pi*eps/2),
      ‖(fun _ : Fin 1 => A.g2 w)‖ ≤ c*eps^3*Real.log (1/eps)^(5*C.tau+2) := fun w hw => by
    rw [pi_norm_const]; exact hbg w hw
  have h := p11PartialVec_norm_le_poly hUo hg hR hcl hM (Fin.append α γ)
  rw [prin_prod_append α γ (fun k => (k.factorial : ℝ)), prin_poly_prod] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- Step pr-in (iii), logarithmic form: `|∂_J^α ∂_ρ̃^γ g₂| ≤ c α! γ! ε^{3-|γ|} ℓ^{5τ₀+2+(τ₀+1)|α|}`
with a constant `c₀` depending only on the data (the lower bound of `s₂ ℓ^{τ₀+1}`). -/
theorem p11_prin_g2_jet_log (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c → P11SlowSpecOf C Fast nu eps c A →
      ∀ (α γ : Fin n → ℕ) (J ρ : P11CVec n),
        ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 →
        ‖ρ - (fun _ => (2*Real.pi*eps : ℂ))‖ < 5*eps/4 →
        ‖p11PartialVec (Fin.append α γ) (fun (I : P11CVec (n+n)) (_ : Fin 1) => A.g2 I)
            (Fin.append J ρ)‖ ≤
          (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
            (c * (4/c0) ^ (∑ i, α i) * 4 ^ (∑ i, γ i)) * (eps^3 / eps ^ (∑ i, γ i)) *
            Real.log (1/eps) ^ (5*C.tau+2+(C.tau+1)*((∑ i, α i : ℕ) : ℝ)) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hL0 : 0 < C.L := by linarith
  have hπ := Real.pi_pos
  have hν0 : 0 < nu := by linarith
  refine ⟨min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))),
    lt_min (div_pos (lt_min hrC0 (by positivity)) (by positivity)) (by positivity), ?_⟩
  intro Fast eps c A heps hεM hc hA α γ J ρ hJ hρ
  set c0 := min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))) with hc0def
  have hc00 : 0 < c0 :=
    lt_min (div_pos (lt_min hrC0 (by positivity)) (by positivity)) (by positivity)
  obtain ⟨-, -, hs2⟩ := slow_pos hC hnu heps hεM
  have hl1 := slow_log_ge_one hC heps hεM
  have hl0 : 0 < Real.log (1/eps) := by linarith
  have hlow := p11s2_log_lower hC (nu := nu) hν0 heps hεM
  have h := p11_prin_g2_jet hs2 heps hA α γ J ρ hJ hρ
  set l := Real.log (1/eps) with hl
  set t := l ^ (C.tau + 1) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hl0 _
  set a := ∑ i, α i
  set b := ∑ i, γ i
  have hS : (p11s2 C nu eps / 4)⁻¹ ≤ 4 / c0 * t := by
    have : c0 / (4 * t) ≤ p11s2 C nu eps / 4 := by
      calc c0 / (4 * t) = c0 / t / 4 := by field_simp
        _ ≤ p11s2 C nu eps / 4 := div_le_div_of_nonneg_right hlow (by norm_num)
    have h2 := inv_anti₀ (by positivity) this
    calc _ ≤ (c0 / (4 * t))⁻¹ := h2
      _ = 4 / c0 * t := by field_simp
  have hP : 0 ≤ (∏ i, ((α i).factorial : ℝ)) * ∏ i, ((γ i).factorial : ℝ) := by positivity
  have hq : l ^ (5 * C.tau + 2 + (C.tau + 1) * (a : ℝ)) = l ^ (5 * C.tau + 2) * t ^ a := by
    rw [Real.rpow_add hl0, Real.rpow_mul hl0.le, Real.rpow_natCast]
  rw [hq]
  refine h.trans ?_
  have e1 : ((p11s2 C nu eps / 4) ^ a * (eps / 4) ^ b)⁻¹ =
      ((p11s2 C nu eps / 4)⁻¹) ^ a * (4 ^ b / eps ^ b) := by
    rw [mul_inv, ← inv_pow, ← inv_pow, inv_div eps 4, div_pow]
  have hl' : 0 ≤ l ^ (5 * C.tau + 2) := (Real.rpow_pos_of_pos hl0 _).le
  have hX : 0 ≤ (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
      (c * eps ^ 3 * l ^ (5 * C.tau + 2)) := by positivity
  rw [div_eq_mul_inv, e1]
  calc _ ≤ (∏ i, ((α i).factorial : ℝ)) * (∏ i, ((γ i).factorial : ℝ)) *
        (c * eps ^ 3 * l ^ (5 * C.tau + 2)) * ((4 / c0 * t) ^ a * (4 ^ b / eps ^ b)) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

theorem p11_prin_K1_le (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    p11K1 C eps ≤ 6 / (Real.pi * C.sigma) * Real.log (1 / eps) := by
  obtain ⟨-, -, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hℓ : Real.log (1 / (eps * C.MF)) ≤ Real.log (1 / eps) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul heps.ne' hM0.ne']
    have := Real.log_nonneg hMF
    linarith
  exact mul_le_mul_of_nonneg_left hℓ (by positivity)

/-- `s₁⁻¹ ≤ k ℓ^{τ₀+1}`. -/
theorem p11_prin_s1_inv (hC : P11SecularSpec D C) :
    ∃ k : ℝ, 0 < k ∧ ∀ {eps : ℝ}, 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      (p11s1 C eps)⁻¹ ≤ k * Real.log (1 / eps) ^ (C.tau + 1) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hL0 : 0 < C.L := by linarith
  have hA : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  refine ⟨(6 / (Real.pi * C.sigma)) ^ (C.tau + 1) / min C.rC (C.gamma / (4 * C.L)),
    by have := Real.rpow_pos_of_pos (show 0 < 6 / (Real.pi * C.sigma) by positivity) (C.tau + 1)
       positivity, ?_⟩
  intro eps heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith [slow_log_ge_one hC heps hεM]
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_pos_of_pos hl0 _
  have hX : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h := p11s1_log_lower hC heps hεM
  have h2 := inv_anti₀ (by positivity) h
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- `(1/α₁)` grows at most like `ℓ^{τ₀}`. -/
theorem p11_prin_alpha1_inv (hC : P11SecularSpec D C) :
    ∃ k : ℝ, 0 < k ∧ ∀ {eps : ℝ}, 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      (p11Alpha1 C eps)⁻¹ ≤ k * Real.log (1 / eps) ^ C.tau := by
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, -, -, -⟩ := fast_consts hC
  have hc : 0 < 6 / (Real.pi * C.sigma) := by positivity
  refine ⟨2 / C.gamma * (6 / (Real.pi * C.sigma)) ^ C.tau,
    by have := Real.rpow_pos_of_pos hc C.tau; positivity, ?_⟩
  intro eps heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith [slow_log_ge_one hC heps hεM]
  have hK1 := p11K1_ge_one hC heps hεM
  have hK0 : 0 < p11K1 C eps := by linarith
  have hKl := p11_prin_K1_le hC heps hεM
  have h1 : p11K1 C eps ^ C.tau ≤
      (6 / (Real.pi * C.sigma)) ^ C.tau * Real.log (1 / eps) ^ C.tau := by
    rw [← Real.mul_rpow hc.le hl0.le]; exact Real.rpow_le_rpow hK0.le hKl hτ0.le
  have : (p11Alpha1 C eps)⁻¹ = 2 / C.gamma * p11K1 C eps ^ C.tau := by
    unfold p11Alpha1
    rw [Real.rpow_neg hK0.le]; field_simp
  rw [this]
  calc _ ≤ 2 / C.gamma * ((6 / (Real.pi * C.sigma)) ^ C.tau * Real.log (1 / eps) ^ C.tau) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- `(1/d₁)` grows at most like `ℓ^{τ₀+1}`. -/
theorem p11_prin_d1_inv (hC : P11SecularSpec D C) :
    ∃ k : ℝ, 0 < k ∧ ∀ {eps : ℝ}, 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      (p11d1 C eps)⁻¹ ≤ k * Real.log (1 / eps) ^ (C.tau + 1) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨k, hk, hs1⟩ := p11_prin_s1_inv hC
  refine ⟨k / C.sigma + (C.rz ^ 2)⁻¹, by positivity, ?_⟩
  intro eps heps hεM
  have hl1 := slow_log_ge_one hC heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith
  have hq1 : 1 ≤ Real.log (1 / eps) ^ (C.tau + 1) := Real.one_le_rpow hl1 (by linarith)
  have hs := (slow_pos hC (nu := 1) le_rfl heps hεM).2.1
  have hd : 0 < p11d1 C eps := lt_min (by positivity) (by positivity)
  have hmin : (p11d1 C eps)⁻¹ ≤ (p11s1 C eps * C.sigma)⁻¹ + (C.rz ^ 2)⁻¹ := by
    unfold p11d1
    rcases min_choice (p11s1 C eps * C.sigma) (C.rz ^ 2) with h | h <;> rw [h]
    · have : 0 ≤ (C.rz ^ 2)⁻¹ := by positivity
      linarith
    · have : 0 ≤ (p11s1 C eps * C.sigma)⁻¹ := by positivity
      linarith
  refine hmin.trans ?_
  have h1 : (p11s1 C eps * C.sigma)⁻¹ ≤ k / C.sigma * Real.log (1 / eps) ^ (C.tau + 1) := by
    calc (p11s1 C eps * C.sigma)⁻¹ = (p11s1 C eps)⁻¹ * C.sigma⁻¹ := mul_inv _ _
      _ ≤ (k * Real.log (1 / eps) ^ (C.tau + 1)) * C.sigma⁻¹ :=
          mul_le_mul_of_nonneg_right (hs1 heps hεM) (by positivity)
      _ = _ := by ring
  have h2 : (C.rz ^ 2)⁻¹ ≤ (C.rz ^ 2)⁻¹ * Real.log (1 / eps) ^ (C.tau + 1) :=
    le_mul_of_one_le_right (by positivity) hq1
  nlinarith

/-- Step pr-in: `η₁ ≤ c ε ℓ^{2τ₀+1}`. -/
theorem p11_prin_eta1_le (hC : P11SecularSpec D C) :
    ∃ k : ℝ, 0 < k ∧ ∀ {eps : ℝ}, 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      p11eta1 C eps ≤ k * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨ka, hka, ha⟩ := p11_prin_alpha1_inv hC
  obtain ⟨kd, hkd, hd⟩ := p11_prin_d1_inv hC
  refine ⟨400 * (1 + n) * C.MF ^ 2 / (2 * Real.pi) * (ka * kd), by positivity, ?_⟩
  intro eps heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith [slow_log_ge_one hC heps hεM]
  have hK1 := p11K1_ge_one hC heps hεM
  have hK0 : 0 < p11K1 C eps := by linarith
  have hα : 0 < p11Alpha1 C eps := by
    unfold p11Alpha1; have := Real.rpow_pos_of_pos hK0 (-C.tau); positivity
  have hs := (slow_pos hC (nu := 1) le_rfl heps hεM).2.1
  have hd0 : 0 < p11d1 C eps := lt_min (by positivity) (by positivity)
  have e : p11eta1 C eps = 400 * (1 + n) * C.MF ^ 2 / (2 * Real.pi) * eps *
      ((p11Alpha1 C eps)⁻¹ * (p11d1 C eps)⁻¹) := by
    unfold p11eta1; field_simp
  rw [e]
  have hprod := mul_le_mul (ha heps hεM) (hd heps hεM) (by positivity) (by positivity)
  have hpow : Real.log (1 / eps) ^ (2 * C.tau + 1) =
      Real.log (1 / eps) ^ C.tau * Real.log (1 / eps) ^ (C.tau + 1) := by
    rw [← Real.rpow_add hl0]; congr 1; ring
  rw [hpow]
  calc _ ≤ 400 * (1 + n) * C.MF ^ 2 / (2 * Real.pi) * eps *
        (ka * Real.log (1 / eps) ^ C.tau * (kd * Real.log (1 / eps) ^ (C.tau + 1))) := by
        gcongr
    _ = _ := by ring

/-- Step pr-in (ii): `|∂_J^α ∂_ρ̃ Ẑ| ≤ c α! ε ℓ^{2τ₀+1+(τ₀+1)|α|}` (the `ρ̃`-derivative of `Z`
in the coordinates of `P11SlowSpecOf`), with `c` depending on `α` only through `(∑ α)`. -/
theorem p11_prin_Z_jet (hC : P11SecularSpec D C) :
    ∃ k : ℝ, 0 < k ∧ ∀ {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c → P11SlowSpecOf C Fast nu eps c A →
      ∀ (α : Fin n → ℕ) (J : P11CVec n),
        ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
        ∀ ρ : P11CVec n, ‖ρ - (fun _ => (2*Real.pi*eps : ℂ))‖ < Real.pi*eps →
        ‖p11PartialVec α
            (fun J => fun i : Fin n =>
              fderiv ℂ (fun rho : P11CVec n => A.Z (Fin.append J rho)) ρ (Pi.single i 1)) J‖ ≤
          (∏ i, ((α i).factorial : ℝ)) * (c * (1 + k) * (4 * k) ^ (∑ i, α i)) * eps *
            Real.log (1 / eps) ^ (2 * C.tau + 1 + (C.tau + 1) * ((∑ i, α i : ℕ) : ℝ)) := by
  obtain ⟨hγ0, hτ0, -, -, -, -, -, -, -, hMF⟩ := fast_consts hC
  obtain ⟨k1, hk1, hs1⟩ := p11_prin_s1_inv hC
  obtain ⟨ke, hke, he⟩ := p11_prin_eta1_le hC
  refine ⟨max k1 ke, lt_max_of_lt_left hk1, ?_⟩
  intro Fast nu eps c A heps hεM hc hA α J hJ ρ hρ
  obtain ⟨-, -, -, -, hZ, -⟩ := hA
  have h := hZ α J hJ ρ hρ
  have hl1 := slow_log_ge_one hC heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith
  set l := Real.log (1 / eps) with hl
  set a := ∑ i, α i
  have hs := (slow_pos hC (nu := 1) le_rfl heps hεM).2.1
  have hq1 : 1 ≤ l ^ (2 * C.tau + 1) := Real.one_le_rpow hl1 (by linarith)
  have hη : p11eta1 C eps ≤ ke * eps * l ^ (2 * C.tau + 1) := he heps hεM
  have hε : eps + p11eta1 C eps ≤ (1 + max k1 ke) * eps * l ^ (2 * C.tau + 1) := by
    have h1 : eps ≤ eps * l ^ (2 * C.tau + 1) := le_mul_of_one_le_right heps.le hq1
    have h2 : ke * eps * l ^ (2 * C.tau + 1) ≤ max k1 ke * eps * l ^ (2 * C.tau + 1) := by
      gcongr; exact le_max_right _ _
    nlinarith
  have h4 : 4 / p11s1 C eps ≤ 4 * max k1 ke * l ^ (C.tau + 1) := by
    have := hs1 heps hεM
    calc 4 / p11s1 C eps = 4 * (p11s1 C eps)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 4 * (k1 * l ^ (C.tau + 1)) := by gcongr
      _ ≤ 4 * max k1 ke * l ^ (C.tau + 1) := by
        rw [← mul_assoc]; gcongr; exact le_max_left _ _
  have hq : l ^ (2 * C.tau + 1 + (C.tau + 1) * (a : ℝ)) =
      l ^ (2 * C.tau + 1) * (l ^ (C.tau + 1)) ^ a := by
    rw [Real.rpow_add hl0, Real.rpow_mul hl0.le, Real.rpow_natCast]
  rw [hq]
  have hP : 0 ≤ ∏ i, ((α i).factorial : ℝ) := by positivity
  refine h.trans ?_
  calc c * (eps + p11eta1 C eps) * (∏ i, ((α i).factorial : ℝ)) * (4 / p11s1 C eps) ^ a
      ≤ c * ((1 + max k1 ke) * eps * l ^ (2 * C.tau + 1)) * (∏ i, ((α i).factorial : ℝ)) *
          (4 * max k1 ke * l ^ (C.tau + 1)) ^ a := by gcongr
    _ = _ := by rw [mul_pow]; ring

private theorem prin_coth_ge_one {x : ℝ} (hx : 0 < x) : 1 ≤ KAM.Weighted.coth x := by
  unfold KAM.Weighted.coth
  exact (one_le_div (Real.sinh_pos_iff.2 hx)).2 (Real.sinh_lt_cosh x).le

/-- The constant term `C` of the secular normal form is bounded by `M_F` on `D(J₀, 2 r_C)`: it is
the fast mean of `F` at `z = 0`. -/
theorem p11_prin_C_bound (hC : P11SecularSpec D C) (J : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < 2 * C.rC) : ‖C.C J‖ ≤ C.MF := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFd, hFb, -, -,
    hmean, -⟩ := hC
  have h0 := hmean J (mem_ball_iff_norm.2 hJ) 0 (by simpa using hrz0)
  have hz : (‖(0 : P11Phase n)‖ / C.rz) ^ 4 = 0 := by simp
  have hzero : ∑ i, C.Omega J i * (((0 : P11Phase n).1 i) ^ 2 + ((0 : P11Phase n).2 i) ^ 2) / 2 =
      0 := by simp
  rw [hz, hzero, mul_zero, sub_zero] at h0
  have h1 : ‖p11FastMean C.F J 0 - C.C J‖ ≤ 0 := h0
  have h2 : p11FastMean C.F J 0 = C.C J := sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  rw [← h2]
  unfold p11FastMean
  refine KAM.norm_torusAverage_le fun θ _ => ?_
  have hmem : (Fin.append (KAM.realInclusion n θ) (0 : P11Phase n).1,
      Fin.append J (0 : P11Phase n).2) ∈ p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Fin.append_left] using KAM.ofReal_mem_complexStrip (n := n)
        (by positivity : (0 : ℝ) < 2*C.sigma) θ
    · simpa [Fin.append_left] using hJ
    · simp only [Prod.fst_zero, Prod.snd_zero, Fin.append_right, Pi.zero_apply]
      rw [show (fun _ : Fin n => (0 : ℂ)) = (0 : P11CVec n) from rfl, norm_zero]; exact hrz0
    · simp only [Prod.fst_zero, Prod.snd_zero, Fin.append_right, Pi.zero_apply]
      rw [show (fun _ : Fin n => (0 : ℂ)) = (0 : P11CVec n) from rfl, norm_zero]; exact hrz0
  refine (hFb _ hmem).trans ?_
  have hc := prin_coth_ge_one (show 0 < Real.pi * C.sigma by positivity)
  have hp : 1 ≤ KAM.Weighted.coth (Real.pi * C.sigma) ^ n := one_le_pow₀ hc
  exact div_le_self (by linarith) hp

private theorem prin_slice_differentiable (ρ0 : P11CVec n) :
    Differentiable ℂ (fun J : P11CVec n => (Fin.append J ρ0 : P11CVec (n+n))) := by
  refine differentiable_pi.2 fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [Fin.append_left] using differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => ℂ) i
  · simpa [Fin.append_right] using differentiable_const (𝕜 := ℂ) (ρ0 i)

/-- The constant term `C` is holomorphic on `D(J₀, s₂)`: it is read off `h₀ = C.h + ε(C + …)`
on the slice `ρ̃ = 2πε` of the slow box. -/
theorem p11_prin_C_diff (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsmall : 2 * Real.pi * eps < Real.pi * C.rz ^ 2 / 16)
    (hA : P11SlowSpecOf C Fast nu eps c A) :
    DifferentiableOn ℂ C.C (ball (KAM.realInclusion n C.J0) (p11s2 C nu eps)) := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨-, -, hform, hZd, -, -, hh0d, -⟩ := hA
  obtain ⟨-, -, ⟨-, hΩd⟩, -, hhd, -⟩ := id hC
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  set ρ0 : P11CVec n := fun _ => (2 * Real.pi * eps : ℂ) with hρ0
  have hsub : ball (KAM.realInclusion n C.J0) (p11s2 C nu eps) ⊆
      ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    ball_subset_ball (by linarith [hspec.1])
  have hmemV : ∀ J ∈ ball (KAM.realInclusion n C.J0) (p11s2 C nu eps),
      (Fin.append J ρ0 : P11CVec (n+n)) ∈ p11Box (Fin.append (KAM.realInclusion n C.J0)
        (fun _ : Fin n => (2*Real.pi*eps : ℂ))) (p11s2 C nu eps) (Real.pi*eps) := by
    intro J hJ
    rw [mem_ball_iff_norm] at hJ
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [Fin.append_left]
      exact lt_of_le_of_lt (norm_le_pi_norm (J - KAM.realInclusion n C.J0) i) hJ
    · simp only [Fin.append_right, hρ0, sub_self, norm_zero]
      positivity
  have hZmem : ∀ J ∈ ball (KAM.realInclusion n C.J0) (p11s2 C nu eps),
      (Fin.append J ρ0 : P11CVec (n+n)) ∈
        {I : P11CVec (n+n) |
          ‖(fun i : Fin n => I (Fin.castAdd n i)) - KAM.realInclusion n C.J0‖ < p11s1 C eps/2 ∧
          ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi * C.rz ^ 2 / 16} := by
    intro J hJ
    rw [mem_ball_iff_norm] at hJ
    refine ⟨?_, ?_⟩
    · have hc : (fun i : Fin n => (Fin.append J ρ0 : P11CVec (n+n)) (Fin.castAdd n i)) = J := by
        funext i; simp
      rw [hc]; linarith [hspec.1]
    · have hc : (fun i : Fin n => (Fin.append J ρ0 : P11CVec (n+n)) (Fin.natAdd n i)) = ρ0 := by
        funext i; simp
      rw [hc]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_) hsmall
      simp [hρ0, abs_of_pos heps, abs_of_pos Real.pi_pos]
  have hsl := (prin_slice_differentiable ρ0).differentiableOn (s := ball (KAM.realInclusion n C.J0)
    (p11s2 C nu eps))
  have hZ' := hZd.comp hsl hZmem
  have hh0' := hh0d.comp hsl hmemV
  have hhd' := hhd.mono hsub
  have hΩ' : DifferentiableOn ℂ (fun J => ∑ i, C.Omega J i)
      (ball (KAM.realInclusion n C.J0) (p11s2 C nu eps)) :=
    DifferentiableOn.fun_sum fun i _ => (differentiableOn_pi.1 hΩd i).mono hsub
  have h1 : DifferentiableOn ℂ (fun J : P11CVec n => A.h0 (Fin.append J ρ0) - C.h J)
      (ball (KAM.realInclusion n C.J0) (p11s2 C nu eps)) := hh0'.sub hhd'
  have h2 := h1.mul_const (eps : ℂ)⁻¹
  have h3 := hΩ'.const_mul (eps : ℂ)
  have hex : DifferentiableOn ℂ (fun J : P11CVec n =>
      (A.h0 (Fin.append J ρ0) - C.h J) * (eps : ℂ)⁻¹ - (eps : ℂ) * ∑ i, C.Omega J i -
        A.Z (Fin.append J ρ0)) (ball (KAM.realInclusion n C.J0) (p11s2 C nu eps)) :=
    (h2.sub h3).sub hZ'
  refine hex.congr fun J hJ => ?_
  have h := hform _ (hmemV J hJ)
  have hc : (fun i : Fin n => (Fin.append J ρ0 : P11CVec (n+n)) (Fin.castAdd n i)) = J := by
    funext i; simp
  rw [hc] at h
  have hsum : ∑ i : Fin n, C.Omega J i / (2 * Real.pi) *
      (Fin.append J ρ0 : P11CVec (n+n)) (Fin.natAdd n i) = (eps : ℂ) * ∑ i, C.Omega J i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.append_right, hρ0]
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast; field_simp
  rw [hsum] at h
  have he : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
  rw [h]
  field_simp
  ring

/-- Step pr-in (i), sharp form: `|∂_J^β C| ≤ M_F β! (4/s₂)^{|β|}` on `|J - J₀| < s₂/4`
(Cauchy radius `s₂/4`; the constant term `C` of `Ĝ₀`). -/
theorem p11_prin_C_jet (hC : P11SecularSpec D C) {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hnu : 1 ≤ nu) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsmall : 2 * Real.pi * eps < Real.pi * C.rz ^ 2 / 16)
    (hA : P11SlowSpecOf C Fast nu eps c A) (β : Fin n → ℕ) (J : P11CVec n)
    (hJ : ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4) :
    ‖p11PartialVec β (fun (J : P11CVec n) (_ : Fin 1) => C.C J) J‖ ≤
      (∏ i, ((β i).factorial : ℝ)) * C.MF / (p11s2 C nu eps / 4) ^ (∑ i, β i) := by
  obtain ⟨hK, hs1, hs2⟩ := slow_pos hC hnu heps hεM
  have hspec := p11s2_spec hC hK
  have hs1r := p11s1_le C eps
  have hdiff := p11_prin_C_diff hC hnu heps hεM hsmall hA
  have hg : DifferentiableOn ℂ (fun (J : P11CVec n) (_ : Fin 1) => C.C J)
      (ball (KAM.realInclusion n C.J0) (p11s2 C nu eps)) := differentiableOn_pi.2 fun _ => hdiff
  have hcl : closedBall J (p11s2 C nu eps / 4) ⊆
      ball (KAM.realInclusion n C.J0) (p11s2 C nu eps) := by
    intro y hy
    rw [mem_closedBall_iff_norm] at hy
    rw [mem_ball_iff_norm]
    have := norm_sub_le_norm_sub_add_norm_sub y J (KAM.realInclusion n C.J0)
    linarith
  have hM : ∀ w ∈ ball (KAM.realInclusion n C.J0) (p11s2 C nu eps),
      ‖(fun _ : Fin 1 => C.C w)‖ ≤ C.MF := fun w hw => by
    rw [pi_norm_const]
    refine p11_prin_C_bound hC w ?_
    rw [mem_ball_iff_norm] at hw
    obtain ⟨-, -, -, hrC0, -⟩ := fast_consts hC
    linarith [hspec.1]
  exact p11PartialVec_norm_le isOpen_ball hg (by positivity) hcl hM β

/-- Step pr-in (i), logarithmic form: `|∂_J^β C| ≤ c β! ℓ^{(τ₀+1)|β|}`. -/
theorem p11_prin_C_jet_log (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) →
      2 * Real.pi * eps < Real.pi * C.rz ^ 2 / 16 → P11SlowSpecOf C Fast nu eps c A →
      ∀ (β : Fin n → ℕ) (J : P11CVec n),
        ‖J - KAM.realInclusion n C.J0‖ < p11s2 C nu eps / 4 →
        ‖p11PartialVec β (fun (J : P11CVec n) (_ : Fin 1) => C.C J) J‖ ≤
          (∏ i, ((β i).factorial : ℝ)) * C.MF * (4 / c0) ^ (∑ i, β i) *
            Real.log (1 / eps) ^ ((C.tau + 1) * ((∑ i, β i : ℕ) : ℝ)) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hL0 : 0 < C.L := by linarith
  have hπ := Real.pi_pos
  have hν0 : 0 < nu := by linarith
  refine ⟨min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))),
    lt_min (div_pos (lt_min hrC0 (by positivity)) (by positivity)) (by positivity), ?_⟩
  intro Fast eps c A heps hεM hsmall hA β J hJ
  set c0 := min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))) with hc0def
  have hc00 : 0 < c0 :=
    lt_min (div_pos (lt_min hrC0 (by positivity)) (by positivity)) (by positivity)
  obtain ⟨-, -, hs2⟩ := slow_pos hC hnu heps hεM
  have hl1 := slow_log_ge_one hC heps hεM
  have hl0 : 0 < Real.log (1/eps) := by linarith
  have hlow := p11s2_log_lower hC (nu := nu) hν0 heps hεM
  have h := p11_prin_C_jet hC hnu heps hεM hsmall hA β J hJ
  set l := Real.log (1/eps) with hl
  set t := l ^ (C.tau + 1) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hl0 _
  set a := ∑ i, β i
  have hS : (p11s2 C nu eps / 4)⁻¹ ≤ 4 / c0 * t := by
    have : c0 / (4 * t) ≤ p11s2 C nu eps / 4 := by
      calc c0 / (4 * t) = c0 / t / 4 := by field_simp
        _ ≤ p11s2 C nu eps / 4 := div_le_div_of_nonneg_right hlow (by norm_num)
    have h2 := inv_anti₀ (by positivity) this
    calc _ ≤ (c0 / (4 * t))⁻¹ := h2
      _ = 4 / c0 * t := by field_simp
  have hq : l ^ ((C.tau + 1) * (a : ℝ)) = t ^ a := by
    rw [Real.rpow_mul hl0.le, Real.rpow_natCast]
  rw [hq]
  refine h.trans ?_
  rw [div_eq_mul_inv, ← inv_pow]
  have hP : 0 ≤ (∏ i, ((β i).factorial : ℝ)) * C.MF := by positivity
  calc _ ≤ (∏ i, ((β i).factorial : ℝ)) * C.MF * (4 / c0 * t) ^ a := by gcongr
    _ = _ := by rw [mul_pow]; ring

end PrIn

end KAM.Planetary

end
