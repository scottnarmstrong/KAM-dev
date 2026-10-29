/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTubeMain
public import KAM.Planetary.Preparation.SlowSmall

/-!
# Asymptotic smallness for the wrapper (P11A-P10, `stepP:p11:wr-nu`)

Eventual (as `ε → 0⁺`) validity of the numerical hypotheses of `p11_wr_tube`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace KAM.Planetary

section Asym

variable {n : ℕ}

/-- Eventually `ε^a ℓ^b ≤ δ`. -/
theorem p11_ev_pow_log {a b δ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps^a*Real.log (1/eps)^b ≤ δ :=
  ((e4 ha hb).eventually (gt_mem_nhds hδ)).mono fun _ h => h.le

theorem p11_ev_lt {r : ℝ} (hr : 0 < r) : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps < r :=
  eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hr)

/-- `hP1`, `hP2` of `p11_wr_tube` hold for small `ε`. -/
theorem p11_ev_slowDisp (c τ : ℝ) (hc : 0 ≤ c) (hτ : 0 ≤ τ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps →
      c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps ∧
      c*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps := by
  filter_upwards [p11_ev_pow_log (a := 1/2) (b := 3*τ+1) (δ := 1/(c+1)) (by norm_num)
    (by linarith) (by positivity), p11_ev_lt one_pos] with eps h h1 heps
  have hℓ : 0 ≤ Real.log (1/eps)^(3*τ+1) := Real.rpow_nonneg (by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos heps.le h1.le
    linarith) _
  have e1 : eps^(3/2 : ℝ) = eps*eps^(1/2 : ℝ) := by
    rw [← Real.rpow_one_add' heps.le (by norm_num)]; norm_num
  have hkey : c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ 1 := by
    have h2 : c*(eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1)) ≤ c*(1/(c+1)) :=
      mul_le_mul_of_nonneg_left h hc
    calc c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1) = c*(eps^(1/2 : ℝ)*_) := by ring
      _ ≤ c*(1/(c+1)) := h2
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hP1 : c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps := by
    rw [e1]
    calc c*(eps*eps^(1/2 : ℝ))*Real.log (1/eps)^(3*τ+1) =
        eps*(c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1)) := by ring
      _ ≤ eps*1 := mul_le_mul_of_nonneg_left hkey heps.le
      _ = eps := mul_one _
  refine ⟨hP1, le_trans ?_ hP1⟩
  have : eps^(5/2 : ℝ) ≤ eps^(3/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge heps h1.le (by norm_num)
  have h3 : 0 ≤ Real.log (1/eps)^(3*τ+1) := hℓ
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) h3

/-- `1/α₁ ≤ (2/γ) c₃^τ ℓ^τ` for small `ε`. -/
theorem p11_inv_alpha_le {D : P11Physical n} (hC : P11SecularSpec D (p11SecularData D))
    {eps : ℝ} (heps : 0 < eps) (hεM : eps*(p11SecularData D).MF ≤ Real.exp (-1)) :
    (p11Alpha1 (p11SecularData D) eps)⁻¹ ≤ 2/(p11SecularData D).gamma *
      ((6/(Real.pi*(p11SecularData D).sigma))^(p11SecularData D).tau *
        Real.log (1/eps)^(p11SecularData D).tau) := by
  set C := p11SecularData D with hCd
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hK1 := p11K1_ge_one hC heps hεM
  have hℓΛ : Real.log (1/(eps*C.MF)) ≤ Real.log (1/eps) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul heps.ne' hM0.ne']
    have := Real.log_nonneg hMF
    linarith
  have hc30 : 0 < 6/(Real.pi*C.sigma) := by positivity
  have hKΛ : p11K1 C eps ≤ 6/(Real.pi*C.sigma)*Real.log (1/eps) :=
    mul_le_mul_of_nonneg_left hℓΛ hc30.le
  have hl0 : 0 ≤ Real.log (1/eps) := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM); linarith
  have hK0 : 0 ≤ p11K1 C eps := by linarith
  unfold p11Alpha1
  rw [mul_inv, Real.rpow_neg hK0, inv_inv, ← Real.mul_rpow hc30.le hl0]
  have h2 : p11K1 C eps ^ C.tau ≤ (6/(Real.pi*C.sigma)*Real.log (1/eps))^C.tau :=
    Real.rpow_le_rpow hK0 hKΛ hτ0.le
  rw [Real.mul_rpow hc30.le hl0] at h2 ⊢
  have : (C.gamma/2)⁻¹ = 2/C.gamma := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `hR1`, `hR2` of `p11_wr_tube` hold for small `ε`. -/
theorem p11_ev_tube {D : P11Physical n} (hC : P11SecularSpec D (p11SecularData D)) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps →
      eps*(p11SecularData D).MF ≤ Real.exp (-1) →
      (2*eps + 3*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
        (p11SecularData D).sigma) ≤ 7*Real.pi*p11PhysicalDelta D/4) ∧
      (3*n*eps + 2*n*(9*eps*(p11SecularData D).MF/(2*Real.pi*
        p11Alpha1 (p11SecularData D) eps*(p11SecularData D).rz))^2 ≤ p11PhysicalDelta D) := by
  set C := p11SecularData D with hCd
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  have hδ0 : 0 < p11PhysicalDelta D := (forward_tube D (p11_zeta_pos D)).choose_spec.1
  set δ := p11PhysicalDelta D with hδ
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast D.n_ge
  have hpi := Real.pi_gt_three
  set c3 := 6/(Real.pi*C.sigma) with hc3
  have hc30 : 0 < c3 := by positivity
  set Xs := 3*C.MF*c3^C.tau/(Real.pi*C.sigma*C.gamma) with hXs
  set Xz := 9*C.MF*c3^C.tau/(Real.pi*C.rz*C.gamma) with hXz
  have hXs0 : 0 < Xs := by positivity
  have hXz0 : 0 < Xz := by positivity
  set η := min (min (δ/Xs) (1/Xz)) (δ/(4*n*Xz)) with hη
  have hη0 : 0 < η := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  filter_upwards [p11_ev_pow_log (a := 1) (b := C.tau) (δ := η) one_pos hτ0.le hη0,
    p11_ev_lt (r := δ/(6*n)) (by positivity)] with eps hB hε1 heps hεM
  rw [Real.rpow_one] at hB
  have hℓ0 : 0 ≤ Real.log (1/eps)^C.tau := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM)
    exact Real.rpow_nonneg (by linarith) _
  have hia := p11_inv_alpha_le hC heps hεM
  have hα : 0 < p11Alpha1 C eps := by
    have hK := p11K1_ge_one hC heps hεM
    unfold p11Alpha1
    have : 0 < p11K1 C eps ^ (-C.tau) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hd1 : 3*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.sigma) ≤ Xs*(eps*Real.log (1/eps)^C.tau) := by
    have e : 3*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.sigma) =
        3*C.MF*eps/(2*Real.pi*C.sigma) * (p11Alpha1 C eps)⁻¹ := by field_simp
    rw [e]
    calc _ ≤ 3*C.MF*eps/(2*Real.pi*C.sigma) * (2/C.gamma*(c3^C.tau*Real.log (1/eps)^C.tau)) :=
          mul_le_mul_of_nonneg_left hia (by positivity)
      _ = _ := by rw [hXs]; field_simp
  have hd2 : 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) ≤ Xz*(eps*Real.log (1/eps)^C.tau) := by
    have e : 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) =
        9*C.MF*eps/(2*Real.pi*C.rz) * (p11Alpha1 C eps)⁻¹ := by field_simp
    rw [e]
    calc _ ≤ 9*C.MF*eps/(2*Real.pi*C.rz) * (2/C.gamma*(c3^C.tau*Real.log (1/eps)^C.tau)) :=
          mul_le_mul_of_nonneg_left hia (by positivity)
      _ = _ := by rw [hXz]; field_simp
  have hBη1 : eps*Real.log (1/eps)^C.tau ≤ δ/Xs :=
    hB.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hBη2 : eps*Real.log (1/eps)^C.tau ≤ 1/Xz :=
    hB.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hBη3 : eps*Real.log (1/eps)^C.tau ≤ δ/(4*n*Xz) := hB.trans (min_le_right _ _)
  have hXsB : Xs*(eps*Real.log (1/eps)^C.tau) ≤ δ := by
    rw [le_div_iff₀ hXs0] at hBη1; linarith
  have hXzB : Xz*(eps*Real.log (1/eps)^C.tau) ≤ 1 := by
    rw [le_div_iff₀ hXz0] at hBη2; linarith
  have hXzB3 : 4*n*(Xz*(eps*Real.log (1/eps)^C.tau)) ≤ δ := by
    rw [le_div_iff₀ (by positivity)] at hBη3; linarith
  have hεδ : 6*n*eps ≤ δ := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 6*n)).1 hε1; linarith
  set d := 9*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.rz) with hd
  have hd0 : 0 ≤ d := by positivity
  have hdle : d ≤ 1 := hd2.trans hXzB
  have hd2' : d^2 ≤ d := by
    calc d^2 = d*d := sq d
      _ ≤ d*1 := mul_le_mul_of_nonneg_left hdle hd0
      _ = d := mul_one d
  have hne : 2*eps ≤ n*eps := mul_le_mul_of_nonneg_right hn heps.le
  have h5 : 5*δ ≤ 7*Real.pi*δ/4 := by nlinarith [hpi, hδ0]
  refine ⟨?_, ?_⟩
  · have h1 : 3*eps*C.MF/(2*Real.pi*p11Alpha1 C eps*C.sigma) ≤ δ := hd1.trans hXsB
    linarith
  · have h1 : 2*n*d^2 ≤ 2*n*(Xz*(eps*Real.log (1/eps)^C.tau)) :=
      mul_le_mul_of_nonneg_left (hd2'.trans hd2) (by positivity)
    linarith

theorem p11_rpow_natpow {eps : ℝ} (heps : 0 < eps) (k : ℕ) (x : ℝ) :
    ((eps ^ k : ℝ)) ^ x = eps ^ ((k : ℝ) * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul heps.le]

theorem p11_rpow_scale {eps : ℝ} (heps : 0 < eps) {βJ : ℝ} (hβ : 0 < βJ) (k : ℕ) (x : ℝ) :
    ((1/2 : ℝ)*eps ^ k*βJ) ^ x = (βJ/2) ^ x * eps ^ ((k : ℝ) * x) := by
  have : (1/2 : ℝ)*eps ^ k*βJ = (βJ/2)*eps ^ k := by ring
  rw [this, Real.mul_rpow (by positivity) (by positivity), p11_rpow_natpow heps]

/-- The threshold and displacement inequalities of `wr-nu`, for small `ε`. -/
theorem p11_ev_thr {c q βJ cstar cD B0 G0 nu : ℝ} {mu : ℕ} (hc : 0 < c) (hq : 0 ≤ q)
    (hβ : 0 < βJ) (hcs : 0 < cstar) (hcD : 0 < cD) (hG0 : 0 ≤ G0)
    (hν1 : ((mu + 2 : ℕ) : ℝ)*B0 + 2 ≤ nu) (hν2 : 2*((mu + 2 : ℕ) : ℝ)*G0 + 4 ≤ nu) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps →
      c*eps^(nu+3/2)*Real.log (1/eps)^q ≤ cstar*((1/2 : ℝ)*eps^(mu+2)*βJ)^B0 ∧
      cD*(c*eps^(nu+3/2)*Real.log (1/eps)^q)^(1/2 : ℝ)*((1/2 : ℝ)*eps^(mu+2)*βJ)^(-G0) ≤ 1/2 := by
  set m : ℝ := ((mu + 2 : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  set K1 : ℝ := cstar*(βJ/2)^B0 with hK1
  have hK10 : 0 < K1 := by positivity
  set K2 : ℝ := cD*c^(1/2 : ℝ)*(βJ/2)^(-G0) with hK2
  have hK20 : 0 < K2 := by positivity
  filter_upwards [p11_ev_pow_log (a := 1/2) (b := q) (δ := K1/c) (by norm_num) hq (by positivity),
    p11_ev_pow_log (a := 1/2) (b := q/2) (δ := 1/(2*K2)) (by norm_num) (by positivity)
      (by positivity), p11_ev_lt one_pos] with eps h1 h2 h3 heps
  have hℓ : 0 ≤ Real.log (1/eps) := by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos heps.le h3.le
    linarith
  have hℓq : 0 ≤ Real.log (1/eps)^q := Real.rpow_nonneg hℓ _
  have hmon : ∀ x : ℝ, 1/2 ≤ x → eps^x ≤ eps^(1/2 : ℝ) := fun x hx =>
    Real.rpow_le_rpow_of_exponent_ge heps h3.le hx
  refine ⟨?_, ?_⟩
  · have e1 : eps^(nu+3/2) = eps^(m*B0)*eps^(nu+3/2-m*B0) := by
      rw [← Real.rpow_add heps]; ring_nf
    rw [p11_rpow_scale heps hβ, e1]
    have h4 : eps^(nu+3/2-m*B0) ≤ eps^(1/2 : ℝ) := hmon _ (by linarith)
    have h5 : c*eps^(1/2 : ℝ)*Real.log (1/eps)^q ≤ K1 := by
      have := mul_le_mul_of_nonneg_left h1 hc.le
      calc c*eps^(1/2 : ℝ)*Real.log (1/eps)^q = c*(eps^(1/2 : ℝ)*Real.log (1/eps)^q) := by ring
        _ ≤ c*(K1/c) := this
        _ = K1 := by field_simp
    have h6 : c*(eps^(m*B0)*eps^(nu+3/2-m*B0))*Real.log (1/eps)^q ≤ eps^(m*B0)*K1 := by
      calc c*(eps^(m*B0)*eps^(nu+3/2-m*B0))*Real.log (1/eps)^q =
          eps^(m*B0)*(c*eps^(nu+3/2-m*B0)*Real.log (1/eps)^q) := by ring
        _ ≤ eps^(m*B0)*(c*eps^(1/2 : ℝ)*Real.log (1/eps)^q) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc.le) hℓq
        _ ≤ eps^(m*B0)*K1 := mul_le_mul_of_nonneg_left h5 (by positivity)
    calc _ ≤ eps^(m*B0)*K1 := h6
      _ = cstar*((βJ/2)^B0*eps^(m*B0)) := by rw [hK1]; ring
  · rw [p11_rpow_scale heps hβ, Real.mul_rpow (by positivity) hℓq]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hℓ,
      ← Real.rpow_mul heps.le]
    have e2 : eps^((nu+3/2)*(1/2 : ℝ))*eps^(m*(-G0)) = eps^((nu+3/2)*(1/2 : ℝ)+m*(-G0)) := by
      rw [← Real.rpow_add heps]
    have h4 : eps^((nu+3/2)*(1/2 : ℝ)+m*(-G0)) ≤ eps^(1/2 : ℝ) := hmon _ (by nlinarith)
    have h5 : K2*(eps^(1/2 : ℝ)*Real.log (1/eps)^(q/2)) ≤ 1/2 := by
      have := mul_le_mul_of_nonneg_left h2 hK20.le
      calc _ ≤ K2*(1/(2*K2)) := this
        _ = 1/2 := by field_simp
    have e3 : q*(1/2 : ℝ) = q/2 := by ring
    rw [e3]
    calc _ =
        K2*((eps^((nu+3/2)*(1/2 : ℝ))*eps^(m*(-G0)))*Real.log (1/eps)^(q/2)) := by
          rw [hK2, hm]; ring
      _ ≤ K2*(eps^(1/2 : ℝ)*Real.log (1/eps)^(q/2)) := by
          rw [e2]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4
            (Real.rpow_nonneg hℓ _)) hK20.le
      _ ≤ 1/2 := h5

end Asym

end KAM.Planetary

end
