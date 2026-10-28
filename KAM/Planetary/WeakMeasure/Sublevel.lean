/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Planetary.WeakMeasure.Stability
public import KAM.Planetary.WeakMeasure.BallSublevel

/-!
# Sublevel estimate on a patch (blueprint `bpP:p11a:sublevel`, P11A-W6)

For `0 < ε < β/4`, `vol {y ∈ K | |g̃ y| ≤ ε} ≤ C_sub (ε/β)^(1/μ)` (`KAM.Planetary.sublevel`).

Steps: the ceiling `κ` and radius `r = √n d / κ` with their inequalities (`bpP:p11a:sublevel#kappa`,
`p11_sl_kappa`); a mean-value bound for jets along a segment (`p11_jet_mvt`); the lower bound of a
directional jet of `g̃` on a ball around a point of `K` (`stepP:p11a:sl-lower`, `p11_sl_lower`);
the sublevel bound on one ball (`stepP:p11a:sl-ball`, `p11_sl_ball`, from `ball_sublevel`); the
cover of `K` by `κ ^ n` closed cells of side `d / κ` (`stepP:p11a:sl-cover`, `p11_cube_cover`); and
the sum over the cells (`stepP:p11a:sl-sum`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Mvt

variable {n : ℕ}

theorem p11euclid_smul (t : ℝ) (x : P11Vec n) : p11euclid (t • x) = |t| * p11euclid x := by
  simp only [p11euclid_eq_norm, map_smul, norm_smul, Real.norm_eq_abs]

theorem p11euclid_eq_zero {x : P11Vec n} (h : p11euclid x = 0) : x = 0 := by
  rw [p11euclid_eq_norm, norm_eq_zero] at h
  exact p11toE.injective (by simpa using h)

/-- A jet with one slot filled by an arbitrary vector is bounded by the operator gauge. -/
theorem p11_jet_cons_bound {g : P11Vec n → ℝ} {ν : ℕ} {w : P11Vec n}
    (hg : ContDiffAt ℝ (ν + 1) g w) {M : ℝ}
    (hop : p11op (fun x (_ : Fin 1) => g x) (ν + 1) w ≤ M) {a : P11Vec n}
    (ha : p11euclid a = 1) (u : P11Vec n) :
    |iteratedFDeriv ℝ (ν + 1) g w (Fin.cons u (fun _ : Fin ν => a))| ≤ M * p11euclid u := by
  set f := iteratedFDeriv ℝ (ν + 1) g w
  by_cases hs : p11euclid u = 0
  · have hu0 := p11euclid_eq_zero hs
    subst hu0
    have : f (Fin.cons 0 (fun _ : Fin ν => a)) = 0 :=
      f.map_coord_zero 0 (by simp)
    rw [this, abs_zero, hs, mul_zero]
  · have hpos : 0 < p11euclid u := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)
    set s := p11euclid u with hsdef
    set v : P11Vec n := s⁻¹ • u with hv
    have hv1 : p11euclid v = 1 := by
      have e : p11euclid u = s := hsdef.symm
      rw [hv, p11euclid_smul, abs_of_pos (inv_pos.2 hpos), e]
      exact inv_mul_cancel₀ hs
    have hu : u = s • v := by rw [hv, smul_inv_smul₀ hs]
    have hcons : (Fin.cons u (fun _ : Fin ν => a) : Fin (ν + 1) → P11Vec n) =
        Function.update (Fin.cons v (fun _ : Fin ν => a)) 0 (s • v) := by
      rw [Fin.update_cons_zero, ← hu]
    have h1 : f (Fin.cons u (fun _ : Fin ν => a)) = s • f (Fin.cons v (fun _ : Fin ν => a)) := by
      rw [hcons, f.map_update_smul]
      simp
    have h2 : |f (Fin.cons v (fun _ : Fin ν => a))| ≤ M := by
      rw [← p11euclid_iteratedFDeriv_scalar hg]
      refine (le_p11op _ _ _ _ ?_).trans hop
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hv1]
      · simp [ha]
    rw [h1, smul_eq_mul, abs_mul, abs_of_pos hpos, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 hpos.le

/-- Mean-value bound for a directional jet along the segment from `b` to `y`. -/
theorem p11_jet_mvt {V : Set (P11Vec n)} (hV : IsOpen V) {g : P11Vec n → ℝ} {ν : ℕ}
    (hg : ContDiffOn ℝ (ν + 1) g V) {b y : P11Vec n} {M : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, b + t • (y - b) ∈ V ∧
      p11op (fun x (_ : Fin 1) => g x) (ν + 1) (b + t • (y - b)) ≤ M)
    {a : P11Vec n} (ha : p11euclid a = 1) :
    |iteratedFDeriv ℝ ν g y (fun _ => a) - iteratedFDeriv ℝ ν g b (fun _ => a)| ≤
      M * p11euclid (y - b) := by
  set z : ℝ → P11Vec n := fun t => b + t • (y - b) with hz
  set ψ : ℝ → ℝ := fun t => iteratedFDeriv ℝ ν g (z t) (fun _ => a) with hψ
  have hzd : ∀ t, HasDerivAt z (y - b) t := fun t => by
    have h := ((hasDerivAt_id t).smul_const (y - b)).const_add b
    simpa only [id, one_smul] using h
  have hat : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (ν + 1) g (z t) := fun t ht =>
    hg.contDiffAt (hV.mem_nhds (hseg t ht).1)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt ψ (iteratedFDeriv ℝ (ν + 1) g (z t) (Fin.cons (y - b) (fun _ : Fin ν => a))) t := by
    intro t ht
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ ν g) (z t) :=
      (hat t ht).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self ν)
    have hΦ := hd.hasFDerivAt.continuousMultilinear_apply_const (fun _ : Fin ν => a)
    have h := hΦ.comp_hasDerivAt t (hzd t)
    have e := hd.iteratedFDeriv_succ_apply_left' (m := (Fin.cons (y - b) (fun _ : Fin ν => a) :
      Fin (ν + 1) → P11Vec n))
    simp only [Fin.cons_zero, Fin.tail_cons] at e
    rw [e, fderiv_continuousMultilinear_apply_const hd]
    exact h
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv ψ t‖ ≤ M * p11euclid (y - b) := by
    intro t ht
    rw [(hder t ht).deriv, Real.norm_eq_abs]
    exact p11_jet_cons_bound (hat t ht) (hseg t ht).2 ha _
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hder t ht).differentiableAt) hb (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  simpa [hψ, hz, Real.norm_eq_abs] using this

end Mvt

section Kappa

/-- `bpP:p11a:sublevel#kappa`: the ceiling and radius inequalities. -/
theorem p11_sl_kappa {n : ℕ} (hn : 1 ≤ n) {d v β M : ℝ} (hd : 0 < d) (hv : 0 < v)
    (hβ : 0 < β) (hM : β ≤ M) {κ : ℕ} (hκ : κ = ⌈(M / β) * (4 + v⁻¹) * Real.sqrt n * d⌉₊) :
    1 ≤ κ ∧ 4 * M * Real.sqrt n * d / β ≤ κ ∧ Real.sqrt n * d / v ≤ κ ∧
      (κ : ℝ) ≤ (M / β) * (1 + (4 + v⁻¹) * Real.sqrt n * d) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hA : 0 < Real.sqrt n * d := mul_pos hsn hd
  have hρ : 1 ≤ M / β := (one_le_div hβ).2 hM
  have hvi : 0 < v⁻¹ := inv_pos.2 hv
  set A := Real.sqrt n * d with hAdef
  have hx : 0 < (M / β) * (4 + v⁻¹) * A := by positivity
  have hle : (M / β) * (4 + v⁻¹) * A ≤ κ := hκ ▸ Nat.le_ceil _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hκ]; exact Nat.ceil_pos.2 hx
  · refine le_trans ?_ hle
    have : 4 * M * Real.sqrt n * d / β = (M / β) * 4 * A := by rw [hAdef]; field_simp
    rw [this]
    have : (M / β) * 4 * A ≤ (M / β) * (4 + v⁻¹) * A := by
      have := mul_pos (by linarith : 0 < M / β) hA
      nlinarith
    exact this
  · refine le_trans ?_ hle
    have : A / v = v⁻¹ * A := by rw [div_eq_inv_mul]
    rw [this]
    have h1 : v⁻¹ * A ≤ (4 + v⁻¹) * A := by nlinarith
    calc v⁻¹ * A ≤ (4 + v⁻¹) * A := h1
      _ = 1 * ((4 + v⁻¹) * A) := by ring
      _ ≤ (M / β) * ((4 + v⁻¹) * A) := by
        refine mul_le_mul_of_nonneg_right hρ (by positivity)
      _ = _ := by ring
  · have h1 : (κ : ℝ) < (M / β) * (4 + v⁻¹) * A + 1 := by
      rw [hκ]; exact Nat.ceil_lt_add_one hx.le
    have h2 : (M / β) * (4 + v⁻¹) * A + 1 ≤ (M / β) * (1 + (4 + v⁻¹) * A) := by nlinarith
    exact (h1.trans_le h2).le

end Kappa

section Lower

variable {n μ : ℕ} {P : P11Patch n} {g gt : P11Vec n → ℝ} {β M : ℝ}

theorem p11_mem_thick {b : P11Vec n} (hb : b ∈ P.K) : b ∈ p11thick P.K P.v :=
  ⟨b, hb, by rw [sub_self, p11euclid_zero]; exact P.v_pos.le⟩

theorem p11_ball_mem_thick {b y : P11Vec n} (hb : b ∈ P.K) {r : ℝ} (hr : r ≤ P.v)
    (hy : p11euclid (y - b) ≤ r) : y ∈ p11thick P.K P.v :=
  ⟨b, hb, hy.trans hr⟩

/-- `stepP:p11a:sl-lower`: some directional jet of `g̃` is `≥ β/4` on the ball around `b`. -/
theorem p11_sl_lower (H : P11SublevelHyp P μ g gt β M) {r : ℝ} (hr : r ≤ P.v)
    (hMr : M * r ≤ β / 4) {b : P11Vec n} (hb : b ∈ P.K) :
    ∃ ν ≤ μ, ∃ a : P11Vec n, p11euclid a = 1 ∧ ∀ y, p11euclid (y - b) ≤ r →
      β / 4 ≤ |iteratedFDeriv ℝ ν gt y (fun _ => a)| := by
  have hM : 0 ≤ M := H.beta_pos.le.trans H.size_ge
  have hbV : b ∈ P.V := P.thick_sub (p11_mem_thick hb)
  obtain ⟨ν, hν, hmax⟩ := p11maxJet_attained (fun x (_ : Fin 1) => g x) b μ
  have hfin := H.finite_type b hb
  rw [hmax] at hfin
  have hgat : ∀ k ≤ μ + 1, ∀ z ∈ P.V, ContDiffAt ℝ k g z := fun k hk z hz =>
    (H.g_smooth.of_le (by exact_mod_cast hk)).contDiffAt (P.openV.mem_nhds hz)
  have hgtat : ∀ k ≤ μ, ∀ z ∈ P.V, ContDiffAt ℝ k gt z := fun k hk z hz =>
    (H.gt_smooth.of_le (by exact_mod_cast hk)).contDiffAt (P.openV.mem_nhds hz)
  obtain ⟨a, ha, hdg⟩ := p11dg_attained (fun x (_ : Fin 1) => g x) ν b P.n_pos
  rw [hdg, p11euclid_iteratedFDeriv_scalar (hgat ν (by omega) b hbV)] at hfin
  refine ⟨ν, hν, a, ha, fun y hy => ?_⟩
  have hyT := p11_ball_mem_thick hb hr hy
  have hyV : y ∈ P.V := P.thick_sub hyT
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, b + t • (y - b) ∈ P.V ∧
      p11op (fun x (_ : Fin 1) => g x) (ν + 1) (b + t • (y - b)) ≤ M := by
    intro t ht
    have hT : b + t • (y - b) ∈ p11thick P.K P.v := by
      refine ⟨b, hb, ?_⟩
      rw [add_sub_cancel_left, p11euclid_smul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) ht.2).trans (hy.trans hr)
    exact ⟨P.thick_sub hT, H.size (ν + 1) (by omega) (by omega) _ hT⟩
  have hmvt := p11_jet_mvt P.openV (H.g_smooth.of_le (by exact_mod_cast (by omega : ν + 1 ≤ μ + 1)))
    hseg ha
  have hMy : M * p11euclid (y - b) ≤ M * r := mul_le_mul_of_nonneg_left hy hM
  have hcl : p11dg (fun x (_ : Fin 1) => gt x - g x) ν y ≤ β / 2 := by
    simpa using H.close ν hν y hyT
  have hcd : ContDiffAt ℝ ν (fun x => gt x - g x) y :=
    (hgtat ν hν y hyV).sub (hgat ν (by omega) y hyV)
  have h3 := le_p11dg (fun x (_ : Fin 1) => gt x - g x) ν y a ha
  rw [p11euclid_iteratedFDeriv_scalar hcd] at h3
  have e : iteratedFDeriv ℝ ν (fun x => gt x - g x) y =
      iteratedFDeriv ℝ ν gt y - iteratedFDeriv ℝ ν g y :=
    iteratedFDeriv_sub_apply (hgtat ν hν y hyV) (hgat ν (by omega) y hyV)
  rw [e] at h3
  simp only [ContinuousMultilinearMap.sub_apply] at h3
  have h4 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ ν g b (fun _ => a))
    (iteratedFDeriv ℝ ν g y (fun _ => a))
  have h5 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ ν g y (fun _ => a))
    (iteratedFDeriv ℝ ν gt y (fun _ => a))
  rw [abs_sub_comm] at h4
  rw [abs_sub_comm] at h5
  linarith

end Lower

section Ball

variable {n μ : ℕ} {P : P11Patch n} {g gt : P11Vec n → ℝ} {β M : ℝ}

/-- The exponent comparison behind `stepP:p11a:sl-ball`. -/
theorem p11_sl_ball_arith {ν μ : ℕ} (hν : 1 ≤ ν) (hνμ : ν ≤ μ) {x Q : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1 / 4) (hQ : 0 ≤ Q) :
    2 * ν * Q * (4 * x) ^ ((ν : ℝ)⁻¹) ≤ 8 * μ * Q * x ^ ((μ : ℝ)⁻¹) := by
  have hνpos : (0 : ℝ) < ν := by exact_mod_cast hν
  have hμν : (ν : ℝ) ≤ μ := by exact_mod_cast hνμ
  rw [Real.mul_rpow (by norm_num) hx0.le]
  have h1 : (4 : ℝ) ^ ((ν : ℝ)⁻¹) ≤ 4 := by
    calc (4 : ℝ) ^ ((ν : ℝ)⁻¹) ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (inv_le_one_of_one_le₀ (by exact_mod_cast hν))
      _ = 4 := Real.rpow_one _
  have h2 : x ^ ((ν : ℝ)⁻¹) ≤ x ^ ((μ : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) (inv_anti₀ hνpos hμν)
  have h3 : 0 ≤ x ^ ((ν : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have h4 : 0 ≤ (4 : ℝ) ^ ((ν : ℝ)⁻¹) := Real.rpow_nonneg (by norm_num) _
  have h5 : (4 : ℝ) ^ ((ν : ℝ)⁻¹) * x ^ ((ν : ℝ)⁻¹) ≤ 4 * x ^ ((μ : ℝ)⁻¹) :=
    mul_le_mul h1 h2 h3 (by norm_num)
  have h6 : 0 ≤ 2 * (ν : ℝ) * Q := by positivity
  calc 2 * ν * Q * ((4 : ℝ) ^ ((ν : ℝ)⁻¹) * x ^ ((ν : ℝ)⁻¹))
      ≤ 2 * ν * Q * (4 * x ^ ((μ : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h5 h6
    _ = 8 * ν * Q * x ^ ((μ : ℝ)⁻¹) := by ring
    _ ≤ 8 * μ * Q * x ^ ((μ : ℝ)⁻¹) := by
        have : 0 ≤ Q * x ^ ((μ : ℝ)⁻¹) := mul_nonneg hQ (Real.rpow_nonneg hx0.le _)
        nlinarith

/-- `stepP:p11a:sl-ball`: the sublevel set inside one ball. -/
theorem p11_sl_ball (H : P11SublevelHyp P μ g gt β M) {r eps : ℝ} (hr : 0 < r)
    (hrv : r ≤ P.v) (hMr : M * r ≤ β / 4) (he : 0 < eps) (he' : eps < β / 4)
    {b : P11Vec n} (hb : b ∈ P.K) :
    volume {y | p11euclid (y - b) ≤ r ∧ |gt y| ≤ eps} ≤
      ENNReal.ofReal (8 * μ * (2 * r) ^ (n - 1) * (eps / β) ^ ((μ : ℝ)⁻¹)) := by
  obtain ⟨ν, hν, a, ha, hlow⟩ := p11_sl_lower H hrv hMr hb
  have hβ := H.beta_pos
  rcases Nat.eq_zero_or_pos ν with rfl | hνpos
  · have : {y | p11euclid (y - b) ≤ r ∧ |gt y| ≤ eps} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y hy => ?_
      have := hlow y hy.1
      simp only [iteratedFDeriv_zero_apply] at this
      linarith [hy.2]
    rw [this, measure_empty]
    exact zero_le _
  · have hsub : {y | p11euclid (y - b) ≤ r} ⊆ P.V := fun y hy =>
      P.thick_sub (p11_ball_mem_thick hb hrv hy)
    have hgt : ContDiffOn ℝ ν gt P.V := H.gt_smooth.of_le (by exact_mod_cast hν)
    refine (ball_sublevel P.n_pos hνpos P.openV hr ha (by linarith) he hsub hgt hlow).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hx0 : 0 < eps / β := div_pos he hβ
    have hx1 : eps / β < 1 / 4 := by rw [div_lt_iff₀ hβ]; linarith
    have e : eps / (β / 4) = 4 * (eps / β) := by field_simp
    rw [e]
    exact p11_sl_ball_arith hνpos hν hx0 hx1 (by positivity)

end Ball

section Cover

variable {n : ℕ}

/-- The closed cell of side `h` with lower corner `a0 + j h`. -/
def p11cell (a0 : P11Vec n) (h : ℝ) {κ : ℕ} (j : Fin n → Fin κ) : Set (P11Vec n) :=
  {x | ∀ i, a0 i + ((j i : ℕ) : ℝ) * h ≤ x i ∧ x i ≤ a0 i + (((j i : ℕ) : ℝ) + 1) * h}

/-- Two points of one cell are within `√n h` in the Euclidean norm. -/
theorem p11cell_euclid_le {a0 : P11Vec n} {h : ℝ} (hh : 0 ≤ h) {κ : ℕ} {j : Fin n → Fin κ}
    {x x' : P11Vec n} (hx : x ∈ p11cell a0 h j) (hx' : x' ∈ p11cell a0 h j) :
    p11euclid (x - x') ≤ Real.sqrt n * h := by
  unfold p11euclid KAM.Nekhoroshev.euclid
  have hi : ∀ i, ‖(x - x') i‖ ^ 2 ≤ h ^ 2 := fun i => by
    have h1 := hx i
    have h2 := hx' i
    rw [Real.norm_eq_abs, sq_abs]
    refine sq_le_sq' ?_ ?_ <;> simp only [Pi.sub_apply] <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  calc Real.sqrt (∑ i, ‖(x - x') i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, h ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hi i)
    _ = Real.sqrt n * h := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hh]

/-- `stepP:p11a:sl-cover`: the compact set `K` of diameter `d > 0` lies in `κ ^ n` closed cells
of side `d / κ`. -/
theorem p11_cube_cover {K : Set (P11Vec n)} (hKc : IsCompact K) (hK : K.Nonempty)
    (hd : 0 < Metric.diam K) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ a0 : P11Vec n, K ⊆ ⋃ j : Fin n → Fin κ, p11cell a0 (Metric.diam K / κ) j := by
  have hmin : ∀ i, ∃ z ∈ K, ∀ x ∈ K, z i ≤ x i := fun i => by
    obtain ⟨z, hz, hm⟩ := hKc.exists_isMinOn hK (continuous_apply i).continuousOn
    exact ⟨z, hz, fun x hx => isMinOn_iff.1 hm x hx⟩
  choose z hzK hzmin using hmin
  refine ⟨fun i => z i i, fun x hx => ?_⟩
  set d := Metric.diam K with hd'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hh : 0 < d / κ := div_pos hd hκpos
  have hlow : ∀ i, z i i ≤ x i := fun i => hzmin i x hx
  have hup : ∀ i, x i ≤ z i i + d := fun i => by
    have h1 : dist x (z i) ≤ d := Metric.dist_le_diam_of_mem hKc.isBounded hx (hzK i)
    have h2 : |x i - z i i| ≤ dist x (z i) := by
      rw [← Real.norm_eq_abs, ← Pi.sub_apply]
      exact (norm_le_pi_norm (x - z i) i).trans_eq (dist_eq_norm _ _).symm
    linarith [(abs_le.1 (h2.trans h1)).2]
  have hidx : ∀ i, ∃ k : Fin κ, z i i + ((k : ℕ) : ℝ) * (d / κ) ≤ x i ∧
      x i ≤ z i i + (((k : ℕ) : ℝ) + 1) * (d / κ) := fun i => by
    set t := (x i - z i i) / (d / κ) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hlow i]) hh.le
    have htκ : t ≤ κ := by
      rw [ht, div_le_iff₀ hh]
      have : (κ : ℝ) * (d / κ) = d := by field_simp
      linarith [hup i]
    have hxt : x i = z i i + t * (d / κ) := by rw [ht]; field_simp; ring
    have hk : min ⌊t⌋₊ (κ - 1) < κ := lt_of_le_of_lt (min_le_right _ _) (by omega)
    refine ⟨⟨min ⌊t⌋₊ (κ - 1), hk⟩, ?_, ?_⟩
    · simp only
      rw [hxt]
      have : ((min ⌊t⌋₊ (κ - 1) : ℕ) : ℝ) ≤ t :=
        ((Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht0))
      nlinarith
    · simp only
      rw [hxt]
      have : t ≤ ((min ⌊t⌋₊ (κ - 1) : ℕ) : ℝ) + 1 := by
        rcases le_total ⌊t⌋₊ (κ - 1) with h | h
        · rw [min_eq_left h]; exact (Nat.lt_floor_add_one t).le
        · rw [min_eq_right h]
          have : ((κ - 1 : ℕ) : ℝ) + 1 = κ := by
            rw [Nat.cast_sub hκ]; push_cast; ring
          rw [this]; exact htκ
      nlinarith
  choose k hk using hidx
  exact mem_iUnion.2 ⟨k, fun i => hk i⟩

end Cover

section Sum

/-- The arithmetic of `stepP:p11a:sl-sum`. -/
theorem p11_sl_sum_arith (m : ℕ) {κ A ρ C X μ : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hR : κ ≤ ρ * C) :
    κ ^ (m + 1) * (8 * μ * (2 * (A / κ)) ^ m * X) ≤ 2 ^ (m + 1 + 2) * μ * A ^ m * ρ * C * X := by
  have e : κ ^ (m + 1) * (8 * μ * (2 * (A / κ)) ^ m * X) = (8 * 2 ^ m * μ * A ^ m * X) * κ := by
    have : κ ^ m * (2 * (A / κ)) ^ m = 2 ^ m * A ^ m := by
      rw [← mul_pow, ← mul_pow]; congr 1; field_simp
    calc κ ^ (m + 1) * (8 * μ * (2 * (A / κ)) ^ m * X)
        = (κ ^ m * (2 * (A / κ)) ^ m) * (8 * μ * X * κ) := by ring
      _ = _ := by rw [this]; ring
  rw [e]
  have e2 : (2 : ℝ) ^ (m + 1 + 2) * μ * A ^ m * ρ * C * X = (8 * 2 ^ m * μ * A ^ m * X) * (ρ * C) := by
    ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

end Sum

/-- `bpP:p11a:sublevel`. -/
theorem sublevel {n mu : ℕ} {P : P11Patch n} {g gt : P11Vec n → ℝ}
    {beta M eps : ℝ} (H : P11SublevelHyp P mu g gt beta M)
    (he : 0 < eps) (he' : eps < beta/4) :
    volume {y ∈ P.K | |gt y| ≤ eps} ≤
      ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) *
        (eps/beta)^((mu : ℝ)⁻¹)) := by
  have hβ := H.beta_pos
  have hM : 0 ≤ M := hβ.le.trans H.size_ge
  have hd := P.diameter_pos
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast P.n_pos)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ, κ = ⌈(M / beta) * (4 + P.v⁻¹) * Real.sqrt n *
      Metric.diam P.K⌉₊ := ⟨_, rfl⟩
  obtain ⟨hκ1, hκ2, hκ3, hκ4⟩ := p11_sl_kappa P.n_pos hd P.v_pos hβ H.size_ge hκdef
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  set d := Metric.diam P.K with hddef
  set r := Real.sqrt n * d / κ with hrdef
  have hr : 0 < r := div_pos (mul_pos hsn hd) hκpos
  have hrv : r ≤ P.v := by
    rw [hrdef, div_le_iff₀ hκpos]
    have := (div_le_iff₀ P.v_pos).1 hκ3
    linarith
  have hMr : M * r ≤ beta / 4 := by
    rw [hrdef, ← mul_div_assoc, div_le_iff₀ hκpos]
    have := (div_le_iff₀ hβ).1 hκ2
    nlinarith
  obtain ⟨a0, hcov⟩ := p11_cube_cover P.compact P.nonempty hd hκ1
  set E : Set (P11Vec n) := {y ∈ P.K | |gt y| ≤ eps} with hE
  set B : ℝ := 8 * mu * (2 * r) ^ (n - 1) * (eps / beta) ^ ((mu : ℝ)⁻¹) with hB
  have hsub : E ⊆ ⋃ j : Fin n → Fin κ, E ∩ p11cell a0 (d / κ) j := fun y hy => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hy.1)
    exact mem_iUnion.2 ⟨j, hy, hj⟩
  have hcell : ∀ j : Fin n → Fin κ, volume (E ∩ p11cell a0 (d / κ) j) ≤ ENNReal.ofReal B := by
    intro j
    by_cases hne : (E ∩ p11cell a0 (d / κ) j).Nonempty
    · obtain ⟨b, hbE, hbc⟩ := hne
      refine le_trans (measure_mono fun y hy => ?_) (p11_sl_ball H hr hrv hMr he he' hbE.1)
      refine ⟨?_, hy.1.2⟩
      have := p11cell_euclid_le (div_pos hd hκpos).le hy.2 hbc
      rwa [← mul_div_assoc] at this
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
      exact zero_le _
  have hsum : volume E ≤ (κ ^ n : ℕ) * ENNReal.ofReal B := by
    calc volume E ≤ volume (⋃ j : Fin n → Fin κ, E ∩ p11cell a0 (d / κ) j) := measure_mono hsub
      _ ≤ ∑ j : Fin n → Fin κ, volume (E ∩ p11cell a0 (d / κ) j) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin n → Fin κ, ENNReal.ofReal B := Finset.sum_le_sum fun j _ => hcell j
      _ = (κ ^ n : ℕ) * ENNReal.ofReal B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
  refine hsum.trans ?_
  have hBnn : 0 ≤ B := by positivity
  have e : (((κ ^ n : ℕ)) : ENNReal) * ENNReal.ofReal B = ENNReal.ofReal ((κ : ℝ) ^ n * B) := by
    rw [ENNReal.ofReal_mul (by positivity), ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  have hX : 0 ≤ (eps / beta) ^ ((mu : ℝ)⁻¹) := Real.rpow_nonneg (div_pos he hβ).le _
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := P.n_pos; omega⟩
  have key := p11_sl_sum_arith m (κ := κ) (A := Real.sqrt n * d) (ρ := M / beta)
    (C := 1 + (4 + P.v⁻¹) * Real.sqrt n * d) (X := (eps / beta) ^ ((mu : ℝ)⁻¹)) (μ := mu)
    hκpos (by positivity) hX (Nat.cast_nonneg _) (div_nonneg hM hβ.le)
    (by have := P.v_pos; positivity) hκ4
  rw [hm] at key ⊢
  simpa [hB, hrdef, p11Csub, ← hm] using key

end KAM.Planetary
