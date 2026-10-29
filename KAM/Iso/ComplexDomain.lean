/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Kepler.Basic
public import KAM.Kepler.Energy
public import KAM.Kepler.Orbit
public import KAM.Kepler.KeplerTube
public import KAM.Kepler.OrbitComplex

/-!
# A common complex neighbourhood for the Delaunay chart (`bpI:p7:sec-complex`, `complex-domain`)

For a safe action region `K` (compact, nonempty, inside the cone `0 < G < L`) the constants
`e₋ = kEccMin K`, `e₁ = kEccMax K`, `m_L = kLMin K`, `m_G = kGMin K`, `r_min`, `ρ_max`
(`SafeAction.ecc_bounds`), the principal-branch eccentricity `eccC L G = (1 - G²/L²)^{1/2}`, the
complex neighbourhood `UDelta K δ` and the complex Delaunay map `delaunayC K`.

`ComplexDomainData K δ₁` bundles the conclusions of `bpI:p7:complex-domain` at a radius `δ₁`
(with the quantifier "nearest `(L', G')`" replaced by "every `(L', G') ∈ K` within `δ₁`");
`complexDelta K` is the radius selected by classical choice, and
`complex_domain_spec` certifies it.

The proof follows `stepI:p7:cd-uc` and `stepI:p7:cd-branch`: uniform continuity of
`(L, G) ↦ G²/L²` on the closed `δ₀`-thickening of `K` gives `δ₁`; the principal square root of
`1 - G²/L²` is then compared with the real eccentricity `e(L', G') ≥ e₋` through
`|√w - √w'| = |w - w'| / |√w + √w'| ≤ |w - w'| / e₋`.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Iso

open KAM KAM.Kepler KAM.Planetary

section Part7Exact

/-- Standing data of `bpI:p7:sec-complex`: a safe action region (`(L, G) = (x 0, x 1)`). -/
structure SafeAction (K : Set (Fin 2 → ℝ)) : Prop where
  isCompact : IsCompact K
  nonempty : K.Nonempty
  sub_cone : ∀ x ∈ K, 0 < x 1 ∧ x 1 < x 0

def kEccMin (K : Set (Fin 2 → ℝ)) : ℝ := sInf ((fun x => eccOf (x 0) (x 1)) '' K)
def kEccMax (K : Set (Fin 2 → ℝ)) : ℝ := sSup ((fun x => eccOf (x 0) (x 1)) '' K)
def kLMin (K : Set (Fin 2 → ℝ)) : ℝ := sInf ((fun x => x 0) '' K)
def kGMin (K : Set (Fin 2 → ℝ)) : ℝ := sInf ((fun x => x 1) '' K)
def kRmin (K : Set (Fin 2 → ℝ)) : ℝ := sInf ((fun x => x 0 ^ 2 * (1 - eccOf (x 0) (x 1))) '' K)
def kRhoMax (K : Set (Fin 2 → ℝ)) : ℝ := sSup ((fun x => x 0 ^ 2 * (1 + eccOf (x 0) (x 1))) '' K)

/-! ### The constants of a safe action region -/

namespace ComplexDomainAux

variable {K : Set (Fin 2 → ℝ)}

theorem eccOf_pos_lt_one {L G : ℝ} (hG : 0 < G) (hGL : G < L) :
    0 < eccOf L G ∧ eccOf L G < 1 := by
  have hL : 0 < L := hG.trans hGL
  have h1 : G ^ 2 / L ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have h2 : 0 < G ^ 2 / L ^ 2 := by positivity
  unfold eccOf
  constructor
  · exact Real.sqrt_pos.mpr (by linarith)
  · rw [Real.sqrt_lt' one_pos]; nlinarith

theorem eccOf_sq {L G : ℝ} (hG : 0 < G) (hGL : G < L) : eccOf L G ^ 2 = 1 - G ^ 2 / L ^ 2 := by
  have hL : 0 < L := hG.trans hGL
  have h1 : G ^ 2 / L ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact Real.sq_sqrt (by linarith)

theorem continuousOn_eccFn (hK : SafeAction K) :
    ContinuousOn (fun x : Fin 2 → ℝ => eccOf (x 0) (x 1)) K := by
  unfold eccOf
  refine ContinuousOn.sqrt (continuousOn_const.sub (ContinuousOn.div (by fun_prop)
    (by fun_prop) fun x hx => ?_))
  have h := hK.sub_cone x hx
  exact pow_ne_zero 2 (h.1.trans h.2).ne'

theorem sInf_spec {f : (Fin 2 → ℝ) → ℝ} (hK : SafeAction K) (hf : ContinuousOn f K) :
    (∃ x ∈ K, sInf (f '' K) = f x) ∧ ∀ x ∈ K, sInf (f '' K) ≤ f x := by
  have hc : IsCompact (f '' K) := hK.isCompact.image_of_continuousOn hf
  refine ⟨?_, fun x hx => csInf_le hc.bddBelow (mem_image_of_mem f hx)⟩
  obtain ⟨x, hx, hxe⟩ := hc.sInf_mem (hK.nonempty.image f)
  exact ⟨x, hx, hxe.symm⟩

theorem sSup_spec {f : (Fin 2 → ℝ) → ℝ} (hK : SafeAction K) (hf : ContinuousOn f K) :
    (∃ x ∈ K, sSup (f '' K) = f x) ∧ ∀ x ∈ K, f x ≤ sSup (f '' K) := by
  have hc : IsCompact (f '' K) := hK.isCompact.image_of_continuousOn hf
  refine ⟨?_, fun x hx => le_csSup hc.bddAbove (mem_image_of_mem f hx)⟩
  obtain ⟨x, hx, hxe⟩ := hc.sSup_mem (hK.nonempty.image f)
  exact ⟨x, hx, hxe.symm⟩

theorem pos_x0 (hK : SafeAction K) {x : Fin 2 → ℝ} (hx : x ∈ K) : 0 < x 0 :=
  (hK.sub_cone x hx).1.trans (hK.sub_cone x hx).2

theorem kEccMin_spec (hK : SafeAction K) :
    (∃ x ∈ K, kEccMin K = eccOf (x 0) (x 1)) ∧ ∀ x ∈ K, kEccMin K ≤ eccOf (x 0) (x 1) :=
  sInf_spec hK (continuousOn_eccFn hK)

theorem kEccMax_spec (hK : SafeAction K) :
    (∃ x ∈ K, kEccMax K = eccOf (x 0) (x 1)) ∧ ∀ x ∈ K, eccOf (x 0) (x 1) ≤ kEccMax K :=
  sSup_spec hK (continuousOn_eccFn hK)

theorem kLMin_spec (hK : SafeAction K) :
    (∃ x ∈ K, kLMin K = x 0) ∧ ∀ x ∈ K, kLMin K ≤ x 0 :=
  sInf_spec (f := fun x : Fin 2 → ℝ => x 0) hK (continuous_apply 0).continuousOn

theorem kGMin_spec (hK : SafeAction K) :
    (∃ x ∈ K, kGMin K = x 1) ∧ ∀ x ∈ K, kGMin K ≤ x 1 :=
  sInf_spec (f := fun x : Fin 2 → ℝ => x 1) hK (continuous_apply 1).continuousOn

theorem continuousOn_rminFn (hK : SafeAction K) :
    ContinuousOn (fun x : Fin 2 → ℝ => x 0 ^ 2 * (1 - eccOf (x 0) (x 1))) K :=
  ((continuous_apply 0).pow 2).continuousOn.mul (continuousOn_const.sub (continuousOn_eccFn hK))

theorem continuousOn_rmaxFn (hK : SafeAction K) :
    ContinuousOn (fun x : Fin 2 → ℝ => x 0 ^ 2 * (1 + eccOf (x 0) (x 1))) K :=
  ((continuous_apply 0).pow 2).continuousOn.mul (continuousOn_const.add (continuousOn_eccFn hK))

theorem kEccMin_pos (hK : SafeAction K) : 0 < kEccMin K := by
  obtain ⟨x, hx, hxe⟩ := (kEccMin_spec hK).1
  have h := hK.sub_cone x hx
  rw [hxe]
  exact (eccOf_pos_lt_one h.1 h.2).1

theorem kEccMin_le_kEccMax (hK : SafeAction K) : kEccMin K ≤ kEccMax K := by
  obtain ⟨x, hx⟩ := hK.nonempty
  exact (kEccMin_spec hK).2 x hx |>.trans ((kEccMax_spec hK).2 x hx)

theorem kEccMax_lt_one (hK : SafeAction K) : kEccMax K < 1 := by
  obtain ⟨x, hx, hxe⟩ := (kEccMax_spec hK).1
  have h := hK.sub_cone x hx
  rw [hxe]
  exact (eccOf_pos_lt_one h.1 h.2).2

theorem kLMin_pos (hK : SafeAction K) : 0 < kLMin K := by
  obtain ⟨x, hx, hxe⟩ := (kLMin_spec hK).1
  rw [hxe]
  exact pos_x0 hK hx

theorem kGMin_pos (hK : SafeAction K) : 0 < kGMin K := by
  obtain ⟨x, hx, hxe⟩ := (kGMin_spec hK).1
  rw [hxe]
  exact (hK.sub_cone x hx).1

end ComplexDomainAux

theorem SafeAction.ecc_bounds {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) :
    0 < kEccMin K ∧ kEccMax K < 1 ∧ 0 < kLMin K ∧ 0 < kGMin K ∧ 0 < kRmin K ∧
      kRmin K ≤ kRhoMax K := by
  refine ⟨ComplexDomainAux.kEccMin_pos hK, ComplexDomainAux.kEccMax_lt_one hK,
    ComplexDomainAux.kLMin_pos hK, ComplexDomainAux.kGMin_pos hK, ?_, ?_⟩
  · obtain ⟨x, hx, hxe⟩ :=
      (ComplexDomainAux.sInf_spec hK (ComplexDomainAux.continuousOn_rminFn hK)).1
    have h := hK.sub_cone x hx
    have h0 := ComplexDomainAux.pos_x0 hK hx
    have he := (ComplexDomainAux.eccOf_pos_lt_one h.1 h.2).2
    show 0 < sInf ((fun x : Fin 2 → ℝ => x 0 ^ 2 * (1 - eccOf (x 0) (x 1))) '' K)
    rw [hxe]
    exact mul_pos (pow_pos h0 2) (by linarith)
  · obtain ⟨x, hx⟩ := hK.nonempty
    have h := hK.sub_cone x hx
    have hmin := (ComplexDomainAux.sInf_spec hK (ComplexDomainAux.continuousOn_rminFn hK)).2 x hx
    have hmax := (ComplexDomainAux.sSup_spec hK (ComplexDomainAux.continuousOn_rmaxFn hK)).2 x hx
    have he := (ComplexDomainAux.eccOf_pos_lt_one h.1 h.2).1
    have : x 0 ^ 2 * (1 - eccOf (x 0) (x 1)) ≤ x 0 ^ 2 * (1 + eccOf (x 0) (x 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    exact hmin.trans (this.trans hmax)

/-- `eccC(L, G) = (1 - G²/L²)^{1/2}` (principal branch). -/
def eccC (L G : ℂ) : ℂ := (1 - G ^ 2 / L ^ 2) ^ (1 / 2 : ℂ)
/-- `𝒰(δ)`: `|Im ℓ|, |Im g| < δ`, `(L, G) ∈ 𝒦_δ`; `w = ((ℓ, g), (L, G))`. -/
def UDelta (K : Set (Fin 2 → ℝ)) (δ : ℝ) : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
  {w | (∀ i, |(w.1 i).im| < δ) ∧ w.2 ∈ actionNbhd K δ}
/-- The complex Delaunay map `𝖰 = 𝖰_el(ℓ, g, L, e(L, G), G/L)`. -/
def delaunayC (K : Set (Fin 2 → ℝ)) (w : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  orbitMapC (kEccMax K) ![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0]

/-- The tolerance `τ = min {e₋²/2, e₋ δ_E}` of `bpI:p7:complex-domain`. -/
def complexTau (K : Set (Fin 2 → ℝ)) : ℝ :=
  min (kEccMin K ^ 2 / 2) (kEccMin K * keplerDeltaE (kEccMax K))

/-- The full output of `bpI:p7:complex-domain` at a given `δ₁` (exact factorization of the earlier
statement). The last three conjuncts add the quantitative conclusions of
the blueprint lemma, namely the ratio bound `|G²/L² - G'²/L'²| < τ`, the radicand-disk membership
`1 - G²/L² ∈ D(e(L', G')², e₋²/2) ⊂ {Re z > 0}` and `e² = 1 - G²/L²`. -/
def ComplexDomainData (K : Set (Fin 2 → ℝ)) (δ₁ : ℝ) : Prop :=
  0 < δ₁ ∧ δ₁ ≤ min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) / 2 ∧
    (∀ x ∈ actionNbhd K δ₁, x 0 ≠ 0 ∧ kLMin K / 2 < (x 0).re) ∧
    DifferentiableOn ℂ (fun x : Fin 2 → ℂ => eccC (x 0) (x 1)) (actionNbhd K δ₁) ∧
    (∀ x ∈ actionNbhd K δ₁, ∀ y ∈ K, ‖x - fun i => (y i : ℂ)‖ < δ₁ →
      ‖eccC (x 0) (x 1) - (eccOf (y 0) (y 1) : ℝ)‖ < keplerDeltaE (kEccMax K) ∧
      ‖eccC (x 0) (x 1)‖ < keplerE2 (kEccMax K)) ∧
    (∀ y : Fin 2 → ℝ, (fun i => (y i : ℂ)) ∈ actionNbhd K δ₁ → 0 < y 1 ∧ y 1 < y 0 ∧
      eccC (y 0) (y 1) = (eccOf (y 0) (y 1) : ℝ)) ∧
    (∀ w ∈ UDelta K δ₁,
      ![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] ∈ orbitDomC (kEccMax K)) ∧
    DifferentiableOn ℂ (delaunayC K) (UDelta K δ₁) ∧
    (∀ w : Phase 2, phaseToC w ∈ UDelta K δ₁ → delaunayC K (phaseToC w) = phaseToC (delaunay w)) ∧
    (∀ x ∈ actionNbhd K δ₁, ∀ y ∈ K, ‖x - fun i => (y i : ℂ)‖ < δ₁ →
      ‖x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2‖ < complexTau K) ∧
    (∀ x ∈ actionNbhd K δ₁, ∀ y ∈ K, ‖x - fun i => (y i : ℂ)‖ < δ₁ →
      ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ < kEccMin K ^ 2 / 2 ∧
        kEccMin K ^ 2 / 2 < (1 - x 1 ^ 2 / x 0 ^ 2).re) ∧
    (∀ x ∈ actionNbhd K δ₁, eccC (x 0) (x 1) ^ 2 = 1 - x 1 ^ 2 / x 0 ^ 2)

open scoped Classical in
/-- The selected `δ₁`. -/
def complexDelta (K : Set (Fin 2 → ℝ)) : ℝ :=
  if h : ∃ δ₁ : ℝ, ComplexDomainData K δ₁ then h.choose else 0

/-! ### The principal square root near a positive real -/

namespace ComplexDomainAux

/-- The principal square root of a number with positive real part has positive real part. -/
theorem re_sqrt_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have harg : |Complex.arg w| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have him : (Complex.log w * (1 / 2 : ℂ)).im = Complex.arg w / 2 := by
    have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.mul_im]
    simp [Complex.log_im]
    ring
  rw [him]
  have := abs_lt.1 harg
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem sqrt_sq_eq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  have h := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  have h2 : (((2 : ℕ) : ℂ)⁻¹) = (1 / 2 : ℂ) := by norm_num
  rw [h2] at h
  exact h

/-- Step `stepI:p7:cd-branch`: if `w` is within `a²/2` of `e'²` with `a ≤ e'`, then `Re w > 0`, and
`|√w - e'| ≤ |w - e'²| / a`. -/
theorem sqrt_branch {a e' : ℝ} (ha : 0 < a) (he' : a ≤ e') {w : ℂ}
    (hw : ‖w - (e' : ℂ) ^ 2‖ ≤ a ^ 2 / 2) :
    0 < w.re ∧ ‖w ^ (1 / 2 : ℂ) - (e' : ℂ)‖ * a ≤ ‖w - (e' : ℂ) ^ 2‖ := by
  have hre : 0 < w.re := by
    have h1 : |(w - (e' : ℂ) ^ 2).re| ≤ ‖w - (e' : ℂ) ^ 2‖ := Complex.abs_re_le_norm _
    have h2 : (w - (e' : ℂ) ^ 2).re = w.re - e' ^ 2 := by
      rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    have h3 : a ^ 2 ≤ e' ^ 2 := pow_le_pow_left₀ ha.le he' 2
    have h4 := (abs_le.1 (h1.trans hw)).1
    rw [h2] at h4
    have : 0 < a ^ 2 := by positivity
    linarith
  refine ⟨hre, ?_⟩
  have hsre : 0 < (w ^ (1 / 2 : ℂ)).re := re_sqrt_pos hre
  have hs2 := sqrt_sq_eq w
  set s := w ^ (1 / 2 : ℂ) with hs
  have hfac : s ^ 2 - (e' : ℂ) ^ 2 = (s - e') * (s + e') := by ring
  have hnorm : a ≤ ‖s + (e' : ℂ)‖ := by
    have h1 : (s + (e' : ℂ)).re = s.re + e' := by simp
    have h2 := Complex.re_le_norm (s + (e' : ℂ))
    linarith
  calc ‖s - (e' : ℂ)‖ * a ≤ ‖s - (e' : ℂ)‖ * ‖s + (e' : ℂ)‖ := by gcongr
    _ = ‖(s - (e' : ℂ)) * (s + (e' : ℂ))‖ := (norm_mul _ _).symm
    _ = ‖w - (e' : ℂ) ^ 2‖ := by rw [← hfac, hs2]

end ComplexDomainAux

/-! ### The radius `δ₁` and the pointwise facts -/

namespace ComplexDomainAux

variable {K : Set (Fin 2 → ℝ)}

/-- The coordinates of two vectors differ by at most the sup norm of the difference. -/
theorem coord_sub_le (x : Fin 2 → ℂ) (y : Fin 2 → ℝ) (i : Fin 2) :
    |(x i).re - y i| ≤ ‖x - fun j => (y j : ℂ)‖ := by
  have h1 : ‖x i - (y i : ℂ)‖ ≤ ‖x - fun j => (y j : ℂ)‖ :=
    norm_le_pi_norm (x - fun j => (y j : ℂ)) i
  have h2 : |(x i - (y i : ℂ)).re| ≤ ‖x i - (y i : ℂ)‖ := Complex.abs_re_le_norm _
  simpa using h2.trans h1

theorem cast_one_sub (a b : ℝ) :
    (1 - (b : ℂ) ^ 2 / (a : ℂ) ^ 2) = ((1 - b ^ 2 / a ^ 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- A radius `δ₁` for which `G²/L²` varies by less than `τ = min {e₋²/2, e₋ δ_E}` between the
points of `𝒦_{δ₁}` and the points of `𝒦` within `δ₁` (Step `stepI:p7:cd-uc`). -/
structure GoodRadius (K : Set (Fin 2 → ℝ)) (δ₁ : ℝ) : Prop where
  pos : 0 < δ₁
  le : δ₁ ≤ min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) / 2
  unif : ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℝ), y ∈ K → ‖x - fun i => (y i : ℂ)‖ < δ₁ →
    ‖(1 - x 1 ^ 2 / x 0 ^ 2) - (1 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2)‖ <
      min (kEccMin K ^ 2 / 2) (kEccMin K * keplerDeltaE (kEccMax K))

theorem kEccMax_pos (hK : SafeAction K) : 0 < kEccMax K :=
  (kEccMin_pos hK).trans_le (kEccMin_le_kEccMax hK)

theorem GoodRadius.le_deltaK {δ₁ : ℝ} (hr : GoodRadius K δ₁) :
    δ₁ ≤ keplerDeltaK (kEccMax K) / 2 := by
  have := (min_le_left (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)))
  have h := hr.le
  linarith

theorem GoodRadius.le_L {δ₁ : ℝ} (hr : GoodRadius K δ₁) :
    δ₁ ≤ kLMin K / 2 := by
  have : min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) ≤ kLMin K :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h := hr.le
  linarith

theorem GoodRadius.le_G {δ₁ : ℝ} (hr : GoodRadius K δ₁) :
    δ₁ ≤ kGMin K / 2 := by
  have : min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) ≤ kGMin K :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h := hr.le
  linarith

/-- Existence of a good radius: uniform continuity of `G²/L²` on the closed `δ₀`-thickening of
`𝒦`, where `|L| ≥ m_L/2` (Step `stepI:p7:cd-uc`). -/
theorem exists_radius (hK : SafeAction K) : ∃ δ₁, GoodRadius K δ₁ := by
  have h0 := kEccMax_pos hK
  have h1 := kEccMax_lt_one hK
  have hΔK : 0 < keplerDeltaK (kEccMax K) := Tube.deltaK_pos h0 h1
  have hΔE : 0 < keplerDeltaE (kEccMax K) := Tube.deltaE_pos h0 h1
  have hL := kLMin_pos hK
  have hG := kGMin_pos hK
  have ha := kEccMin_pos hK
  have hδ₀ : 0 < min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) / 2 :=
    div_pos (lt_min hΔK (lt_min hL hG)) two_pos
  have hτ : 0 < min (kEccMin K ^ 2 / 2) (kEccMin K * keplerDeltaE (kEccMax K)) :=
    lt_min (by positivity) (mul_pos ha hΔE)
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀, δ₀ = min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) / 2 :=
    ⟨_, rfl⟩
  rw [← hδ₀def] at hδ₀
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = min (kEccMin K ^ 2 / 2) (kEccMin K * keplerDeltaE (kEccMax K)) :=
    ⟨_, rfl⟩
  rw [← hτdef] at hτ
  have hδL : δ₀ ≤ kLMin K / 2 := by
    have : min (keplerDeltaK (kEccMax K)) (min (kLMin K) (kGMin K)) ≤ kLMin K :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [hδ₀def]; linarith
  have hofR : Continuous (fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hKc : IsCompact ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K) :=
    hK.isCompact.image hofR
  have hCc : IsCompact (cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K)) :=
    hKc.cthickening
  have hCmem : ∀ x ∈ cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K),
      ∃ y ∈ K, ‖x - fun i => (y i : ℂ)‖ ≤ δ₀ := by
    intro x hx
    rw [hKc.cthickening_eq_biUnion_closedBall hδ₀.le] at hx
    simp only [mem_iUnion, mem_closedBall, exists_prop] at hx
    obtain ⟨z, ⟨y, hy, rfl⟩, hxz⟩ := hx
    exact ⟨y, hy, by rwa [dist_eq_norm] at hxz⟩
  have hC0 : ∀ x ∈ cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K), x 0 ≠ 0 := by
    intro x hx h0'
    obtain ⟨y, hy, hxy⟩ := hCmem x hx
    have h := (abs_le.1 ((coord_sub_le x y 0).trans hxy)).1
    have hy0 := (kLMin_spec hK).2 y hy
    rw [h0'] at h
    simp only [Complex.zero_re] at h
    linarith
  have hcont : ContinuousOn (fun x : Fin 2 → ℂ => x 1 ^ 2 / x 0 ^ 2)
      (cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K)) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => pow_ne_zero 2 (hC0 x hx)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hCc.uniformContinuousOn_of_continuous hcont) τ hτ
  refine ⟨min δ₀ δ, lt_min hδ₀ hδ, ?_, ?_⟩
  · rw [← hδ₀def]; exact min_le_left _ _
  · intro x y hy hxy
    have hxy' : ‖x - fun i => (y i : ℂ)‖ < δ₀ := hxy.trans_le (min_le_left _ _)
    have hyC : (fun i => (y i : ℂ)) ∈
        cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K) :=
      Metric.mem_cthickening_of_dist_le _ _ _ _ (mem_image_of_mem _ hy) (by simpa using hδ₀.le)
    have hxC : x ∈ cthickening δ₀ ((fun y : Fin 2 → ℝ => fun i => (y i : ℂ)) '' K) :=
      Metric.mem_cthickening_of_dist_le _ (fun i => (y i : ℂ)) _ _ (mem_image_of_mem _ hy)
        (by rw [dist_eq_norm]; exact hxy'.le)
    have key : dist (x 1 ^ 2 / x 0 ^ 2) ((y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2) < τ :=
      hδu x hxC (fun i => (y i : ℂ)) hyC
        (by rw [dist_eq_norm]; exact hxy.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at key
    rw [hτdef] at key
    have e : (1 - x 1 ^ 2 / x 0 ^ 2) - (1 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2) =
        -(x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2) := by ring
    rw [e, norm_neg]
    exact key

/-- The pointwise facts of `bpI:p7:complex-domain`: for `x` within `δ₁` of `y ∈ 𝒦`, `Re x₀ > m_L/2`,
`Re (1 - x₁²/x₀²) > 0`, `|e(x) - e(y)| < δ_E` and `|e(x)| < e₂`. -/
theorem point_facts (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {x : Fin 2 → ℂ}
    {y : Fin 2 → ℝ} (hy : y ∈ K) (hxy : ‖x - fun i => (y i : ℂ)‖ < δ₁) :
    kLMin K / 2 < (x 0).re ∧ 0 < (1 - x 1 ^ 2 / x 0 ^ 2).re ∧
      ‖eccC (x 0) (x 1) - ((eccOf (y 0) (y 1) : ℝ) : ℂ)‖ < keplerDeltaE (kEccMax K) ∧
      ‖eccC (x 0) (x 1)‖ < keplerE2 (kEccMax K) := by
  have hLpos := kLMin_pos hK
  have hle0 : kLMin K ≤ y 0 := (kLMin_spec hK).2 y hy
  have hδ := hr.le_L
  have hre0 : kLMin K / 2 < (x 0).re := by
    have h := abs_lt.1 ((coord_sub_le x y 0).trans_lt hxy)
    linarith [h.1]
  refine ⟨hre0, ?_⟩
  have hy' := hK.sub_cone y hy
  have hae' : kEccMin K ≤ eccOf (y 0) (y 1) := (kEccMin_spec hK).2 y hy
  have he'1 : eccOf (y 0) (y 1) ≤ kEccMax K := (kEccMax_spec hK).2 y hy
  have ha0 : 0 < kEccMin K := kEccMin_pos hK
  have he'sq : ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2 = 1 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2 := by
    rw [cast_one_sub, ← Complex.ofReal_pow, eccOf_sq hy'.1 hy'.2]
  have hτ := hr.unif x y hy hxy
  rw [← he'sq] at hτ
  have hτ1 : ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ ≤
      kEccMin K ^ 2 / 2 := hτ.le.trans (min_le_left _ _)
  obtain ⟨hre, hnorm⟩ := sqrt_branch ha0 hae' hτ1
  refine ⟨hre, ?_⟩
  have hlt : ‖eccC (x 0) (x 1) - ((eccOf (y 0) (y 1) : ℝ) : ℂ)‖ < keplerDeltaE (kEccMax K) := by
    have h1 : ‖eccC (x 0) (x 1) - ((eccOf (y 0) (y 1) : ℝ) : ℂ)‖ * kEccMin K <
        keplerDeltaE (kEccMax K) * kEccMin K := by
      calc ‖eccC (x 0) (x 1) - ((eccOf (y 0) (y 1) : ℝ) : ℂ)‖ * kEccMin K
          ≤ ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ := hnorm
        _ < min (kEccMin K ^ 2 / 2) (kEccMin K * keplerDeltaE (kEccMax K)) := hτ
        _ ≤ kEccMin K * keplerDeltaE (kEccMax K) := min_le_right _ _
        _ = keplerDeltaE (kEccMax K) * kEccMin K := mul_comm _ _
    exact lt_of_mul_lt_mul_right h1 ha0.le
  refine ⟨hlt, ?_⟩
  have hnn : ‖((eccOf (y 0) (y 1) : ℝ) : ℂ)‖ = eccOf (y 0) (y 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (ha0.le.trans hae')]
  have h3 := norm_sub_norm_le (eccC (x 0) (x 1)) ((eccOf (y 0) (y 1) : ℝ) : ℂ)
  have h4 := Tube.deltaE_le_left (kEccMax K)
  linarith

/-- The ratio bound and the radicand-disk membership of `bpI:p7:complex-domain`: for `x` within
`δ₁` of `y ∈ 𝒦`, `|G²/L² - G'²/L'²| < τ` and `1 - G²/L² ∈ D(e(y)², e₋²/2)` with
`Re (1 - G²/L²) > e₋²/2`. -/
theorem ratio_disk_facts (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {x : Fin 2 → ℂ}
    {y : Fin 2 → ℝ} (hy : y ∈ K) (hxy : ‖x - fun i => (y i : ℂ)‖ < δ₁) :
    ‖x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2‖ < complexTau K ∧
      ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ < kEccMin K ^ 2 / 2 ∧
        kEccMin K ^ 2 / 2 < (1 - x 1 ^ 2 / x 0 ^ 2).re := by
  have hy' := hK.sub_cone y hy
  have hae' : kEccMin K ≤ eccOf (y 0) (y 1) := (kEccMin_spec hK).2 y hy
  have ha0 : 0 < kEccMin K := kEccMin_pos hK
  have he'sq : ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2 = 1 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2 := by
    rw [cast_one_sub, ← Complex.ofReal_pow, eccOf_sq hy'.1 hy'.2]
  have hτ := hr.unif x y hy hxy
  have hτ' : ‖x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2‖ < complexTau K := by
    have e : (1 - x 1 ^ 2 / x 0 ^ 2) - (1 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2) =
        -(x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2) := by ring
    rw [e, norm_neg] at hτ
    exact hτ
  refine ⟨hτ', ?_⟩
  have hdisk : ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ <
      kEccMin K ^ 2 / 2 := by
    rw [he'sq]
    exact hτ.trans_le (min_le_left _ _)
  refine ⟨hdisk, ?_⟩
  have h1 : |((1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2).re| ≤
      ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ := Complex.abs_re_le_norm _
  have h2 : ((1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2).re =
      (1 - x 1 ^ 2 / x 0 ^ 2).re - eccOf (y 0) (y 1) ^ 2 := by
    rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h3 : kEccMin K ^ 2 ≤ eccOf (y 0) (y 1) ^ 2 := pow_le_pow_left₀ ha0.le hae' 2
  have h4 := (abs_lt.1 (h1.trans_lt hdisk)).1
  rw [h2] at h4
  linarith

/-- `x₀ ≠ 0` and `Re (1 - x₁²/x₀²) > 0` on `𝒦_{δ₁}`. -/
theorem nbhd_facts (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {x : Fin 2 → ℂ}
    (hx : x ∈ actionNbhd K δ₁) : x 0 ≠ 0 ∧ 0 < (1 - x 1 ^ 2 / x 0 ^ 2).re := by
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨hL, hre, -, -⟩ := point_facts hK hr hy hxy
  refine ⟨fun h => ?_, hre⟩
  rw [h, Complex.zero_re] at hL
  linarith [kLMin_pos hK]

theorem slit_of_re_pos {z : ℂ} (h : 0 < z.re) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl h)

/-- Clause (ii) of `ComplexDomainData`: `eccC` is holomorphic on `𝒦_{δ₁}`. -/
theorem cd_diff_ecc (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) :
    DifferentiableOn ℂ (fun x : Fin 2 → ℂ => eccC (x 0) (x 1)) (actionNbhd K δ₁) := by
  intro x hx
  obtain ⟨hx0, hre⟩ := nbhd_facts hK hr hx
  have hd : DifferentiableAt ℂ (fun x : Fin 2 → ℂ => 1 - x 1 ^ 2 / x 0 ^ 2) x := by
    fun_prop (disch := exact pow_ne_zero 2 hx0)
  exact (hd.cpow_const (c := (1 / 2 : ℂ)) (slit_of_re_pos hre)).differentiableWithinAt

/-- Real points of `𝒦_{δ₁}` (clause (vi)). -/
theorem cd_real (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {v : Fin 2 → ℝ}
    (hv : (fun i => (v i : ℂ)) ∈ actionNbhd K δ₁) :
    0 < v 1 ∧ v 1 < v 0 ∧ eccC (v 0) (v 1) = (eccOf (v 0) (v 1) : ℝ) := by
  obtain ⟨y, hy, hxy⟩ := hv
  obtain ⟨hL, hre, -, -⟩ := point_facts hK hr hy hxy
  have hL' : kLMin K / 2 < v 0 := by simpa using hL
  have hv0 : 0 < v 0 := lt_trans (half_pos (kLMin_pos hK)) hL'
  have hv1 : 0 < v 1 := by
    have h := abs_lt.1 ((coord_sub_le (fun i => (v i : ℂ)) y 1).trans_lt hxy)
    have hy1 := (kGMin_spec hK).2 y hy
    have hδ := hr.le_G
    have hG := kGMin_pos hK
    simp only [Complex.ofReal_re] at h
    linarith [h.1]
  have hre' : 0 < 1 - v 1 ^ 2 / v 0 ^ 2 := by
    have : (1 - (v 1 : ℂ) ^ 2 / (v 0 : ℂ) ^ 2).re = 1 - v 1 ^ 2 / v 0 ^ 2 := by
      rw [cast_one_sub, Complex.ofReal_re]
    rw [← this]
    simpa using hre
  have hlt : v 1 < v 0 := by
    have h1 : v 1 ^ 2 / v 0 ^ 2 < 1 := by linarith
    rw [div_lt_one (by positivity)] at h1
    by_contra hcon
    have := pow_le_pow_left₀ hv0.le (not_lt.1 hcon) 2
    linarith
  refine ⟨hv1, hlt, ?_⟩
  unfold eccC eccOf
  rw [cast_one_sub]
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h12, ← Complex.ofReal_cpow hre'.le, Real.sqrt_eq_rpow]

/-- The point `(ℓ, e(L, G))` lies in the thin tube when `x` is within `δ₁` of `K`. -/
theorem tube_mem (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {x : Fin 2 → ℂ}
    (hx : x ∈ actionNbhd K δ₁) {ℓ : ℂ} (hℓ : |ℓ.im| < δ₁) :
    (ℓ, eccC (x 0) (x 1)) ∈ keplerTube (kEccMax K) := by
  have h0 := kEccMax_pos hK
  have h1 := kEccMax_lt_one hK
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨-, -, hE, -⟩ := point_facts hK hr hy hxy
  have hΔK : 0 < keplerDeltaK (kEccMax K) := Tube.deltaK_pos h0 h1
  have hδK := hr.le_deltaK
  have hy' := hK.sub_cone y hy
  have hae' : kEccMin K ≤ eccOf (y 0) (y 1) := (kEccMin_spec hK).2 y hy
  have he'1 : eccOf (y 0) (y 1) ≤ kEccMax K := (kEccMax_spec hK).2 y hy
  have ha0 : 0 < kEccMin K := kEccMin_pos hK
  refine ⟨by linarith, ?_⟩
  have hmemI : ((eccOf (y 0) (y 1) : ℝ) : ℂ) ∈ Complex.ofReal '' Icc (-kEccMax K) (kEccMax K) :=
    ⟨_, ⟨by linarith, he'1⟩, rfl⟩
  exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hmemI) (by rwa [dist_eq_norm])

/-- Clause (vii): on `𝒰(δ₁)` the arguments lie in the domain of the complex orbit map. -/
theorem cd_mem_dom (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁)
    {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hw : w ∈ UDelta K δ₁) :
    (![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ) ∈
      orbitDomC (kEccMax K) := by
  refine ⟨tube_mem hK hr hw.2 (hw.1 0), (nbhd_facts hK hr hw.2).1⟩

/-- Clause (viii): `delaunayC K` is holomorphic on `𝒰(δ₁)`. -/
theorem cd_diff_delaunay (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) :
    DifferentiableOn ℂ (delaunayC K) (UDelta K δ₁) := by
  have h0 := kEccMax_pos hK
  have h1 := kEccMax_lt_one hK
  have hd1 : ∀ i : Fin 2, Differentiable ℂ (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => w.1 i) :=
    fun i => by fun_prop
  have hd2 : ∀ i : Fin 2, Differentiable ℂ (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => w.2 i) :=
    fun i => by fun_prop
  have hecc : DifferentiableOn ℂ
      (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => eccC (w.2 0) (w.2 1)) (UDelta K δ₁) :=
    (cd_diff_ecc hK hr).comp differentiable_snd.differentiableOn (fun w hw => hw.2)
  have hdiv : DifferentiableOn ℂ
      (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) => w.2 1 / w.2 0) (UDelta K δ₁) :=
    OrbitC.differentiableOn_div (hd2 1).differentiableOn (hd2 0).differentiableOn
      (fun w hw => (nbhd_facts hK hr hw.2).1)
  have hF : DifferentiableOn ℂ
      (fun w : (Fin 2 → ℂ) × (Fin 2 → ℂ) =>
        (![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ))
      (UDelta K δ₁) := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · exact (hd1 0).differentiableOn
    · exact (hd1 1).differentiableOn
    · exact (hd2 0).differentiableOn
    · exact hecc
    · exact hdiv
  exact (orbitMapC_differentiableOn h0 h1).comp hF (fun w hw => cd_mem_dom hK hr hw)

/-! ### Real points -/

/-- The eccentric anomaly at a real point of the tube is the real one (the real solution lies in the
strip and solves the equation, so it is the unique one). -/
theorem eccAnomC_real_tube {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {ℓ e : ℝ}
    (hmem : ((ℓ : ℂ), (e : ℂ)) ∈ keplerTube e₁) (he : |e| < 1) :
    eccAnomC e₁ ((ℓ : ℂ), (e : ℂ)) = (eccAnom ℓ e : ℂ) := by
  have h2 := eccAnom_eq ℓ he
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) h2
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sin] at h3
  have hstrip : |((eccAnom ℓ e : ℝ) : ℂ).im| ≤ keplerY0 e₁ := by
    simpa using (Tube.y0_pos h0 h1).le
  exact (((keplerEq_tube h0 h1).2.2.1 _ hmem).2.2 _ hstrip h3).symm

/-- At a real point `(ℓ, g, L, e)` of the tube (not only `|e| ≤ e₁`) with `G/L = √(1 - e²)` the
complex orbit map is the complexified real one. -/
theorem orbitMapC_real_tube {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {ℓ g L e : ℝ}
    (hmem : ((ℓ : ℂ), (e : ℂ)) ∈ keplerTube e₁) (he : |e| < 1) :
    orbitMapC e₁ ![(ℓ : ℂ), (g : ℂ), (L : ℂ), (e : ℂ), ((√(1 - e ^ 2) : ℝ) : ℂ)] =
      phaseToC (orbitMapR ℓ g L e) := by
  have hu := eccAnomC_real_tube h0 h1 hmem he
  simp only [orbitMapC]
  refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [phaseToC, orbitMapR, orbitFrame, rot, hu]

/-- The real point `(ℓ, g, L, G)` with `0 < G < L` in the tube. -/
theorem delaunayC_real_pt {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {ℓ g L G : ℝ} (hG : 0 < G)
    (hGL : G < L) (hmem : ((ℓ : ℂ), ((eccOf L G : ℝ) : ℂ)) ∈ keplerTube e₁) :
    orbitMapC e₁ ![(ℓ : ℂ), (g : ℂ), (L : ℂ), ((eccOf L G : ℝ) : ℂ), (G : ℂ) / (L : ℂ)] =
      phaseToC (orbitMapR ℓ g L (eccOf L G)) := by
  have hL : 0 < L := hG.trans hGL
  have hm := eccOf_pos_lt_one hG hGL
  have hk : √(1 - eccOf L G ^ 2) = G / L := by
    have : 1 - eccOf L G ^ 2 = (G / L) ^ 2 := by rw [eccOf_sq hG hGL, div_pow]; ring
    rw [this]
    exact Real.sqrt_sq (by positivity)
  have habs : |eccOf L G| < 1 := by rw [abs_of_pos hm.1]; exact hm.2
  have := orbitMapC_real_tube h0 h1 (g := g) (L := L) hmem habs
  rw [hk] at this
  rw [← this]
  push_cast
  rfl

/-- Clause (ix): on real points the complex Delaunay map is the complexified real one. -/
theorem cd_real_eq (hK : SafeAction K) {δ₁ : ℝ} (hr : GoodRadius K δ₁) {w : Phase 2}
    (hw : phaseToC w ∈ UDelta K δ₁) : delaunayC K (phaseToC w) = phaseToC (delaunay w) := by
  have h0 := kEccMax_pos hK
  have h1 := kEccMax_lt_one hK
  obtain ⟨hG, hGL, hec⟩ := cd_real hK hr (v := w.2) hw.2
  have hmem := (cd_mem_dom hK hr hw).1
  have ht : ((w.1 0 : ℂ), eccC (w.2 0 : ℂ) (w.2 1 : ℂ)) ∈ keplerTube (kEccMax K) := hmem
  rw [hec] at ht
  show orbitMapC (kEccMax K) ![(w.1 0 : ℂ), (w.1 1 : ℂ), (w.2 0 : ℂ),
    eccC (w.2 0 : ℂ) (w.2 1 : ℂ), (w.2 1 : ℂ) / (w.2 0 : ℂ)] =
    phaseToC (orbitMapR (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)))
  rw [hec]
  exact delaunayC_real_pt h0 h1 hG hGL ht

/-- Existence of an admissible `δ₁`: the conclusion of `bpI:p7:complex-domain`. -/
theorem exists_complexDomainData (hK : SafeAction K) : ∃ δ₁, ComplexDomainData K δ₁ := by
  obtain ⟨δ₁, hr⟩ := exists_radius hK
  refine ⟨δ₁, hr.pos, hr.le, fun x hx => ?_, cd_diff_ecc hK hr, ?_, fun y hy => cd_real hK hr hy,
    fun w hw => cd_mem_dom hK hr hw, cd_diff_delaunay hK hr, fun w hw => cd_real_eq hK hr hw,
    ?_, ?_, ?_⟩
  · obtain ⟨hx0, -⟩ := nbhd_facts hK hr hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨hx0, (point_facts hK hr hy hxy).1⟩
  · intro x hx y hy hxy
    obtain ⟨-, -, h3, h4⟩ := point_facts hK hr hy hxy
    exact ⟨h3, h4⟩
  · intro x _ y hy hxy
    exact (ratio_disk_facts hK hr hy hxy).1
  · intro x _ y hy hxy
    exact (ratio_disk_facts hK hr hy hxy).2
  · intro x _
    exact sqrt_sq_eq _

end ComplexDomainAux

/-- `bpI:p7:complex-domain` (the quantifier "nearest `(L', G')`" is replaced by "every
`(L', G') ∈ K` within `δ₁`", see B1): the selected `δ₁` is admissible. -/
theorem complex_domain_spec {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) :
    ComplexDomainData K (complexDelta K) := by
  have h : ∃ δ₁ : ℝ, ComplexDomainData K δ₁ := ComplexDomainAux.exists_complexDomainData hK
  unfold complexDelta
  split
  · rename_i h'
    exact h'.choose_spec
  · rename_i h'
    exact absurd h h'

/-- The ratio bound `|G²/L² - G'²/L'²| < τ` of `bpI:p7:complex-domain` holds at the
selected radius `complexDelta K`. -/
theorem complexDelta_ratio_bound {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) :
    ∀ x ∈ actionNbhd K (complexDelta K), ∀ y ∈ K, ‖x - fun i => (y i : ℂ)‖ < complexDelta K →
      ‖x 1 ^ 2 / x 0 ^ 2 - (y 1 : ℂ) ^ 2 / (y 0 : ℂ) ^ 2‖ < complexTau K := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := complex_domain_spec hK
  exact h

/-- The radicand `1 - G²/L²` lies in `D(e(L', G')², e₋²/2)`, where its real part
exceeds `e₋²/2 > 0`, at the selected radius. -/
theorem complexDelta_radicand_disk {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) :
    ∀ x ∈ actionNbhd K (complexDelta K), ∀ y ∈ K, ‖x - fun i => (y i : ℂ)‖ < complexDelta K →
      ‖(1 - x 1 ^ 2 / x 0 ^ 2) - ((eccOf (y 0) (y 1) : ℝ) : ℂ) ^ 2‖ < kEccMin K ^ 2 / 2 ∧
        kEccMin K ^ 2 / 2 < (1 - x 1 ^ 2 / x 0 ^ 2).re := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := complex_domain_spec hK
  exact h

/-- `e(L, G)² = 1 - G²/L²` on `𝒦_{δ₁}` at the selected radius. -/
theorem complexDelta_ecc_sq {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) :
    ∀ x ∈ actionNbhd K (complexDelta K), eccC (x 0) (x 1) ^ 2 = 1 - x 1 ^ 2 / x 0 ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := complex_domain_spec hK
  exact h

/-- `delaunayC K` is `2π`-periodic in `ℓ` and in `g` on `𝒰(complexDelta K)`
(`bpI:p7:complex-domain`). -/
theorem delaunayC_periodic {K : Set (Fin 2 → ℝ)} (hK : SafeAction K)
    {w : (Fin 2 → ℂ) × (Fin 2 → ℂ)} (hw : w ∈ UDelta K (complexDelta K)) :
    delaunayC K (Function.update w.1 0 (w.1 0 + 2 * π), w.2) = delaunayC K w ∧
      delaunayC K (Function.update w.1 1 (w.1 1 + 2 * π), w.2) = delaunayC K w := by
  obtain ⟨-, -, -, -, -, -, hdom, -⟩ := complex_domain_spec hK
  have h0 := ComplexDomainAux.kEccMax_pos hK
  have h1 := ComplexDomainAux.kEccMax_lt_one hK
  have hx := hdom w hw
  have hper := orbitMapC_periodic h0 h1 hx
  constructor
  · have e : (![(Function.update w.1 0 (w.1 0 + 2 * π)) 0,
        (Function.update w.1 0 (w.1 0 + 2 * π)) 1,
        w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ) =
        Function.update (![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ)
          0 (w.1 0 + 2 * π) := by
      funext j
      fin_cases j <;> simp
    show orbitMapC (kEccMax K) _ = orbitMapC (kEccMax K) _
    rw [e]
    exact hper.1
  · have e : (![(Function.update w.1 1 (w.1 1 + 2 * π)) 0,
        (Function.update w.1 1 (w.1 1 + 2 * π)) 1,
        w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ) =
        Function.update (![w.1 0, w.1 1, w.2 0, eccC (w.2 0) (w.2 1), w.2 1 / w.2 0] : Fin 5 → ℂ)
          1 (w.1 1 + 2 * π) := by
      funext j
      fin_cases j <;> simp
    show orbitMapC (kEccMax K) _ = orbitMapC (kEccMax K) _
    rw [e]
    exact hper.2

end Part7Exact

end KAM.Iso

end
