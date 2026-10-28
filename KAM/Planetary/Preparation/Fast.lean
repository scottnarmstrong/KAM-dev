/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.FastBridge
public import KAM.Planetary.Preparation.FastParams

/-!
# Fast averaging (P11A-P5, `bpP:p11:avg-fast`, `bpP:p11:sec-C#data`)

The exact CP09 preparation parameters `p11K1, p11Alpha1, p11s1, p11d1, p11eta1` (`ν₁ = 3`), the
fast data `P11FastData` with its specification `P11FastSpec`, and the exported core theorem
`avg_fast_of_spec`: for an arbitrary `C : P11SecularData n` with `P11SecularSpec D C` the
conclusion of `avg_fast` holds. The signed `avg_fast` and `p11FastData` (which select
`C = p11SecularData D` through `holo_chart`) are one-line wrappers of it. The proof is the
application of `osc_averaging` (`af-apply`), the divisor bound (`af-o1`), the smallness (S1)
(`af-o2`, via `e4`) and the bookkeeping of the conclusion (`af-concl`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Exact CP09 preparation parameters; nu1 is fixed at 3. -/
def p11K1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) : ℝ :=
  6/(Real.pi*C.sigma)*Real.log (1/(eps*C.MF))
def p11Alpha1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := C.gamma/2*p11K1 C eps^(-C.tau)
def p11s1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  min C.rC (C.gamma/(4*C.L*p11K1 C eps^(C.tau+1)))
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := min (p11s1 C eps*C.sigma) (C.rz^2)
def p11eta1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  400*(1+n)*eps*C.MF^2/(2*Real.pi*p11Alpha1 C eps*p11d1 C eps)
structure P11FastData (n : ℕ) where
  map : P11Phase (n+n) → P11Phase (n+n)
  G : P11CVec n × P11Phase n → ℂ
  f1 : P11Phase (n+n) → ℂ
  deriving Inhabited
def P11FastSpec {n : ℕ} (C : P11SecularData n) (eps : ℝ) (A : P11FastData n) : Prop :=
  let U := p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2)
  DifferentiableOn ℂ A.map U ∧ InjOn A.map U ∧
  DifferentiableOn ℂ A.f1 U ∧ KAM.Canonical.RealOn U A.f1 ∧
  DifferentiableOn ℂ A.G
    (Metric.ball (KAM.realInclusion n C.J0) (p11s1 C eps/2) ×ˢ Metric.ball 0 (C.rz/2)) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < p11s1 C eps/2 → ∀ z : Phase n, ‖z‖ < C.rz/2 →
    (A.G (KAM.realInclusion n J,KAM.realInclusion₂ n z)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ U → ∀ i,
    ((A.map (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
    ((A.map (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ A.map z u) (fderiv ℂ A.map z v)=
    KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ U, ∀ k : Fin n → ℤ, A.map (z.1+Fin.append (fun i => (k i : ℂ)) 0,z.2)=
    A.map z+(Fin.append (fun i => (k i : ℂ)) 0,0)) ∧
  MapsTo A.map U (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz) ∧
  (∀ z ∈ U, p11WorkingH C eps (A.map z)=
    C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+
    eps*A.G ((fun i : Fin n => z.2 (Fin.castAdd n i)),
      ((fun i : Fin n => z.1 (Fin.natAdd n i)),fun i : Fin n => z.2 (Fin.natAdd n i)))+A.f1 z) ∧
  p11Bound U A.f1 ((eps*C.MF)^3) ∧
  (∀ z : P11Phase n, ‖z‖ < C.rz/2 → ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 →
    let f := fun u : P11CVec n × P11CVec n => A.f1 (Fin.append u.1 z.1,Fin.append u.2 z.2)
    KAM.Weighted.WSummable f (C.sigma/6) J ∧ KAM.Weighted.wsum f (C.sigma/6) J ≤ (eps*C.MF)^3) ∧
  (∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 → ∀ z : P11Phase n, ‖z‖ < C.rz/2 →
    ‖A.G (J,z)-p11FastMean C.F J z‖ ≤ p11eta1 C eps) ∧
  ∀ z ∈ U,
    2*Real.pi*p11Alpha1 C eps*C.sigma*
      ‖(fun i : Fin n => (A.map z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤ 3*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*p11s1 C eps*
      ‖(fun i : Fin n => (A.map z).1 (Fin.castAdd n i)-z.1 (Fin.castAdd n i))‖ ≤ 9*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*C.rz*
      max (‖(fun i : Fin n => (A.map z).1 (Fin.natAdd n i)-z.1 (Fin.natAdd n i))‖)
        (‖(fun i : Fin n => (A.map z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖) ≤ 9*eps*C.MF

section Params

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The positivity and size data of `P11SecularSpec` used by the fast averaging. -/
theorem fast_consts (hC : P11SecularSpec D C) :
    0 < C.gamma ∧ 0 < C.tau ∧ 1 ≤ C.L ∧ 0 < C.rC ∧ C.rC ≤ 1 ∧ 0 < C.sigma ∧ C.sigma ≤ 1 / 4 ∧
      0 < C.rz ∧ C.rz ≤ 1 ∧ 1 ≤ C.MF := by
  obtain ⟨-, -, -, hτ, -, -, -, -, hγ0, -, -, hrC0, hrC1, -, hσ0, hσ1, hrz0, hrz1, hMF, hL1, -⟩ :=
    hC
  refine ⟨hγ0, ?_, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩
  rw [hτ]
  have : (2 : ℝ) ≤ n := by exact_mod_cast D.n_ge
  exact lt_max_of_lt_right (by linarith)

theorem p11K1_ge_one (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 1 ≤ p11K1 C eps := by
  obtain ⟨-, -, -, -, -, hσ0, hσ1, -, -, hMF⟩ := fast_consts hC
  have hℓ := log_inv_ge_one (mul_pos heps (by linarith)) hεM
  have hc : 1 ≤ 6 / (Real.pi * C.sigma) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  unfold p11K1
  nlinarith

theorem exp_p11K1 (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps) :
    Real.exp (-(2 * Real.pi * p11K1 C eps * C.sigma) / 6) = (eps * C.MF) ^ 2 := by
  obtain ⟨-, -, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hεM : 0 < eps * C.MF := mul_pos heps (by linarith)
  have h1 : -(2 * Real.pi * p11K1 C eps * C.sigma) / 6 = 2 * Real.log (eps * C.MF) := by
    unfold p11K1
    rw [one_div, Real.log_inv]
    field_simp
  rw [h1, show 2 * Real.log (eps * C.MF) = Real.log (eps * C.MF) + Real.log (eps * C.MF) by ring,
    Real.exp_add, Real.exp_log hεM, sq]

theorem p11s1_pos (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 0 < p11s1 C eps := by
  obtain ⟨hγ0, -, hL1, hrC0, -⟩ := fast_consts hC
  have hK := p11K1_ge_one hC heps hεM
  unfold p11s1
  refine lt_min hrC0 ?_
  have : 0 < p11K1 C eps ^ (C.tau + 1) := Real.rpow_pos_of_pos (by linarith) _
  positivity

theorem p11s1_le (C : P11SecularData n) (eps : ℝ) : p11s1 C eps ≤ C.rC := min_le_left _ _

theorem p11_budget (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 6 ≤ 2 * Real.pi * p11K1 C eps * C.sigma := by
  obtain ⟨-, -, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hℓ := log_inv_ge_one (mul_pos heps (by linarith)) hεM
  have : 2 * Real.pi * p11K1 C eps * C.sigma = 12 * Real.log (1 / (eps * C.MF)) := by
    unfold p11K1; field_simp; ring
  rw [this]; linarith

theorem p11_sK (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    p11K1 C eps * C.L * p11s1 C eps ≤ C.gamma * p11K1 C eps ^ (-C.tau) / 4 := by
  obtain ⟨hγ0, hτ0, hL1, -⟩ := fast_consts hC
  have hK := p11K1_ge_one hC heps hεM
  have hK0 : 0 < p11K1 C eps := by linarith
  have hL0 : 0 < C.L := by linarith
  have h1 : p11s1 C eps ≤ C.gamma / (4 * C.L * p11K1 C eps ^ (C.tau + 1)) := min_le_right _ _
  calc p11K1 C eps * C.L * p11s1 C eps
      ≤ p11K1 C eps * C.L * (C.gamma / (4 * C.L * p11K1 C eps ^ (C.tau + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C.gamma * p11K1 C eps ^ (-C.tau) / 4 := by
        rw [Real.rpow_neg hK0.le, Real.rpow_add_one hK0.ne']
        have : 0 < p11K1 C eps ^ C.tau := Real.rpow_pos_of_pos hK0 _
        field_simp

theorem p11_alpha_le (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    0 < p11Alpha1 C eps ∧ p11Alpha1 C eps ≤ 3 / 4 * C.gamma * p11K1 C eps ^ (-C.tau) := by
  obtain ⟨hγ0, -⟩ := fast_consts hC
  have hK0 : 0 < p11K1 C eps := by linarith [p11K1_ge_one hC heps hεM]
  have : 0 < p11K1 C eps ^ (-C.tau) := Real.rpow_pos_of_pos hK0 _
  unfold p11Alpha1
  constructor <;> nlinarith

/-- The signed `p11d1` is the source `d₁ = min {s₁ σ_F, r_z²}`; it is positive. -/
theorem p11d1_le (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    0 < p11d1 C eps ∧ p11d1 C eps ≤ min (p11s1 C eps * C.sigma) (C.rz * C.rz) := by
  obtain ⟨-, -, -, -, -, hσ0, -, hrz0, -, -⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  refine ⟨lt_min (mul_pos hs0 hσ0) (by positivity), ?_⟩
  unfold p11d1
  rw [sq]

/-- Reality of `h̃` at real points: the extra source premise of `osc_averaging`
(`OscHyp.real_h`) which `P11SecularSpec` does not record. -/
def P11SecularHReal {n : ℕ} (C : P11SecularData n) : Prop :=
  ∀ J : P11Vec n, KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n C.J0) (2 * C.rC) →
    (C.h (KAM.realInclusion n J)).im = 0

/-- The point of the working domain with the angles set to zero. -/
theorem zero_angle_mem {s r rz : ℝ} (J0 : P11Vec n) (hs : 0 < s) {J x y : P11CVec n}
    (hJ : ‖J - KAM.realInclusion n J0‖ < r) (hx : ‖x‖ < rz) (hy : ‖y‖ < rz) :
    ((Fin.append (0 : P11CVec n) x, Fin.append J y) : P11Phase (n + n)) ∈
      p11WorkingDom n J0 s r rz := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; simpa [Fin.append_left] using hs
  · simpa [Fin.append_left] using hJ
  · simpa [Fin.append_right] using hx
  · simpa [Fin.append_right] using hy

end Params

section Core

open KAM.Weighted KAM.Canonical

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Steps `af-apply`, `af-o1`, `af-concl` at a fixed `ε` for which (S1) holds. -/
theorem fast_spec_at (hC : P11SecularSpec D C) (hh : P11SecularHReal C) {eps : ℝ}
    (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hS1 : 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * eps * C.MF * C.sigma ≤
      p11Alpha1 C eps * p11d1 C eps) : ∃ A, P11FastSpec C eps A := by
  have hC' := hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hK1 := p11K1_ge_one hC heps hεM
  have hs0 := p11s1_pos hC heps hεM
  obtain ⟨hα0, hαK⟩ := p11_alpha_le hC heps hεM
  obtain ⟨hd0, hdle⟩ := p11d1_le hC heps hεM
  have hsmall : 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * (eps * C.MF) * C.sigma ≤
      p11Alpha1 C eps * min (p11s1 C eps * C.sigma) (C.rz ^ 2) := by
    calc _ = 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * eps * C.MF * C.sigma := by ring
      _ ≤ p11Alpha1 C eps * p11d1 C eps := hS1
      _ ≤ _ := by
        rw [← sq] at hdle
        exact mul_le_mul_of_nonneg_left (by simpa [sq] using hdle) hα0.le
  have hH := oscHyp_fast hC hh heps hs0 (p11s1_le C eps) (by linarith) hα0
    (p11_budget hC heps hεM) (p11_sK hC heps hεM) hαK hsmall
  obtain ⟨Ψ, g, fs, hV⟩ := osc_averaging hH
  dsimp only at hV
  simp only [zero_add, oscDom_eq_workingDom] at hV
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hV
  refine ⟨⟨Ψ, fun p => (eps : ℂ)⁻¹ * g (Fin.append (0 : P11CVec n) p.2.1,
    Fin.append p.1 p.2.2), fs⟩, ?_⟩
  unfold P11FastSpec
  dsimp only
  set s1 := p11s1 C eps with hs1def
  set α := p11Alpha1 C eps with hαdef
  set U := p11WorkingDom n C.J0 (C.sigma / 6) (s1 / 2) (C.rz / 2) with hUdef
  have hUo : oscDom (m := n) {C.J0} (s1 / 2) (C.rz / 2) (C.rz / 2) (C.sigma / 6) = U :=
    oscDom_eq_workingDom _ _ _ _
  have hs2 : 0 < s1 / 2 := by linarith
  have hσ6 : 0 < C.sigma / 6 := by linarith
  have hnorm : ∀ z : Phase n, ‖z‖ < C.rz / 2 → ‖KAM.realInclusion n z.1‖ < C.rz / 2 ∧
      ‖KAM.realInclusion n z.2‖ < C.rz / 2 := fun z hz => by
    rw [KAM.norm_realInclusion, KAM.norm_realInclusion]
    exact ⟨lt_of_le_of_lt (norm_fst_le z) hz, lt_of_le_of_lt (norm_snd_le z) hz⟩
  have hnormC : ∀ z : P11Phase n, ‖z‖ < C.rz / 2 → ‖z.1‖ < C.rz / 2 ∧ ‖z.2‖ < C.rz / 2 :=
    fun z hz => ⟨lt_of_le_of_lt (norm_fst_le z) hz, lt_of_le_of_lt (norm_snd_le z) hz⟩
  have hgd : DifferentiableOn ℂ g U := hUo ▸ c7.1
  have hg0 : ∀ z ∈ U, g z = g (Fin.append (0 : P11CVec n) (lastBlock (a := n) z.1),
      Fin.append (firstBlock (b := n) z.2) (lastBlock (a := n) z.2)) := by
    intro z hz
    have hzo : z ∈ oscDom (m := n) {C.J0} (s1 / 2) (C.rz / 2) (C.rz / 2) (C.sigma / 6) := hUo ▸ hz
    have h1 := c9 (oscPack z).2 hzo.2 (oscPack z).1 0
      (by rw [show ((oscPack z).1, (oscPack z).2) = oscPack z from rfl, s_osc_data]; exact hz)
      (by
        rw [oscPack_eq, p11_oscUnpack_flat]
        exact zero_angle_mem C.J0 hσ6
          (show ‖firstBlock (b := n) z.2 - KAM.realInclusion n C.J0‖ < s1 / 2 from hz.2.1)
          (show ‖lastBlock (a := n) z.1‖ < C.rz / 2 from hz.2.2.1)
          (show ‖lastBlock (a := n) z.2‖ < C.rz / 2 from hz.2.2.2))
    rw [show ((oscPack z).1, (oscPack z).2) = oscPack z from rfl, s_osc_data] at h1
    rw [h1, oscPack_eq, p11_oscUnpack_flat]
  have hflat : ∀ J : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < s1 / 2 → ∀ z : P11Phase n,
      ‖z‖ < C.rz / 2 →
        p11Flat J z.2 z.1 ∈ oscParams (m := n) {C.J0} (s1 / 2) (C.rz / 2) (C.rz / 2) :=
    fun J hJ z hz => by
      obtain ⟨hz1, hz2⟩ := hnormC z hz
      refine ⟨?_, ?_, ?_⟩
      · rw [firstBlock_p11Flat]
        refine ⟨C.J0, rfl, ?_⟩
        have : KAM.realInclusion n C.J0 = fun i => (C.J0 i : ℂ) := by funext i; simp
        rwa [← this]
      · rw [p_p11Flat]; exact hz2
      · rw [q_p11Flat]; exact hz1
  have hmemU : ∀ J : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < s1 / 2 → ∀ z : P11Phase n,
      ‖z‖ < C.rz / 2 →
        ((Fin.append (0 : P11CVec n) z.1, Fin.append J z.2) : P11Phase (n + n)) ∈ U :=
    fun J hJ z hz => zero_angle_mem C.J0 hσ6 hJ (hnormC z hz).1 (hnormC z hz).2
  refine ⟨c1, c2, hUo ▸ c12.1, c13, ?_, ?_, ?_, c4, ?_, c3, ?_, ?_, ?_, ?_, ?_⟩
  · -- G holomorphic
    have hφ : Differentiable ℂ (fun p : P11CVec n × P11Phase n =>
        ((Fin.append (0 : P11CVec n) p.2.1, Fin.append p.1 p.2.2) : P11Phase (n + n))) := by
      intro p
      refine DifferentiableAt.prodMk ?_ ?_
      · exact differentiableAt_append (differentiableAt_const _) (by fun_prop)
      · exact differentiableAt_append (by fun_prop) (by fun_prop)
    have hmaps : ∀ p ∈ Metric.ball (KAM.realInclusion n C.J0) (s1 / 2) ×ˢ
        Metric.ball (0 : P11Phase n) (C.rz / 2),
        ((Fin.append (0 : P11CVec n) p.2.1, Fin.append p.1 p.2.2) : P11Phase (n + n)) ∈ U := by
      rintro p ⟨hp1, hp2⟩
      rw [Metric.mem_ball, dist_eq_norm] at hp1
      rw [Metric.mem_ball, dist_zero_right] at hp2
      exact hmemU p.1 hp1 p.2 hp2
    exact ((hgd.comp hφ.differentiableOn hmaps).const_mul _)
  · -- G real
    intro J hJ z hz
    obtain ⟨hz1, hz2⟩ := hnorm z hz
    have hJ' : ‖KAM.realInclusion n J - KAM.realInclusion n C.J0‖ < s1 / 2 := by
      rw [← map_sub, KAM.norm_realInclusion]; exact hJ
    have hmem := zero_angle_mem (J := KAM.realInclusion n J) (x := KAM.realInclusion n z.1)
      (y := KAM.realInclusion n z.2) C.J0 hσ6 hJ' hz1 hz2
    have hre := c8 (Fin.append (0 : Fin n → ℝ) z.1, Fin.append J z.2) (by
      rw [realInclusion₂_append, map_zero]; exact hmem)
    rw [realInclusion₂_append, map_zero] at hre
    simp only [KAM.realInclusion₂_apply]
    rw [Complex.mul_im, hre]
    simp
  · -- real map
    intro z hz i
    obtain ⟨w, hw⟩ := c6 z hz
    rw [← hw]
    simp
  · -- lattice
    intro z hz k
    have := c5 z hz k
    convert this using 2
    ext <;> simp
  · -- identity
    intro z hz
    have h10 := c10 z hz
    have h0 : g z = g (Fin.append (0 : P11CVec n) fun i => z.1 (Fin.natAdd n i),
        Fin.append (fun i => z.2 (Fin.castAdd n i)) fun i => z.2 (Fin.natAdd n i)) := hg0 z hz
    unfold p11WorkingH
    have hε : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
    rw [mul_inv_cancel_left₀ hε, ← h0]
    exact h10
  · -- sup bound on f1
    intro z hz
    have hzo : z ∈ oscDom (m := n) {C.J0} (s1 / 2) (C.rz / 2) (C.rz / 2) (C.sigma / 6) := hUo ▸ hz
    have := oscBound.norm_le c12 c14 z hzo
    rw [exp_p11K1 hC heps] at this
    calc ‖fs z‖ ≤ (eps * C.MF) ^ 2 * (eps * C.MF) := this
      _ = _ := by ring
  · -- weighted bound on f1
    intro z hz J hJ
    obtain ⟨h1, h2⟩ := c14 _ (hflat J hJ z hz)
    rw [exp_p11K1 hC heps] at h2
    refine ⟨(spectator_wsummable fs z J _).2 h1, ?_⟩
    rw [spectator_wsum_eq]
    calc _ ≤ (eps * C.MF) ^ 2 * (eps * C.MF) := h2
      _ = _ := by ring
  · -- the averaged function is close to the fast mean
    intro J hJ z hz
    have hw := hmemU J hJ z hz
    have hzm : oscClass {C.J0} (s1 / 2) (C.rz / 2) (C.rz / 2) (C.sigma / 6)
        (fun z => coeff (oscFunction fun z => (eps : ℂ) * C.F z) (oscPack z).2 0) := by
      simpa [zero_add] using (osc_zero_mode hH).1
    have hb := oscBound.norm_le (c7.sub hzm) c11 _ (hUo ▸ hw)
    have hpack :
        (oscPack ((Fin.append (0 : P11CVec n) z.1, Fin.append J z.2) : P11Phase (n + n))).2 =
        p11Flat J z.2 z.1 := by
      rw [oscPack_eq]
      simp only [p11Flat]
      congr 1
      · funext i; simp [firstBlock]
      · congr 1
        · funext i; simp [lastBlock]
        · funext i; simp [lastBlock]
    simp only [hpack, coeff_zero_flat] at hb
    have hε : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
    have hrewrite : (eps : ℂ)⁻¹ * g (Fin.append 0 z.1, Fin.append J z.2) - p11FastMean C.F J z =
        (eps : ℂ)⁻¹ *
          (g (Fin.append 0 z.1, Fin.append J z.2) - eps * p11FastMean C.F J (z.1, z.2)) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
    rw [hrewrite, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg heps.le]
    refine le_trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.2 heps.le)) ?_
    unfold p11eta1
    have hm0 : 0 < min (s1 * C.sigma) (C.rz * C.rz) := lt_min (mul_pos hs0 hσ0) (mul_pos hrz0 hrz0)
    have hαp : 0 < 2 * Real.pi * α := by positivity
    calc eps⁻¹ * (400 * (1 + (n : ℝ)) * (eps * C.MF) ^ 2 /
          (2 * Real.pi * α * min (s1 * C.sigma) (C.rz * C.rz)))
        = 400 * (1 + (n : ℝ)) * eps * C.MF ^ 2 /
          (2 * Real.pi * α * min (s1 * C.sigma) (C.rz * C.rz)) := by
          field_simp
      _ ≤ _ := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact mul_le_mul_of_nonneg_left hdle hαp.le
  · -- displacement
    intro z hz
    obtain ⟨d1, d2, d3, d4⟩ := c15 z hz
    have e1 : ‖fun i : Fin n => (Ψ z).2 (Fin.castAdd n i) - z.2 (Fin.castAdd n i)‖ =
        ‖firstBlock (b := n) ((Ψ z).2 - z.2)‖ := rfl
    have e2 : ‖fun i : Fin n => (Ψ z).1 (Fin.castAdd n i) - z.1 (Fin.castAdd n i)‖ =
        ‖firstBlock (b := n) ((Ψ z).1 - z.1)‖ := rfl
    have e3 : ‖fun i : Fin n => (Ψ z).2 (Fin.natAdd n i) - z.2 (Fin.natAdd n i)‖ =
        ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ := rfl
    have e4 : ‖fun i : Fin n => (Ψ z).1 (Fin.natAdd n i) - z.1 (Fin.natAdd n i)‖ =
        ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ := rfl
    rw [e1, e2, e3, e4]
    refine ⟨by linarith, by linarith, ?_⟩
    have d3' : 2 * Real.pi * α * C.rz * ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤
        9 * eps * C.MF := by linarith
    have d4' : 2 * Real.pi * α * C.rz * ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤
        9 * eps * C.MF := by linarith
    rcases le_total (‖lastBlock (a := n) ((Ψ z).1 - z.1)‖)
      (‖lastBlock (a := n) ((Ψ z).2 - z.2)‖) with h | h
    · rw [max_eq_right h]; exact d3'
    · rw [max_eq_left h]; exact d4'

/-- `bpP:p11:avg-fast` for an arbitrary secular package: the content of `avg_fast` with
`C = p11SecularData D` replaced by any `C` with `P11SecularSpec D C`
(steps `af-apply`, `af-o1`, `af-o2`, `af-concl`). The only premise beyond the specification is
`hh`, the reality of `h̃` at real points, which `osc_averaging` takes as a hypothesis. -/
theorem avg_fast_of_spec (hC : P11SecularSpec D C) (hh : P11SecularHReal C) :
    ∃ eps1 : ℝ, 0 < eps1 ∧ eps1 < 1 ∧ ∀ eps, 0 < eps → eps ≤ eps1 →
      2^12*(1+n)*p11K1 C eps*eps*C.MF*C.sigma ≤ p11Alpha1 C eps*p11d1 C eps ∧
      ∃ A, P11FastSpec C eps A := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨ε1, h0, h1, hε⟩ := fast_small_eventually (n := n) hγ0 hτ0 hL1 hrC0 hσ0 hσ1 hrz0 hMF
  refine ⟨ε1, h0, h1, fun eps heps hle => ?_⟩
  obtain ⟨hεM, hS⟩ := hε eps heps hle
  have hS1 : 2^12*(1+n)*p11K1 C eps*eps*C.MF*C.sigma ≤ p11Alpha1 C eps*p11d1 C eps :=
    hS (p11K1 C eps) rfl
  exact ⟨hS1, fast_spec_at hC hh heps hεM hS1⟩

/-- Source rate for `η₁` (blueprint `p11-cp09-preparation.tex`, line 108, the closing note of
`bpP:p11:avg-fast`: `η₁(ε) ≤ c ε (log (1/ε))^{2τ₀+1}`, CP09 (25)). Unsigned companion to
the signed `p11eta1`; the design maps it to the graph node `bpP:p11:avg-fast` (its final clause),
which `stepP:p11:as-osc` (line 181, `ε² + η₁ √ε`) consumes. -/
theorem p11eta1_source_rate (hC : P11SecularSpec D C) :
    ∃ c eps1 : ℝ, 0 < eps1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps1 →
      p11eta1 C eps ≤ c * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  set c3 : ℝ := 6 / (Real.pi * C.sigma) with hc3
  have hc30 : 0 < c3 := by positivity
  set c2 : ℝ := min (min C.rC (C.gamma / (4 * C.L)) * C.sigma) (C.rz ^ 2) with hc2
  have hL0 : 0 < C.L := by linarith
  have hc20 : 0 < c2 :=
    lt_min (mul_pos (lt_min hrC0 (by positivity)) hσ0) (by positivity)
  refine ⟨400 * (1 + (n : ℝ)) * C.MF ^ 2 * c3 ^ (2 * C.tau + 1) / (Real.pi * C.gamma * c2),
    Real.exp (-1) / C.MF, by positivity, fun eps heps hle => ?_⟩
  have hεM : eps * C.MF ≤ Real.exp (-1) := by rwa [le_div_iff₀ hM0] at hle
  have hεM0 : 0 < eps * C.MF := mul_pos heps hM0
  have hℓ1 : 1 ≤ Real.log (1 / (eps * C.MF)) := log_inv_ge_one hεM0 hεM
  have hℓΛ : Real.log (1 / (eps * C.MF)) ≤ Real.log (1 / eps) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul heps.ne' hM0.ne']
    have := Real.log_nonneg hMF
    linarith
  have hΛ0 : 0 ≤ Real.log (1 / eps) := by linarith
  have hK1 := p11K1_ge_one hC heps hεM
  have hK0 : 0 < p11K1 C eps := by linarith
  have hKΛ : p11K1 C eps ≤ c3 * Real.log (1 / eps) :=
    mul_le_mul_of_nonneg_left hℓΛ hc30.le
  set K := p11K1 C eps with hK
  have hd : c2 / K ^ (C.tau + 1) ≤ p11d1 C eps :=
    fast_d_lower hγ0 hL1 hrC0 hσ0 hrz0 hK1 hτ0
  have hP0 : 0 < K ^ (C.tau + 1) := Real.rpow_pos_of_pos hK0 _
  have hKτ : 0 < K ^ C.tau := Real.rpow_pos_of_pos hK0 _
  have hα : p11Alpha1 C eps = C.gamma / 2 * K ^ (-C.tau) := rfl
  have hpow : K ^ (2 * C.tau + 1) = K ^ C.tau * K ^ (C.tau + 1) := by
    rw [← Real.rpow_add hK0]; ring_nf
  have hmain : p11eta1 C eps ≤
      400 * (1 + (n : ℝ)) * eps * C.MF ^ 2 * K ^ (2 * C.tau + 1) / (Real.pi * C.gamma * c2) := by
    have hd0 : 0 < p11d1 C eps := lt_of_lt_of_le (by positivity) hd
    have e : p11eta1 C eps = 400 * (1 + (n : ℝ)) * eps * C.MF ^ 2 * K ^ C.tau /
        (Real.pi * C.gamma * p11d1 C eps) := by
      unfold p11eta1
      rw [hα, Real.rpow_neg hK0.le]
      field_simp
    rw [e, hpow]
    calc _ ≤ 400 * (1 + (n : ℝ)) * eps * C.MF ^ 2 * K ^ C.tau /
          (Real.pi * C.gamma * (c2 / K ^ (C.tau + 1))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hd (by positivity))
      _ = _ := by field_simp
  calc p11eta1 C eps ≤ _ := hmain
    _ ≤ 400 * (1 + (n : ℝ)) * eps * C.MF ^ 2 * (c3 * Real.log (1 / eps)) ^ (2 * C.tau + 1) /
          (Real.pi * C.gamma * c2) := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hK0.le hKΛ (by linarith)) (by positivity)) (by positivity)
    _ = _ := by rw [Real.mul_rpow hc30.le hΛ0]; ring

end Core

end KAM.Planetary

end
