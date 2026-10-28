/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Poschel.Setting
public import KAM.Nekhoroshev.Poschel.Elementary
public import KAM.Nekhoroshev.Poschel.Frequency
public import KAM.Nekhoroshev.ResonanceGeometry.Covering
public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Strip.Bridges

/-!
# Block hypotheses of Theorem 1 (`bpN:p9:block-hyp`, `bpN:p9:block-stab#local-field`)

For a maximal lattice `Λ` and an action `I₀` in the block of `Λ`, the singleton tube of radius
`r = radius Λ` satisfies every premise of the Part 7 stability theorems (`block_hyp`); the
full-rank zone (`full_rank_zone`); the half-radius frequency ball `blockBall` with its guard
`block_frequency_radius`; the multiplicative time predicate `blockAdm` (full rank and `Ω = 0`
included, with no division); and `local_field`, the agreement of the indicator field and the total
Hamiltonian field on each open tube.
-/

@[expose] public noncomputable section

open Set Matrix Module Classical

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

section Tube

variable {P : Set (Fin n → ℝ)} {I0 : Fin n → ℝ} {r r0 s : ℝ}

private theorem polyNbhd_single_sub (hI : I0 ∈ P) (hr : r ≤ r0) :
    polyNbhd (cpx {I0}) r ⊆ polyNbhd (cpx P) r0 := by
  rintro I ⟨I', ⟨J, hJ, rfl⟩, hlt⟩
  rw [mem_singleton_iff] at hJ
  subst hJ
  exact ⟨KAM.realInclusion n J, ⟨J, hI, rfl⟩, hlt.trans_le hr⟩

private theorem realNbhd_single_sub (hI : I0 ∈ P) (hr : r ≤ r0) :
    realNbhd {I0} r ⊆ realNbhd P r0 := by
  rintro I ⟨J, hJ, hlt⟩
  rw [mem_singleton_iff] at hJ
  subst hJ
  exact ⟨_, hI, hlt.trans_le hr⟩

private theorem realStrip_single_sub (hI : I0 ∈ P) (hr : r ≤ r0) :
    realStrip {I0} r ⊆ realStrip P r0 :=
  prod_mono subset_rfl (realNbhd_single_sub hI hr)

private theorem Dom_single_sub (hI : I0 ∈ P) (hr : r ≤ r0) :
    Dom n (cpx {I0}) r s ⊆ Dom n (cpx P) r0 s :=
  prod_mono subset_rfl (polyNbhd_single_sub hI hr)

private theorem inClass_single {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hI : I0 ∈ P) (hr : r ≤ r0)
    (hf : InClass (cpx P) r0 s f) : InClass (cpx {I0}) r s f :=
  ⟨hf.differentiableOn.mono (Dom_single_sub hI hr), fun j z hz =>
    hf.periodic j z (Dom_single_sub hI hr hz)⟩

private theorem realOn_single {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hI : I0 ∈ P) (hr : r ≤ r0)
    (hu : RealOn (Dom n (cpx P) r0 s) u) : RealOn (Dom n (cpx {I0}) r s) u :=
  fun x hx => hu x (Dom_single_sub hI hr hx)

end Tube

section Analysis

variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The derivative of the complex frequency is bounded by `√n M` in the max operator norm. -/
private theorem fderiv_freq_bound {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) {M : ℝ} (hM : 0 ≤ M)
    (hess : ∀ I ∈ U, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v)
    {I : Fin n → ℂ} (hI : I ∈ U) : ‖fderiv ℂ (KAM.NormalForm.freq h) I‖ ≤ Real.sqrt n * M := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hfd : DifferentiableAt ℂ (KAM.NormalForm.freq h) I :=
    KAM.NormalForm.differentiableAt_freq hU hh hI
  have hcomp : ∀ i, fderiv ℂ (KAM.NormalForm.freq h) I v i =
      fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1) := fun i => by
    have h1 := (hasFDerivAt_pi'.1 hfd.hasFDerivAt) i
    have h2 : fderiv ℂ (fun J => fderiv ℂ h J (Pi.single i 1)) I =
        (ContinuousLinearMap.proj i).comp (fderiv ℂ (KAM.NormalForm.freq h) I) := h1.fderiv
    have h3 := congrArg (fun L => L v) h2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [← h3]
    exact fderiv_apply_comm_of_differentiableOn hU hh hI v (Pi.single i 1)
  have hv := hess I hI v
  have h1 : euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) =
      euclid (fderiv ℂ (KAM.NormalForm.freq h) I v) := by
    congr 1
    funext i
    exact (hcomp i).symm
  rw [h1] at hv
  calc ‖fderiv ℂ (KAM.NormalForm.freq h) I v‖
      ≤ euclid (fderiv ℂ (KAM.NormalForm.freq h) I v) := (norm_le_euclid _).1
    _ ≤ M * euclid v := hv
    _ ≤ M * (Real.sqrt n * ‖v‖) := by gcongr; exact (norm_le_euclid v).2.1
    _ = Real.sqrt n * M * ‖v‖ := by ring

private theorem im_eq_zero_single (S : Theorem1Setting P r0 s m M ell h f) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd P r0) : (h (KAM.realInclusion n I)).im = 0 := by
  have hmem : KAM.realInclusion₂ n ((0 : Fin n → ℝ), I) ∈ Dom n (cpx P) r0 s :=
    (realInclusion₂_mem_Dom_iff P S.hs _).2 ⟨mem_univ _, hI⟩
  simpa using S.real _ hmem

private theorem dotC_realInclusion (k : Fin n → ℤ) (w : Fin n → ℝ) :
    KAM.NormalForm.dotC k (KAM.realInclusion n w) = ((integerReal k ⬝ᵥ w : ℝ) : ℂ) := by
  simp [KAM.NormalForm.dotC, integerReal, dotProduct]

end Analysis

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

private theorem cover_valid (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M) :
    (theoremCover n r0 m M eps).Valid :=
  (elementary S heps heps0).2.2.2.2.2.2.2.2.2.2.2.2

theorem full_rank_zone (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M) :
    let c := theoremCover n r0 m M eps
    maximalK c.K (⊤ : Lattice n) ∧ c.radius (⊤ : Lattice n) = r0 ∧
    c.delta (⊤ : Lattice n) = m * r0 / 8 ∧
    (∀ v, proj (lattice (⊤ : Lattice n)) v = v) ∧
    (∀ I ∈ P, I ∈ actionBlock c P (KAM.frequencyMap h) (⊤ : Lattice n) ↔
      euclid (KAM.frequencyMap h I) < m * r0 / 8) := by
  intro c
  have hc : c.Valid := cover_valid S heps heps0
  have hn1 : 1 ≤ n := hc.hn
  have hK : 1 ≤ c.K := hc.hK
  have hlat : lattice (⊤ : Lattice n) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_fin_fun]
    exact latticeDim_top
  have hproj : ∀ v, proj (lattice (⊤ : Lattice n)) v = v := fun v =>
    (projection _).2.2.1 v (by rw [hlat]; trivial)
  have htop_ne : (⊤ : Lattice n) ≠ ⊥ := fun hb => by
    have := latticeDim_top (n := n)
    rw [hb, latticeDim_bot] at this
    omega
  have hdelta : c.delta (⊤ : Lattice n) = m * r0 / 8 := by
    unfold CoverParams.delta
    rw [CoverParams.radius_top hc]
    show 1 / 8 * m * r0 = m * r0 / 8
    ring
  refine ⟨((maximal (n := n) (K := c.K) (by linarith) ⊤).2.2.2.2.2.2.2.1 hK).1,
    CoverParams.radius_top hc, hdelta, hproj, fun I _ => ?_⟩
  have hq := hc.hqpos
  have hlam : c.lam n / volume_def (⊤ : Lattice n) = m * r0 / 8 := by
    rw [volume_top, div_one]
    unfold CoverParams.lam
    show 1 / 8 * m * r0 / (thmA m M * c.K) ^ n * (thmA m M * c.K) ^ n = m * r0 / 8
    have : (0 : ℝ) < (thmA m M * c.K) ^ n := pow_pos hq _
    field_simp
  have hstrat : zoneStratum c.K c.lam (n + 1) = (∅ : Set (Fin n → ℝ)) := by
    ext w
    simp only [zoneStratum, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨-, h2, -⟩
    omega
  show I ∈ P ∧ KAM.frequencyMap h I ∈ blocks c.K c.lam ⊤ ↔ _
  have hblk : KAM.frequencyMap h I ∈ blocks c.K c.lam (⊤ : Lattice n) ↔
      euclid (KAM.frequencyMap h I) < m * r0 / 8 := by
    unfold blocks zone
    simp only [hstrat, htop_ne, ↓reduceIte, sdiff_empty, mem_ofPred_eq, resonanceDistance, hproj,
      latticeDim_top, hlam]
  constructor
  · exact fun H => hblk.1 H.2
  · exact fun H => ⟨‹_›, hblk.2 H⟩

/-- Numerical relations of `block_hyp` on the radius `r` of a block. -/
private theorem block_arith (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    {Λ : Lattice n} (hΛ : maximalK (thmK n r0 m M eps) Λ) :
    let c := theoremCover n r0 m M eps
    let r := c.radius Λ
    let Ka := c.K / Real.sqrt n
    0 < r ∧ 0 < c.alpha Λ ∧ 0 < c.delta Λ ∧ eps ≤ m * r ^ 2 / 2 ^ 10 ∧
    m * r ^ 2 / 2 ^ 10 = (9 / 8 : ℝ) / 9 * (m * r ^ 2 / 2 ^ 7) ∧
    r = c.alpha Λ / ((9 / 8 : ℝ) * Real.sqrt n * M * Ka) ∧
    Ka * (Real.sqrt n * M) * r = c.alpha Λ / (9 / 8 : ℝ) ∧
    r ≤ 4 * ell / m ∧ M * r ≤ ell / 2 ∧ c.delta Λ ≤ m * r / 8 ∧
    (Λ = ⊥ → eps ≤ c.alpha Λ * r / (2 ^ 7 * 9 * Ka)) := by
  intro c r Ka
  obtain ⟨hA, -, -, hr4, hK1, -, -, heq, -, hKa0, hKsq, -, hc⟩ := elementary S heps heps0
  have hm := S.hm
  have hM : 0 < M := lt_of_lt_of_le hm S.hmM
  have hr0 := S.hr0
  have hK0 : 0 < c.K := lt_of_lt_of_le one_pos hK1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := S.hn; omega : 0 < n)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := S.hn; omega : 1 ≤ n)
  have hvol : 1 ≤ volume_def Λ := one_le_volume Λ
  have hq := hc.hqpos
  have hrpos : 0 < r := by
    show 0 < c.radius Λ
    have hv : 0 < volume_def Λ := by linarith
    exact div_pos (mul_pos (div_pos hr0 (pow_pos hq _)) (pow_pos hq _)) hv
  have hrb := hc.radius_bounds hΛ
  have hral : c.alpha Λ = 9 / 8 * M * c.K * r := rfl
  have hdel : c.delta Λ = 1 / 8 * m * r := rfl
  have hr_le : r ≤ r0 := hrb.2.1
  have hbot : (r0 / (c.A * c.K) ^ n) ≤ r := by
    have := hrb.1
    rwa [c.radius_bot] at this
  have heps' : eps ≤ m * r ^ 2 / 2 ^ 10 := by
    refine heq.trans_le ?_
    change m * (r0 / (c.A * c.K) ^ n) ^ 2 / 2 ^ 10 ≤ m * r ^ 2 / 2 ^ 10
    have h0 : 0 ≤ r0 / (c.A * c.K) ^ n := (div_pos hr0 (pow_pos hq _)).le
    have : (r0 / (c.A * c.K) ^ n) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hbot 2
    have := mul_le_mul_of_nonneg_left this hm.le
    linarith
  refine ⟨hrpos, ?_, ?_, heps', ?_, ?_, ?_, hr_le.trans hr4, ?_, ?_, fun hΛ0 => ?_⟩
  · rw [hral]; positivity
  · rw [hdel]; positivity
  · ring
  · rw [hral]
    have : Real.sqrt n * Ka = c.K := hKsq
    have hKa : Ka = c.K / Real.sqrt n := rfl
    rw [hKa]
    field_simp
  · rw [hral]
    have hKa : Ka = c.K / Real.sqrt n := rfl
    rw [hKa]
    field_simp
  · have := S.radius
    have h2 : M * r0 ≤ ell / 2 := by
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    nlinarith
  · rw [hdel]; linarith
  · subst hΛ0
    have hrbot : r = r0 / (c.A * c.K) ^ n := c.radius_bot
    have hKa : Ka = c.K / Real.sqrt n := rfl
    rw [hral, hKa]
    have h1 : m ≤ M * Real.sqrt n := by
      have := S.hmM
      nlinarith [Real.one_le_sqrt.2 hn1]
    rw [show 9 / 8 * M * c.K * r * r / (2 ^ 7 * 9 * (c.K / Real.sqrt n)) =
      M * Real.sqrt n * r ^ 2 / 2 ^ 10 by field_simp; ring]
    have : m * r ^ 2 ≤ M * Real.sqrt n * r ^ 2 := by gcongr
    have hh := heps'
    calc eps ≤ m * r ^ 2 / 2 ^ 10 := hh
      _ ≤ _ := by gcongr

theorem block_frequency_radius (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (Λ : Lattice n) (hΛ : maximalK (thmK n r0 m M eps) Λ) :
    0 ≤ (theoremCover n r0 m M eps).radius Λ / 2 ∧
    (theoremCover n r0 m M eps).radius Λ / 2 < r0 := by
  have hc := cover_valid S heps heps0
  have hle : (theoremCover n r0 m M eps).radius Λ ≤ r0 := (hc.radius_bounds hΛ).2.1
  have := S.hr0
  exact ⟨div_nonneg (hc.radius_nonneg Λ) (by norm_num), by linarith⟩

def blockBall (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (Λ : Lattice n) (hΛ : maximalK (thmK n r0 m M eps) Λ)
    (I0 : Fin n → ℝ) (hI : I0 ∈ P) : FrequencyBall S :=
  ⟨I0, hI, (theoremCover n r0 m M eps).radius Λ / 2,
    (block_frequency_radius S heps heps0 Λ hΛ).1,
    (block_frequency_radius S heps heps0 Λ hΛ).2⟩

/-- Multiplication form includes Ω=0 and full rank as infinite time, with no division by zero. -/
def blockAdm (c : CoverParams n) (s eps Om : ℝ) (Λ : Lattice n) (t : ℝ) : Prop :=
  Λ = ⊤ ∨ if Λ = ⊥ then
    |t| * (5 * eps) ≤ s * c.radius Λ * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6)
  else |t| * (288 * Om * eps) ≤
    s * c.m * c.radius Λ ^ 2 * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6)

theorem local_field (S : Theorem1Setting P r0 s m M ell h f)
    {I0 : Fin n → ℝ} (hI : I0 ∈ P) {r : ℝ} (hr : 0 < r) (hrr : r ≤ r0) :
    IsOpen (realStrip {I0} r) ∧ realStrip {I0} r ⊆ realStrip P r0 ∧
    (∀ x ∈ realStrip {I0} r,
      KAM.hamiltonianVectorField ((realStrip {I0} r).indicator (realH (fun w => h w.2 + f w))) x =
        KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x) ∧
    (∀ x ∈ realStrip P r0,
      KAM.hamiltonianVectorField ((realStrip P r0).indicator (realH (fun w => h w.2 + f w))) x =
        KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x) := by
  have hfield : ∀ {U : Set ((Fin n → ℝ) × (Fin n → ℝ))}, IsOpen U →
      ∀ x ∈ U, KAM.hamiltonianVectorField (U.indicator (realH (fun w => h w.2 + f w))) x =
        KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x := by
    intro U hU x hx
    have hev : U.indicator (realH (fun w => h w.2 + f w)) =ᶠ[nhds x]
        realH (fun w => h w.2 + f w) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => indicator_of_mem hy _
    unfold KAM.hamiltonianVectorField
    rw [hev.fderiv_eq]
  have hopen : ∀ (D : Set (Fin n → ℝ)) (ϱ : ℝ), IsOpen (realStrip D ϱ) := fun D ϱ =>
    isOpen_univ.prod (isOpen_realNbhd D ϱ)
  exact ⟨hopen _ _, realStrip_single_sub hI hrr, hfield (hopen _ _), hfield (hopen _ _)⟩

end Theorem1

end KAM.Nekhoroshev

end
