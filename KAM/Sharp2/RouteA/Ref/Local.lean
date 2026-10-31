/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Correction
public import KAM.Sharp2.RouteA.Geometry
public import KAM.Sharp2.RouteA.Ref.Constants
public import KAM.Sharp2.RouteA.Torsion
public import KAM.Sharp2.TorsionRef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lever L8′ of route A: the two torsion estimates

* `Ref.Adm0`: admissibility without the bounds of the torsion;
* `Ref.torsionAB_sub_le`: the frame part `𝒯_ab` of the torsion changes by at most `C_Δab D`
  (the first part of `KAM.Sharp2.RouteA.torsion_sub_le`);
* `Ref.local_bound`: `|T - 𝒯_ab| ≤ B_loc x` on `T_{r-δ}` (`bp:p2s2:torsion-local`), with the
  small-divisor constant at the bite `δ/2`;
* `Ref.RefT`, `Ref.AdmR`, `Ref.AdmR.entry`: the reference data of the initial torus, the
  admissibility of a stage, and Lemma `bp:p2s2:torsion-ref`: at the entry to a stage the bounds of
  `T` and `⟨T⟩⁻¹` follow from the reference data.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA.Ref

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Admissibility at the strip `r`, without the bounds of the torsion. -/
structure Adm0 {n : ℕ} (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (r β ε mK mB mLt mN mNt : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  r_pos : 0 < r
  β_pos : 0 < β
  ε_nonneg : 0 ≤ ε
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball_sub : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  deriv_le : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ mK
  gram : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ mB
  tangentT : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ mLt
  normal : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mN
  normalT : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ mNt
  error_le : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ ε

namespace Adm0

variable {r β ε mK mB mLt mN mNt : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Raising the values of the caps. -/
theorem mono {mK' mB' mLt' mN' mNt' : ℝ} (hA : Adm0 𝔅 h ω r β ε mK mB mLt mN mNt K)
    (h1 : mK ≤ mK') (h2 : mB ≤ mB') (h3 : mLt ≤ mLt') (h4 : mN ≤ mN') (h5 : mNt ≤ mNt') :
    Adm0 𝔅 h ω r β ε mK' mB' mLt' mN' mNt' K :=
  { hA with
    deriv_le := fun θ hθ => (hA.deriv_le θ hθ).trans h1
    gram := fun θ hθ => ⟨(hA.gram θ hθ).1, (hA.gram θ hθ).2.trans h2⟩
    tangentT := fun θ hθ => (hA.tangentT θ hθ).trans h3
    normal := fun θ hθ => (hA.normal θ hθ).trans h4
    normalT := fun θ hθ => (hA.normalT θ hθ).trans h5 }

theorem mem (hA : Adm0 𝔅 h ω r β ε mK mB mLt mN mNt K) :
    ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
  hA.ball_sub θ hθ (Metric.mem_ball_self hA.β_pos)

/-- With the bounds of the torsion, the admissibility of the additive step. -/
theorem toAdmA {rT mT mH : ℝ} (hA : Adm0 𝔅 h ω r β ε mK mB mLt mN mNt K)
    (htors : ∀ θ ∈ complexStrip n rT, ‖torsion h K ω θ‖ ≤ mH)
    (htw : IsUnit (torsionAverage h K ω).det ∧ ‖(torsionAverage h K ω)⁻¹‖ ≤ mT) :
    AdmA 𝔅 h ω r rT β ε mK mB mT mLt mN mNt mH K :=
  { hA with
    tors := htors
    twist := htw }

end Adm0

/-- The change of `𝒯_ab` (the first part of `torsion_sub_le`). -/
theorem torsionAB_sub_le {p : StepInA} (hp : p.Pos) (hpn : p.n = n)
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {β d δ : ℝ} {θ : Fin n → ℂ} (hδ : 0 < δ)
    (hδD : δ ≤ p.δ) (hKθ : K θ ∈ 𝔅) (hK'θ : K' θ ∈ 𝔅) (hball : Metric.ball (K θ) β ⊆ 𝔅)
    (hd : ‖K' θ - K θ‖ ≤ d) (hdβ : d < β) (hNt : ‖(normalMat K θ)ᵀ‖ ≤ p.sNt)
    (hN' : ‖normalMat K' θ‖ ≤ p.sN) (hbar : BarBd p K K' θ (d / δ)) :
    ‖torsionAB h K' θ - torsionAB h K θ‖ ≤ p.CDab * (d / δ) := by
  subst hpn
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  set D := d / δ with hDdef
  have hD0 : 0 ≤ D := div_nonneg hd0 hδ.le
  have hdeq : d = δ * D := by rw [hDdef]; field_simp
  have hsN := hp.sN
  have hsNt := hp.sNt
  have hM1 := hp.M1
  have hM2 := hp.M2
  have hA : ‖linMat h K θ‖ ≤ p.M1 := by rw [FrameAux.norm_linMat]; exact hd1 _ hKθ
  have hA' : ‖linMat h K' θ‖ ≤ p.M1 := by rw [FrameAux.norm_linMat]; exact hd1 _ hK'θ
  have hdA := norm_linMat_sub_le_M2 hS hd2 hp.M2 hball hd hdβ
  rw [TorsionRef.torsionAB_eq_tAB, TorsionRef.torsionAB_eq_tAB]
  set A := linMat h K θ
  set A' := linMat h K' θ
  set L := tangentMat K θ
  set L' := tangentMat K' θ
  set B := (gramMatrix K θ)⁻¹
  set B' := (gramMatrix K' θ)⁻¹
  have hY : ‖B * Lᵀ‖ ≤ p.sNt := by rw [norm_B_Lt]; exact hNt
  have hdY : ‖B' * L'ᵀ - B * Lᵀ‖ ≤ p.CNtd * D := by
    have := hbar.dNt
    rwa [← norm_mul_omegaZeroMatrix, Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega] at this
  have hZ' : ‖L' * B'‖ ≤ p.sN := by rw [norm_L_B]; exact hN'
  have hdZ : ‖L' * B' - L * B‖ ≤ p.CNd * D := by
    have := hbar.dN
    rw [← norm_omegaZeroMatrix_mul, Matrix.mul_sub]
    simpa only [normalMat, Matrix.mul_assoc] using this
  have hX : ‖A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A‖ ≤ 2 * p.M1 := norm_comm_le hA
  have hX' : ‖A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A'‖ ≤ 2 * p.M1 := norm_comm_le hA'
  have hdX : ‖(A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
      (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A)‖ ≤ 2 * (p.M2 * d) := by
    have e : (A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
        (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A) =
        (A' - A) * omegaZeroMatrix p.n - omegaZeroMatrix p.n * (A' - A) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [e]
    exact norm_comm_le hdA
  rw [tAB_eq, tAB_eq]
  refine (triple_sub_le _ _ _ _ _ _).trans ?_
  have h1 : ‖B' * L'ᵀ - B * Lᵀ‖ * ‖A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A'‖ *
      ‖L' * B'‖ ≤ p.CNtd * D * (2 * p.M1) * p.sN :=
    mul_le_mul (mul_le_mul hdY hX' (norm_nonneg _) (mul_nonneg hp.CNtd hD0)) hZ' (norm_nonneg _)
      (mul_nonneg (mul_nonneg hp.CNtd hD0) (by positivity))
  have h2 : ‖B * Lᵀ‖ * ‖(A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
      (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A)‖ * ‖L' * B'‖ ≤
      p.sNt * (2 * (p.M2 * d)) * p.sN :=
    mul_le_mul (mul_le_mul hY hdX (norm_nonneg _) hsNt) hZ' (norm_nonneg _)
      (mul_nonneg hsNt (by positivity))
  have h3 : ‖B * Lᵀ‖ * ‖A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A‖ *
      ‖L' * B' - L * B‖ ≤ p.sNt * (2 * p.M1) * (p.CNd * D) :=
    mul_le_mul (mul_le_mul hY hX (norm_nonneg _) hsNt) hdZ (norm_nonneg _)
      (mul_nonneg hsNt (by positivity))
  have h4 : p.sNt * (2 * (p.M2 * d)) * p.sN ≤ 2 * p.M2 * p.sNt * p.sN * p.δ * D := by
    rw [hdeq]
    have : p.sNt * (2 * (p.M2 * (δ * D))) * p.sN = 2 * p.M2 * p.sNt * p.sN * D * δ := by ring
    rw [this]
    have h5 := mul_le_mul_of_nonneg_left hδD
      (show 0 ≤ 2 * p.M2 * p.sNt * p.sN * D by positivity)
    linarith
  calc _ ≤ p.CNtd * D * (2 * p.M1) * p.sN + 2 * p.M2 * p.sNt * p.sN * p.δ * D +
        p.sNt * (2 * p.M1) * (p.CNd * D) := add_le_add (add_le_add h1 (h2.trans h4)) h3
    _ = p.CDab * D := by unfold StepInA.CDab; ring

/-- `bp:p2s2:torsion-local`, at the data of a stage: `|T - 𝒯_ab| ≤ B_loc x` on `T_{r-δ}`. -/
theorem local_bound {p : StepInA} (hp : p.Pos) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω) {r β ε δ ch : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : Adm0 𝔅 h ω r β ε p.sK p.sB p.sLt p.sN p.sNt K) (hδ : 0 < δ) (hδD : δ ≤ p.δ)
    (h2δ : 2 * δ < r) (hεδ : ε ≤ δ) (hc : SDConst n p.κ γ (δ / 2) ch Ω) :
    ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ - torsionAB h K θ‖ ≤
      p.bLoc0 ch * (ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) := by
  intro θ hθ
  subst hpn
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hκ := hp.κ_ge
  have hθr : θ ∈ complexStrip p.n r := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hK𝔅 := hK.mem
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  have hηNd := Correction.diffOn_etaN hηd
  have hHN : ∀ θ ∈ complexStrip p.n r, ‖etaN h K ω θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  have hθ2 : θ ∈ complexStrip p.n (r - 2 * (δ / 2)) := by
    rwa [show r - 2 * (δ / 2) = r - δ by ring]
  have hΩ := norm_lagrangeMat_le hS hp.n_pos hc hω hr (by linarith) hK.holo hK.primary hK𝔅 hηNd hHN
    θ hθ2
  have hL : ‖tangentMat K θ‖ ≤ p.sK :=
    (FrameAux.norm_tangentMat K θ).le.trans (hK.deriv_le θ hθr)
  have hA : ‖linMat h K θ‖ ≤ p.M1 := by
    rw [FrameAux.norm_linMat]; exact hd1 _ (hK𝔅 θ hθr)
  have hAt : ‖(linMat h K θ)ᵀ‖ ≤ p.M1 := by
    rw [FrameSharp.linMat_transpose hS (hK𝔅 θ hθr), norm_mul_omegaZeroMatrix,
      norm_omegaZeroMatrix_mul]
    exact hA
  obtain ⟨hF, hFt⟩ := geo_de_any hS hK.holo hK𝔅 hK.error_le hδ θ hθ
  have hεδ1 : ε / δ ≤ 1 := (div_le_one hδ).2 hεδ
  have hεδ0 : 0 ≤ ε / δ := div_nonneg hε0 hδ.le
  have hsK := hp.sK
  have hsB := hp.sB
  have hsLt := hp.sLt
  have hsNt := hp.sNt
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hWw : ‖(tangentMat K θ)ᵀ * ((linMat h K θ)ᵀ + linMat h K θ) * tangentMat K θ -
      (errDerivMat h K ω θ)ᵀ * tangentMat K θ - (tangentMat K θ)ᵀ * errDerivMat h K ω θ‖ ≤ p.w := by
    refine (norm_W_le hA hAt hL (hK.tangentT θ hθr) hF hFt).trans ?_
    have e : p.sLt * (2 * p.M1) * p.sK + 2 * p.n * ε / δ * p.sK + p.sLt * (p.n * ε / δ) =
        2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt) * (ε / δ) := by ring
    rw [e]
    unfold StepInA.w
    have : (2 * (p.n : ℝ) * p.sK + p.n * p.sLt) * (ε / δ) ≤ 2 * p.n * p.sK + p.n * p.sLt :=
      mul_le_of_le_one_right (by positivity) hεδ1
    linarith
  have key := norm_torsion_sub_torsionAB_le hS hr hK.holo hK𝔅 (fun θ hθ => (hK.gram θ hθ).1) hθr
    (hK.gram θ hθr).2 (hK.normalT θ hθr) hF hWw hΩ
  refine key.trans ?_
  obtain ⟨-, -, -, -, -, s6, s7, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set x := ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) with hx
  have hx0 : 0 ≤ x := div_nonneg hε0 (by positivity)
  have b4 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 2 * (2 * p.κ) - 1) 4 hγ hγb hδ hδD (by linarith)) hx0
  have b3 := mul_le_mul_of_nonneg_right
    (pow_mul_rpow_le (j := 3 * p.κ - 1) 3 hγ hγb hδ hδD (by linarith)) hx0
  have hch0 : 0 ≤ ch := by
    have := hc.c_pos
    exact this.le
  have h2p : (0 : ℝ) < 2 ^ (p.κ + 1) := Real.rpow_pos_of_pos two_pos _
  have hδp : 0 < δ ^ (p.κ + 1) := Real.rpow_pos_of_pos hδ _
  have e2 : 2 * ((p.n : ℝ) - 1) * ch * (p.sLt * ε) / (γ * (δ / 2) ^ (p.κ + 1)) =
      2 ^ (p.κ + 1) * (2 * ((p.n : ℝ) - 1) * ch * p.sLt) * (ε / (γ * δ ^ (p.κ + 1))) := by
    rw [Real.div_rpow hδ.le two_pos.le]
    field_simp
  have e1 : (p.n : ℝ) * ε / δ = p.n * (ε / δ) := mul_div_assoc _ _ _
  rw [e2, e1, s6, s7]
  have hn1 : 0 ≤ (p.n : ℝ) - 1 := by linarith [hp.n_cast]
  have hw0 := hp.w
  have c1 : p.sNt * p.sB * (p.n * (γ ^ 4 * δ ^ (2 * (2 * p.κ) - 1) * x)) ≤
      p.sNt * p.sB * (p.n * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b4 hn0) (mul_nonneg hsNt hsB)
  have c2 : p.sB ^ 3 * p.w * (2 ^ (p.κ + 1) * (2 * ((p.n : ℝ) - 1) * ch * p.sLt) *
        (γ ^ 3 * δ ^ (3 * p.κ - 1) * x)) ≤
      p.sB ^ 3 * p.w * (2 ^ (p.κ + 1) * (2 * ((p.n : ℝ) - 1) * ch * p.sLt) *
        (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1) * x)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b3 (by positivity)) (by positivity)
  refine (add_le_add c1 c2).trans (le_of_eq ?_)
  unfold StepInA.bLoc0
  ring

/-- The data of the initial torus `K₀`, on the strip `T_R`: `|⟨T₀⟩⁻¹| ≤ m_T`, `|T₀| ≤ H`, and the
local bound `b_F`. -/
structure RefT {n : ℕ} (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K₀ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (R bF iH mT : ℝ) : Prop where
  cont : Continuous (fun x : Fin n → ℝ => torsion h K₀ ω (fun i => (x i : ℂ)))
  unit : IsUnit (torsionAverage h K₀ ω).det
  inv : ‖(torsionAverage h K₀ ω)⁻¹‖ ≤ mT
  tors : ∀ θ ∈ complexStrip n R, ‖torsion h K₀ ω θ‖ ≤ iH
  loc : ∀ θ ∈ complexStrip n R, ‖torsion h K₀ ω θ - torsionAB h K₀ θ‖ ≤ bF

/-- Admissibility of a stage: `𝒯_ab` is compared with that of `K₀`, on `T_{rT}`. -/
structure AdmR {n : ℕ} (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ)
    (K₀ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (r rT β ε mK mB mAb mLt mN mNt : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop extends
    Adm0 𝔅 h ω r β ε mK mB mLt mN mNt K where
  tab : ∀ θ ∈ complexStrip n rT, ‖torsionAB h K θ - torsionAB h K₀ θ‖ ≤ mAb

/-- Lemma `bp:p2s2:torsion-ref` at the entry to a stage. -/
theorem AdmR.entry {K₀ K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {r rT β ε mK mB mAb mLt mN mNt R bF iH mT σ t : ℝ}
    (hK : AdmR 𝔅 h ω K₀ r rT β ε mK mB mAb mLt mN mNt K) (hR : RefT h K₀ ω R bF iH mT)
    (hsub : complexStrip n rT ⊆ complexStrip n R)
    (hcont : Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))))
    (hrT : 0 < rT) (hloc : ∀ θ ∈ complexStrip n rT, ‖torsion h K ω θ - torsionAB h K θ‖ ≤ bF)
    (hm0 : 0 < mT) (hmσ : mT < σ) (hβ : mAb + 2 * bF ≤ (σ - mT) / (σ * mT))
    (ht : iH + mAb + 2 * bF ≤ t) : AdmA 𝔅 h ω r rT β ε mK mB σ mLt mN mNt t K := by
  have hd : ∀ θ ∈ complexStrip n rT, ‖torsion h K ω θ - torsion h K₀ ω θ‖ ≤ mAb + 2 * bF := by
    intro θ hθ
    have e : torsion h K ω θ - torsion h K₀ ω θ = (torsion h K ω θ - torsionAB h K θ) +
        (torsionAB h K θ - torsionAB h K₀ θ) - (torsion h K₀ ω θ - torsionAB h K₀ θ) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_add_le (torsion h K ω θ - torsionAB h K θ)
      (torsionAB h K θ - torsionAB h K₀ θ)
    have h2 := hloc θ hθ
    have h3 := hK.tab θ hθ
    have h4 := hR.loc θ (hsub hθ)
    linarith
  have havg := norm_torsionAverage_sub_le_any hR.cont hcont
    (fun x => hd _ (ofReal_mem_complexStrip hrT x))
  refine hK.toAdm0.toAdmA (fun θ hθ => ?_) (inv_le_of_ref hR.unit hR.inv hm0 hmσ (havg.trans hβ))
  have e : torsion h K ω θ = torsion h K₀ ω θ + (torsion h K ω θ - torsion h K₀ ω θ) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := hR.tors θ (hsub hθ)
  have h2 := hd θ hθ
  linarith

end KAM.Sharp2.RouteA.Ref

end
