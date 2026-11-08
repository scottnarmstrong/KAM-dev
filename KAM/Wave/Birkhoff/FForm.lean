/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.FCoef

/-!
# `F` is bounded and one-smoothing (blueprint-W `bpW:w3:F`)

Package W3-DIVISOR-F, blueprint label `bpW:w3:F`.

`birkFform = δ_*⁻¹ 𝔓_c` (`𝔉`), `birkFgrad` (`∇𝔉`), `birkS = 4∇𝔉 : 𝔚³ → 𝔚⁺`,
`C_F = C_*/δ_*` (`birkCF`):
`birkF_isSmoothing` (smoothing with constant `C_*/(4δ_*)`), `norm_birkS_le` (`‖S‖₊ ≤ C_F ∏‖w^t‖`),
`birkS_pairing` (`Ω(S(w¹,w²,w³), v) = 4 𝔉(w¹,w²,w³,v)`), `birkS_perm` (symmetry),
`birkS_rho` (reality),
`birkF_real`, `norm_birkF_le` (`|F(w)| ≤ (C_F/4)‖w‖⁴`), `birkXF_eq` (`X_F(w) = S(w,w,w)`),
`birkF_isClassA` (`X_F` analytic into `𝔚⁺`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- `C_F = C_*/δ_*`. -/
def birkCF (m p : ℝ) : ℝ := waveCubicConst p / birkDeltaStar m

/-- Scaling a smoothing form by `z` scales the constant by `‖z‖`. -/
theorem IsBirkSmoothing.birkScale {ha : 0 ≤ a} {hp : 0 ≤ p} {n : ℕ} {c c' : ℝ}
    {𝔓 : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => BirkSpace) ℂ}
    {N : ContinuousMultilinearMap ℂ (fun _ : Fin n => BirkSpace) BirkSpace}
    (hS : IsBirkSmoothing a p ha hp n c 𝔓 N) (z : ℂ) (hc : ‖z‖ * c = c') :
    IsBirkSmoothing a p ha hp n c' (z • 𝔓) (z • N) where
  nonneg := by rw [← hc]; exact mul_nonneg (norm_nonneg _) hS.nonneg
  symm σ w := by simp [hS.symm σ w]
  pairing w v := by
    simp only [ContinuousMultilinearMap.smul_apply, hS.pairing, birkOmegaPlus_smul, smul_eq_mul]
  bound w := by
    simp only [ContinuousMultilinearMap.smul_apply, norm_smul]
    rw [← hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS.bound w) (norm_nonneg _)

include hm in
theorem birkDeltaStar_pos : 0 < birkDeltaStar m := by
  unfold birkDeltaStar; positivity

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `𝔉 = δ_*⁻¹ 𝔓_c`. -/
def birkFform : ContinuousMultilinearMap ℂ (fun _ : Fin 4 => BirkSpace) ℂ :=
  ((birkDeltaStar m : ℂ)⁻¹) • birkQuartForm m hm ha hp (birkFcoef_isCoef m hm)

/-- `∇𝔉 = δ_*⁻¹ ∇𝔓_c`. -/
def birkFgrad : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace :=
  ((birkDeltaStar m : ℂ)⁻¹) • birkGradML m hm ha hp (birkFcoef_isCoef m hm).bound

/-- `S = 4 ∇𝔉 : 𝔚³ → 𝔚⁺`. -/
def birkS : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace :=
  (4 : ℂ) • birkFgrad m hm ha hp

include hm in
theorem norm_inv_deltaStar : ‖((birkDeltaStar m : ℂ)⁻¹)‖ = (birkDeltaStar m)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (birkDeltaStar_pos m hm)]

include ha hp in
/-- (`bpW:w3:F`) `𝔉` is smoothing with constant `C_*/(4δ_*)`, gradient `∇𝔉`. -/
theorem birkF_isSmoothing :
    IsBirkSmoothing a p ha (by linarith) 3 (waveCubicConst p / (4 * birkDeltaStar m))
      (birkFform m hm ha hp) (birkFgrad m hm ha hp) := by
  refine (birkQuart_isSmoothing m hm ha hp (birkFcoef_isCoef m hm)).birkScale _ ?_
  rw [norm_inv_deltaStar m hm]
  have := birkDeltaStar_pos m hm
  field_simp

include ha hp in
/-- (`bpW:w3:F`) `‖S(w¹,w²,w³)‖₊ ≤ C_F ∏‖w^t‖`. -/
theorem norm_birkS_le (w : Fin 3 → BirkSpace) :
    ‖birkS m hm ha hp w‖ ≤ birkCF m p * ∏ t, ‖w t‖ := by
  have hs := birkDeltaStar_pos m hm
  have hcb := (birkFcoef_isCoef m hm).bound
  have h := norm_birkGradLp_le m hm ha hp hcb w
  show ‖((4 : ℂ) • ((birkDeltaStar m : ℂ)⁻¹ • birkGradML m hm ha hp hcb)) w‖ ≤ _
  simp only [ContinuousMultilinearMap.smul_apply, norm_smul, norm_inv_deltaStar m hm]
  have e : ‖(4 : ℂ)‖ = 4 := by simp
  rw [e]
  unfold birkCF
  calc 4 * ((birkDeltaStar m)⁻¹ * ‖birkGradML m hm ha hp hcb w‖)
      ≤ 4 * ((birkDeltaStar m)⁻¹ * (waveCubicConst p / 4 * ∏ t, ‖w t‖)) := by
        gcongr
        exact h
    _ = _ := by field_simp

include ha hp in
/-- (`bpW:w3:F`) `Ω(S(w¹,w²,w³), v) = 4 𝔉(w¹,w²,w³,v)`. -/
theorem birkS_pairing (w : Fin 3 → BirkSpace) (v : BirkSpace) :
    birkOmegaPlus a p ha (by linarith) (birkS m hm ha hp w) v =
      4 * birkFform m hm ha hp (Fin.snoc (α := fun _ => BirkSpace) w v) := by
  have h := (birkF_isSmoothing m hm ha hp).pairing w v
  show _ = 4 * _
  rw [h]
  show birkOmegaPlus a p ha _ ((4 : ℂ) • birkFgrad m hm ha hp w) v = _
  rw [birkOmegaPlus_smul]

end

theorem birkOmegaPlus_ext (ha : 0 ≤ a) (hp : 0 ≤ p) {X Y : BirkSpace}
    (h : ∀ v, birkOmegaPlus a p ha hp X v = birkOmegaPlus a p ha hp Y v) : X = Y := by
  have key : birkEmbed a (p + 1) p (by linarith) X - birkEmbed a (p + 1) p (by linarith) Y = 0 :=
    birkOmega_nondegenerate ha hp fun v => by
      have := h v
      simp only [birkOmegaPlus] at this
      rw [map_sub, sub_apply, this, sub_self]
  exact birkEmbed_injective a (p + 1) p (by linarith) (sub_eq_zero.1 key)

theorem snoc_comp_perm3 (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → BirkSpace) (v : BirkSpace) :
    (fun i => (Fin.snoc (α := fun _ => BirkSpace) w v : Fin 4 → BirkSpace)
        (Equiv.Perm.viaFintypeEmbedding σ Fin.castSuccEmb i)) =
      Fin.snoc (α := fun _ => BirkSpace) (fun i => w (σ i)) v := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    have : Equiv.Perm.viaFintypeEmbedding σ Fin.castSuccEmb (Fin.last 3) = Fin.last 3 :=
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ (by simp)
    simp only [this, Fin.snoc_last]
  | cast i =>
    have : Equiv.Perm.viaFintypeEmbedding σ Fin.castSuccEmb (Fin.castSucc i) =
        Fin.castSucc (σ i) := Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _
    simp [this]

theorem snoc_rho (w : Fin 3 → BirkSpace) (v : BirkSpace) :
    (Fin.snoc (α := fun _ => BirkSpace) (fun i => birkRho (w i)) (birkRho v) : Fin 4 → BirkSpace) =
      fun i => birkRho ((Fin.snoc (α := fun _ => BirkSpace) w v : Fin 4 → BirkSpace) i) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:F`) `S` is symmetric. -/
theorem birkS_perm (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → BirkSpace) :
    birkS m hm ha hp (fun i => w (σ i)) = birkS m hm ha hp w := by
  refine birkOmegaPlus_ext ha (by linarith) fun v => ?_
  rw [birkS_pairing m hm ha hp, birkS_pairing m hm ha hp, ← snoc_comp_perm3 σ w v]
  congr 1
  exact (birkF_isSmoothing m hm ha hp).symm _ _

include ha hp in
/-- (`bpW:w3:F`) `𝔉(ϱw¹,…,ϱw⁴) = conj 𝔉(w¹,…,w⁴)`. -/
theorem birkF_real (w : Fin 4 → BirkSpace) :
    birkFform m hm ha hp (fun i => birkRho (w i)) = conj (birkFform m hm ha hp w) := by
  have h := birkQuartForm_rho m hm ha hp (birkFcoef_isCoef m hm) w
  have hs : conj ((birkDeltaStar m : ℂ)⁻¹) = (birkDeltaStar m : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  simp only [birkFform, ContinuousMultilinearMap.smul_apply, h, map_mul, hs, smul_eq_mul]

include ha hp in
/-- (`bpW:w3:F`) `S(ϱw¹,ϱw²,ϱw³) = ϱ S(w¹,w²,w³)`. -/
theorem birkS_rho (w : Fin 3 → BirkSpace) :
    birkS m hm ha hp (fun i => birkRho (w i)) = birkRho (birkS m hm ha hp w) := by
  refine birkOmegaPlus_ext ha (by linarith) fun v' => ?_
  obtain ⟨v, rfl⟩ : ∃ v, birkRho v = v' := ⟨birkRho v', birkRho_birkRho v'⟩
  rw [birkS_pairing m hm ha hp, snoc_rho, birkF_real m hm ha hp]
  have h2 : birkOmegaPlus a p ha (by linarith) (birkRho (birkS m hm ha hp w)) (birkRho v) =
      conj (birkOmegaPlus a p ha (by linarith) (birkS m hm ha hp w) v) := by
    simp only [birkOmegaPlus]
    rw [← birkRho_birkEmbed, birkOmega_birkRho]
  rw [h2, birkS_pairing m hm ha hp, map_mul]
  have : conj (4 : ℂ) = 4 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [this]

include ha hp in
/-- (`bpW:w3:F`) `|F(w)| ≤ (C_F/4) ‖w‖⁴`. -/
theorem norm_birkF_le (w : BirkSpace) :
    ‖birkDiag (birkFform m hm ha hp) w‖ ≤ birkCF m p / 4 * ‖w‖ ^ 4 := by
  have := norm_birkDiag_le (birkF_isSmoothing m hm ha hp) w
  have e : waveCubicConst p / (4 * birkDeltaStar m) = birkCF m p / 4 := by
    unfold birkCF; have := birkDeltaStar_pos m hm; field_simp
  rw [e] at this
  exact this

include ha hp in
/-- `X_F(w) = S(w,w,w)`. -/
theorem birkXF_eq (w : BirkSpace) :
    birkDiagField (birkFgrad m hm ha hp) w = birkS m hm ha hp (fun _ => w) := by
  unfold birkDiagField
  show _ = ((4 : ℂ) • birkFgrad m hm ha hp) (fun _ => w)
  rw [ContinuousMultilinearMap.smul_apply]
  norm_num

include ha hp in
/-- (`bpW:w3:F`) `F ∈ 𝒜(𝔚)` with field `X_F = S(w,w,w)`, a cubic polynomial, analytic into `𝔚⁺`. -/
theorem birkF_isClassA :
    IsBirkClassA a p ha (by linarith) Set.univ (birkDiag (birkFform m hm ha hp))
      (birkDiagField (birkFgrad m hm ha hp)) :=
  birkDiag_isClassA (birkF_isSmoothing m hm ha hp) (birkF_real m hm ha hp)

end

end KAM.Wave

end
