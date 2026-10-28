/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Energy
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Nekhoroshev.Stability.Transfer

/-!
# The resonant setting and Lemmas 1, 2 (`bpN:p7:s-energy#rs`, `admissible`, `no-exit`,
`resonant-lemma1`, `resonant-lemma2`)

The resonant setting `ResSetting`, the radius `resRho`, admissible initial actions, and the
energy-convexity argument: `admissible`, `no_exit`, `resonant_lemma1`, `resonant_lemma2`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- `bpN:p7:s-energy#rs`: the resonant setting (RS); `Mg`, `η` bound `|g|`, `|f_*|`. -/
structure ResSetting (D : Set (Fin n → ℝ)) (r s : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (m M : ℝ) (g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (Mg η ζ δ : ℝ) : Prop where
  hn : 1 ≤ n
  hr : 0 < r
  hs : 0 < s
  h_holo : DifferentiableOn ℂ h (polyNbhd (cpx D) r)
  h_real : RealOn (Dom n (cpx D) r s) (fun w => h w.2)
  hm : 0 < m
  hmM : m ≤ M
  hess : HessBound (realNbhd D r) h M
  g_class : InClass (cpx D) r s g
  g_real : RealOn (Dom n (cpx D) r s) g
  g_bound : WBound (cpx D) r s g Mg
  g_res : ∀ I ∈ polyNbhd (cpx D) r, ∀ k, k ∉ Λ → coeff g I k = 0
  fs_class : InClass (cpx D) r s fs
  fs_real : RealOn (Dom n (cpx D) r s) fs
  fs_bound : WBound (cpx D) r s fs η
  η_nonneg : 0 ≤ η
  ζ_ge : Mg + η ≤ ζ
  hδ : 0 < δ
  close : IsCloseToRes D Λ h δ
  δ_le : δ ≤ m * r / 4
  ζ_le : ζ ≤ m * r ^ 2 / 32

/-- `ρ = δ/(4M)`. -/
def resRho (δ M : ℝ) : ℝ := δ / (4 * M)

/-- Admissible initial action: `‖I₀ - J₀‖₂ < ρ` for some `J₀ ∈ D`. -/
def IsAdmissible (D : Set (Fin n → ℝ)) (δ M : ℝ) (I₀ : Fin n → ℝ) : Prop :=
  ∃ J₀ ∈ D, KAM.Nekhoroshev.euclid (I₀ - J₀) < resRho δ M

section Aux

open KAM.Nekhoroshev (euclid realPart)

private theorem euclid_nonneg' (x : Fin n → ℝ) : 0 ≤ euclid x := Real.sqrt_nonneg _

private theorem euclid_smul_le {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (x : Fin n → ℝ) :
    euclid (a • x) ≤ euclid x := by
  rw [isActionNorm_euclid.smul, abs_of_nonneg ha.1]
  exact mul_le_of_le_one_left (euclid_nonneg' x) ha.2

private theorem mem_realNbhd_of_euclid_lt {D : Set (Fin n → ℝ)} {r : ℝ} {I J : Fin n → ℝ}
    (hJ : J ∈ D) (h : euclid (I - J) < r) : I ∈ realNbhd D r :=
  ⟨J, hJ, ((KAM.Nekhoroshev.norm_le_euclid _).1).trans_lt h⟩

private theorem realInclusion_mem_polyNbhd' {D : Set (Fin n → ℝ)} {ϱ : ℝ} {I : Fin n → ℝ}
    (hI : I ∈ realNbhd D ϱ) : KAM.realInclusion n I ∈ polyNbhd (cpx D) ϱ := by
  obtain ⟨J', hJ', hlt⟩ := hI
  exact ⟨KAM.realInclusion n J', ⟨J', hJ', rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩

/-- An orthogonal projection does not increase the Euclidean size. -/
private theorem orthProj_euclid_le {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (v : Fin n → ℝ) : euclid (P v) ≤ euclid v := by
  have h1 : euclid (P v) ^ 2 = v ⬝ᵥ P v := by
    rw [euclid_sq_eq_dot, hP.symm, hP.idem]
  have h2 : euclid (P v) * euclid (P v) ≤ euclid v * euclid (P v) := by
    calc euclid (P v) * euclid (P v) = v ⬝ᵥ P v := by rw [← sq, h1]
      _ ≤ |v ⬝ᵥ P v| := le_abs_self _
      _ ≤ euclid v * euclid (P v) := abs_dot_le_euclid _ _
  rcases (euclid_nonneg' (P v)).eq_or_lt with h | h
  · rw [← h]; exact euclid_nonneg' v
  · exact le_of_mul_le_mul_right h2 h

private theorem dot_resSpace {Λ : Set (Fin n → ℤ)} {w : Fin n → ℝ} (hw : w ∈ resSpace Λ)
    {u : Fin n → ℝ} (hu : u ∈ resSpan Λ) : u ⬝ᵥ w = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact hw k hk
  | zero => simp
  | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]

private theorem orthProj_resSpace {Λ : Set (Fin n → ℤ)} {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hP : IsOrthProj P) (hPV : ∀ v, P v ∈ resSpan Λ) {w : Fin n → ℝ} (hw : w ∈ resSpace Λ) :
    P w = 0 := by
  have h1 : P w ⬝ᵥ P w = 0 := by
    rw [hP.symm, hP.idem, dotProduct_comm]
    exact dot_resSpace hw (hPV w)
  exact dotProduct_self_eq_zero.1 h1

private theorem realPart_contDiffOn {D : Set (Fin n → ℝ)} {r : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)) :
    ContDiffOn ℝ ∞ (realPart h) (realNbhd D r) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_polyNbhd (cpx D) r) hh
  have h1 : ContDiffOn ℝ ∞ h (polyNbhd (cpx D) r) := hreg.2.2.1.restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun x => h (KAM.realInclusion n x)) (realNbhd D r) :=
    h1.comp (KAM.realInclusion n).contDiff.contDiffOn fun x hx => realInclusion_mem_polyNbhd' hx
  exact Complex.reCLM.contDiff.comp_contDiffOn h2

/-- Mean value inequality for the gradient in the Euclidean size, from a Hessian bound. -/
private theorem hess_lipschitz {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    (h2 : ContDiffOn ℝ 2 hR U) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ I ∈ U, ∀ ξ η, |hessR hR I ξ η| ≤ M * euclid ξ * euclid η) {I J : Fin n → ℝ}
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, J + a • (I - J) ∈ U) :
    euclid ((fun i => fderiv ℝ hR I (Pi.single i 1)) - fun i => fderiv ℝ hR J (Pi.single i 1)) ≤
      M * euclid (I - J) := by
  set v : Fin n → ℝ :=
    (fun i => fderiv ℝ hR I (Pi.single i 1)) - fun i => fderiv ℝ hR J (Pi.single i 1) with hv
  set Δ : Fin n → ℝ := I - J with hΔ
  have hp : ∀ a : ℝ, HasDerivAt (fun a : ℝ => J + a • Δ) Δ a := fun a => by
    simpa using ((hasDerivAt_id a).smul_const Δ).const_add J
  have hat : ∀ a ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 hR (J + a • Δ) := fun a ha =>
    h2.contDiffAt (hU.mem_nhds (hseg a ha))
  have hd : ∀ a ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun a : ℝ => fderiv ℝ hR (J + a • Δ) v)
      (hessR hR (J + a • Δ) Δ v) (Icc (0 : ℝ) 1) a := fun a ha => by
    have h1 : DifferentiableAt ℝ (fderiv ℝ hR) (J + a • Δ) :=
      ((hat a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h3 := h1.hasFDerivAt.comp_hasDerivAt a (hp a)
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt a h3).hasDerivWithinAt
  have hbd : ∀ a ∈ Icc (0 : ℝ) 1, ‖hessR hR (J + a • Δ) Δ v‖ ≤ M * euclid Δ * euclid v :=
    fun a ha => by
      rw [Real.norm_eq_abs]
      exact hM _ (hseg a ha) _ _
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd (convex_Icc 0 1)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have hval : fderiv ℝ hR (J + (1 : ℝ) • Δ) v - fderiv ℝ hR (J + (0 : ℝ) • Δ) v =
      euclid v ^ 2 := by
    have e1 : J + (1 : ℝ) • Δ = I := by rw [hΔ, one_smul]; abel
    have e0 : J + (0 : ℝ) • Δ = J := by rw [zero_smul, add_zero]
    rw [e1, e0, clm_eq_dot (fderiv ℝ hR I), clm_eq_dot (fderiv ℝ hR J), ← sub_dotProduct,
      euclid_sq_eq_dot]
  rw [hval, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sub_zero, norm_one, mul_one] at hmv
  have hE : 0 ≤ euclid v := euclid_nonneg' v
  rcases hE.eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg hM0 (euclid_nonneg' _)
  · nlinarith [mul_pos h h]

end Aux

end KAM.Stability

end
