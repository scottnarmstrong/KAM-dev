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

private theorem euclid_add_le (a b : Fin n → ℝ) : euclid (a + b) ≤ euclid a + euclid b :=
  isActionNorm_euclid.add_le a b

/-- The frequency map is `M`-Lipschitz in the Euclidean size along segments in `U_r D`. -/
private theorem freq_lip {D : Set (Fin n → ℝ)} {r : ℝ} {h : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r)) (hM0 : 0 ≤ M)
    (hess : HessBound (realNbhd D r) h M) {I J : Fin n → ℝ}
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, J + a • (I - J) ∈ realNbhd D r) :
    euclid (KAM.frequencyMap h I - KAM.frequencyMap h J) ≤ M * euclid (I - J) :=
  hess_lipschitz (isOpen_realNbhd D r) ((realPart_contDiffOn hh).of_le
    (by exact WithTop.coe_le_coe.2 le_top)) hM0 hess hseg

private theorem exp_one_ge_two : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

private theorem abs_le_of_mem_uIcc {x t : ℝ} (hx : x ∈ uIcc 0 t) : |x| ≤ |t| := by
  rcases mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact abs_le.2 ⟨by linarith [abs_nonneg t, neg_abs_le t], by linarith [abs_nonneg t, le_abs_self t]⟩

/-- `‖ω‖ · (|t| η/(e s)) ≤ m r²/24` from the time bound. -/
private theorem term_arith {m r s η eω ep t Ω : ℝ} (hm : 0 < m) (hr : 0 < r) (hs : 0 < s)
    (hη : 0 ≤ η) (hω : 0 ≤ eω) (hωΩ : eω ≤ Ω)
    (hper : ep ≤ |t| * (η / (Real.exp 1 * s))) (hb : |t| * Ω * η ≤ s * m * r ^ 2 / 12) :
    eω * ep ≤ m * r ^ 2 / 24 := by
  have hE := exp_one_ge_two
  have hEs : 0 < Real.exp 1 * s := by positivity
  have h0 : 0 ≤ |t| * (η / (Real.exp 1 * s)) := by positivity
  calc eω * ep ≤ eω * (|t| * (η / (Real.exp 1 * s))) := mul_le_mul_of_nonneg_left hper hω
    _ ≤ Ω * (|t| * (η / (Real.exp 1 * s))) := mul_le_mul_of_nonneg_right hωΩ h0
    _ = (|t| * Ω * η) / (Real.exp 1 * s) := by field_simp
    _ ≤ (s * m * r ^ 2 / 12) / (Real.exp 1 * s) := by gcongr
    _ ≤ m * r ^ 2 / 24 := by
      rw [div_le_iff₀ hEs]
      nlinarith [mul_nonneg (sub_nonneg.2 hE) (by positivity : 0 ≤ s * m * r ^ 2)]

private theorem no_exit_arith {m r δ ζ Δ eP X : ℝ} (hm : 0 < m) (hr : 0 < r) (hδ : δ ≤ m * r / 4)
    (hζ : ζ ≤ m * r ^ 2 / 32) (hΔ1 : 15 / 16 * r ≤ Δ) (hΔ2 : Δ ≤ r) (hP : eP ≤ 5 / 4 * δ)
    (hX : X ≤ m * r ^ 2 / 24) (hmain : m / 2 * Δ ^ 2 ≤ 2 * ζ + eP * Δ + X) : False := by
  have hu : 0 < m * r ^ 2 := by positivity
  have h1 : m / 2 * (15 / 16 * r) ^ 2 ≤ m / 2 * Δ ^ 2 := by gcongr
  have hΔ0 : 0 ≤ Δ := by linarith
  have h2 : eP * Δ ≤ 5 / 16 * (m * r ^ 2) := by
    calc eP * Δ ≤ 5 / 4 * δ * Δ := by gcongr
      _ ≤ 5 / 4 * (m * r / 4) * r := by gcongr
      _ = 5 / 16 * (m * r ^ 2) := by ring
  nlinarith

private theorem cone_arith {ℓ m M r δ Δ Y : ℝ} (hm : 0 < m) (hr : 0 < r) (hmr : m * r ≤ 2 * ℓ)
    (hMr : M * r ≤ ℓ / 4) (hδ : δ ≤ m * r / 4) (hΔ1 : 15 / 16 * r ≤ Δ)
    (hY : Y ≤ m * r ^ 2 / 24) : (5 / 4 * δ + M * r) * Δ + Y ≤ ℓ * Δ := by
  have hℓ : 0 < ℓ := by nlinarith [mul_pos hm hr]
  have hΔ0 : 0 ≤ Δ := by linarith
  have h1 : (5 / 4 * δ + M * r) * Δ ≤ 7 / 8 * ℓ * Δ := by
    gcongr
    linarith
  have h2 : m * r ^ 2 ≤ 2 * ℓ * r := by nlinarith
  have h3 : ℓ * r ≤ ℓ * (16 / 15 * Δ) := by gcongr; linarith
  nlinarith

end Aux

section Resonant

variable {D : Set (Fin n → ℝ)} {r s : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {m M : ℝ}
  {g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {Mg η ζ δ : ℝ}

open KAM.Nekhoroshev (euclid realPart)

private theorem M_pos (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) : 0 < M :=
  hRS.hm.trans_le hRS.hmM

private theorem resRho_pos (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) : 0 < resRho δ M :=
  div_pos hRS.hδ (by have := M_pos hRS; positivity)

private theorem resRho_le (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) :
    resRho δ M ≤ r / 16 := by
  have hM := M_pos hRS
  unfold resRho
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hRS.δ_le, mul_le_mul_of_nonneg_right hRS.hmM hRS.hr.le]

private theorem ball_mem {I₀ : Fin n → ℝ}
    (hI₀ : IsAdmissible D δ M I₀) {I : Fin n → ℝ} (hI : euclid (I - I₀) ≤ r - resRho δ M) :
    I ∈ realNbhd D r := by
  obtain ⟨J₀, hJ₀, hlt⟩ := hI₀
  refine mem_realNbhd_of_euclid_lt hJ₀ ?_
  have e : I - J₀ = (I - I₀) + (I₀ - J₀) := by abel
  rw [e]
  exact lt_of_le_of_lt (euclid_add_le _ _) (by linarith)

private theorem seg_mem {I₀ : Fin n → ℝ}
    (hI₀ : IsAdmissible D δ M I₀) {I : Fin n → ℝ} (hI : euclid (I - I₀) ≤ r - resRho δ M) :
    ∀ a ∈ Icc (0 : ℝ) 1, I₀ + a • (I - I₀) ∈ realNbhd D r := fun a ha => by
  refine ball_mem hI₀ ?_
  rw [add_sub_cancel_left]
  exact (euclid_smul_le ha _).trans hI

/-- `bpN:p7:admissible`. (The orthogonal projection `Π_Λ` is any `P` given by `exists_orthProj`.) -/
theorem admissible (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P) (hPV : ∀ v, P v ∈ resSpan Λ)
    (hPid : ∀ v ∈ resSpan Λ, P v = v) {I₀ : Fin n → ℝ} (hI₀ : IsAdmissible D δ M I₀) :
    (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M → I ∈ realNbhd D r) ∧
    (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M →
      KAM.Nekhoroshev.euclid (P (KAM.frequencyMap h I)) ≤
        5 / 4 * δ + M * KAM.Nekhoroshev.euclid (I - I₀)) ∧
    KAM.Nekhoroshev.euclid (P (KAM.frequencyMap h I₀)) ≤ 5 / 4 * δ := by
  have hM := M_pos hRS
  have hρ := resRho_pos hRS
  have hρr := resRho_le hRS
  have hr := hRS.hr
  have h3 : euclid (P (KAM.frequencyMap h I₀)) ≤ 5 / 4 * δ := by
    obtain ⟨J₀, hJ₀, hlt⟩ := hI₀
    obtain ⟨w, hw, hwδ⟩ := hRS.close J₀ hJ₀
    have hseg : ∀ a ∈ Icc (0 : ℝ) 1, J₀ + a • (I₀ - J₀) ∈ realNbhd D r := fun a ha => by
      refine mem_realNbhd_of_euclid_lt hJ₀ ?_
      rw [add_sub_cancel_left]
      linarith [euclid_smul_le ha (I₀ - J₀)]
    have hlip := freq_lip hRS.h_holo hM.le hRS.hess hseg
    have hMρ : M * euclid (I₀ - J₀) ≤ δ / 4 := by
      have : M * euclid (I₀ - J₀) ≤ M * resRho δ M := by gcongr
      refine this.trans (le_of_eq ?_)
      unfold resRho
      field_simp
    have hPw := orthProj_resSpace hP hPV hw
    have e1 : P (KAM.frequencyMap h I₀) =
        P (KAM.frequencyMap h J₀ - w) + P (KAM.frequencyMap h I₀ - KAM.frequencyMap h J₀) := by
      simp only [map_sub, hPw]
      abel
    rw [e1]
    have b1 := orthProj_euclid_le hP (KAM.frequencyMap h J₀ - w)
    have b2 := orthProj_euclid_le hP (KAM.frequencyMap h I₀ - KAM.frequencyMap h J₀)
    linarith [euclid_add_le (P (KAM.frequencyMap h J₀ - w))
      (P (KAM.frequencyMap h I₀ - KAM.frequencyMap h J₀))]
  refine ⟨fun I hI => ball_mem hI₀ hI, fun I hI => ?_, h3⟩
  have hlip := freq_lip hRS.h_holo hM.le hRS.hess (seg_mem hI₀ hI)
  have e1 : P (KAM.frequencyMap h I) =
      P (KAM.frequencyMap h I₀) + P (KAM.frequencyMap h I - KAM.frequencyMap h I₀) := by
    simp only [map_sub]
    abel
  rw [e1]
  have b2 := orthProj_euclid_le hP (KAM.frequencyMap h I - KAM.frequencyMap h I₀)
  linarith [euclid_add_le (P (KAM.frequencyMap h I₀))
    (P (KAM.frequencyMap h I - KAM.frequencyMap h I₀))]

private theorem realH_abs_le (hs : 0 < s) {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass (cpx D) r s u) {B : ℝ} (hb : WBound (cpx D) r s u B)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) : |realH u x| ≤ B :=
  (Complex.abs_re_le_norm _).trans
    ((theta_derivative hs hu hb).2 _ ((realInclusion₂_mem_Dom_iff D hs x).2 hx))

/-- The real `θ`-gradient of `realH u` at a real point is the real part of `∂_θ u`. -/
private theorem thetaGradR_realH' (hs : 0 < s) {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass (cpx D) r s u) {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r)
    (i : Fin n) : thetaGradR (realH u) x i = (dtheta i u (KAM.realInclusion₂ n x)).re := by
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s := (realInclusion₂_mem_Dom_iff D hs x).2 hx
  have hgd : DifferentiableAt ℂ u (KAM.realInclusion₂ n x) :=
    hu.differentiableOn.differentiableAt ((isOpen_Dom (n := n) (cpx D) r s).mem_nhds hxD)
  have h2 : HasFDerivAt (fun y => u (KAM.realInclusion₂ n y))
      (((fderiv ℂ u (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 := congrArg (fun L => L (Pi.single i 1, 0)) (Complex.reCLM.hasFDerivAt.comp x h2).fderiv
  unfold thetaGradR realH dtheta
  rw [show (fun y => (u (KAM.realInclusion₂ n y)).re) =
    Complex.reCLM ∘ (fun y => u (KAM.realInclusion₂ n y)) from rfl]
  simpa [KAM.realInclusion_single] using h3

private theorem gradR_bound (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) :
    euclid (thetaGradR (realH fs) x) ≤ η / (Real.exp 1 * s) := by
  have hs := hRS.hs
  have hb := ((theta_derivative hs hRS.fs_class hRS.fs_bound).1 x.1 x.2 hx.2).2
  refine le_trans ?_ hb
  unfold KAM.Nekhoroshev.euclid
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [thetaGradR_realH' hs hRS.fs_class hx i, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

/-- The energy-convexity inequality in the resonant setting (`bpN:p7:energy-core` instantiated). -/
private theorem rs_energy (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P) (hPid : ∀ v ∈ resSpan Λ, P v = v)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsOrbit (fun w => h w.2 + g w + fs w) D r J z) (hadm : IsAdmissible D δ M (z 0).2)
    {t₁ : ℝ} (ht₁ : t₁ ∈ J) (hΔ : euclid ((z t₁).2 - (z 0).2) ≤ r - resRho δ M) :
    (∀ m', (∀ a ∈ Icc (0 : ℝ) 1, m' * euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
        hessR (realPart h) ((z 0).2 + a • ((z t₁).2 - (z 0).2)) ((z t₁).2 - (z 0).2)
          ((z t₁).2 - (z 0).2)) →
      m' / 2 * euclid ((z t₁).2 - (z 0).2) ^ 2 ≤ 2 * ζ +
        euclid (P (KAM.frequencyMap h (z 0).2)) * euclid ((z t₁).2 - (z 0).2) +
        euclid (KAM.frequencyMap h (z 0).2) *
          euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2))) ∧
    euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2)) ≤ |t₁| * (η / (Real.exp 1 * s)) := by
  have hs := hRS.hs
  have hsg := real_system hs hRS.g_class hRS.g_real
  have hsf := real_system hs hRS.fs_class hRS.fs_real
  have hmem : ∀ t ∈ J, z t ∈ realStrip D r := fun t ht => (hz t ht).1
  have hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ realNbhd D r,
      realH (fun w => h w.2 + g w + fs w) x = realPart h x.2 + realH g x + realH fs x :=
    fun x _ => by
      simp only [realH, KAM.Nekhoroshev.realPart, Complex.add_re, KAM.realInclusion₂_apply]
      rfl
  have hgP : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ realNbhd D r,
      P (thetaGradR (realH g) x) = thetaGradR (realH g) x := fun x hx =>
    hPid _ (resonant_gradient hs hRS.g_class hRS.g_real hRS.g_bound hRS.g_res x hx)
  obtain ⟨-, hB, -, hD⟩ := energy_core (isOpen_realNbhd D r) (hR := realPart h)
    (g := realH g) (f := realH fs) (HR := realH (fun w => h w.2 + g w + fs w))
    ((realPart_contDiffOn hRS.h_holo).of_le (by exact WithTop.coe_le_coe.2 le_top))
    (by exact_mod_cast hsg.1 1) (by exact_mod_cast hsf.1 1) hHR hP hgP hJ h0 hz ht₁
    (seg_mem hadm hΔ)
  refine ⟨fun m' hm' => ?_, hB _ fun τ hτ => gradR_bound hRS (hmem τ (hJ.uIcc_subset h0 ht₁ hτ))⟩
  have hd : m' / 2 * euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
      |(realH g (z t₁) + realH fs (z t₁)) - (realH g (z 0) + realH fs (z 0))| +
      euclid (P (KAM.frequencyMap h (z 0).2)) * euclid ((z t₁).2 - (z 0).2) +
      euclid (KAM.frequencyMap h (z 0).2) *
        euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2)) := hD m' hm'
  have hA : |(realH g (z t₁) + realH fs (z t₁)) - (realH g (z 0) + realH fs (z 0))| ≤ 2 * ζ := by
    have a1 := abs_le.1 (realH_abs_le hs hRS.g_class hRS.g_bound (hmem t₁ ht₁))
    have a2 := abs_le.1 (realH_abs_le hs hRS.g_class hRS.g_bound (hmem 0 h0))
    have a3 := abs_le.1 (realH_abs_le hs hRS.fs_class hRS.fs_bound (hmem t₁ ht₁))
    have a4 := abs_le.1 (realH_abs_le hs hRS.fs_class hRS.fs_bound (hmem 0 h0))
    have := hRS.ζ_ge
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  linarith

/-- `bpN:p7:no-exit`: (i)-(iii) cannot hold together. -/
theorem no_exit (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsOrbit (fun w => h w.2 + g w + fs w) D r J z) (hadm : IsAdmissible D δ M (z 0).2)
    {t₁ : ℝ} (ht₁ : t₁ ∈ J) (ht₁0 : t₁ ≠ 0)
    (hi : (∀ τ ∈ uIcc 0 t₁, KAM.Nekhoroshev.euclid ((z τ).2 - (z 0).2) ≤ r - resRho δ M) ∧
      KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) = r - resRho δ M)
    (hii : ∀ a ∈ Icc (0 : ℝ) 1, m * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
      hessR (KAM.Nekhoroshev.realPart h) ((z 0).2 + a • ((z t₁).2 - (z 0).2))
        ((z t₁).2 - (z 0).2) ((z t₁).2 - (z 0).2))
    (hiii : |t₁| * KAM.Nekhoroshev.euclid (KAM.frequencyMap h (z 0).2) * η ≤ s * m * r ^ 2 / 12) :
    False := by
  obtain ⟨P, hP, hPV, hPid⟩ := exists_orthProj (resSpan Λ)
  have hρ := resRho_pos hRS
  have hρr := resRho_le hRS
  have hΔ := hi.2
  obtain ⟨hd, hb⟩ := rs_energy hRS hP hPid hJ h0 hz hadm ht₁ hi.2.le
  have hP0 := (admissible hRS hP hPV hPid hadm).2.2
  have hX := term_arith hRS.hm hRS.hr hRS.hs hRS.η_nonneg (euclid_nonneg' _) le_rfl hb hiii
  refine no_exit_arith hRS.hm hRS.hr hRS.δ_le hRS.ζ_le ?_ ?_ hP0 hX (hd m hii)
  · rw [hΔ]; linarith
  · rw [hΔ]; linarith

private theorem rs_exit (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsOrbit (fun w => h w.2 + g w + fs w) D r J z) {t : ℝ} (ht : t ∈ J)
    (hlt : r - resRho δ M < euclid ((z t).2 - (z 0).2)) :
    ∃ ts ∈ J, |ts| ≤ |t| ∧ ts ≠ 0 ∧
      (∀ τ ∈ uIcc 0 ts, euclid ((z τ).2 - (z 0).2) ≤ r - resRho δ M) ∧
      euclid ((z ts).2 - (z 0).2) = r - resRho δ M := by
  have hρ := resRho_pos hRS
  have hρr := resRho_le hRS
  have hr := hRS.hr
  have hcont : ContinuousOn z J := fun t ht => (hz t ht).2.continuousAt.continuousWithinAt
  obtain ⟨ts, hts, htsI, heq, hle⟩ := exit_ball (Nrm := fun a => euclid a) isActionNorm_euclid
    hJ h0 hcont (by linarith) ht hlt
  refine ⟨ts, hts, abs_le_of_mem_uIcc htsI, ?_, hle, heq⟩
  rintro rfl
  simp only [sub_self] at heq
  have : euclid (0 : Fin n → ℝ) = 0 := by simp [KAM.Nekhoroshev.euclid]
  linarith

/-- `bpN:p7:resonant-lemma1` (Lemma 1; off the published graph, consumed by track I only). -/
theorem resonant_lemma1 (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    (hconv : IsMConvex (realNbhd D r) h m) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + g w + fs w) D r J z →
      IsAdmissible D δ M (z 0).2 → ∀ t ∈ J,
        |t| * (12 * KAM.Nekhoroshev.euclid (KAM.frequencyMap h (z 0).2) * η) ≤ s * m * r ^ 2 →
          KAM.Nekhoroshev.euclid ((z t).2 - (z 0).2) ≤ r - resRho δ M := by
  intro J hJ h0 z hz hadm t ht hT
  by_contra hlt
  push_neg at hlt
  obtain ⟨ts, hts, hle, hts0, hmax, heq⟩ := rs_exit hRS hJ h0 hz ht hlt
  refine no_exit hRS hJ h0 hz hadm hts hts0 ⟨hmax, heq⟩ (fun a ha => ?_) ?_
  · exact hconv _ (seg_mem hadm heq.le a ha) _
  · have h1 : 0 ≤ euclid (KAM.frequencyMap h (z 0).2) * η :=
      mul_nonneg (euclid_nonneg' _) hRS.η_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hle h1]

/-- `bpN:p7:resonant-lemma2`; `Ω` is any bound of `‖ω‖₂` on the ball (the max is one). -/
theorem resonant_lemma2 (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) {ℓ : ℝ}
    (hqc : IsQuasiConvex (realNbhd D r) h ℓ m) (hR1 : r ≤ 2 * ℓ / m) (hR2 : M * r ≤ ℓ / 4)
    {I₀ : Fin n → ℝ} (hI₀ : IsAdmissible D δ M I₀) {Ω : ℝ}
    (hΩ : ∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M →
      KAM.Nekhoroshev.euclid (KAM.frequencyMap h I) ≤ Ω) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + g w + fs w) D r J z →
      (z 0).2 = I₀ → ∀ t ∈ J, |t| * (12 * Ω * η) ≤ s * m * r ^ 2 →
        KAM.Nekhoroshev.euclid ((z t).2 - I₀) ≤ r - resRho δ M := by
  intro J hJ h0 z hz hz0 t ht hT
  rw [← hz0] at hI₀ hΩ ⊢
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hP, hPV, hPid⟩ := exists_orthProj (resSpan Λ)
  have hM := M_pos hRS
  have hρ := resRho_pos hRS
  have hρr := resRho_le hRS
  have hm := hRS.hm
  have hr := hRS.hr
  have hmr : m * r ≤ 2 * ℓ := by
    have := (le_div_iff₀ hm).1 hR1
    linarith
  have hΩ0 : 0 ≤ Ω := (euclid_nonneg' _).trans (hΩ (z 0).2 (by simp [KAM.Nekhoroshev.euclid]; linarith))
  obtain ⟨ts, hts, hle, hts0, hmax, heq⟩ := rs_exit hRS hJ h0 hz ht hlt
  have hbΩ : |ts| * Ω * η ≤ s * m * r ^ 2 / 12 := by
    have h1 : 0 ≤ Ω * η := mul_nonneg hΩ0 hRS.η_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hle h1]
  obtain ⟨-, hperp⟩ := rs_energy hRS hP hPid hJ h0 hz hI₀ hts heq.le
  refine no_exit hRS hJ h0 hz hI₀ hts hts0 ⟨hmax, heq⟩ (fun a ha => ?_) ?_
  · set Δ := (z ts).2 - (z 0).2 with hΔ
    have hIa : euclid (((z 0).2 + a • Δ) - (z 0).2) ≤ r - resRho δ M := by
      rw [add_sub_cancel_left]
      exact (euclid_smul_le ha _).trans heq.le
    have hmem := seg_mem hI₀ heq.le a ha
    rcases hqc _ hmem Δ with hcase | hcase
    · exfalso
      obtain ⟨-, hPb, -⟩ := admissible hRS hP hPV hPid hI₀
      have hPa := hPb _ hIa
      have hsplit : KAM.frequencyMap h ((z 0).2 + a • Δ) ⬝ᵥ Δ =
          P (KAM.frequencyMap h ((z 0).2 + a • Δ)) ⬝ᵥ Δ +
          KAM.frequencyMap h ((z 0).2 + a • Δ) ⬝ᵥ (Δ - P Δ) := by
        rw [hP.symm, ← dotProduct_add]
        congr 1
        abel
      have c1 := abs_dot_le_euclid (P (KAM.frequencyMap h ((z 0).2 + a • Δ))) Δ
      have c2 := abs_dot_le_euclid (KAM.frequencyMap h ((z 0).2 + a • Δ)) (Δ - P Δ)
      have hY := term_arith hm hr hRS.hs hRS.η_nonneg (euclid_nonneg' _) (hΩ _ hIa) hperp hbΩ
      have hsm : euclid (a • Δ) ≤ euclid Δ := euclid_smul_le ha Δ
      rw [add_sub_cancel_left] at hPa
      have hcone := cone_arith (ℓ := ℓ) (M := M) (δ := δ) (Δ := euclid Δ)
        (Y := euclid (KAM.frequencyMap h ((z 0).2 + a • Δ)) * euclid (Δ - P Δ)) hm hr hmr hR2
        hRS.δ_le (by rw [heq]; linarith) hY
      have hMr : M * euclid (a • Δ) ≤ M * r := by
        apply mul_le_mul_of_nonneg_left _ hM.le
        linarith
      have hc1 : euclid (P (KAM.frequencyMap h ((z 0).2 + a • Δ))) * euclid Δ ≤
          (5 / 4 * δ + M * r) * euclid Δ :=
        mul_le_mul_of_nonneg_right (by linarith) (euclid_nonneg' _)
      have habs : |KAM.frequencyMap h ((z 0).2 + a • Δ) ⬝ᵥ Δ| ≤
          euclid (P (KAM.frequencyMap h ((z 0).2 + a • Δ))) * euclid Δ +
          euclid (KAM.frequencyMap h ((z 0).2 + a • Δ)) * euclid (Δ - P Δ) := by
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add c1 c2)
      linarith
    · exact hcase
  · have h1 := hΩ (z 0).2 (by simp [KAM.Nekhoroshev.euclid]; linarith)
    have h2 : 0 ≤ |ts| * η := mul_nonneg (abs_nonneg _) hRS.η_nonneg
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]

end Resonant

end KAM.Stability

end
