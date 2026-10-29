/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData

/-!
# The prepared admissibility datum (P11A-P8D, `bpP:p11:data-star`), parametric form

`data_star_of_amount` assumes, for every `ν ≥ 1`, exactly the conclusion of the signed `amount`
(P11A-P8e, proved elsewhere) and concludes exactly the statement of the signed `data_star`.
When `amount` lands the signed theorem is `data_star D := data_star_of_amount D (amount D ·)`.
The purely numeric and box clauses are separate helper lemmas.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace KAM.Planetary

section Datum

variable {n : ℕ}

theorem p11PreparedBox_isCompact (n : ℕ) : IsCompact (p11PreparedBox n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem p11PreparedBox_volume (n : ℕ) : volume (p11PreparedBox n) = 1 := by
  rw [p11PreparedBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  have : ((2 : ℝ)⁻¹ - -1 / 2) = 1 := by norm_num
  simp [this]

theorem p11PreparedBox_diam {n : ℕ} (hn : 1 ≤ n + n) : Metric.diam (p11PreparedBox n) = 1 := by
  have hbdd : Bornology.IsBounded (p11PreparedBox n) := (p11PreparedBox_isCompact n).isBounded
  have hmem : ∀ c : ℝ, -1/2 ≤ c → c ≤ 1/2 → (fun _ => c : Fin (n+n) → ℝ) ∈ p11PreparedBox n :=
    fun c h1 h2 i _ => ⟨h1, h2⟩
  have hi : Nonempty (Fin (n+n)) := ⟨⟨0, hn⟩⟩
  refine le_antisymm ?_ ?_
  · refine Metric.diam_le_of_forall_dist_le zero_le_one fun x hx y hy => ?_
    rw [dist_pi_le_iff zero_le_one]
    intro i
    have hx' := hx i (mem_univ i)
    have hy' := hy i (mem_univ i)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  · have h1 := hmem (-1/2) le_rfl (by norm_num)
    have h2 := hmem (1/2) (by norm_num) le_rfl
    refine le_trans ?_ (Metric.dist_le_diam_of_mem hbdd h2 h1)
    obtain ⟨i⟩ := hi
    refine le_trans ?_ (dist_le_pi_dist _ _ i)
    rw [Real.dist_eq]; norm_num

theorem p11_tau_max_gt (D : P11Physical n) :
    max ((n : ℝ)*(p11PatchData D).mu) (2*n) >
      max (((n+n : ℕ) : ℝ)*(p11PatchData D).mu/2-1) (((n+n : ℕ) : ℝ)-1) := by
  push_cast
  refine max_lt_iff.2 ⟨?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_left _ _)
    linarith
  · refine lt_of_lt_of_le ?_ (le_max_right _ _)
    linarith

theorem p11_one_le_L (D : P11Physical n) : 1 ≤ (p11SecularData D).L := by
  have hC : P11SecularSpec D (p11SecularData D) := (holo_chart D).choose_spec.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -⟩ := hC
  exact hL

theorem p11_one_le_M0 (D : P11Physical n) : 1 ≤ p11M0 n (p11PatchData D).mu
    (p11SecularData D).L := by
  have := p11_one_le_L D
  unfold p11M0
  have h1 : (1 : ℝ) ≤ (2*n+1 : ℝ)^((p11PatchData D).mu+1) :=
    one_le_pow₀ (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  nlinarith

/-- Numerics of `beta_eps`: positive, and at most `min 1 M` once `eps` is small. -/
theorem p11_beta_bounds (D : P11Physical n) {eps : ℝ} (heps : 0 < eps) (h1 : eps < 1)
    (hsmall : eps * (p11PatchData D).beta ≤ 1) :
    let C := p11SecularData D
    let A := p11PatchData D
    let beta := (1/2 : ℝ)*eps^(A.mu+2)*A.beta
    let M := (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2
    0 < beta ∧ beta ≤ min 1 M := by
  intro C A beta M
  have hb : 0 < A.beta := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -⟩ := p11PatchData_spec D
    exact hb
  have hL := p11_one_le_L D
  have hep : eps^(A.mu+2) ≤ eps := by
    calc eps^(A.mu+2) ≤ eps^1 := pow_le_pow_of_le_one heps.le h1.le (by omega)
      _ = eps := pow_one eps
  have hpos : 0 < beta := by positivity
  have hle : beta ≤ 1/2 := by
    calc beta = (1/2)*(eps^(A.mu+2)*A.beta) := by ring
      _ ≤ (1/2)*(eps*A.beta) := by gcongr
      _ ≤ 1/2 := by linarith
  have hM : 2 ≤ M := by
    have h2 : (2:ℝ) ≤ 2^(A.mu+1) := by
      calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^(A.mu+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (1:ℝ) ≤ (2*C.L+1)^2 := by nlinarith
    show 2 ≤ (2:ℝ)^(A.mu+1)*(2*C.L+1)^2
    nlinarith
  exact ⟨hpos, le_min (by linarith) (by linarith)⟩

/-- Parametric `data_star`: the hypothesis is exactly the conclusion of the signed `amount`. -/
theorem data_star_of_amount (D : P11Physical n)
    (hamount : ∀ nu : ℝ, 1 ≤ nu →
      ∃ epsA c3 : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c3 ∧
      ∀ eps, 0 < eps → eps ≤ epsA →
        let Q := p11PreparedData D nu eps c3
        P11PreparedFullSpec D nu eps c3 Q ∧
        (1/2 : ℝ)*eps^((p11PatchData D).mu+2)*(p11PatchData D).beta ≤
          index_def 2 (p11PatchData D).mu (p11PreparedFreqR Q) (p11PreparedBox n)) :
    IsCompact (p11PreparedBox n) ∧ volume (p11PreparedBox n)=1 ∧
    Metric.diam (p11PreparedBox n)=1 ∧
    0 < (1/4 : ℝ) ∧ 0 < (1/2 : ℝ) ∧
    max ((n : ℝ)*(p11PatchData D).mu) (2*n) >
      max (((n+n : ℕ) : ℝ)*(p11PatchData D).mu/2-1)
        (((n+n : ℕ) : ℝ)-1) ∧
    ∀ nu : ℝ, 1 ≤ nu →
      ∃ epsA c : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c ∧
      ∀ eps, 0 < eps → eps ≤ epsA →
        let C := p11SecularData D
        let A := p11PatchData D
        let beta := (1/2 : ℝ)*eps^(A.mu+2)*A.beta
        let M := (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2
        0 < beta ∧ beta ≤ min 1 M ∧
        1 ≤ p11M0 n A.mu C.L ∧
        let Q := p11PreparedData D nu eps c
        P11PreparedFullSpec D nu eps c Q ∧
          beta ≤ index_def 2 A.mu (p11PreparedFreqR Q) (p11PreparedBox n) := by
  have hn : 1 ≤ n + n := by have := D.n_ge; omega
  refine ⟨p11PreparedBox_isCompact _, p11PreparedBox_volume _, p11PreparedBox_diam hn,
    by norm_num, by norm_num, p11_tau_max_gt D, fun nu hnu => ?_⟩
  obtain ⟨epsA, c3, hA0, hA1, hc, H⟩ := hamount nu hnu
  have hb : 0 < (p11PatchData D).beta := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -⟩ := p11PatchData_spec D
    exact hb
  have hq : 0 < 1 / (1 + (p11PatchData D).beta) := by positivity
  refine ⟨min epsA (1 / (1 + (p11PatchData D).beta)), c3, lt_min hA0 hq,
    lt_of_le_of_lt (min_le_left _ _) hA1, hc, fun eps heps hle => ?_⟩
  have hleA : eps ≤ epsA := hle.trans (min_le_left _ _)
  have hlq : eps ≤ 1 / (1 + (p11PatchData D).beta) := hle.trans (min_le_right _ _)
  have hsmall : eps * (p11PatchData D).beta ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hlq
    nlinarith
  obtain ⟨hpos, hbeta⟩ := p11_beta_bounds D heps (lt_of_le_of_lt hleA hA1) hsmall
  exact ⟨hpos, hbeta, p11_one_le_M0 D, H eps heps hleA⟩

end Datum

end KAM.Planetary

end
