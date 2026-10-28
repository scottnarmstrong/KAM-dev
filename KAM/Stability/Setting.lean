/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Strip.RealRestriction
public import KAM.Weighted.Domains
public import KAM.Weighted.Norm
public import KAM.ODE.Basic
public import KAM.Nekhoroshev.Interfaces.Norms

/-!
# Setting of the stability estimates (`bpN:p7:setting`, `bpN:p7:exit-ball`)

Real neighbourhoods `U_ϱ D`, real strips `W_ϱ = ℝⁿ × U_ϱ D`, the real Hamiltonian `realH G = Re G ∘ ι`
(total), orbits, the real part `reMap Ψ` of a map, the real `θ`-gradient and Hessian, and the norm
structure `IsActionNorm` with its two instances and the first-exit theorem `exit_ball`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Stability

open KAM.Weighted

variable {n : ℕ}

/-- `D ⊆ ℝⁿ` viewed in `ℂⁿ` (the `D` of Parts 4-6). -/
def cpx (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D

/-- `U_ϱ D = {I ∈ ℝⁿ : ∃ J ∈ D, |I - J| < ϱ}` (max norm). -/
def realNbhd (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set (Fin n → ℝ) := {I | ∃ J ∈ D, ‖I - J‖ < ϱ}

/-- `W_ϱ = ℝⁿ × U_ϱ D`. -/
def realStrip (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  univ ×ˢ realNbhd D ϱ

/-- The real Hamiltonian `G^ℝ = Re G ∘ ι` (total; equals `G` on `W_r` for `G ∈ O(r,s)^ℝ`). -/
def realH (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (G (KAM.realInclusion₂ n x)).re

/-- A `G`-orbit in `W_ϱ` on `J`. -/
def IsOrbit (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (D : Set (Fin n → ℝ)) (ϱ : ℝ) (J : Set ℝ)
    (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (realH G)) (realStrip D ϱ) J z

/-- The real part of a map of `ℂ²ⁿ`, as a map of `ℝ²ⁿ`. -/
def reMap (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => ((Ψ (KAM.realInclusion₂ n x)).1 i).re, fun i => ((Ψ (KAM.realInclusion₂ n x)).2 i).re)

/-- Real `θ`-gradient `∂_θ G(x)` of a real function. -/
def thetaGradR (G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => fderiv ℝ G x (Pi.single i 1, 0)

/-- The real Hessian `Q(I)[ξ, η] = D²h_ℝ(I)[ξ, η]`. -/
def hessR (hR : (Fin n → ℝ) → ℝ) (I ξ η : Fin n → ℝ) : ℝ := fderiv ℝ (fderiv ℝ hR) I ξ η

theorem isOpen_realNbhd (D : Set (Fin n → ℝ)) (ϱ : ℝ) : IsOpen (realNbhd D ϱ) := by
  have h : realNbhd D ϱ = ⋃ J ∈ D, ball J ϱ := by
    ext I
    simp [realNbhd, mem_ball, dist_eq_norm]
  rw [h]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem realNbhd_mono (D : Set (Fin n → ℝ)) {ϱ ϱ' : ℝ} (h : ϱ' ≤ ϱ) :
    realNbhd D ϱ' ⊆ realNbhd D ϱ :=
  fun _ ⟨J, hJ, hlt⟩ => ⟨J, hJ, hlt.trans_le h⟩

/-- `W_r = 𝒟_{r,s} ∩ ℝ²ⁿ` (for `s > 0`). -/
theorem realInclusion₂_mem_Dom_iff (D : Set (Fin n → ℝ)) {r s : ℝ} (hs : 0 < s)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s ↔ x ∈ realStrip D r := by
  simp only [Dom, cpx, realStrip, realNbhd, polyNbhd, KAM.realInclusion₂_apply, mem_prod,
    mem_univ, true_and, KAM.complexStrip, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨-, _, ⟨J, hJ, rfl⟩, h⟩
    exact ⟨J, hJ, by rwa [← map_sub, KAM.norm_realInclusion] at h⟩
  · rintro ⟨J, hJ, h⟩
    refine ⟨fun i => ?_, _, ⟨J, hJ, rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩
    simpa using hs

/-- The frozen Hamiltonian is the real Hamiltonian of `h + f` (Part 10 bridge). -/
theorem realHamiltonian_eq_realH (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    KAM.realHamiltonian h f = realH (fun w => h w.2 + f w) := rfl

/-- A norm `|·|_*` on `ℝⁿ` dominating the max norm (the two instances used: `‖·‖`, `euclid`). -/
structure IsActionNorm (N : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous N
  map_zero : N 0 = 0
  add_le : ∀ a b, N (a + b) ≤ N a + N b
  neg : ∀ a, N (-a) = N a
  smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a
  norm_le : ∀ a, ‖a‖ ≤ N a

theorem isActionNorm_norm : IsActionNorm (fun a : Fin n → ℝ => ‖a‖) where
  continuous := continuous_norm
  map_zero := norm_zero
  add_le := norm_add_le
  neg := norm_neg
  smul c a := by rw [norm_smul, Real.norm_eq_abs]
  norm_le _ := le_rfl

theorem isActionNorm_euclid : IsActionNorm (fun a : Fin n → ℝ => KAM.Nekhoroshev.euclid a) where
  continuous := by
    unfold KAM.Nekhoroshev.euclid
    fun_prop
  map_zero := by simp [KAM.Nekhoroshev.euclid]
  add_le a b := by
    unfold KAM.Nekhoroshev.euclid
    set A := Real.sqrt (∑ i, ‖a i‖ ^ 2) with hA
    set B := Real.sqrt (∑ i, ‖b i‖ ^ 2) with hB
    have hA2 : A ^ 2 = ∑ i, ‖a i‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hB2 : B ^ 2 = ∑ i, ‖b i‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hcs : ∑ i, ‖a i‖ * ‖b i‖ ≤ A * B := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖b i‖)
      rw [← hA2, ← hB2, ← mul_pow] at h
      exact abs_le_of_sq_le_sq' h (by positivity) |>.2
    have hsum : ∑ i, ‖(a + b) i‖ ^ 2 ≤ (A + B) ^ 2 := by
      calc ∑ i, ‖(a + b) i‖ ^ 2 ≤ ∑ i, (‖a i‖ + ‖b i‖) ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              gcongr
              exact norm_add_le _ _
        _ = A ^ 2 + 2 * ∑ i, ‖a i‖ * ‖b i‖ + B ^ 2 := by
            rw [hA2, hB2, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ (A + B) ^ 2 := by nlinarith
    calc Real.sqrt (∑ i, ‖(a + b) i‖ ^ 2) ≤ Real.sqrt ((A + B) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = A + B := Real.sqrt_sq (by positivity)
  neg a := by simp [KAM.Nekhoroshev.euclid]
  smul c a := by
    unfold KAM.Nekhoroshev.euclid
    have : ∑ i, ‖(c • a) i‖ ^ 2 = |c| ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp [mul_pow]
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  norm_le a := (KAM.Nekhoroshev.norm_le_euclid a).1

/-- A real continuous function on `[0, b]` that starts below `ϱ` and ends above it has a first
time at which it equals `ϱ`. -/
private theorem first_hit {φ : ℝ → ℝ} {b ϱ : ℝ} (hb0 : 0 ≤ b) (hφ : ContinuousOn φ (Icc 0 b)) (h0 : φ 0 < ϱ)
    (hb : ϱ < φ b) : ∃ t ∈ Icc 0 b, φ t = ϱ ∧ ∀ τ ∈ Icc 0 t, φ τ ≤ ϱ := by
  set S := Icc 0 b ∩ φ ⁻¹' Ici ϱ with hS
  have hSc : IsClosed S := hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨b, ⟨hb0, le_rfl⟩, hb.le⟩
  have hSb : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  set t := sInf S with ht
  have htS : t ∈ S := hSc.csInf_mem hSne hSb
  have hlt : ∀ τ ∈ Ico 0 t, φ τ < ϱ := by
    intro τ hτ
    by_contra hge
    rw [not_lt] at hge
    have : τ ∈ S := ⟨⟨hτ.1, hτ.2.le.trans (htS.1.2)⟩, hge⟩
    exact absurd (csInf_le hSb this) (not_le.2 hτ.2)
  have ht0 : 0 < t := by
    rcases htS.1.1.eq_or_lt with h | h
    · have h2 : ϱ ≤ φ t := htS.2
      rw [← h] at h2
      exact absurd h2 (not_le.2 h0)
    · exact h
  have hT : IsClosed (Icc 0 b ∩ φ ⁻¹' Iic ϱ) :=
    hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcl : t ∈ closure (Ico 0 t) := by
    rw [closure_Ico ht0.ne]
    exact ⟨ht0.le, le_rfl⟩
  have htT : t ∈ Icc 0 b ∩ φ ⁻¹' Iic ϱ := by
    refine hT.closure_subset_iff.2 (fun τ hτ => ⟨⟨hτ.1, hτ.2.le.trans htS.1.2⟩, (hlt τ hτ).le⟩) hcl
  refine ⟨t, htS.1, le_antisymm htT.2 htS.2, fun τ hτ => ?_⟩
  rcases hτ.2.eq_or_lt with h | h
  · rw [h]; exact htT.2
  · exact (hlt τ ⟨hτ.1, h⟩).le

/-- `bpN:p7:exit-ball`. -/
theorem exit_ball {Nrm : (Fin n → ℝ) → ℝ} (hN : IsActionNorm Nrm) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ContinuousOn z J) {ϱ : ℝ}
    (hϱ : 0 < ϱ) {t₁ : ℝ} (ht₁ : t₁ ∈ J) (hexit : ϱ < Nrm ((z t₁).2 - (z 0).2)) :
    ∃ tstar ∈ J, tstar ∈ uIcc 0 t₁ ∧ Nrm ((z tstar).2 - (z 0).2) = ϱ ∧
      ∀ τ ∈ uIcc 0 tstar, Nrm ((z τ).2 - (z 0).2) ≤ ϱ := by
  have hsub : uIcc 0 t₁ ⊆ J := hJ.uIcc_subset h0 ht₁
  have hc : ContinuousOn (fun τ => Nrm ((z τ).2 - (z 0).2)) (uIcc 0 t₁) :=
    hN.continuous.comp_continuousOn
      (((continuous_snd.comp_continuousOn (hz.mono hsub))).sub continuousOn_const)
  have h00 : Nrm ((z 0).2 - (z 0).2) < ϱ := by simpa [hN.map_zero] using hϱ
  rcases le_total 0 t₁ with h | h
  · rw [uIcc_of_le h] at hc hsub
    obtain ⟨t, ht, he, hle⟩ := first_hit h hc h00 hexit
    refine ⟨t, hsub ht, by rw [uIcc_of_le h]; exact ht, he, fun τ hτ => ?_⟩
    rw [uIcc_of_le ht.1] at hτ
    exact hle τ hτ
  · rw [uIcc_of_ge h] at hc hsub
    have hc' : ContinuousOn (fun τ => Nrm ((z (-τ)).2 - (z 0).2)) (Icc 0 (-t₁)) := by
      refine hc.comp continuous_neg.continuousOn (fun τ hτ => ⟨?_, ?_⟩) <;> linarith [hτ.1, hτ.2]
    obtain ⟨t, ht, he, hle⟩ := first_hit (φ := fun τ => Nrm ((z (-τ)).2 - (z 0).2)) (by linarith) hc'
      (by simpa using h00) (by simpa using hexit)
    have hmem : -t ∈ Icc t₁ 0 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨-t, hsub hmem, by rw [uIcc_of_ge h]; exact hmem, he, fun τ hτ => ?_⟩
    rw [uIcc_of_ge (by linarith [ht.1] : -t ≤ 0)] at hτ
    simpa using hle (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩

end KAM.Stability

end
