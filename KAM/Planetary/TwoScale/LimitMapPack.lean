/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapLip

/-!
# Two-scale KAM: the private conditional helper `psi_lip_of_steps` (`bpP:p3:psi-lip`)

Packages `stepP:p3:pl-dom`, `stepP:p3:pl-disp`, `stepP:p3:pl-lip`, `stepP:p3:pl-sum` for the
stage maps `Ψ_{j+1}` of `iterative`, from `PsiSteps` (the proved outputs of `iterative` on the
shared witnesses; `iterative_steps` discharges it). Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

namespace PsiSteps

/-- `c Ê₀ ≤ 1/2` and `Ê₀ < 1/(8192 n)` from the KAM smallness condition. -/
theorem kam_small (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    (24 : ℝ) ^ (p.τ + 1) / 6 * eHat p ≤ 1 / 2 ∧
      8192 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by
  have hs : kamConstant (a + b) p.τ * eHat p < 1 := (P.hyp 0).small
  have he : 0 ≤ eHat p := (P.hyp 0).eHat_nonneg
  have h1 : (24 : ℝ) ^ (p.τ + 1) / 3 ≤ kamConstant (a + b) p.τ := le_max_right _ _
  have h2 : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h1 he]
  · nlinarith [mul_le_mul_of_nonneg_right h2 he]

/-- The scaled displacement bound of `stepP:p3:pl-disp`. -/
theorem psi_disp (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {x : Phase (a + b)}
    (hx : x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2)) :
    limitmap_data (rhoHat p) p.s (psiR (Ψ (j + 1)) x - x) ≤ 3 / 4 * eHat (seq p j) / 12 ^ j := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have hR := P.rho_pos j
  have he := (P.hyp j).eHat_nonneg
  obtain ⟨-, -, b2, b3⟩ := P.psi_step j hx
  unfold limitmap_data
  refine max_le ?_ ?_
  · have b3' : ‖(psiR (Ψ (j + 1)) x - x).1‖ * (2 * π) ≤ 3 / 4 * eHat (seq p j) * (seq p j).s := by
      rw [mul_comm]; exact b3
    calc ‖(psiR (Ψ (j + 1)) x - x).1‖ * (2 * π / p.s)
        = (‖(psiR (Ψ (j + 1)) x - x).1‖ * (2 * π)) / p.s := by ring
      _ ≤ (3 / 4 * eHat (seq p j) * (seq p j).s) / p.s := by gcongr
      _ = _ := by rw [seq_s]; field_simp
  · have hup := P.rho_upper j
    have h1216 : (12 : ℝ) ^ j ≤ 16 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    calc ‖(psiR (Ψ (j + 1)) x - x).2‖ / rhoHat p
        ≤ (3 / 4 * eHat (seq p j) * (rhoHat p / 16 ^ j)) / rhoHat p := by
          gcongr; exact b2.trans (by gcongr)
      _ = 3 / 4 * eHat (seq p j) / 16 ^ j := by field_simp
      _ ≤ _ := by gcongr

end PsiSteps

/-- The local obligation `psi_lip` of `two_scale_kam` (private conditional helper, P23-18):
* (`pl-dom`) `Ψ_{k}` maps `𝒟_k × ℝⁿ` into `𝒟_{k-1} × ℝⁿ` (`𝒟_j = Re(D_j)_{ρ_j/2}`), and the real
  restriction `psiR` is the real part of the complex map;
* (`pl-disp`) scaled displacement `≤ (3/4) Ê_{k-1} 12^{-(k-1)}`;
* (`pl-lip`) rescaled Lipschitz constant `ς_k = 192 n c^{k-1} Ê_{k-1}`, `c = 24^{τ+1}/6`;
* (`pl-sum`) `Σ ς_k ≤ 384 n Ê₀ < 1/20`. -/
theorem psi_lip_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      KAM.realInclusion₂ (a + b) (psiR (Ψ (j + 1)) x) = Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∧
      psiR (Ψ (j + 1)) x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) ∧
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      limitmap_data (rhoHat p) p.s (psiR (Ψ (j + 1)) x - x) ≤ 3 / 4 * eHat (seq p j) / 12 ^ j) ∧
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      ∀ y ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      limitmap_data (rhoHat p) p.s
          ((psiR (Ψ (j + 1)) x - x) - (psiR (Ψ (j + 1)) y - y)) ≤
        192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)) *
          limitmap_data (rhoHat p) p.s (x - y)) ∧
    Summable (fun j =>
      192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j))) ∧
    ∑' j, 192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)) ≤
      384 * ((a + b : ℕ) : ℝ) * eHat p ∧
    384 * ((a + b : ℕ) : ℝ) * eHat p < 1 / 20 := by
  obtain ⟨hc, hk⟩ := P.kam_small
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have he0 := (P.hyp 0).eHat_nonneg
  have h0 : eHat (seq p 0) < 1 / 2 := by have := (P.hyp 0).eHat_lt_small; linarith
  have hsum := sums (e := fun j => eHat (seq p j)) (R := fun j => rhoHat (seq p j))
    (s := fun j => (seq p j).s) (c := (24 : ℝ) ^ (p.τ + 1) / 6)
    (fun j => (P.hyp j).eHat_nonneg) h0 (fun j => (P.eHat_sq j).le) (by positivity) hc
    (fun j => ⟨(P.rho_pos j).le, P.rho_hi j⟩) (fun j => rfl)
  refine ⟨fun j x hx => ?_, fun j x hx => P.psi_disp j hx,
    fun j x hx y hy => P.psi_lip_step j hx hy,
    hsum.2.2.1.mul_left _, ?_, ?_⟩
  · exact ⟨(P.psi_step j hx).1, (P.psi_step j hx).2.1⟩
  · rw [tsum_mul_left]
    have := hsum.2.2.2.1
    calc 192 * ((a + b : ℕ) : ℝ) * ∑' j, ((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)
        ≤ 192 * ((a + b : ℕ) : ℝ) * (2 * eHat (seq p 0)) := by gcongr
      _ = _ := by simp only [seq]; ring
  · nlinarith

end KAM.Planetary

end
