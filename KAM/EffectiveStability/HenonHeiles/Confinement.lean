/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Check
public import KAM.EffectiveStability.HenonHeiles.Eval
public import KAM.EffectiveStability.OscillatorChainPhysicalDisc

/-!
# Confinement for the Hénon–Heiles Hamiltonian (track B, B3-CERT)

`henonHeiles_confinement`: for `H = I₁ - (√2/2) I₂ + q₁² q₂ - q₂³/3`, every initial point with
both actions `≤ (1/12500)²` has a solution on an interval `(-T₁, T₁)`, `T₁ > 10¹⁰`, unique among
solutions on intervals through `0`, whose actions stay `< 101/10¹⁰` and within `12/10¹⁰` of their
initial values for `|t| ≤ 10¹⁰`.

The proof applies `oscillatorChain_physical_disc` to the certificate `hhCert`, whose Boolean
checker `hhCert_check` was verified in the kernel (`Check`); the premises are unpacked from the
checker exactly as in `checkOscChain_sound`, and the producer's scalars
`σ = 1/12500`, `s = 5657/5·10⁷`, `d = 209/10¹³` discharge the physical-box arithmetic.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open Set CartPoly

theorem henonHeiles_confinement (z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ (1 / 12500) ^ 2) :
    ∃ T₁ : ℝ, 10 ^ 10 < T₁ ∧ ∃ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField
        (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
          (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
            + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField
          (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
            (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
              + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 10 ^ 10 → ∀ j,
        KAM.Planetary.oscillatorAction (z t).2 (z t).1 j < 101 / 10 ^ 10 ∧
        |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
            KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 12 / 10 ^ 10 := by
  have hc := hhCert_check
  unfold checkOscChain at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hH, hN⟩, hP⟩, hA⟩, hok⟩, hdom⟩, hδc⟩, hεb⟩, hT⟩, hall⟩ := hc
  have hK : ∀ i : Fin 2, _ := fun i => hall i i.2
  have hr0 := fun i : Fin 2 => (hK i).1.1.1.1
  have hd1 := fun i : Fin 2 => (hK i).1.1.1.2
  have hη := fun i : Fin 2 => (hK i).1.1.2
  have hdr := fun i : Fin 2 => (hK i).1.2
  have hmg := fun i : Fin 2 => (hK i).2
  have ha : ∀ j : Fin 2, hhCert.a.getD j 0 = 6561 / 1000000000000 := fun j => by
    fin_cases j <;> simp [hhCert]
  have hrr : ∀ j : Fin 2, hhCert.r.getD j 0 = 14143 / 100000000 := fun j => by
    fin_cases j <;> simp [hhCert]
  have hee : ∀ j : Fin 2, hhCert.η.getD j 0 = 1 / 10000000000000000000 := fun j => by
    fin_cases j <;> simp [hhCert]
  have htail : oscTail hhCert.steps = 147597 / 2000000000000 := by decide +kernel
  have htailR : (oscTail hhCert.steps : ℝ) = 147597 / 2000000000000 := by
    rw [htail]; norm_num
  have hTc : (hhCert.T : ℝ) = 10 ^ 10 := by simp [hhCert]; norm_num
  obtain ⟨T₁, hT₁, z, hz0, hder, huniq, hb⟩ := oscillatorChain_physical_disc
    (K := QSqrt2) (cartFitsB_sound hH) (cartFitsB_sound hN)
    (cartFitsB_sound hP) hA (oscChainOKB_sound _ _ hok) (δc := (hhCert.δc : ℝ))
    (by exact_mod_cast hδc)
    (fun j => (hhCert.a.getD j 0 : ℝ)) (fun j => (hhCert.b.getD j 0 : ℝ))
    (fun j => (hhCert.η.getD j 0 : ℝ))
    (hhCert.εb : ℝ) (hhCert.T : ℝ) (by exact_mod_cast hεb) (by exact_mod_cast hT) hhCert.r
    (fun i => (hhCert.r.getD i 0 : ℝ)) (fun i => rfl)
    (fun i => by exact_mod_cast hr0 i) (fun i => by exact_mod_cast hd1 i)
    (oscDomOKB_sound _ hdom) (fun i => by exact_mod_cast hη i)
    (fun j => by
      have h2 := (Rat.cast_le (K := ℝ)).2 (hdr j)
      push_cast at h2 ⊢
      exact h2)
    (fun j => by exact_mod_cast hmg j)
    (fun _ => (1 / 12500) ^ 2) (fun _ => 5657 / 50000000) (fun _ => 209 / 10000000000000)
    (fun _ => by norm_num) (fun _ => 1 / 12500) (fun _ => by norm_num) (fun _ => le_refl _)
    (fun _ => by norm_num)
    (by
      simp only [OscPhysDom, hhCert, hhStep1, hhStep2, hhStep3]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, trivial⟩ <;> norm_num)
    (fun i => by
      rw [htailR, ha i]; norm_num)
    (fun j => by
      rw [htailR, hrr j]; norm_num)
    z₀ hz₀
  have hf : (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) => cartEval hhCert.H w) =
      fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
          + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3 := funext hhH_eval
  refine ⟨T₁, by rw [hTc] at hT₁; exact hT₁, z, hz0, ?_, ?_, ?_⟩
  · intro t ht
    have := (hder t ht).2
    rwa [hf] at this
  · intro I y hI h0 hy hyd t htI htT
    refine huniq I y hI h0 hy (fun t ht => ⟨trivial, ?_⟩) t htI htT
    rw [hf]
    exact hyd t ht
  · intro t ht j
    have ht' : |t| ≤ (hhCert.T : ℝ) := by rw [hTc]; exact ht
    obtain ⟨h1, h2⟩ := hb t ht' j
    simp only [ha j, hee j] at h1 h2
    have hT10 : (1 / 10000000000000000000 : ℝ) * |t| ≤ 1 / 10000000000000000000 * 10 ^ 10 :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    rw [hTc] at h2
    have h3 := hz₀ j
    constructor
    · refine lt_of_le_of_lt h2 ?_
      norm_num
    · refine le_trans h1 ?_
      norm_num at hT10 ⊢
      linarith

end KAM.EffectiveStability.HenonHeiles

end
