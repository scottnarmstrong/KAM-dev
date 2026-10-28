/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm

/-!
# Planar quartic torsion: the frozen-predicate bridge

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form`): a sixth-order remainder bound on the oscillator
slow length, with integrability, implies the frozen predicate `HasSecularBirkhoffForm` on a
smaller oscillator disc.  The statement is deliberately conditional and separately named; it does
not replace `birkhoff_form`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

/-- Build the frozen predicate from a sixth-order remainder on the SAME perturbation.
A conditional helper has a distinct name and does not replace birkhoff_form. -/
theorem hasSecularBirkhoffForm_of_sixth_order
    (P : ℝ → Phase (2 + 2) → ℝ) (V : Set (Fin 2 → ℝ)) (r C mu0 : ℝ)
    (hr : 0 < r) (hC : 0 < C) (hmu : 0 < mu0)
    (P0 : ℝ → (Fin 2 → ℝ) → ℝ) (Omega : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (beta : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hi : ∀ mu ∈ Icc (0 : ℝ) mu0, ∀ I ∈ V, ∀ p q : Fin 2 → ℝ,
      p11c_slowLength (q, p) < r → IntegrableOn (fun phi => P mu (assemble I phi p q))
        (Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π))))
    (he : ∀ mu ∈ Icc (0 : ℝ) mu0, ∀ I ∈ V, ∀ p q : Fin 2 → ℝ,
      p11c_slowLength (q, p) < r →
      |secularAverage P mu I p q - (P0 mu I + (∑ j, Omega mu I j * oscillatorAction p q j) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, beta mu I i j * oscillatorAction p q i * oscillatorAction p q j)| ≤
          C * (p11c_slowLength (q, p)) ^ 6) (r0 : ℝ) (hr0 : 0 < r0) (hrr : r0 ≤ r / sqrt 2) :
    HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta := by
  -- the slow length is controlled by the oscillator discs
  have hsq : ∀ (p q : Fin 2 → ℝ) (d : ℝ), (∀ j, p j ^ 2 + q j ^ 2 < d ^ 2) →
      p11c_slowLength (q, p) ^ 2 < 2 * d ^ 2 := by
    intro p q d h
    have h0 : 0 ≤ ∑ i, (q i ^ 2 + p i ^ 2) := Finset.sum_nonneg fun i _ => by positivity
    rw [p11c_slowLength, sq_sqrt h0, Fin.sum_univ_two]
    have := h 0; have := h 1
    simp only []
    linarith
  have hlen : ∀ (p q : Fin 2 → ℝ) (d : ℝ), 0 < d → d ≤ r0 → (∀ j, p j ^ 2 + q j ^ 2 < d ^ 2) →
      p11c_slowLength (q, p) < r := by
    intro p q d hd hdr h
    have h2 := hsq p q d h
    have hs : 0 < sqrt 2 := by positivity
    have hs2 : sqrt 2 ^ 2 = 2 := sq_sqrt (by norm_num)
    have hle : sqrt 2 * r0 ≤ r := by
      have := (le_div_iff₀ hs).1 hrr; linarith
    have hl0 : 0 ≤ p11c_slowLength (q, p) := sqrt_nonneg _
    have : p11c_slowLength (q, p) < sqrt 2 * r0 := by
      apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
      rw [mul_pow, hs2]
      nlinarith
    linarith
  intro mu hmu' I hI
  refine ⟨fun p q h => hi mu hmu' I hI p q (hlen p q r0 hr0 le_rfl h), ?_⟩
  intro eps heps
  have hd : 0 < sqrt (eps / (32 * C)) := sqrt_pos.2 (by positivity)
  refine ⟨min r0 (sqrt (eps / (32 * C))), lt_min hr0 hd, min_le_left _ _, ?_⟩
  intro p q h
  set δ := min r0 (sqrt (eps / (32 * C))) with hδ
  have hδpos : 0 < δ := lt_min hr0 hd
  have hδr : δ ≤ r0 := min_le_left _ _
  have hδ2 : δ ^ 2 ≤ eps / (32 * C) := by
    have : δ ≤ sqrt (eps / (32 * C)) := min_le_right _ _
    calc δ ^ 2 ≤ sqrt (eps / (32 * C)) ^ 2 := by gcongr
      _ = _ := sq_sqrt (by positivity)
  refine (he mu hmu' I hI p q (hlen p q δ hδpos hδr h)).trans ?_
  set N := ‖(p, q)‖ with hN
  have hp : ∀ j, p j ^ 2 ≤ N ^ 2 := fun j => by
    apply sq_le_sq' <;> [skip; skip] <;>
    · have h1 := (abs_le.1 ((norm_le_pi_norm p j).trans (le_max_left _ _) : |p j| ≤ N))
      linarith [h1.1, h1.2]
  have hq : ∀ j, q j ^ 2 ≤ N ^ 2 := fun j => by
    apply sq_le_sq' <;> [skip; skip] <;>
    · have h1 := (abs_le.1 ((norm_le_pi_norm q j).trans (le_max_right _ _) : |q j| ≤ N))
      linarith [h1.1, h1.2]
  set L := p11c_slowLength (q, p) with hL
  have hL2 : L ^ 2 < 2 * δ ^ 2 := hsq p q δ h
  have hL2' : L ^ 2 ≤ 4 * N ^ 2 := by
    have h0 : 0 ≤ ∑ i, (q i ^ 2 + p i ^ 2) := Finset.sum_nonneg fun i _ => by positivity
    rw [hL, p11c_slowLength, sq_sqrt h0, Fin.sum_univ_two]
    have := hp 0; have := hp 1; have := hq 0; have := hq 1
    simp only []
    linarith
  have hN0 : 0 ≤ N ^ 2 := by positivity
  have hL0 : 0 ≤ L ^ 2 := by positivity
  have h6 : L ^ 6 = L ^ 2 * (L ^ 2) ^ 2 := by ring
  have h4 : (L ^ 2) ^ 2 ≤ (4 * N ^ 2) ^ 2 := by gcongr
  have h5 : L ^ 6 ≤ (2 * δ ^ 2) * (16 * (N ^ 2) ^ 2) := by
    rw [h6]
    calc L ^ 2 * (L ^ 2) ^ 2 ≤ (2 * δ ^ 2) * (4 * N ^ 2) ^ 2 := by
          apply mul_le_mul hL2.le h4 (by positivity) (by positivity)
      _ = _ := by ring
  have hN4 : N ^ 4 = (N ^ 2) ^ 2 := by ring
  rw [hN4.symm] at h5 ⊢
  have hk : 32 * C * δ ^ 2 ≤ eps := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 32 * C)).1 (by linarith [hδ2] : δ ^ 2 ≤ eps / (32 * C))
    linarith
  have hN4' : 0 ≤ N ^ 4 := by positivity
  calc C * L ^ 6 ≤ C * ((2 * δ ^ 2) * (16 * N ^ 4)) := by gcongr
    _ = (32 * C * δ ^ 2) * N ^ 4 := by ring
    _ ≤ eps * N ^ 4 := by gcongr

end KAM.Planetary

end
