/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Poschel.BlockStability

/-!
# Pöschel's Theorem 1, stopped form (`bpN:p9:thm1`)

The joint statement `thm1` with both branches and the shared constants. The exceptional branch
(`t1-b`) puts the initial action in the full-rank block (`full_rank_zone`); the nonexceptional
branch chooses a maximal block by `covering` (`t1-a-choice`) and compares its admissible time
with the target time (`t1-a-theta`, `t1-a-res`, `t1-a-concl`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

section Arith

/-- `t1-a-theta`: the numerical time comparison for the block `⊥`. -/
private theorem time_bot {T Om A s E rb eps m r0 : ℝ} (hOm : 0 < Om) (hs : 0 < s) (hE : 0 < E)
    (hrb : 0 < rb) (hm : 0 < m) (hT : T * Om ≤ A ^ 2 * s * E) (heps : eps = m * rb ^ 2 / 2 ^ 10)
    (hA : A ^ 2 * rb ≤ r0) (hmr : m * r0 ≤ 8 * Om) : T * (5 * eps) ≤ s * rb * E := by
  have hsE : 0 < s * rb * E := by positivity
  refine le_of_mul_le_mul_right ?_ hOm
  have h1 : T * (5 * eps) * Om = 5 * eps * (T * Om) := by ring
  have h2 : 5 * eps * (T * Om) ≤ 5 * eps * (A ^ 2 * s * E) :=
    mul_le_mul_of_nonneg_left hT (by rw [heps]; positivity)
  have h3 : 5 * eps * (A ^ 2 * s * E) = 5 / 2 ^ 10 * (m * (s * rb * E)) * (A ^ 2 * rb) := by
    rw [heps]; ring
  have h4 : m * (s * rb * E) * (A ^ 2 * rb) ≤ m * (s * rb * E) * r0 :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h5 : (s * rb * E) * (m * r0) ≤ (s * rb * E) * (8 * Om) :=
    mul_le_mul_of_nonneg_left hmr hsE.le
  have h6 : 0 < s * rb * E * Om := by positivity
  nlinarith

/-- `t1-a-res`: the numerical time comparison for an intermediate block. -/
private theorem time_mid {T Om Omb A s E rb rl eps m : ℝ} (hOmbOm : Omb ≤ Om)
    (hT0 : 0 ≤ T) (hs : 0 < s) (hE : 0 < E) (hm : 0 < m) (hrb : 0 < rb)
    (hT : T * Om ≤ A ^ 2 * s * E) (heps : eps = m * rb ^ 2 / 2 ^ 10) (hrl : A * rb ≤ rl)
    (hA : 1 ≤ A) : T * (288 * Omb * eps) ≤ s * m * rl ^ 2 * E := by
  have heps0 : 0 ≤ eps := by rw [heps]; positivity
  have h1 : T * Omb ≤ A ^ 2 * s * E :=
    (mul_le_mul_of_nonneg_left hOmbOm hT0).trans hT
  have h2 : T * (288 * Omb * eps) = 288 * eps * (T * Omb) := by ring
  have h3 : 288 * eps * (T * Omb) ≤ 288 * eps * (A ^ 2 * s * E) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 288 * eps * (A ^ 2 * s * E) = 288 / 2 ^ 10 * (m * s * E) * (A * rb) ^ 2 := by
    rw [heps]; ring
  have h5 : (A * rb) ^ 2 ≤ rl ^ 2 := by
    have : 0 ≤ A * rb := by positivity
    exact pow_le_pow_left₀ this hrl 2
  have h6 : 0 ≤ m * s * E := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h5 h6, mul_nonneg h6 (sq_nonneg (A * rb))]

end Arith

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

theorem thm1 (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (hfb : WBound (cpx P) r0 s f eps)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip P r0, F x = KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t)
    (hI : (z 0).2 ∈ P) :
    let I0 := (z 0).2
    let Om0 := (omega0Ball S I0 hI).maximum
    (m * r0 / 8 ≤ euclid (KAM.frequencyMap h I0) →
      ∀ t ∈ J, |t| ≤ thmA m M ^ 2 * s / Om0 *
        Real.exp (Real.pi * s / (3 * Real.sqrt n) * thmK n r0 m M eps) →
      z t ∈ realStrip P r0 ∧
      ‖(z t).2 - I0‖ ≤ (r0 / thmA m M) / 2 *
        (eps / thmEps0 n r0 m M) ^ HeadParams.expo n) ∧
    (euclid (KAM.frequencyMap h I0) < m * r0 / 8 →
      ∀ t ∈ J, z t ∈ realStrip P r0 ∧ euclid ((z t).2 - I0) ≤ r0 / 2) := by
  intro I0 Om0
  -- `t1-par`
  obtain ⟨hA11, -, -, -, hK1, -, hexpo, heq, -, -, -, -, hvalid⟩ := elementary S heps heps0
  have hn := S.hn
  have hTB : (⊤ : Lattice n) ≠ ⊥ := fun h' => by
    have := latticeDim_top (n := n)
    rw [h', latticeDim_bot] at this
    omega
  obtain ⟨-, hcov, hcovΛ, hrbot, -⟩ :=
    covering (theoremCover n r0 m M eps) hvalid P (KAM.frequencyMap h)
  obtain ⟨htopmax, htoprad, -, -, hzoneiff⟩ := full_rank_zone S heps heps0
  refine ⟨fun hge t ht htime => ?_, fun hlt t ht => ?_⟩
  · -- `t1-a-choice`
    obtain ⟨Λ, hΛ, hblock⟩ := hcov I0 hI
    have hΛT : Λ ≠ ⊤ := by
      rintro rfl
      have := (hzoneiff I0 hI).1 hblock
      linarith
    have hmax := maximal (n := n) (K := thmK n r0 m M eps) (by linarith) Λ
    have hvol := hmax.2.2.2.2.2.2.2.2.2 hΛ
    obtain ⟨-, -, -, -, -, -, hrK⟩ := hcovΛ Λ hΛ
    have hrK := hrK hΛT
    have hA0 : 0 < thmA m M := by linarith
    have hK0 : 0 < thmK n r0 m M eps := by linarith
    have hAK : 1 ≤ thmA m M * thmK n r0 m M eps := by nlinarith
    have hrbot' : (theoremCover n r0 m M eps).radius (⊥ : Lattice n) =
        r0 / (thmA m M * thmK n r0 m M eps) ^ n := hrbot
    have hbot0 : 0 < (theoremCover n r0 m M eps).radius (⊥ : Lattice n) := by
      rw [hrbot']; exact div_pos S.hr0 (pow_pos (by linarith) n)
    have hrΛ : (theoremCover n r0 m M eps).radius Λ ≤ r0 / (thmA m M * thmK n r0 m M eps) := hrK
    -- the block ball sits inside the `omega0` ball
    have hrΛ0 : 0 ≤ (theoremCover n r0 m M eps).radius Λ := hvalid.radius_nonneg Λ
    have hrΛA : (theoremCover n r0 m M eps).radius Λ / 2 ≤ r0 / thmA m M := by
      have : r0 / (thmA m M * thmK n r0 m M eps) ≤ r0 / thmA m M :=
        div_le_div_of_nonneg_left S.hr0.le hA0 (by nlinarith)
      linarith
    obtain ⟨-, -, hOmle, hOmcen, -⟩ := omega0 S I0 hI
    have hOm0pos : 0 < Om0 := by
      have : 0 < m * r0 / 8 := by have := S.hm; have := S.hr0; positivity
      linarith
    set B := blockBall S heps heps0 Λ hΛ I0 hI with hBdef
    obtain ⟨-, -, -, hattain, hmaxleB, hcenB, -⟩ := frequency_maximum B
    obtain ⟨Ib, hIb, hIbeq⟩ := hattain
    have hOmΛ : B.maximum ≤ Om0 := by
      rw [hIbeq]
      refine hOmle Ib ?_
      have hh : euclid (Ib - I0) ≤ (theoremCover n r0 m M eps).radius Λ / 2 := hIb
      exact hh.trans hrΛA
    have hOmΛ0 : 0 ≤ B.maximum :=
      le_trans (by unfold KAM.Nekhoroshev.euclid; positivity) hcenB
    -- `t1-a-concl`: time
    have hE : Real.pi * s / (3 * Real.sqrt n) * thmK n r0 m M eps =
        2 * Real.pi * ((theoremCover n r0 m M eps).K / Real.sqrt n) * s / 6 := by
      show _ = 2 * Real.pi * (thmK n r0 m M eps / Real.sqrt n) * s / 6
      ring
    rw [hE] at htime
    have hEpos := Real.exp_pos (2 * Real.pi * ((theoremCover n r0 m M eps).K / Real.sqrt n) * s / 6)
    have hT : |t| * Om0 ≤ thmA m M ^ 2 * s *
        Real.exp (2 * Real.pi * ((theoremCover n r0 m M eps).K / Real.sqrt n) * s / 6) := by
      have := mul_le_mul_of_nonneg_right htime hOm0pos.le
      refine this.trans_eq ?_
      field_simp
    have hLam0 : Λ ≠ ⊥ → 1 ≤ latticeDim Λ := fun hne => by
      by_contra hlt
      exact hne ((lattice_resonance Λ).2.1 (by omega))
    have hadm : blockAdm (theoremCover n r0 m M eps) s eps B.maximum Λ t := by
      refine Or.inr ?_
      have hmr : m * r0 ≤ 8 * Om0 := by
        have : m * r0 / 8 ≤ Om0 := hge.trans hOmcen
        linarith
      have hepsb : eps = m * ((theoremCover n r0 m M eps).radius (⊥ : Lattice n)) ^ 2 / 2 ^ 10 := by
        rw [hrbot']; exact heq
      by_cases hB : Λ = ⊥
      · subst hB
        simp only [↓reduceIte]
        refine time_bot hOm0pos S.hs hEpos hbot0 S.hm hT hepsb ?_ hmr
        rw [hrbot']
        have h1 : thmA m M ^ 2 ≤ (thmA m M * thmK n r0 m M eps) ^ n :=
          (pow_le_pow_left₀ hA0.le (by nlinarith) 2).trans (pow_le_pow_right₀ hAK hn)
        rw [← mul_div_assoc, mul_comm, mul_div_assoc, mul_le_iff_le_one_right S.hr0,
          div_le_one (pow_pos (by linarith) n)]
        exact h1
      · simp only [hB, ↓reduceIte]
        refine time_mid hOmΛ (abs_nonneg t) S.hs hEpos S.hm hbot0 hT hepsb ?_ (by linarith)
        have hd := hLam0 hB
        have hvpos : 0 < volume_def Λ := by linarith [hvol.1]
        have hq : 0 < r0 / (thmA m M * thmK n r0 m M eps) ^ n :=
          div_pos S.hr0 (pow_pos (by linarith) n)
        have hΛeq : (theoremCover n r0 m M eps).radius Λ =
            r0 / (thmA m M * thmK n r0 m M eps) ^ n *
              (thmA m M * thmK n r0 m M eps) ^ latticeDim Λ / volume_def Λ := rfl
        rw [hrbot', hΛeq, le_div_iff₀ hvpos]
        have hv : volume_def Λ ≤ thmK n r0 m M eps ^ latticeDim Λ := hvol.2
        have hAd : thmA m M ≤ thmA m M ^ latticeDim Λ := le_self_pow₀ (by linarith) (by omega)
        have key : thmA m M * volume_def Λ ≤ (thmA m M * thmK n r0 m M eps) ^ latticeDim Λ := by
          rw [mul_pow]
          calc thmA m M * volume_def Λ ≤ thmA m M * thmK n r0 m M eps ^ latticeDim Λ := by gcongr
            _ ≤ thmA m M ^ latticeDim Λ * thmK n r0 m M eps ^ latticeDim Λ := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left key hq.le]
    obtain ⟨h1, h2, -⟩ := block_stab S heps heps0 hfb Λ hΛ hF hJ h0 hz hI hblock t ht hadm
    refine ⟨h1, h2.trans ?_⟩
    rw [hexpo]
    calc _ ≤ r0 / (thmA m M * thmK n r0 m M eps) / 2 := by linarith
      _ = _ := by field_simp
  · have hmem := (hzoneiff I0 hI).2 hlt
    obtain ⟨h1, -, h3⟩ := block_stab S heps heps0 hfb ⊤ htopmax hF hJ h0 hz hI hmem t ht
      (Or.inl rfl)
    refine ⟨h1, ?_⟩
    have := h3 hTB
    rwa [htoprad] at this

end Theorem1

end KAM.Nekhoroshev

end
