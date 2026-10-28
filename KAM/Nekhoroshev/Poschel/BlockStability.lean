/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Poschel.BlockHypotheses
public import KAM.Nekhoroshev.Stability.Nonresonant
public import KAM.Nekhoroshev.Stability.ResonantStability
public import KAM.Nekhoroshev.Stability.Transfer

/-!
# Stability on a block (`bpN:p9:block-stab`)

For an action `I₀ = (z 0).2` in the block of a maximal lattice `Λ`, every orbit of the total field
`F` through `I₀` stays in the strip and drifts by at most `radius Λ / 2` for admissible times
(`block_stab`). The contained-orbit estimate is proved by `nonresonant` for `Λ = ⊥`
(`bs-theta`) and by `resonant_prop2` otherwise (`bs-res`), and extended to arbitrary `F`-orbits by
`stopped_extension` (`bs-stop`), with the max norm and the Euclidean norm respectively.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

section Theorem1
variable {P : Set (Fin n → ℝ)} {r0 s m M ell : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

theorem block_stab (S : Theorem1Setting P r0 s m M ell h f)
    {eps : ℝ} (heps : 0 < eps) (heps0 : eps ≤ thmEps0 n r0 m M)
    (hfb : WBound (cpx P) r0 s f eps) (Λ : Lattice n)
    (hΛ : maximalK (thmK n r0 m M eps) Λ)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip P r0, F x = KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t)
    (hI : (z 0).2 ∈ P)
    (hblock : (z 0).2 ∈ actionBlock (theoremCover n r0 m M eps) P (KAM.frequencyMap h) Λ) :
    let c := theoremCover n r0 m M eps
    let B := blockBall S heps heps0 Λ hΛ (z 0).2 hI
    ∀ t ∈ J, blockAdm c s eps B.maximum Λ t →
      z t ∈ realStrip P r0 ∧ ‖(z t).2 - (z 0).2‖ ≤ c.radius Λ / 2 ∧
      (Λ ≠ ⊥ → euclid ((z t).2 - (z 0).2) ≤ c.radius Λ / 2) := by
  intro c B
  have hn1 : 1 ≤ n := by have := S.hn; omega
  have hM : 0 < M := lt_of_lt_of_le S.hm S.hmM
  obtain ⟨hr, hα, hδ, -, -, -, -, -, hsub, hh, hhr, hhess, hqc, hfc, hfr, hfb', hepsb, hcoef,
    hrad, hKrad, hr4, hMr, hnr, -, hclose, hδb, hlip, hbot⟩ :=
    block_hyp S heps heps0 hfb Λ hΛ (z 0).2 hblock
  obtain ⟨-, -, -, -, -, -, -, -, -, hKpos, -⟩ := elementary S heps heps0
  obtain ⟨-, -, -, -, hmaxle, hcenter, -⟩ := frequency_maximum B
  have hOm0 : 0 ≤ B.maximum :=
    le_trans (by unfold KAM.Nekhoroshev.euclid; positivity) hcenter
  have hconj : KAM.NormalForm.conjExp (9 / 8 : ℝ) = 9 := by
    unfold KAM.NormalForm.conjExp; norm_num
  have hmono : ∀ t t' : ℝ, |t'| ≤ |t| → blockAdm c s eps B.maximum Λ t →
      blockAdm c s eps B.maximum Λ t' := by
    intro t t' htt hadm
    unfold blockAdm at hadm ⊢
    rcases hadm with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      split_ifs at h ⊢
      · exact (mul_le_mul_of_nonneg_right htt (by positivity)).trans h
      · exact (mul_le_mul_of_nonneg_right htt
          (mul_nonneg (mul_nonneg (by norm_num) hOm0) heps.le)).trans h
  have hFloc : ∀ x ∈ realStrip {(z 0).2} (c.radius Λ),
      F x = KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)) x :=
    fun x hx => hF x (hsub hx)
  have hz0 : (z 0).2 ∈ ({(z 0).2} : Set (Fin n → ℝ)) := mem_singleton _
  -- `bs-res`: Euclidean estimate for `Λ = ⊤` or `Λ ≠ ⊥`
  have hEuc : (Λ = ⊤ ∨ Λ ≠ ⊥) → ∀ t ∈ J, blockAdm c s eps B.maximum Λ t →
      euclid ((z t).2 - (z 0).2) ≤ c.radius Λ / 2 ∧
        z t ∈ realStrip {(z 0).2} (c.radius Λ) := by
    intro hcase
    have hprop := resonant_prop2 (D := {(z 0).2}) hn1 (by norm_num : (1 : ℝ) < 9 / 8)
      (by norm_num : (9 / 8 : ℝ) ≤ 3 / 2) hr S.hs hKpos hα S.hm S.hmM S.hell hδ hh hhr hhess hqc
      hfc hfr hfb' heps.le hnr hclose
      (by rw [hconj]; exact hepsb.trans hcoef.le) hδb hrad.le hr4 hMr
    refine fun t ht hadm => (stopped_extension (D := {(z 0).2}) (Nrm := fun a => euclid a)
      (adm := blockAdm c s eps B.maximum Λ) (H := fun w => h w.2 + f w) isActionNorm_euclid
      (by linarith) (by linarith) hmono ?_ hFloc hJ h0 hz hz0 t ht hadm) |> fun h => h
    intro J' hJ' h0' z' hz' hz0' t' ht' hadm'
    have hz0e : (z' 0).2 = (z 0).2 := hz0'
    have hadm2 : (((Λ : Lattice n) : Set (Fin n → ℤ)) = univ ∨
        |t'| * (288 * B.maximum * eps) ≤
          s * m * c.radius Λ ^ 2 * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6)) := by
      unfold blockAdm at hadm'
      rcases hadm' with h | h
      · left; rw [h]; simp
      · by_cases hT : Λ = ⊤
        · left; rw [hT]; simp
        · right
          rcases hcase with hc | hc
          · exact absurd hc hT
          · simp only [hc, ↓reduceIte] at h; exact h
    have := hprop (z 0).2 hz0 B.maximum (fun I hI => hmaxle I hI) J' hJ' h0' z' hz' hz0e t' ht'
      hadm2
    rw [hz0e]; exact this.1
  -- `bs-theta`: max-norm estimate for `Λ = ⊥`
  have hTheta : Λ ≠ ⊤ → Λ = ⊥ → ∀ t ∈ J, blockAdm c s eps B.maximum Λ t →
      ‖(z t).2 - (z 0).2‖ ≤ c.radius Λ / 2 ∧ z t ∈ realStrip {(z 0).2} (c.radius Λ) := by
    intro hT hB
    have hcoe : ((Λ : Lattice n) : Set (Fin n → ℤ)) = {0} := by rw [hB]; simp
    rw [hcoe] at hnr
    have hL : 0 ≤ Real.sqrt n * M := by positivity
    have hnon := nonresonant (D := {(z 0).2}) hn1 (p := 9 / 8) (by norm_num) hr S.hs hKpos hα hL
      hh hhr hfc hfr hfb' heps.le hnr hlip hKrad.le (by rw [hconj]; exact hbot hB)
    refine fun t ht hadm => (stopped_extension (D := {(z 0).2}) (Nrm := fun a => ‖a‖)
      (adm := blockAdm c s eps B.maximum Λ) (H := fun w => h w.2 + f w) isActionNorm_norm
      (by linarith) (by linarith) hmono ?_ hFloc hJ h0 hz hz0 t ht hadm)
    intro J' hJ' h0' z' hz' hz0' t' ht' hadm'
    have hz0e : (z' 0).2 = (z 0).2 := hz0'
    have hadm2 : |t'| * (5 * eps) ≤
        s * c.radius Λ * Real.exp (2 * Real.pi * (c.K / Real.sqrt n) * s / 6) := by
      unfold blockAdm at hadm'
      have := hadm'.resolve_left hT
      simp only [hB, ↓reduceIte] at this
      rw [hB]; exact this
    have := hnon J' hJ' h0' z' hz' hz0' t' ht' hadm2
    rw [hz0e] at this ⊢
    exact this
  intro t ht hadm
  by_cases hT : Λ = ⊤ ∨ Λ ≠ ⊥
  · obtain ⟨he, hs'⟩ := hEuc hT t ht hadm
    exact ⟨hsub hs', (isActionNorm_euclid.norm_le _).trans he, fun _ => he⟩
  · push Not at hT
    obtain ⟨hT1, hB⟩ := hT
    obtain ⟨hn', hs'⟩ := hTheta hT1 hB t ht hadm
    exact ⟨hsub hs', hn', fun h => absurd hB h⟩

end Theorem1

end KAM.Nekhoroshev

end
