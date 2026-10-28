/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Domains
public import KAM.Weighted.Norm
public import KAM.Weighted.Coefficients
public import KAM.Canonical.Setting

/-!
# Normal form setting (`bpN:p6:setting`, `bpN:p6#data`, `bpN:p6:lipschitz`, `bpN:p6:divisor`)

The data of blueprint-N Part 6: the cut-off set `Z_K`, the frequency `ω = ∂_I h`, the pairing
`k · v`, the conjugate exponent, the nonresonance, Lipschitz and divisor predicates, finite
decompositions with the `*`-norm, and the lemmas `lipschitz`, `lipschitz_entries`, `divisor`.
Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-1.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}


/-- `Z_K = {k : |k|₁ ≤ K}` (the `ℓ¹` ball; the cut-off set of `truncate K`). -/
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}

/-- The complex frequency `ω(I) = ∂_I h(I) ∈ ℂⁿ` (`ωᵢ = Dh(I)eᵢ`). -/
def freq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)

/-- `k · v = ∑ kᵢ vᵢ` for `k ∈ ℤⁿ`, `v ∈ ℂⁿ`. -/
def dotC (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i

/-- The Hölder conjugate `q = p/(p-1)`. -/
def conjExp (p : ℝ) : ℝ := p / (p - 1)

/-- `(N1)`: `(α, K)`-nonresonant modulo `Λ` on `D`. -/
def IsNonresonant (D : Set (Fin n → ℂ)) (K α : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I ∈ D, ∀ k ∈ zBall n K \ Λ, α ≤ ‖dotC k (freq h I)‖

/-- `(N2)`: the frequency Lipschitz bound (max norms) from points of `D` into `V_r D`. -/
def FreqLipschitz (D : Set (Fin n → ℂ)) (r L : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ I ∈ polyNbhd D r, ‖I - I₀‖ < r → ‖freq h I - freq h I₀‖ ≤ L * ‖I - I₀‖

/-- `(N-dir)` (and the conclusion of `divisor`): `|k · ω(I)| ≥ c` on `V` for `k ∈ Z_K \ Λ`. -/
def DivisorBound (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖

/-- A finite decomposition `g = ∑ⱼ gⱼ`, `gⱼ ∈ O(rⱼ, sⱼ)`, `|gⱼ|_{rⱼ,sⱼ} ≤ Mⱼ`, `rⱼ ≥ r`, `sⱼ ≥ s`
(Definition `bpN:p6:setting`; the bounds `Mⱼ` stand for the norms). -/
structure IsDecomp (D : Set (Fin n → ℂ)) (r s : ℝ) (g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) {N : ℕ}
    (gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (rj sj Mj : Fin N → ℝ) : Prop where
  eq_sum : g = fun z => ∑ j, gj j z
  r_le : ∀ j, r ≤ rj j
  s_le : ∀ j, s ≤ sj j
  inClass : ∀ j, InClass D (rj j) (sj j) (gj j)
  bound : ∀ j, WBound D (rj j) (sj j) (gj j) (Mj j)

/-- `|g|_* = ∑ⱼ ½(ρ/(rⱼ-r+ρ) + σ/(sⱼ-s+σ)) Mⱼ` (depends on the decomposition). -/
def starNorm (r s ρ σ : ℝ) {N : ℕ} (rj sj Mj : Fin N → ℝ) : ℝ :=
  ∑ j, (1 / 2) * (ρ / (rj j - r + ρ) + σ / (sj j - s + σ)) * Mj j

theorem norm_dotC_le (k : Fin n → ℤ) (v : Fin n → ℂ) :
    ‖dotC k v‖ ≤ KAM.Fourier.modeSize k * ‖v‖ := by
  unfold dotC KAM.Fourier.modeSize
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

theorem differentiableAt_freq {h : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) {I : Fin n → ℂ} (hI : I ∈ U) :
    DifferentiableAt ℂ (freq h) I := by
  have hd : DifferentiableAt ℂ (fderiv ℂ h) I :=
    ((KAM.holomorphic_regularity hU hh).1).differentiableAt (hU.mem_nhds hI)
  refine differentiableAt_pi.2 fun i => ?_
  exact hd.clm_apply (differentiableAt_const _)

/-- `bpN:p6:lipschitz`: an operator-norm bound `L` on `Dω` over `V_r D` gives `(N2)`. -/
theorem lipschitz {D : Set (Fin n → ℂ)} {r L : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hD2 : ∀ I ∈ polyNbhd D r, ‖fderiv ℂ (freq h) I‖ ≤ L) : FreqLipschitz D r L h := by
  intro I₀ hI₀ I hI hlt
  have hsub : ball I₀ r ⊆ polyNbhd D r := fun J hJ =>
    ⟨I₀, hI₀, by simpa [dist_eq_norm] using hJ⟩
  have hopen := isOpen_polyNbhd D r
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (f := freq h) (s := ball I₀ r)
    (fun x hx => differentiableAt_freq hopen hh (hsub hx)) (fun x hx => hD2 x (hsub hx))
    (convex_ball I₀ r) (mem_ball_self (lt_of_le_of_lt (norm_nonneg _) hlt))
    (by simpa [dist_eq_norm] using hlt)
  exact this

/-- `bpN:p6:lipschitz`, entry form: `|∂ᵢ∂ⱼh| ≤ M_C` on `V_r D` gives `(N2)` with `L = n M_C`. -/
theorem lipschitz_entries {D : Set (Fin n → ℂ)} {r Mc : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hD2 : ∀ I ∈ polyNbhd D r, ∀ i j : Fin n,
      ‖fderiv ℂ (fun J => fderiv ℂ h J (Pi.single j 1)) I (Pi.single i 1)‖ ≤ Mc) :
    FreqLipschitz D r (n * Mc) h := by
  refine lipschitz hh fun I hI => ?_
  have hopen := isOpen_polyNbhd D r
  have hfd : DifferentiableAt ℂ (freq h) I := differentiableAt_freq hopen hh hI
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have : ‖fderiv ℂ (freq h) I‖ ≤ 0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun v => ?_
      simp [Subsingleton.elim (fderiv ℂ (freq h) I v) 0]
    have hn0 : n = 0 := by
      have := Fintype.card_eq_zero_iff.2 hn
      rwa [Fintype.card_fin] at this
    exact this.trans (by simp [hn0])
  have hMc : 0 ≤ Mc := by
    obtain ⟨i⟩ := hn
    exact (norm_nonneg _).trans (hD2 I hI i i)
  have hnn : (0 : ℝ) ≤ n * Mc := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  have hcomp : ∀ w j, fderiv ℂ (freq h) I w j =
      fderiv ℂ (fun J => fderiv ℂ h J (Pi.single j 1)) I w := by
    intro w j
    rw [fderiv_pi (fun i => (differentiableAt_pi.1 hfd) i)]
    rfl
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℂ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [hcomp]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖v i • fderiv ℂ (fun J => fderiv ℂ h J (Pi.single j 1)) I (Pi.single i 1)‖
      ≤ ∑ _i : Fin n, ‖v‖ * Mc := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm v i) (hD2 I hI i j) (norm_nonneg _) (norm_nonneg _)
    _ = n * Mc * ‖v‖ := by simp; ring

/-- `bpN:p6:divisor`: `(N1)`, `(N2)`, `KLr ≤ α/p` give `|k·ω| ≥ α - KLr ≥ α/q` on `V_r D`. -/
theorem divisor {D : Set (Fin n → ℂ)} {r K α L p : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p) :
    DivisorBound (polyNbhd D r) K Λ h (α - K * L * r) ∧
    DivisorBound (polyNbhd D r) K Λ h (α / conjExp p) := by
  have h1 : DivisorBound (polyNbhd D r) K Λ h (α - K * L * r) := by
    intro I hI k hk
    obtain ⟨I₀, hI₀, hlt⟩ := hI
    have hIn : I ∈ polyNbhd D r := ⟨I₀, hI₀, hlt⟩
    have hN := hnr I₀ hI₀ k hk
    have hLip := hlip I₀ hI₀ I hIn hlt
    have hsplit : dotC k (freq h I₀) = dotC k (freq h I) - dotC k (freq h I - freq h I₀) := by
      simp only [dotC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
    have hmode : KAM.Fourier.modeSize k ≤ K := hk.1
    have hb : ‖dotC k (freq h I - freq h I₀)‖ ≤ K * L * r := by
      refine (norm_dotC_le _ _).trans ?_
      calc KAM.Fourier.modeSize k * ‖freq h I - freq h I₀‖
          ≤ K * (L * r) := by
            refine mul_le_mul hmode (hLip.trans ?_) (norm_nonneg _) hK
            exact mul_le_mul_of_nonneg_left hlt.le hL
        _ = K * L * r := by ring
    have : ‖dotC k (freq h I₀)‖ ≤ ‖dotC k (freq h I)‖ + ‖dotC k (freq h I - freq h I₀)‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    linarith
  refine ⟨h1, fun I hI k hk => le_trans ?_ (h1 I hI k hk)⟩
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p - 1 ≠ 0 := by linarith
  have : α / conjExp p = α - α / p := by
    unfold conjExp; field_simp
  linarith

end KAM.NormalForm
